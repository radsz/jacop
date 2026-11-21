/*
 * LayeredGraphConstraint.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2008-2026 Polina Makeeva and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints.regular;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.WeakHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Supplier;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.InitOnce;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.ClauseModel;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;

/**
 * Generalized arc consistency for a layered graph: a directed acyclic graph with one layer of edges
 * per variable, where every edge is labelled with a value of its variable. An assignment is allowed
 * when it labels a path from a node of the first level to a node of the last level. Subclasses only
 * describe the graph; {@link Regular} unfolds an automaton into it and {@link
 * org.jacop.constraints.ExtensionalSupportMdd} takes it from a multi-valued decision diagram.
 *
 * <p>Each node counts its alive incoming and outgoing edges; an edge is alive while its value and
 * both its nodes are alive, so edges carry no state of their own. When a value is removed from a
 * variable only the edges labelled with it are visited. A node whose incoming or outgoing count
 * drops to zero is removed and only its edges on the other side are visited, which may remove
 * further nodes. Afterwards each value of a level where edges were removed is checked for an alive
 * edge, starting from the edge that supported it last time, and values without one are removed from
 * the variable. The counters are trailed, so backtracking costs time proportional to the counters
 * changed since the restored level. This follows the layered graph propagator of Gecode and the
 * incremental approach of MDD4R (Perez and Regin, "Improving GAC-4 for Table and MDD Constraints",
 * CP 2014), adapted to a trailing solver.
 *
 * <p>Two further measures keep large graphs fast. Removed edges stay in the static adjacency
 * arrays, so when a subtree of the search visited many of them, the arrays are compacted to the
 * alive edges before the search continues below the restored level, much as Gecode compacts the
 * graph when it copies a space. And in graphs too large for the processor caches, removed nodes are
 * processed a level at a time, one pass towards the last level and one towards the first, as Gecode
 * does.
 *
 * @author Polina Makeeva and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class LayeredGraphConstraint extends Constraint
    implements UsesQueueVariable, Stateful, Explainable, PbEncodable {

  /** Array of the variables of the graph levels. */
  public final IntVar[] list;

  private Map<IntVar, Integer> mapping;

  /**
   * Position of each variable indexed by its store index minus indexOffset, or -1, used instead of
   * mapping when the store indices of the variables are close to each other. Every change of a
   * variable is reported to all its constraints, so this lookup is on a hot path.
   */
  private int[] positionByIndex;

  private int indexOffset;

  /** Removes the values that label no edge, and in the first pass checks every level. */
  private final InitOnce init = new InitOnce();

  /** The graph as described, kept for explanations. */
  private LayeredGraphDescription description;

  /** The graph built when the constraint was imposed, possibly shared with other constraints. */
  private BuiltGraph built;

  /** The described graph ordered by level, built at the first explanation. */
  private LayeredGraphExplanation.Graph explanationGraph;

  /** Set while this constraint prunes domains, so its own changes are not queued again. */
  private boolean pruning;

  /** Levels (variable positions) whose variables changed since the last consistency call. */
  private int[] levelQueue;

  private int levelQueueSize;

  private boolean[] levelQueued;

  // Slots: a slot is a (level, value) pair. Slots of level i are
  // levelSlotStart[i]..levelSlotStart[i+1]-1.
  private int[] levelSlotStart;
  private int[] slotValue;
  private int[] slotLevel;

  // Static adjacency of the layered graph, two ints per edge so that both are read together. Edges
  // leaving node u are at positions outStart[u]..outStart[u+1]-1 and outEdge holds at 2e the
  // destination and at 2e+1 the slot of edge e; edges entering node u are at positions
  // inStart[u]..inStart[u+1]-1 and inEdge holds the source and the slot; edges of slot s are at
  // positions slotStart[s]..slotStart[s+1]-1 and slotEdge holds the source and the destination.
  private int[] outStart;
  private int[] outEdge;
  private int[] inStart;
  private int[] inEdge;
  private int[] slotStart;
  private int[] slotEdge;

  /**
   * Number of edges in the current adjacency arrays. Removed edges stay in these arrays and are
   * skipped, so once most of them are removed the arrays are compacted into new ones holding only
   * the alive edges. The compacted arrays are valid until the store level at which they were made
   * is removed; earlier arrays are kept on a stack, together with arrays that can be reused.
   */
  private int edges;

  private int aliveEdges;

  /** Visits of removed edges so far, which decide when to compact. */
  private long wastedVisits;

  /** The value of wastedVisits when the search entered each store level up to openLevel. */
  private long[] levelWaste = new long[16];

  private int openLevel = -1;

  /** Store level for which the next consistency call compacts the adjacency arrays, or -1. */
  private int pendingCompaction = -1;

  private Adjacency[] adjacency = new Adjacency[8];

  private int adjacencyTop;

  /** Adjacency arrays of the layered graph and the store level at which they were made. */
  private static final class Adjacency {
    int level;
    int edges;
    int[] outStart;
    int[] outEdge;
    int[] inStart;
    int[] inEdge;
    int[] slotStart;
    int[] slotEdge;
    int[] residue;
  }

  // Backtrackable state, one long per record so that a record is a single memory access. Bits
  // 0..39 hold the value, bits 40..62 the epoch in which the record was trailed last and bit 63 is
  // set for a removed node. Records 0..nodes-1 hold for each node the number of alive outgoing
  // edges (the low outBits bits of the value) and incoming edges (the bits above). The next records
  // hold for each slot 1 while the value is alive and 0 once it is removed, followed by one record
  // per level with the number of its values that are still alive and one record with the number of
  // alive edges. An edge is alive when its slot and both its nodes are alive.
  private static final long VALUE = (1L << 40) - 1;
  private static final int STAMP_SHIFT = 40;
  private static final int STAMP_MASK = (1 << 23) - 1;
  private static final long REMOVED = Long.MIN_VALUE;

  private long[] state;

  private long outMask;
  private long inMask;
  private long inOne;
  private int slotBase;
  // the numbers of nodes and slots of the graph
  private int nodeCount;
  private int slotCount;
  private int levelBase;

  /** Record holding the number of alive edges. */
  private int edgeRecord;

  /**
   * Epoch of the current consistency call. A new epoch starts whenever the store level differs from
   * the one of the previous call or a level was removed, so a record trailed in an earlier epoch is
   * trailed again before it changes.
   */
  private int epoch;

  private int epochLevel = -1;

  // Trail of saved records (record and its previous content) and, for each level with trailed
  // records, the level and the trail position where its records start.
  private long[] trail = new long[256];
  private int trailTop;
  private int[] markLevel = new int[16];
  private int[] markPosition = new int[16];
  private int markTop;

  private int currentLevel;

  // The store of the constraint and the levels at which its state changed, each recorded once with
  // the store, so the store calls removeLevel only for those levels instead of for every level.
  private Store imposedStore;
  private int[] changedLevels = new int[16];
  private int changedTop;

  // Nodes that lost all their incoming edges (forward lists) or all their outgoing edges
  // (backward lists) and must be removed. In large graphs they are kept as linked lists per level:
  // the first node of level l is
  // forwardHead[l] and the next one of node u is forwardNext[u], -1 ends a list. Removing a node
  // of the forward lists can only empty nodes of the next level and one of the backward lists only
  // nodes of the previous level, so one pass up and one pass down remove them all, a level at a
  // time, which keeps the visited counters close together in memory as in Gecode.
  private int[] forwardHead;
  private int[] forwardNext;
  private int[] backwardHead;
  private int[] backwardNext;
  // Bit l is set while the forward (backward) list of level l is not empty.
  private long[] forwardLevels;
  private long[] backwardLevels;

  /**
   * Graphs with at most this many nodes fit in the processor caches, so their nodes are removed in
   * any order from the deadNodes stack, which costs less than keeping the lists per level.
   */
  private static final int LAYERED_REMOVAL_NODES = 4096;

  private boolean layeredRemoval;

  // In large graphs the alive nodes of each level form a sparse set: levelOrder holds the nodes of
  // level l at positions levelNodeStart[l]..levelNodeStart[l+1]-1, the alive ones first, and
  // orderPosition is its inverse. The record aliveBase + l holds the number of alive nodes of level
  // l, so restoring the record on backtracking restores the set.
  private int[] levelNodeStart;
  private int[] levelOrder;
  private int[] orderPosition;
  private int aliveBase;

  // In large graphs removed values are processed in the forward pass, level by level; until then
  // they are kept as linked lists per level, the first is removedSlotHead[l] and the next one of
  // slot s is removedSlotNext[s], -1 ends a list.
  private int[] removedSlotHead;
  private int[] removedSlotNext;

  /** The count of a node before its level was recounted. */
  private int[] previousCount;

  private int inShift;

  // Support search, used instead of the counters when supportSearch is set. Each consistency call
  // searches the graph depth first from the first level for paths labelled with values of the
  // domains, as the mddc algorithm of Cheng and Yap (CP 2008) does, and stops as soon as every
  // value of the levels below has a support. Nodes from which no such path exists are kept in a
  // list, noList, whose size is the record noRecord and whose members are set in noBits, so they
  // are skipped until backtracking; the bits of the entries past the record are cleared at the
  // next call. Nodes with a path are marked with the stamp of the call in yesStamp. The stamps are
  // only read during one call, so the constraints of a store that share a built graph share them
  // (SearchScratch): WordDesign2-words-mdd-100 (XCSP 2023) posts 4,950 MDDs on one diagram of
  // 525,720 nodes, and three node arrays of their own took 6 MB for each of them.
  private boolean supportSearch;
  private long[] noBits;
  private int[] noList;
  private int noListTop;
  private int noRecord;
  private SearchScratch scratch;
  private int[] yesStamp;
  private int[] inDomainStamp;
  private int[] supportedStamp;
  private int searchStamp;
  private int[] levelUnsupported;
  private int deepestUnsupported;

  static final String ENGINE_PROPERTY = System.getProperty("layered_graph_engine", "");

  /** The propagation algorithms of the layered graph. */
  public enum Engine {
    /** The counters, switching to support search during the search when that is faster. */
    AUTO,
    /** Trailed counters of alive edges per node, as in Gecode and the reset of MDD4R. */
    COUNTERS,
    /** Depth first search for supports from the first level, as in mddc. */
    SUPPORT_SEARCH
  }

  private Engine engine = Engine.AUTO;

  /**
   * It sets the propagation algorithm. It must be called before the constraint is imposed.
   *
   * @param engine the algorithm.
   */
  public void setEngine(Engine engine) {
    this.engine = engine;
  }

  /**
   * It returns the propagation algorithm in use. Before the constraint is imposed it is the one
   * set; with {@link Engine#AUTO} it may change from the counters to support search during the
   * search.
   *
   * @return the algorithm.
   */
  public Engine engine() {
    if (state == null) {
      return engine;
    }
    if (supportSearch) {
      return Engine.SUPPORT_SEARCH;
    }
    return Engine.COUNTERS;
  }

  /**
   * It decides, with {@link Engine#AUTO}, whether to switch from the counters to support search,
   * given the time both took on the same calls.
   *
   * @param countersNanos the time of the counters, in nanoseconds.
   * @param searchNanos the time of support search on the same calls, in nanoseconds.
   * @return true to switch to support search.
   */
  protected boolean preferSupportSearch(long countersNanos, long searchNanos) {
    return searchNanos < SWITCH_SHARE * countersNanos;
  }

  /**
   * It gives a copy of this constraint the propagation algorithm set for this one.
   *
   * @param copy the copy, not imposed yet.
   */
  protected void copyEngineTo(LayeredGraphConstraint copy) {
    copy.engine = engine;
  }

  private Engine resolveEngine() {
    Engine chosen = engine == Engine.AUTO ? defaultEngine() : engine;
    if (chosen == Engine.AUTO && !ENGINE_PROPERTY.isEmpty()) {
      chosen = Engine.valueOf(ENGINE_PROPERTY.toUpperCase(Locale.ROOT));
    }
    return chosen;
  }

  // Automatic choice. Support search costs a depth first search from the first level at every
  // call; the counters cost time proportional to the removed edges and their nodes. Which one is
  // cheaper depends on the model as much as on the graph: on short graphs in tightly constrained
  // models support search was up to three times faster, on loose models with sliding window
  // automata it was up to two and a half times slower, and from about 30 levels on the counters
  // were faster on most models measured. So the constraint starts with the counters and, for
  // at most PROBE_CALLS calls after the first PROBE_SKIP calls, also runs support search on the
  // propagated domains and times both. Then it switches to support search for good if that took
  // less than SWITCH_SHARE of the time of the counters. Every PROBE_CHECK calls it decides early
  // when support search took more than STAY_SHARE or less than SWITCH_EARLY_SHARE of the time of
  // the counters, so a clear case pays little for the probe. Both are domain consistent, so the
  // choice changes only the speed. The switch is one way because support search does not keep the
  // counters up to date.

  static final int PROBE_SKIP = 8;

  static final int PROBE_CALLS = 1024;

  static final int PROBE_CHECK = 64;

  static final double STAY_SHARE = 1.2;

  static final double SWITCH_EARLY_SHARE = 0.5;

  static final double SWITCH_SHARE = 0.8;

  private boolean probing;

  private int probeCalls;

  private long probeCountersTime;

  private long probeSearchTime;

  private int[] deadNodes = new int[64];
  private int deadNodesSize;

  // Slots that lost all their edges during the current consistency call.
  private int[] emptySlots;
  private int emptySlotsSize;

  /** Level of each node. */
  private int[] nodeLevel;

  /** For each slot, the position of an edge that was alive when last checked. */
  private int[] residue;

  // Levels where edges were removed by node removals; their values must be checked for support.
  private int[] touchedLevels;
  private int touchedLevelsSize;
  private boolean[] levelTouched;

  /**
   * It constructs a layered graph constraint.
   *
   * @param list the variables of the levels, without duplicates.
   * @param queueIndex the queue of the constraint.
   */
  protected LayeredGraphConstraint(IntVar[] list, int queueIndex) {

    checkInputForNullness("list", list);
    checkInputForDuplicationSkipSingletons("list", list);

    this.queueIndex = queueIndex;
    this.list = Arrays.copyOf(list, list.length);
    setScope(list);
  }

  /**
   * The edges of a layered graph as described by a subclass. Nodes are numbered from 0 within each
   * level. Level 0 holds the sources and level {@code list.length} the accepting nodes; an edge of
   * level i connects a node of level i with a node of level i + 1 and is labelled with a value of
   * the i-th variable. Edges may be added in any order and labels need not be deterministic.
   */
  public static final class LayeredGraphDescription {

    final int[] levelNodes;

    // Four ints per edge: level, source, value and target.
    int[] edges = new int[256];

    int size;

    LayeredGraphDescription(int levels) {
      levelNodes = new int[levels + 1];
    }

    /**
     * It sets the number of nodes of a level.
     *
     * @param level the level, from 0 to the number of variables.
     * @param nodes the number of nodes of the level.
     */
    public void setNodes(int level, int nodes) {
      levelNodes[level] = nodes;
    }

    /**
     * It adds an edge.
     *
     * @param level the level of the edge, which is the position of its variable.
     * @param source the source node within the level.
     * @param value the value labelling the edge.
     * @param target the target node within the next level.
     */
    public void addEdge(int level, int source, int value, int target) {
      if (level < 0
          || level + 1 >= levelNodes.length
          || source < 0
          || source >= levelNodes[level]
          || target < 0
          || target >= levelNodes[level + 1]) {
        throw new IllegalArgumentException(
            "Edge " + source + " -> " + target + " of level " + level + " is outside the graph");
      }
      if (4 * size + 4 > edges.length) {
        edges = Arrays.copyOf(edges, 2 * edges.length);
      }
      edges[4 * size] = level;
      edges[4 * size + 1] = source;
      edges[4 * size + 2] = value;
      edges[4 * size + 3] = target;
      size++;
    }
  }

  /**
   * It describes the layered graph of this constraint. It is called once, when the constraint is
   * imposed. Edges labelled with values outside the current domains and nodes that are not on a
   * path from level 0 to the last level may be included; they are removed.
   *
   * @param graph the description to be filled.
   */
  protected abstract void describeGraph(LayeredGraphDescription graph);

  /**
   * Tells whether the paths of the graph are exactly the solutions, so that explanations by cuts of
   * the graph hold. A subclass that prunes by more than the paths returns false.
   *
   * @return true when this constraint is explained by its graph
   */
  protected boolean explainedByPaths() {
    return false;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    LayeredGraphExplanation.Graph graph = explanationGraph();
    return graph != null
        && new LayeredGraphExplanation(trail, list, graph, entry).explain(entry, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    LayeredGraphExplanation.Graph graph = explanationGraph();
    return graph != null
        && new LayeredGraphExplanation(trail, list, graph, trail.size()).explainFailure(out);
  }

  /**
   * Writes the graph with a literal per node and per edge: an edge implies its two nodes and its
   * value, a node needs an incoming and an outgoing edge, and each value of a variable needs an
   * edge of its level labelled with it. Unit propagation on them removes every edge that is on no
   * path, which is domain consistency. Only a deterministic graph with one source is written, so
   * that the values of a solution fix every literal by unit propagation.
   */
  @Override
  public boolean encode(PbModel model) {
    if (description != null && description.levelNodes[0] == 0) {
      // no path is left over the domains the graph was built from: the constraint fails
      model.clause();
      return true;
    }
    if (description == null || description.levelNodes[0] != 1) {
      return false;
    }
    return PbModel.layeredGraph(
        model, list, description.levelNodes, description.edges, description.size);
  }

  /**
   * Gives a lazy clause generation solver the graph over the current domains as clauses, so that it
   * propagates and explains this constraint by unit propagation instead of by cuts of the graph.
   * The edges between the same two nodes become one arc. There is a literal per node and per arc,
   * except where one stands for another: a level with one node has none, and an arc that is the
   * only one entering its target, or leaving its source, is that node. The clauses: an arc implies
   * its two nodes and one of its values; a node implies an arc entering it and an arc leaving it; a
   * value implies an arc of its level labelled with it; a node and a value imply an arc leaving the
   * node labelled with the value. Unit propagation then removes every value on no path (domain
   * consistency), and a solution fixes every literal.
   *
   * @param model where the clauses go
   * @return false when the paths of the graph are not exactly the solutions of the constraint
   */
  public boolean encodeClauses(ClauseModel model) {
    if (description == null || !explainedByPaths()) {
      return false;
    }
    new GraphClauses(model).encode();
    return true;
  }

  /**
   * It returns the size of the graph described when the constraint was imposed, its edges (one per
   * value of an edge label) and nodes: {@link #encodeClauses} makes at most one literal and four
   * clauses for each of them.
   *
   * @return the number of described edges and nodes, 0 before the constraint is imposed
   */
  public long describedSize() {
    if (description == null) {
      return 0;
    }
    long size = description.size;
    for (int n : description.levelNodes) {
      size += n;
    }
    return size;
  }

  /**
   * Attaches the constraint to its variables again after {@link #removeConstraint()}, at the level
   * where it was removed, when the clauses of {@link #encodeClauses} no longer stand for it, for
   * example when search without learning takes over from a lazy clause generation solver. Every
   * level is queued, so that the next consistency removes what the domains lost while the
   * constraint was detached.
   *
   * @param store the store the constraint was imposed in
   */
  public void restoreConstraint(Store store) {
    // above the root, removeConstraint only marked the constraint as entailed
    store.clearEntailed(this);
    for (Var v : arguments()) {
      // a variable fixed when the constraint was removed kept it
      if (!v.singleton()) {
        v.putModelConstraint(this, getSubscriptionPruningEvent(v));
      }
    }
    for (IntVar v : list) {
      queueVariable(store.level, v);
    }
    store.addChanged(this);
  }

  /**
   * Returns the edges of the graph over the current domains that lie on a path from level 0 to the
   * last level, four ints per edge: its level, its source node, its value and its target node, the
   * nodes numbered within their level as described. The linear relaxation states the flow model of
   * the graph over them (one unit of flow from level 0 to the last level, an arc column per edge,
   * and {@code [x_i = v]} as the flow over the edges of level i labelled v), whose solutions are
   * the paths (M.-C. Cote, B. Gendron and L.-M. Rousseau, "Modeling the regular constraint with
   * integer programming", CPAIOR 2007).
   *
   * @return the edges, or null when the paths of the graph are not exactly the solutions of the
   *     constraint or the graph is not built yet; the constraints of one shared graph over equal
   *     domains return the same array, which must not be changed
   */
  public int[] pathEdges() {
    if (description == null || !explainedByPaths()) {
      return null;
    }
    // the thousands of diagrams of one graph mostly see equal domains at the root (1,485 diagrams
    // of 1.8 million edges in WordDesign2-words-mdd-055, XCSP 2023)
    return built != null ? built.pathEdges(list, this::computePathEdges) : computePathEdges();
  }

  private int[] computePathEdges() {
    int levels = list.length;
    int[] edge = description.edges;
    PathNodes paths = new PathNodes();
    int[] first = paths.first;
    int[] levelEdges = paths.levelEdges;
    int[] order = paths.order;
    int[] fill = paths.fill;
    boolean[] kept = paths.kept;
    int[] out = new int[4 * description.size];
    int size = 0;
    for (int level = 0; level < levels; level++) {
      for (int k = levelEdges[level]; k < fill[level]; k++) {
        int e = order[k];
        if (kept[first[level] + edge[4 * e + 1]] && kept[first[level + 1] + edge[4 * e + 3]]) {
          System.arraycopy(edge, 4 * e, out, 4 * size++, 4);
        }
      }
    }
    return Arrays.copyOf(out, 4 * size);
  }

  /**
   * The usable edges of the graph over the current domains in level order, and the nodes on a path
   * from level 0 to the last level.
   */
  private final class PathNodes {
    // the index of the first node of each level among all nodes
    final int[] first;
    // the usable edges of level l are order[levelEdges[l]] to order[fill[l] - 1]
    final int[] levelEdges;
    final int[] order;
    final int[] fill;
    // the nodes on a path from level 0 to the last level
    final boolean[] kept;

    PathNodes() {
      int levels = list.length;
      int[] levelNodes = description.levelNodes;
      int[] edge = description.edges;
      first = new int[levels + 2];
      for (int level = 0; level <= levels; level++) {
        first[level + 1] = first[level] + levelNodes[level];
      }
      levelEdges = new int[levels + 1];
      for (int e = 0; e < description.size; e++) {
        levelEdges[edge[4 * e] + 1]++;
      }
      for (int level = 0; level < levels; level++) {
        levelEdges[level + 1] += levelEdges[level];
      }
      order = new int[description.size];
      fill = Arrays.copyOf(levelEdges, levels);
      for (int e = 0; e < description.size; e++) {
        int level = edge[4 * e];
        if (list[level].domain.contains(edge[4 * e + 2])) {
          order[fill[level]++] = e;
        }
      }
      boolean[] reached = new boolean[first[levels + 1]];
      kept = new boolean[first[levels + 1]];
      Arrays.fill(reached, 0, first[1], true);
      for (int level = 0; level < levels; level++) {
        for (int k = levelEdges[level]; k < fill[level]; k++) {
          int e = order[k];
          if (reached[first[level] + edge[4 * e + 1]]) {
            reached[first[level + 1] + edge[4 * e + 3]] = true;
          }
        }
      }
      System.arraycopy(reached, first[levels], kept, first[levels], levelNodes[levels]);
      for (int level = levels - 1; level >= 0; level--) {
        for (int k = levelEdges[level]; k < fill[level]; k++) {
          int e = order[k];
          int source = first[level] + edge[4 * e + 1];
          if (reached[source] && kept[first[level + 1] + edge[4 * e + 3]]) {
            kept[source] = true;
          }
        }
      }
    }
  }

  /** The clauses of {@link #encodeClauses}. */
  private final class GraphClauses {

    // the constant literals; a clause holding TRUE is dropped and FALSE is left out of a clause
    static final int TRUE = Integer.MAX_VALUE;
    static final int FALSE = -TRUE;

    final ClauseModel model;
    final int levels = list.length;
    final int[] edge = description.edges;
    int[] clause = new int[16];

    GraphClauses(ClauseModel model) {
      this.model = model;
    }

    void encode() {
      PathNodes paths = new PathNodes();
      int[] first = paths.first;
      int[] levelEdges = paths.levelEdges;
      int[] order = paths.order;
      int[] fill = paths.fill;
      boolean[] kept = paths.kept;

      // the arcs: the kept edges grouped by level, source and target
      int[] arcOf = new int[description.size];
      Arrays.fill(arcOf, -1);
      int[] arcLevel = new int[description.size];
      int[] arcSource = new int[description.size];
      int[] arcTarget = new int[description.size];
      int arcs = 0;
      int[] outDegree = new int[first[levels + 1]];
      int[] inDegree = new int[first[levels + 1]];
      Map<Long, Integer> arcIndex = new HashMap<>();
      for (int level = 0; level < levels; level++) {
        arcIndex.clear();
        for (int k = levelEdges[level]; k < fill[level]; k++) {
          int e = order[k];
          int source = first[level] + edge[4 * e + 1];
          int target = first[level + 1] + edge[4 * e + 3];
          arcOf[e] = -1;
          if (!kept[source] || !kept[target]) {
            continue;
          }
          long key = (long) source << 32 | target;
          Integer a = arcIndex.get(key);
          if (a == null) {
            a = arcs++;
            arcIndex.put(key, a);
            arcLevel[a] = level;
            arcSource[a] = source;
            arcTarget[a] = target;
            outDegree[source]++;
            inDegree[target]++;
          }
          arcOf[e] = a;
        }
      }

      // node literals: none for the only node of a level, which every path passes
      int[] node = new int[first[levels + 1]];
      boolean empty = false;
      for (int level = 0; level <= levels; level++) {
        int count = 0;
        for (int n = first[level]; n < first[level + 1]; n++) {
          count += kept[n] ? 1 : 0;
        }
        if (count == 0) {
          empty = true;
        }
        for (int n = first[level]; n < first[level + 1]; n++) {
          node[n] = !kept[n] ? FALSE : count == 1 ? TRUE : model.newLiteral();
        }
      }
      if (empty) {
        model.clause(clause, 0);
        return;
      }
      // a path starts at a node of level 0
      int size = 0;
      for (int n = first[0]; n < first[1]; n++) {
        if (kept[n]) {
          size = add(size, node[n]);
        }
      }
      emit(size);

      int[] arc = new int[arcs];
      for (int a = 0; a < arcs; a++) {
        if (inDegree[arcTarget[a]] == 1) {
          arc[a] = node[arcTarget[a]];
        } else if (outDegree[arcSource[a]] == 1) {
          arc[a] = node[arcSource[a]];
        } else {
          arc[a] = model.newLiteral();
        }
      }

      // the values of each arc, the arcs leaving and entering each node, the arcs of each value
      int[][] arcValues = collect(arcs, arcOf);
      int[][] leaving = adjacency(arcSource, outDegree, arcs);
      int[][] entering = adjacency(arcTarget, inDegree, arcs);

      for (int a = 0; a < arcs; a++) {
        emit(add(add(0, -arc[a]), node[arcSource[a]]));
        emit(add(add(0, -arc[a]), node[arcTarget[a]]));
        size = add(0, -arc[a]);
        for (int v : arcValues[a]) {
          size = add(size, valueLiteral(arcLevel[a], v));
        }
        emit(size);
      }
      for (int n = 0; n < first[levels + 1]; n++) {
        if (!kept[n]) {
          continue;
        }
        if (n < first[levels]) {
          size = add(0, -node[n]);
          for (int a : leaving[n]) {
            size = add(size, arc[a]);
          }
          emit(size);
        }
        if (n >= first[1]) {
          size = add(0, -node[n]);
          for (int a : entering[n]) {
            size = add(size, arc[a]);
          }
          emit(size);
        }
      }
      // a value needs an arc of its level labelled with it, and from a node, one leaving it
      int[][] labelled = new int[description.size][];
      for (int level = 0; level < levels; level++) {
        int m = 0;
        for (int k = levelEdges[level]; k < fill[level]; k++) {
          int e = order[k];
          if (arcOf[e] >= 0) {
            labelled[m++] = new int[] {edge[4 * e + 2], arcSource[arcOf[e]], arcOf[e]};
          }
        }
        Arrays.sort(
            labelled,
            0,
            m,
            (p, q) -> p[0] != q[0] ? Integer.compare(p[0], q[0]) : Integer.compare(p[1], q[1]));
        int i = 0;
        for (var it = list[level].domain.valueEnumeration(); it.hasMoreElements(); ) {
          int v = it.nextElement();
          while (i < m && labelled[i][0] < v) {
            i++;
          }
          int end = i;
          while (end < m && labelled[end][0] == v) {
            end++;
          }
          size = add(0, -valueLiteral(level, v));
          for (int k = i; k < end; k++) {
            size = add(size, arc[labelled[k][2]]);
          }
          emit(size);
          for (int k = i; k < end; ) {
            int source = labelled[k][1];
            int j = k;
            while (j < end && labelled[j][1] == source) {
              j++;
            }
            if (leaving[source].length > 1) {
              size = add(add(0, -node[source]), -valueLiteral(level, v));
              for (int r = k; r < j; r++) {
                size = add(size, arc[labelled[r][2]]);
              }
              emit(size);
            }
            k = j;
          }
          i = end;
        }
      }
    }

    /** The values of each arc, distinct, from the edges grouped into it. */
    private int[][] collect(int arcs, int[] arcOf) {
      int[] count = new int[arcs];
      for (int e = 0; e < description.size; e++) {
        if (arcOf[e] >= 0 && list[edge[4 * e]].domain.contains(edge[4 * e + 2])) {
          count[arcOf[e]]++;
        }
      }
      int[][] values = new int[arcs][];
      for (int a = 0; a < arcs; a++) {
        values[a] = new int[count[a]];
        count[a] = 0;
      }
      for (int e = 0; e < description.size; e++) {
        if (arcOf[e] >= 0 && list[edge[4 * e]].domain.contains(edge[4 * e + 2])) {
          values[arcOf[e]][count[arcOf[e]]++] = edge[4 * e + 2];
        }
      }
      return values;
    }

    private int[][] adjacency(int[] end, int[] degree, int arcs) {
      int[][] adj = new int[degree.length][];
      for (int n = 0; n < degree.length; n++) {
        adj[n] = new int[degree[n]];
        degree[n] = 0;
      }
      for (int a = 0; a < arcs; a++) {
        adj[end[a]][degree[end[a]]++] = a;
      }
      return adj;
    }

    private int valueLiteral(int level, int v) {
      IntVar x = list[level];
      return x.singleton() ? TRUE : model.valueLiteral(x, v);
    }

    /** Appends a literal to the clause being built and returns its new size. */
    private int add(int size, int literal) {
      if (size == clause.length) {
        clause = Arrays.copyOf(clause, 2 * size);
      }
      clause[size] = literal;
      return size + 1;
    }

    // clauses longer than this are cleared of duplicates by sorting, not pairwise
    private static final int SORT_FROM = 64;

    /** Adds the clause being built, without constants, duplicates and tautologies. */
    private void emit(int size) {
      int n = 0;
      if (size > SORT_FROM) {
        for (int k = 0; k < size; k++) {
          int l = clause[k];
          if (l == TRUE) {
            return;
          }
          if (l != FALSE) {
            clause[n++] = l;
          }
        }
        // the clause of a value lists every arc of its level labelled with it, hundreds of
        // thousands in the diagrams of WordDesign2-words-mdd (XCSP 2023)
        Arrays.sort(clause, 0, n);
        int m = 0;
        for (int k = 0; k < n; k++) {
          int l = clause[k];
          if (l < 0 && Arrays.binarySearch(clause, k + 1, n, -l) >= 0) {
            return;
          }
          if (m == 0 || clause[m - 1] != l) {
            clause[m++] = l;
          }
        }
        model.clause(clause, m);
        return;
      }
      for (int k = 0; k < size; k++) {
        int l = clause[k];
        if (l == TRUE) {
          return;
        }
        if (l == FALSE) {
          continue;
        }
        boolean seen = false;
        for (int j = 0; j < n; j++) {
          if (clause[j] == -l) {
            return;
          }
          seen |= clause[j] == l;
        }
        if (!seen) {
          clause[n++] = l;
        }
      }
      model.clause(clause, n);
    }
  }

  private LayeredGraphExplanation.Graph explanationGraph() {
    if (!explainedByPaths() || description == null) {
      return null;
    }
    if (explanationGraph == null) {
      explanationGraph = built.explanation();
    }
    return explanationGraph;
  }

  /**
   * The arrays of the support search that are only read during one call: the stamps of the nodes
   * with a path, of the values in the domains and of the supported values, and the count of
   * unsupported values per level. A store propagates one constraint at a time, so its constraints
   * on one built graph share them, each call with a stamp of its own.
   */
  static final class SearchScratch {
    final int[] yesStamp;
    final int[] inDomainStamp;
    final int[] supportedStamp;
    final int[] levelUnsupported;
    private int stamp;

    SearchScratch(int nodes, int slots, int levels) {
      yesStamp = new int[nodes];
      inDomainStamp = new int[slots];
      supportedStamp = new int[slots];
      levelUnsupported = new int[levels];
    }

    /** A stamp no node or slot carries yet. */
    int nextStamp() {
      if (++stamp == Integer.MAX_VALUE) {
        Arrays.fill(yesStamp, 0);
        Arrays.fill(inDomainStamp, 0);
        Arrays.fill(supportedStamp, 0);
        stamp = 1;
      }
      return stamp;
    }
  }

  /**
   * The layered graph built from a description over the domains of the levels when the constraint
   * was imposed: the kept nodes and edges, the slots and the static adjacency arrays. It is never
   * changed after it is built, so constraints with the same diagram over equal domains share it:
   * MiniZinc posts one MDD for every pair of words of WordDesign2-words-mdd-025 (XCSP 2023), 300
   * constraints on one diagram of 1.8 million edges, and a graph of their own for each of them did
   * not fit in 6 GB.
   */
  static final class BuiltGraph {
    final LayeredGraphDescription description;
    final int levels;
    final int nodes;
    final int slots;
    final int edges;
    final int[] levelNodeStart;
    final int[] levelSlotStart;
    final int[] slotValue;
    final int[] slotLevel;
    final int[] nodeLevel;
    final int[] outStart;
    final int[] outEdge;
    final int[] inStart;
    final int[] inEdge;
    final int[] slotStart;
    final int[] slotEdge;
    final int outBits;
    final int inBits;
    // the domains of the levels the graph was built over and the rest of the key it is shared by
    private final IntDomain[] domains;
    private final Object[] key;
    private LayeredGraphExplanation.Graph explanation;
    private final Map<Store, SearchScratch> scratches = new WeakHashMap<>();
    // the edges on a path last computed, over the domains they were computed over
    private IntDomain[] pathDomains;
    private int[] pathEdges;

    /**
     * It builds the graph. Edges with values outside the domains are dropped, a forward and a
     * backward pass keep the nodes on a path from level 0 to the last level, and the static
     * adjacency arrays are created. All work is proportional to the size of the description.
     */
    BuiltGraph(LayeredGraphDescription description, IntDomain[] domains, Object[] key) {
      this.description = description;
      this.domains = domains;
      this.key = key;
      levels = domains.length;
      final int[] edge = description.edges;
      final int described = description.size;

      // Edges in level order, keeping the order of description within a level.
      int[] levelEdgeStart = new int[levels + 1];
      for (int e = 0; e < described; e++) {
        levelEdgeStart[edge[4 * e] + 1]++;
      }
      for (int level = 0; level < levels; level++) {
        levelEdgeStart[level + 1] += levelEdgeStart[level];
      }
      int[] order = new int[described];
      int[] fill = Arrays.copyOf(levelEdgeStart, levels);
      for (int e = 0; e < described; e++) {
        int level = edge[4 * e];
        if (domains[level].contains(edge[4 * e + 2])) {
          order[fill[level]++] = e;
        }
      }
      // fill[level] now ends the usable edges of each level.

      int[] describedStart = new int[levels + 2];
      for (int level = 0; level <= levels; level++) {
        describedStart[level + 1] = describedStart[level] + description.levelNodes[level];
      }
      boolean[] reached = new boolean[describedStart[levels + 1]];
      boolean[] kept = new boolean[describedStart[levels + 1]];
      Arrays.fill(reached, 0, describedStart[1], true);
      for (int level = 0; level < levels; level++) {
        for (int i = levelEdgeStart[level]; i < fill[level]; i++) {
          int e = order[i];
          if (reached[describedStart[level] + edge[4 * e + 1]]) {
            reached[describedStart[level + 1] + edge[4 * e + 3]] = true;
          }
        }
      }
      for (int n = describedStart[levels]; n < describedStart[levels + 1]; n++) {
        kept[n] = reached[n];
      }
      for (int level = levels - 1; level >= 0; level--) {
        for (int i = levelEdgeStart[level]; i < fill[level]; i++) {
          int e = order[i];
          int src = describedStart[level] + edge[4 * e + 1];
          if (reached[src] && kept[describedStart[level + 1] + edge[4 * e + 3]]) {
            kept[src] = true;
          }
        }
      }

      // Kept nodes get consecutive ids, level by level; kept edges are the usable edges between
      // them.
      int[] nodeId = new int[describedStart[levels + 1]];
      levelNodeStart = new int[levels + 2];
      int nodeCount = 0;
      for (int level = 0; level <= levels; level++) {
        levelNodeStart[level] = nodeCount;
        for (int n = describedStart[level]; n < describedStart[level + 1]; n++) {
          nodeId[n] = kept[n] ? nodeCount++ : -1;
        }
      }
      levelNodeStart[levels + 1] = nodeCount;
      nodes = nodeCount;
      int keptEdges = 0;
      int[] keptStart = new int[levels + 1];
      for (int level = 0; level < levels; level++) {
        keptStart[level] = keptEdges;
        for (int i = levelEdgeStart[level]; i < fill[level]; i++) {
          int e = order[i];
          if (kept[describedStart[level] + edge[4 * e + 1]]
              && kept[describedStart[level + 1] + edge[4 * e + 3]]) {
            order[keptEdges++] = e;
          }
        }
      }
      keptStart[levels] = keptEdges;

      // Slots: the values labelling edges of each level.
      levelSlotStart = new int[levels + 1];
      int[][] levelValues = new int[levels][];
      for (int level = 0; level < levels; level++) {
        int[] values = new int[keptStart[level + 1] - keptStart[level]];
        for (int i = 0; i < values.length; i++) {
          values[i] = edge[4 * order[keptStart[level] + i] + 2];
        }
        Arrays.sort(values);
        int k = 0;
        for (int i = 0; i < values.length; i++) {
          if (k == 0 || values[k - 1] != values[i]) {
            values[k++] = values[i];
          }
        }
        levelValues[level] = Arrays.copyOf(values, k);
        levelSlotStart[level + 1] = levelSlotStart[level] + k;
      }
      slots = levelSlotStart[levels];
      slotValue = new int[slots];
      slotLevel = new int[slots];
      for (int level = 0; level < levels; level++) {
        System.arraycopy(
            levelValues[level], 0, slotValue, levelSlotStart[level], levelValues[level].length);
        Arrays.fill(slotLevel, levelSlotStart[level], levelSlotStart[level + 1], level);
      }

      // Kept edges as global source, slot and target.
      edges = keptEdges;
      int[] edgeSource = new int[edges];
      int[] edgeSlot = new int[edges];
      int[] edgeTarget = new int[edges];
      for (int level = 0; level < levels; level++) {
        for (int i = keptStart[level]; i < keptStart[level + 1]; i++) {
          int e = order[i];
          edgeSource[i] = nodeId[describedStart[level] + edge[4 * e + 1]];
          edgeTarget[i] = nodeId[describedStart[level + 1] + edge[4 * e + 3]];
          edgeSlot[i] =
              levelSlotStart[level] + Arrays.binarySearch(levelValues[level], edge[4 * e + 2]);
        }
      }

      // Count edges per node and per slot.
      int[] outCount = new int[nodes + 1];
      int[] inCount = new int[nodes + 1];
      int[] slotCount = new int[slots + 1];
      for (int e = 0; e < edges; e++) {
        outCount[edgeSource[e]]++;
        inCount[edgeTarget[e]]++;
        slotCount[edgeSlot[e]]++;
      }
      int maxOut = 1;
      int maxIn = 1;
      for (int n = 0; n < nodes; n++) {
        maxOut = Math.max(maxOut, outCount[n]);
        maxIn = Math.max(maxIn, inCount[n]);
      }
      outBits = 32 - Integer.numberOfLeadingZeros(maxOut);
      inBits = 32 - Integer.numberOfLeadingZeros(maxIn);

      outStart = segmentStarts(outCount);
      inStart = segmentStarts(inCount);
      slotStart = segmentStarts(slotCount);
      outEdge = new int[2 * edges];
      inEdge = new int[2 * edges];
      slotEdge = new int[2 * edges];
      int[] slotFill = new int[slots];
      int[] outFill = new int[nodes];
      int[] inFill = new int[nodes];
      for (int e = 0; e < edges; e++) {
        int src = edgeSource[e];
        int dst = edgeTarget[e];
        int slot = edgeSlot[e];
        int o = outStart[src] + outFill[src]++;
        outEdge[2 * o] = dst;
        outEdge[2 * o + 1] = slot;
        int in = inStart[dst] + inFill[dst]++;
        inEdge[2 * in] = src;
        inEdge[2 * in + 1] = slot;
        int se = slotStart[slot] + slotFill[slot]++;
        slotEdge[2 * se] = src;
        slotEdge[2 * se + 1] = dst;
      }

      nodeLevel = new int[nodes];
      for (int level = 0; level <= levels; level++) {
        Arrays.fill(nodeLevel, levelNodeStart[level], levelNodeStart[level + 1], level);
      }
    }

    /**
     * Returns the edges on a path over the domains of the list, computed again only when they
     * differ from the domains of the last call.
     */
    synchronized int[] pathEdges(IntVar[] list, Supplier<int[]> compute) {
      boolean same = pathDomains != null && pathDomains.length == list.length;
      for (int i = 0; same && i < list.length; i++) {
        same = pathDomains[i].eq(list[i].domain);
      }
      if (!same) {
        pathEdges = compute.get();
        pathDomains = new IntDomain[list.length];
        for (int i = 0; i < list.length; i++) {
          pathDomains[i] = list[i].domain.cloneLight();
        }
      }
      return pathEdges;
    }

    /** The stamps of the support search for the constraints of a store on this graph. */
    synchronized SearchScratch scratch(Store store) {
      return scratches.computeIfAbsent(store, s -> new SearchScratch(nodes, slots, levels));
    }

    /** The graph for explanations by cuts, made once for all constraints sharing this graph. */
    synchronized LayeredGraphExplanation.Graph explanation() {
      if (explanation == null) {
        explanation = new LayeredGraphExplanation.Graph(description);
      }
      return explanation;
    }

    /** Whether this graph was built for the given key over equal domains. */
    boolean builtFor(Object[] otherKey, IntDomain[] otherDomains) {
      if (otherKey.length != key.length || otherDomains.length != domains.length) {
        return false;
      }
      for (int i = 0; i < key.length; i++) {
        if (otherKey[i] != key[i]) {
          return false;
        }
      }
      for (int i = 0; i < domains.length; i++) {
        if (!domains[i].eq(otherDomains[i])) {
          return false;
        }
      }
      return true;
    }
  }

  // Built graphs by the first object of their key (see sharedGraphKey). The key objects are held
  // by the constraints, so a graph is kept while a constraint that may share it is alive. Guarded
  // by itself, as the workers of a parallel search impose their copies at the same time.
  private static final Map<Object, List<BuiltGraph>> BUILT_GRAPHS = new WeakHashMap<>();

  /**
   * Identifies the diagram this constraint describes, so that constraints with the same diagram
   * over equal domains share one built graph. Two constraints whose keys hold the same objects
   * (compared by identity, element by element) must describe the same graph. The objects must be
   * held by the constraint and the first one must not be reachable from the others.
   *
   * @return the key, or null when the graph is not shared
   */
  protected Object[] sharedGraphKey() {
    return null;
  }

  /** Statistics: the graphs taken from another constraint with the same diagram. */
  private static final AtomicLong sharedGraphs = new AtomicLong();

  /**
   * It returns how many constraints took the graph built for another constraint with the same
   * diagram instead of building their own.
   *
   * @return the number of shared graphs since the start
   */
  public static long sharedGraphs() {
    return sharedGraphs.get();
  }

  /**
   * It builds the layered graph from its description over the current domains, or takes the one
   * built for another constraint with the same diagram over equal domains, and creates the
   * backtrackable state of this constraint.
   */
  private void buildLayeredGraph(Store store) {
    int levels = list.length;
    IntDomain[] domains = new IntDomain[levels];
    for (int level = 0; level < levels; level++) {
      domains[level] = list[level].domain.cloneLight();
    }
    Object[] key = sharedGraphKey();
    BuiltGraph built = key == null ? null : sharedGraph(key, domains);
    if (built == null) {
      LayeredGraphDescription localDescription = new LayeredGraphDescription(levels);
      describeGraph(localDescription);
      built = new BuiltGraph(localDescription, domains, key == null ? new Object[0] : key);
      if (key != null) {
        synchronized (BUILT_GRAPHS) {
          BUILT_GRAPHS.computeIfAbsent(key[0], k -> new ArrayList<>(1)).add(built);
        }
      }
    } else {
      sharedGraphs.incrementAndGet();
    }
    installGraph(built, store);
  }

  /**
   * It tells whether this constraint uses the graph built for the other one, or the other way
   * round, after both were imposed.
   *
   * @param other another layered graph constraint
   * @return true when both constraints use one built graph
   */
  public boolean sharesGraphWith(LayeredGraphConstraint other) {
    return built != null && built == other.built;
  }

  private static BuiltGraph sharedGraph(Object[] key, IntDomain[] domains) {
    synchronized (BUILT_GRAPHS) {
      List<BuiltGraph> graphs = BUILT_GRAPHS.get(key[0]);
      if (graphs != null) {
        for (BuiltGraph g : graphs) {
          if (g.builtFor(key, domains)) {
            return g;
          }
        }
      }
      return null;
    }
  }

  // The bytes that the counters of one node take: its record and its lists in the state, about
  // two saved records on the trail along a branch, and the scratch of a recount.
  private static final long COUNTER_BYTES_PER_NODE = 64;

  // The share of the heap that the counters of the layered graphs of one store may take.
  private static final double COUNTER_HEAP_SHARE = 0.25;

  // The bytes taken by the counters of the layered graphs of each store, guarded by itself.
  private static final Map<Store, long[]> COUNTER_BYTES = new WeakHashMap<>();

  /**
   * Whether the counters of a graph fit in the share of the heap left to the counters of the store,
   * which then takes them. Each constraint keeps its own counters, and their trail grows with the
   * nodes removed along a branch: the 300 diagrams of 525,720 nodes of WordDesign2-words-mdd-025
   * (XCSP 2023) need more than 6 GB for them. Past the share, the automatic choice takes support
   * search, which keeps a stamp and a position per node and saves one record per call.
   */
  private static boolean countersFit(Store store, int nodes, int slots) {
    long need = COUNTER_BYTES_PER_NODE * nodes + 16L * slots;
    long budget = (long) (COUNTER_HEAP_SHARE * Runtime.getRuntime().maxMemory());
    synchronized (COUNTER_BYTES) {
      long[] used = COUNTER_BYTES.computeIfAbsent(store, s -> new long[1]);
      if (used[0] + need > budget) {
        return false;
      }
      used[0] += need;
      return true;
    }
  }

  /** It takes the static arrays of a built graph and creates the state of this constraint. */
  private void installGraph(BuiltGraph built, Store store) {
    this.built = built;
    int levels = list.length;
    this.description = built.description;
    int nodes = built.nodes;
    int slots = built.slots;
    levelNodeStart = built.levelNodeStart;
    levelSlotStart = built.levelSlotStart;
    slotValue = built.slotValue;
    slotLevel = built.slotLevel;
    nodeLevel = built.nodeLevel;
    edges = built.edges;
    aliveEdges = edges;
    outStart = built.outStart;
    outEdge = built.outEdge;
    inStart = built.inStart;
    inEdge = built.inEdge;
    slotStart = built.slotStart;
    slotEdge = built.slotEdge;

    nodeCount = nodes;
    slotCount = slots;
    emptySlots = new int[Math.max(1, slots)];
    residue = Arrays.copyOf(slotStart, slots);
    adjacency[0] = saveAdjacency(new Adjacency(), -1);
    adjacencyTop = 1;
    touchedLevels = new int[levels];
    levelTouched = new boolean[levels];
    Engine chosen = resolveEngine();
    if (chosen == Engine.AUTO && !countersFit(store, nodes, slots)) {
      chosen = Engine.SUPPORT_SEARCH;
    }
    supportSearch = chosen == Engine.SUPPORT_SEARCH;
    probing = chosen == Engine.AUTO;
    if (supportSearch) {
      // Support search from the start never reads the counters: its only records are the alive
      // edges, restored by removeLevel, and the size of the set of nodes without support.
      edgeRecord = 0;
      noRecord = 1;
      slotBase = -1;
      levelBase = -1;
      aliveBase = -1;
      state = new long[2];
      state[edgeRecord] = edges;
      return;
    }

    slotBase = nodes;
    levelBase = nodes + slots;
    edgeRecord = levelBase + levels;
    aliveBase = edgeRecord + 1;
    noRecord = aliveBase + levels + 1;
    state = new long[noRecord + 1];
    for (int level = 0; level < levels; level++) {
      state[levelBase + level] = (long) levelSlotStart[level + 1] - levelSlotStart[level];
    }
    state[edgeRecord] = edges;
    for (int slot = 0; slot < slots; slot++) {
      state[slotBase + slot] = 1;
    }
    int outBits = built.outBits;
    int inBits = built.inBits;
    if (outBits + inBits > STAMP_SHIFT) {
      throw new IllegalArgumentException(
          getClass().getSimpleName() + ": too many edges per node in the layered graph");
    }
    outMask = (1L << outBits) - 1;
    inShift = outBits;
    inOne = 1L << outBits;
    inMask = ((1L << inBits) - 1) << outBits;
    for (int n = 0; n < nodes; n++) {
      state[n] =
          ((long) (inStart[n + 1] - inStart[n]) << outBits) | (outStart[n + 1] - outStart[n]);
    }
    layeredRemoval = nodes > LAYERED_REMOVAL_NODES;
    if (layeredRemoval) {
      forwardHead = new int[levels + 1];
      backwardHead = new int[levels + 1];
      Arrays.fill(forwardHead, -1);
      Arrays.fill(backwardHead, -1);
      forwardNext = new int[nodes];
      backwardNext = new int[nodes];
      forwardLevels = new long[(levels >> 6) + 1];
      backwardLevels = new long[(levels >> 6) + 1];
      levelOrder = new int[nodes];
      orderPosition = new int[nodes];
      for (int n = 0; n < nodes; n++) {
        levelOrder[n] = n;
        orderPosition[n] = n;
      }
      for (int level = 0; level <= levels; level++) {
        state[aliveBase + level] = (long) levelNodeStart[level + 1] - levelNodeStart[level];
      }
      removedSlotHead = new int[levels];
      Arrays.fill(removedSlotHead, -1);
      removedSlotNext = new int[slots];
    }
  }

  private static int[] segmentStarts(int[] counts) {
    int[] start = new int[counts.length];
    int position = 0;
    for (int i = 0; i < counts.length; i++) {
      start[i] = position;
      position += counts[i];
    }
    return start;
  }

  private Adjacency saveAdjacency(Adjacency a, int level) {
    a.level = level;
    a.edges = edges;
    a.outStart = outStart;
    a.outEdge = outEdge;
    a.inStart = inStart;
    a.inEdge = inEdge;
    a.slotStart = slotStart;
    a.slotEdge = slotEdge;
    a.residue = residue;
    return a;
  }

  private void loadAdjacency(Adjacency a) {
    edges = a.edges;
    outStart = a.outStart;
    outEdge = a.outEdge;
    inStart = a.inStart;
    inEdge = a.inEdge;
    slotStart = a.slotStart;
    slotEdge = a.slotEdge;
    residue = a.residue;
  }

  private static int[] reuse(int[] array, int length) {
    return array != null && array.length >= length ? array : new int[length];
  }

  /**
   * It replaces the adjacency arrays with arrays holding only the alive edges, valid until the
   * given store level is removed. Arrays made earlier at the same stack depth are reused.
   */
  private void compact(int level) {
    if (adjacencyTop == adjacency.length) {
      adjacency = Arrays.copyOf(adjacency, adjacencyTop * 2);
    }
    Adjacency a = adjacency[adjacencyTop];
    if (a == null) {
      a = new Adjacency();
      adjacency[adjacencyTop] = a;
    }
    int nodes = nodeCount;
    int slots = slotCount;
    int[] newOutStart = reuse(a.outStart, nodes + 1);
    int[] newOutEdge = reuse(a.outEdge, 2 * aliveEdges);
    int[] newInStart = reuse(a.inStart, nodes + 1);
    int[] newInEdge = reuse(a.inEdge, 2 * aliveEdges);
    int[] newSlotStart = reuse(a.slotStart, slots + 1);
    int[] newSlotEdge = reuse(a.slotEdge, 2 * aliveEdges);
    int[] newResidue = reuse(a.residue, slots);

    int o = 0;
    int in = 0;
    for (int node = 0; node < nodes; node++) {
      newOutStart[node] = o;
      newInStart[node] = in;
      if (!alive(node)) {
        continue;
      }
      for (int e = outStart[node]; e < outStart[node + 1]; e++) {
        int dst = outEdge[2 * e];
        int slot = outEdge[2 * e + 1];
        if (alive(dst) && slotAlive(slot)) {
          newOutEdge[2 * o] = dst;
          newOutEdge[2 * o++ + 1] = slot;
        }
      }
      for (int e = inStart[node]; e < inStart[node + 1]; e++) {
        int src = inEdge[2 * e];
        int slot = inEdge[2 * e + 1];
        if (alive(src) && slotAlive(slot)) {
          newInEdge[2 * in] = src;
          newInEdge[2 * in++ + 1] = slot;
        }
      }
    }
    newOutStart[nodes] = o;
    newInStart[nodes] = in;
    int s = 0;
    for (int slot = 0; slot < slots; slot++) {
      newSlotStart[slot] = s;
      newResidue[slot] = s;
      if (!slotAlive(slot)) {
        continue;
      }
      for (int e = slotStart[slot]; e < slotStart[slot + 1]; e++) {
        int src = slotEdge[2 * e];
        int dst = slotEdge[2 * e + 1];
        if (alive(src) && alive(dst)) {
          newSlotEdge[2 * s] = src;
          newSlotEdge[2 * s++ + 1] = dst;
        }
      }
    }
    newSlotStart[slots] = s;
    assert o == aliveEdges && in == aliveEdges && s == aliveEdges;

    outStart = newOutStart;
    outEdge = newOutEdge;
    inStart = newInStart;
    inEdge = newInEdge;
    slotStart = newSlotStart;
    slotEdge = newSlotEdge;
    residue = newResidue;
    edges = aliveEdges;
    saveAdjacency(a, level);
    adjacencyTop++;
  }

  /** It saves a record on the trail unless it was saved in the current epoch already. */
  private void save(int rec) {
    long s = state[rec];
    if ((int) (s >>> STAMP_SHIFT & STAMP_MASK) == epoch) {
      return;
    }
    state[rec] = s & ~((long) STAMP_MASK << STAMP_SHIFT) | (long) epoch << STAMP_SHIFT;
    if (markTop == 0 || markLevel[markTop - 1] != currentLevel) {
      if (markTop == markLevel.length) {
        markLevel = Arrays.copyOf(markLevel, markTop * 2);
        markPosition = Arrays.copyOf(markPosition, markTop * 2);
      }
      markLevel[markTop] = currentLevel;
      markPosition[markTop++] = trailTop;
    }
    if (trailTop + 2 > trail.length) {
      trail = Arrays.copyOf(trail, trail.length * 2);
    }
    trail[trailTop] = rec;
    trail[trailTop + 1] = s;
    trailTop += 2;
  }

  private boolean alive(int node) {
    return state[node] >= 0;
  }

  private boolean slotAlive(int slot) {
    return (state[slotBase + slot] & VALUE) != 0;
  }

  /** It decrements the number of outgoing edges of a node. */
  private void decrementOut(int node) {
    save(node);
    long s = state[node] - 1;
    state[node] = s;
    if ((s & outMask) == 0) {
      if (!layeredRemoval) {
        pushDeadNode(node);
        return;
      }
      pushBackward(node);
    }
  }

  private void pushBackward(int node) {
    int level = nodeLevel[node];
    backwardNext[node] = backwardHead[level];
    backwardHead[level] = node;
    backwardLevels[level >> 6] |= 1L << level;
  }

  private void pushForward(int node) {
    int level = nodeLevel[node];
    forwardNext[node] = forwardHead[level];
    forwardHead[level] = node;
    forwardLevels[level >> 6] |= 1L << level;
  }

  /** It decrements the number of incoming edges of a node. */
  private void decrementIn(int node) {
    save(node);
    long s = state[node] - inOne;
    state[node] = s;
    if ((s & inMask) == 0) {
      if (!layeredRemoval) {
        pushDeadNode(node);
        return;
      }
      pushForward(node);
    }
  }

  private void touchLevel(int level) {
    if (!levelTouched[level]) {
      levelTouched[level] = true;
      touchedLevels[touchedLevelsSize++] = level;
    }
  }

  /**
   * It checks whether a value of a level still labels an alive edge. The search starts at the edge
   * found last time (a residue, which needs no trailing) and wraps around.
   */
  private boolean hasSupport(int slot) {
    int start = slotStart[slot];
    int end = slotStart[slot + 1];
    int r = residue[slot];
    for (int e = r; e < end; e++) {
      if (alive(slotEdge[2 * e]) && alive(slotEdge[2 * e + 1])) {
        residue[slot] = e;
        return true;
      }
    }
    for (int e = start; e < r; e++) {
      if (alive(slotEdge[2 * e]) && alive(slotEdge[2 * e + 1])) {
        residue[slot] = e;
        return true;
      }
    }
    return false;
  }

  /** It removes the values of touched levels that no longer label an alive edge. */
  private void checkTouchedLevels() {
    for (int i = 0; i < touchedLevelsSize; i++) {
      int level = touchedLevels[i];
      levelTouched[level] = false;
      for (int slot = levelSlotStart[level]; slot < levelSlotStart[level + 1]; slot++) {
        if (slotAlive(slot) && !hasSupport(slot)) {
          int rec = slotBase + slot;
          save(rec);
          state[rec] &= ~VALUE;
          emptySlots[emptySlotsSize++] = slot;
          removedSlotOfLevel(level);
        }
      }
    }
    touchedLevelsSize = 0;
  }

  /**
   * It records that a level lost one of its values. A level without values means that no word is
   * accepted, so the constraint fails at once instead of removing the rest of the graph.
   */
  private void removedSlotOfLevel(int level) {
    int rec = levelBase + level;
    save(rec);
    if ((--state[rec] & VALUE) == 0) {
      throw Store.failException;
    }
  }

  /** It removes a value of a level, together with all alive edges labelled with it. */
  private void removeSlot(int slot) {
    int rec = slotBase + slot;
    save(rec);
    state[rec] &= ~VALUE;
    removedSlotOfLevel(slotLevel[slot]);
    removeSlotEdges(slot);
  }

  /** It removes a value of a level and leaves its edges to the forward pass. */
  private void deferSlot(int slot) {
    int rec = slotBase + slot;
    save(rec);
    state[rec] &= ~VALUE;
    int level = slotLevel[slot];
    removedSlotOfLevel(level);
    removedSlotNext[slot] = removedSlotHead[level];
    removedSlotHead[level] = slot;
    forwardLevels[level >> 6] |= 1L << level;
  }

  /** It removes the alive edges of a removed value. */
  private void removeSlotEdges(int slot) {
    wastedVisits += (long) slotStart[slot + 1] - slotStart[slot];
    for (int e = slotStart[slot]; e < slotStart[slot + 1]; e++) {
      int src = slotEdge[2 * e];
      int dst = slotEdge[2 * e + 1];
      if (alive(src) && alive(dst)) {
        decrementOut(src);
        decrementIn(dst);
        aliveEdges--;
        wastedVisits--;
      }
    }
  }

  /**
   * It removes the nodes that lost all their incoming or all their outgoing edges. Their remaining
   * alive edges are removed too, which may remove further nodes and leave values without support.
   */
  private void pushDeadNode(int node) {
    if (deadNodesSize == deadNodes.length) {
      deadNodes = Arrays.copyOf(deadNodes, deadNodesSize * 2);
    }
    deadNodes[deadNodesSize++] = node;
  }

  private void removeDeadNodes() {
    if (!layeredRemoval) {
      while (deadNodesSize > 0) {
        removeNode(deadNodes[--deadNodesSize]);
      }
      return;
    }
    // Removing a node of level l adds nodes of level l + 1 only, which the forward loop reaches
    // later; the backward pass is symmetric. Only levels with nodes to remove are visited. The
    // forward step of level l handles the removed values of level l and the nodes of level l that
    // lost all their incoming edges, so it changes only the edges of level l. When visiting the
    // edges these remove would cost more than counting the alive edges of the level anew, the
    // counters of the level are recounted instead, as the reset of MDD4R does. This keeps the work
    // proportional to what stays alive when a decision removes most of a level, as an assignment
    // does in a diagram built from a table, where a removed node takes its whole subtree along.
    int levels = list.length;
    for (int level = nextLevel(forwardLevels, 0);
        level >= 0;
        level = nextLevel(forwardLevels, level)) {
      forwardLevels[level >> 6] &= ~(1L << level);
      int node = forwardHead[level];
      forwardHead[level] = -1;
      int slot = -1;
      if (level < levels) {
        slot = removedSlotHead[level];
        removedSlotHead[level] = -1;
        if (recountIsCheaper(level, node, slot, aliveNodes(level + 1))) {
          for (; node >= 0; node = forwardNext[node]) {
            removeWithoutEdges(node);
          }
          recountForward(level);
          continue;
        }
      }
      for (; slot >= 0; slot = removedSlotNext[slot]) {
        removeSlotEdges(slot);
      }
      for (; node >= 0; node = forwardNext[node]) {
        removeNode(node);
      }
    }
    for (int level = previousLevel(backwardLevels, levels);
        level >= 0;
        level = previousLevel(backwardLevels, level)) {
      backwardLevels[level >> 6] &= ~(1L << level);
      int node = backwardHead[level];
      backwardHead[level] = -1;
      if (level > 0 && recountIsCheaper(level - 1, node)) {
        for (; node >= 0; node = backwardNext[node]) {
          removeWithoutEdges(node);
        }
        recountBackward(level - 1);
        continue;
      }
      for (; node >= 0; node = backwardNext[node]) {
        removeNode(node);
      }
    }
  }

  private int aliveNodes(int level) {
    return (int) (state[aliveBase + level] & VALUE);
  }

  /**
   * It checks whether, in the forward step of a level, recounting the edges of the nodes that stay
   * alive costs less than visiting the edges of the removed values and of the removed nodes.
   */
  private boolean recountIsCheaper(int level, int deadNodes, int removedSlots, long extra) {
    long removal = 0;
    long deadPart = 0;
    for (int slot = removedSlots; slot >= 0; slot = removedSlotNext[slot]) {
      removal += slotStart[slot + 1] - slotStart[slot];
    }
    for (int node = deadNodes; node >= 0; node = forwardNext[node]) {
      int degree = outStart[node + 1] - outStart[node];
      removal += degree;
      deadPart += 1 + degree;
    }
    return !outDegreesExceed(level, removal + deadPart - extra);
  }

  /**
   * It checks whether, in the backward step of a level, recounting the edges of the nodes of the
   * previous level costs less than visiting the incoming edges of the removed nodes.
   */
  private boolean recountIsCheaper(int previousLevel, int deadNodes) {
    long removal = 0;
    for (int node = deadNodes; node >= 0; node = backwardNext[node]) {
      removal += inStart[node + 1] - inStart[node];
    }
    return !outDegreesExceed(previousLevel, removal);
  }

  /** It checks whether the alive nodes of a level and their outgoing edges are more than limit. */
  private boolean outDegreesExceed(int level, long limit) {
    long cost = 0;
    int from = levelNodeStart[level];
    int end = from + aliveNodes(level);
    for (int i = from; i < end; i++) {
      int u = levelOrder[i];
      cost += 1 + outStart[u + 1] - outStart[u];
      if (cost > limit) {
        return true;
      }
    }
    return false;
  }

  /** It removes a node without visiting its edges, which are recounted afterwards. */
  private void removeWithoutEdges(int node) {
    if (alive(node)) {
      save(node);
      state[node] |= REMOVED;
      removeAlive(node);
    }
  }

  /** It removes a node from the alive nodes of its level. */
  private void removeAlive(int node) {
    int level = nodeLevel[node];
    int rec = aliveBase + level;
    save(rec);
    int last = levelNodeStart[level] + (int) (state[rec] & VALUE) - 1;
    state[rec]--;
    int position = orderPosition[node];
    int other = levelOrder[last];
    levelOrder[position] = other;
    orderPosition[other] = position;
    levelOrder[last] = node;
    orderPosition[node] = last;
  }

  /**
   * It recounts the outgoing edges of the alive nodes of a level and the incoming edges of the
   * alive nodes of the next level, visiting only the outgoing edges of the alive nodes. Nodes whose
   * count drops to zero are queued for removal.
   */
  private void recountForward(int level) {
    touchLevel(level);
    int to = levelNodeStart[level + 1];
    int toEnd = to + aliveNodes(level + 1);
    long before = 0;
    if (previousCount == null) {
      // scratch of this call only, made at the first recount: many large graphs never need it
      previousCount = new int[nodeCount];
    }
    for (int i = to; i < toEnd; i++) {
      int v = levelOrder[i];
      save(v);
      long in = (state[v] & inMask) >>> inShift;
      previousCount[v] = (int) in;
      before += in;
      state[v] &= ~inMask;
    }
    long counted = recountOut(level, true);
    aliveEdges -= (int) (before - counted);
    for (int i = to; i < toEnd; i++) {
      int v = levelOrder[i];
      if (previousCount[v] != 0 && (state[v] & inMask) == 0) {
        pushForward(v);
      }
    }
  }

  /**
   * It recounts the outgoing edges of the alive nodes of a level after nodes of the next level were
   * removed. Nodes whose count drops to zero are queued for removal.
   */
  private void recountBackward(int level) {
    touchLevel(level);
    int from = levelNodeStart[level];
    int end = from + aliveNodes(level);
    long before = 0;
    for (int i = from; i < end; i++) {
      before += state[levelOrder[i]] & outMask;
    }
    long counted = recountOut(level, false);
    aliveEdges -= (int) (before - counted);
  }

  /**
   * It sets the number of outgoing edges of each alive node of a level to its alive edges, and
   * increments the incoming count of their targets if asked to. Nodes whose outgoing count drops to
   * zero are queued for removal. It returns the number of alive edges of the level.
   */
  private long recountOut(int level, boolean countIn) {
    int from = levelNodeStart[level];
    int end = from + aliveNodes(level);
    long counted = 0;
    long visited = 0;
    for (int i = from; i < end; i++) {
      int u = levelOrder[i];
      long out = 0;
      int edgeEnd = outStart[u + 1];
      visited += edgeEnd - outStart[u];
      for (int e = outStart[u]; e < edgeEnd; e++) {
        int dst = outEdge[2 * e];
        if (slotAlive(outEdge[2 * e + 1]) && alive(dst)) {
          out++;
          if (countIn) {
            state[dst] += inOne;
          }
        }
      }
      counted += out;
      long previous = state[u] & outMask;
      if (previous != out) {
        save(u);
        state[u] = state[u] & ~outMask | out;
        if (out == 0) {
          pushBackward(u);
        }
      }
    }
    wastedVisits += visited - counted;
    return counted;
  }

  /** It returns the smallest level at least from with its bit set, or -1. */
  private static int nextLevel(long[] levels, int from) {
    int word = from >> 6;
    if (word >= levels.length) {
      return -1;
    }
    long bits = levels[word] & -1L << from;
    while (bits == 0) {
      if (++word == levels.length) {
        return -1;
      }
      bits = levels[word];
    }
    return (word << 6) + Long.numberOfTrailingZeros(bits);
  }

  /** It returns the largest level at most from with its bit set, or -1. */
  private static int previousLevel(long[] levels, int from) {
    int word = from >> 6;
    long bits = levels[word] & -1L >>> (63 - (from & 63));
    while (bits == 0) {
      if (--word < 0) {
        return -1;
      }
      bits = levels[word];
    }
    return (word << 6) + 63 - Long.numberOfLeadingZeros(bits);
  }

  private void removeNode(int node) {
    if (!alive(node)) {
      return;
    }
    // A node is removed because one of its counts dropped to zero, so only the other side can
    // still have alive edges.
    boolean scanOut = (state[node] & outMask) != 0;
    boolean scanIn = (state[node] & inMask) != 0;
    save(node);
    state[node] |= REMOVED;
    if (layeredRemoval) {
      removeAlive(node);
    }
    if (scanOut) {
      touchLevel(nodeLevel[node]);
      wastedVisits += (long) outStart[node + 1] - outStart[node];
      for (int e = outStart[node]; e < outStart[node + 1]; e++) {
        int dst = outEdge[2 * e];
        if (slotAlive(outEdge[2 * e + 1]) && alive(dst)) {
          decrementIn(dst);
          aliveEdges--;
          wastedVisits--;
        }
      }
    }
    if (scanIn) {
      touchLevel(nodeLevel[node] - 1);
      wastedVisits += (long) inStart[node + 1] - inStart[node];
      for (int e = inStart[node]; e < inStart[node + 1]; e++) {
        int src = inEdge[2 * e];
        if (slotAlive(inEdge[2 * e + 1]) && alive(src)) {
          decrementOut(src);
          aliveEdges--;
          wastedVisits--;
        }
      }
    }
  }

  private void clearDeadNodes() {
    deadNodesSize = 0;
    if (!layeredRemoval) {
      return;
    }
    for (int level = nextLevel(forwardLevels, 0);
        level >= 0;
        level = nextLevel(forwardLevels, level)) {
      forwardLevels[level >> 6] &= ~(1L << level);
      forwardHead[level] = -1;
      if (level < list.length) {
        removedSlotHead[level] = -1;
      }
    }
    for (int level = nextLevel(backwardLevels, 0);
        level >= 0;
        level = nextLevel(backwardLevels, level)) {
      backwardLevels[level >> 6] &= ~(1L << level);
      backwardHead[level] = -1;
    }
  }

  /**
   * Records with the store that the state changes at this level, once per level.
   *
   * @param level the current store level.
   */
  private void changedAt(int level) {
    if (changedTop == 0 || changedLevels[changedTop - 1] != level) {
      if (changedTop == changedLevels.length) {
        changedLevels = Arrays.copyOf(changedLevels, 2 * changedTop);
      }
      changedLevels[changedTop++] = level;
      imposedStore.recordChange(this);
    }
  }

  /**
   * The store calls removeLevel only for the levels recorded by changedAt, so the constraint does
   * not listen to the removal of every level.
   *
   * @return false.
   */
  @Override
  public boolean isStateful() {
    return false;
  }

  @Override
  public void removeLevel(int level) {

    while (changedTop > 0 && changedLevels[changedTop - 1] >= level) {
      changedTop--;
    }

    while (markTop > 0 && markLevel[markTop - 1] >= level) {
      int start = markPosition[--markTop];
      while (trailTop > start) {
        trailTop -= 2;
        state[(int) trail[trailTop]] = trail[trailTop + 1];
      }
    }

    aliveEdges = (int) (state[edgeRecord] & VALUE);
    if (adjacency[adjacencyTop - 1].level >= level) {
      while (adjacency[adjacencyTop - 1].level >= level) {
        adjacencyTop--;
      }
      loadAdjacency(adjacency[adjacencyTop - 1]);
    }

    // The search usually continues below the restored level, where removed edges would be visited
    // again. If the subtree just left visited more removed edges than compacting costs, the arrays
    // are compacted before the next propagation; the restored state is the one of level - 1.
    long subtreeWaste = level <= openLevel ? wastedVisits - levelWaste[level] : 0;
    openLevel = Math.min(openLevel, level - 1);
    pendingCompaction =
        subtreeWaste > (long) edges + levelBase
                && aliveEdges < edges / 2
                && adjacency[adjacencyTop - 1].level < level - 1
            ? level - 1
            : -1;

    epochLevel = -1;
    for (int i = 0; i < levelQueueSize; i++) {
      levelQueued[levelQueue[i]] = false;
    }
    levelQueueSize = 0;
    clearDeadNodes();
    emptySlotsSize = 0;
    for (int i = 0; i < touchedLevelsSize; i++) {
      levelTouched[touchedLevels[i]] = false;
    }
    touchedLevelsSize = 0;
  }

  @Override
  public void queueVariable(int level, Var v) {

    if (pruning) {
      return;
    }
    int position;
    if (positionByIndex != null) {
      int i = v.storeIndex - indexOffset;
      position = i >= 0 && i < positionByIndex.length ? positionByIndex[i] : -1;
    } else {
      Integer p = mapping.get(v);
      position = p == null ? -1 : p;
    }
    if (position >= 0 && !levelQueued[position]) {
      changedAt(level);
      levelQueued[position] = true;
      levelQueue[levelQueueSize++] = position;
    }
  }

  @Override
  public void consistency(Store store) {

    currentLevel = store.level;
    changedAt(currentLevel);
    if (epochLevel != currentLevel) {
      if (++epoch > STAMP_MASK) {
        // Stamps are restored from the trail too, so they are cleared there as well.
        long clear = ~((long) STAMP_MASK << STAMP_SHIFT);
        for (int i = 0; i < state.length; i++) {
          state[i] &= clear;
        }
        for (int i = 1; i < trailTop; i += 2) {
          trail[i] &= clear;
        }
        epoch = 1;
      }
      epochLevel = currentLevel;
    }
    emptySlotsSize = 0;
    touchedLevelsSize = 0;

    if (currentLevel > openLevel) {
      if (currentLevel >= levelWaste.length) {
        levelWaste = Arrays.copyOf(levelWaste, Math.max(2 * levelWaste.length, currentLevel + 1));
      }
      Arrays.fill(levelWaste, openLevel + 1, currentLevel + 1, wastedVisits);
      openLevel = currentLevel;
    }
    if (supportSearch) {
      for (int i = 0; i < levelQueueSize; i++) {
        levelQueued[levelQueue[i]] = false;
      }
      levelQueueSize = 0;
      if (init.begin(store)) {
        // Values that label no edge are removed once; afterwards each value is a slot.
        pruning = true;
        try {
          for (int level = 0; level < list.length; level++) {
            IntervalDomain labels = new IntervalDomain();
            for (int slot = levelSlotStart[level]; slot < levelSlotStart[level + 1]; slot++) {
              labels.unionAdapt(slotValue[slot], slotValue[slot]);
            }
            list[level].domain.in(store.level, list[level], labels);
          }
        } finally {
          pruning = false;
        }
      }
      searchSupports(store);
      return;
    }
    if (!probing) {
      consistencyCounters(store);
      return;
    }
    if (++probeCalls <= PROBE_SKIP) {
      consistencyCounters(store);
      return;
    }
    long start = System.nanoTime();
    consistencyCounters(store);
    long middle = System.nanoTime();
    // The domains are at the fixpoint of this constraint, so the search only finds supports. It
    // runs at every call of the probe, so its nodes without support accumulate as they would if
    // it propagated alone.
    searchSupports(store);
    probeCountersTime += middle - start;
    probeSearchTime += System.nanoTime() - middle;
    int calls = probeCalls - PROBE_SKIP;
    if (calls == PROBE_CALLS
        || calls >= PROBE_CHECK
            && calls % PROBE_CHECK == 0
            && (probeSearchTime > STAY_SHARE * probeCountersTime
                || probeSearchTime < SWITCH_EARLY_SHARE * probeCountersTime)) {
      probing = false;
      supportSearch = preferSupportSearch(probeCountersTime, probeSearchTime);
      if (!supportSearch) {
        releaseSearchArrays();
      }
    }
  }

  private void consistencyCounters(Store store) {
    if (pendingCompaction >= 0) {
      compact(pendingCompaction);
      pendingCompaction = -1;
    }

    boolean first = init.begin(store);
    if (first) {
      for (int i = 0; i < list.length; i++) {
        if (!levelQueued[i]) {
          levelQueued[i] = true;
          levelQueue[levelQueueSize++] = i;
        }
      }
    }

    for (int q = 0; q < levelQueueSize; q++) {
      int level = levelQueue[q];
      levelQueued[level] = false;
      IntDomain dom = list[level].domain;
      for (int slot = levelSlotStart[level]; slot < levelSlotStart[level + 1]; slot++) {
        if (slotAlive(slot) && !dom.contains(slotValue[slot])) {
          if (layeredRemoval) {
            deferSlot(slot);
          } else {
            removeSlot(slot);
          }
        }
      }
    }
    levelQueueSize = 0;

    removeDeadNodes();
    checkTouchedLevels();

    if (aliveEdges != (state[edgeRecord] & VALUE)) {
      save(edgeRecord);
      state[edgeRecord] = state[edgeRecord] & ~VALUE | aliveEdges;
    }

    pruning = true;
    try {
      if (first) {
        for (int level = 0; level < list.length; level++) {
          IntervalDomain supported = new IntervalDomain();
          for (int slot = levelSlotStart[level]; slot < levelSlotStart[level + 1]; slot++) {
            if (slotAlive(slot)) {
              supported.unionAdapt(slotValue[slot], slotValue[slot]);
            }
          }
          list[level].domain.in(store.level, list[level], supported);
        }
      } else {
        for (int i = 0; i < emptySlotsSize; i++) {
          int slot = emptySlots[i];
          IntVar x = list[slotLevel[slot]];
          if (x.domain.contains(slotValue[slot])) {
            x.domain.inComplement(store.level, x, slotValue[slot]);
          }
        }
      }
    } finally {
      pruning = false;
      emptySlotsSize = 0;
    }
  }

  @Override
  public void impose(Store store) {

    buildLayeredGraph(store);

    mapping = Var.positionMapping(list, true, this.getClass());
    int min = Integer.MAX_VALUE;
    int max = Integer.MIN_VALUE;
    for (IntVar v : mapping.keySet()) {
      min = Math.min(min, v.storeIndex);
      max = Math.max(max, v.storeIndex);
    }
    if (min >= 0 && (long) max - min < 4L * list.length + 64) {
      indexOffset = min;
      positionByIndex = new int[max - min + 1];
      Arrays.fill(positionByIndex, -1);
      mapping.forEach((v, position) -> positionByIndex[v.storeIndex - indexOffset] = position);
    }
    levelQueue = new int[list.length];
    levelQueued = new boolean[list.length];
    imposedStore = store;

    super.impose(store);
  }

  /**
   * It checks whether all variables are ground and their values label a path from the first to the
   * last level of the graph built when the constraint was imposed.
   *
   * @return true if the current assignment is ground and allowed.
   */
  protected boolean groundAssignmentAllowed() {
    if (state == null) {
      return false;
    }
    for (IntVar v : list) {
      if (!v.singleton()) {
        return false;
      }
    }
    Adjacency initial = adjacency[0];
    int nodes = nodeCount;
    boolean[] reached = new boolean[nodes];
    int[] frontier = new int[nodes];
    int size = 0;
    for (int node = 0; node < nodes && nodeLevel[node] == 0; node++) {
      frontier[size++] = node;
    }
    int[] next = new int[nodes];
    for (int level = 0; level < list.length && size > 0; level++) {
      int value = list[level].value();
      int nextSize = 0;
      for (int i = 0; i < size; i++) {
        int node = frontier[i];
        for (int e = initial.outStart[node]; e < initial.outStart[node + 1]; e++) {
          int dst = initial.outEdge[2 * e];
          if (!reached[dst] && slotValue[initial.outEdge[2 * e + 1]] == value) {
            reached[dst] = true;
            next[nextSize++] = dst;
          }
        }
      }
      int[] swap = frontier;
      frontier = next;
      next = swap;
      size = nextSize;
    }
    return size > 0;
  }

  /**
   * It returns the propagation algorithm used when none was set, which may depend on the layered
   * graph, built already when this is called. The default is {@link Engine#AUTO}.
   *
   * @return the algorithm.
   */
  protected Engine defaultEngine() {
    return Engine.AUTO;
  }

  /**
   * It returns the number of nodes of the layered graph.
   *
   * @return the number of nodes.
   */
  protected int graphNodes() {
    return nodeCount;
  }

  /**
   * It creates the arrays of the support search at its first call: with the automatic choice they
   * are needed only once the probe starts, and constraints that settle on the counters release
   * them, which matters for models with hundreds of large diagrams.
   */
  private void createSearchArrays(Store store) {
    noBits = new long[(nodeCount >>> 6) + 1];
    noList = new int[16];
    noListTop = 0;
    scratch = built.scratch(store);
    yesStamp = scratch.yesStamp;
    inDomainStamp = scratch.inDomainStamp;
    supportedStamp = scratch.supportedStamp;
    levelUnsupported = scratch.levelUnsupported;
  }

  /**
   * It releases the arrays of the support search once the counters were chosen for good. The record
   * of the nodes without support is left as it is; it is not read by the counters.
   */
  private void releaseSearchArrays() {
    noBits = null;
    noList = null;
    scratch = null;
    yesStamp = null;
    inDomainStamp = null;
    supportedStamp = null;
    levelUnsupported = null;
  }

  private void searchSupports(Store store) {
    if (noBits == null) {
      createSearchArrays(store);
    }
    searchStamp = scratch.nextStamp();
    // backtracking restored the record: the nodes past it have a path again
    int noSize = (int) (state[noRecord] & VALUE);
    while (noListTop > noSize) {
      int node = noList[--noListTop];
      noBits[node >>> 6] &= ~(1L << node);
    }
    int levels = list.length;
    for (int level = 0; level < levels; level++) {
      IntDomain dom = list[level].domain;
      int count = 0;
      for (int slot = levelSlotStart[level]; slot < levelSlotStart[level + 1]; slot++) {
        if (dom.contains(slotValue[slot])) {
          inDomainStamp[slot] = searchStamp;
          count++;
        }
      }
      if (count == 0) {
        throw Store.failException;
      }
      levelUnsupported[level] = count;
    }
    deepestUnsupported = levels - 1;
    boolean supported = levels == 0;
    for (int root = 0; root < nodeCount && nodeLevel[root] == 0; root++) {
      if (seekSupport(root, 0)) {
        supported = true;
        if (deepestUnsupported < 0) {
          break;
        }
      }
    }
    if (!supported) {
      throw Store.failException;
    }
    if (deepestUnsupported < 0) {
      return;
    }
    pruning = true;
    try {
      for (int level = 0; level < levels; level++) {
        if (levelUnsupported[level] == 0) {
          continue;
        }
        IntVar x = list[level];
        for (int slot = levelSlotStart[level]; slot < levelSlotStart[level + 1]; slot++) {
          if (inDomainStamp[slot] == searchStamp && supportedStamp[slot] != searchStamp) {
            x.domain.inComplement(store.level, x, slotValue[slot]);
          }
        }
      }
    } finally {
      pruning = false;
    }
  }

  /** It checks whether a path labelled with values of the domains leads from a node to the end. */
  private boolean seekSupport(int node, int level) {
    if (yesStamp[node] == searchStamp) {
      return true;
    }
    if ((noBits[node >>> 6] & (1L << node)) != 0) {
      return false;
    }
    boolean result = false;
    boolean last = level + 1 == list.length;
    for (int e = outStart[node]; e < outStart[node + 1]; e++) {
      int slot = outEdge[2 * e + 1];
      if (inDomainStamp[slot] != searchStamp) {
        continue;
      }
      if (!last && !seekSupport(outEdge[2 * e], level + 1)) {
        continue;
      }
      result = true;
      if (supportedStamp[slot] != searchStamp) {
        supportedStamp[slot] = searchStamp;
        if (--levelUnsupported[level] == 0 && level == deepestUnsupported) {
          while (deepestUnsupported >= 0 && levelUnsupported[deepestUnsupported] == 0) {
            deepestUnsupported--;
          }
        }
      }
      if (deepestUnsupported < level) {
        break;
      }
    }
    if (result) {
      yesStamp[node] = searchStamp;
    } else {
      save(noRecord);
      if (noListTop == noList.length) {
        noList = Arrays.copyOf(noList, Math.min(nodeCount, 2 * noListTop));
      }
      noList[noListTop++] = node;
      noBits[node >>> 6] |= 1L << node;
      state[noRecord]++;
    }
    return result;
  }
}
