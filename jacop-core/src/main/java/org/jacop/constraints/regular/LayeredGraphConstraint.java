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

import java.util.Arrays;
import java.util.Map;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

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
    implements UsesQueueVariable, Stateful {

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

  private boolean firstConsistencyCheck = true;

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
  private long[] previousCount;

  private int inShift;

  // Support search, used instead of the counters when supportSearch is set. Each consistency call
  // searches the graph depth first from the first level for paths labelled with values of the
  // domains, as the mddc algorithm of Cheng and Yap (CP 2008) does, and stops as soon as every
  // value of the levels below has a support. Nodes from which no such path exists are kept in a
  // sparse set, noNodes, whose size is the record noRecord, so they are skipped until
  // backtracking. Nodes with a path are marked with the stamp of the call in yesStamp.
  private boolean supportSearch;
  private int[] noNodes;
  private int[] noPosition;
  private int noRecord;
  private int[] yesStamp;
  private int[] inDomainStamp;
  private int[] supportedStamp;
  private int searchStamp;
  private int[] levelUnsupported;
  private int deepestUnsupported;

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
   * It builds the layered graph from its description. Edges with values outside the domains are
   * dropped, a forward and a backward pass keep the nodes on a path from level 0 to the last level,
   * and the static adjacency arrays are created. All work is proportional to the size of the
   * description.
   */
  private void buildLayeredGraph() {
    int levels = list.length;
    LayeredGraphDescription description = new LayeredGraphDescription(levels);
    describeGraph(description);
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
      if (list[level].domain.contains(edge[4 * e + 2])) {
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

    // Kept nodes get consecutive ids, level by level; kept edges are the usable edges between them.
    int[] nodeId = new int[describedStart[levels + 1]];
    levelNodeStart = new int[levels + 2];
    int nodes = 0;
    for (int level = 0; level <= levels; level++) {
      levelNodeStart[level] = nodes;
      for (int n = describedStart[level]; n < describedStart[level + 1]; n++) {
        nodeId[n] = kept[n] ? nodes++ : -1;
      }
    }
    levelNodeStart[levels + 1] = nodes;
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
    int slots = levelSlotStart[levels];
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

    outStart = segmentStarts(outCount);
    inStart = segmentStarts(inCount);
    slotStart = segmentStarts(slotCount);
    aliveEdges = edges;
    outEdge = new int[2 * edges];
    inEdge = new int[2 * edges];
    slotEdge = new int[2 * edges];

    slotBase = nodes;
    levelBase = nodes + slots;
    edgeRecord = levelBase + levels;
    aliveBase = edgeRecord + 1;
    noRecord = aliveBase + levels + 1;
    state = new long[noRecord + 1];
    int[] slotFill = new int[slots];
    int[] outFill = new int[nodes];
    int[] inFill = new int[nodes];
    for (int level = 0; level < levels; level++) {
      state[levelBase + level] = (long) levelSlotStart[level + 1] - levelSlotStart[level];
    }
    state[edgeRecord] = edges;

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

    emptySlots = new int[Math.max(1, slots)];
    residue = Arrays.copyOf(slotStart, slots);
    adjacency[0] = saveAdjacency(new Adjacency(), -1);
    adjacencyTop = 1;
    for (int slot = 0; slot < slots; slot++) {
      state[slotBase + slot] = 1;
    }
    int maxOut = 1;
    int maxIn = 1;
    for (int n = 0; n < nodes; n++) {
      maxOut = Math.max(maxOut, outFill[n]);
      maxIn = Math.max(maxIn, inFill[n]);
    }
    int outBits = 32 - Integer.numberOfLeadingZeros(maxOut);
    int inBits = 32 - Integer.numberOfLeadingZeros(maxIn);
    if (outBits + inBits > STAMP_SHIFT) {
      throw new IllegalArgumentException(
          getClass().getSimpleName() + ": too many edges per node in the layered graph");
    }
    outMask = (1L << outBits) - 1;
    inShift = outBits;
    inOne = 1L << outBits;
    inMask = ((1L << inBits) - 1) << outBits;
    for (int n = 0; n < nodes; n++) {
      state[n] = ((long) inFill[n] << outBits) | outFill[n];
    }
    nodeLevel = new int[nodes];
    for (int level = 0; level <= levels; level++) {
      Arrays.fill(nodeLevel, levelNodeStart[level], levelNodeStart[level + 1], level);
    }
    touchedLevels = new int[levels];
    levelTouched = new boolean[levels];
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
      previousCount = new long[nodes];
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
    int nodes = slotBase;
    int slots = levelBase - slotBase;
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
  private void save(int record) {
    long s = state[record];
    if ((int) (s >>> STAMP_SHIFT & STAMP_MASK) == epoch) {
      return;
    }
    state[record] = s & ~((long) STAMP_MASK << STAMP_SHIFT) | (long) epoch << STAMP_SHIFT;
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
    trail[trailTop] = record;
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
          int record = slotBase + slot;
          save(record);
          state[record] &= ~VALUE;
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
    int record = levelBase + level;
    save(record);
    if ((--state[record] & VALUE) == 0) {
      throw Store.failException;
    }
  }

  /** It removes a value of a level, together with all alive edges labelled with it. */
  private void removeSlot(int slot) {
    int record = slotBase + slot;
    save(record);
    state[record] &= ~VALUE;
    removedSlotOfLevel(slotLevel[slot]);
    removeSlotEdges(slot);
  }

  /** It removes a value of a level and leaves its edges to the forward pass. */
  private void deferSlot(int slot) {
    int record = slotBase + slot;
    save(record);
    state[record] &= ~VALUE;
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
    int record = aliveBase + level;
    save(record);
    int last = levelNodeStart[level] + (int) (state[record] & VALUE) - 1;
    state[record]--;
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
    for (int i = to; i < toEnd; i++) {
      int v = levelOrder[i];
      save(v);
      long in = (state[v] & inMask) >>> inShift;
      previousCount[v] = in;
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

  @Override
  public void removeLevel(int level) {

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
      levelQueued[position] = true;
      levelQueue[levelQueueSize++] = position;
    }
  }

  @Override
  public void consistency(Store store) {

    currentLevel = store.level;
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
      if (firstConsistencyCheck) {
        // Values that label no edge are removed once; afterwards each value is a slot.
        firstConsistencyCheck = false;
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
    if (pendingCompaction >= 0) {
      compact(pendingCompaction);
      pendingCompaction = -1;
    }

    if (firstConsistencyCheck) {
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
      if (firstConsistencyCheck) {
        firstConsistencyCheck = false;
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

    buildLayeredGraph();
    supportSearch = useSupportSearch();
    if (supportSearch) {
      int nodes = slotBase;
      int slots = levelBase - slotBase;
      noNodes = new int[nodes];
      noPosition = new int[nodes];
      for (int n = 0; n < nodes; n++) {
        noNodes[n] = n;
        noPosition[n] = n;
      }
      yesStamp = new int[nodes];
      inDomainStamp = new int[slots];
      supportedStamp = new int[slots];
      levelUnsupported = new int[list.length];
    }

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
    int nodes = slotBase;
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
   * It decides, once the layered graph is built, whether the constraint is propagated by support
   * search instead of the incremental counters. The default keeps the counters.
   *
   * @return true if support search is used.
   */
  protected boolean useSupportSearch() {
    return false;
  }

  /**
   * It returns the number of nodes of the layered graph.
   *
   * @return the number of nodes.
   */
  protected int graphNodes() {
    return slotBase;
  }

  private void searchSupports(Store store) {
    if (++searchStamp == Integer.MAX_VALUE) {
      Arrays.fill(yesStamp, 0);
      Arrays.fill(inDomainStamp, 0);
      Arrays.fill(supportedStamp, 0);
      searchStamp = 1;
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
    for (int root = 0; root < slotBase && nodeLevel[root] == 0; root++) {
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
    int noSize = (int) (state[noRecord] & VALUE);
    if (noPosition[node] < noSize) {
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
      noSize = (int) (state[noRecord] & VALUE);
      int position = noPosition[node];
      int other = noNodes[noSize];
      noNodes[position] = other;
      noPosition[other] = position;
      noNodes[noSize] = node;
      noPosition[node] = noSize;
      state[noRecord]++;
    }
    return result;
  }
}
