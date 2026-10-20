/*
 * Regular.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2008 Polina Maakeva and Radoslaw Szymanek
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
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ExtensionalSupportStr;
import org.jacop.constraints.In;
import org.jacop.constraints.XeqC;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;

/**
 * Regular constraint accepts only the assignment to variables which is accepted by an automaton. It
 * achieves generalized arc consistency (domain consistency).
 *
 * <p>The automaton is unfolded into a layered graph with one layer of edges per variable. Every
 * edge is labelled with a single value. Each node counts its alive incoming and outgoing edges; an
 * edge is alive while its value and both its nodes are alive, so edges carry no state of their own.
 * When a value is removed from a variable only the edges labelled with it are visited. A node whose
 * incoming or outgoing count drops to zero is removed and only its edges on the other side are
 * visited, which may remove further nodes. Afterwards each value of a level where edges were
 * removed is checked for an alive edge, starting from the edge that supported it last time, and
 * values without one are removed from the variable. The counters are trailed, so backtracking costs
 * time proportional to the counters changed since the restored level. This follows the layered
 * graph propagator of Gecode and the incremental approach of MDD4R (Perez and Regin, "Improving
 * GAC-4 for Table and MDD Constraints", CP 2014), adapted to a trailing solver.
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
public class Regular extends Constraint implements UsesQueueVariable, Stateful {

  /** It specifies if debugging information should be printed out. */
  public static final boolean DEBUG_ALL = false;

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies finite state machine used by this regular. */
  public final Fsm fsm;

  /** Array of the variables of the graph levels. */
  public final IntVar[] list;

  List<Constraint> constraints;

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
   * It constructs a regular constraint.
   *
   * @param fsm (deterministic) finite automaton
   * @param list variables which values have to be accepted by the automaton.
   */
  public Regular(Fsm fsm, IntVar[] list) {

    checkInputForNullness("list", list);
    checkInputForDuplicationSkipSingletons("list", list);

    this.queueIndex = 3;
    this.list = Arrays.copyOf(list, list.length);
    this.fsm = fsm;
    numberId = idNumber.incrementAndGet();
    setScope(list);
  }

  /**
   * It unfolds the automaton into the layered graph. A forward pass collects the states reachable
   * at each layer, a backward pass keeps the states from which a final state can be reached, and
   * only then the nodes and edges of the layered graph are created. All work is proportional to the
   * number of reachable states and their transitions.
   */
  private void buildLayeredGraph() {
    int levels = list.length;
    fsm.resize();
    int stateNumber = fsm.allStates.size();

    // Transitions of each automaton state, indexed by state id.
    final FsmTransition[][] transitions = new FsmTransition[stateNumber][];
    for (FsmState s : fsm.allStates) {
      transitions[s.id] = s.transitions.toArray(new FsmTransition[0]);
    }

    // Forward pass: states reachable at each level, stored sparsely as lists of state ids.
    final int[][] reachable = new int[levels + 1][];
    final boolean[] marked = new boolean[stateNumber];
    final int[] buffer = new int[stateNumber];
    reachable[0] = new int[] {fsm.initState.id};
    for (int level = 0; level < levels; level++) {
      IntDomain varDom = list[level].dom();
      int count = 0;
      for (int sId : reachable[level]) {
        for (FsmTransition t : transitions[sId]) {
          int sucId = t.successor.id;
          if (marked[sucId]
              || (level == levels - 1 && !fsm.finalStates.contains(t.successor))
              || !t.domain.isIntersecting(varDom)) {
            continue;
          }
          marked[sucId] = true;
          buffer[count++] = sucId;
        }
      }
      reachable[level + 1] = Arrays.copyOf(buffer, count);
      for (int i = 0; i < count; i++) {
        marked[buffer[i]] = false;
      }
    }

    // Backward pass: keep only states from which a final state can be reached. For each kept
    // state remember its arcs (successor and the merged domain of values leading to it). Kept
    // states get consecutive node ids, level by level.
    final int[][] node = new int[levels + 1][];
    final int[][][] arcSuccessors = new int[levels][][];
    final IntDomain[][][] arcDomains = new IntDomain[levels][][];
    final int[] nodeOfState = new int[stateNumber];
    final IntDomain[] arc = new IntDomain[stateNumber];
    final int[] arcOrder = new int[stateNumber];
    Arrays.fill(nodeOfState, -1);

    node[levels] = new int[reachable[levels].length];
    int[] levelNodeCount = new int[levels + 1];
    levelNodeCount[levels] = reachable[levels].length;
    for (int i = 0; i < reachable[levels].length; i++) {
      node[levels][i] = i;
    }
    for (int level = levels - 1; level >= 0; level--) {
      int[] next = reachable[level + 1];
      for (int i = 0; i < next.length; i++) {
        nodeOfState[next[i]] = node[level + 1][i];
      }
      IntDomain varDom = list[level].dom();
      int[] current = reachable[level];
      node[level] = new int[current.length];
      arcSuccessors[level] = new int[current.length][];
      arcDomains[level] = new IntDomain[current.length][];
      int count = 0;
      for (int i = 0; i < current.length; i++) {
        int arcs = 0;
        for (FsmTransition t : transitions[current[i]]) {
          int sucId = t.successor.id;
          if (nodeOfState[sucId] < 0) {
            continue;
          }
          IntDomain dom = t.domain.intersect(varDom);
          if (dom.isEmpty()) {
            continue;
          }
          if (arc[sucId] == null) {
            arc[sucId] = dom;
            arcOrder[arcs++] = sucId;
          } else {
            arc[sucId] = arc[sucId].union(dom);
          }
        }
        if (arcs == 0) {
          node[level][i] = -1;
          continue;
        }
        Arrays.sort(arcOrder, 0, arcs);
        arcSuccessors[level][i] = new int[arcs];
        arcDomains[level][i] = new IntDomain[arcs];
        for (int k = 0; k < arcs; k++) {
          arcSuccessors[level][i][k] = nodeOfState[arcOrder[k]];
          arcDomains[level][i][k] = arc[arcOrder[k]];
          arc[arcOrder[k]] = null;
        }
        node[level][i] = count++;
      }
      levelNodeCount[level] = count;
      for (int sId : next) {
        nodeOfState[sId] = -1;
      }
    }

    // Global node ids: level offsets.
    int[] levelNodeStart = new int[levels + 2];
    for (int level = 0; level <= levels; level++) {
      levelNodeStart[level + 1] = levelNodeStart[level] + levelNodeCount[level];
    }
    int nodes = levelNodeStart[levels + 1];

    // Slots: the values labelling edges of each level.
    levelSlotStart = new int[levels + 1];
    int[][] levelValues = new int[levels][];
    for (int level = 0; level < levels; level++) {
      IntervalDomain values = new IntervalDomain();
      for (IntDomain[] domains : arcDomains[level]) {
        if (domains != null) {
          for (IntDomain dom : domains) {
            values.unionAdapt(dom);
          }
        }
      }
      levelValues[level] = new int[values.getSize()];
      int k = 0;
      for (ValueEnumeration e = values.valueEnumeration(); e.hasMoreElements(); ) {
        levelValues[level][k++] = e.nextElement();
      }
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

    // Count edges per node and per slot.
    int[] outCount = new int[nodes + 1];
    int[] inCount = new int[nodes + 1];
    int[] slotCount = new int[slots + 1];
    for (int level = 0; level < levels; level++) {
      for (int i = 0; i < node[level].length; i++) {
        if (node[level][i] < 0) {
          continue;
        }
        int src = levelNodeStart[level] + node[level][i];
        for (int k = 0; k < arcSuccessors[level][i].length; k++) {
          int dst = levelNodeStart[level + 1] + arcSuccessors[level][i][k];
          for (ValueEnumeration e = arcDomains[level][i][k].valueEnumeration();
              e.hasMoreElements(); ) {
            int slot = slotOf(level, levelValues[level], e.nextElement());
            outCount[src]++;
            inCount[dst]++;
            slotCount[slot]++;
          }
        }
      }
    }

    outStart = segmentStarts(outCount);
    inStart = segmentStarts(inCount);
    slotStart = segmentStarts(slotCount);
    edges = outStart[nodes];
    aliveEdges = edges;
    outEdge = new int[2 * edges];
    inEdge = new int[2 * edges];
    slotEdge = new int[2 * edges];

    slotBase = nodes;
    levelBase = nodes + slots;
    edgeRecord = levelBase + levels;
    state = new long[edgeRecord + 1];
    int[] slotFill = new int[slots];
    int[] outFill = new int[nodes];
    int[] inFill = new int[nodes];
    for (int level = 0; level < levels; level++) {
      state[levelBase + level] = levelSlotStart[level + 1] - levelSlotStart[level];
    }
    state[edgeRecord] = edges;

    for (int level = 0; level < levels; level++) {
      for (int i = 0; i < node[level].length; i++) {
        if (node[level][i] < 0) {
          continue;
        }
        int src = levelNodeStart[level] + node[level][i];
        for (int k = 0; k < arcSuccessors[level][i].length; k++) {
          int dst = levelNodeStart[level + 1] + arcSuccessors[level][i][k];
          for (ValueEnumeration e = arcDomains[level][i][k].valueEnumeration();
              e.hasMoreElements(); ) {
            int slot = slotOf(level, levelValues[level], e.nextElement());
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
        }
      }
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
      throw new IllegalArgumentException("Regular: too many edges per node in the layered graph");
    }
    outMask = (1L << outBits) - 1;
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
    }
  }

  private int slotOf(int level, int[] values, int value) {
    return levelSlotStart[level] + Arrays.binarySearch(values, value);
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
      int level = nodeLevel[node];
      backwardNext[node] = backwardHead[level];
      backwardHead[level] = node;
      backwardLevels[level >> 6] |= 1L << level;
    }
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
      int level = nodeLevel[node];
      forwardNext[node] = forwardHead[level];
      forwardHead[level] = node;
      forwardLevels[level >> 6] |= 1L << level;
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
    wastedVisits += slotStart[slot + 1] - slotStart[slot];
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
    // later; the backward pass is symmetric. Only levels with nodes to remove are visited.
    for (int level = nextLevel(forwardLevels, 0);
        level >= 0;
        level = nextLevel(forwardLevels, level)) {
      forwardLevels[level >> 6] &= ~(1L << level);
      int node = forwardHead[level];
      forwardHead[level] = -1;
      for (; node >= 0; node = forwardNext[node]) {
        removeNode(node);
      }
    }
    for (int level = previousLevel(backwardLevels, list.length);
        level >= 0;
        level = previousLevel(backwardLevels, level)) {
      backwardLevels[level >> 6] &= ~(1L << level);
      int node = backwardHead[level];
      backwardHead[level] = -1;
      for (; node >= 0; node = backwardNext[node]) {
        removeNode(node);
      }
    }
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
    if (scanOut) {
      touchLevel(nodeLevel[node]);
      wastedVisits += outStart[node + 1] - outStart[node];
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
      wastedVisits += inStart[node + 1] - inStart[node];
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
        subtreeWaste > edges + levelBase
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
          removeSlot(slot);
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

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append("( [ ");
    for (IntVar intVar : list) {
      result.append(intVar.id()).append(" ");
    }
    result.append(" ], Fsm \n");
    result.append(fsm.toString());
    result.append(")");

    return result.toString();
  }

  @Override
  public void imposeDecomposition(Store store) {

    if (constraints == null) {
      constraints = decompose(store);
    }

    for (Constraint c : constraints) {
      store.impose(c, queueIndex);
    }
  }

  @Override
  public List<Constraint> decompose(Store store) {

    fsm.resize();

    List<int[]> listOfTuples = new ArrayList<>();

    // tuples for transitions from not-intial states.

    for (FsmState state : fsm.allStates) {

      for (FsmTransition transition : state.transitions) {

        for (ValueEnumeration enumer = transition.domain.valueEnumeration();
            enumer.hasMoreElements(); ) {

          int[] row = {state.id, enumer.nextElement(), transition.successor.id};

          listOfTuples.add(row);
        }
      }
    }

    int[][] tuples = new int[listOfTuples.size()][];
    listOfTuples.toArray(tuples);

    IntVar[] q = new IntVar[list.length + 1];

    for (int i = 0; i < q.length; i++) {
      q[i] = new IntVar(store, "Q" + i, 0, fsm.allStates.size());
    }

    constraints = new ArrayList<>();

    for (int i = 0; i < q.length - 1; i++) {
      IntVar[] scope = {q[i], list[i], q[i + 1]};
      constraints.add(new ExtensionalSupportStr(scope, tuples));
    }

    constraints.add(new XeqC(q[0], fsm.initState.id));

    IntervalDomain finalQ = new IntervalDomain();
    for (FsmState finalState : fsm.finalStates) {
      finalQ.unionAdapt(finalState.id, finalState.id);
    }

    constraints.add(new In(q[q.length - 1], finalQ));

    return constraints;
  }
}
