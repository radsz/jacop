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

  // Static adjacency of the layered graph. Edges leaving node u are at positions
  // outStart[u]..outStart[u+1]-1 of outNode (destination) and outSlot; edges entering node u are at
  // positions inStart[u]..inStart[u+1]-1 of inNode (source) and inSlot; edges of slot s are at
  // positions slotStart[s]..slotStart[s+1]-1 of slotSrc and slotDst.
  private int[] outStart;
  private int[] outNode;
  private int[] outSlot;
  private int[] inStart;
  private int[] inNode;
  private int[] inSlot;
  private int[] slotStart;
  private int[] slotSrc;
  private int[] slotDst;

  // Backtrackable state, RECORD ints per record. Records 0..nodes-1 hold for each node the number
  // of alive incoming and outgoing edges; a removed node has -1 incoming edges. The next records
  // hold for each slot 1 while the value is alive and 0 once it is removed, followed by one record
  // per level with the number of its values that are still alive. An edge is alive when its slot
  // and both its nodes are alive. The third int of a record is the epoch in which the record was
  // trailed last; it is kept next to the counters so that both are read together.
  private static final int RECORD = 4;
  private static final int STAMP = 2;

  private int[] state;
  private int slotBase;
  private int levelBase;

  /**
   * Epoch of the current consistency call. A new epoch starts whenever the store level differs from
   * the one of the previous call or a level was removed, so a record trailed in an earlier epoch is
   * trailed again before it changes. Epochs are never reused, so stamps need no restoring.
   */
  private int epoch;

  private int epochLevel = -1;

  // Trail of saved records (record and its two counters) and, for each level with trailed records,
  // the level and the trail position where its records start.
  private int[] trail = new int[256];
  private int trailTop;
  private int[] markLevel = new int[16];
  private int[] markPosition = new int[16];
  private int markTop;

  private int currentLevel;

  // Nodes that lost all their incoming or all their outgoing edges and must be removed.
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
    int edges = outStart[nodes];
    outNode = new int[edges];
    outSlot = new int[edges];
    inNode = new int[edges];
    inSlot = new int[edges];
    slotSrc = new int[edges];
    slotDst = new int[edges];

    slotBase = nodes;
    levelBase = nodes + slots;
    state = new int[RECORD * (levelBase + levels)];
    int[] slotFill = new int[slots];
    for (int level = 0; level < levels; level++) {
      state[RECORD * (levelBase + level)] = levelSlotStart[level + 1] - levelSlotStart[level];
    }

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
            int o = outStart[src] + state[RECORD * src + 1]++;
            outNode[o] = dst;
            outSlot[o] = slot;
            int in = inStart[dst] + state[RECORD * dst]++;
            inNode[in] = src;
            inSlot[in] = slot;
            int se = slotStart[slot] + slotFill[slot]++;
            slotSrc[se] = src;
            slotDst[se] = dst;
          }
        }
      }
    }

    emptySlots = new int[Math.max(1, slots)];
    residue = Arrays.copyOf(slotStart, slots);
    for (int slot = 0; slot < slots; slot++) {
      state[RECORD * (slotBase + slot)] = 1;
    }
    nodeLevel = new int[nodes];
    for (int level = 0; level <= levels; level++) {
      Arrays.fill(nodeLevel, levelNodeStart[level], levelNodeStart[level + 1], level);
    }
    touchedLevels = new int[levels];
    levelTouched = new boolean[levels];
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

  /** It saves a record on the trail unless it was saved in the current epoch already. */
  private void save(int record) {
    int base = RECORD * record;
    if (state[base + STAMP] == epoch) {
      return;
    }
    state[base + STAMP] = epoch;
    if (markTop == 0 || markLevel[markTop - 1] != currentLevel) {
      if (markTop == markLevel.length) {
        markLevel = Arrays.copyOf(markLevel, markTop * 2);
        markPosition = Arrays.copyOf(markPosition, markTop * 2);
      }
      markLevel[markTop] = currentLevel;
      markPosition[markTop++] = trailTop;
    }
    if (trailTop + 3 > trail.length) {
      trail = Arrays.copyOf(trail, trail.length * 2);
    }
    trail[trailTop] = record;
    trail[trailTop + 1] = state[base];
    trail[trailTop + 2] = state[base + 1];
    trailTop += 3;
  }

  private boolean alive(int node) {
    return state[RECORD * node] >= 0;
  }

  private boolean slotAlive(int slot) {
    return state[RECORD * (slotBase + slot)] > 0;
  }

  /** It decrements the number of incoming (degree 0) or outgoing (degree 1) edges of a node. */
  private void decrementDegree(int node, int degree) {
    save(node);
    if (--state[RECORD * node + degree] == 0) {
      if (deadNodesSize == deadNodes.length) {
        deadNodes = Arrays.copyOf(deadNodes, deadNodesSize * 2);
      }
      deadNodes[deadNodesSize++] = node;
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
      if (alive(slotSrc[e]) && alive(slotDst[e])) {
        residue[slot] = e;
        return true;
      }
    }
    for (int e = start; e < r; e++) {
      if (alive(slotSrc[e]) && alive(slotDst[e])) {
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
          state[RECORD * record] = 0;
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
    if (--state[RECORD * record] == 0) {
      throw Store.failException;
    }
  }

  /** It removes a value of a level, together with all alive edges labelled with it. */
  private void removeSlot(int slot) {
    int record = slotBase + slot;
    save(record);
    state[RECORD * record] = 0;
    removedSlotOfLevel(slotLevel[slot]);
    for (int e = slotStart[slot]; e < slotStart[slot + 1]; e++) {
      int src = slotSrc[e];
      int dst = slotDst[e];
      if (alive(src) && alive(dst)) {
        decrementDegree(src, 1);
        decrementDegree(dst, 0);
      }
    }
  }

  /**
   * It removes the nodes that lost all their incoming or all their outgoing edges. Their remaining
   * alive edges are removed too, which may remove further nodes and leave values without support.
   */
  private void removeDeadNodes() {
    while (deadNodesSize > 0) {
      int node = deadNodes[--deadNodesSize];
      if (!alive(node)) {
        continue;
      }
      // A node is removed because one of its counts dropped to zero, so only the other side can
      // still have alive edges.
      boolean scanOut = state[RECORD * node + 1] > 0;
      boolean scanIn = state[RECORD * node] > 0;
      save(node);
      state[RECORD * node] = -1;
      if (scanOut) {
        touchLevel(nodeLevel[node]);
        for (int e = outStart[node]; e < outStart[node + 1]; e++) {
          int dst = outNode[e];
          if (slotAlive(outSlot[e]) && alive(dst)) {
            decrementDegree(dst, 0);
          }
        }
      }
      if (scanIn) {
        touchLevel(nodeLevel[node] - 1);
        for (int e = inStart[node]; e < inStart[node + 1]; e++) {
          int src = inNode[e];
          if (slotAlive(inSlot[e]) && alive(src)) {
            decrementDegree(src, 1);
          }
        }
      }
    }
  }

  @Override
  public void removeLevel(int level) {

    while (markTop > 0 && markLevel[markTop - 1] >= level) {
      int start = markPosition[--markTop];
      while (trailTop > start) {
        trailTop -= 3;
        int base = RECORD * trail[trailTop];
        state[base] = trail[trailTop + 1];
        state[base + 1] = trail[trailTop + 2];
      }
    }

    epochLevel = -1;
    for (int i = 0; i < levelQueueSize; i++) {
      levelQueued[levelQueue[i]] = false;
    }
    levelQueueSize = 0;
    deadNodesSize = 0;
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
    Integer position = mapping.get(v);
    if (position != null && !levelQueued[position]) {
      levelQueued[position] = true;
      levelQueue[levelQueueSize++] = position;
    }
  }

  @Override
  public void consistency(Store store) {

    currentLevel = store.level;
    if (epochLevel != currentLevel) {
      if (++epoch == Integer.MAX_VALUE) {
        for (int base = STAMP; base < state.length; base += RECORD) {
          state[base] = 0;
        }
        epoch = 1;
      }
      epochLevel = currentLevel;
    }
    deadNodesSize = 0;
    emptySlotsSize = 0;
    touchedLevelsSize = 0;

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
