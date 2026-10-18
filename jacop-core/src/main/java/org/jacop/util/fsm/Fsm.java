/*
 * Fsm.java
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

package org.jacop.util.fsm;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Consumer;
import java.util.function.IntConsumer;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.util.Mdd;

/**
 * Deterministic Finite Acyclic graph.
 *
 * @author Polina Makeeva and Radoslaw Szymanek
 * @version 5.0
 */
public class Fsm {

  /** It specifies number of states created in DFA class. */
  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies the intial state of DFA. */
  public FsmState initState;

  /** It specifies final states of DFA. */
  public Set<FsmState> finalStates;

  /** It specifies all states including the initial one and final ones. */
  public Set<FsmState> allStates;

  /**
   * It creates a Finite State Machine.
   *
   * @param initState it specifies the initial state.
   * @param allStates it specifies all the states.
   * @param finalStates it specifies the final states.
   */
  public Fsm(FsmState initState, Set<FsmState> finalStates, Set<FsmState> allStates) {

    this.initState = initState;
    this.allStates = allStates;
    this.finalStates = finalStates;
  }

  /** It creates a Finite State Machine used by Regular constraint constructor. */
  public Fsm() {

    finalStates = new HashSet<>();
    allStates = new HashSet<>();
  }

  /**
   * It computes a union of two Finite State Machines. Neither of the two Fsm is modified.
   *
   * @param other the other Fsm which is used in the union computation.
   * @return the resulting Fsm, which accepts the words accepted by this or the other Fsm.
   */
  public Fsm union(Fsm other) {
    Fsm result = new Fsm();
    Map<FsmState, FsmState> thisCopy = copyReachableStates(this, result.allStates);
    Map<FsmState, FsmState> otherCopy = copyReachableStates(other, result.allStates);

    // a fresh initial state with the outgoing transitions of both initial states
    result.initState = new FsmState();
    result.allStates.add(result.initState);
    copyOutgoingTransitions(thisCopy.get(initState), result.initState);
    copyOutgoingTransitions(otherCopy.get(other.initState), result.initState);

    addCopiedFinalStates(finalStates, thisCopy, result.finalStates);
    addCopiedFinalStates(other.finalStates, otherCopy, result.finalStates);
    if (finalStates.contains(initState) || other.finalStates.contains(other.initState)) {
      result.finalStates.add(result.initState);
    }
    return result;
  }

  /**
   * It does concatenation of two Fsm. Neither of the two Fsm is modified.
   *
   * @param other the Fsm with which the concatenation takes place.
   * @return the resulting Fsm, which accepts a word accepted by this Fsm followed by a word
   *     accepted by the other Fsm.
   */
  public Fsm concatenation(Fsm other) {
    Fsm result = new Fsm();
    Map<FsmState, FsmState> thisCopy = copyReachableStates(this, result.allStates);
    Map<FsmState, FsmState> otherCopy = copyReachableStates(other, result.allStates);

    result.initState = thisCopy.get(initState);
    FsmState otherInit = otherCopy.get(other.initState);
    for (FsmState f : finalStates) {
      FsmState copy = thisCopy.get(f);
      if (copy != null) {
        copyOutgoingTransitions(otherInit, copy);
      }
    }

    addCopiedFinalStates(other.finalStates, otherCopy, result.finalStates);
    if (other.finalStates.contains(other.initState)) {
      addCopiedFinalStates(finalStates, thisCopy, result.finalStates);
    }
    return result;
  }

  /**
   * It performs star operation on this Fsm. This Fsm is not modified.
   *
   * @return the resulting Fsm, which accepts any sequence of zero or more words accepted by this
   *     Fsm.
   */
  public Fsm star() {

    Fsm result = new Fsm();
    Map<FsmState, FsmState> copy = copyReachableStates(this, result.allStates);
    FsmState init = copy.get(initState);

    // a fresh initial state accepting the empty word
    result.initState = new FsmState();
    result.allStates.add(result.initState);
    copyOutgoingTransitions(init, result.initState);

    // after a complete word another word may start
    for (FsmState f : finalStates) {
      FsmState finalCopy = copy.get(f);
      if (finalCopy != null) {
        copyOutgoingTransitions(init, finalCopy);
      }
    }

    addCopiedFinalStates(finalStates, copy, result.finalStates);
    result.finalStates.add(result.initState);

    return result;
  }

  /**
   * It creates fresh copies, with new ids, of all states reachable from the initial state of a
   * given Fsm, including their transitions.
   *
   * @param fsm the Fsm whose states are copied.
   * @param allStates the set to which the copies are added.
   * @return the mapping from the original states to their copies.
   */
  private static Map<FsmState, FsmState> copyReachableStates(Fsm fsm, Set<FsmState> allStates) {
    Map<FsmState, FsmState> copy = new IdentityHashMap<>();
    Deque<FsmState> toVisit = new ArrayDeque<>();
    copy.put(fsm.initState, new FsmState());
    toVisit.add(fsm.initState);
    while (!toVisit.isEmpty()) {
      FsmState state = toVisit.poll();
      for (FsmTransition t : state.transitions) {
        if (!copy.containsKey(t.successor)) {
          copy.put(t.successor, new FsmState());
          toVisit.add(t.successor);
        }
      }
    }
    for (Map.Entry<FsmState, FsmState> entry : copy.entrySet()) {
      for (FsmTransition t : entry.getKey().transitions) {
        entry.getValue().addTransition(new FsmTransition(t.domain, copy.get(t.successor)));
      }
      allStates.add(entry.getValue());
    }
    return copy;
  }

  private static void copyOutgoingTransitions(FsmState from, FsmState to) {
    for (FsmTransition t : new ArrayList<>(from.transitions)) {
      to.addTransition(new FsmTransition(t.domain, t.successor));
    }
  }

  private static void addCopiedFinalStates(
      Set<FsmState> finalStates, Map<FsmState, FsmState> copy, Set<FsmState> result) {
    for (FsmState f : finalStates) {
      FsmState finalCopy = copy.get(f);
      // final states that are not reachable from the initial state are not copied
      if (finalCopy != null) {
        result.add(finalCopy);
      }
    }
  }

  /**
   * It gets state of a given id.
   *
   * @param id the id of the searched state.
   * @return the state of Fsm with a given id.
   */
  public FsmState getState(int id) {

    for (FsmState s : this.allStates) {
      if (s.id == id) {
        return s;
      }
    }

    return null;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder("digraph Fsm {\nnode [shape = doublecircle]; ");

    result.append(initState.id).append("; /* Init state */\n");

    result.append("node [shape = doubleoctagon]; ");

    for (FsmState s : finalStates) {
      result.append(s.id).append(" ");
    }

    result.append(";  /* Final states */\nnode [shape = circle];\n\n");

    for (FsmState s : allStates) {

      for (FsmTransition t : s.transitions) {
        result
            .append(s.id)
            .append(" -> ")
            .append(t.successor.id)
            .append(" [label = \"")
            .append(t.domain)
            .append("\"]\n");
      }
    }

    result.append("}\n");

    return result.toString();
  }

  /**
   * It resizes the Finite State Machine. All states get a new id between 0..n-1, where n is the
   * number of states.
   */
  public void resize() {

    int id = 0;

    for (FsmState s : this.allStates) {
      s.id = id++;
    }

    Set<FsmState> finalStates = new HashSet<>(this.finalStates);
    Set<FsmState> states = new HashSet<>(this.allStates);

    this.finalStates = finalStates;
    this.allStates = states;
  }

  /**
   * Computes the pruned outgoing-arc graph for the given variables. This performs a forward pass
   * (computing reachable states and intersecting transition domains with variable domains) followed
   * by a backward pass (removing paths that don't reach an accepting state). The FSM is resized
   * (state IDs renumbered 0..n-1) as a side effect.
   *
   * @param vars the variables whose domains constrain the transitions.
   * @return the outarc graph indexed by [level][fromState][toState].
   */
  private IntervalDomain[][][] computeOutarc(IntVar[] vars) {

    int levels = vars.length;
    int stateNumber = this.allStates.size();

    IntervalDomain[][][] outarc = new IntervalDomain[levels + 1][stateNumber][stateNumber];

    Set<FsmState> reachable = new HashSet<>();
    Set<FsmState> tmp = new HashSet<>();

    int level = 0;

    resize();
    FsmState[] array = new FsmState[stateNumber];
    for (FsmState s : this.allStates) {
      array[s.id] = s;
    }

    // Forward pass: compute reachable states and transition domains
    reachable.add(this.initState);
    level = doForwardPass(outarc, vars, levels, reachable, tmp, finalStates, level);

    // Backward pass: prune paths that don't reach an accepting state
    doBackwardPass(outarc, stateNumber, array, reachable, tmp, level);

    return outarc;
  }

  private int doForwardPass(
      IntervalDomain[][][] outarc,
      IntVar[] vars,
      int levels,
      Set<FsmState> reachable,
      Set<FsmState> tmp,
      Set<FsmState> finalStates,
      int level) {
    while (level < levels) {
      tmp.clear();
      for (FsmState s : reachable) {
        for (FsmTransition t : s.transitions) {
          IntDomain dom = t.domain.intersect(vars[level].dom());
          outarc[level][s.id][t.successor.id] = (IntervalDomain) dom;

          if (dom.getSize() > 0) {
            if (level < levels - 1) {
              tmp.add(t.successor);
            } else if (finalStates.contains(t.successor)) {
              tmp.add(t.successor);
            }
          }
        }
      }
      reachable.clear();
      reachable.addAll(tmp);
      level++;
    }
    return level;
  }

  private void doBackwardPass(
      IntervalDomain[][][] outarc,
      int stateNumber,
      FsmState[] array,
      Set<FsmState> reachable,
      Set<FsmState> tmp,
      int level) {
    while (level > 0) {
      tmp.clear();

      for (int i = 0; i < stateNumber; i++) {
        for (int j = 0; j < stateNumber; j++) {
          if (outarc[level - 1][j][i] != null && outarc[level - 1][j][i].getSize() > 0) {
            if (!reachable.contains(array[i])) {
              outarc[level - 1][j][i].clear();
            } else {
              tmp.add(array[j]);
            }
          }
        }
      }

      reachable.clear();
      reachable.addAll(tmp);
      level--;
    }
  }

  /**
   * Enumerates all valid tuples from the outarc graph, invoking the given action for each complete
   * tuple. Iterates over all level-0 arcs and recursively builds tuples from there.
   *
   * @param outarc the pruned outgoing-arc graph.
   * @param tuple the tuple array to fill (mutated in place).
   * @param action the action to perform on each complete tuple.
   */
  private void enumerateAllTuples(
      IntervalDomain[][][] outarc, int[] tuple, Consumer<int[]> action) {

    int stateNumber = this.allStates.size();

    for (int i = 0; i < stateNumber; i++) {
      for (int j = 0; j < stateNumber; j++) {
        if (outarc[0][i][j] != null && outarc[0][i][j].getSize() > 0) {
          final int nextState = j;
          forEachValueInArc(
              outarc[0][i][j],
              v -> {
                tuple[0] = v;
                enumerateTuples(nextState, 1, stateNumber, outarc, tuple, action);
              });
        }
      }
    }
  }

  /** Iterates over every value in the domain (all intervals) and invokes the consumer. */
  private void forEachValueInArc(IntervalDomain dom, IntConsumer withValue) {
    for (int h = 0; h < dom.size; h++) {
      Interval inv = dom.intervals[h];
      if (inv != null) {
        for (int v = inv.min(); v <= inv.max(); v++) {
          withValue.accept(v);
        }
      }
    }
  }

  /**
   * It creates an array of tuples representing this Regular context. It generates only the tuples
   * which are allowed in the current context of the store.
   *
   * @param vars variables in which context a list of tuples is created.
   * @return an array of tuples.
   */
  public int[][] transformIntoTuples(IntVar[] vars) {

    IntervalDomain[][][] outarc = computeOutarc(vars);
    int[] tuple = new int[vars.length];
    List<int[]> result = new ArrayList<>();

    enumerateAllTuples(outarc, tuple, t -> result.add(t.clone()));

    return result.toArray(new int[result.size()][]);
  }

  /**
   * Recursively enumerates all tuples from the outarc graph starting at the given level and
   * predecessor state, invoking the action for each complete tuple.
   *
   * @param prevSuc the predecessor state index.
   * @param level the current level (variable index).
   * @param stateNumber total number of states.
   * @param outarc the reachability graph.
   * @param tuple the tuple being built (mutated in place).
   * @param action the action to perform on each complete tuple.
   */
  private void enumerateTuples(
      int prevSuc,
      int level,
      int stateNumber,
      IntervalDomain[][][] outarc,
      int[] tuple,
      Consumer<int[]> action) {

    if (level == tuple.length) {
      action.accept(tuple);
      return;
    }

    for (int i = 0; i < stateNumber; i++) {
      if (outarc[level][prevSuc][i] != null && outarc[level][prevSuc][i].getSize() > 0) {
        final int nextState = i;
        forEachValueInArc(
            outarc[level][prevSuc][i],
            v -> {
              tuple[level] = v;
              enumerateTuples(nextState, level + 1, stateNumber, outarc, tuple, action);
            });
      }
    }
  }

  /**
   * It generates one by one tuples allowed by a Regular constraint, which are added to the Mdd
   * being built. After all tuples are added Mdd is being reduced. The standard Mdd creating
   * procedure employed in paper presenting Mdd based extensional constraint. It generates only the
   * tuples which are allowed in the current context of the store.
   *
   * @param vars variables in which context Mdd is being created from Regular constraint.
   * @return Mdd representing the same constraint as Regular.
   */
  public Mdd transformIntoMdd(IntVar[] vars) {

    IntervalDomain[][][] outarc = computeOutarc(vars);
    int[] tuple = new int[vars.length];

    Mdd result = new Mdd(vars);
    enumerateAllTuples(outarc, tuple, result::addTuple);

    result.reduce();
    return result;
  }

  /**
   * It generates one by one tuples allowed by a Regular constraint, which are added to the Mdd
   * being built. After all tuples are added Mdd is being reduced. The standard Mdd creating
   * procedure employed in paper presenting Mdd based extensional constraint. It generates only the
   * tuples which are allowed in the current context of the store.
   *
   * @param vars variables in which context Mdd is being created from Regular constraint.
   * @return Mdd representing the same constraint as Regular.
   */
  public Mdd transformDirectlyIntoMdd(IntVar[] vars) {

    IntervalDomain[][][] outarc = computeOutarc(vars);
    int stateNumber = this.allStates.size();

    int[] positions = new int[(vars.length + 1) * stateNumber];

    Mdd result = new Mdd(vars);
    positions[initState.id] = 0;
    // not needed as constructor is already doing it.
    // result.freePosition += vars[0].getSize();

    for (int l = 0; l < vars.length; l++) {
      for (int i = 0; i < stateNumber; i++) {
        for (int j = 0; j < stateNumber; j++) {
          if (outarc[l][i][j] != null && outarc[l][i][j].getSize() > 0) {
            addArcToMdd(result, vars, outarc[l][i][j], positions, stateNumber, l, i, j);
          }
        }
      }
    }
    return result;
  }

  private void addArcToMdd(
      Mdd result,
      IntVar[] vars,
      IntervalDomain arcDom,
      int[] positions,
      int stateNumber,
      int level,
      int fromState,
      int toState) {
    ValueEnumeration enumer = arcDom.valueEnumeration();
    while (enumer.hasMoreElements()) {
      int nextElement = enumer.nextElement();
      int indexOfValue = result.findPosition(nextElement, result.views[level].indexToValue);

      if (positions[level * stateNumber + fromState] == 0
          && (level != 0 || fromState != initState.id)) {
        positions[level * stateNumber + fromState] = result.freePosition;
        result.freePosition += vars[level].getSize();
        result.freePosition += result.domainLimits[level];
      }
      if (positions[(level + 1) * stateNumber + toState] == 0) {
        positions[(level + 1) * stateNumber + toState] = result.freePosition;
        if (level + 1 < vars.length) {
          result.freePosition += result.domainLimits[level + 1];
        }
      }
      int pos = positions[level * stateNumber + fromState] + indexOfValue;
      result.ensureSize(pos + 1);
      result.diagram[pos] =
          level + 1 < vars.length ? positions[(level + 1) * stateNumber + toState] : Mdd.TERMINAL;
    }
  }
}
