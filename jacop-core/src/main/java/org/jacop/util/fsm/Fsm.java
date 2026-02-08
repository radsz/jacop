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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
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
 * @version 4.10
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
   * It computes a union of two Finite State Machines.
   *
   * @param other the other Fsm which is used in the union computation.
   * @return the resulting Fsm.
   */
  public Fsm union(Fsm other) {

    Fsm result = new Fsm();

    result.initState = new FsmState();

    result.allStates.add(result.initState);

    for (FsmTransition t : initState.transitions) {

      FsmState addState = t.successor.deepClone(result.allStates);

      result.initState.addTransition(new FsmTransition(t.domain, addState));
    }

    for (FsmState f : finalStates) {
      result.finalStates.add(f.deepClone(result.allStates));
    }

    for (FsmTransition t : other.initState.transitions) {
      FsmState addState = t.successor.deepClone(result.allStates);
      result.initState.addTransition(new FsmTransition(t.domain, addState));
    }

    for (FsmState f : other.finalStates) {
      result.finalStates.add(f.deepClone(result.allStates));
    }

    return result;
  }

  /**
   * It does concatenation of two Fsm.
   *
   * @param other the Fsm with which the concatenation takes place.
   * @return the resulting Fsm.
   */
  public Fsm concatenation(Fsm other) {

    Fsm result = new Fsm();

    boolean otherIsStar =
        other.finalStates.size() == 1 && other.finalStates.contains(other.initState);

    result.initState = initState.deepClone(result.allStates);

    for (FsmState f : finalStates) {

      FsmState ff = f.deepClone(result.allStates);

      for (FsmTransition t : other.initState.transitions) {

        FsmState addState = t.successor.deepClone(result.allStates);
        ff.addTransition(new FsmTransition(t.domain, addState));

        if (otherIsStar) {
          for (FsmState s : result.allStates) {
            for (FsmTransition ts : s.transitions) {
              if (ts.successor.id == other.initState.id) {
                ts.successor = ff;
              }
            }
          }
          result.allStates.remove(other.initState);
        }
      }
    }

    if (!otherIsStar) {
      for (FsmState f : other.finalStates) {
        result.finalStates.add(f.deepClone(result.allStates));
      }
    } else {
      for (FsmState f : finalStates) {
        result.finalStates.add(f.deepClone(result.allStates));
      }
    }

    return result;
  }

  /**
   * It performs star operation on this Fsm.
   *
   * @return the resulting Fsm.
   */
  public Fsm star() {

    Fsm result = new Fsm();

    result.initState = new FsmState(initState);

    result.allStates.add(result.initState);

    List<FsmState> set = new ArrayList<>();

    set.add(result.initState);

    int length = 1;
    FsmState s;

    for (int i = 0; i < length; i++) {
      s = set.get(i);
      FsmState orgS = getState(s.id);
      for (FsmTransition t : orgS.transitions) {
        if (!finalStates.contains(t.successor)) {
          FsmState suc = result.getState(t.successor.id);
          if (suc == null) {
            suc = new FsmState(t.successor);
            result.allStates.add(suc);
            set.add(suc);
            length = length + 1;
          }
          s.addTransition(new FsmTransition(t.domain, suc));
        } else {
          s.addTransition(new FsmTransition(t.domain, result.initState));
        }
      }
    }
    result.finalStates.add(result.initState);

    return result;
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

      //       result.append( s.id ).append("\n");

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
   * It creates an array of tuples representing this Regular context. It generates only the tuples
   * which are allowed in the current context of the store.
   *
   * @param vars variables in which context a list of tuples is created.
   * @return an array of tuples.
   */
  public int[][] transformIntoTuples(IntVar[] vars) {

    int levels = vars.length;
    int stateNumber = this.allStates.size();

    // The array that keep all possible states with arcs and their domains
    // If the domain is empty then the arc doesn't exist
    IntervalDomain[][][] outarc = new IntervalDomain[levels + 1][stateNumber][stateNumber];

    // Reachable region of the graph
    Set<FsmState> reachable = new HashSet<>();
    // Temporal variable for reachable region
    Set<FsmState> tmp = new HashSet<>();

    // The id's of the states are renamed to make the future graph in latex look pretty
    int level = 0;

    resize();
    FsmState[] array = new FsmState[stateNumber];
    for (FsmState s : this.allStates) {
      array[s.id] = s;
    }

    // ----- compute the reachable region of the graph -----

    // Start with initial state
    reachable.add(this.initState);

    while (level < levels) {
      // prepare tmp set of reachable states in the next level
      tmp.clear();
      // For each state reached until now
      for (FsmState s : reachable) {
        // watch it's edges
        for (FsmTransition t : s.transitions) {
          // prepare the set of values of this edge
          IntDomain dom = t.domain.intersect(vars[level].dom());
          outarc[level][s.id][t.successor.id] = (IntervalDomain) dom;

          /* If the edge is not empty them add the state to tmp set
           * check that such states wasn't previously added.
           *
           * If the level is the last, then check whether the state
           * belongs to the set of accepted states
           */

          if (dom.getSize() > 0) {
            if (level < levels - 1) {
              tmp.add(t.successor);
            } else if (finalStates.contains(t.successor)) {
              tmp.add(t.successor);
            }
          }
        }
      }
      // copy the tmp set of states into reachable region
      reachable.clear();
      reachable.addAll(tmp);
      // got to next level
      level++;
    }

    /* ----- delete the paths of the graph that doesn't reach the accepted state -----
     *
     *
     *  by calculating the reachable region of the graph starting from the accepted
     *  states and following the edges in the opposite direction.
     */

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

    IntervalDomain dom;
    int[] tuple = new int[levels];
    List<int[]> result = new ArrayList<>();

    for (int i = 0; i < stateNumber; i++) {
      for (int j = 0; j < stateNumber; j++) {
        if (outarc[0][i][j] != null && outarc[0][i][j].getSize() > 0) {
          dom = outarc[0][i][j];
          for (int h = 0; h < dom.size; h++) {
            Interval inv = dom.intervals[h];
            // for each interval of val
            if (inv != null) {
              // For each value of the interval
              for (int v = inv.min(); v <= inv.max(); v++) {
                tuple[0] = v;
                recursiveCall(j, 1, stateNumber, outarc, tuple, result);
              }
            }
          }
        }
      }
    }

    return result.toArray(new int[result.size()][]);
  }

  // Recursive function used to create a list of tuples.
  private void recursiveCall(
      int prevSuc,
      int level,
      int stateNumber,
      IntervalDomain[][][] outarc,
      int[] tuple,
      List<int[]> tuples) {

    if (level == tuple.length) {
      tuples.add(tuple.clone());
      return;
    }

    IntervalDomain dom;

    for (int i = 0; i < stateNumber; i++) {
      if (outarc[level][prevSuc][i] != null && outarc[level][prevSuc][i].getSize() > 0) {
        dom = outarc[level][prevSuc][i];

        for (int h = 0; h < dom.size; h++) {

          Interval inv = dom.intervals[h];

          if (inv != null) {
            // For each value of the interval
            for (int v = inv.min(); v <= inv.max(); v++) {
              tuple[level] = v;
              recursiveCall(i, level + 1, stateNumber, outarc, tuple, tuples);
            }
          }
        }
      }
    }
  }

  // It recursively creates
  private void recursiveCall(
      int prevSuc,
      int level,
      int stateNumber,
      IntervalDomain[][][] outarc,
      int[] tuple,
      Mdd result) {

    if (level == tuple.length) {
      // it adds a tuple to an Mdd.
      result.addTuple(tuple);
      return;
    }

    IntervalDomain dom;

    for (int i = 0; i < stateNumber; i++) {
      if (outarc[level][prevSuc][i] != null && outarc[level][prevSuc][i].getSize() > 0) {

        dom = outarc[level][prevSuc][i];

        for (int h = 0; h < dom.size; h++) {

          Interval inv = dom.intervals[h];

          if (inv != null) {
            // For each value of the interval
            for (int v = inv.min(); v <= inv.max(); v++) {
              tuple[level] = v;
              recursiveCall(i, level + 1, stateNumber, outarc, tuple, result);
            }
          }
        }
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

    int levels = vars.length;
    int stateNumber = this.allStates.size();

    // The array that keep all possible states with arcs and their domains
    // If the domain is empty then the arc doesn't exist
    IntervalDomain[][][] outarc = new IntervalDomain[levels + 1][stateNumber][stateNumber];

    // Reachable region of the graph
    Set<FsmState> reachable = new HashSet<>();
    // Temporal variable for reachable region
    Set<FsmState> tmp = new HashSet<>();

    // The id's of the states are renamed to make the future graph in latex look pretty
    int level = 0;

    resize();
    FsmState[] array = new FsmState[stateNumber];
    for (FsmState s : this.allStates) {
      array[s.id] = s;
    }

    // ----- compute the reachable region of the graph -----

    // Start with initial state
    reachable.add(this.initState);

    while (level < levels) {
      // prepare tmp set of reachable states in the next level
      tmp.clear();
      // For each state reached until now
      for (FsmState s : reachable) {
        // watch it's edges
        for (FsmTransition t : s.transitions) {
          // prepare the set of values of this edge
          IntDomain dom = t.domain.intersect(vars[level].dom());
          outarc[level][s.id][t.successor.id] = (IntervalDomain) dom;

          /* If the edge is not empty them add the state to tmp set
           * check that such states wasn't previously added.
           *
           * If the level is the last, then check whether the state
           * belongs to the set of accepted states
           */

          if (dom.getSize() > 0) {
            if (level < levels - 1) {
              tmp.add(t.successor);
            } else if (finalStates.contains(t.successor)) {
              tmp.add(t.successor);
            }
          }
        }
      }

      // copy the tmp set of states into reachable region
      reachable.clear();
      reachable.addAll(tmp);
      // got to next level
      level++;
    }

    /* ----- delete the paths of the graph that doesn't reach the accepted state -----
     *
     *
     *  by calculating the reachable region of the graph starting from the accepted
     *  states and following the edges in the opposite direction.
     */

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

    IntervalDomain dom;
    int[] tuple = new int[levels];

    Mdd result = new Mdd(vars);
    // Part exploring all tuples and adding one by one to Mdd.
    for (int i = 0; i < stateNumber; i++) {
      for (int j = 0; j < stateNumber; j++) {
        // for level 0 (first variable in the tuple)
        if (outarc[0][i][j] != null && outarc[0][i][j].getSize() > 0) {
          dom = outarc[0][i][j];
          for (int h = 0; h < dom.size; h++) {
            Interval inv = dom.intervals[h];
            // for each interval of val
            if (inv != null) {
              // For each value of the interval
              for (int v = inv.min(); v <= inv.max(); v++) {
                tuple[0] = v;
                recursiveCall(j, 1, stateNumber, outarc, tuple, result);
              }
            }
          }
        }
      }
    }

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

    int levels = vars.length;
    int stateNumber = this.allStates.size();

    // The array that keep all possible states with arcs and their domains
    // If the domain is empty then the arc doesn't exist
    IntervalDomain[][][] outarc = new IntervalDomain[levels + 1][stateNumber][stateNumber];

    // Reachable region of the graph
    Set<FsmState> reachable = new HashSet<>();
    // Temporal variable for reachable region
    Set<FsmState> tmp = new HashSet<>();

    // The id's of the states are renamed to make the future graph in latex look pretty
    int level = 0;

    resize();
    FsmState[] array = new FsmState[stateNumber];
    for (FsmState s : this.allStates) {
      array[s.id] = s;
    }

    // ----- compute the reachable region of the graph -----

    // Start with initial state
    reachable.add(this.initState);

    while (level < levels) {

      // prepare tmp set of reachable states in the next level
      tmp.clear();
      // For each state reached until now
      for (FsmState s : reachable) {
        // watch it's edges
        for (FsmTransition t : s.transitions) {
          // prepare the set of values of this edge
          IntDomain dom = t.domain.intersect(vars[level].dom());
          outarc[level][s.id][t.successor.id] = (IntervalDomain) dom;

          /* If the edge is not empty them add the state to tmp set
           * check that such states wasn't previously added.
           *
           * If the level is the last, then check whether the state
           * belongs to the set of accepted states
           */

          if (dom.getSize() > 0) {
            if (level < levels - 1) {
              tmp.add(t.successor);
            } else if (finalStates.contains(t.successor)) {
              tmp.add(t.successor);
            }
          }
        }
      }

      // copy the tmp set of states into reachable region
      reachable.clear();
      reachable.addAll(tmp);
      // got to next level
      level++;
    }

    /* ----- delete the paths of the graph that doesn't reach the accepted state -----
     *
     *
     *  by calculating the reachable region of the graph starting from the accepted
     *  states and following the edges in the opposite direction.
     */

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

    int[] positions = new int[(vars.length + 1) * stateNumber];

    Mdd result = new Mdd(vars);
    positions[initState.id] = 0;
    // not needed as constructor is already doing it.
    // result.freePosition += vars[0].getSize();

    // Part exploring all tuples and adding one by one to Mdd.
    for (int l = 0; l < vars.length; l++) {
      for (int i = 0; i < stateNumber; i++) {
        for (int j = 0; j < stateNumber; j++) {
          // for level 0 (first variable in the tuple)
          if (outarc[l][i][j] != null && outarc[l][i][j].getSize() > 0) {

            // There is an arc from state i to state j at level 0.
            ValueEnumeration enumer = outarc[l][i][j].valueEnumeration();

            while (enumer.hasMoreElements()) {

              int nextElement = enumer.nextElement();

              int indexOfValue = result.findPosition(nextElement, result.views[l].indexToValue);

              if (positions[l * stateNumber + i] == 0 && !(l == 0 && i == initState.id)) {
                positions[l * stateNumber + i] = result.freePosition;
                result.freePosition += vars[l].getSize();
                result.freePosition += result.domainLimits[l];
              }

              if (positions[(l + 1) * stateNumber + j] == 0) {
                positions[(l + 1) * stateNumber + j] = result.freePosition;
                if (l + 1 < vars.length) {
                  result.freePosition += result.domainLimits[l + 1];
                }
              }

              if (l + 1 < vars.length) {
                result.ensureSize(positions[l * stateNumber + i] + indexOfValue + 1);
                result.diagram[positions[l * stateNumber + i] + indexOfValue] =
                    positions[(l + 1) * stateNumber + j];
              } else {
                result.ensureSize(positions[l * stateNumber + i] + indexOfValue + 1);
                result.diagram[positions[l * stateNumber + i] + indexOfValue] = Mdd.TERMINAL;
              }
            }
          }
        }
      }
    }

    return result;
  }
}
