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
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ExtensionalSupportStr;
import org.jacop.constraints.In;
import org.jacop.constraints.XeqC;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;

/**
 * Regular constraint accepts only the assignment to variables which is accepted by an automaton. It
 * achieves generalized arc consistency (domain consistency).
 *
 * <p>The automaton is unfolded into a layered graph with one layer of edges per variable, which is
 * propagated by {@link LayeredGraphConstraint}.
 *
 * @author Polina Makeeva and Radoslaw Szymanek
 * @version 5.0
 */
public class Regular extends LayeredGraphConstraint implements Copyable<Regular> {

  /** It specifies if debugging information should be printed out. */
  public static final boolean DEBUG_ALL = false;

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies finite state machine used by this regular. */
  public final Fsm fsm;

  List<Constraint> constraints;

  /**
   * It constructs a regular constraint.
   *
   * @param fsm (deterministic) finite automaton
   * @param list variables which values have to be accepted by the automaton.
   */
  public Regular(Fsm fsm, IntVar[] list) {
    super(list, 3);
    this.fsm = fsm;
    numberId = idNumber.incrementAndGet();
  }

  /**
   * It unfolds the automaton into the layered graph. A forward pass collects the states reachable
   * at each layer, a backward pass keeps the states from which a final state can be reached, and
   * only the edges between kept states are described. All work is proportional to the number of
   * reachable states and their transitions.
   */
  @Override
  protected void describeGraph(LayeredGraphDescription graph) {
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

    for (int level = 0; level <= levels; level++) {
      graph.setNodes(level, levelNodeCount[level]);
    }
    for (int level = 0; level < levels; level++) {
      for (int i = 0; i < node[level].length; i++) {
        if (node[level][i] < 0) {
          continue;
        }
        for (int k = 0; k < arcSuccessors[level][i].length; k++) {
          for (ValueEnumeration e = arcDomains[level][i][k].valueEnumeration();
              e.hasMoreElements(); ) {
            graph.addEdge(level, node[level][i], e.nextElement(), arcSuccessors[level][i][k]);
          }
        }
      }
    }
  }

  @Override
  protected boolean explainedByPaths() {
    return getClass() == Regular.class;
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

  @Override
  public Regular copy(VarMap map) {
    Regular copy = new Regular(fsm, map.get(list));
    copyEngineTo(copy);
    return copy;
  }
}
