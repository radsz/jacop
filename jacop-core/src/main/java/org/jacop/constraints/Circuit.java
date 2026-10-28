/*
 * Circuit.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.constraints;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.VarMap;
import org.jacop.core.InitOnce;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.MutableVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Circuit constraint assures that all variables build a Hamiltonian circuit. Value of every
 * variable x[i] points to the next variable in the circuit. Variables create one circuit.
 *
 * <p>Variables are numbered from 1 by default, so x[i] = j means that the successor of the i-th
 * variable (counted from 1) is the j-th one. With an offset, they are numbered from the offset
 * instead; for example offset 0 numbers them from 0.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Circuit extends Alldiff implements Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  // a circuit has no dominator pruning to suggest roots to its explanations
  private static final int[] NO_ROOTS = {};
  final int[] val;
  private final int[] low;
  private final int[] dfsNode;
  private final int[] dfsValue;
  final Map<Var, Integer> valueIndex = new HashMap<>();
  int chainLength;

  /** One-time work of the first consistency call. */
  final InitOnce init = new InitOnce();

  MutableVar[] graph;
  int idd;

  /** The number of the first variable, that is the value pointing to list[0]. */
  final int offset;

  /** The value pointing to a node minus the node number used by the chains (1..n), offset - 1. */
  private final int shift;

  /**
   * It constructs a circuit constraint.
   *
   * @param list variables which must form a circuit.
   */
  public Circuit(IntVar[] list) {
    this(list, 1);
  }

  /**
   * It constructs a circuit constraint whose variables are numbered from the given offset.
   *
   * @param list variables which must form a circuit.
   * @param offset the value that points to list[0]; list[i] is pointed to by offset + i.
   */
  public Circuit(IntVar[] list, int offset) {

    checkInputForNullness("list", list);
    checkInputForDuplication("list", list);
    if ((long) offset < IntDomain.MIN_INT || (long) offset + list.length - 1 > IntDomain.MAX_INT) {
      throw new IllegalArgumentException(
          "Circuit has values "
              + offset
              + ".."
              + ((long) offset + list.length - 1)
              + " out of range");
    }

    this.offset = offset;
    this.shift = offset - 1;

    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.queueIndex = 2;

    int i = 0;
    for (Var v : list) {
      valueIndex.put(v, i++);
    }

    val = new int[list.length];
    low = new int[list.length];
    dfsNode = new int[list.length];
    dfsValue = new int[list.length];

    setScope(list);
  }

  /**
   * It constructs a circuit constraint.
   *
   * @param list variables which must form a circuit.
   */
  public Circuit(List<? extends IntVar> list) {
    this(list.toArray(new IntVar[0]));
  }

  /**
   * It constructs a circuit constraint whose variables are numbered from the given offset.
   *
   * @param list variables which must form a circuit.
   * @param offset the value that points to the first variable of the list.
   */
  public Circuit(List<? extends IntVar> list, int offset) {
    this(list.toArray(new IntVar[0]), offset);
  }

  // Alldiff queues only grounded variables, but consistency() here reads every changed variable
  // from variableQueue.
  @Override
  public void queueVariable(int level, Var v) {
    variableQueue.add((IntVar) v);
  }

  @Override
  public void consistency(Store store) {

    if (init.begin(store)) {
      for (int i = 0; i < list.length; i++) {
        list[i].domain.in(store.level, list[i], offset, shift + list.length);
        list[i].domain.inComplement(store.level, list[i], offset + i);
      }
    }

    do {

      store.propagationHasOccurred = false;

      LinkedHashSet<IntVar> fdvs = variableQueue;
      variableQueue = new LinkedHashSet<>();

      propagateAllDifferentOnSingletons(store, fdvs);

      oneCircuit(store, fdvs);

    } while (store.propagationHasOccurred);

    sccs(); // strongly connected components
  }

  int firstNode(int current) {
    int start = current;
    int first;
    do {
      first = ((CircuitVarValue) graph[current - 1].value()).previous;
      if (first != 0 && first != start) {
        current = first;
        chainLength++;
      }
    } while (first != 0 && first != start);
    return current;
  }

  // registers the constraint in the constraint store
  @Override
  public void impose(Store store) {

    super.impose(store);

    graph = new CircuitVar[list.length];
    for (int j = 0; j < graph.length; j++) {
      graph[j] = new CircuitVar(store, 0, 0);
    }
  }

  int lastNode(int current) {
    int start = current;
    int last;
    do {
      last = ((CircuitVarValue) graph[current - 1].value()).next;
      if (last != 0) {
        current = last;
        if (++chainLength > graph.length) {
          throw Store.failException;
        }
      }
    } while (last != 0 && last != start);
    if (last == current) {
      chainLength = 0;
    }
    return current;
  }

  void oneCircuit(Store store, LinkedHashSet<IntVar> fdvs) {

    IntDomain dom;

    for (IntVar v : fdvs) {
      dom = v.dom();
      if (dom.singleton()) {
        updateChains(v);
        int qMin = dom.min() - shift;

        chainLength = 0;
        int lastInChain = lastNode(qMin);
        int firstInChain = firstNode(qMin);
        if (chainLength < list.length - 1) {
          list[lastInChain - 1].domain.inComplement(
              store.level, list[lastInChain - 1], firstInChain + shift);
        }
      }
    }
  }

  // redesign satisfied function since the implementation of alldiff has changed.
  @Override
  public int getDefaultConsistencyPruningEvent() {
    // the circuit reasoning uses every value of the domains, not only their bounds
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {

    if (grounded.value() != list.length) {
      return false;
    }

    boolean sat = super.satisfied(); // alldifferent

    if (sat) {
      int i = 0;
      int no = 0;
      do {
        i = list[i].min() - offset;
        no++;
      } while (no < list.length && i != 0);
      if (no != list.length || i != 0) {
        return false;
      }
    }
    return sat;
  }

  // --- Strongly Connected Conmponents

  // Uses Tarjan's algorithm to check that the graph of the domains is one strongly connected
  // component; otherwise no Hamiltonian circuit exists and failure is enforced. Based on the
  // algorithm from the book Robert Sedgewick, Algorithms, 1988, p. 482.

  void sccs() {

    Arrays.fill(val, 0);
    idd = 0;

    // iterative depth-first search from node 0 (recursion overflows the stack for large circuits)
    int n = list.length;
    int sp = 0;
    push(0, sp++);
    while (sp > 0) {
      int k = dfsNode[sp - 1];
      IntDomain dom = list[k].dom();
      int last = dfsValue[sp - 1];
      if (last < dom.max()) {
        int value = last < dom.min() ? dom.min() : dom.nextValue(last);
        dfsValue[sp - 1] = value;
        int t = value - offset;
        if (val[t] == 0) {
          push(t, sp++);
        } else if (val[t] < low[k]) {
          low[k] = val[t];
        }
        continue;
      }
      if (low[k] == val[k]) {
        // k is the root of a strongly connected component. It is the first component completed
        // (the search stops at the first one), so all visited nodes are still in the Tarjan stack
        // and low is the exact lowlink. The graph is strongly connected only if this component
        // is rooted at node 0 and contains all nodes.
        if (k != 0 || idd != n) {
          throw Store.failException;
        }
      }
      sp--;
      if (sp > 0 && low[k] < low[dfsNode[sp - 1]]) {
        low[dfsNode[sp - 1]] = low[k];
      }
    }
  }

  private void push(int k, int sp) {
    idd++;
    val[k] = idd;
    low[k] = idd;
    dfsNode[sp] = k;
    dfsValue[sp] = Integer.MIN_VALUE;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : circuit([");
    appendArrayToString(result, list);
    result.append(']');
    if (offset != 1) {
      result.append(", ").append(offset);
    }
    result.append(')');

    return result.toString();
  }

  // --- Strongly Connected Conmponents

  void updateChains(IntVar v) {

    int i = valueIndex.get(v);
    int vMin = v.min() - shift;

    graph[i].update(new CircuitVarValue(vMin, ((CircuitVarValue) graph[i].value()).previous));
    graph[vMin - 1].update(
        new CircuitVarValue(((CircuitVarValue) graph[vMin - 1].value()).next, i + 1));
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    int mark = out.size();
    if (SubcircuitExplanation.explain(trail, entry, list, offset, true, NO_ROOTS, out)) {
      return true;
    }
    out.truncate(mark);
    return AlldiffExplanation.explain(trail, entry, list, new IntervalDomain(), out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return SubcircuitExplanation.explainFailure(trail, list, offset, true, NO_ROOTS, out);
  }

  @Override
  public Circuit copy(VarMap map) {
    return new Circuit(map.get(list), offset);
  }
}
