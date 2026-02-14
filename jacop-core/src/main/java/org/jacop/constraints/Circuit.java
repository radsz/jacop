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
import org.jacop.api.Stateful;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.MutableVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Circuit constraint assures that all variables build a Hamiltonian circuit. Value of every
 * variable x[i] points to the next variable in the circuit. Variables create one circuit.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Circuit extends Alldiff implements Stateful {

  static final AtomicInteger idNumber = new AtomicInteger(0);
  final int[] val;
  final Map<Var, Integer> valueIndex = new HashMap<>();
  int chainLength;
  boolean firstConsistencyCheck = true;
  MutableVar[] graph;
  int idd;
  int sccLength;
  int firstConsistencyLevel;

  /**
   * It constructs a circuit constraint.
   *
   * @param list variables which must form a circuit.
   */
  public Circuit(IntVar[] list) {

    checkInputForNullness("list", list);
    checkInputForDuplication("list", list);

    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.queueIndex = 2;

    int i = 0;
    for (Var v : list) {
      valueIndex.put(v, i++);
    }

    val = new int[list.length];

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

  @Override
  public void consistency(Store store) {

    if (firstConsistencyCheck) {
      for (int i = 0; i < list.length; i++) {
        list[i].domain.in(store.level, list[i], 1, list.length);
        list[i].domain.inComplement(store.level, list[i], i + 1);
      }
      firstConsistencyCheck = false;
      firstConsistencyLevel = store.level;
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

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
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
        int Qmin = dom.min();

        chainLength = 0;
        int lastInChain = lastNode(Qmin);
        int firstInChain = firstNode(Qmin);
        if (chainLength < list.length - 1) {
          list[lastInChain - 1].domain.inComplement(
              store.level, list[lastInChain - 1], firstInChain);
        }
      }
    }
  }

  // @todo, what if there is a small circuit ending with zero, it is not consistent but can be
  // satisfied.
  // redesign satisfied function since the implementation of alldiff has changed.
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
        i = list[i].min() - 1;
        no++;
      } while (no < list.length && i != 0);
      if (no != list.length || i != 0) {
        return false;
      }
    }
    return sat;
  }

  // --- Strongly Connected Conmponents

  // Uses Trajan's algorithm to find strongly connected components
  // if found strongly connected component is shorter than the
  // Hamiltonian circuit length fail is enforced (one is unable to
  // to build a circuit. Based on the algorithm from the book
  // Robert Sedgewick, Algorithms, 1988, p. 482.

  void sccs() {

    Arrays.fill(val, 0);
    idd = 0;

    sccLength = 0;
    visit(0);
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : circuit([");
    appendArrayToString(result, list);
    result.append("])");

    return result.toString();
  }

  // --- Strongly Connected Conmponents

  @Override
  public void removeLevel(int level) {
    if (firstConsistencyLevel == level) {
      firstConsistencyCheck = true;
    }
  }

  void updateChains(IntVar v) {

    int i = valueIndex.get(v);
    int vMin = v.min();

    graph[i].update(new CircuitVarValue(vMin, ((CircuitVarValue) graph[i].value()).previous));
    graph[vMin - 1].update(
        new CircuitVarValue(((CircuitVarValue) graph[vMin - 1].value()).next, i + 1));
  }

  int visit(int k) {

    idd++;
    val[k] = idd;
    int min = idd;
    sccLength++;
    for (ValueEnumeration e = list[k].dom().valueEnumeration(); e.hasMoreElements(); ) {
      int t = e.nextElement() - 1;
      int m;
      if (val[t] == 0) {
        m = visit(t);
      } else {
        m = val[t];
      }
      if (m < min) {
        min = m;
      }
    }
    if (min == val[k]) {
      if (sccLength != list.length && sccLength != 0) {
        // the scc is shorter than all nodes in the circuit constraints
        sccLength = 0;
        throw Store.failException;
      }
      sccLength = 0;
    }
    return min;
  }
}
