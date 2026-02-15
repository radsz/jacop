/*
 * Subcircuit.java
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
import java.util.BitSet;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.util.SophisticatedLengauerTarjan;

/**
 * Subcircuit constraint assures that all variables build a subcircuit. Value of every variable x[i]
 * points to the next variable in the subcircuit. If a variable does not belong to a subcircuit it
 * has value of its position, i.e., x[i] = i.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Subcircuit extends Alldiff {

  static final AtomicInteger idNumber = new AtomicInteger(0);
  final int[] val;
  final Map<Var, Integer> valueIndex = new HashMap<>();
  final SophisticatedLengauerTarjan graphDominance;
  final int[] stack; // stack for strongly connected compoents algorithm
  boolean firstConsistencyCheck = true;
  boolean useScc = true;
  boolean useDominance = true;
  int idd;
  int sccLength;
  int firstConsistencyLevel;
  int sccCounter;
  int stack_pointer;
  BitSet cycleVar;

  /**
   * It constructs a circuit constraint.
   *
   * @param list variables which must form a circuit.
   */
  public Subcircuit(IntVar[] list) {

    checkInputForNullness("list", list);
    checkInputForDuplication("list", list);

    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.graphDominance = new SophisticatedLengauerTarjan(list.length + 1);

    this.queueIndex = 2;

    int i = 0;
    for (Var v : list) {
      valueIndex.put(v, i++);
    }

    val = new int[list.length];

    stack = new int[list.length];
    stack_pointer = 0;

    String scc = System.getProperty("sub_circuit_scc_pruning");
    String dominance = System.getProperty("sub_circuit_dominance_pruning");
    if (scc != null) {
      useScc = Boolean.parseBoolean(scc);
    }
    if (dominance != null) {
      useDominance = Boolean.parseBoolean(dominance);
    }
    if (!useScc && !useDominance) {
      throw new IllegalArgumentException("Wrong property configuration for Subcircuit");
    }

    setScope(list);
  }

  /**
   * It constructs a circuit constraint.
   *
   * @param list variables which must form a circuit.
   */
  public Subcircuit(List<? extends IntVar> list) {
    this(list.toArray(new IntVar[0]));
  }

  @Override
  public void consistency(Store store) {

    if (firstConsistencyCheck) {
      for (IntVar intVar : list) {
        intVar.domain.in(store.level, intVar, 1, list.length);
      }

      firstConsistencyCheck = false;
      firstConsistencyLevel = store.level;
    }

    do {

      store.propagationHasOccurred = false;

      LinkedHashSet<IntVar> fdvs = variableQueue;
      variableQueue = new LinkedHashSet<>();

      propagateAllDifferentOnSingletons(store, fdvs);

    } while (store.propagationHasOccurred);

    if (useScc) {
      sccsBasedPruning(store); // strongly connected components

      if (store.propagationHasOccurred) {
        sccCounter = 0;
      }

      // if 10 consecutive applications of SCC based pruning did
      // not give any pruning try domianance based pruning
      if (useDominance && sccCounter++ > 10) {
        sccCounter = 0;
        dominanceFilter(); // filter based on dominance of nodes
      }
    } else if (useDominance) {
      dominanceFilter(); // filter based on dominance of nodes
    }
    if (store.propagationHasOccurred) {
      store.addChanged(this);
    }
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {

    // If consistency function mode
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }
    return IntDomain.ANY;
  }

  // --- Strongly Connected Conmponents

  // Uses Trajan's algorithm to find strongly connected components
  // Based on the algorithm from the book
  // Robert Sedgewick, Algorithms, 1988, p. 482.

  boolean needsListPruning() {

    for (IntVar el : list) {
      if (!(el.min() >= 1 && el.max() <= list.length)) {
        return true;
      }
    }
    return false;
  }

  // registers the constraint in the constraint store
  @Override
  public void impose(Store store) {

    this.store = store;

    super.impose(store);

    if (!needsListPruning()) {
      firstConsistencyCheck = false;
    }
  }

  @Override
  public boolean satisfied() {

    if (grounded.value() != list.length) {
      return false;
    }

    boolean sat = super.satisfied(); // alldifferent

    if (sat) {
      // check if there are subcricuits that together cover all nodes
      sat = sccs() == list.length;
    }
    return sat;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : subcircuit([");
    appendArrayToString(result, list);
    result.append("])");

    return result.toString();
  }

  private void sccsBasedPruning(Store store) {
    Arrays.fill(val, 0);
    idd = 0;
    BitSet realCycle = null;

    for (int i = 0; i < list.length; i++) {
      sccLength = 0;
      if (val[i] != 0) {
        continue;
      }
      visit(i);
      if (sccLength == 1) {
        list[i].domain.inValue(store.level, list[i], i + 1);
      }
      realCycle = checkCycleAndGetRealCycle(realCycle);
    }

    if (realCycle != null && realCycle.cardinality() < list.length) {
      for (int j = realCycle.nextClearBit(0); j < list.length; j = realCycle.nextClearBit(j + 1)) {
        list[j].domain.inValue(store.level, list[j], j + 1);
      }
    }
  }

  /** Checks the current cycleVar for validity; returns the BitSet to use as realCycle or throws. */
  private BitSet checkCycleAndGetRealCycle(BitSet currentRealCycle) {
    for (int cv = cycleVar.nextSetBit(0); cv >= 0; cv = cycleVar.nextSetBit(cv + 1)) {
      if (!list[cv].domain.contains(cv + 1)) {
        if (currentRealCycle != null) {
          throw Store.failException;
        }
        return cycleVar;
      }
    }
    return currentRealCycle;
  }

  private int sccs() {

    int totalNodes = 0;

    Arrays.fill(val, 0);

    idd = 0;

    for (int i = 0; i < list.length; i++) {

      sccLength = 0;

      if (val[i] == 0) {

        visit(i);

        totalNodes += sccLength;
      }
    }

    return totalNodes;
  }

  private int visit(int k) {

    idd++;
    val[k] = idd;
    int min = idd;

    // stack push
    stack[stack_pointer++] = k;

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

      cycleVar = new BitSet(list.length);
      sccLength = 0;

      int n;
      do {
        // stack pop
        n = stack[--stack_pointer];
        cycleVar.set(n);

        val[n] = list.length + 1;

        sccLength++;
      } while (n != k);
    }

    return min;
  }

  private void dominanceFilter() {
    int n = list.length;

    // find possible roots
    int[] possibleRoots = new int[n];
    int pr = 0;
    for (int v = 0; v < n; v++) {
      if (!list[v].dom().contains(v + 1)) {
        possibleRoots[pr++] = v;
      }
    }

    if (pr > 0 && !graphDominance(possibleRoots[Store.getRandom().nextInt(pr)])) {
      reversedGraphDominance(possibleRoots[Store.getRandom().nextInt(pr)]);
    }
  }

  private boolean graphDominance(int root) {
    int n = list.length;
    graphDominance.init();
    buildGraphForDominance(root, n);
    if (!graphDominance.dominators(n)) {
      throw Store.failException;
    }
    return applyGraphDominancePruning(root, n);
  }

  private void buildGraphForDominance(int root, int n) {
    for (int v = 0; v < n; v++) {
      for (ValueEnumeration e = list[v].dom().valueEnumeration(); e.hasMoreElements(); ) {
        int w = e.nextElement() - 1;
        if (v == root || v == w) {
          graphDominance.addArc(n, w);
        } else {
          graphDominance.addArc(v, w);
        }
      }
    }
  }

  private boolean applyGraphDominancePruning(int root, int n) {
    boolean pruning = false;
    for (int v = 0; v < n; v++) {
      if (v == root) {
        continue;
      }
      for (ValueEnumeration e = list[v].domain.valueEnumeration(); e.hasMoreElements(); ) {
        int w = e.nextElement() - 1;
        if (v != w && graphDominance.dominatedBy(v, w)) {
          pruning = true;
          list[v].domain.inComplement(store.level, list[v], w + 1);
          list[w].domain.inComplement(store.level, list[w], w + 1);
        }
      }
    }
    return pruning;
  }

  private boolean reversedGraphDominance(int root) {
    int n = list.length;
    graphDominance.init();
    buildReversedGraphForDominance(root, n);
    if (!graphDominance.dominators(n)) {
      throw Store.failException;
    }
    return applyReversedDominancePruning(root, n);
  }

  private void buildReversedGraphForDominance(int root, int n) {
    for (int v = 0; v < n; v++) {
      for (ValueEnumeration e = list[v].dom().valueEnumeration(); e.hasMoreElements(); ) {
        int w = e.nextElement() - 1;
        if (w == root || v == w) {
          graphDominance.addArc(n, v);
        } else {
          graphDominance.addArc(w, v);
        }
      }
    }
  }

  private boolean applyReversedDominancePruning(int root, int n) {
    boolean pruning = false;
    for (int v = 0; v < n; v++) {
      if (v == root) {
        continue;
      }
      for (ValueEnumeration e = list[v].domain.valueEnumeration(); e.hasMoreElements(); ) {
        int w = e.nextElement() - 1;
        if (v != w && w != root && graphDominance.dominatedBy(w, v)) {
          pruning = true;
          list[v].domain.inComplement(store.level, list[v], w + 1);
          list[v].domain.inComplement(store.level, list[v], v + 1);
        }
      }
    }
    return pruning;
  }
}
