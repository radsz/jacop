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
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.VarMap;
import org.jacop.core.InitOnce;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.util.DominatorTree;

/**
 * Subcircuit constraint assures that all variables build a subcircuit. Value of every variable x[i]
 * points to the next variable in the subcircuit. If a variable does not belong to a subcircuit it
 * has value of its position, i.e., x[i] = i.
 *
 * <p>Propagation removes fixed values from the other variables, then prunes with the strongly
 * connected components of the successor graph and, when those find nothing more, with the
 * dominators of a node that must be in the circuit. Dominator pruning is expensive and seldom
 * prunes, so after a call that prunes nothing it is skipped for a growing number of calls, at most
 * 32 or the value of the system property sub_circuit_dominance_skip (0 runs it every time, for the
 * strongest pruning).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Subcircuit extends Alldiff {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final Map<Var, Integer> valueIndex = new HashMap<>();
  final DominatorTree graphDominance;
  // a fixed seed keeps propagation, and so the search tree, the same on every run
  final Random random = new Random(0); // NOSONAR not used for security
  final InitOnce init = new InitOnce();
  boolean useScc = true;
  boolean useDominance = true;
  // the largest number of consecutive calls that skip the dominator pruning
  int maxDominanceSkip = 32;

  // successor graph of the current domains: arcs v -> w (w != v) of node v are at positions
  // arcStart[v] .. arcStart[v + 1] - 1, and selfLoop[v] tells whether v may stay out of the circuit
  private int[] arcStart;
  private int[] arcTo;
  private boolean[] selfLoop;
  private int arcCount;

  // strongly connected components: comp[v] is the component of v
  private final int[] comp;
  private final int[] compSize;
  private int compCount;
  private final int[] tarjanIndex;
  private final int[] tarjanLow;
  private final int[] tarjanStack;
  private final int[] callStack;
  private final int[] callArc;

  private final int[] possibleRoots;

  // calls left before dominator pruning runs again, and the length of the current pause
  private int dominanceWait;
  private int dominanceSkip;

  // the roots the dominator pruning used last, tried first by the explanations
  private final int[] recentRoots = {-1, -1, -1, -1};
  private int nextRoot;

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
    int n = list.length;
    this.graphDominance = new DominatorTree(n + 1);

    this.queueIndex = 2;

    int i = 0;
    for (Var v : list) {
      valueIndex.put(v, i++);
    }

    arcStart = new int[n + 1];
    arcTo = new int[n];
    selfLoop = new boolean[n];
    comp = new int[n];
    compSize = new int[n];
    tarjanIndex = new int[n];
    tarjanLow = new int[n];
    tarjanStack = new int[n];
    callStack = new int[n];
    callArc = new int[n];
    possibleRoots = new int[n];

    String scc = System.getProperty("sub_circuit_scc_pruning");
    String dominance = System.getProperty("sub_circuit_dominance_pruning");
    if (scc != null) {
      useScc = Boolean.parseBoolean(scc);
    }
    if (dominance != null) {
      useDominance = Boolean.parseBoolean(dominance);
    }
    String dominanceSkip = System.getProperty("sub_circuit_dominance_skip");
    if (dominanceSkip != null) {
      maxDominanceSkip = Integer.parseInt(dominanceSkip);
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
    this(list.toArray(IntVar[]::new));
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
      for (IntVar intVar : list) {
        intVar.domain.in(store.level, intVar, 1, list.length);
      }
    }

    do {

      store.propagationHasOccurred = false;

      LinkedHashSet<IntVar> fdvs = variableQueue;
      variableQueue = new LinkedHashSet<>();

      propagateAllDifferentOnSingletons(store, fdvs);

    } while (store.propagationHasOccurred);

    collectArcs();
    if (useScc) {
      sccsBasedPruning(store);
    }

    // the arcs are still those of the current domains when the components pruned nothing
    if (useDominance && !store.propagationHasOccurred) {
      if (dominanceWait > 0) {
        dominanceWait--;
      } else {
        dominanceFilter();
        if (store.propagationHasOccurred) {
          dominanceSkip = 0;
        } else {
          dominanceSkip = Math.min(2 * dominanceSkip + 1, maxDominanceSkip);
        }
        dominanceWait = dominanceSkip;
      }
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

  // registers the constraint in the constraint store
  @Override
  public void impose(Store store) {

    this.store = store;

    super.impose(store);
  }

  @Override
  public boolean satisfied() {

    if (grounded.value() != list.length || !super.satisfied()) {
      return false;
    }

    // the nodes that do not point to themselves must form a single cycle
    int start = -1;
    int inCircuit = 0;
    for (int v = 0; v < list.length; v++) {
      if (list[v].value() != v + 1) {
        start = v;
        inCircuit++;
      }
    }
    if (inCircuit == 0) {
      return true;
    }
    int length = 0;
    int v = start;
    do {
      v = list[v].value() - 1;
      length++;
    } while (v != start && length <= inCircuit);
    return v == start && length == inCircuit;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : subcircuit([");
    appendArrayToString(result, list);
    result.append("])");

    return result.toString();
  }

  private void collectArcs() {
    int n = list.length;
    arcCount = 0;
    for (int v = 0; v < n; v++) {
      IntDomain d = list[v].domain;
      if (arcCount + d.getSize() > arcTo.length) {
        arcTo = Arrays.copyOf(arcTo, Math.max(2 * arcTo.length, arcCount + d.getSize()));
      }
      selfLoop[v] = false;
      arcStart[v] = arcCount;
      for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
        int w = e.nextElement() - 1;
        if (w == v) {
          selfLoop[v] = true;
        } else {
          arcTo[arcCount++] = w;
        }
      }
    }
    arcStart[n] = arcCount;
  }

  // A node alone in its component cannot be on a cycle, the nodes that must be on the circuit have
  // to share one component, nodes outside that component stay out of the circuit, and an arc
  // between two components is on no cycle.
  private void sccsBasedPruning(Store store) {
    stronglyConnectedComponents();
    int n = list.length;
    int circuitComp = -1;
    for (int v = 0; v < n; v++) {
      if (!selfLoop[v]) {
        if (circuitComp == -1) {
          circuitComp = comp[v];
        } else if (circuitComp != comp[v]) {
          throw Store.failException;
        }
      }
    }
    for (int v = 0; v < n; v++) {
      if (compSize[comp[v]] == 1 || (circuitComp != -1 && comp[v] != circuitComp)) {
        list[v].domain.inValue(store.level, list[v], v + 1);
      } else {
        for (int a = arcStart[v]; a < arcStart[v + 1]; a++) {
          int w = arcTo[a];
          if (comp[w] != comp[v]) {
            list[v].domain.inComplement(store.level, list[v], w + 1);
          }
        }
      }
    }
  }

  // Tarjan's algorithm over the collected arcs, without recursion.
  private void stronglyConnectedComponents() {
    int n = list.length;
    Arrays.fill(tarjanIndex, -1);
    int index = 0;
    int sp = 0;
    compCount = 0;
    for (int s = 0; s < n; s++) {
      if (tarjanIndex[s] != -1) {
        continue;
      }
      int top = 0;
      callStack[0] = s;
      callArc[0] = arcStart[s];
      tarjanIndex[s] = index;
      tarjanLow[s] = index++;
      tarjanStack[sp++] = s;
      comp[s] = -1;
      while (top >= 0) {
        int v = callStack[top];
        int a = callArc[top];
        if (a < arcStart[v + 1]) {
          callArc[top] = a + 1;
          int w = arcTo[a];
          if (tarjanIndex[w] == -1) {
            tarjanIndex[w] = index;
            tarjanLow[w] = index++;
            tarjanStack[sp++] = w;
            comp[w] = -1;
            top++;
            callStack[top] = w;
            callArc[top] = arcStart[w];
          } else if (comp[w] == -1 && tarjanIndex[w] < tarjanLow[v]) {
            // w is still on the stack
            tarjanLow[v] = tarjanIndex[w];
          }
          continue;
        }
        if (tarjanLow[v] == tarjanIndex[v]) {
          int size = 0;
          int w;
          do {
            w = tarjanStack[--sp];
            comp[w] = compCount;
            size++;
          } while (w != v);
          compSize[compCount++] = size;
        }
        top--;
        if (top >= 0 && tarjanLow[v] < tarjanLow[callStack[top]]) {
          tarjanLow[callStack[top]] = tarjanLow[v];
        }
      }
    }
  }

  private void dominanceFilter() {
    int n = list.length;

    // possible roots are the nodes that must be in the circuit
    int pr = 0;
    for (int v = 0; v < n; v++) {
      if (!selfLoop[v]) {
        possibleRoots[pr++] = v;
      }
    }

    if (pr > 0) {
      int root = possibleRoots[random.nextInt(pr)];
      recordRoot(root);
      if (!graphDominance(root)) {
        root = possibleRoots[random.nextInt(pr)];
        recordRoot(root);
        reversedGraphDominance(root);
      }
    }
  }

  private void recordRoot(int root) {
    for (int r : recentRoots) {
      if (r == root) {
        return;
      }
    }
    recentRoots[nextRoot] = root;
    nextRoot = (nextRoot + 1) % recentRoots.length;
  }

  // Graph from a source n that replaces the root's outgoing arcs and reaches every node that may
  // stay out of the circuit. If w dominates v there, arc v -> w closes a cycle without the root.
  private boolean graphDominance(int root) {
    int n = list.length;
    graphDominance.clear();
    for (int v = 0; v < n; v++) {
      if (selfLoop[v]) {
        graphDominance.addArc(n, v);
      }
      int from = v == root ? n : v;
      for (int a = arcStart[v]; a < arcStart[v + 1]; a++) {
        graphDominance.addArc(from, arcTo[a]);
      }
    }
    if (!graphDominance.compute(n)) {
      throw Store.failException;
    }
    boolean pruning = false;
    for (int v = 0; v < n; v++) {
      if (v == root) {
        continue;
      }
      for (int a = arcStart[v]; a < arcStart[v + 1]; a++) {
        int w = arcTo[a];
        if (graphDominance.dominates(w, v)) {
          pruning = true;
          list[v].domain.inComplement(store.level, list[v], w + 1);
          list[w].domain.inComplement(store.level, list[w], w + 1);
        }
      }
    }
    return pruning;
  }

  // The same on the reversed graph: if v dominates w there, arc v -> w closes a cycle without the
  // root.
  private boolean reversedGraphDominance(int root) {
    int n = list.length;
    graphDominance.clear();
    for (int v = 0; v < n; v++) {
      if (selfLoop[v]) {
        graphDominance.addArc(n, v);
      }
      for (int a = arcStart[v]; a < arcStart[v + 1]; a++) {
        int w = arcTo[a];
        graphDominance.addArc(w == root ? n : w, v);
      }
    }
    if (!graphDominance.compute(n)) {
      throw Store.failException;
    }
    boolean pruning = false;
    for (int v = 0; v < n; v++) {
      if (v == root) {
        continue;
      }
      for (int a = arcStart[v]; a < arcStart[v + 1]; a++) {
        int w = arcTo[a];
        if (w != root && graphDominance.dominates(v, w)) {
          pruning = true;
          list[v].domain.inComplement(store.level, list[v], w + 1);
          list[v].domain.inComplement(store.level, list[v], v + 1);
        }
      }
    }
    return pruning;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    int mark = out.size();
    if (SubcircuitExplanation.explain(trail, entry, list, 1, false, recentRoots, out)) {
      return true;
    }
    out.truncate(mark);
    return AlldiffExplanation.explain(trail, entry, list, new IntervalDomain(), out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return SubcircuitExplanation.explainFailure(trail, list, 1, false, recentRoots, out);
  }

  @Override
  public Subcircuit copy(VarMap map) {
    Subcircuit copy = new Subcircuit(map.get(list));
    copy.useScc = useScc;
    copy.useDominance = useDominance;
    copy.maxDominanceSkip = maxDominanceSkip;
    return copy;
  }
}
