/*
 * AbstractSame.java
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
import java.util.Map;
import java.util.TreeSet;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Common part of {@link Same} and {@link UsedBy}: the values of y are the values of x (Same) or a
 * sub-multiset of them (UsedBy). Both are propagated with the flow network of N. Beldiceanu, I.
 * Katriel and S. Thiel, "Filtering algorithms for the Same constraint", CPAIOR 2004, LNCS 3011,
 * 65-79 (and their report "Filtering algorithms for the Same and UsedBy constraints",
 * MPI-I-2004-1-001): a source, a node per variable of x, a node per value, a node per variable of y
 * and a sink, with an arc from x[i] to each value of its domain and from each value to each y[j]
 * that can take it. Every arc from the source to x[i] has flow 1 (Same) or 0..1 (UsedBy), and every
 * arc from y[j] to the sink has flow 1. Feasible flows and solutions correspond: x[i] and y[j]
 * joined through value v both take v. A value of a variable is kept when its arc has flow in some
 * feasible flow, which the strongly connected components of the residual graph tell, so the
 * constraint is domain consistent. In UsedBy a variable of x that may stay out of the flow keeps
 * all its values.
 *
 * <p>For lazy clause generation an atom is explained by a cut of the same network built over the
 * domains before it, with the atom negated (G. Downing, T. Feydy and P. J. Stuckey, "Explaining
 * flow-based propagation", CPAIOR 2012; see {@link FlowReason}): the values that the variables of x
 * inside the cut cannot take outside it, and the values inside the cut that the variables of y
 * outside it cannot take.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractSame extends Constraint implements SatisfiedPresent, Explainable {

  // the most values (over the ranges of all variables) an explanation reads
  private static final long VALUE_LIMIT = 1 << 16;

  /** The first list. */
  final IntVar[] x;

  /** The second list. */
  final IntVar[] y;

  /** Whether y may use only part of x (UsedBy) instead of all of it (Same). */
  private final boolean subset;

  private final BoundedFlow flow = new BoundedFlow();
  private final Map<Integer, Integer> valueNode = new HashMap<>();
  private final CardinalityExplanation.Budget budget = new CardinalityExplanation.Budget();

  AbstractSame(IntVar[] x, IntVar[] y, boolean subset) {
    checkInputForNullness(new String[] {"x", "y"}, x, y);
    if (subset ? y.length > x.length : y.length != x.length) {
      throw new IllegalArgumentException(
          getClass().getSimpleName()
              + (subset ? ": y cannot be longer than x" : ": x and y need the same length"));
    }
    this.x = Arrays.copyOf(x, x.length);
    this.y = Arrays.copyOf(y, y.length);
    this.subset = subset;
    this.queueIndex = 2;
    setScope(this.x, this.y);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void consistency(Store store) {
    int n = x.length;
    int p = y.length;
    valueNode.clear();
    int source = 0;
    int sink = 1;
    int firstX = 2;
    int firstY = firstX + n;
    int next = firstY + p;
    // values that some y can take; a value of x outside them cannot be matched
    for (IntVar v : y) {
      for (ValueEnumeration e = v.domain.valueEnumeration(); e.hasMoreElements(); ) {
        int value = e.nextElement();
        if (!valueNode.containsKey(value)) {
          valueNode.put(value, next++);
        }
      }
    }
    flow.reset(next);
    int[] sourceArc = new int[n];
    int[][] xArcs = new int[n][];
    int[][] xValues = new int[n][];
    for (int i = 0; i < n; i++) {
      sourceArc[i] = flow.addArc(source, firstX + i, subset ? 0 : 1, 1);
      int[] arcs = new int[x[i].domain.getSize()];
      int[] vals = new int[arcs.length];
      int count = 0;
      for (ValueEnumeration e = x[i].domain.valueEnumeration(); e.hasMoreElements(); ) {
        int value = e.nextElement();
        Integer node = valueNode.get(value);
        if (node != null) {
          vals[count] = value;
          arcs[count++] = flow.addArc(firstX + i, node, 0, 1);
        }
      }
      xArcs[i] = Arrays.copyOf(arcs, count);
      xValues[i] = Arrays.copyOf(vals, count);
    }
    int[][] yArcs = new int[p][];
    int[][] yValues = new int[p][];
    for (int j = 0; j < p; j++) {
      int[] arcs = new int[y[j].domain.getSize()];
      int[] vals = new int[arcs.length];
      int count = 0;
      for (ValueEnumeration e = y[j].domain.valueEnumeration(); e.hasMoreElements(); ) {
        int value = e.nextElement();
        vals[count] = value;
        arcs[count++] = flow.addArc(valueNode.get(value), firstY + j, 0, 1);
      }
      yArcs[j] = arcs;
      yValues[j] = vals;
      flow.addArc(firstY + j, sink, 1, 1);
    }
    flow.addArc(sink, source, p, p);
    if (!flow.solve()) {
      throw Store.failException;
    }
    for (int j = 0; j < p; j++) {
      prune(store, y[j], yArcs[j], yValues[j], false);
    }
    for (int i = 0; i < n; i++) {
      boolean optional = subset && (flow.flow(sourceArc[i]) == 0 || flow.variable(sourceArc[i]));
      if (!optional) {
        prune(store, x[i], xArcs[i], xValues[i], true);
      }
    }
  }

  // keeps the values of v whose arcs can carry flow; with all, also removes values without an arc
  private void prune(Store store, IntVar v, int[] arcs, int[] vals, boolean all) {
    if (all && arcs.length < v.domain.getSize()) {
      IntDomain keep = new IntervalDomain();
      for (int k = 0; k < arcs.length; k++) {
        if (flow.flow(arcs[k]) == 1 || flow.variable(arcs[k])) {
          keep.unionAdapt(vals[k], vals[k]);
        }
      }
      v.domain.in(store.level, v, keep);
      return;
    }
    for (int k = 0; k < arcs.length; k++) {
      if (flow.flow(arcs[k]) == 0 && !flow.variable(arcs[k])) {
        v.domain.inComplement(store.level, v, vals[k]);
      }
    }
  }

  @Override
  public boolean satisfied() {
    for (IntVar v : x) {
      if (!v.singleton()) {
        return false;
      }
    }
    for (IntVar v : y) {
      if (!v.singleton()) {
        return false;
      }
    }
    Map<Integer, Integer> counts = new HashMap<>();
    for (IntVar v : x) {
      counts.merge(v.value(), 1, Integer::sum);
    }
    for (IntVar v : y) {
      if (counts.merge(v.value(), -1, Integer::sum) < 0) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar z = trail.variable(entry);
    boolean in = false;
    for (IntVar v : x) {
      in |= v == z;
    }
    for (IntVar v : y) {
      in |= v == z;
    }
    return in && explain(FlowReason.ofEntry(trail, entry, out));
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return explain(new FlowReason(trail, trail.size(), out));
  }

  @Override
  public boolean checksReasons() {
    return true;
  }

  // the network of the domains before the reason's position, with its atom negated: a node per
  // value in the range of some variable, arcs of flow 0 for the values a variable's range holds
  // but its domain does not
  private boolean explain(FlowReason reason) {
    long started = System.nanoTime();
    if (!budget.allows(started)) {
      return false;
    }
    try {
      int n = x.length;
      int p = y.length;
      IntVar[] all = new IntVar[n + p];
      System.arraycopy(x, 0, all, 0, n);
      System.arraycopy(y, 0, all, n, p);
      int[] lo = new int[n + p];
      int[] hi = new int[n + p];
      long range = 0;
      for (int i = 0; i < n + p; i++) {
        lo[i] = reason.min(all[i]);
        hi[i] = reason.max(all[i]);
        if (lo[i] > hi[i]) {
          return false;
        }
        range += (long) hi[i] - lo[i] + 1;
        if (range > VALUE_LIMIT) {
          return false;
        }
      }
      TreeSet<Integer> seen = new TreeSet<>();
      for (int i = 0; i < n + p; i++) {
        IntDomain root = reason.root(all[i]);
        for (int v = lo[i]; v <= hi[i]; v++) {
          if (root.contains(v)) {
            seen.add(v);
          }
        }
      }
      int[] values = seen.stream().mapToInt(Integer::intValue).toArray();
      int firstValue = 2 + n + p;
      flow.reset(firstValue + values.length);
      for (int i = 0; i < n; i++) {
        flow.addArc(0, 2 + i, subset ? 0 : 1, 1);
        for (int k = from(values, lo[i]); k < values.length && values[k] <= hi[i]; k++) {
          flow.addArc(2 + i, firstValue + k, 0, reason.contains(x[i], values[k]) ? 1 : 0);
        }
      }
      for (int j = 0; j < p; j++) {
        int node = 2 + n + j;
        for (int k = from(values, lo[n + j]); k < values.length && values[k] <= hi[n + j]; k++) {
          flow.addArc(firstValue + k, node, 0, reason.contains(y[j], values[k]) ? 1 : 0);
        }
        flow.addArc(node, 1, 1, 1);
      }
      flow.addArc(1, 0, 0, BoundedFlow.INFINITE);
      if (flow.solve() || !FlowReason.violated(flow)) {
        return false;
      }
      for (int i = 0; i < n; i++) {
        if (!flow.inCut(2 + i)) {
          continue;
        }
        // x[i] takes no value outside its range, nor the values of it outside the cut
        reason.needLower(x[i], lo[i]);
        reason.needUpper(x[i], hi[i]);
        for (int k = from(values, lo[i]); k < values.length && values[k] <= hi[i]; k++) {
          if (!flow.inCut(firstValue + k) && !reason.contains(x[i], values[k])) {
            reason.exclude(x[i], values[k]);
          }
        }
      }
      for (int j = 0; j < p; j++) {
        if (flow.inCut(2 + n + j)) {
          continue;
        }
        // y[j] takes none of the values in the cut
        for (int k = 0; k < values.length; k++) {
          if (!flow.inCut(firstValue + k)) {
            continue;
          }
          int v = values[k];
          if (v < lo[n + j]) {
            reason.needLower(y[j], (long) v + 1);
          } else if (v > hi[n + j]) {
            reason.needUpper(y[j], (long) v - 1);
          } else if (!reason.contains(y[j], v)) {
            reason.exclude(y[j], v);
          }
        }
      }
      return reason.finish();
    } finally {
      budget.spend(started);
    }
  }

  // the index of the first value at least v
  private static int from(int[] values, int v) {
    int k = Arrays.binarySearch(values, v);
    return k >= 0 ? k : -k - 1;
  }

  String toString(String name) {
    StringBuilder result = new StringBuilder(id());
    result.append(" : ").append(name).append("([");
    appendArrayToString(result, x);
    result.append("], [");
    appendArrayToString(result, y);
    result.append("])");
    return result.toString();
  }
}
