/*
 * BinPackingCostBound.java
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

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.lp.TimeIndexedBound;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * Bounds the cost of the loads of each bin packing on its own: when the objective sums functions
 * y<sub>p</sub> = g<sub>p</sub>(load<sub>p</sub>) of the loads of one bin packing ({@link
 * LoadFunctionDetector}), the smallest value of &Sigma;<sub>p</sub> g<sub>p</sub>(load<sub>p</sub>)
 * over the assignments of its items to bins is a lower bound on &Sigma;<sub>p</sub> y<sub>p</sub>.
 * In the linear constraint that sums most of the y<sub>p</sub> with one coefficient (the
 * objective's definition), they become a new variable z = &Sigma;<sub>p</sub> y<sub>p</sub> whose
 * domain starts at that bound, as linear overlap factoring ({@link LinearOverlapDetector}) makes a
 * sub-sum a variable: the objective's bound then adds up the bounds of the bin packings, and the
 * core-guided search of LCG takes each z as a term. The assignments are enumerated by a branch and
 * bound over the items, heaviest first, with the bound &Sigma;<sub>p</sub> min<sub>v &ge;
 * load</sub> g<sub>p</sub>(v) and the symmetry of bins with the same function and the same items
 * allowed in them; a bin packing whose enumeration exceeds {@link #NODES} nodes gets no bound.
 *
 * <p>This is the relaxation of a decomposable objective to one global constraint, solved exactly,
 * as the deviation constraint of Schaus, Deville, Dupont and R&eacute;gin (The deviation
 * constraint, CPAIOR 2007) and the dispersion constraints of Pesant (Achieving domain consistency
 * and counting solutions for dispersion constraints, INFORMS Journal on Computing 27(4), 2015) do
 * for the deviation of a sum; here the indivisible items of the bin packing give the bound. On the
 * balanced academic curriculum (MiniZinc Challenge gbac) each curriculum is a bin packing of its
 * courses over the periods, and its load cost is the square of the distance of the load to a band:
 * the sum of the curricula's own minima is 1,336 for 2020 reduced_UD5 (optimum 1,374), where the
 * core-guided search of LCG reached 1,030.
 *
 * <p>Setting the system property {@code org.jacop.fz.binPackingCost} to false turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class BinPackingCostBound {

  private static final Set<String> GATE_KINDS = Set.of("jacop_bin_packing");

  /**
   * It tells if the bounds are posted.
   *
   * @return false if the system property org.jacop.fz.binPackingCost is false
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.binPackingCost"));
  }

  /** The nodes of the enumeration of one bin packing at most. */
  static final long NODES = Long.getLong("org.jacop.fz.binPackingCost.nodes", 2_000_000L);

  // a value that no load takes
  private static final long NONE = Long.MAX_VALUE / 4;

  private static final Set<String> ROWS = Set.of("int_lin_eq", "int_lin_le");

  private final Support support;
  private final Set<SimpleNode> skipped;
  private final List<SimpleNode> nodes = new ArrayList<>();
  private final List<LinkedHashMap<IntVar, Long>> rows = new ArrayList<>();
  private final Map<IntVar, List<Integer>> occurrences = new IdentityHashMap<>();
  private final List<SimpleNode> packings = new ArrayList<>();
  private final Set<Integer> changed = new LinkedHashSet<>();
  private int bounds;

  /**
   * It creates the bounds of the bin packings of a model.
   *
   * @param support the support of the FlatZinc front end
   * @param skipped constraint nodes that earlier detectors replaced; they are not posted
   */
  public BinPackingCostBound(Support support, Set<SimpleNode> skipped) {
    this.support = support;
    this.skipped = skipped;
  }

  /**
   * It finds the bin packings whose load costs a linear constraint sums, posts the sum of each as a
   * new variable bounded below by its minimum and records the constraint rewritten over it.
   *
   * @param astTree the root of the parsed model
   * @return the number of sums posted
   */
  public int detect(SimpleNode astTree) {
    // the bounds are of bin packings: a model without them is not read
    if (!support.hasConstraint(astTree, GATE_KINDS)) {
      return 0;
    }
    support.forEachConstraint(
        astTree,
        item -> {
          if (skipped.contains(item)) {
            return;
          }
          if ("jacop_bin_packing".equals(item.getName())) {
            packings.add(item);
          } else if (ROWS.contains(item.getName()) && !support.linearRewrites.containsKey(item)) {
            collect(item);
          }
        });
    if (packings.isEmpty() || rows.isEmpty()) {
      return 0;
    }
    Map<IntVar, List<TimeIndexedBound.LoadFunction>> byLoad = new IdentityHashMap<>();
    for (TimeIndexedBound.LoadFunction f : new LoadFunctionDetector(support).detect(astTree)) {
      if (occurrences.containsKey(f.out())) {
        byLoad.computeIfAbsent(f.load(), k -> new ArrayList<>()).add(f);
      }
    }
    if (byLoad.isEmpty()) {
      return 0;
    }
    LinearConstraints linear = new LinearConstraints(support);
    for (SimpleNode packing : packings) {
      try {
        bound(packing, byLoad, linear);
      } catch (RuntimeException e) {
        // an argument of another shape: no bound
      }
    }
    for (int j : changed) {
      LinkedHashMap<IntVar, Long> row = rows.get(j);
      int[] a = new int[row.size()];
      IntVar[] x = new IntVar[row.size()];
      int k = 0;
      for (Map.Entry<IntVar, Long> t : row.entrySet()) {
        a[k] = t.getValue().intValue();
        x[k++] = t.getKey();
      }
      support.linearRewrites.put(nodes.get(j), new LinearOverlapDetector.Rewrite(a, x));
    }
    if (support.options.debug() && bounds > 0) {
      FzConsole.println("% bin packing cost bounds: " + bounds);
    }
    return bounds;
  }

  private void collect(SimpleNode node) {
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (a == null || x == null || a.length != x.length) {
      return;
    }
    LinkedHashMap<IntVar, Long> row = new LinkedHashMap<>();
    for (int i = 0; i < x.length; i++) {
      row.merge(x[i], (long) a[i], Long::sum);
    }
    row.values().removeIf(c -> c == 0);
    int id = rows.size();
    nodes.add(node);
    rows.add(row);
    for (IntVar v : row.keySet()) {
      occurrences.computeIfAbsent(v, k -> new ArrayList<>()).add(id);
    }
  }

  // the bound of one bin packing: its load costs in the row that has most of them with one
  // coefficient become a variable z >= the smallest cost of the bin packing
  private void bound(
      SimpleNode packing,
      Map<IntVar, List<TimeIndexedBound.LoadFunction>> byLoad,
      LinearConstraints linear) {
    IntVar[] items = support.getVarArray((SimpleNode) packing.jjtGetChild(0));
    IntVar[] loads = support.getVarArray((SimpleNode) packing.jjtGetChild(1));
    int[] w = support.getIntArray((SimpleNode) packing.jjtGetChild(2));
    int minBin = support.getInt((ASTScalarFlatExpr) packing.jjtGetChild(3));
    Set<Integer> candidates = new LinkedHashSet<>();
    for (IntVar load : loads) {
      for (TimeIndexedBound.LoadFunction f : byLoad.getOrDefault(load, List.of())) {
        candidates.addAll(occurrences.get(f.out()));
      }
    }
    int bestRow = -1;
    long bestCoefficient = 0;
    TimeIndexedBound.LoadFunction[] best = null;
    int bestCount = 1;
    for (int j : candidates) {
      LinkedHashMap<IntVar, Long> row = rows.get(j);
      Map<Long, TimeIndexedBound.LoadFunction[]> groups = new HashMap<>();
      Map<Long, Integer> counts = new HashMap<>();
      Set<IntVar> taken = Collections.newSetFromMap(new IdentityHashMap<>());
      for (int p = 0; p < loads.length; p++) {
        for (TimeIndexedBound.LoadFunction f : byLoad.getOrDefault(loads[p], List.of())) {
          Long c = row.get(f.out());
          if (c != null && taken.add(f.out())) {
            groups.computeIfAbsent(c, k -> new TimeIndexedBound.LoadFunction[loads.length])[p] = f;
            int n = counts.merge(c, 1, Integer::sum);
            if (n > bestCount) {
              bestCount = n;
              bestRow = j;
              bestCoefficient = c;
              best = groups.get(c);
            }
            break;
          }
        }
      }
    }
    if (best == null) {
      return;
    }
    long[][] cost = new long[loads.length][];
    long lo = 0;
    long hi = 0;
    List<IntVar> outs = new ArrayList<>();
    for (int p = 0; p < loads.length; p++) {
      if (best[p] != null) {
        cost[p] = table(loads[p], best[p]);
        outs.add(best[p].out());
        lo += best[p].out().min();
        hi += best[p].out().max();
      }
    }
    long m = new Enumeration(items, w, minBin, cost).minimum();
    if (m == NONE || m <= lo || m > hi || hi > IntDomain.MAX_INT || lo < IntDomain.MIN_INT) {
      return;
    }
    LinkedHashMap<IntVar, Long> row = rows.get(bestRow);
    if (Math.abs(bestCoefficient) * Math.max(Math.abs(m), Math.abs(hi)) > IntDomain.MAX_INT) {
      return;
    }
    IntVar z = new IntVar(support.store, (int) m, (int) hi);
    int[] a = new int[outs.size() + 1];
    IntVar[] x = new IntVar[outs.size() + 1];
    for (int t = 0; t < outs.size(); t++) {
      a[t] = 1;
      x[t] = outs.get(t);
      row.remove(outs.get(t));
      occurrences.get(outs.get(t)).remove(Integer.valueOf(bestRow));
    }
    a[outs.size()] = -1;
    x[outs.size()] = z;
    linear.poseLinearEquality(a, x, 0);
    row.put(z, bestCoefficient);
    changed.add(bestRow);
    bounds++;
    if (support.options.debug()) {
      FzConsole.println("% bin packing cost bound: " + z + " = sum of " + outs.size() + " costs");
    }
  }

  // g(v) for v = 0 .. load.max(), NONE where the load cannot be v
  private static long[] table(IntVar load, TimeIndexedBound.LoadFunction f) {
    int max = Math.max(0, load.max());
    long[] g = new long[max + 1];
    for (int v = 0; v <= max; v++) {
      long i = v - f.offset();
      g[v] =
          load.domain.contains(v) && i >= 0 && i < f.values().length ? f.values()[(int) i] : NONE;
    }
    return g;
  }

  /** The branch and bound over the items of one bin packing. */
  private static final class Enumeration {

    private final int[][] bins; // per item (heaviest first): the bins it can go to
    private final int[] weight;
    private final long[][] cost; // per bin: g(v), null for a bin whose load costs nothing here
    private final long[][] suffix; // per bin: min over v' >= v of g(v'), NONE beyond
    private final int[] cls; // per bin: its class of symmetry
    private final int[] load;
    private long best = NONE;
    private long nodes;

    Enumeration(IntVar[] vars, int[] w, int minBin, long[][] cost) {
      int n = cost.length;
      this.cost = cost;
      Integer[] order = new Integer[vars.length];
      for (int i = 0; i < order.length; i++) {
        order[i] = i;
      }
      Arrays.sort(order, (x, y) -> Integer.compare(w[y], w[x]));
      bins = new int[vars.length][];
      weight = new int[vars.length];
      for (int k = 0; k < order.length; k++) {
        IntVar x = vars[order[k]];
        weight[k] = w[order[k]];
        int[] in = new int[n];
        int count = 0;
        for (int p = 0; p < n; p++) {
          if (x.domain.contains(p + minBin)) {
            in[count++] = p;
          }
        }
        bins[k] = Arrays.copyOf(in, count);
      }
      suffix = new long[n][];
      for (int p = 0; p < n; p++) {
        if (cost[p] != null) {
          long[] s = new long[cost[p].length + 1];
          s[cost[p].length] = NONE;
          for (int v = cost[p].length - 1; v >= 0; v--) {
            s[v] = Math.min(cost[p][v], s[v + 1]);
          }
          suffix[p] = s;
        }
      }
      cls = new int[n];
      for (int p = 0; p < n; p++) {
        cls[p] = p;
        for (int q = 0; q < p; q++) {
          if (cls[q] == q && symmetric(p, q)) {
            cls[p] = q;
            break;
          }
        }
      }
      load = new int[n];
    }

    // bins p and q have the same function and every item can go to both or neither
    private boolean symmetric(int p, int q) {
      if (!Arrays.equals(cost[p], cost[q])) {
        return false;
      }
      for (int[] in : bins) {
        if (Arrays.binarySearch(in, p) >= 0 != Arrays.binarySearch(in, q) >= 0) {
          return false;
        }
      }
      return true;
    }

    // the smallest total cost, NONE when there is none or the enumeration was too long
    long minimum() {
      long bound = 0;
      for (int p = 0; p < cost.length; p++) {
        if (cost[p] != null) {
          bound += suffix[p][0];
        }
      }
      if (bound >= NONE) {
        return NONE;
      }
      search(0, bound);
      return nodes > NODES ? NONE : best;
    }

    private void search(int k, long bound) {
      if (++nodes > NODES || bound >= best) {
        return;
      }
      if (k == weight.length) {
        long total = 0;
        for (int p = 0; p < cost.length; p++) {
          if (cost[p] != null) {
            total += cost[p][load[p]];
          }
        }
        if (total < best) {
          best = total;
        }
        return;
      }
      int w = weight[k];
      int[] tried = new int[bins[k].length];
      int numTried = 0;
      for (int p : bins[k]) {
        int to = load[p] + w;
        if (cost[p] != null && to >= cost[p].length) {
          continue; // above the largest load
        }
        boolean same = false;
        for (int t = 0; t < numTried && !same; t++) {
          int q = tried[t];
          same = cls[q] == cls[p] && load[q] == load[p];
        }
        if (same) {
          continue; // a symmetric bin with the same load was tried
        }
        tried[numTried++] = p;
        long next = bound;
        if (cost[p] != null) {
          next += suffix[p][to] - suffix[p][load[p]];
        }
        if (next >= NONE) {
          continue;
        }
        load[p] = to;
        search(k + 1, next);
        load[p] -= w;
      }
    }
  }
}
