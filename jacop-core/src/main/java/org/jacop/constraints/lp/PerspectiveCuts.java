/*
 * CapacityCuts.java
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

package org.jacop.constraints.lp;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import org.jacop.api.VarMap;
import org.jacop.constraints.Linearizations.Implication;
import org.jacop.core.IntVar;
import org.jacop.lcg.LinearForm;

/**
 * Perspective cuts of half-reified linear relations, separated from an LP solution. For {@code [b =
 * when] -> sum a x <= c} with x in the box of its root bounds, write {@code beta} for {@code b}
 * (when = 1) or {@code 1 - b} (when = 0), and {@code L_i}, {@code U_i} for the least and the
 * largest value of {@code a_i x_i} in the box. The convex hull of the disjunction {@code (beta = 1,
 * sum a x <= c, x in box) or (beta = 0, x in box)} is, after the copies {@code x = x1 + x0} with
 * {@code x1} in {@code beta box}, {@code sum a x1 <= c beta} and {@code x0} in {@code (1 - beta)
 * box} are projected out (Balas 1979, 1998), the box and, for every subset S of the variables,
 *
 * <pre>
 *   sum_{i in S} a_i x_i + beta (sum_{i in S} U_i + sum_{i not in S} L_i - c) &lt;= sum_{i in S} U_i.
 * </pre>
 *
 * The full set S is the big-M row that {@link org.jacop.constraints.Linearizations} adds, and a
 * single variable is its bound implied by beta, the perspective reformulation of a semi-continuous
 * variable (Frangioni and Gentile 2006; Günlük and Linderoth 2010): at a fractional b the big-M row
 * alone lets each variable reach its bound. The most violated subset for a solution takes each i
 * whose {@code a_i x_i - (1 - beta) U_i} exceeds {@code beta L_i}, so the separation is exact and
 * linear. As x is integer, {@code c - sum_{i not in S} L_i} is rounded down to a multiple of the
 * gcd of the weights in S, as for a Chvátal-Gomory cut; since that rounding can make a single
 * variable's cut (its implied integer bound) the most violated one, those are separated too. The
 * cuts use the root bounds, so they hold in the whole search.
 *
 * <p>E. Balas, Disjunctive programming, Annals of Discrete Mathematics 5 (1979) 3-51. E. Balas,
 * Disjunctive programming: properties of the convex hull of feasible points, Discrete Applied
 * Mathematics 89 (1998) 3-44. A. Frangioni and C. Gentile, Perspective cuts for a class of convex
 * 0-1 mixed integer programs, Mathematical Programming 106 (2006) 225-236. O. Günlük and J.
 * Linderoth, Perspective reformulations of mixed integer nonlinear programs with indicator
 * variables, Mathematical Programming 124 (2010) 183-205.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class PerspectiveCuts {

  // the largest weight of a cut, as for the MIR cuts
  private static final long MAX_WEIGHT = 1L << 24;

  private final List<Implication> implications;

  // the column of each variable of each implication and of its control, -1 when it is no column
  private int[][] columns;
  private int[] controls;

  PerspectiveCuts(List<Implication> implications) {
    this.implications = new ArrayList<>(implications);
  }

  /**
   * Returns the number of implications.
   *
   * @return the implications separated
   */
  int size() {
    return implications.size();
  }

  /**
   * Returns the cuts of single 0/1 variables of the implications over a 0/1 control, as rows: each
   * is the conflict of two literals ({@code b = when} with {@code x = 1}, or with {@code x = 0}),
   * which {@link PairCliques} merges with the other conflicts of the model into clique rows, much
   * stronger than the pairs or any cut of one implication.
   *
   * @param implications the implications
   * @return the rows {@code x <= [b != when]} or {@code x >= [b = when]}
   */
  static List<LinearForm> pairRows(List<Implication> implications) {
    List<LinearForm> out = new ArrayList<>();
    for (Implication imp : implications) {
      IntVar b = imp.control();
      IntVar[] vs = imp.vars();
      long[] a = imp.weights();
      if (b.min() < 0 || b.max() > 1) {
        continue;
      }
      try {
        long least = 0;
        for (int k = 0; k < vs.length; k++) {
          least =
              Math.addExact(least, Math.multiplyExact(a[k], a[k] > 0 ? vs[k].min() : vs[k].max()));
        }
        for (int k = 0; k < vs.length; k++) {
          IntVar x = vs[k];
          if (x.min() != 0 || x.max() != 1 || a[k] == 0) {
            continue;
          }
          // a_k x <= c - (least - min a_k x)
          long room = Math.subtractExact(imp.side(), Math.subtractExact(least, Math.min(a[k], 0)));
          IntVar[] pair = {x, b};
          if (a[k] > 0 && room < a[k]) {
            // [b = when] -> x = 0: x + b <= 1, or x - b <= 0
            out.add(
                imp.when()
                    ? new LinearForm(pair, new long[] {1, 1}, 1, LinearForm.LE)
                    : new LinearForm(pair, new long[] {1, -1}, 0, LinearForm.LE));
          } else if (a[k] < 0 && room < 0) {
            // [b = when] -> x = 1: x - b >= 0, or x + b >= 1
            out.add(
                imp.when()
                    ? new LinearForm(pair, new long[] {1, -1}, 0, LinearForm.GE)
                    : new LinearForm(pair, new long[] {1, 1}, 1, LinearForm.GE));
          }
        }
      } catch (ArithmeticException _) {
        // no rows of this implication
      }
    }
    return out;
  }

  /**
   * It returns the copy over the variables of a copied store.
   *
   * @param map the variables of the copy
   * @return the copy
   */
  PerspectiveCuts copy(VarMap map) {
    List<Implication> copies = new ArrayList<>();
    for (Implication i : implications) {
      IntVar[] vs = i.vars();
      for (int k = 0; k < vs.length; k++) {
        vs[k] = map.get(vs[k]);
      }
      copies.add(new Implication(vs, i.weights(), i.side(), map.get(i.control()), i.when()));
    }
    return new PerspectiveCuts(copies);
  }

  /**
   * It returns violated cuts {@code sum w x <= rhs} over the columns, most efficacious first: for
   * each implication the cut of the most violated subset and the violated cuts of single variables.
   * The bounds of the variables are those of now, the root.
   *
   * @param columnOf the column of each variable that is one
   * @param value the LP solution by column
   * @param limit the most cuts returned
   * @return the cuts
   */
  List<MirCut> separate(Map<IntVar, Integer> columnOf, double[] value, int limit) {
    if (columns == null) {
      columns = new int[implications.size()][];
      controls = new int[implications.size()];
      for (int r = 0; r < columns.length; r++) {
        Implication i = implications.get(r);
        IntVar[] vs = i.vars();
        columns[r] = new int[vs.length];
        for (int k = 0; k < vs.length; k++) {
          columns[r][k] = columnOf.getOrDefault(vs[k], -1);
        }
        controls[r] = columnOf.getOrDefault(i.control(), -1);
      }
    }
    List<MirCut> found = new ArrayList<>();
    for (int r = 0; r < columns.length; r++) {
      if (controls[r] < 0) {
        continue;
      }
      try {
        separate(implications.get(r), columns[r], controls[r], value, found);
      } catch (ArithmeticException _) {
        // no cut of this implication
      }
    }
    found.sort(Comparator.comparingDouble((MirCut c) -> -c.efficacy));
    return found.size() > limit ? new ArrayList<>(found.subList(0, limit)) : found;
  }

  // the violated cuts of one implication: that of the subset most violated before rounding, and
  // those of the single variables, which the rounding to an integer bound may make the most
  // violated ones
  private static void separate(
      Implication imp, int[] column, int control, double[] value, List<MirCut> found) {
    IntVar[] vs = imp.vars();
    long[] a = imp.weights();
    double b = value[control];
    // also at beta = 1, where the rounded cuts are stronger than the big-M row
    double beta = imp.when() ? b : 1 - b;
    int n = vs.length;
    long[] lo = new long[n];
    long[] hi = new long[n];
    boolean[] best = new boolean[n];
    boolean[] free = new boolean[n];
    int size = 0;
    for (int k = 0; k < n; k++) {
      lo[k] = Math.multiplyExact(a[k], a[k] > 0 ? vs[k].min() : vs[k].max());
      hi[k] = Math.multiplyExact(a[k], a[k] > 0 ? vs[k].max() : vs[k].min());
      free[k] = column[k] >= 0 && hi[k] > lo[k];
      best[k] = free[k] && a[k] * value[column[k]] - (1 - beta) * hi[k] > beta * lo[k] + 1e-9;
      size += best[k] ? 1 : 0;
    }
    List<MirCut> cuts = new ArrayList<>();
    Set<List<Long>> seen = new HashSet<>();
    if (size > 1) {
      add(cut(imp, lo, hi, best, column, control, value), cuts, seen);
    }
    for (int k = 0; k < n; k++) {
      if (free[k]) {
        boolean[] one = new boolean[n];
        one[k] = true;
        add(cut(imp, lo, hi, one, column, control, value), cuts, seen);
      }
    }
    found.addAll(cuts);
  }

  private static void add(MirCut cut, List<MirCut> cuts, Set<List<Long>> seen) {
    if (cut == null) {
      return;
    }
    List<Long> key = new ArrayList<>();
    for (int k = 0; k < cut.columns.length; k++) {
      key.add((long) cut.columns[k]);
      key.add(cut.weights[k]);
    }
    key.add(cut.rhs);
    if (seen.add(key)) {
      cuts.add(cut);
    }
  }

  // the cut of the subset in, sum_S a x + k beta <= sum_S U with k = sum_S U + sum_{not S} L - c
  // and the side c - sum_{not S} L rounded down to a multiple of the gcd of the weights in S, or
  // null when it is not violated enough
  private static MirCut cut(
      Implication imp,
      long[] lo,
      long[] hi,
      boolean[] in,
      int[] column,
      int control,
      double[] value) {
    long[] a = imp.weights();
    Map<Integer, Long> weights = new TreeMap<>();
    long inS = 0;
    long outS = 0;
    long g = 0;
    for (int k = 0; k < a.length; k++) {
      if (in[k]) {
        weights.merge(column[k], a[k], Math::addExact);
        inS = Math.addExact(inS, hi[k]);
        g = gcd(g, Math.abs(a[k]));
      } else {
        outS = Math.addExact(outS, lo[k]);
      }
    }
    weights.values().removeIf(w -> w == 0);
    if (weights.isEmpty() || g == 0) {
      return null;
    }
    // beta = 1: sum_S a x <= c - outS, rounded down to a multiple of g
    long side = Math.multiplyExact(g, Math.floorDiv(Math.subtractExact(imp.side(), outS), g));
    long k = Math.subtractExact(inS, side);
    if (k <= 0) {
      return null; // the box alone meets it
    }
    // sum_S a x + k beta <= inS, i.e. + k b <= inS, or - k b <= inS - k, all divided by g
    weights.merge(control, imp.when() ? k : -k, Math::addExact);
    long rhs = (imp.when() ? inS : Math.subtractExact(inS, k)) / g;
    int[] cs = new int[weights.size()];
    long[] ws = new long[weights.size()];
    int n = 0;
    double activity = 0;
    double norm = 0;
    for (Map.Entry<Integer, Long> e : weights.entrySet()) {
      cs[n] = e.getKey();
      ws[n] = e.getValue() / g;
      if (Math.abs(ws[n]) > MAX_WEIGHT) {
        return null;
      }
      activity += ws[n] * value[cs[n]];
      norm += (double) ws[n] * ws[n];
      n++;
    }
    double efficacy = (activity - rhs) / Math.sqrt(norm);
    return efficacy > MirCut.MIN_EFFICACY ? MirCut.row(cs, ws, rhs, efficacy) : null;
  }

  private static long gcd(long a, long b) {
    while (b != 0) {
      long t = a % b;
      a = b;
      b = t;
    }
    return a;
  }
}
