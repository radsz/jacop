/*
 * CoveringDominance.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.LinearForm;

/**
 * Column dominance of covering models: fixes to 0 the 0/1 variables of a minimized objective whose
 * clauses another variable covers at no higher cost.
 *
 * <p>A candidate is a 0/1 variable with a cost of at least 0 in the objective that occurs only in
 * the objective's definition and, positively, in clauses. A candidate {@code y} is dominated by a
 * candidate {@code x} when every clause on {@code y} also holds {@code x} and the cost of {@code x}
 * is at most that of {@code y}: in any solution with {@code y = 1}, setting {@code y = 0} and
 * {@code x = 1} keeps every clause true and does not raise the cost. So {@code y = 0} keeps an
 * optimal solution. Pairs with the same clauses and costs are taken in the order of the variables,
 * and every dominance moves along the order (more clauses, then lower cost, then earlier), so all
 * dominated variables are fixed at once. This is the column reduction of set covering (R. S.
 * Garfinkel and G. L. Nemhauser, "Integer Programming", Wiley 1972, chapter 8; C. Toregas and C.
 * ReVelle, "Binary logic solutions to a class of location problem", Geographical Analysis 5, 1973);
 * CP-SAT's presolve finds such pairs with its dominance detection (var_domination). The
 * pseudo-Boolean competition's pdc.r (6,904 covering clauses over 19,021 variables) keeps 2,968 of
 * them, and JaCoP proves its optimum 94 in 17-21 s, where it found 97 in 120 s before.
 *
 * <p>The variables are fixed only when at least {@link #minFixed()} of them are dominated. The rule
 * removes optimal solutions, so it runs only for a minimized or maximized objective, without proof
 * logging.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class CoveringDominance {

  /**
   * Whether the rule runs (system property org.jacop.fz.coveringDominance, default true).
   *
   * @return true unless the property is false
   */
  static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.coveringDominance"));
  }

  /**
   * The fewest dominated variables for which the rule fixes them (system property
   * org.jacop.fz.coveringDominance.min, default 100).
   *
   * @return the threshold
   */
  static int minFixed() {
    return Integer.getInteger("org.jacop.fz.coveringDominance.min", 100);
  }

  // the most clause memberships compared in all
  private static final long MAX_WORK = 50_000_000L;

  private CoveringDominance() {}

  /**
   * The outcome.
   *
   * @param candidates the variables the rule may fix
   * @param fixed the variables fixed to 0
   */
  record Outcome(int candidates, int fixed) {}

  /**
   * Fixes the dominated variables to 0.
   *
   * @param store the store, at its root
   * @param clauses the clauses collected for the SAT solver, positive and negative variables
   * @param objective the objective
   * @param maximize true when the objective is maximized
   * @return the outcome, or null when the model is no covering model
   */
  static Outcome run(Store store, List<IntVar[][]> clauses, IntVar objective, boolean maximize) {
    // the objective as a sum of weighted variables, through the equalities that define its
    // integer terms (such as the block sums of a long sum that lazy clause generation splits)
    Map<IntVar, Long> cost = new IdentityHashMap<>();
    Set<Constraint> definitions = Collections.newSetFromMap(new IdentityHashMap<>());
    cost.put(objective, maximize ? -1L : 1L);
    ArrayDeque<IntVar> open = new ArrayDeque<>();
    open.add(objective);
    List<IntVar> expanded = new ArrayList<>();
    List<long[]> ranges = new ArrayList<>();
    while (!open.isEmpty()) {
      IntVar y = open.poll();
      Long scale = cost.get(y);
      if (scale == null || y.min() >= 0 && y.max() <= 1 && y != objective) {
        continue;
      }
      Constraint definition = null;
      LinearForm form = null;
      long a = 0;
      for (Constraint c : y.dom().constraints()) {
        LinearForm f = definitions.contains(c) ? null : LinearForms.of(c);
        if (f == null || f.relation() != LinearForm.EQ) {
          continue;
        }
        long k = 0;
        for (int i = 0; i < f.vars().length; i++) {
          if (f.vars()[i] == y) {
            k += f.weights()[i];
          }
        }
        if (Math.abs(k) == 1) {
          definition = c;
          form = f;
          a = k;
          break;
        }
      }
      if (definition == null) {
        return null;
      }
      definitions.add(definition);
      cost.remove(y);
      // the values the definition gives y over the domains of its other variables
      long lo = form.c();
      long hi = form.c();
      for (int i = 0; i < form.vars().length; i++) {
        IntVar v = form.vars()[i];
        if (v != y) {
          long w = form.weights()[i];
          lo -= Math.max(w * v.min(), w * v.max());
          hi -= Math.min(w * v.min(), w * v.max());
        }
      }
      expanded.add(y);
      ranges.add(a == 1 ? new long[] {lo, hi} : new long[] {-hi, -lo});
      // a y + sum w v = c, so y = (c - sum w v) / a and scale * y = -scale * a * sum w v + ...
      for (int i = 0; i < form.vars().length; i++) {
        IntVar v = form.vars()[i];
        if (v == y || v.singleton()) {
          continue;
        }
        cost.merge(v, -scale * a * form.weights()[i], Long::sum);
        if (v.min() < 0 || v.max() > 1) {
          open.add(v);
        }
      }
      if (definitions.size() > 100_000) {
        return null;
      }
    }
    // a swap moves the objective towards its optimum and the variables defined on the way either
    // way: they must be in no other constraint, and their domains must not cut what their
    // definitions give (such as a lower bound of a minimized objective above the least cost)
    for (int i = 0; i < expanded.size(); i++) {
      IntVar y = expanded.get(i);
      long[] range = ranges.get(i);
      boolean lowOk = y == objective && maximize || y.min() <= range[0];
      boolean highOk = y == objective && !maximize || y.max() >= range[1];
      if (!lowOk || !highOk || y.dom().noIntervals() != 1 || !onlyIn(store, y, definitions)) {
        return null;
      }
    }
    // the clauses, as candidate memberships; a variable in a clause negatively is no candidate
    Map<IntVar, Integer> index = new IdentityHashMap<>();
    List<IntVar> vars = new ArrayList<>();
    Set<IntVar> excluded = Collections.newSetFromMap(new IdentityHashMap<>());
    List<int[]> rows = new ArrayList<>();
    for (IntVar[][] clause : clauses) {
      boolean satisfied = false;
      for (IntVar x : clause[0]) {
        satisfied |= x.singleton(1);
      }
      for (IntVar x : clause[1]) {
        satisfied |= x.singleton(0);
        excluded.add(x);
      }
      if (satisfied) {
        continue;
      }
      int[] row = new int[clause[0].length];
      int n = 0;
      for (IntVar x : clause[0]) {
        if (!x.singleton()) {
          Integer j = index.get(x);
          if (j == null) {
            j = vars.size();
            index.put(x, j);
            vars.add(x);
          }
          row[n++] = j;
        }
      }
      rows.add(Arrays.copyOf(row, n));
    }
    // candidates: 0/1, cost >= 0, in no other constraint than the definition
    int m = vars.size();
    boolean[] candidate = new boolean[m];
    int candidates = 0;
    for (int j = 0; j < m; j++) {
      IntVar x = vars.get(j);
      Long c = cost.get(x);
      if (excluded.contains(x) || c == null || c < 0 || x.min() != 0 || x.max() != 1) {
        continue;
      }
      if (onlyIn(store, x, definitions)) {
        candidate[j] = true;
        candidates++;
      }
    }
    if (candidates == 0) {
      return null;
    }
    // the rows of each candidate, sorted
    int[][] rowsOf = new int[m][];
    int[] count = new int[m];
    for (int[] row : rows) {
      for (int j : row) {
        count[j]++;
      }
    }
    for (int j = 0; j < m; j++) {
      rowsOf[j] = new int[count[j]];
      count[j] = 0;
    }
    for (int r = 0; r < rows.size(); r++) {
      for (int j : rows.get(r)) {
        rowsOf[j][count[j]++] = r;
      }
    }
    boolean[] zero = new boolean[m];
    long work = 0;
    for (int y = 0; y < m && work < MAX_WORK; y++) {
      if (!candidate[y] || rowsOf[y].length == 0) {
        continue;
      }
      // the dominating candidates are in every row of y, so in its shortest
      int[] shortest = rows.get(rowsOf[y][0]);
      for (int r : rowsOf[y]) {
        if (rows.get(r).length < shortest.length) {
          shortest = rows.get(r);
        }
      }
      long cy = cost.get(vars.get(y));
      for (int x : shortest) {
        if (x == y || !candidate[x] || zero[x]) {
          continue;
        }
        long cx = cost.get(vars.get(x));
        if (cx > cy || rowsOf[x].length < rowsOf[y].length) {
          continue;
        }
        work += rowsOf[y].length + rowsOf[x].length;
        if (!contains(rowsOf[x], rowsOf[y])) {
          continue;
        }
        // strictly along the order: more rows, then lower cost, then the earlier variable
        if (rowsOf[x].length > rowsOf[y].length || cx < cy || x < y) {
          zero[y] = true;
          break;
        }
      }
    }
    List<IntVar> toFix = new ArrayList<>();
    for (int y = 0; y < m; y++) {
      if (zero[y]) {
        toFix.add(vars.get(y));
      }
    }
    // the candidates in no clause, of cost at least 0, are 0 in an optimal solution as well
    for (Map.Entry<IntVar, Long> e : cost.entrySet()) {
      IntVar v = e.getKey();
      if (!index.containsKey(v)
          && !excluded.contains(v)
          && e.getValue() > 0
          && v.min() == 0
          && v.max() == 1
          && onlyIn(store, v, definitions)) {
        toFix.add(v);
      }
    }
    // a few fixings shrink the model little but move the search: fir09_area_opers (2 fixings)
    // found its optimum 34 in 142 s without them and not in 600 s with them
    if (toFix.size() < minFixed()) {
      return new Outcome(candidates, 0);
    }
    for (IntVar v : toFix) {
      v.domain.in(store.level, v, 0, 0);
    }
    int fixed = toFix.size();
    if (fixed > 0) {
      simplify(clauses);
    }
    return new Outcome(candidates, fixed);
  }

  // drops the clauses that a fixed literal satisfies and the fixed false literals of the others,
  // so that the rows built from them later (the linear relaxation's clause rows) carry no column
  // of a fixed variable: with the 16,053 fixed columns of pdc.r left in, the root trial of the
  // clause rows kept none of them and the root bound stayed 15 instead of 88
  private static void simplify(List<IntVar[][]> clauses) {
    List<IntVar[][]> kept = new ArrayList<>(clauses.size());
    for (IntVar[][] clause : clauses) {
      boolean satisfied = false;
      boolean changed = false;
      for (IntVar x : clause[0]) {
        satisfied |= x.singleton(1);
        changed |= x.singleton(0);
      }
      for (IntVar x : clause[1]) {
        satisfied |= x.singleton(0);
        changed |= x.singleton(1);
      }
      if (satisfied) {
        continue;
      }
      if (!changed) {
        kept.add(clause);
        continue;
      }
      kept.add(
          new IntVar[][] {
            Arrays.stream(clause[0]).filter(x -> !x.singleton()).toArray(IntVar[]::new),
            Arrays.stream(clause[1]).filter(x -> !x.singleton()).toArray(IntVar[]::new)
          });
    }
    clauses.clear();
    clauses.addAll(kept);
  }

  // whether every constraint on x is one of the definitions
  private static boolean onlyIn(Store store, IntVar x, Set<Constraint> definitions) {
    Set<Constraint> on = new LinkedHashSet<>(x.dom().constraints());
    on.addAll(store.valueWatchers(x));
    on.addAll(store.watchedLiteralConstraints((Var) x));
    for (Constraint c : on) {
      if (!definitions.contains(c)) {
        return false;
      }
    }
    return true;
  }

  // whether the sorted array a holds every element of the sorted array b
  private static boolean contains(int[] a, int[] b) {
    int i = 0;
    for (int e : b) {
      while (i < a.length && a[i] < e) {
        i++;
      }
      if (i == a.length || a[i] != e) {
        return false;
      }
      i++;
    }
    return true;
  }
}
