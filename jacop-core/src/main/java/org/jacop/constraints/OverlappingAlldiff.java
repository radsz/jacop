/*
 * OverlappingAlldiff.java
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
import java.util.IdentityHashMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * OverlappingAlldiff is the conjunction alldifferent(s) and alldifferent(t) of two alldifferent
 * constraints that share variables, propagated together on the bounds of the variables (Bessiere,
 * Katsirelos, Narodytska, Quimper and Walsh, "Propagating Conjunctions of AllDifferent
 * Constraints", AAAI 2010).
 *
 * <p>The variables split into the shared ones W (in s and in t), X (only in s) and Y (only in t). A
 * value can be taken by one variable of W, or by one variable of X and one of Y at the same time.
 * For each of W, X and Y and each interval of values [a, c) the constraint keeps bounds on the
 * number of its variables taking a value in the interval: at least the variables whose bounds lie
 * inside, at most those whose bounds meet it. The counts are differences p(c) - p(a) of a prefix
 * count p, so their bounds form a system of difference constraints closed by shortest paths
 * (additivity of counts over adjacent intervals, constraints (8), (11) and (12) of the paper). The
 * two alldifferents couple W with X and W with Y: count(W) + count(X) and count(W) + count(Y) are
 * at most the width of the interval (constraints (9) and (10)). Both steps are repeated to a
 * fixpoint; a negative cycle means failure. A variable is then removed from an interval at its
 * bound when the interval is full with the variables of its group that lie inside it, and is
 * restricted to an interval when every variable of its group meeting the interval is needed in it.
 *
 * <p>This is the reasoning of the paper's decomposition (3)-(12), which detects every failure of
 * the bound relaxation (Theorem 4) and enforces rules 2a-2d (Theorem 6), done directly on the
 * distinct bounds of the variables instead of on Boolean variables for every value and interval.
 * Rule 3a, which the paper needs in addition for full bounds consistency, is not applied. It is
 * stronger than bounds consistency on the two alldifferents apart: for x in 1..2, w1, w2, w3 in
 * 1..4 and z in 3..4, alldifferent([x, w1, w2, w3]) and alldifferent([w1, w2, w3, z]) each have
 * solutions, but x and z cannot share a value, so the five variables would need five of the four
 * values, and the conjunction fails at once. The intervals are bounded by the distinct bounds of
 * the variables, m of them, and a pass costs O(m<sup>3</sup>), so it is meant for small groups of
 * values such as the rows, columns and blocks of puzzles; it is used next to, not instead of, the
 * alldifferent propagators.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class OverlappingAlldiff extends Constraint
    implements SatisfiedPresent, Copyable<OverlappingAlldiff> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  static final int W = 0;
  static final int X = 1;
  static final int Y = 2;

  final IntVar[] s;
  final IntVar[] t;

  // the variables of W, X and Y
  private final IntVar[][] group;
  private final int n;

  // distinct bounds min and max + 1 of the variables, in increasing order, and their number
  private final int[] point;
  private int m;

  // matrices over the points, stored by rows of length size: for each group dist[g][a * size + c]
  // bounds p(c) - p(a) from above, p(k) being the number of the variables of the group taking a
  // value below point[k]; inside and meets count, for a < c, the variables of the group whose
  // bounds lie inside [point[a], point[c]) and those whose bounds meet it
  private final int size;
  private final int[][] dist;
  private final int[][] inside;
  private final int[][] meets;

  // bounds of the variables of the current pass and their positions among the points
  private final int[] min;
  private final int[] max;
  private final int[] lo;
  private final int[] hi;

  // first variable of each group in min, max, lo and hi
  private final int[] first;

  /**
   * It constructs the conjunction of alldifferent(s) and alldifferent(t).
   *
   * @param s variables of the first alldifferent.
   * @param t variables of the second alldifferent.
   */
  public OverlappingAlldiff(IntVar[] s, IntVar[] t) {

    checkInputForNullness(new String[] {"s", "t"}, new Object[][] {s, t});
    checkInputForDuplication("s", s);
    checkInputForDuplication("t", t);

    this.numberId = idNumber.incrementAndGet();
    this.s = Arrays.copyOf(s, s.length);
    this.t = Arrays.copyOf(t, t.length);

    IdentityHashMap<IntVar, Boolean> inT = new IdentityHashMap<>();
    for (IntVar v : t) {
      inT.put(v, Boolean.TRUE);
    }
    IdentityHashMap<IntVar, Boolean> inS = new IdentityHashMap<>();
    for (IntVar v : s) {
      inS.put(v, Boolean.TRUE);
    }
    this.group = new IntVar[3][];
    group[W] = Arrays.stream(s).filter(inT::containsKey).toArray(IntVar[]::new);
    group[X] = Arrays.stream(s).filter(v -> !inT.containsKey(v)).toArray(IntVar[]::new);
    group[Y] = Arrays.stream(t).filter(v -> !inS.containsKey(v)).toArray(IntVar[]::new);
    this.n = group[W].length + group[X].length + group[Y].length;

    this.point = new int[2 * n];
    this.size = 2 * n;
    this.dist = new int[3][size * size];
    this.inside = new int[3][size * size];
    this.meets = new int[3][size * size];
    this.min = new int[n];
    this.max = new int[n];
    this.lo = new int[n];
    this.hi = new int[n];
    this.first = new int[] {0, group[W].length, group[W].length + group[X].length, n};

    this.queueIndex = 2;

    setScope(Stream.concat(Arrays.stream(s), Arrays.stream(group[Y])));
  }

  private static void checkInputForDuplication(String name, IntVar[] v) {
    if (Arrays.stream(v).distinct().count() != v.length) {
      throw new IllegalArgumentException(
          "OverlappingAlldiff: variable occurs twice in " + name + "; alldifferent cannot hold");
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void consistency(Store store) {
    if (n == 0) {
      return;
    }
    do {
      store.propagationHasOccurred = false;
      propagate(store);
    } while (store.propagationHasOccurred);
  }

  private void propagate(Store store) {

    // distinct bounds
    int k = 0;
    for (IntVar[] g : group) {
      for (IntVar v : g) {
        min[k] = v.min();
        max[k] = v.max();
        point[2 * k] = min[k];
        point[2 * k + 1] = max[k] + 1;
        k++;
      }
    }
    Arrays.sort(point, 0, 2 * n);
    m = 0;
    for (int i = 0; i < 2 * n; i++) {
      if (m == 0 || point[i] != point[m - 1]) {
        point[m++] = point[i];
      }
    }
    for (int i = 0; i < n; i++) {
      lo[i] = Arrays.binarySearch(point, 0, m, min[i]);
      hi[i] = Arrays.binarySearch(point, 0, m, max[i] + 1);
    }

    for (int g = 0; g < 3; g++) {
      count(g);
    }

    // The counts of the bounds are closed under additivity already: inside is superadditive,
    // meets subadditive, and meets(a, c) >= meets(a, b) + inside(b, c). Only the coupling
    // tightens them; each tightening is closed again incrementally.
    boolean changed = true;
    while (changed) {
      changed = couple();
    }

    prune(store);
  }

  // inside and meets of group g, and dist from them
  private void count(int g) {
    int[] in = inside[g];
    int[] me = meets[g];
    int[] d = dist[g];
    for (int a = 0; a < m; a++) {
      Arrays.fill(in, a * size, a * size + m, 0);
    }
    // in[a * size + c] first counts the variables with lo = a and hi = c
    int total = first[g + 1] - first[g];
    int[] left = me; // left[c] = variables with hi <= c, right[a] (stored at size + a) lo >= a
    Arrays.fill(left, 0, 2 * size, 0);
    for (int i = first[g]; i < first[g + 1]; i++) {
      in[lo[i] * size + hi[i]]++;
      left[hi[i]]++;
      left[size + lo[i]]++;
    }
    for (int c = 1; c < m; c++) {
      left[c] += left[c - 1];
    }
    for (int a = m - 2; a >= 0; a--) {
      left[size + a] += left[size + a + 1];
    }
    // meets(a, c) = total - (hi <= a) - (lo >= c), kept in d before left is overwritten
    for (int a = 0; a < m; a++) {
      for (int c = a + 1; c < m; c++) {
        d[a * size + c] = total - left[a] - left[size + c];
      }
    }
    // inside(a, c) = sum of the counts with a <= lo and hi <= c, by rows from the right
    for (int a = m - 1; a >= 0; a--) {
      for (int c = a + 1; c < m; c++) {
        int v = in[a * size + c] + in[a * size + c - 1];
        if (a + 1 < m) {
          v += in[(a + 1) * size + c] - in[(a + 1) * size + c - 1];
        }
        in[a * size + c] = v;
      }
    }
    for (int a = 0; a < m; a++) {
      d[a * size + a] = 0;
      for (int c = a + 1; c < m; c++) {
        me[a * size + c] = d[a * size + c];
        d[c * size + a] = -in[a * size + c];
      }
    }
  }

  // count(W) + count(X) and count(W) + count(Y) are at most the width of an interval
  private boolean couple() {
    boolean changed = false;
    int[] dw = dist[W];
    int[] dx = dist[X];
    int[] dy = dist[Y];
    for (int a = 0; a < m; a++) {
      for (int c = a + 1; c < m; c++) {
        int width = point[c] - point[a];
        int ac = a * size + c;
        int ca = c * size + a;
        int ubw = width + Math.min(dx[ca], dy[ca]);
        if (ubw < dw[ac]) {
          tighten(dw, a, c, ubw);
          changed = true;
        }
        int ubxy = width + dw[ca];
        if (ubxy < dx[ac]) {
          tighten(dx, a, c, ubxy);
          changed = true;
        }
        if (ubxy < dy[ac]) {
          tighten(dy, a, c, ubxy);
          changed = true;
        }
      }
    }
    return changed;
  }

  // lowers the bound d(a, c) to v and restores the shortest paths; a negative cycle is a failure
  private void tighten(int[] d, int a, int c, int v) {
    if (v + d[c * size + a] < 0) {
      throw Store.failException;
    }
    for (int i = 0; i < m; i++) {
      int ia = d[i * size + a] + v;
      int row = i * size;
      int rowc = c * size;
      for (int j = 0; j < m; j++) {
        int w = ia + d[rowc + j];
        if (w < d[row + j]) {
          d[row + j] = w;
        }
      }
    }
  }

  private void prune(Store store) {
    for (int g = 0; g < 3; g++) {
      int[] d = dist[g];
      int[] in = inside[g];
      int[] me = meets[g];
      IntVar[] vars = group[g];
      for (int a = 0; a < m; a++) {
        for (int c = a + 1; c < m; c++) {
          int ac = a * size + c;
          int inAc = in[ac];
          int meAc = me[ac];
          if (meAc == inAc) {
            continue;
          }
          int ub = d[ac];
          int lb = -d[c * size + a];
          if (ub == inAc) {
            // the interval is full: the others leave it at their bounds
            for (int i = first[g]; i < first[g + 1]; i++) {
              if (hi[i] > a && lo[i] < c && (lo[i] < a || hi[i] > c)) {
                IntVar v = vars[i - first[g]];
                if (lo[i] >= a) {
                  v.domain.inMin(store.level, v, point[c]);
                } else if (hi[i] <= c) {
                  v.domain.inMax(store.level, v, point[a] - 1);
                }
              }
            }
          } else if (lb == meAc) {
            // every variable meeting the interval is needed in it
            for (int i = first[g]; i < first[g + 1]; i++) {
              if (hi[i] > a && lo[i] < c && (lo[i] < a || hi[i] > c)) {
                IntVar v = vars[i - first[g]];
                v.domain.in(
                    store.level, v, Math.max(point[a], min[i]), Math.min(point[c] - 1, max[i]));
              }
            }
          }
        }
      }
    }
  }

  @Override
  public boolean satisfied() {
    for (IntVar v : s) {
      if (!v.singleton()) {
        return false;
      }
    }
    for (IntVar v : t) {
      if (!v.singleton()) {
        return false;
      }
    }
    return distinct(s) && distinct(t);
  }

  private static boolean distinct(IntVar[] v) {
    return Arrays.stream(v).mapToInt(IntVar::value).distinct().count() == v.length;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : OverlappingAlldiff([");
    for (int i = 0; i < s.length; i++) {
      result.append(s[i]);
      if (i < s.length - 1) {
        result.append(", ");
      }
    }
    result.append("], [");
    for (int i = 0; i < t.length; i++) {
      result.append(t[i]);
      if (i < t.length - 1) {
        result.append(", ");
      }
    }
    result.append("])");
    return result.toString();
  }

  @Override
  public OverlappingAlldiff copy(VarMap map) {
    return new OverlappingAlldiff(map.get(s), map.get(t));
  }
}
