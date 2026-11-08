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
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import org.jacop.api.VarMap;
import org.jacop.core.IntVar;
import org.jacop.util.DualFeasibleFunctions;

/**
 * Energy cuts of a resource over the start times of its tasks, separated from an LP solution.
 *
 * <p>A task j with start {@code S_j}, duration at least {@code p_j} and usage at least {@code r_j}
 * has energy {@code e_j = p_j r_j} and mean busy time {@code M_j = S_j + p_j / 2}. Cutting every
 * task down to {@code p_j} and {@code r_j} keeps a schedule feasible, so whatever holds for the cut
 * tasks holds for the model. The usage of a set S of tasks is never above {@code C' = min(C, sum
 * r_j)} and starts no earlier than {@code t = min est_j}; the energy-weighted mean busy time is
 * then least for a profile at full height from t, which gives
 *
 * <pre>
 *   sum e_j M_j &gt;= t E + E^2 / (2 C'),   E = sum e_j,
 * </pre>
 *
 * or, times {@code 2 C'} and over the starts, {@code sum 2 C' e_j S_j >= 2 C' t E + E^2 - C' sum
 * e_j p_j}. With {@code r_j = C = 1} this is the inequality of Queyranne for one machine, {@code
 * sum p_j S_j >= t p(S) + sum_{i<j} p_i p_j} (M. Queyranne, Structure of a simple scheduling
 * polyhedron, Mathematical Programming 58 (1993) 263-285), with the release date shift of the mean
 * busy time relaxation (M. X. Goemans, M. Queyranne, A. S. Schulz, M. Skutella and Y. Wang, Single
 * machine scheduling with release dates, SIAM Journal on Discrete Mathematics 15 (2002) 165-192);
 * with unit usages it is the inequality of Hall, Schulz, Shmoys and Wein for C identical machines
 * (Scheduling to minimize average completion time: off-line and on-line approximation algorithms,
 * Mathematics of Operations Research 22 (1997) 513-544). Tasks of which no two fit together ({@code
 * 2 r_j > C}) run one at a time, so they also get the one-machine form over their durations, which
 * is stronger than the energy one. Mirrored in time, {@code sum e_j M_j <= d E - E^2 / (2 C')} for
 * the latest end {@code d = max (lst_j + p_j)}.
 *
 * <p>The separation follows Queyranne's for one machine: for each release date t, the tasks
 * released at t or later in the order of their mean busy times in the LP solution, every prefix
 * checked; the most violated prefix of each t is a candidate (and in mirror the latest ends). The
 * earliest and latest starts are those of the root, so the cuts hold for the whole search.
 *
 * <p>With {@code org.jacop.lp.energyWindows=true} the separation also tries, for each release date
 * t and root deadline d, the tasks released at t or later that end by d: a short window holds few
 * tasks, so its cut can be violated where the prefixes of all tasks released at t are not. Applied
 * to the uses of a dual feasible function ({@link #mapped(int)}), a window of a few large tasks
 * gets the energy of their pairwise exclusion (J. Carlier and E. Néron, Computing redundant
 * resources for the resource constrained project scheduling problem, European Journal of
 * Operational Research 176(3) (2007) 1452-1463).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class EnergyCuts {

  // the least violation of a cut over its norm
  private static final double MIN_EFFICACY = 1e-4;

  // also separate over the tasks of each window [t, d]: released at t or later and due by d
  static boolean windows = Boolean.getBoolean("org.jacop.lp.energyWindows");

  private final IntVar[] starts;
  private final long[] dur;
  private final long[] use;
  private final long cap;

  /**
   * It creates the separation of the cuts of one resource.
   *
   * @param starts the starts of the tasks
   * @param dur the least duration of each task, positive
   * @param use the least usage of each task, positive
   * @param cap the capacity, positive
   */
  public EnergyCuts(IntVar[] starts, long[] dur, long[] use, long cap) {
    this.starts = starts.clone();
    this.dur = dur.clone();
    this.use = use.clone();
    this.cap = cap;
  }

  /**
   * It returns the separations of the same tasks with their usages and the capacity mapped by dual
   * feasible functions. Tasks that run together use at most C, so their mapped usages sum to at
   * most f(C), and the cuts of the mapped resource hold for the model too (J. Carlier and E. Néron,
   * Computing redundant resources for the resource constrained project scheduling problem, European
   * Journal of Operational Research 176(3) (2007) 1452-1463). The functions are those of {@link
   * DualFeasibleFunctions#redundantResources}; tasks mapped to 0 are left out.
   *
   * @param max the most functions
   * @return the separations, empty when no function adds anything or the sizes are too large
   */
  List<EnergyCuts> mapped(int max) {
    List<EnergyCuts> result = new ArrayList<>();
    int n = starts.length;
    if (max <= 0 || cap > DualFeasibleFunctions.MAX_SIDE) {
      return result;
    }
    int c = (int) cap;
    int[] u = new int[n];
    int[] p = new int[n];
    for (int j = 0; j < n; j++) {
      if (dur[j] > Integer.MAX_VALUE) {
        return result;
      }
      u[j] = (int) Math.min(use[j], cap);
      p[j] = (int) dur[j];
    }
    for (DualFeasibleFunctions.Resource f :
        DualFeasibleFunctions.redundantResources(u, p, c, max)) {
      List<Integer> kept = new ArrayList<>();
      for (int j = 0; j < n; j++) {
        if (f.map(u[j]) > 0) {
          kept.add(j);
        }
      }
      if (kept.size() < 2) {
        continue;
      }
      IntVar[] s = new IntVar[kept.size()];
      long[] d = new long[kept.size()];
      long[] m = new long[kept.size()];
      for (int k = 0; k < s.length; k++) {
        int j = kept.get(k);
        s[k] = starts[j];
        d[k] = dur[j];
        m[k] = f.map(u[j]);
      }
      result.add(new EnergyCuts(s, d, m, f.capacity()));
    }
    return result;
  }

  /**
   * It returns the starts of the tasks.
   *
   * @return the starts, a copy
   */
  public IntVar[] starts() {
    return starts.clone();
  }

  /**
   * It returns the copy over the variables of a copied store.
   *
   * @param map the variables of the copy
   * @return the copy
   */
  public EnergyCuts copy(VarMap map) {
    IntVar[] s = new IntVar[starts.length];
    for (int j = 0; j < s.length; j++) {
      s[j] = map.get(starts[j]);
    }
    return new EnergyCuts(s, dur, use, cap);
  }

  /**
   * It returns violated cuts {@code sum w x <= rhs} over the columns, most efficacious first.
   *
   * @param column the column of the start of each task, or -1 for a start that is no column
   * @param value the LP solution by column
   * @param lo the lower bounds at the root by column
   * @param hi the upper bounds at the root by column
   * @param limit the most cuts returned
   * @return the cuts
   */
  List<MirCut> separate(int[] column, double[] value, long[] lo, long[] hi, int limit) {
    List<Integer> all = new ArrayList<>();
    List<Integer> unary = new ArrayList<>();
    for (int j = 0; j < starts.length; j++) {
      if (column[j] >= 0 && dur[j] > 0) {
        all.add(j);
        if (2 * use[j] > cap) {
          unary.add(j);
        }
      }
    }
    List<MirCut> found = new ArrayList<>();
    try {
      for (boolean mirror : new boolean[] {false, true}) {
        separate(all, false, mirror, column, value, lo, hi, found);
        if (unary.size() >= 2 && unary.size() < all.size()) {
          separate(unary, true, mirror, column, value, lo, hi, found);
        } else if (unary.size() == all.size() && cap > 1) {
          // every task runs alone: the one-machine form is stronger than the energy one
          separate(unary, true, mirror, column, value, lo, hi, found);
        }
      }
    } catch (ArithmeticException _) {
      // the cuts found so far are exact
    }
    found.sort(Comparator.comparingDouble((MirCut c) -> -c.efficacy));
    return found.size() > limit ? new ArrayList<>(found.subList(0, limit)) : found;
  }

  // the most violated prefix for each release date; in mirror, time runs backwards from the root
  // latest ends: S'_j = -S_j - p_j, released at -(lst_j + p_j)
  private void separate(
      List<Integer> tasks,
      boolean oneMachine,
      boolean mirror,
      int[] column,
      double[] value,
      long[] lo,
      long[] hi,
      List<MirCut> found) {
    int n = tasks.size();
    if (n < 2) {
      return;
    }
    long[] est = new long[n];
    long[] due = new long[n];
    double[] start = new double[n];
    long[] p = new long[n];
    long[] r = new long[n];
    for (int k = 0; k < n; k++) {
      int j = tasks.get(k);
      int c = column[j];
      p[k] = dur[j];
      r[k] = oneMachine ? 1 : use[j];
      if (mirror) {
        est[k] = Math.negateExact(Math.addExact(hi[c], p[k]));
        due[k] = Math.negateExact(lo[c]);
        start[k] = -value[c] - p[k];
      } else {
        est[k] = lo[c];
        due[k] = Math.addExact(hi[c], p[k]);
        start[k] = value[c];
      }
    }
    long capacity = oneMachine ? 1 : cap;
    Integer[] order = new Integer[n];
    for (int k = 0; k < n; k++) {
      order[k] = k;
    }
    Arrays.sort(
        order,
        (a, b) -> {
          int d = Double.compare(start[a] + p[a] / 2.0, start[b] + p[b] / 2.0);
          return d != 0 ? d : Integer.compare(a, b);
        });
    long[] releases = Arrays.stream(est).distinct().sorted().toArray();
    long[] deadlines =
        windows ? Arrays.stream(due).distinct().sorted().toArray() : new long[] {Long.MAX_VALUE};
    for (long t : releases) {
      for (long d : deadlines) {
        if (d > t) {
          separate(
              tasks, order, t, d, est, due, p, r, start, capacity, mirror, column, value, found);
        }
      }
    }
  }

  // the most violated prefix, in the order, of the tasks released at t or later and due by d
  private static void separate(
      List<Integer> tasks,
      Integer[] order,
      long t,
      long d,
      long[] est,
      long[] due,
      long[] p,
      long[] r,
      double[] start,
      long capacity,
      boolean mirror,
      int[] column,
      double[] value,
      List<MirCut> found) {
    int n = order.length;
    // the prefix sums over the tasks released at t or later, in the order
    long e = 0;
    long ep = 0;
    long usage = 0;
    double activity = 0;
    double squares = 0;
    int count = 0;
    int bestSize = 0;
    double bestViolation = 0;
    long bestRight = 0;
    for (int q = 0; q < n; q++) {
      int k = order[q];
      if (est[k] < t || due[k] > d) {
        continue;
      }
      long ek = Math.multiplyExact(p[k], r[k]);
      e = Math.addExact(e, ek);
      ep = Math.addExact(ep, Math.multiplyExact(ek, p[k]));
      usage = Math.addExact(usage, r[k]);
      activity += (double) ek * start[k];
      squares += (double) ek * ek;
      if (++count < 2) {
        continue;
      }
      long c = Math.min(capacity, usage);
      // sum e S >= t E + (E^2 - c sum e p) / (2 c), with the right side rounded up
      long twice = Math.subtractExact(Math.multiplyExact(e, e), Math.multiplyExact(c, ep));
      long right = Math.addExact(Math.multiplyExact(t, e), Math.ceilDiv(twice, 2 * c));
      double violation = (right - activity) / Math.sqrt(squares);
      if (violation > bestViolation) {
        bestViolation = violation;
        bestSize = q + 1;
        bestRight = right;
      }
    }
    if (bestSize > 0) {
      MirCut cut =
          cut(tasks, order, bestSize, t, d, est, due, p, r, mirror, column, value, bestRight);
      if (cut != null) {
        found.add(cut);
      }
    }
  }

  // sum e_k S_k >= right over the tasks of the prefix released at t or later, as -sum e S <= -right
  // over the columns; mirrored, S' = -S - p turns it into sum e S <= -right - sum e p
  private static MirCut cut(
      List<Integer> tasks,
      Integer[] order,
      int size,
      long t,
      long d,
      long[] est,
      long[] due,
      long[] p,
      long[] r,
      boolean mirror,
      int[] column,
      double[] value,
      long right) {
    Map<Integer, Long> weights = new TreeMap<>();
    long side = Math.negateExact(right);
    long g = 0;
    for (int q = 0; q < size; q++) {
      int k = order[q];
      if (est[k] < t || due[k] > d) {
        continue;
      }
      long ek = Math.multiplyExact(p[k], r[k]);
      int c = column[tasks.get(k)];
      if (mirror) {
        weights.merge(c, ek, Math::addExact);
        side = Math.subtractExact(side, Math.multiplyExact(ek, p[k]));
      } else {
        weights.merge(c, -ek, Math::addExact);
      }
    }
    weights.values().removeIf(w -> w == 0);
    if (weights.size() < 2) {
      return null;
    }
    int[] cs = new int[weights.size()];
    long[] ws = new long[weights.size()];
    int k = 0;
    for (Map.Entry<Integer, Long> en : weights.entrySet()) {
      cs[k] = en.getKey();
      ws[k] = en.getValue();
      g = gcd(g, Math.abs(ws[k]));
      k++;
    }
    // the weights are multiples of g: the side rounds down when divided by it
    double activity = 0;
    double norm = 0;
    for (k = 0; k < ws.length; k++) {
      ws[k] /= g;
      activity += ws[k] * value[cs[k]];
      norm += (double) ws[k] * ws[k];
    }
    long rhs = Math.floorDiv(side, g);
    double efficacy = (activity - rhs) / Math.sqrt(norm);
    return efficacy > MIN_EFFICACY ? MirCut.row(cs, ws, rhs, efficacy) : null;
  }

  private static long gcd(long a, long b) {
    while (b != 0) {
      long t = a % b;
      a = b;
      b = t;
    }
    return a;
  }

  @Override
  public String toString() {
    return "EnergyCuts(" + starts.length + " tasks, capacity " + cap + ")";
  }
}
