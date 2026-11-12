/*
 * TimeIndexedBound.java
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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.constraints.cumulative.CumulativeUnaryOptional;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jalp.RevisedDualSimplex;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;

/**
 * A bound on the objective from the time-indexed relaxation of the cumulative resources.
 *
 * <p>The linear program has the rows of the model's relaxation, over its variables, and for every
 * start s<sub>j</sub> of a task of positive least duration p<sub>j</sub> and usage r<sub>j</sub> of
 * a cumulative resource the columns x<sub>jt</sub> = [s<sub>j</sub> starts in bucket t], with
 * &Sigma;<sub>t</sub> x<sub>jt</sub> = 1 and s<sub>j</sub> = &Sigma;<sub>t</sub> t x<sub>jt</sub>.
 * Each resource of capacity C gets, for every window [k, k + w) of the horizon, the row
 * &Sigma;<sub>j,t</sub> r<sub>j</sub> o<sub>jtk</sub> x<sub>jt</sub> &le; C w, where
 * o<sub>jtk</sub> is the least overlap of the task with the window over the starts of the bucket (w
 * = 1: the classic time-indexed formulation of A. A. B. Pritsker, L. J. Watters and P. M. Wolfe,
 * Multiproject scheduling with limited resources: a zero-one programming approach, Management
 * Science 16 (1969) 93-108; w &gt; 1: an interval-indexed relaxation of it, as for the
 * interval-indexed formulations of M. Queyranne and A. S. Schulz, Polyhedral approaches to machine
 * scheduling, TU Berlin report 408/1994). A precedence s<sub>i</sub> + d &le; s<sub>j</sub> between
 * two tasks of unit buckets gets the aggregated rows &Sigma;<sub>u &le; t</sub> x<sub>ju</sub> &le;
 * &Sigma;<sub>u &le; t - d</sub> x<sub>iu</sub> of N. Christofides, R. Alvarez-Valdes and J. M.
 * Tamarit, Project scheduling with resource constraints: a branch and bound approach, European
 * Journal of Operational Research 29 (1987) 262-273.
 *
 * <p>It is solved with the bounds of the variables at the root and the objective at most its
 * current bound, after interval propagation of the rows: the horizon shrinks as better solutions
 * are found (destructive lower bounding, R. Klein and A. Scholl, Computing lower bounds by
 * destructive improvement: an application to resource-constrained project scheduling, European
 * Journal of Operational Research 112 (1999) 322-346). The bound is the Lagrangian bound of the
 * duals of JaLP's solution, computed in exact integer arithmetic over the bounds of the columns, so
 * it holds whatever the rounding of the simplex; an infeasible program is checked the same way with
 * its Farkas ray. Its reason is the bound of the objective and the root bounds it used.
 *
 * <p>It is solved again when the objective bound has dropped, within a share of the run time
 * ({@code org.jacop.lp.timeIndexed.share}, 0.2) plus an allowance ({@code
 * org.jacop.lp.timeIndexed.allowance}, 1,000 ms).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class TimeIndexedBound extends Constraint
    implements Explainable, Copyable<TimeIndexedBound> {

  /**
   * The columns of the time buckets of all tasks at most, {@code org.jacop.lp.timeIndexed.columns}.
   */
  static final int MAX_COLUMNS = Integer.getInteger("org.jacop.lp.timeIndexed.columns", 20_000);

  /** The nonzeros of the window rows at most, {@code org.jacop.lp.timeIndexed.nonzeros}. */
  static final long MAX_NONZEROS = Long.getLong("org.jacop.lp.timeIndexed.nonzeros", 500_000L);

  // the share of the run time the solves may take after the first
  private static final double SHARE =
      Double.parseDouble(System.getProperty("org.jacop.lp.timeIndexed.share", "0.2"));

  // the time the solves may take beyond the share, in nanoseconds
  private static final long ALLOWANCE =
      Long.getLong("org.jacop.lp.timeIndexed.allowance", 1000L) * 1_000_000L;

  // the time of one solve at most, in milliseconds: the first, at the root, and the later ones
  private static final long FIRST_MS = Long.getLong("org.jacop.lp.timeIndexed.firstMs", 10_000L);

  private static final long SOLVE_MS = Long.getLong("org.jacop.lp.timeIndexed.solveMs", 3000L);

  // the pivots between two checks of the time
  private static final int SLICE = 500;

  // the pivots of one solve at most
  private static final int PIVOTS = Integer.getInteger("org.jacop.lp.timeIndexed.pivots", 50_000);

  // the duals are rounded to multiples of 2^-SCALE before the exact bound is computed
  private static final int SCALE = 30;

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** A cumulative resource: the starts, least durations and usages of its tasks, its capacity. */
  public record Resource(IntVar[] starts, long[] dur, long[] use, IntVar cap) {

    @Override
    public boolean equals(Object o) {
      return o instanceof Resource r
          && Arrays.equals(starts, r.starts)
          && Arrays.equals(dur, r.dur)
          && Arrays.equals(use, r.use)
          && Objects.equals(cap, r.cap);
    }

    @Override
    public int hashCode() {
      return Objects.hash(Arrays.hashCode(starts), Arrays.hashCode(dur), Arrays.hashCode(use), cap);
    }

    @Override
    public String toString() {
      return "Resource[starts="
          + Arrays.toString(starts)
          + ", dur="
          + Arrays.toString(dur)
          + ", use="
          + Arrays.toString(use)
          + ", cap="
          + cap
          + "]";
    }
  }

  private final IntVar objective;
  private final boolean maximize;
  private final List<LinearForm> rows;
  private final List<Resource> resources;

  // the variables of the program: the objective first
  private final IntVar[] vars;
  private final Map<IntVar, Integer> index = new IdentityHashMap<>();

  // the bounds of the variables at the root, captured at the first consistency at the root level
  // and again when search is back at it; each capture is a new pair of arrays, kept by the solves
  private long[] rootLo;
  private long[] rootHi;
  private int rootLevel = -1;

  /** A solve: the objective bound it assumed, the bound it gave, the root bounds it used. */
  private record Solve(long assumed, long bound, long[] lo, long[] hi) {

    @Override
    public boolean equals(Object o) {
      return o instanceof Solve v
          && assumed == v.assumed
          && bound == v.bound
          && Arrays.equals(lo, v.lo)
          && Arrays.equals(hi, v.hi);
    }

    @Override
    public int hashCode() {
      return Objects.hash(assumed, bound, Arrays.hashCode(lo), Arrays.hashCode(hi));
    }

    @Override
    public String toString() {
      return "Solve[assumed=" + assumed + ", bound=" + bound + "]";
    }
  }

  // the solves that proved something, the last one current
  private final List<Solve> proved = new ArrayList<>();
  private Solve current;
  private boolean solvedOnce;

  // re-solves back off: an event is a new objective limit or changed root bounds, and after k
  // solves in a row that proved nothing new the next solve waits for 2^k events (with LCG free
  // search the root is visited at every restart and the limit drops at every solution: cargo
  // challenge12 made 379 solves in 240 s, 45 s, for no better bound than the first ones)
  private long seenLimit = Long.MAX_VALUE;
  private int events;
  private int idle;
  private final long created = System.nanoTime();
  private long spent;

  /** The solves made. */
  public long solves;

  /** The best bound found, in the direction of the objective. */
  public long bestBound;

  /** The columns and rows of the last program. */
  public int lastColumns;

  /** The rows of the last program. */
  public int lastRows;

  /** The time of all solves in seconds. */
  public double seconds;

  /**
   * Creates the bound.
   *
   * @param objective the objective variable
   * @param maximize whether the objective is maximized
   * @param rows the rows of the relaxation of the model (rows over LP-only columns are left out)
   * @param resources the cumulative resources
   */
  public TimeIndexedBound(
      IntVar objective, boolean maximize, Collection<LinearForm> rows, List<Resource> resources) {
    this.numberId = idNumber.incrementAndGet();
    this.objective = objective;
    this.maximize = maximize;
    this.rows = new ArrayList<>();
    for (LinearForm f : rows) {
      if (f != null
          && f.relation() != LinearForm.NE
          && Arrays.stream(f.vars()).noneMatch(v -> v instanceof LpColumn)) {
        this.rows.add(f);
      }
    }
    this.resources = List.copyOf(resources);
    List<IntVar> vs = new ArrayList<>();
    add(objective, vs);
    for (LinearForm f : this.rows) {
      for (IntVar v : f.vars()) {
        add(v, vs);
      }
    }
    for (Resource r : this.resources) {
      for (IntVar s : r.starts()) {
        add(s, vs);
      }
      add(r.cap(), vs);
    }
    this.vars = vs.toArray(new IntVar[0]);
    this.bestBound = maximize ? Long.MAX_VALUE : Long.MIN_VALUE;
    this.queueIndex = 4;
    setScope(objective);
  }

  private void add(IntVar v, List<IntVar> vs) {
    if (!index.containsKey(v)) {
      index.put(v, vs.size());
      vs.add(v);
    }
  }

  /**
   * Returns the bound over the cumulative resources of the store, or null when there are none with
   * two tasks of positive least duration and usage.
   *
   * @param store the store
   * @param objective the objective
   * @param maximize whether it is maximized
   * @param rows the rows of the relaxation of the model
   * @return the bound, not imposed, or null
   */
  public static TimeIndexedBound of(
      Store store, IntVar objective, boolean maximize, Collection<LinearForm> rows) {
    List<Resource> resources = new ArrayList<>();
    for (Constraint c : LinearRelaxation.constraintsOf(store)) {
      Resource r = resource(c);
      if (r != null) {
        resources.add(r);
      }
    }
    return resources.isEmpty() ? null : new TimeIndexedBound(objective, maximize, rows, resources);
  }

  // the tasks of positive least duration and usage of a cumulative resource, or null
  private static Resource resource(Constraint c) {
    if (!(c instanceof CumulativeBasic cb)
        || c instanceof CumulativeOptional
        || c instanceof CumulativeUnaryOptional
        || cb.limit().max() <= 0) {
      return null;
    }
    IntVar[][] t = cb.tasks();
    List<IntVar> starts = new ArrayList<>();
    List<long[]> sizes = new ArrayList<>();
    for (int i = 0; i < t[0].length; i++) {
      if (t[1][i].min() > 0 && t[2][i].min() > 0) {
        starts.add(t[0][i]);
        sizes.add(new long[] {t[1][i].min(), Math.min(t[2][i].min(), cb.limit().max())});
      }
    }
    if (starts.size() < 2) {
      return null;
    }
    long[] dur = new long[starts.size()];
    long[] use = new long[starts.size()];
    for (int k = 0; k < dur.length; k++) {
      dur[k] = sizes.get(k)[0];
      use[k] = sizes.get(k)[1];
    }
    return new Resource(starts.toArray(new IntVar[0]), dur, use, cb.limit());
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  // the objective bound now, in the direction that the solves assume
  private long objectiveLimit() {
    return maximize ? -(long) objective.min() : objective.max();
  }

  @Override
  public void consistency(Store store) {
    if (rootLevel < 0 || store.level <= rootLevel) {
      // the root, or back at it after a restart: the bounds there
      rootLevel = rootLevel < 0 ? store.level : rootLevel;
      if (captureRoot()) {
        events++;
      }
    }
    long limit = objectiveLimit();
    if (limit < seenLimit) {
      seenLimit = limit;
      events++;
    }
    if (events >= 1 << Math.min(idle, 12) && mayResolve()) {
      events = 0;
      long t0 = System.nanoTime();
      long b = solve(limit);
      long dt = System.nanoTime() - t0;
      spent += dt;
      seconds += dt / 1e9;
      solves++;
      solvedOnce = true;
      boolean better = b != Long.MIN_VALUE && (current == null || b > current.bound());
      idle = better ? 0 : idle + 1;
      if (b != Long.MIN_VALUE) {
        // a weaker solve (cut short by its time limit) leaves the stronger one current: that one
        // assumed a looser objective limit and looser root bounds, so it still holds
        Solve solve = new Solve(limit, b, rootLo, rootHi);
        proved.add(solve);
        if (current == null || b >= current.bound()) {
          current = solve;
        }
        if (b != Long.MAX_VALUE) {
          long v = maximize ? -b : b;
          bestBound = maximize ? Math.min(bestBound, v) : Math.max(bestBound, v);
        }
      }
    }
    if (current == null || limit > current.assumed()) {
      return;
    }
    long bound = current.bound();
    if (bound > limit) {
      throw Store.failException;
    }
    if (maximize) {
      if (-bound < objective.max()) {
        objective.domain.inMax(store.level, objective, (int) -bound);
      }
    } else if (bound > objective.min()) {
      objective.domain.inMin(store.level, objective, (int) bound);
    }
  }

  private boolean mayResolve() {
    if (!solvedOnce) {
      return true;
    }
    return spent <= ALLOWANCE + SHARE * (System.nanoTime() - created);
  }

  // captures the root bounds and returns whether they differ from the last capture
  private boolean captureRoot() {
    if (rootLo != null) {
      boolean same = true;
      for (int j = 0; j < vars.length && same; j++) {
        same = rootLo[j] == vars[j].min() && rootHi[j] == vars[j].max();
      }
      if (same) {
        return false;
      }
    }
    rootLo = new long[vars.length];
    rootHi = new long[vars.length];
    for (int j = 0; j < vars.length; j++) {
      rootLo[j] = vars[j].min();
      rootHi[j] = vars[j].max();
    }
    return true;
  }

  // ---- the program

  /**
   * Returns the bound of the time-indexed relaxation at the root bounds with the objective at most
   * limit (at least -limit when maximizing), in the minimized direction: Long.MAX_VALUE when no
   * solution is that good, Long.MIN_VALUE when nothing was proved.
   */
  long solve(long limit) {
    int n = vars.length;
    long[] lo = rootLo.clone();
    long[] hi = rootHi.clone();
    if (maximize) {
      lo[0] = Math.max(lo[0], -limit);
    } else {
      hi[0] = Math.min(hi[0], limit);
    }
    if (lo[0] > hi[0] || !propagate(lo, hi)) {
      return Long.MAX_VALUE;
    }
    Program p = new Program(n);
    for (int j = 0; j < n; j++) {
      p.colLo.add((double) lo[j]);
      p.colHi.add((double) hi[j]);
    }
    for (LinearForm f : rows) {
      int[] cs = new int[f.vars().length];
      double[] ws = new double[cs.length];
      for (int k = 0; k < cs.length; k++) {
        cs[k] = index.get(f.vars()[k]);
        ws[k] = f.weights()[k];
      }
      double c = f.c();
      switch (f.relation()) {
        case LinearForm.LE -> p.row(cs, ws, Double.NEGATIVE_INFINITY, c);
        case LinearForm.GE -> p.row(cs, ws, c, Double.POSITIVE_INFINITY);
        default -> p.row(cs, ws, c, c);
      }
    }
    // the bucket columns of each start, with the width of the first resource that has it
    Map<Integer, int[]> buckets = new HashMap<>();
    Map<Integer, Integer> widths = new HashMap<>();
    // each resource gets a share of the caps by the columns it would have at unit width
    double[] unit = new double[resources.size()];
    double units = 0;
    for (int q = 0; q < unit.length; q++) {
      for (IntVar x : resources.get(q).starts()) {
        int j = index.get(x);
        unit[q] += hi[j] - lo[j] + 1;
      }
      units += unit[q];
    }
    for (int q = 0; q < unit.length; q++) {
      Resource r = resources.get(q);
      int w = width(r, lo, hi, widths, unit[q] / units);
      for (int k = 0; k < r.starts().length; k++) {
        int j = index.get(r.starts()[k]);
        if (!widths.containsKey(j)) {
          widths.put(j, w);
          buckets.put(j, p.buckets(j, lo[j], hi[j], w));
        }
      }
    }
    for (Resource r : resources) {
      windows(p, r, lo, hi, widths, buckets);
    }
    precedences(p, lo, hi, widths, buckets);
    lastColumns = p.columns();
    lastRows = p.rowLo.size();
    return p.bound(maximize, solvedOnce ? SOLVE_MS : FIRST_MS);
  }

  // the smallest bucket width that keeps the columns and window nonzeros of a resource in the caps
  private int width(Resource r, long[] lo, long[] hi, Map<Integer, Integer> widths, double share) {
    long w = 1;
    while (true) {
      long cols = 0;
      long nnz = 0;
      for (int k = 0; k < r.starts().length; k++) {
        int j = index.get(r.starts()[k]);
        long ww = widths.getOrDefault(j, (int) w);
        long c = (hi[j] - lo[j]) / ww + 1;
        cols += c;
        nnz += c * (r.dur()[k] / w + 2);
      }
      if ((cols <= share * MAX_COLUMNS && nnz <= share * MAX_NONZEROS)
          || w > Integer.MAX_VALUE / 2) {
        return (int) w;
      }
      w += Math.max(1, w / 4);
    }
  }

  // the window rows of a resource
  private void windows(
      Program p,
      Resource r,
      long[] lo,
      long[] hi,
      Map<Integer, Integer> widths,
      Map<Integer, int[]> buckets) {
    int m = r.starts().length;
    long tmin = Long.MAX_VALUE;
    long tmax = Long.MIN_VALUE;
    for (int k = 0; k < m; k++) {
      int j = index.get(r.starts()[k]);
      tmin = Math.min(tmin, lo[j]);
      tmax = Math.max(tmax, hi[j] + r.dur()[k]);
    }
    int w = widths.get(index.get(r.starts()[0]));
    for (int k = 1; k < m; k++) {
      w = Math.max(w, widths.get(index.get(r.starts()[k])));
    }
    long nwin = (tmax - tmin + w - 1) / w;
    if (nwin <= 0 || nwin > 10_000_000) {
      return;
    }
    List<List<Integer>> winCols = new ArrayList<>();
    List<List<Double>> winWeights = new ArrayList<>();
    for (int q = 0; q < nwin; q++) {
      winCols.add(new ArrayList<>());
      winWeights.add(new ArrayList<>());
    }
    for (int k = 0; k < m; k++) {
      int j = index.get(r.starts()[k]);
      int[] cs = buckets.get(j);
      int ww = widths.get(j);
      long d = r.dur()[k];
      for (int b = 0; b < cs.length; b++) {
        long tl = lo[j] + (long) b * ww;
        long th = Math.min(tl + ww - 1, hi[j]);
        long q0 = (tl - tmin) / w;
        long q1 = Math.min(nwin - 1, (th + d - 1 - tmin) / w);
        for (long q = q0; q <= q1; q++) {
          long ks = tmin + q * w;
          long o = Math.min(overlap(tl, d, ks, w), overlap(th, d, ks, w));
          if (o > 0) {
            winCols.get((int) q).add(cs[b]);
            winWeights.get((int) q).add((double) (r.use()[k] * o));
          }
        }
      }
    }
    int cap = index.get(r.cap());
    for (int q = 0; q < nwin; q++) {
      List<Integer> cs = winCols.get(q);
      if (cs.size() < 2) {
        continue;
      }
      int[] c = new int[cs.size() + 1];
      double[] wt = new double[c.length];
      for (int i = 0; i < cs.size(); i++) {
        c[i] = cs.get(i);
        wt[i] = winWeights.get(q).get(i);
      }
      c[cs.size()] = cap;
      wt[cs.size()] = -w;
      p.row(c, wt, Double.NEGATIVE_INFINITY, 0);
    }
  }

  private static long overlap(long s, long d, long k, long w) {
    return Math.max(0, Math.min(s + d, k + w) - Math.max(s, k));
  }

  // the aggregated precedence rows between starts with unit buckets, over prefix columns
  // y_jt = sum_{u <= t} x_ju (made once per start), so that each row has two nonzeros
  private void precedences(
      Program p, long[] lo, long[] hi, Map<Integer, Integer> widths, Map<Integer, int[]> buckets) {
    Map<Integer, int[]> prefixes = new HashMap<>();
    long budget = MAX_NONZEROS;
    for (LinearForm f : rows) {
      if (f.vars().length != 2 || f.weights()[0] != -f.weights()[1]) {
        continue;
      }
      long a = f.weights()[0];
      if (a != 1 && a != -1) {
        continue;
      }
      // a x0 - a x1 (rel) c
      int x0 = index.get(f.vars()[0]);
      int x1 = index.get(f.vars()[1]);
      if (f.relation() == LinearForm.LE || f.relation() == LinearForm.EQ) {
        // a = 1: x0 - x1 <= c, so x1 >= x0 - c
        budget -=
            precedence(
                p, a == 1 ? x0 : x1, a == 1 ? x1 : x0, -f.c(), lo, widths, buckets, prefixes);
      }
      if (f.relation() == LinearForm.GE || f.relation() == LinearForm.EQ) {
        budget -=
            precedence(p, a == 1 ? x1 : x0, a == 1 ? x0 : x1, f.c(), lo, widths, buckets, prefixes);
      }
      if (budget <= 0) {
        return;
      }
    }
  }

  // the prefix columns of a start: y_t = y_{t-1} + x_t, y over the buckets but the last (which is
  // 1)
  private static int[] prefix(Program p, int[] cs) {
    int[] y = new int[cs.length - 1];
    for (int b = 0; b < y.length; b++) {
      y[b] = p.columns();
      p.colLo.add(0.0);
      p.colHi.add(1.0);
      if (b == 0) {
        p.row(new int[] {y[0], cs[0]}, new double[] {1, -1}, 0, 0);
      } else {
        p.row(new int[] {y[b], y[b - 1], cs[b]}, new double[] {1, -1, -1}, 0, 0);
      }
    }
    return y;
  }

  // x_j >= x_i + d: j has started by t only when i had by t - d; the nonzeros added
  private static long precedence(
      Program p,
      int i,
      int j,
      long d,
      long[] lo,
      Map<Integer, Integer> widths,
      Map<Integer, int[]> buckets,
      Map<Integer, int[]> prefixes) {
    if (d <= 0
        || !buckets.containsKey(i)
        || !buckets.containsKey(j)
        || widths.get(i) != 1
        || widths.get(j) != 1
        || buckets.get(i).length < 2
        || buckets.get(j).length < 2) {
      return 0;
    }
    long nnz = 0;
    if (!prefixes.containsKey(i)) {
      prefixes.put(i, prefix(p, buckets.get(i)));
      nnz += 3L * buckets.get(i).length;
    }
    if (!prefixes.containsKey(j)) {
      prefixes.put(j, prefix(p, buckets.get(j)));
      nnz += 3L * buckets.get(j).length;
    }
    int[] yi = prefixes.get(i);
    int[] yj = prefixes.get(j);
    for (int b = 0; b < yj.length; b++) {
      long t = lo[j] + b;
      long ti = t - d - lo[i];
      if (ti >= yi.length) {
        break;
      }
      if (ti < 0) {
        // j cannot have started by t
        p.row(new int[] {yj[b]}, new double[] {1}, Double.NEGATIVE_INFINITY, 0);
        nnz++;
      } else {
        p.row(new int[] {yj[b], yi[(int) ti]}, new double[] {1, -1}, Double.NEGATIVE_INFINITY, 0);
        nnz += 2;
      }
    }
    return nnz;
  }

  // interval propagation of the rows over long bounds; false when a bound crosses
  private boolean propagate(long[] lo, long[] hi) {
    for (int pass = 0; pass < 30; pass++) {
      boolean changed = false;
      for (LinearForm f : rows) {
        int r = f.relation();
        if (r == LinearForm.LE || r == LinearForm.EQ) {
          int c = narrow(f, 1, lo, hi);
          if (c < 0) {
            return false;
          }
          changed |= c > 0;
        }
        if (r == LinearForm.GE || r == LinearForm.EQ) {
          int c = narrow(f, -1, lo, hi);
          if (c < 0) {
            return false;
          }
          changed |= c > 0;
        }
      }
      if (!changed) {
        break;
      }
    }
    return true;
  }

  // sign * (sum w x) <= sign * c: -1 when infeasible, 1 when a bound moved, 0 otherwise
  private int narrow(LinearForm f, int sign, long[] lo, long[] hi) {
    IntVar[] xs = f.vars();
    long[] ws = f.weights();
    long c = sign * f.c();
    long least = 0;
    long[] parts = new long[xs.length];
    try {
      for (int k = 0; k < xs.length; k++) {
        int j = index.get(xs[k]);
        long w = sign * ws[k];
        parts[k] = Math.multiplyExact(w, w > 0 ? lo[j] : hi[j]);
        least = Math.addExact(least, parts[k]);
      }
    } catch (ArithmeticException e) {
      return 0;
    }
    if (least > c) {
      return -1;
    }
    long room = c - least;
    int moved = 0;
    for (int k = 0; k < xs.length; k++) {
      int j = index.get(xs[k]);
      long w = sign * ws[k];
      if (w == 0) {
        continue;
      }
      long limit;
      try {
        limit = Math.addExact(parts[k], room);
      } catch (ArithmeticException e) {
        continue;
      }
      if (w > 0) {
        long b = Math.floorDiv(limit, w);
        if (b < hi[j]) {
          hi[j] = b;
          moved = 1;
        }
      } else {
        long b = Math.ceilDiv(limit, w);
        if (b > lo[j]) {
          lo[j] = b;
          moved = 1;
        }
      }
      if (lo[j] > hi[j]) {
        return -1;
      }
    }
    return moved;
  }

  /** A linear program under construction, and its exact bound. */
  private static final class Program {
    final List<int[]> rowCols = new ArrayList<>();
    final List<double[]> rowWeights = new ArrayList<>();
    final List<Double> rowLo = new ArrayList<>();
    final List<Double> rowHi = new ArrayList<>();
    final List<Double> colLo = new ArrayList<>();
    final List<Double> colHi = new ArrayList<>();
    final int given;

    Program(int given) {
      this.given = given;
    }

    int columns() {
      return colLo.size();
    }

    void row(int[] cs, double[] ws, double lo, double hi) {
      rowCols.add(cs);
      rowWeights.add(ws);
      rowLo.add(lo);
      rowHi.add(hi);
    }

    // the bucket columns of a start in [lo, hi] of width w, with their assignment and link rows
    int[] buckets(int j, long lo, long hi, int w) {
      int count = (int) ((hi - lo) / w + 1);
      int[] cs = new int[count];
      for (int b = 0; b < count; b++) {
        cs[b] = columns();
        colLo.add(0.0);
        colHi.add(1.0);
      }
      double[] ones = new double[count];
      Arrays.fill(ones, 1);
      row(cs, ones, 1, 1);
      int[] c = Arrays.copyOf(cs, count + 1);
      c[count] = j;
      double[] low = new double[count + 1];
      double[] high = new double[count + 1];
      for (int b = 0; b < count; b++) {
        low[b] = lo + (double) b * w;
        high[b] = Math.min(lo + (double) b * w + w - 1, hi);
      }
      low[count] = -1;
      high[count] = -1;
      if (w == 1) {
        row(c, low, 0, 0);
      } else {
        // sum a_b x_b <= s <= sum (a_b + w - 1) x_b
        row(c, low, Double.NEGATIVE_INFINITY, 0);
        row(c, high, 0, Double.POSITIVE_INFINITY);
      }
      return cs;
    }

    // the exact bound of the program in the minimized direction (column 0, negated when maximizing)
    long bound(boolean maximize, long millis) {
      int m = rowLo.size();
      int n = columns();
      int[][] cs = rowCols.toArray(new int[0][]);
      double[][] ws = rowWeights.toArray(new double[0][]);
      double[] lo = new double[m];
      double[] hi = new double[m];
      for (int i = 0; i < m; i++) {
        lo[i] = rowLo.get(i);
        hi[i] = rowHi.get(i);
      }
      double[] cost = new double[n];
      cost[0] = maximize ? -1 : 1;
      RevisedDualSimplex lp = new RevisedDualSimplex(cs, ws, lo, hi, cost, true);
      for (int j = 0; j < n; j++) {
        lp.setBounds(j, colLo.get(j), colHi.get(j));
      }
      // in slices of pivots, until the time of one solve is up
      long deadline = System.nanoTime() + millis * 1_000_000L;
      int status = RevisedDualSimplex.LIMIT;
      for (int done = 0; done < PIVOTS && status == RevisedDualSimplex.LIMIT; done += SLICE) {
        status = lp.solve(SLICE);
        if (System.nanoTime() > deadline) {
          break;
        }
      }
      if (status == RevisedDualSimplex.OPTIMAL) {
        double[] y = lp.duals();
        BigInteger best = null;
        for (int sign : new int[] {1, -1}) {
          BigInteger b = lagrangian(y, sign, cost, cs, ws, lo, hi);
          if (b != null && (best == null || b.compareTo(best) > 0)) {
            best = b;
          }
        }
        if (best == null) {
          return Long.MIN_VALUE;
        }
        // ceil(best / 2^SCALE)
        BigInteger[] qr = best.divideAndRemainder(BigInteger.ONE.shiftLeft(SCALE));
        BigInteger q = qr[0];
        if (qr[1].signum() > 0) {
          q = q.add(BigInteger.ONE);
        }
        if (q.bitLength() > 62) {
          return q.signum() > 0 ? Long.MAX_VALUE : Long.MIN_VALUE;
        }
        return q.longValue();
      }
      if (status == RevisedDualSimplex.INFEASIBLE) {
        double[] ray = lp.farkas();
        double[] zero = new double[n];
        for (int sign : new int[] {1, -1}) {
          BigInteger b = lagrangian(ray, sign, zero, cs, ws, lo, hi);
          if (b != null && b.signum() > 0) {
            return Long.MAX_VALUE;
          }
        }
      }
      return Long.MIN_VALUE;
    }

    // 2^SCALE times the Lagrangian bound min over the column box of cost x - y (A x - side), with
    // the multipliers sign * y rounded to multiples of 2^-SCALE (a multiplier whose side is
    // infinite is 0); null when the bound is minus infinity
    BigInteger lagrangian(
        double[] y, int sign, double[] cost, int[][] cs, double[][] ws, double[] lo, double[] hi) {
      if (y == null || y.length < rowLo.size()) {
        return null;
      }
      int m = rowLo.size();
      int n = columns();
      long[] mult = new long[m];
      BigInteger total = BigInteger.ZERO;
      for (int i = 0; i < m; i++) {
        double v = sign * y[i];
        if (!Double.isFinite(v) || Math.abs(v) > 0x1p30) {
          return null;
        }
        long q = Math.round(Math.scalb(v, SCALE));
        if (q > 0 && lo[i] == Double.NEGATIVE_INFINITY
            || q < 0 && hi[i] == Double.POSITIVE_INFINITY) {
          q = 0;
        }
        mult[i] = q;
        if (q != 0) {
          long side = (long) (q > 0 ? lo[i] : hi[i]);
          total = total.add(BigInteger.valueOf(q).multiply(BigInteger.valueOf(side)));
        }
      }
      // the reduced cost of each column, 2^SCALE times
      BigInteger[] reduced = new BigInteger[n];
      long[] fast = new long[n];
      boolean[] big = new boolean[n];
      for (int j = 0; j < n; j++) {
        fast[j] = Math.round(Math.scalb(cost[j], SCALE));
      }
      for (int i = 0; i < m; i++) {
        long q = mult[i];
        if (q == 0) {
          continue;
        }
        int[] c = cs[i];
        double[] w = ws[i];
        for (int k = 0; k < c.length; k++) {
          int j = c[k];
          long a = (long) w[k];
          if (!big[j]) {
            try {
              fast[j] = Math.subtractExact(fast[j], Math.multiplyExact(q, a));
              continue;
            } catch (ArithmeticException e) {
              big[j] = true;
              reduced[j] = BigInteger.valueOf(fast[j]);
            }
          }
          reduced[j] = reduced[j].subtract(BigInteger.valueOf(q).multiply(BigInteger.valueOf(a)));
        }
      }
      for (int j = 0; j < n; j++) {
        int s = big[j] ? reduced[j].signum() : Long.signum(fast[j]);
        if (s == 0) {
          continue;
        }
        double b = s > 0 ? colLo.get(j) : colHi.get(j);
        if (Double.isInfinite(b)) {
          return null;
        }
        BigInteger r = big[j] ? reduced[j] : BigInteger.valueOf(fast[j]);
        total = total.add(r.multiply(BigInteger.valueOf((long) b)));
      }
      return total;
    }
  }

  // ---- explanations

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    int kind = trail.kind(entry);
    if (trail.variable(entry) != objective
        || (maximize ? kind != AtomicTrail.LE : kind != AtomicTrail.GE)) {
      return false;
    }
    long v = maximize ? -(long) trail.value(entry) : trail.value(entry);
    Solve s = solveFor(trail, entry, v);
    if (s == null) {
      return false;
    }
    reason(s, trail, entry, out);
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int position = trail.size();
    long limit =
        maximize
            ? -(long) trail.minBefore(objective, position)
            : trail.maxBefore(objective, position);
    Solve s = solveFor(trail, position, limit + 1);
    if (s == null) {
      return false;
    }
    reason(s, trail, position, out);
    return true;
  }

  // the latest solve whose bound reaches v and whose assumed objective bound held before position
  private Solve solveFor(AtomicTrail trail, int position, long v) {
    long limit =
        maximize
            ? -(long) trail.minBefore(objective, position)
            : trail.maxBefore(objective, position);
    for (int k = proved.size() - 1; k >= 0; k--) {
      Solve s = proved.get(k);
      if (s.bound() >= v && limit <= s.assumed()) {
        return s;
      }
    }
    return null;
  }

  // the objective bound a solve assumed, and every root bound it used that is not initial
  private void reason(Solve s, AtomicTrail trail, int position, EntryList out) {
    if (maximize) {
      long limit = Math.max(-s.assumed(), s.lo()[0]);
      if (trail.rootDomain(objective).min() < limit) {
        trail.addBoundReaching(objective, position, true, limit, out);
      }
    } else {
      long limit = Math.min(s.assumed(), s.hi()[0]);
      if (trail.rootDomain(objective).max() > limit) {
        trail.addBoundReaching(objective, position, false, limit, out);
      }
    }
    for (int j = 0; j < vars.length; j++) {
      IntDomain d = trail.rootDomain(vars[j]);
      if (d.min() < s.lo()[j] && !(j == 0 && maximize)) {
        trail.addBoundReaching(vars[j], position, true, s.lo()[j], out);
      }
      if (d.max() > s.hi()[j] && !(j == 0 && !maximize)) {
        trail.addBoundReaching(vars[j], position, false, s.hi()[j], out);
      }
    }
  }

  @Override
  public TimeIndexedBound copy(VarMap map) {
    List<LinearForm> rs = new ArrayList<>();
    for (LinearForm f : rows) {
      rs.add(new LinearForm(map.get(f.vars()), f.weights(), f.c(), f.relation()));
    }
    List<Resource> res = new ArrayList<>();
    for (Resource r : resources) {
      res.add(new Resource(map.get(r.starts()), r.dur(), r.use(), map.get(r.cap())));
    }
    return new TimeIndexedBound(map.get(objective), maximize, rs, res);
  }

  @Override
  public String toString() {
    return id()
        + " : TimeIndexedBound("
        + objective
        + (maximize ? ", max" : ", min")
        + ", rows "
        + rows.size()
        + ", resources "
        + resources.size()
        + ")";
  }
}
