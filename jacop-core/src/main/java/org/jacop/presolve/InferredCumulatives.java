/*
 * InferredCumulatives.java
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

package org.jacop.presolve;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Set;

/**
 * Infers redundant cumulative constraints from the cumulative resources of a model by lifting cover
 * inequalities, following Sidorov, "On Inferring Cumulative Constraints", CP 2026 (arXiv
 * 2602.15635).
 *
 * <p>A cumulative resource {@code sum_i a_i <s_i | d_i> <= b} is a knapsack inequality over the
 * occupancy vectors of its tasks: at every time point the tasks running then form a 0-1 point
 * {@code x} with {@code a x <= b}. Every valid inequality {@code pi x <= pi0} of the 0-1 points
 * that satisfy all resources at once, and the pairs of tasks that can never overlap, is then a new
 * cumulative with uses {@code pi} and capacity {@code pi0} (Lemma 7 of the paper), provided a task
 * has the same start and duration in every resource. The inequalities are found as in the paper:
 *
 * <ol>
 *   <li>covers {@code C} (sets of tasks whose uses exceed a capacity) of two and three tasks, the
 *       best by their capacity bound kept, and per resource and use value the {@code k} longest and
 *       the {@code k} shortest tasks of that use, {@code k} the least number exceeding the capacity
 *       (Algorithm 1);
 *   <li>the cover inequality {@code x(C) <= |C| - 1} is lifted sequentially (Padberg, "A note on
 *       zero-one programming", Operations Research 23(4), 1975), shortest task first, over all
 *       resources and disjoint pairs together: the coefficient of task {@code i} is {@code pi0 -
 *       v}, {@code v} the largest left-hand side with {@code x_i = 1} (Algorithm 2);
 *   <li>the inequalities that a resource of the model dominates are dropped, and the best by their
 *       capacity bound {@code sum_i d_i pi_i / pi0} (a lower bound on the span of the tasks) are
 *       returned.
 * </ol>
 *
 * <p>The disjoint pairs ({@link #disjoint}) are an addition to the paper, which lifts over the
 * resources only: a pair of tasks that the precedences order can never run at the same time, so
 * {@code x_i + x_j <= 1} holds for every time point too. Each lifting subproblem (a
 * multi-dimensional knapsack) is solved by a small branch and bound; when it runs out of nodes its
 * upper bound is used, which gives a smaller, still valid coefficient. The total work is bounded,
 * so the result does not depend on the speed of the machine.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class InferredCumulatives {

  /** The default number of covers of two and three tasks that are lifted (N_cover of the paper). */
  public static final int DEFAULT_COVERS = 100;

  /** The default number of inferred cumulatives returned (N_out of the paper). */
  public static final int DEFAULT_OUT = 5;

  /** The default largest number of tasks; with more tasks nothing is inferred. */
  public static final int DEFAULT_MAX_TASKS = 5000;

  // nodes of one lifting subproblem; beyond them its upper bound is taken
  private static final int SUBPROBLEM_NODES = 2_000;

  // elementary steps of the whole inference; the covers lifted before it runs out are kept
  private static final long DEFAULT_WORK = 200_000_000L;

  /**
   * An inferred cumulative: its tasks, their uses and its capacity.
   *
   * @param tasks the tasks, in increasing order.
   * @param use the use of each task, positive.
   * @param capacity the capacity.
   * @param bound the capacity bound {@code sum_i d_i use_i / capacity}.
   */
  public record Inferred(int[] tasks, int[] use, int capacity, double bound) {

    /**
     * It tells if this is a unary resource: capacity one, every use one.
     *
     * @return true for a unary resource.
     */
    public boolean unary() {
      return capacity == 1;
    }
  }

  private final int n;
  private final int[] duration;
  private final List<int[]> rows = new ArrayList<>();
  private final List<Integer> capacities = new ArrayList<>();
  private long[][] disjoint;
  private final long workLimit;
  private long work;

  // statistics of the last inference
  private int coversFound;
  private int coversLifted;
  private int dominated;

  /**
   * It creates the inference over tasks with the given durations.
   *
   * @param duration the duration of each task, used to rank the covers and inequalities.
   */
  public InferredCumulatives(int[] duration) {
    this(duration, DEFAULT_WORK);
  }

  /**
   * It creates the inference over tasks with the given durations and a bound on its work.
   *
   * @param duration the duration of each task, used to rank the covers and inequalities.
   * @param workLimit the largest number of elementary steps.
   */
  public InferredCumulatives(int[] duration, long workLimit) {
    this.n = duration.length;
    this.duration = duration.clone();
    this.workLimit = workLimit;
  }

  /**
   * It adds a cumulative resource. A task listed twice uses the sum of its uses; tasks of no
   * positive use are ignored.
   *
   * @param tasks the tasks of the resource.
   * @param use the least use of each task.
   * @param capacity the largest capacity.
   */
  public void resource(int[] tasks, int[] use, int capacity) {
    if (capacity <= 0) {
      return;
    }
    int[] row = new int[n];
    boolean any = false;
    for (int k = 0; k < tasks.length; k++) {
      if (tasks[k] >= 0 && use[k] > 0) {
        // a use above the capacity behaves as capacity + 1
        row[tasks[k]] = (int) Math.min((long) row[tasks[k]] + use[k], (long) capacity + 1);
        any = true;
      }
    }
    if (any) {
      rows.add(row);
      capacities.add(capacity);
    }
  }

  /**
   * It sets the pairs of tasks that can never overlap.
   *
   * @param adjacency bit j of row i is set when tasks i and j are disjoint; null for none.
   */
  public void disjoint(long[][] adjacency) {
    this.disjoint = adjacency;
  }

  /**
   * It returns the number of covers found by the last inference.
   *
   * @return the number of covers.
   */
  public int covers() {
    return coversFound;
  }

  /**
   * It returns the number of covers lifted by the last inference.
   *
   * @return the number of lifted covers.
   */
  public int lifted() {
    return coversLifted;
  }

  /**
   * It returns the number of lifted inequalities that a resource of the model dominates.
   *
   * @return the number of dominated inequalities.
   */
  public int dominated() {
    return dominated;
  }

  /**
   * It returns the work done by the last inference.
   *
   * @return the number of elementary steps.
   */
  public long work() {
    return work;
  }

  private boolean disjoint(int i, int j) {
    return disjoint != null && (disjoint[i][j >>> 6] & (1L << j)) != 0;
  }

  // a cover with its capacity bound
  private record Cover(int[] tasks, double bound) {}

  // an int array as a key of a hash set
  private record Key(int[] a) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Key k && Arrays.equals(a, k.a);
    }

    @Override
    public int hashCode() {
      return Arrays.hashCode(a);
    }

    @Override
    public String toString() {
      return Arrays.toString(a);
    }
  }

  private double coverBound(int[] c) {
    long sum = 0;
    for (int t : c) {
      sum += duration[t];
    }
    return (double) sum / (c.length - 1);
  }

  /**
   * It infers the cumulatives.
   *
   * @param maxCovers the number of covers of two and three tasks kept for lifting.
   * @param maxOut the largest number of cumulatives returned.
   * @param keep tells which inferred cumulatives may be returned (for example not the unary
   *     resources already posted); null keeps all.
   * @return the inferred cumulatives, best capacity bound first.
   */
  public List<Inferred> infer(
      int maxCovers, int maxOut, java.util.function.Predicate<Inferred> keep) {
    work = 0;
    coversFound = 0;
    coversLifted = 0;
    dominated = 0;
    List<Inferred> result = new ArrayList<>();
    if (rows.isEmpty() || n < 2 || n > DEFAULT_MAX_TASKS) {
      return result;
    }
    List<Cover> covers = covers(maxCovers);
    coversFound = covers.size();

    // (U, k): every subset of U of k tasks or more is a cover already lifted
    List<long[]> skipSets = new ArrayList<>();
    List<Integer> skipSizes = new ArrayList<>();
    Set<Key> seen = new HashSet<>();
    List<Inferred> found = new ArrayList<>();
    for (Cover c : covers) {
      if (work >= workLimit) {
        break;
      }
      if (skipped(c.tasks, skipSets, skipSizes)) {
        continue;
      }
      int[] pi = lift(c.tasks);
      if (pi == null) {
        continue;
      }
      coversLifted++;
      int pi0 = c.tasks.length - 1;
      long[] unit = new long[(n + 63) >>> 6];
      for (int t = 0; t < n; t++) {
        if (pi[t] == 1) {
          unit[t >>> 6] |= 1L << t;
        }
      }
      skipSets.add(unit);
      skipSizes.add(c.tasks.length);

      // divide by the greatest common divisor
      int g = pi0;
      for (int t = 0; t < n && g > 1; t++) {
        if (pi[t] > 0) {
          g = gcd(g, pi[t]);
        }
      }
      long sum = 0;
      int size = 0;
      for (int t = 0; t < n; t++) {
        pi[t] /= g;
        if (pi[t] > 0) {
          sum += pi[t];
          size++;
        }
      }
      pi0 /= g;
      // two tasks give a pair that the resources or the disjoint pairs already keep apart
      if (size < 3 || sum <= pi0 || dominatedByRow(pi, pi0)) {
        dominated++;
        continue;
      }
      int[] tasks = new int[size];
      int[] use = new int[size];
      long energy = 0;
      int k = 0;
      for (int t = 0; t < n; t++) {
        if (pi[t] > 0) {
          tasks[k] = t;
          use[k++] = pi[t];
          energy += (long) duration[t] * pi[t];
        }
      }
      Key key = new Key(concat(tasks, use, pi0));
      if (!seen.add(key)) {
        continue;
      }
      Inferred inf = new Inferred(tasks, use, pi0, (double) energy / pi0);
      if (keep == null || keep.test(inf)) {
        found.add(inf);
      }
    }
    found.sort(Comparator.comparingDouble((Inferred i) -> -i.bound));
    for (Inferred i : found) {
      if (result.size() >= maxOut) {
        break;
      }
      result.add(i);
    }
    return result;
  }

  private static int[] concat(int[] a, int[] b, int c) {
    int[] r = Arrays.copyOf(a, a.length + b.length + 1);
    System.arraycopy(b, 0, r, a.length, b.length);
    r[r.length - 1] = c;
    return r;
  }

  private static int gcd(int a, int b) {
    while (b != 0) {
      int t = a % b;
      a = b;
      b = t;
    }
    return a;
  }

  private boolean skipped(int[] cover, List<long[]> sets, List<Integer> sizes) {
    for (int s = 0; s < sets.size(); s++) {
      if (sizes.get(s) > cover.length) {
        continue;
      }
      long[] u = sets.get(s);
      boolean all = true;
      for (int t : cover) {
        if ((u[t >>> 6] & (1L << t)) == 0) {
          all = false;
          break;
        }
      }
      if (all) {
        return true;
      }
    }
    return false;
  }

  // pi x <= pi0 follows from a row a x <= b when pi_i / pi0 <= a_i / b for every task
  private boolean dominatedByRow(int[] pi, int pi0) {
    for (int r = 0; r < rows.size(); r++) {
      int[] a = rows.get(r);
      long b = capacities.get(r);
      boolean dom = true;
      for (int t = 0; t < n && dom; t++) {
        if (pi[t] > 0 && pi[t] * b > (long) a[t] * pi0) {
          dom = false;
        }
      }
      work += n;
      if (dom) {
        return true;
      }
    }
    return false;
  }

  // ------------------------------------------------------------------------------------------
  // covers (Algorithm 1)

  private List<Cover> covers(int maxCovers) {
    Set<Key> keys = new HashSet<>();
    PriorityQueue<Cover> best =
        new PriorityQueue<>(Comparator.comparingDouble((Cover c) -> c.bound));
    for (int r = 0; r < rows.size() && work < workLimit; r++) {
      shortCovers(rows.get(r), capacities.get(r), maxCovers, best, keys);
    }
    List<Cover> result = new ArrayList<>(best);
    result.sort(Comparator.comparingDouble((Cover c) -> -c.bound));
    Set<Key> kept = new HashSet<>();
    for (Cover c : result) {
      kept.add(new Key(c.tasks));
    }
    // long covers: per use value v, the k longest and the k shortest tasks, k * v > b
    List<Cover> longCovers = new ArrayList<>();
    for (int r = 0; r < rows.size(); r++) {
      int[] a = rows.get(r);
      int b = capacities.get(r);
      int[] tasks = tasksOf(a);
      Integer[] order = new Integer[tasks.length];
      for (int k = 0; k < tasks.length; k++) {
        order[k] = tasks[k];
      }
      // by use, then by duration, then by task
      Arrays.sort(
          order,
          Comparator.comparingInt((Integer t) -> a[t])
              .thenComparingInt(t -> duration[t])
              .thenComparingInt(t -> t));
      work += (long) tasks.length * 8;
      int from = 0;
      while (from < order.length) {
        int v = a[order[from]];
        int to = from;
        while (to < order.length && a[order[to]] == v) {
          to++;
        }
        int k = b / v + 1;
        if (k >= 2 && to - from >= k) {
          int[] shortest = new int[k];
          int[] longest = new int[k];
          for (int q = 0; q < k; q++) {
            shortest[q] = order[from + q];
            longest[q] = order[to - 1 - q];
          }
          for (int[] c : new int[][] {longest, shortest}) {
            Arrays.sort(c);
            if (kept.add(new Key(c))) {
              longCovers.add(new Cover(c, coverBound(c)));
            }
          }
        }
        from = to;
      }
    }
    longCovers.sort(Comparator.comparingDouble((Cover c) -> -c.bound));
    result.addAll(longCovers);
    return result;
  }

  private int[] tasksOf(int[] a) {
    int count = 0;
    for (int t = 0; t < n; t++) {
      if (a[t] > 0) {
        count++;
      }
    }
    int[] tasks = new int[count];
    int k = 0;
    for (int t = 0; t < n; t++) {
      if (a[t] > 0) {
        tasks[k++] = t;
      }
    }
    return tasks;
  }

  private void offer(int[] c, int maxCovers, PriorityQueue<Cover> best, Set<Key> keys) {
    double bound = coverBound(c);
    if (best.size() >= maxCovers && bound <= best.peek().bound) {
      return;
    }
    Arrays.sort(c);
    if (!keys.add(new Key(c))) {
      return;
    }
    best.add(new Cover(c, bound));
    if (best.size() > maxCovers) {
      Cover out = best.poll();
      keys.remove(new Key(out.tasks));
    }
  }

  // the covers of two tasks and, for each pair that is not a cover, the longest third task
  private void shortCovers(
      int[] a, int b, int maxCovers, PriorityQueue<Cover> best, Set<Key> keys) {
    int[] tasks = tasksOf(a);
    int m = tasks.length;
    if (m < 2) {
      return;
    }
    // by use, largest first; the tasks above a threshold of use are a prefix
    Integer[] boxed = new Integer[m];
    for (int k = 0; k < m; k++) {
      boxed[k] = tasks[k];
    }
    Arrays.sort(boxed, Comparator.comparingInt((Integer t) -> -a[t]).thenComparingInt(t -> t));
    int[] byUse = new int[m];
    int[] uses = new int[m];
    for (int k = 0; k < m; k++) {
      byUse[k] = boxed[k];
      uses[k] = a[byUse[k]];
    }
    // the three longest tasks of each prefix
    int[][] top = new int[m + 1][3];
    Arrays.fill(top[0], -1);
    for (int k = 0; k < m; k++) {
      int[] t3 = top[k + 1];
      System.arraycopy(top[k], 0, t3, 0, 3);
      int t = byUse[k];
      for (int q = 0; q < 3; q++) {
        if (t3[q] < 0 || duration[t] > duration[t3[q]]) {
          for (int z = 2; z > q; z--) {
            t3[z] = t3[z - 1];
          }
          t3[q] = t;
          break;
        }
      }
    }
    work += (long) m * 8;
    for (int x = 0; x < m && work < workLimit; x++) {
      int i = byUse[x];
      for (int y = x + 1; y < m; y++) {
        int j = byUse[y];
        work++;
        long rest = (long) b - a[i] - a[j];
        if (rest < 0) {
          offer(new int[] {i, j}, maxCovers, best, keys);
        } else {
          // the tasks of use above rest
          int p = prefix(uses, rest);
          for (int t : top[p]) {
            if (t >= 0 && t != i && t != j) {
              offer(new int[] {i, j, t}, maxCovers, best, keys);
              break;
            }
          }
        }
      }
    }
  }

  // the number of leading entries of uses (descending) greater than v
  private static int prefix(int[] uses, long v) {
    int lo = 0;
    int hi = uses.length;
    while (lo < hi) {
      int mid = (lo + hi) >>> 1;
      if (uses[mid] > v) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    return lo;
  }

  // ------------------------------------------------------------------------------------------
  // lifting (Algorithm 2)

  // the lifted coefficients of the cover inequality x(C) <= |C| - 1, or null if C is no cover
  private int[] lift(int[] cover) {
    int pi0 = cover.length - 1;
    if (!isCover(cover)) {
      return null;
    }
    int[] pi = new int[n];
    boolean[] inCover = new boolean[n];
    for (int t : cover) {
      pi[t] = 1;
      inCover[t] = true;
    }
    Integer[] order = new Integer[n - cover.length];
    int k = 0;
    for (int t = 0; t < n; t++) {
      if (!inCover[t]) {
        order[k++] = t;
      }
    }
    // shortest task first, as in the paper
    Arrays.sort(
        order, Comparator.comparingInt((Integer t) -> duration[t]).thenComparingInt(t -> t));
    int[] support = new int[n];
    int size = 0;
    for (int t : cover) {
      support[size++] = t;
    }
    for (int i : order) {
      if (work >= workLimit) {
        // the tasks not lifted keep coefficient 0, which is valid
        break;
      }
      int v = maxWith(i, support, size, pi, pi0);
      pi[i] = pi0 - v;
      if (pi[i] > 0) {
        support[size++] = i;
      }
    }
    return pi;
  }

  private boolean isCover(int[] c) {
    for (int x = 0; x < c.length; x++) {
      for (int y = x + 1; y < c.length; y++) {
        if (disjoint(c[x], c[y])) {
          return true;
        }
      }
    }
    for (int r = 0; r < rows.size(); r++) {
      long sum = 0;
      for (int t : c) {
        sum += rows.get(r)[t];
      }
      if (sum > capacities.get(r)) {
        return true;
      }
    }
    return false;
  }

  /**
   * The largest value of sum pi_c x_c over the support with x_i = 1, the resources and the disjoint
   * pairs, or an upper bound on it; at most pi0, since pi x <= pi0 is valid.
   */
  private int maxWith(int i, int[] support, int size, int[] pi, int pi0) {
    int m = rows.size();
    long[] cap = new long[m];
    for (int r = 0; r < m; r++) {
      cap[r] = (long) capacities.get(r) - rows.get(r)[i];
      if (cap[r] < 0) {
        // the task cannot run at all: any coefficient is valid
        return 0;
      }
    }
    // the items that fit with i, by coefficient, largest first
    int[] items = new int[size];
    int count = 0;
    for (int k = 0; k < size; k++) {
      int c = support[k];
      if (disjoint(i, c)) {
        continue;
      }
      boolean fits = true;
      for (int r = 0; r < m && fits; r++) {
        fits = rows.get(r)[c] <= cap[r];
      }
      if (fits) {
        items[count++] = c;
      }
    }
    work += (long) size * (m + 1);
    if (count == 0) {
      return 0;
    }
    Integer[] boxed = new Integer[count];
    for (int k = 0; k < count; k++) {
      boxed[k] = items[k];
    }
    Arrays.sort(boxed, Comparator.comparingInt((Integer c) -> -pi[c]).thenComparingInt(c -> c));
    int[] it = new int[count];
    int[] val = new int[count];
    for (int k = 0; k < count; k++) {
      it[k] = boxed[k];
      val[k] = pi[it[k]];
    }
    int upper = (int) Math.min(pi0, rootBound(it, val, cap));
    // greedy, largest coefficient first
    int greedy = greedy(it, val, cap);
    if (greedy >= upper) {
      return upper;
    }
    Search s = new Search(it, val, upper, greedy);
    s.dfs(0, 0, cap.clone(), new int[count]);
    work += s.nodes * (long) (m + count);
    return s.complete ? s.best : upper;
  }

  // the least over the resources of the fractional knapsack bound, and the sum of the values
  private long rootBound(int[] it, int[] val, long[] cap) {
    long sum = 0;
    for (int v : val) {
      sum += v;
    }
    long bound = sum;
    for (int r = 0; r < rows.size(); r++) {
      int[] a = rows.get(r);
      // values of items of no use in this row count fully; the others by value per use
      long free = 0;
      List<int[]> used = new ArrayList<>();
      for (int k = 0; k < it.length; k++) {
        if (a[it[k]] == 0) {
          free += val[k];
        } else {
          used.add(new int[] {val[k], a[it[k]]});
        }
      }
      if (used.isEmpty()) {
        continue;
      }
      used.sort((x, y) -> Long.compare((long) y[0] * x[1], (long) x[0] * y[1]));
      double left = cap[r];
      double frac = 0;
      for (int[] u : used) {
        if (u[1] <= left) {
          left -= u[1];
          frac += u[0];
        } else {
          frac += u[0] * left / u[1];
          break;
        }
      }
      bound = Math.min(bound, free + (long) Math.floor(frac + 1e-9));
      work += used.size();
    }
    return bound;
  }

  private int greedy(int[] it, int[] val, long[] capacity) {
    long[] cap = capacity.clone();
    int[] taken = new int[it.length];
    int nt = 0;
    int value = 0;
    for (int k = 0; k < it.length; k++) {
      if (fits(it[k], cap) && !disjointWithAny(it[k], it, taken, nt)) {
        take(it[k], cap);
        taken[nt++] = k;
        value += val[k];
      }
    }
    work += (long) it.length * (rows.size() + nt);
    return value;
  }

  private boolean fits(int c, long[] cap) {
    for (int r = 0; r < cap.length; r++) {
      if (rows.get(r)[c] > cap[r]) {
        return false;
      }
    }
    return true;
  }

  private void take(int c, long[] cap) {
    for (int r = 0; r < cap.length; r++) {
      cap[r] -= rows.get(r)[c];
    }
  }

  private boolean disjointWithAny(int c, int[] it, int[] taken, int nt) {
    if (disjoint == null) {
      return false;
    }
    for (int q = 0; q < nt; q++) {
      if (disjoint(c, it[taken[q]])) {
        return true;
      }
    }
    return false;
  }

  // a depth-first branch and bound over the items, largest coefficient first
  private final class Search {
    final int[] it;
    final int[] val;
    final int upper;
    int best;
    long nodes;
    boolean complete = true;

    Search(int[] it, int[] val, int upper, int best) {
      this.it = it;
      this.val = val;
      this.upper = upper;
      this.best = best;
    }

    void dfs(int pos, int value, long[] cap, int[] taken) {
      dfs(pos, value, cap, taken, 0);
    }

    // taken[0..nt) are the indices of the items in the solution
    private void dfs(int pos, int value, long[] cap, int[] taken, int nt) {
      if (best >= upper || !complete) {
        return;
      }
      if (++nodes > SUBPROBLEM_NODES) {
        complete = false;
        return;
      }
      if (value > best) {
        best = value;
      }
      // bound: the items left that still fit on their own
      long rest = 0;
      for (int k = pos; k < it.length; k++) {
        if (fits(it[k], cap) && !disjointWithAny(it[k], it, taken, nt)) {
          rest += val[k];
        }
      }
      if (value + rest <= best) {
        return;
      }
      for (int k = pos; k < it.length; k++) {
        if (fits(it[k], cap) && !disjointWithAny(it[k], it, taken, nt)) {
          long[] next = cap.clone();
          take(it[k], next);
          taken[nt] = k;
          dfs(k + 1, value + val[k], next, taken, nt + 1);
          if (best >= upper || !complete) {
            return;
          }
        }
      }
    }
  }
}
