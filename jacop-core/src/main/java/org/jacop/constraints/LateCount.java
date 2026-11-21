/*
 * LateCount.java
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
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Number of late tasks on a unary resource. Tasks i with start s[i] and duration d[i] do not
 * overlap, and the number of tasks with s[i] + d[i] &gt; due[i] is at most late.
 *
 * <p>The lower bound on late is the minimum number of late jobs on one machine without release
 * dates (1||sum U_j), which the algorithm of Moore and Hodgson finds in O(n log n): take the tasks
 * by earliest due date and, whenever the current one ends after its due date, drop the longest task
 * taken so far (J. M. Moore, "An n job, one machine sequencing algorithm for minimizing the number
 * of late jobs", Management Science 15(1), 1968). With release dates the problem is NP-hard;
 * dropping them except the earliest start of all tasks gives a valid bound. A task that must be
 * late (earliest end after its due date) is counted and left out; a task that must be on time
 * (latest end within its due date) is kept on time by tightening the due dates of the others, which
 * keeps the bound exact for the relaxation: a task j before a must-be-on-time task f in due date
 * order gets min(due[j], due[f] - P(f)), a task after it due[j] - p[f], where P(f) is the duration
 * of the must-be-on-time tasks up to f. The same transformation tells whether a task can be on
 * time, and taking a task out tells whether it can be late: if forcing a task on time (late) raises
 * the bound above the maximum of late, the task must be late (on time), which bounds its start.
 * Propagation of the number of late jobs on a unary resource with release dates was studied by
 * Baptiste, Le Pape and Peridy ("Global constraints for partial CSPs: a case-study of resource and
 * due date constraints", CP 1998, LNCS 1520). Release dates are used by a relaxation: for an origin
 * t (each earliest start in turn), every task does its processing before t on a machine of its own,
 * at most t - est of it, and the rest from t on the machine, which Moore and Hodgson solves; the
 * origin with the largest bound is kept, and the earliest start of all gives the bound without
 * release dates. With the dominance rule of P. Baptiste, L. Peridy and E. Pinson ("A branch and
 * bound to minimize the number of late jobs on a single machine with release time constraints",
 * European J. Operational Research 144(1), 2003), see {@link #LateCount(IntVar[], int[], int[],
 * IntVar, boolean)}, a task on time keeps the tasks that dominate it on time.
 *
 * <p>The constraint enforces non overlap only between fixed tasks; post it as a redundant
 * constraint next to a unary resource (cumulative with capacity 1, disjunctive). late is an upper
 * bound of the count, which filters only its minimum; post the count as well when it must be equal.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class LateCount extends Constraint
    implements SatisfiedPresent, Copyable<LateCount>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final IntVar[] starts;
  final int[] durations;
  final int[] dues;
  final IntVar late;

  private final int n;

  // tasks of the relaxation (positive duration, neither surely late nor decided by a fixed start
  // ... see below) sorted by due date, and the flag of the ones that must be on time
  private final int[] order;
  private final boolean[] forced;
  private int size;

  // per position of order: the due date of a free task after the forced ones, relative to origin
  private final long[] due;

  // max-heap of durations of the tasks taken on time, and their positions
  private final int[] heap;

  // positions of the free tasks that the last run kept on time
  private final boolean[] onTime;

  private final long[] key;

  // the release dates of the dominance rule (null without it), and the pairs: dominant[k] is on
  // time when dominated[k] is
  private final int[] releases;
  private final int[] dominant;
  private final int[] dominated;

  // per position of order: the processing left after the origin of the run
  private final long[] eff;

  // per task: the bounds of its start the relaxation reads (the domains, or the trail when
  // explaining), and when explaining the minimum before weakening and the root minimum
  private final long[] lo;
  private final long[] hi;
  private final long[] low;
  private final long[] root;

  // the weight of each task, null when all are 1; uniform when all are equal
  private final int[] weights;
  private final boolean uniform;

  // the linear relaxation of weighted tasks: the free tasks by weight per unit of processing, a
  // segment tree of the slack of the nested due dates with its pending additions, the index of each
  // position of order among the free tasks, and the weights of the free tasks for the smallest ones
  private final int[] ratioOrder;
  private final long[] slack;
  private final long[] lazy;
  private final int[] position;
  private final int[] smallest;

  // the on time processing the last linear relaxation gives each position of order, and of the
  // bound before filtering: that processing, the sorted free weights with their prefix sums and
  // the count of Moore and Hodgson
  private final long[] taken;
  private final long[] baseTaken;
  private final int[] baseSorted;
  private final long[] prefix;
  private int lastCount;
  private int lastFree;
  private int baseCount;
  private int baseFree;

  // own reasons under lazy clause generation, on unless -Dorg.jacop.lateCount.reasons=false
  static final boolean REASONS = !"false".equals(System.getProperty("org.jacop.lateCount.reasons"));

  // the halvings tried when weakening the minima of a reason
  private static final int REASON_ROUNDS = 4;

  // the bound with release dates (origins after the earliest start), on unless
  // -Dorg.jacop.lateCount.releases=false
  static final boolean RELEASES =
      !"false".equals(System.getProperty("org.jacop.lateCount.releases"));

  // the result of a run whose must-be-on-time tasks cannot all be on time
  private static final int IMPOSSIBLE = Integer.MAX_VALUE / 4;

  /**
   * It constructs a late count constraint on a unary resource.
   *
   * @param starts the start of each task.
   * @param durations the duration of each task, at least 0.
   * @param dues the due date of each task: it is late if its start plus duration exceeds it.
   * @param late the bound on the number of late tasks.
   */
  public LateCount(IntVar[] starts, int[] durations, int[] dues, IntVar late) {
    this(starts, durations, dues, null, late, null);
  }

  /**
   * It constructs a late count constraint on a unary resource that also enforces the dominance rule
   * of Baptiste, Peridy and Pinson (2003) between the tasks: task i dominates task j when p[i]
   * &lt;= p[j], r[i] + p[i] &lt;= r[j] + p[j], due[i] - p[i] &gt;= due[j] - p[j] and r[i] + p[i]
   * &lt;= due[i], with r the release dates (the minima of the starts now); then if j is on time, so
   * is i. In any schedule with j on time and i late, i fits into the interval of j, and the on time
   * tasks can be left justified and the late ones put after them, so the number of late tasks stays
   * the same. Such a rule keeps an optimal schedule but removes others: it is valid only when the
   * tasks are constrained by nothing else than this unary resource, their release dates and a
   * horizon that leaves room for the late tasks at the end (each start's maximum at least max(r) +
   * sum(p) - p), and the objective counts the late tasks with one weight.
   *
   * @param starts the start of each task.
   * @param durations the duration of each task, at least 0.
   * @param dues the due date of each task: it is late if its start plus duration exceeds it.
   * @param late the bound on the number of late tasks.
   * @param dominance true to enforce the dominance rule.
   */
  public LateCount(IntVar[] starts, int[] durations, int[] dues, IntVar late, boolean dominance) {
    this(starts, durations, dues, null, late, dominance ? releases(starts) : null);
  }

  private static int[] releases(IntVar[] starts) {
    if (starts == null) {
      return new int[0];
    }
    int[] r = new int[starts.length];
    for (int i = 0; i < starts.length; i++) {
      r[i] = starts[i] == null ? 0 : starts[i].min();
    }
    return r;
  }

  /**
   * It constructs a weighted late count constraint on a unary resource: late bounds the sum of the
   * weights of the late tasks (1|r_j|sum w_j U_j). With different weights the bound is the larger
   * of the linear relaxation of the on time tasks (a knapsack over the nested due dates, which
   * greedy by weight per unit of processing solves, as the constraints form a polymatroid) and the
   * smallest weights of as many tasks as Moore and Hodgson finds late. Without release dates the
   * weighted problem is already NP-hard (it contains knapsack; E. L. Lawler and J. M. Moore, "A
   * functional equation and its application to resource allocation and sequencing problems",
   * Management Science 16(1), 1969, solve it by dynamic programming in pseudo-polynomial time). The
   * greedy algorithm is optimal over a polymatroid (J. Edmonds, "Submodular functions, matroids,
   * and certain polyhedra", Combinatorial Structures and their Applications, 1970); here every task
   * takes the least slack of the due dates from its own on, kept in a segment tree.
   *
   * @param starts the start of each task.
   * @param durations the duration of each task, at least 0.
   * @param dues the due date of each task: it is late if its start plus duration exceeds it.
   * @param weights the weight of each task, at least 0.
   * @param late the bound on the weight of the late tasks.
   */
  public LateCount(IntVar[] starts, int[] durations, int[] dues, int[] weights, IntVar late) {
    this(starts, durations, dues, checkedWeights(weights, starts), late, null);
  }

  // the weights, null when all are 1
  private static int[] checkedWeights(int[] weights, IntVar[] starts) {
    if (weights == null || starts == null || weights.length != starts.length) {
      throw new IllegalArgumentException("LateCount needs one weight per task.");
    }
    boolean ones = true;
    for (int w : weights) {
      if (w < 0) {
        throw new IllegalArgumentException("LateCount needs weights of at least 0.");
      }
      ones &= w == 1;
    }
    return ones ? null : Arrays.copyOf(weights, weights.length);
  }

  private LateCount(
      IntVar[] starts, int[] durations, int[] dues, int[] weights, IntVar late, int[] releases) {

    if (starts == null
        || durations == null
        || dues == null
        || durations.length != starts.length
        || dues.length != starts.length) {
      throw new IllegalArgumentException("LateCount needs one duration and one due date per task.");
    }
    checkInputForNullness(new String[] {"starts", "late"}, starts, new Object[] {late});
    for (int d : durations) {
      if (d < 0) {
        throw new IllegalArgumentException("LateCount needs durations of at least 0.");
      }
    }
    if (starts.length >= 1 << 24) {
      throw new IllegalArgumentException("LateCount takes at most 2^24 - 1 tasks.");
    }

    this.numberId = idNumber.incrementAndGet();
    this.starts = Arrays.copyOf(starts, starts.length);
    this.durations = Arrays.copyOf(durations, durations.length);
    this.dues = Arrays.copyOf(dues, dues.length);
    this.late = late;
    this.n = starts.length;
    this.order = new int[n];
    this.forced = new boolean[n];
    this.due = new long[n];
    this.heap = new int[n];
    this.onTime = new boolean[n];
    this.key = new long[n];
    this.eff = new long[n];
    this.weights = weights;
    boolean same = true;
    for (int i = 1; weights != null && i < n; i++) {
      same &= weights[i] == weights[0];
    }
    this.uniform = same;
    this.ratioOrder = new int[n];
    this.slack = new long[4 * Math.max(1, n)];
    this.lazy = new long[4 * Math.max(1, n)];
    this.position = new int[n];
    this.smallest = new int[n];
    this.taken = new long[n];
    this.baseTaken = new long[n];
    this.baseSorted = new int[n];
    this.prefix = new long[n + 1];
    this.lo = new long[n];
    this.hi = new long[n];
    this.low = new long[n];
    this.root = new long[n];
    this.releases = releases == null ? null : Arrays.copyOf(releases, n);
    int[][] pairs = releases == null ? new int[2][0] : dominancePairs(this.releases);
    this.dominant = pairs[0];
    this.dominated = pairs[1];

    this.queueIndex = 2;

    setScope(Stream.concat(Arrays.stream(starts), Stream.of(late)));
  }

  // the latest start of task i that is on time
  private long lastOnTime(int i) {
    return (long) dues[i] - durations[i];
  }

  @Override
  public void consistency(Store store) {

    boolean again;
    do {
      final long before = boundsSum();
      checkFixed();
      dominance(store);

      for (int i = 0; i < n; i++) {
        lo[i] = starts[i].min();
        hi[i] = starts[i].max();
      }
      long sure = prepare();
      long theta = bestOrigin();
      long origin = theta;
      int relaxed = relaxed(theta, -1, false);
      if (relaxed == IMPOSSIBLE) {
        throw Store.failException;
      }
      long bound = sure + relaxed;
      if (!uniform) {
        keepBase();
      }
      if (bound > late.max()) {
        throw Store.failException;
      }
      if (bound > late.min()) {
        late.domain.inMin(store.level, late, (int) bound);
      }

      int max = late.max();
      // tasks without duration do not use the machine: on time is always possible
      {
        for (int i = 0; i < n; i++) {
          IntVar s = starts[i];
          if (durations[i] == 0
              && bound + weight(i) > max
              && s.min() <= lastOnTime(i)
              && s.max() > lastOnTime(i)) {
            s.domain.inMax(store.level, s, (int) lastOnTime(i));
          }
        }
      }

      boolean[] kept = Arrays.copyOf(onTime, size);
      for (int k = 0; k < size; k++) {
        if (forced[k]) {
          continue;
        }
        int i = order[k];
        IntVar s = starts[i];
        // with unit weights only a task the bound takes on time can raise it when made late, and
        // only a late one when made on time
        // with equal weights only a task the bound takes on time can raise it when made late, and
        // only a late one when made on time; with other weights, a task the linear relaxation
        // leaves late (on time) does not change it when made late (on time), and the smallest
        // weights follow from the ones of the bound
        if ((!uniform || kept[k])
            && bound + weight(i) > max
            && sure + weight(i) + late(origin, k, kept, false) > max) {
          s.domain.inMax(store.level, s, (int) lastOnTime(i));
        } else if ((!uniform || !kept[k]) && sure + late(origin, k, kept, true) > max) {
          if (lastOnTime(i) >= IntDomain.MAX_INT) {
            throw Store.failException;
          }
          s.domain.inMin(store.level, s, (int) (lastOnTime(i) + 1));
        }
      }
      // also after a change of late, which may be one of the starts
      again = boundsSum() != before;
    } while (again);
  }

  /**
   * It sorts the tasks by the bounds lo and hi: it counts the ones that must be late and puts the
   * others with a positive duration into order by due date, with forced the ones that must be on
   * time.
   *
   * @return the number of tasks that must be late.
   */
  private long prepare() {
    long sure = 0;
    size = 0;
    for (int i = 0; i < n; i++) {
      if (lo[i] > lastOnTime(i)) {
        sure += weight(i);
      } else if (durations[i] > 0) {
        key[size++] = ((long) dues[i] << 24) | i;
      }
    }
    Arrays.sort(key, 0, size);
    for (int k = 0; k < size; k++) {
      int i = (int) (key[k] & 0xFFFFFF);
      order[k] = i;
      forced[k] = hi[i] <= lastOnTime(i);
    }
    return sure;
  }

  /**
   * The origin with the largest bound: the earliest start of all, or a later one with the
   * processing each task can do before it on a machine of its own taken off.
   */
  private long bestOrigin() {
    long theta = Long.MAX_VALUE;
    for (int k = 0; k < size; k++) {
      theta = Math.min(theta, lo[order[k]]);
    }
    if (RELEASES) {
      int relaxed = -1;
      for (int k = 0; k < size; k++) {
        long t = lo[order[k]];
        if (seen(k, t)) {
          continue;
        }
        int value = relaxed(t, -1, false);
        if (value > relaxed) {
          relaxed = value;
          theta = t;
          if (value == IMPOSSIBLE) {
            break;
          }
        }
      }
    }
    return theta;
  }

  /**
   * The pairs of the dominance rule of Baptiste, Peridy and Pinson (2003): i dominates j if p[i]
   * &lt;= p[j], r[i] + p[i] &lt;= r[j] + p[j], due[i] - p[i] &gt;= due[j] - p[j] and r[i] + p[i]
   * &lt;= due[i], strictly in one of the first three or with i &lt; j, which orders the rules so
   * that one optimal schedule satisfies all of them: each exchange replaces an on time task by one
   * earlier in that order.
   */
  private int[][] dominancePairs(int[] r) {
    int[] from = new int[16];
    int[] to = new int[16];
    int count = 0;
    for (int i = 0; i < n; i++) {
      long pi = durations[i];
      if (pi == 0 || r[i] + pi > dues[i]) {
        continue;
      }
      for (int j = 0; j < n; j++) {
        long pj = durations[j];
        if (j == i || pj == 0) {
          continue;
        }
        long ai = r[i] + pi;
        long aj = r[j] + pj;
        long bi = (long) dues[i] - pi;
        long bj = (long) dues[j] - pj;
        if (pi > pj || ai > aj || bi < bj) {
          continue;
        }
        if (pi == pj && ai == aj && bi == bj && i > j) {
          continue;
        }
        if (count == from.length) {
          from = Arrays.copyOf(from, 2 * count);
          to = Arrays.copyOf(to, 2 * count);
        }
        from[count] = i;
        to[count++] = j;
      }
    }
    return new int[][] {Arrays.copyOf(from, count), Arrays.copyOf(to, count)};
  }

  // the dominance rule: a dominated task on time keeps its dominant on time, a late dominant makes
  // the dominated task late
  private void dominance(Store store) {
    for (int k = 0; k < dominant.length; k++) {
      int i = dominant[k];
      int j = dominated[k];
      IntVar si = starts[i];
      IntVar sj = starts[j];
      if (sj.max() <= lastOnTime(j) && si.max() > lastOnTime(i)) {
        si.domain.inMax(store.level, si, (int) Math.max(lastOnTime(i), IntDomain.MIN_INT));
      }
      if (si.min() > lastOnTime(i) && sj.min() <= lastOnTime(j)) {
        sj.domain.inMin(store.level, sj, (int) Math.min(lastOnTime(j) + 1, IntDomain.MAX_INT));
      }
    }
  }

  // whether a task before position k in order has earliest start t
  private boolean seen(int k, long t) {
    for (int l = 0; l < k; l++) {
      if (lo[order[l]] == t) {
        return true;
      }
    }
    return false;
  }

  // the bounds of the starts change only by narrowing, so their sum tells whether one changed
  private long boundsSum() {
    long sum = 0;
    for (IntVar s : starts) {
      sum += (long) s.max() - s.min();
    }
    return sum;
  }

  // it fails if two fixed tasks with a positive duration overlap
  private void checkFixed() {
    int count = 0;
    for (int i = 0; i < n; i++) {
      if (starts[i].singleton() && durations[i] > 0) {
        key[count++] = ((long) starts[i].value() << 24) | i;
      }
    }
    Arrays.sort(key, 0, count);
    for (int k = 1; k < count; k++) {
      int a = (int) (key[k - 1] & 0xFFFFFF);
      int b = (int) (key[k] & 0xFFFFFF);
      if ((long) starts[a].value() + durations[a] > starts[b].value()) {
        throw Store.failException;
      }
    }
  }

  private long weight(int i) {
    return weights == null ? 1 : weights[i];
  }

  // the bound of relaxed(origin, k, onTime) as far as filtering needs it: when the linear
  // relaxation of the bound already has k late (on time) and Moore and Hodgson agrees, the linear
  // bound stays and the count changes by the weight of k, so only the smallest weights can raise it
  private long late(long origin, int k, boolean[] kept, boolean onTime) {
    if (!uniform && eff[k] > 0 && kept[k] == onTime) {
      if (onTime && baseTaken[k] == eff[k] && baseCount < baseFree) {
        return smallestWithout(k, baseCount);
      }
      if (!onTime && baseTaken[k] == 0 && baseCount >= 1) {
        return smallestWithout(k, baseCount - 1);
      }
    }
    return relaxed(origin, k, onTime);
  }

  // the bound's free weights, its count of Moore and Hodgson and the processing its linear
  // relaxation takes on time
  private void keepBase() {
    baseCount = lastCount;
    baseFree = lastFree;
    System.arraycopy(smallest, 0, baseSorted, 0, baseFree);
    prefix[0] = 0;
    for (int j = 0; j < baseFree; j++) {
      prefix[j + 1] = prefix[j] + baseSorted[j];
    }
    System.arraycopy(taken, 0, baseTaken, 0, size);
  }

  // the sum of the c smallest free weights of the bound without the one of position k
  private long smallestWithout(int k, int c) {
    if (c == 0) {
      return 0;
    }
    int w = weights[order[k]];
    if (w > baseSorted[c - 1]) {
      return prefix[c];
    }
    return prefix[c] - w + baseSorted[c];
  }

  /**
   * The bound on the weight of the late free tasks from origin on, as {@link #lateOf}: the count of
   * Moore and Hodgson with unit weights, else the larger of the smallest weights of that many free
   * tasks and the linear relaxation.
   */
  private int relaxed(long origin, int special, boolean specialOnTime) {
    int count = lateOf(origin, special, specialOnTime);
    lastCount = count;
    if (weights == null || count == IMPOSSIBLE) {
      return count;
    }
    // the free tasks Moore and Hodgson schedules (onTime is set for those it keeps)
    int m = 0;
    for (int k = 0; k < size; k++) {
      if (!forced[k] && k != special && eff[k] > 0) {
        smallest[m++] = weights[order[k]];
      }
    }
    lastFree = m;
    long fewest;
    if (uniform) {
      fewest = (long) count * (m > 0 ? smallest[0] : 0);
    } else {
      Arrays.sort(smallest, 0, m);
      fewest = 0;
      for (int j = 0; j < count; j++) {
        fewest += smallest[j];
      }
    }
    long best = uniform ? fewest : Math.max(fewest, linearLate(special));
    return (int) Math.min(best, IMPOSSIBLE - 1L);
  }

  /**
   * The linear relaxation of the weight of the late free tasks: the on time processing z of the
   * free tasks in order of due dates must fit before each of their due dates (as left by the forced
   * tasks, see {@link #lateOf}); the nested constraints with z between 0 and the processing form a
   * polymatroid, so taking the tasks by weight per unit of processing, each as far as the least
   * slack from its due date on allows, maximises the weight on time.
   */
  private long linearLate(int special) {
    int m = 0;
    double total = 0;
    for (int k = 0; k < size; k++) {
      taken[k] = 0;
      if (!forced[k] && k != special && eff[k] > 0) {
        position[k] = m;
        ratioOrder[m++] = k;
        total += weights[order[k]];
      } else {
        position[k] = -1;
      }
    }
    if (m == 0) {
      return 0;
    }
    build(1, 0, m - 1, m);
    sortByRatio(m);
    double onTimeWeight = 0;
    for (int j = 0; j < m; j++) {
      int k = ratioOrder[j];
      int w = weights[order[k]];
      if (w == 0) {
        break;
      }
      long room = minimum(1, 0, m - 1, position[k], m - 1);
      long z = Math.min(eff[k], room);
      if (z <= 0) {
        continue;
      }
      add(1, 0, m - 1, position[k], m - 1, -z);
      taken[k] = z;
      onTimeWeight += (double) w * z / eff[k];
    }
    double lateWeight = total - onTimeWeight;
    return (long) Math.ceil(lateWeight - 1e-6 * Math.max(1, lateWeight));
  }

  // the slack of the due dates of the free tasks, by their index among them
  private void build(int node, int left, int right, int m) {
    lazy[node] = 0;
    if (left == right) {
      slack[node] = dueOfFree(left);
      return;
    }
    int mid = (left + right) >>> 1;
    build(2 * node, left, mid, m);
    build(2 * node + 1, mid + 1, right, m);
    slack[node] = Math.min(slack[2 * node], slack[2 * node + 1]);
  }

  private long dueOfFree(int index) {
    return due[ratioOrder[index]];
  }

  private long minimum(int node, int left, int right, int from, int to) {
    if (to < left || right < from) {
      return Long.MAX_VALUE;
    }
    if (from <= left && right <= to) {
      return slack[node];
    }
    int mid = (left + right) >>> 1;
    return lazy[node]
        + Math.min(
            minimum(2 * node, left, mid, from, to),
            minimum(2 * node + 1, mid + 1, right, from, to));
  }

  private void add(int node, int left, int right, int from, int to, long value) {
    if (to < left || right < from) {
      return;
    }
    if (from <= left && right <= to) {
      slack[node] += value;
      lazy[node] += value;
      return;
    }
    int mid = (left + right) >>> 1;
    add(2 * node, left, mid, from, to, value);
    add(2 * node + 1, mid + 1, right, from, to, value);
    slack[node] = lazy[node] + Math.min(slack[2 * node], slack[2 * node + 1]);
  }

  // the free tasks by weight per unit of processing, largest first (a heap sort, without boxing)
  private void sortByRatio(int m) {
    for (int start = m / 2 - 1; start >= 0; start--) {
      sift(start, m);
    }
    for (int end = m - 1; end > 0; end--) {
      int t = ratioOrder[0];
      ratioOrder[0] = ratioOrder[end];
      ratioOrder[end] = t;
      sift(0, end);
    }
  }

  // a min-heap on the ratio, so that the sort leaves the largest first
  private void sift(int root, int end) {
    int c = root;
    while (true) {
      int l = 2 * c + 1;
      if (l >= end) {
        return;
      }
      int r = l + 1;
      int lower = r < end && smallerRatio(ratioOrder[r], ratioOrder[l]) ? r : l;
      if (!smallerRatio(ratioOrder[lower], ratioOrder[c])) {
        return;
      }
      int t = ratioOrder[c];
      ratioOrder[c] = ratioOrder[lower];
      ratioOrder[lower] = t;
      c = lower;
    }
  }

  private boolean smallerRatio(int k, int l) {
    return weights[order[k]] * eff[l] < weights[order[l]] * eff[k];
  }

  /**
   * It runs Moore and Hodgson on the tasks of order from origin on, the forced ones kept on time.
   *
   * @param origin the earliest start of the machine.
   * @param special the position of a free task taken out (late) or forced on time, -1 for none.
   * @param specialOnTime true to force the special task on time, false to take it out.
   * @return the minimum number of late free tasks, IMPOSSIBLE if the forced ones cannot be on time.
   */
  private int lateOf(long origin, int special, boolean specialOnTime) {
    // the processing left after origin: a task can do origin - est of it before, on a machine of
    // its own (a relaxation); a task with none left is on time
    for (int k = 0; k < size; k++) {
      int i = order[k];
      eff[k] = Math.max(0, durations[i] - Math.max(0, origin - lo[i]));
    }
    // forward: the due date of a free task less the forced durations before it, and the slack of
    // each forced task
    long forcedSum = 0;
    for (int k = 0; k < size; k++) {
      if (eff[k] == 0) {
        continue;
      }
      int i = order[k];
      boolean f = forced[k] || k == special && specialOnTime;
      if (f) {
        forcedSum += eff[k];
        due[k] = dues[i] - origin - forcedSum;
        if (due[k] < 0) {
          return IMPOSSIBLE;
        }
      } else {
        due[k] = dues[i] - origin - forcedSum;
      }
    }
    // backward: a free task also ends before the slack of every forced task after it
    long slack = Long.MAX_VALUE;
    for (int k = size - 1; k >= 0; k--) {
      if (eff[k] == 0) {
        continue;
      }
      boolean f = forced[k] || k == special && specialOnTime;
      if (f) {
        slack = Math.min(slack, due[k]);
      } else {
        due[k] = Math.min(due[k], slack);
      }
    }
    // Moore and Hodgson over the free tasks; their due dates are now in non decreasing order
    int heapSize = 0;
    int free = 0;
    long time = 0;
    for (int k = 0; k < size; k++) {
      onTime[k] = false;
      if (forced[k] || k == special) {
        continue;
      }
      if (eff[k] == 0) {
        onTime[k] = true;
        continue;
      }
      free++;
      long p = eff[k];
      time += p;
      heapSize = push(heapSize, k);
      onTime[k] = true;
      if (time > due[k]) {
        int longest = heap[0];
        heapSize = pop(heapSize);
        onTime[longest] = false;
        time -= eff[longest];
      }
    }
    return free - heapSize;
  }

  private boolean longer(int k, int l) {
    long a = eff[k];
    long b = eff[l];
    return a > b || a == b && k > l;
  }

  private int push(int heapSize, int k) {
    int c = heapSize;
    while (c > 0) {
      int p = (c - 1) >>> 1;
      if (!longer(k, heap[p])) {
        break;
      }
      heap[c] = heap[p];
      c = p;
    }
    heap[c] = k;
    return heapSize + 1;
  }

  private int pop(int heapSize) {
    int last = heap[heapSize - 1];
    int m = heapSize - 1;
    int c = 0;
    while (true) {
      int l = 2 * c + 1;
      if (l >= m) {
        break;
      }
      int r = l + 1;
      int better = r < m && longer(heap[r], heap[l]) ? r : l;
      if (!longer(heap[better], last)) {
        break;
      }
      heap[c] = heap[better];
      c = better;
    }
    heap[c] = last;
    return m;
  }

  /**
   * The relaxation reads, for each task, whether it must be late (its minimum after its latest on
   * time start), whether it must be on time (its maximum at most that start) and the minimum of its
   * start, and to prune it reads the maximum of late. An atom is explained by those bounds, cited
   * as weakly as they serve: late tasks by start &gt; due - p, on time ones by start &lt;= due - p,
   * the minima lowered towards their root values by a common fraction (1, 1/2, 1/4, ...) as far as
   * the bound from the same origin still implies the atom, and late by the largest maximum that
   * still fails. The dominance rule and fixed overlaps have reasons of their own.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (!REASONS || !ownReason(trail, entry, out)) {
      return false;
    }
    int kind = trail.kind(entry);
    // inMin and inMax may have moved the bound past holes next to the computed one
    if (kind == AtomicTrail.GE || kind == AtomicTrail.LE) {
      trail.addSkippedHoles(
          entry, kind == AtomicTrail.GE ? Integer.MIN_VALUE : Integer.MAX_VALUE, out);
    }
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return REASONS && ownReason(trail, trail.size(), out);
  }

  // what an own reason explains
  private static final int LATE_MIN = 0;
  private static final int ON_TIME = 1;
  private static final int MADE_LATE = 2;
  private static final int FAILURE = 3;

  /**
   * It adds the reason of the entry at position (a failure when position is the trail size), or
   * returns false when this is not an entry the constraint explains, so the generic reason is used.
   */
  private boolean ownReason(AtomicTrail trail, int position, EntryList out) {
    int what;
    int task = -1;
    for (IntVar s : starts) {
      if (s == late) {
        return false;
      }
    }
    if (position == trail.size()) {
      what = FAILURE;
    } else {
      IntVar x = trail.variable(position);
      int kind = trail.kind(position);
      long v = trail.skippedBound(position);
      if (x == late) {
        if (kind != AtomicTrail.GE) {
          return false;
        }
        what = LATE_MIN;
        return countReason(trail, position, what, -1, v, out);
      }
      for (int i = 0; i < n; i++) {
        if (starts[i] == x) {
          if (task >= 0) {
            return false;
          }
          task = i;
        }
      }
      if (task < 0) {
        return false;
      }
      if (kind == AtomicTrail.LE && lastOnTime(task) <= v) {
        what = ON_TIME;
      } else if (kind == AtomicTrail.GE && lastOnTime(task) + 1 >= v) {
        what = MADE_LATE;
      } else {
        return false;
      }
    }
    for (int i = 0; i < n; i++) {
      lo[i] = trail.minBefore(starts[i], position);
      hi[i] = trail.maxBefore(starts[i], position);
    }
    if (dominanceReason(trail, position, what, task, out)) {
      return true;
    }
    if (what == FAILURE && overlapReason(trail, position, out)) {
      return true;
    }
    return countReason(trail, position, what, task, 0, out);
  }

  // a reason from one pair of the dominance rule
  private boolean dominanceReason(
      AtomicTrail trail, int position, int what, int task, EntryList out) {
    for (int k = 0; k < dominant.length; k++) {
      int i = dominant[k];
      int j = dominated[k];
      boolean jOnTime = hi[j] <= lastOnTime(j);
      boolean iLate = lo[i] > lastOnTime(i);
      if (what == ON_TIME && i == task && jOnTime
          || what == MADE_LATE && j == task && iLate
          || what == FAILURE && jOnTime && iLate) {
        if (what != MADE_LATE) {
          trail.addBoundReaching(starts[j], position, false, lastOnTime(j), out);
        }
        if (what != ON_TIME) {
          trail.addBoundReaching(starts[i], position, true, lastOnTime(i) + 1, out);
        }
        return true;
      }
    }
    return false;
  }

  // a reason of two fixed tasks that overlap
  private boolean overlapReason(AtomicTrail trail, int position, EntryList out) {
    for (int i = 0; i < n; i++) {
      if (lo[i] != hi[i] || durations[i] == 0) {
        continue;
      }
      for (int j = i + 1; j < n; j++) {
        if (lo[j] == hi[j]
            && durations[j] > 0
            && lo[i] < lo[j] + durations[j]
            && lo[j] < lo[i] + durations[i]) {
          for (int t : new int[] {i, j}) {
            trail.addLowerBound(starts[t], position, out);
            trail.addUpperBound(starts[t], position, out);
          }
          return true;
        }
      }
    }
    return false;
  }

  /**
   * A reason from the count: the task of an atom start &lt;= due - p is taken late, of an atom
   * start &gt; due - p on time, and the count from the best origin must exceed the maximum of late
   * (or reach v for an atom late &gt;= v). The minima are then weakened at that origin.
   */
  private boolean countReason(
      AtomicTrail trail, int position, int what, int task, long v, EntryList out) {
    if (what == LATE_MIN) {
      for (int i = 0; i < n; i++) {
        lo[i] = trail.minBefore(starts[i], position);
        hi[i] = trail.maxBefore(starts[i], position);
      }
    }
    if (what == ON_TIME) {
      lo[task] = Math.max(lo[task], lastOnTime(task) + 1);
    } else if (what == MADE_LATE) {
      hi[task] = Math.min(hi[task], lastOnTime(task));
    }
    long max = trail.maxBefore(late, position);
    long sure = prepare();
    long theta = bestOrigin();
    if (!follows(what, sure, relaxed(theta, -1, false), v, max)) {
      return false;
    }
    for (int k = 0; k < size; k++) {
      int i = order[k];
      low[i] = lo[i];
      root[i] = Math.min(lo[i], trail.rootDomain(starts[i]).min());
    }
    double fraction = 0;
    double step = 1;
    for (int round = 0; round < REASON_ROUNDS && fraction < 1; round++) {
      double tryFraction = fraction + step;
      if (tryFraction <= 1 && follows(what, sure, relaxedAt(theta, tryFraction), v, max)) {
        fraction = tryFraction;
      }
      step /= 2;
    }
    int relaxed = relaxedAt(theta, fraction);
    for (int i = 0; i < n; i++) {
      if (lo[i] > lastOnTime(i)) {
        if (i != task || what != ON_TIME) {
          trail.addBoundReaching(starts[i], position, true, lastOnTime(i) + 1, out);
        }
      } else if (durations[i] > 0) {
        if (hi[i] <= lastOnTime(i) && (i != task || what != MADE_LATE)) {
          trail.addBoundReaching(starts[i], position, false, lastOnTime(i), out);
        }
        trail.addBoundReaching(starts[i], position, true, lo[i], out);
      }
    }
    if (what != LATE_MIN && relaxed != IMPOSSIBLE) {
      trail.addBoundReaching(late, position, false, sure + (long) relaxed - 1, out);
    }
    return true;
  }

  // the count from origin theta with the minima of the relaxed tasks lowered by fraction
  private int relaxedAt(long theta, double fraction) {
    for (int k = 0; k < size; k++) {
      int i = order[k];
      lo[i] = low[i] - (long) Math.floor(fraction * (low[i] - root[i]));
    }
    return relaxed(theta, -1, false);
  }

  private static boolean follows(int what, long sure, int relaxed, long v, long max) {
    if (relaxed == IMPOSSIBLE) {
      return true;
    }
    long count = sure + (long) relaxed;
    return what == LATE_MIN ? count >= v : count > max;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    long count = 0;
    for (IntVar s : starts) {
      if (!s.singleton()) {
        return false;
      }
    }
    for (int i = 0; i < n; i++) {
      if (starts[i].value() > lastOnTime(i)) {
        count += weight(i);
      }
      for (int j = i + 1; j < n; j++) {
        if (durations[i] > 0
            && durations[j] > 0
            && starts[i].value() < (long) starts[j].value() + durations[j]
            && starts[j].value() < (long) starts[i].value() + durations[i]) {
          return false;
        }
      }
    }
    return count <= late.min();
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : LateCount([");
    for (int i = 0; i < n; i++) {
      result.append(starts[i]);
      if (i < n - 1) {
        result.append(", ");
      }
    }
    result.append("], ").append(Arrays.toString(durations));
    result.append(", ").append(Arrays.toString(dues));
    result.append(", ").append(late);
    if (releases != null) {
      result.append(", dominance");
    }
    if (weights != null) {
      result.append(", weights ").append(Arrays.toString(weights));
    }
    result.append(")");

    return result.toString();
  }

  @Override
  public LateCount copy(VarMap map) {
    return new LateCount(map.get(starts), durations, dues, weights, map.get(late), releases);
  }
}
