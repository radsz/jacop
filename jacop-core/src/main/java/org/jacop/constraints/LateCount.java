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
public class LateCount extends Constraint implements SatisfiedPresent, Copyable<LateCount> {

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
    this(starts, durations, dues, late, null);
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
    this(starts, durations, dues, late, dominance ? releases(starts) : null);
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

  private LateCount(IntVar[] starts, int[] durations, int[] dues, IntVar late, int[] releases) {

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

      // count the tasks that must be late, collect the others with a positive duration
      int sure = 0;
      size = 0;
      long origin = Long.MAX_VALUE;
      for (int i = 0; i < n; i++) {
        IntVar s = starts[i];
        if (s.min() > lastOnTime(i)) {
          sure++;
        } else if (durations[i] > 0) {
          key[size++] = ((long) dues[i] << 24) | i;
          origin = Math.min(origin, s.min());
        }
      }
      Arrays.sort(key, 0, size);
      for (int k = 0; k < size; k++) {
        int i = (int) (key[k] & 0xFFFFFF);
        order[k] = i;
        forced[k] = starts[i].max() <= lastOnTime(i);
      }

      // the origin with the largest bound: the earliest start of all, or a later one with the
      // processing each task can do before it on a machine of its own taken off
      long theta = origin;
      int relaxed = -1;
      if (RELEASES) {
        for (int k = 0; k < size; k++) {
          long t = starts[order[k]].min();
          if (seen(k, t)) {
            continue;
          }
          int value = lateOf(t, -1, false);
          if (value > relaxed) {
            relaxed = value;
            theta = t;
            if (value == IMPOSSIBLE) {
              break;
            }
          }
        }
      }
      relaxed = lateOf(theta, -1, false);
      origin = theta;
      if (relaxed == IMPOSSIBLE) {
        throw Store.failException;
      }
      int bound = sure + relaxed;
      if (bound > late.max()) {
        throw Store.failException;
      }
      if (bound > late.min()) {
        late.domain.inMin(store.level, late, bound);
      }

      int max = late.max();
      // tasks without duration do not use the machine: on time is always possible
      if (bound == max) {
        for (int i = 0; i < n; i++) {
          IntVar s = starts[i];
          if (durations[i] == 0 && s.min() <= lastOnTime(i) && s.max() > lastOnTime(i)) {
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
        if (kept[k]) {
          // taken on time by the bound: forcing it late adds one
          if (bound == max && sure + 1 + lateOf(origin, k, false) > max) {
            s.domain.inMax(store.level, s, (int) lastOnTime(i));
          }
        } else {
          // late in the bound: forcing it on time can only raise it
          if (sure + (long) lateOf(origin, k, true) > max) {
            if (lastOnTime(i) >= IntDomain.MAX_INT) {
              throw Store.failException;
            }
            s.domain.inMin(store.level, s, (int) (lastOnTime(i) + 1));
          }
        }
      }
      // also after a change of late, which may be one of the starts
      again = boundsSum() != before;
    } while (again);
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
      if (starts[order[l]].min() == t) {
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
      eff[k] = Math.max(0, durations[i] - Math.max(0, origin - starts[i].min()));
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

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public boolean satisfied() {
    int count = 0;
    for (IntVar s : starts) {
      if (!s.singleton()) {
        return false;
      }
    }
    for (int i = 0; i < n; i++) {
      if (starts[i].value() > lastOnTime(i)) {
        count++;
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
    result.append(")");

    return result.toString();
  }

  @Override
  public LateCount copy(VarMap map) {
    return new LateCount(map.get(starts), durations, dues, map.get(late), releases);
  }
}
