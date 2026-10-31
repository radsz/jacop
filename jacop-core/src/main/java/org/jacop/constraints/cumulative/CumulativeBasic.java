/*
 * CumulativeBasic.java
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

package org.jacop.constraints.cumulative;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;
import java.util.function.ToIntFunction;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.Copyable;
import org.jacop.api.Simplifiable;
import org.jacop.api.VarMap;
import org.jacop.api.Violation;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;

/**
 * CumulativeBasic implements the cumulative constraint using time tabling algorithm.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class CumulativeBasic extends Constraint
    implements Simplifiable, Copyable<CumulativeBasic>, Explainable, Violation, PbEncodable {

  private static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final boolean DEBUG = false;
  private static final boolean DEBUG_NARR = false;
  // event type
  protected static final int PROFILE = 0;
  protected static final int PRUNE_START = 1;
  protected static final int PRUNE_END = 2;

  /** It specifies the limit of the PROFILE of cumulative use of resources. */
  protected final IntVar limit;

  /*
   * All tasks of the constraint
   */
  final TaskView[] taskNormal;

  private final TimetableSweep sweep = new TimetableSweep();

  /**
   * It specifies whether there possibly exist tasks that have duration or resource variable min
   * value equal zero.
   */
  boolean possibleZeroTasks;

  CumulativePrimary cumulativeForConstants;

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public CumulativeBasic(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit) {

    checkInputForNullness(
        new String[] {"starts", "durations", "resources", "limit"},
        starts,
        durations,
        resources,
        new Object[] {limit});
    checkInput(durations, i -> i.min() >= 0, "durations cannot allow negative values");
    checkInput(resources, i -> i.min() >= 0, "resources cannot allow negative values");

    if (starts.length != durations.length) {
      throw new IllegalArgumentException(
          "Cumulative constraint needs to have starts and durations lists the same length.");
    }
    if (starts.length != resources.length) {
      throw new IllegalArgumentException(
          "Cumulative constraint needs to have starts and resources lists the same length.");
    }

    if (limit.min() >= 0) {
      this.limit = limit;
    } else {
      throw new IllegalArgumentException("\nResource limit must be >= 0 in cumulative");
    }

    this.queueIndex = 2;
    this.numberId = idNumber.incrementAndGet();
    this.taskNormal = new TaskNormalView[starts.length];

    for (int i = 0; i < starts.length; i++) {
      taskNormal[i] = new TaskNormalView(starts[i], durations[i], resources[i]);
      taskNormal[i].index = i;
      if (durations[i].min() == 0 || resources[i].min() == 0) {
        possibleZeroTasks = true;
      }
    }

    if (grounded(durations) && grounded(resources)) {
      int[] durInt = new int[durations.length];
      for (int i = 0; i < durations.length; i++) {
        durInt[i] = durations[i].value();
      }
      int[] resInt = new int[resources.length];
      for (int i = 0; i < resources.length; i++) {
        resInt[i] = resources[i].value();
      }

      cumulativeForConstants = new CumulativePrimary(starts, durInt, resInt, limit);
    }

    setScope(
        Stream.concat(
            Stream.concat(Arrays.stream(starts), Arrays.stream(durations)),
            Stream.concat(Arrays.stream(resources), Stream.of(limit))));
  }

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public CumulativeBasic(
      List<? extends IntVar> starts,
      List<? extends IntVar> durations,
      List<? extends IntVar> resources,
      IntVar limit) {

    this(
        starts.toArray(IntVar[]::new),
        durations.toArray(IntVar[]::new),
        resources.toArray(IntVar[]::new),
        limit);
  }

  /**
   * It imposes the constraint; a constraint without tasks is always satisfied, since the limit is
   * not negative, so it is not imposed.
   *
   * @param store the constraint store in which the constraint is imposed.
   */
  @Override
  public void impose(Store store) {
    if (taskNormal.length == 0) {
      return;
    }
    super.impose(store);
  }

  @Override
  public void consistency(Store store) {

    do {

      store.propagationHasOccurred = false;
      profileProp(store);

    } while (store.propagationHasOccurred);
  }

  void profileProp(Store store) {

    if (cumulativeForConstants == null) {
      sweepPruning(store);
    } else {
      cumulativeForConstants.sweepPruning(store);
    }
    updateTasksRes(store);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  private void updateTasksRes(Store store) {
    int limitMax = limit.max();
    for (TaskView t : taskNormal) {
      // a task with zero duration does not use the resource, so it may use more than the limit
      if (t.dur.min() > 0) {
        t.res.domain.inMax(store.level, t.res, limitMax);
      } else if (t.res.min() > limitMax) {
        t.dur.domain.inMax(store.level, t.dur, 0);
      }
    }
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : cumulativeBasic([ ");
    for (int i = 0; i < taskNormal.length - 1; i++) {
      result.append(taskNormal[i]).append(", ");
    }

    result.append(taskNormal[taskNormal.length - 1]);

    result.append(" ]").append(", limit = ").append(limit).append(" )");

    return result.toString();
  }

  // Sweep algorithm for PROFILE
  private void sweepPruning(Store store) {
    sweep.prune(store, taskNormal, limit, DEBUG, DEBUG_NARR, null, null);
  }

  /**
   * Returns the counterparts of the variables of the tasks in the order the tasks were given.
   *
   * @param map the counterparts of the variables of this constraint.
   * @return the starts, the durations and the resources.
   */
  IntVar[][] taskVariables(VarMap map) {
    int n = taskNormal.length;
    IntVar[][] vars = new IntVar[3][n];
    // the array keeps the order of the tasks; their index field is reused by propagation
    for (int i = 0; i < n; i++) {
      vars[0][i] = map.get(taskNormal[i].start);
      vars[1][i] = map.get(taskNormal[i].dur);
      vars[2][i] = map.get(taskNormal[i].res);
    }
    return vars;
  }

  /**
   * Returns the variables of the tasks in the order the tasks were given.
   *
   * @return the starts, the durations and the resources, one array each.
   */
  public IntVar[][] tasks() {
    int n = taskNormal.length;
    IntVar[][] vars = new IntVar[3][n];
    for (int i = 0; i < n; i++) {
      vars[0][i] = taskNormal[i].start;
      vars[1][i] = taskNormal[i].dur;
      vars[2][i] = taskNormal[i].res;
    }
    return vars;
  }

  /**
   * Returns the limit of the resource.
   *
   * @return the limit.
   */
  public IntVar limit() {
    return limit;
  }

  /**
   * Returns a constraint of the same class, with the same options and limit, over the tasks kept.
   *
   * @param kept for each task, in the order the tasks were given, whether it is kept.
   * @return the constraint, or null for a subclass that cannot drop tasks.
   */
  public CumulativeBasic restrict(boolean[] kept) {
    IntVar[][] t = tasks();
    int n = 0;
    for (boolean k : kept) {
      if (k) {
        n++;
      }
    }
    IntVar[][] r = new IntVar[3][n];
    for (int i = 0, j = 0; i < kept.length; i++) {
      if (kept[i]) {
        r[0][j] = t[0][i];
        r[1][j] = t[1][i];
        r[2][j] = t[2][i];
        j++;
      }
    }
    return withTasks(r[0], r[1], r[2]);
  }

  /**
   * Returns a constraint of the same class and options as this one over other tasks.
   *
   * @param s the starts.
   * @param d the durations.
   * @param r the resources.
   * @return the constraint, or null for a subclass that does not override this method.
   */
  CumulativeBasic withTasks(IntVar[] s, IntVar[] d, IntVar[] r) {
    return getClass() == CumulativeBasic.class ? new CumulativeBasic(s, d, r, limit) : null;
  }

  /**
   * Leaves out the tasks that never use the resource: those with no resource use, and those with no
   * duration whose use fits under the limit. If the uses of all tasks fit under the limit together,
   * the constraint holds.
   *
   * @param factory builds a constraint of the class being simplified from starts, durations and
   *     resources (in this order).
   * @return the replacing constraints, as {@link Simplifiable#simplify()}.
   */
  Optional<List<Constraint>> simplifyTasks(Function<IntVar[][], Constraint> factory) {
    int n = taskNormal.length;
    List<TaskView> kept = new ArrayList<>(n);
    long total = 0;
    for (TaskView t : taskNormal) {
      // a task with no resource use, or no duration and a use under the limit, uses nothing
      boolean usesResource = t.res.max() > 0 && (t.dur.max() > 0 || t.res.max() > limit.min());
      if (usesResource) {
        kept.add(t);
        total += t.res.max();
      }
    }
    if (total <= limit.min()) {
      return Optional.of(List.of());
    }
    if (kept.size() == n) {
      return Optional.empty();
    }
    IntVar[][] vars = new IntVar[3][kept.size()];
    for (int i = 0; i < kept.size(); i++) {
      vars[0][i] = kept.get(i).start;
      vars[1][i] = kept.get(i).dur;
      vars[2][i] = kept.get(i).res;
    }
    return Optional.of(List.of(factory.apply(vars)));
  }

  @Override
  public Optional<List<Constraint>> simplify() {
    if (getClass() != CumulativeBasic.class) {
      return Optional.empty();
    }
    return simplifyTasks(t -> new CumulativeBasic(t[0], t[1], t[2], limit));
  }

  @Override
  public CumulativeBasic copy(VarMap map) {
    IntVar[][] t = taskVariables(map);
    return new CumulativeBasic(t[0], t[1], t[2], map.get(limit));
  }

  /**
   * Writes the time-indexed encoding: a literal [s <= t < s + d] for each task and each time point
   * t it may cover, equal to [s >= t - d + 1] - [s >= t + 1], and at each time point the resource
   * uses of the tasks covering it summed to at most the limit. Unit propagation over it is the time
   * table, which every explanation of this class states. Only tasks of fixed duration and resource
   * use are encoded; the subclasses, whose rules unit propagation does not reach, are not.
   */
  @Override
  public boolean encode(PbModel model) {
    if (getClass() != CumulativeBasic.class) {
      return false;
    }
    // time point -> the literals of the tasks that may cover it, and their resource uses
    TreeMap<Integer, List<String>> covering = new TreeMap<>();
    Map<Integer, List<Long>> uses = new HashMap<>();
    for (TaskView task : taskNormal) {
      IntDomain dd = model.domain(task.dur);
      IntDomain rd = model.domain(task.res);
      if (!dd.singleton() || !rd.singleton()) {
        return false;
      }
      int d = dd.value();
      int r = rd.value();
      if (d == 0 || r == 0) {
        continue;
      }
      IntDomain sd = model.domain(task.start);
      for (long t = sd.min(); t <= (long) sd.max() + d - 1; t++) {
        String from = model.atLeast(task.start, (int) (t - d + 1));
        String after = model.atLeast(task.start, (int) (t + 1));
        String covers;
        if ("0".equals(from) || "1".equals(after)) {
          continue;
        } else if ("0".equals(after)) {
          covers = from;
        } else if ("1".equals(from)) {
          covers = PbModel.not(after);
        } else {
          covers = model.auxiliary();
          model.sum(
              new String[] {covers, from, after},
              new long[] {1, -1, 1},
              new IntVar[0],
              new long[0],
              LinearForm.EQ,
              0);
        }
        covering.computeIfAbsent((int) t, k -> new ArrayList<>()).add(covers);
        uses.computeIfAbsent((int) t, k -> new ArrayList<>()).add((long) r);
      }
    }
    IntVar[] cap = {limit};
    long[] minus = {-1};
    for (var e : covering.entrySet()) {
      List<String> l = e.getValue();
      long[] a = uses.get(e.getKey()).stream().mapToLong(Long::longValue).toArray();
      model.sum(l.toArray(new String[0]), a, cap, minus, LinearForm.LE, 0);
    }
    return true;
  }

  /**
   * Explains a bound of a start time by the time table: each start value it removed overlaps a time
   * point where the compulsory parts of other tasks leave too little capacity, or a time window
   * where the tasks need more energy than the limit gives. Durations and resource uses count at
   * their smallest values and the limit at its largest, each with its bound in the reason.
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    int kind = trail.kind(entry);
    if (!explainable()) {
      return false;
    }
    snapshot(trail, entry);
    IntVar y = trail.variable(entry);
    int j = -1;
    for (int i = 0; i < taskNormal.length; i++) {
      if (taskNormal[i].start == y) {
        if (j >= 0) {
          return false;
        }
        j = i;
      }
    }
    if (j < 0) {
      if (y == limit) {
        return kind == AtomicTrail.GE && explainLimit(trail, entry, out);
      }
      return kind == AtomicTrail.LE && explainUseBound(trail, entry, y, out);
    }
    TaskView own = taskNormal[j];
    int d = dmin(entry, own);
    int r = rmin(entry, own);
    if (d <= 0 || r <= 0) {
      return false;
    }
    trail.addLowerBound(own.dur, entry, out);
    trail.addLowerBound(own.res, entry, out);
    int room = limitMax - r;
    int v = trail.value(entry);
    if (kind == AtomicTrail.NE) {
      int t = firstOverloaded(trail, entry, j, v, v + d - 1, room);
      if (t != NONE) {
        overloaded(trail, entry, j, t, room, out);
        return true;
      }
      int[] window = overloadedWindow(trail, entry, j, v);
      if (window != null) {
        addWindowReason(trail, entry, j, window, v, v, out);
        return true;
      }
      int[] pair = pairConflict(entry, j, v, d, room);
      if (pair == null) {
        return false;
      }
      addPairReason(trail, entry, j, pair, room, out);
      return true;
    } else if (kind == AtomicTrail.GE) {
      trail.addLowerBound(y, entry, out);
      return explainStartsBelow(trail, entry, j, trail.minBefore(y, entry), v, d, room, out);
    } else {
      trail.addUpperBound(y, entry, out);
      int u = trail.maxBefore(y, entry);
      while (u > v) {
        int t = firstOverloaded(trail, entry, j, u, u + d - 1, room);
        if (t != NONE) {
          int lo = Math.max(v + 1, t - d + 1);
          if (pointBeforeHoles(trail, entry, j, lo, u, t, room)) {
            overloaded(trail, entry, j, t, room, out);
          } else {
            for (int x = lo; x <= u; x++) {
              trail.excludedBefore(y, x, entry, out);
            }
          }
          u = t - d;
          continue;
        }
        if (trail.excludedBefore(y, u, entry, out)) {
          u--;
          continue;
        }
        if (t != NONE) {
          overloaded(trail, entry, j, t, room, out);
          u = t - d;
          continue;
        }
        int[] window = overloadedWindow(trail, entry, j, u);
        if (window != null) {
          int next = windowRight(trail, entry, j, u, v, window);
          addWindowReason(trail, entry, j, window, next + 1, u, out);
          u = next;
          continue;
        }
        int[] pair = pairConflict(entry, j, u, d, room);
        if (pair == null) {
          return false;
        }
        addPairReason(trail, entry, j, pair, room, out);
        // every start from p2 - d + 1 up to u covers both points
        u = pair[2] - d;
      }
    }
    return true;
  }

  /**
   * Explains a failure by a time point where the compulsory parts exceed the limit, or else by a
   * time window where the tasks need more energy than the limit gives.
   */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (!explainable()) {
      return false;
    }
    int position = trail.size();
    snapshot(trail, position);
    int room = limitMax;
    // the load rises only where a compulsory part begins, so an overload shows at such a point
    for (TaskView task : taskNormal) {
      int t = lst(task);
      if (t < est(task) + dmin(position, task) && overloaded(trail, position, -1, t, room, null)) {
        overloaded(trail, position, -1, t, room, out);
        return true;
      }
    }
    if (explainNoStartLeft(trail, position, out)) {
      return true;
    }
    int[] window = overloadedWindow(trail, position, -1, 0);
    if (window != null) {
      addWindowReason(trail, position, -1, window, 0, 0, out);
      return true;
    }
    return false;
  }

  /**
   * The most task overlaps one explanation weighs in windows before it leaves the atom to the
   * generic reason.
   */
  private static final int WINDOW_BUDGET = 1 << 22;

  // the bounds of the tasks and the limit's maximum just before the position being explained
  private TaskView[] snapshotTasks;
  private IdentityHashMap<TaskView, Integer> taskSlot;
  private int[] snapshotEst;
  private int[] snapshotLst;
  private int[] snapshotDur;
  private int[] snapshotRes;
  private int limitMax;
  private int snapshotPosition = -1;
  private int windowBudget;

  // the explanations hold for the relation of every task present, using the smallest durations
  // and resource uses and the largest limit; CumulativeOptional and other subclasses with another
  // relation use the generic reason
  private boolean explainable() {
    Class<?> type = getClass();
    return type == CumulativeBasic.class
        || type == Cumulative.class
        || type == CumulativeUnary.class;
  }

  /**
   * Tells whether the compulsory parts of the tasks other than {@code skip}, just before a trail
   * position, use more than {@code room} at time t; with {@code out}, adds the bounds of the
   * largest of those tasks until they exceed it.
   */
  private boolean overloaded(
      AtomicTrail trail, int position, int skip, int t, int room, EntryList out) {
    return overloaded(trail, position, skip, -1, t, room, out);
  }

  // as above, leaving out the tasks skip and skip2
  private boolean overloaded(
      AtomicTrail trail, int position, int skip, int skip2, int t, long room, EntryList out) {
    long load = 0;
    for (int i = 0; i < taskNormal.length; i++) {
      TaskView task = taskNormal[i];
      if (i != skip && i != skip2 && covers(trail, position, task, t)) {
        load += rmin(position, task);
      }
    }
    if (load <= room || out == null) {
      return load > room;
    }
    Integer[] order = new Integer[taskNormal.length];
    for (int i = 0; i < order.length; i++) {
      order[i] = i;
    }
    Arrays.sort(
        order,
        (a, b) -> Integer.compare(rmin(position, taskNormal[b]), rmin(position, taskNormal[a])));
    trail.addUpperBound(limit, position, out);
    long sum = 0;
    for (int i : order) {
      if (sum > room) {
        break;
      }
      TaskView task = taskNormal[i];
      if (i != skip && i != skip2 && covers(trail, position, task, t)) {
        addTaskReasonAt(trail, position, task, t, out);
        sum += rmin(position, task);
      }
    }
    return true;
  }

  /**
   * Explains a failure of the time table on a task whose start lost all its values: none of its
   * starts from the earliest to the latest is possible.
   */
  private boolean explainNoStartLeft(AtomicTrail trail, int position, EntryList out) {
    // the sweep that ran is that of the constraint over constant tasks when there is one
    IntVar failed =
        cumulativeForConstants == null ? sweep.noStartLeft : cumulativeForConstants.noStartLeft;
    if (failed == null) {
      return false;
    }
    int j = -1;
    for (int i = 0; i < taskNormal.length; i++) {
      if (taskNormal[i].start == failed) {
        if (j >= 0) {
          return false;
        }
        j = i;
      }
    }
    if (j < 0) {
      return false;
    }
    TaskView own = taskNormal[j];
    int d = dmin(position, own);
    int r = rmin(position, own);
    if (d <= 0 || r <= 0) {
      return false;
    }
    int mark = out.size();
    trail.addLowerBound(own.dur, position, out);
    trail.addLowerBound(own.res, position, out);
    trail.addLowerBound(own.start, position, out);
    trail.addUpperBound(own.start, position, out);
    if (explainStartsBelow(trail, position, j, est(own), lst(own) + 1, d, limitMax - r, out)) {
      return true;
    }
    out.truncate(mark);
    return false;
  }

  /**
   * Explains why task j, just before a trail position, starts at none of [u, v): each such start is
   * out of its domain already, or the task started there overlaps a time point where the others'
   * compulsory parts leave less than its resource use (room is the limit less that use), or a
   * window that then needs more energy than the limit gives.
   */
  private boolean explainStartsBelow(
      AtomicTrail trail, int entry, int j, int u, int v, int d, int room, EntryList out) {
    IntVar y = taskNormal[j].start;
    while (u < v) {
      int t = lastOverloaded(trail, entry, j, u, u + d - 1, room);
      if (t != NONE) {
        int hi = Math.min(v - 1, t);
        if (pointBeforeHoles(trail, entry, j, u, hi, t, room)) {
          overloaded(trail, entry, j, t, room, out);
        } else {
          for (int x = u; x <= hi; x++) {
            trail.excludedBefore(y, x, entry, out);
          }
        }
        u = t + 1;
        continue;
      }
      if (trail.excludedBefore(y, u, entry, out)) {
        u++;
        continue;
      }
      if (t != NONE) {
        overloaded(trail, entry, j, t, room, out);
        u = t + 1;
        continue;
      }
      int[] window = overloadedWindow(trail, entry, j, u);
      if (window != null) {
        int next = windowLeft(trail, entry, j, u, v, window);
        addWindowReason(trail, entry, j, window, u, next - 1, out);
        u = next;
        continue;
      }
      int[] pair = pairConflict(entry, j, u, d, room);
      if (pair == null) {
        return false;
      }
      addPairReason(trail, entry, j, pair, room, out);
      // every start from u up to p1 covers both points
      u = pair[1] + 1;
    }
    return true;
  }

  // explains starts by pairs of tasks that cannot overlap where the time table leaves too little
  // room, unless -Djacop.lcg.cumulativePairs=false
  private static final boolean PAIRS =
      !"false".equals(System.getProperty("jacop.lcg.cumulativePairs"));

  /**
   * Finds a task i that task j, started at u, cannot leave room for, as time-table disjunctive
   * reasoning does (Gay, Hartert and Schaus, CPAIOR 2015): every start of i in [p1 - d_i + 1, p2]
   * overlaps [p1, p2], task j started at u covers [p1, p2], and the compulsory parts of the tasks
   * other than i and j leave less than r_i + r_j at p1 and p2 when p2 - p1 is at most d_i (i then
   * covers one of them), at every point of [p1, p2] otherwise. Returns {i, p1, p2}, or null. Room
   * is the limit less j's resource use.
   */
  private int[] pairConflict(int position, int j, int u, int d, int room) {
    if (!PAIRS) {
      return null;
    }
    int[] best = null;
    int bestReach = 0;
    for (int i = 0; i < taskNormal.length; i++) {
      TaskView task = taskNormal[i];
      int di = dmin(position, task);
      int ri = rmin(position, task);
      int est = est(task);
      int lst = lst(task);
      if (i == j || di <= 0 || ri <= 0 || est == lst) {
        continue;
      }
      int ect = est + di;
      // the points every start of i in [est, lst] covers one of: around its compulsory part, or
      // its earliest end and its latest start
      int p1 = lst < ect ? lst - 1 : ect - 1;
      int p2 = lst < ect ? ect : lst;
      if (u > p1 || (long) u + d <= p2) {
        continue;
      }
      long left = (long) room - ri;
      if (p2 - p1 <= di
          ? !overloaded(null, position, j, i, p1, left, null)
              || !overloaded(null, position, j, i, p2, left, null)
          : !overloadedThrough(position, j, i, p1, p2, left)) {
        continue;
      }
      // prefer the pair that rules out the most starts of j next to u
      int reach = Math.min(p1 - u, u + d - 1 - p2);
      if (best == null || reach > bestReach) {
        best = new int[] {i, p1, p2};
        bestReach = reach;
      }
    }
    return best;
  }

  /**
   * Adds the reason of a pair found by {@link #pairConflict}: the bounds that keep every start of i
   * on p1 or p2, its smallest duration and resource use, and the compulsory parts at both points.
   */
  private void addPairReason(
      AtomicTrail trail, int position, int j, int[] pair, int room, EntryList out) {
    TaskView task = taskNormal[pair[0]];
    int di = dmin(position, task);
    trail.addBoundReaching(task.start, position, true, (long) pair[1] - di + 1, out);
    trail.addBoundReaching(task.start, position, false, pair[2], out);
    trail.addLowerBound(task.dur, position, out);
    trail.addLowerBound(task.res, position, out);
    long left = (long) room - rmin(position, task);
    if (pair[2] - pair[1] <= di) {
      overloaded(trail, position, j, pair[0], pair[1], left, out);
      overloaded(trail, position, j, pair[0], pair[2], left, out);
    } else {
      addLoadThrough(trail, position, j, pair[0], pair[1], pair[2], left, out);
    }
  }

  /**
   * Tells whether the compulsory parts of the tasks other than skip and skip2 use more than room at
   * every point of [a, b]. The load falls only where a compulsory part ends, so it is lowest at a
   * or at such an end.
   */
  private boolean overloadedThrough(int position, int skip, int skip2, int a, int b, long room) {
    if (!overloaded(null, position, skip, skip2, a, room, null)) {
      return false;
    }
    for (int i = 0; i < taskNormal.length; i++) {
      TaskView task = taskNormal[i];
      int end = est(task) + dmin(position, task);
      if (i != skip
          && i != skip2
          && a < end
          && end <= b
          && lst(task) < end
          && !overloaded(null, position, skip, skip2, end, room, null)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Adds what makes the compulsory parts of the tasks other than skip and skip2 use more than room
   * at every point of [a, b] (see {@link #overloadedThrough}), segment by segment: at the first
   * point of a segment the largest tasks covering it until they exceed room, each with the bounds
   * that keep its compulsory part over the segment, which ends where the first of them ends.
   */
  private void addLoadThrough(
      AtomicTrail trail,
      int position,
      int skip,
      int skip2,
      int a,
      int b,
      long room,
      EntryList out) {
    trail.addUpperBound(limit, position, out);
    Integer[] order = new Integer[taskNormal.length];
    for (int i = 0; i < order.length; i++) {
      order[i] = i;
    }
    Arrays.sort(
        order,
        (x, y) -> Integer.compare(rmin(position, taskNormal[y]), rmin(position, taskNormal[x])));
    int t = a;
    while (t <= b && room >= 0) {
      long sum = 0;
      int end = b;
      int first = -1;
      int count = 0;
      for (int k = 0; k < order.length && sum <= room; k++) {
        int i = order[k];
        TaskView task = taskNormal[i];
        if (i != skip && i != skip2 && covers(trail, position, task, t)) {
          sum += rmin(position, task);
          end = Math.min(end, est(task) + dmin(position, task) - 1);
          if (first < 0) {
            first = k;
          }
          count = k + 1;
        }
      }
      for (int k = first; k >= 0 && k < count; k++) {
        int i = order[k];
        TaskView task = taskNormal[i];
        if (i != skip && i != skip2 && covers(trail, position, task, t)) {
          trail.addBoundReaching(task.start, position, false, t, out);
          trail.addBoundReaching(
              task.start, position, true, (long) end - dmin(position, task) + 1, out);
          trail.addLowerBound(task.dur, position, out);
          trail.addLowerBound(task.res, position, out);
        }
      }
      t = end + 1;
    }
  }

  /**
   * Tells whether the starts lo..hi of task j, which a time-table point t rules out, are better
   * explained by that point than one by one: some of them are still in the domain (so the point is
   * needed anyway), or the point cites fewer entries than the removals of all of them do. A walk
   * over a start range with many holes otherwise cites one removal per hole.
   */
  private boolean pointBeforeHoles(
      AtomicTrail trail, int entry, int j, int lo, int hi, int t, int room) {
    IntVar y = taskNormal[j].start;
    if ((long) hi - lo > HOLE_SCAN) {
      return true;
    }
    holeScratch.clear();
    for (int x = lo; x <= hi; x++) {
      if (!trail.excludedBefore(y, x, entry, holeScratch)) {
        return true;
      }
    }
    holeScratch.sortUnique(0);
    int holes = holeScratch.size();
    holeScratch.clear();
    overloaded(trail, entry, j, t, room, holeScratch);
    holeScratch.sortUnique(0);
    return holeScratch.size() < holes;
  }

  /** The most starts {@link #pointBeforeHoles} checks one by one. */
  private static final int HOLE_SCAN = 256;

  private final EntryList holeScratch = new EntryList();

  /** No such time point. */
  private static final int NONE = Integer.MIN_VALUE;

  /**
   * The first time point in [a, b] where the compulsory parts of the tasks other than skip use more
   * than room, or {@link #NONE}. The load rises only where a compulsory part begins, so the point
   * is a or the latest start of a task.
   */
  private int firstOverloaded(AtomicTrail trail, int position, int skip, int a, int b, int room) {
    int best = NONE;
    if (a > b || overloaded(trail, position, skip, a, room, null)) {
      return a > b ? NONE : a;
    }
    for (int i = 0; i < taskNormal.length; i++) {
      TaskView task = taskNormal[i];
      int t = lst(task);
      if (i != skip
          && a < t
          && t <= b
          && (best == NONE || t < best)
          && t < est(task) + dmin(position, task)
          && overloaded(trail, position, skip, t, room, null)) {
        best = t;
      }
    }
    return best;
  }

  /**
   * The last time point in [a, b] where the compulsory parts of the tasks other than skip use more
   * than room, or {@link #NONE}. The load falls only after a compulsory part ends, so the point is
   * b or the last time point of the compulsory part of a task.
   */
  private int lastOverloaded(AtomicTrail trail, int position, int skip, int a, int b, int room) {
    int best = NONE;
    if (a > b || overloaded(trail, position, skip, b, room, null)) {
      return a > b ? NONE : b;
    }
    for (int i = 0; i < taskNormal.length; i++) {
      TaskView task = taskNormal[i];
      int t = est(task) + dmin(position, task) - 1;
      if (i != skip
          && a <= t
          && t < b
          && t > best
          && lst(task) <= t
          && overloaded(trail, position, skip, t, room, null)) {
        best = t;
      }
    }
    return best;
  }

  /**
   * The first start in (u, v] of task j at which the window no longer needs more energy than the
   * limit gives, or v. Only task j's overlap with the window depends on its start, and that overlap
   * rises, stays and falls as the start grows, so the starts with an excess form an interval: those
   * after u are found by bisection.
   */
  private int windowLeft(AtomicTrail trail, int position, int j, int u, int v, int[] window) {
    int lo = u; // has an excess
    int hi = v; // the answer when every start up to v has one
    while (hi - lo > 1) {
      int mid = (int) (((long) lo + hi) >>> 1);
      if (windowExcess(trail, position, j, mid, window[0], window[1]) > 0) {
        lo = mid;
      } else {
        hi = mid;
      }
    }
    return hi;
  }

  /** As {@link #windowLeft}, downwards: the last start in [v, u) without an excess, or v. */
  private int windowRight(AtomicTrail trail, int position, int j, int u, int v, int[] window) {
    int hi = u;
    int lo = v;
    while (hi - lo > 1) {
      int mid = (int) (((long) lo + hi) >>> 1);
      if (windowExcess(trail, position, j, mid, window[0], window[1]) > 0) {
        hi = mid;
      } else {
        lo = mid;
      }
    }
    return lo;
  }

  /**
   * Finds a time window [a, b) where the tasks other than j, with task j started at u (when j is
   * not -1), need more energy than the limit gives over the window, just before a trail position:
   * each task needs at least its smallest overlap with the window over its start range. Returns the
   * window of the largest excess, or null.
   *
   * <p>For a window start a, the smallest overlap of a task with [a, b) is 0 up to b = max(lst, a),
   * then grows by one per time unit up to min(d, ect - a), so the need of all tasks is piecewise
   * linear in b and one sweep over these breakpoints weighs every window end. Window starts are the
   * earliest starts of the tasks.
   */
  private int[] overloadedWindow(AtomicTrail trail, int position, int j, int u) {
    int n = taskNormal.length;
    int[] from = new int[n + 1];
    int nf = 0;
    for (int i = 0; i < n; i++) {
      if (i != j) {
        from[nf++] = est(taskNormal[i]);
      }
    }
    if (j >= 0) {
      from[nf++] = u;
    }
    Arrays.sort(from, 0, nf);
    long[] events = new long[2 * n];
    int[] best = null;
    long bestExcess = 0;
    for (int f = 0; f < nf; f++) {
      int a = from[f];
      if (f > 0 && a == from[f - 1]) {
        continue;
      }
      windowBudget -= n;
      if (windowBudget < 0) {
        return null;
      }
      int ne = 0;
      for (int i = 0; i < n; i++) {
        TaskView task = taskNormal[i];
        long r = rmin(position, task);
        int d = dmin(position, task);
        int est = i == j ? u : est(task);
        int lst = i == j ? u : lst(task);
        long rise = Math.max((long) lst, a);
        long length = Math.min(d, (long) est + d - a);
        if (r > 0 && length > 0) {
          events[ne++] = rise << 32 | i;
          events[ne++] = (rise + length) << 32 | i | 1L << 31;
        }
      }
      Arrays.sort(events, 0, ne);
      long need = 0;
      long slope = 0;
      long at = a;
      for (int k = 0; k < ne; k++) {
        long b = events[k] >> 32;
        need += slope * (b - at);
        at = b;
        long excess = need - (long) limitMax * (b - a);
        if (b > a && excess > bestExcess && b <= Integer.MAX_VALUE) {
          bestExcess = excess;
          best = new int[] {a, (int) b};
        }
        long r = rmin(position, taskNormal[(int) (events[k] & 0x7fffffffL)]);
        slope += (events[k] & 1L << 31) == 0 ? r : -r;
      }
    }
    return best;
  }

  /** The energy the tasks need in [a, b) beyond what the limit gives (see overloadedWindow). */
  private long windowExcess(AtomicTrail trail, int position, int j, int u, int a, int b) {
    long need = 0;
    for (int i = 0; i < taskNormal.length; i++) {
      TaskView task = taskNormal[i];
      int d = dmin(position, task);
      long r = rmin(position, task);
      if (i == j) {
        need += r * overlap(u, d, a, b);
      } else {
        int est = est(task);
        int lst = lst(task);
        need += r * Math.min(overlap(est, d, a, b), overlap(lst, d, a, b));
      }
    }
    return need - (long) limitMax * (b - a);
  }

  private static int overlap(int start, int d, int a, int b) {
    return Math.max(0, Math.min(start + d, b) - Math.max(start, a));
  }

  /**
   * Explains a lower bound of the limit by the time point where the compulsory parts use the most,
   * with the values between that use and the bound already out of the limit's domain.
   */
  private boolean explainLimit(AtomicTrail trail, int entry, EntryList out) {
    int v = trail.value(entry);
    int best = Integer.MIN_VALUE;
    long bestLoad = -1;
    for (TaskView task : taskNormal) {
      int t = lst(task);
      long load = 0;
      for (TaskView other : taskNormal) {
        if (covers(trail, entry, other, t)) {
          load += rmin(entry, other);
        }
      }
      if (load > bestLoad) {
        bestLoad = load;
        best = t;
      }
    }
    long from = Math.max(bestLoad, trail.minBefore(limit, entry));
    if (v - from > 1024) {
      return false; // too many values to check one by one
    }
    int mark = out.size();
    for (long u = from; u < v; u++) {
      if (!trail.excludedBefore(limit, (int) u, entry, out)) {
        out.truncate(mark);
        return false;
      }
    }
    if (bestLoad > trail.minBefore(limit, entry)) {
      for (TaskView task : taskNormal) {
        if (covers(trail, entry, task, best) && rmin(entry, task) > 0) {
          addTaskReasonAt(trail, entry, task, best, out);
        }
      }
    } else {
      trail.addLowerBound(limit, entry, out);
    }
    return true;
  }

  /**
   * Explains an upper bound w of a task's duration or resource use. A duration of w + 1 would make
   * the task, from its latest start up to its earliest start plus w, cover a time point where the
   * compulsory parts of the other tasks leave too little; or, failing one such point, every start
   * of the task would then be ruled out as {@link #explainStartsBelow} rules out starts. One more
   * unit of resource would exceed the limit at a point of the task's compulsory part, or the limit
   * itself. Values just above the bound already out of the domain widen it: the propagator bounds
   * the variable by the largest value it allows, which the domain may round down.
   */
  private boolean explainUseBound(AtomicTrail trail, int entry, IntVar y, EntryList out) {
    int mark = out.size();
    int w = trail.value(entry);
    for (int v = w; v - w <= USE_BOUND_HOLES; v++) {
      int before = out.size();
      if (explainUseBoundAt(trail, entry, y, v, out)) {
        return true;
      }
      out.truncate(before);
      if (v == Integer.MAX_VALUE || !trail.excludedBefore(y, v + 1, entry, out)) {
        break;
      }
      if (v + 1 > trail.maxBefore(y, entry)) {
        // every value above w was out already
        return true;
      }
    }
    out.truncate(mark);
    return false;
  }

  /** The most values out of the domain above a bound that {@link #explainUseBound} looks past. */
  private static final int USE_BOUND_HOLES = 64;

  private boolean explainUseBoundAt(AtomicTrail trail, int entry, IntVar y, int w, EntryList out) {
    for (int i = 0; i < taskNormal.length; i++) {
      TaskView task = taskNormal[i];
      if (task.dur == y && task.res != y) {
        int r = rmin(entry, task);
        if (r > 0 && explainDurationBound(trail, entry, i, w, limitMax - r, out)) {
          return true;
        }
      } else if (task.res == y && task.dur != y) {
        int d = dmin(entry, task);
        if (d <= 0) {
          continue;
        }
        if (w >= limitMax) {
          trail.addLowerBound(task.dur, entry, out);
          trail.addBoundReaching(limit, entry, false, w, out);
          return true;
        }
        int t = firstOverloaded(trail, entry, i, lst(task), est(task) + d - 1, limitMax - w - 1);
        if (t != NONE) {
          addTaskReasonAt(trail, entry, task, t, out);
          overloaded(trail, entry, i, t, limitMax - w - 1, out);
          return true;
        }
      }
    }
    return false;
  }

  // explains that task i, with a duration above w, has no start left (see explainUseBound)
  private boolean explainDurationBound(
      AtomicTrail trail, int entry, int i, int w, int room, EntryList out) {
    TaskView task = taskNormal[i];
    int mark = out.size();
    trail.addLowerBound(task.res, entry, out);
    int t = firstOverloaded(trail, entry, i, lst(task), est(task) + w, room);
    if (t != NONE) {
      trail.addBoundReaching(task.start, entry, true, (long) t - w, out);
      trail.addBoundReaching(task.start, entry, false, t, out);
      overloaded(trail, entry, i, t, room, out);
      return true;
    }
    trail.addLowerBound(task.start, entry, out);
    trail.addUpperBound(task.start, entry, out);
    if (w < Integer.MAX_VALUE - 1
        && explainStartsBelow(trail, entry, i, est(task), lst(task) + 1, w + 1, room, out)) {
      return true;
    }
    out.truncate(mark);
    return false;
  }

  // window reasons keep only the energy the excess needs, unless -Djacop.lcg.windowLift=false
  private static final boolean WINDOW_LIFT =
      !"false".equals(System.getProperty("jacop.lcg.windowLift"));

  /**
   * Adds what makes the tasks other than j need more energy in the window than the limit gives, for
   * every start of j in [lo, hi] (j's overlap with the window rises, stays and falls with its
   * start, so the excess is smallest at lo or hi). Each task needs r times its smallest overlap o
   * with the window. The excess beyond what the explanation needs is spent on leaving out the tasks
   * that need the least energy, then on lowering o for the others; a task is then kept to an
   * overlap of o by start bounds lifted to [a + o - d, b - o], which every start overlaps by at
   * least o.
   */
  private void addWindowReason(
      AtomicTrail trail, int position, int j, int[] window, int lo, int hi, EntryList out) {
    int a = window[0];
    int b = window[1];
    trail.addUpperBound(limit, position, out);
    int n = taskNormal.length;
    int[] need = new int[n];
    Integer[] order = new Integer[n];
    int count = 0;
    for (int i = 0; i < n; i++) {
      TaskView task = taskNormal[i];
      int d = dmin(position, task);
      if (i != j && rmin(position, task) > 0) {
        need[i] = Math.min(overlap(est(task), d, a, b), overlap(lst(task), d, a, b));
        if (need[i] > 0) {
          order[count++] = i;
        }
      }
    }
    long slack = 0;
    if (WINDOW_LIFT) {
      slack =
          j < 0
              ? windowExcess(trail, position, -1, 0, a, b)
              : Math.min(
                  windowExcess(trail, position, j, lo, a, b),
                  windowExcess(trail, position, j, hi, a, b));
      // the energy must exceed what the limit gives by at least one
      slack--;
    }
    // the tasks needing the least energy first
    Arrays.sort(
        order,
        0,
        count,
        (x, y) ->
            Long.compare(
                (long) rmin(position, taskNormal[x]) * need[x],
                (long) rmin(position, taskNormal[y]) * need[y]));
    int first = 0;
    while (first < count
        && (long) rmin(position, taskNormal[order[first]]) * need[order[first]] <= slack) {
      slack -= (long) rmin(position, taskNormal[order[first]]) * need[order[first]];
      first++;
    }
    for (int k = first; k < count; k++) {
      int i = order[k];
      TaskView task = taskNormal[i];
      int r = rmin(position, task);
      int d = dmin(position, task);
      int less = (int) Math.min(need[i] - 1L, slack / r);
      int o = need[i] - less;
      slack -= (long) less * r;
      trail.addBoundReaching(task.start, position, true, (long) a + o - d, out);
      trail.addBoundReaching(task.start, position, false, (long) b - o, out);
      trail.addLowerBound(task.dur, position, out);
      trail.addLowerBound(task.res, position, out);
    }
  }

  private boolean covers(AtomicTrail trail, int position, TaskView task, int t) {
    return lst(task) <= t && t < est(task) + dmin(position, task);
  }

  // the smallest duration and resource use of a task just before a trail position
  private int dmin(int position, TaskView task) {
    assert position == snapshotPosition : "bounds read at another position than the snapshot";
    return snapshotDur[slot(task)];
  }

  private int rmin(int position, TaskView task) {
    assert position == snapshotPosition : "bounds read at another position than the snapshot";
    return snapshotRes[slot(task)];
  }

  private int est(TaskView task) {
    return snapshotEst[slot(task)];
  }

  private int lst(TaskView task) {
    return snapshotLst[slot(task)];
  }

  private int slot(TaskView task) {
    return taskSlot.get(task);
  }

  /**
   * Reads the bounds of every task and the limit's maximum just before a trail position, once per
   * explanation, since each read walks the variable's entries; and sets the work an explanation may
   * spend on windows.
   */
  private void snapshot(AtomicTrail trail, int position) {
    int n = taskNormal.length;
    if (taskSlot == null) {
      // the propagators reorder taskNormal, so the slots follow a copy of their own
      snapshotTasks = taskNormal.clone();
      taskSlot = new IdentityHashMap<>();
      for (int i = 0; i < n; i++) {
        taskSlot.put(snapshotTasks[i], i);
      }
      snapshotEst = new int[n];
      snapshotLst = new int[n];
      snapshotDur = new int[n];
      snapshotRes = new int[n];
    }
    for (int i = 0; i < n; i++) {
      TaskView task = snapshotTasks[i];
      snapshotEst[i] = trail.minBefore(task.start, position);
      snapshotLst[i] = trail.maxBefore(task.start, position);
      snapshotDur[i] = trail.minBefore(task.dur, position);
      snapshotRes[i] = trail.minBefore(task.res, position);
    }
    limitMax = trail.maxBefore(limit, position);
    snapshotPosition = position;
    windowBudget = WINDOW_BUDGET;
  }

  /**
   * Adds what makes a task's compulsory part cover time t, lifted: the earliest bounds of its start
   * on the trail that keep it within [t - d + 1, t] for its smallest duration d, and the lower
   * bounds of its duration and resource use.
   */
  private void addTaskReasonAt(
      AtomicTrail trail, int position, TaskView task, int t, EntryList out) {
    trail.addBoundReaching(task.start, position, true, (long) t - dmin(position, task) + 1, out);
    trail.addBoundReaching(task.start, position, false, t, out);
    trail.addLowerBound(task.dur, position, out);
    trail.addLowerBound(task.res, position, out);
  }

  /**
   * Returns the overload: the sum over time of the resource used above the limit.
   *
   * @param value the value of each variable.
   * @return the overload.
   */
  @Override
  public long violation(ToIntFunction<IntVar> value) {
    int n = taskNormal.length;
    long[] events = new long[2 * n];
    int k = 0;
    for (int i = 0; i < n; i++) {
      TaskView t = taskNormal[i];
      int r = value.applyAsInt(t.res);
      int d = value.applyAsInt(t.dur);
      if (r <= 0 || d <= 0 || !present(i, value)) {
        continue;
      }
      int s = value.applyAsInt(t.start);
      // time in the high bits, the change of usage in the low 32 bits
      events[k++] = ((long) s << 32) | (r & 0xffffffffL);
      events[k++] = ((long) s + d << 32) | (-r & 0xffffffffL);
    }
    Arrays.sort(events, 0, k);
    long cap = value.applyAsInt(limit);
    long usage = 0;
    long over = 0;
    for (int e = 0; e < k; e++) {
      long time = events[e] >> 32;
      if (usage > cap) {
        long previous = events[e - 1] >> 32;
        over += (usage - cap) * (time - previous);
      }
      usage += (int) events[e];
    }
    return over;
  }

  /**
   * Whether a task is present for {@link #violation(ToIntFunction)}; optional tasks override it.
   *
   * @param i the task.
   * @param value the value of each variable.
   * @return true when the task uses the resource.
   */
  protected boolean present(int i, ToIntFunction<IntVar> value) {
    return true;
  }
}
