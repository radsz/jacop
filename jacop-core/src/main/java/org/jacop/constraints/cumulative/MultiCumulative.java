/*
 * MultiCumulative.java
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
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/**
 * Time-table propagation of several cumulative resources used by the same tasks, as in the
 * multi_cumulative constraint of SICStus Prolog with cumulative resources only (Letort, Beldiceanu
 * and Carlsson, "Synchronized sweep algorithms for scalable scheduling constraints", Constraints
 * 19(3), 2014).
 *
 * <p>Task i starts at starts[i], lasts durations[i] and uses heights[r][i] of resource r, whose
 * capacity is limits[r]. The compulsory parts of the tasks are the same on every resource, only
 * their heights differ, so one sweep over one sorted event list keeps a profile per resource and
 * removes a start as soon as the task does not fit on one of them. It prunes what one {@link
 * CumulativePrimary} per resource prunes, with one sort and one wake-up instead of one per
 * resource.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class MultiCumulative extends Constraint implements Copyable<MultiCumulative> {

  private static final AtomicInteger idNumber = new AtomicInteger(0);

  // event types, in the order events of the same date are processed
  private static final int PROFILE_START = 0;
  private static final int PROFILE_END = 1;
  private static final int PRUNE_START = 2;
  private static final int PRUNE_END = 3;
  private static final int SEQUENCE_MASK = (1 << 30) - 1;

  private final IntVar[] start;
  private final int[] dur;
  private final int[][] heights;
  private final IntVar[] limits;

  // per task, the resources it uses and how much of each
  private final int[][] usedResources;
  private final int[][] usedHeights;
  // per task, the resources it uses as a bit mask (all bits with more than 64 resources)
  private final long[] resourceMask;
  // per resource, the largest use by a task that lasts
  private final int[] maxHeight;

  /** The start that lost all its values when the last sweep failed, or null. */
  IntVar noStartLeft;

  // events: (date, type, sequence number) in the key, the task by sequence number
  private final long[] eventKeys;
  private final int[] eventIndex;

  // sweep state, reused between calls
  private final int[] profile;
  private final int[] limitMax;
  private final BitSet tasksToPrune;
  private final boolean[] inProfile;
  private final int[] startExcluded;
  private final boolean[] startConsidered;
  private final int[] activeMap;
  private final TimeStamp<Integer> activePnt;

  /**
   * It creates a multi-resource cumulative constraint.
   *
   * @param starts the starts of the tasks.
   * @param durations the durations of the tasks.
   * @param heights heights[r][i] is the use of resource r by task i.
   * @param limits the capacities of the resources.
   */
  public MultiCumulative(IntVar[] starts, int[] durations, int[][] heights, IntVar[] limits) {

    checkInputForNullness(
        new String[] {"starts", "durations", "heights", "limits"},
        starts,
        new Object[] {durations},
        new Object[] {heights},
        limits);
    int n = starts.length;
    if (durations.length != n) {
      throw new IllegalArgumentException(
          "MultiCumulative needs the starts and durations of the same length.");
    }
    if (heights.length != limits.length) {
      throw new IllegalArgumentException(
          "MultiCumulative needs one row of heights for each resource limit.");
    }
    checkInput(durations, i -> i >= 0, "durations must not be negative");
    for (int[] h : heights) {
      if (h.length != n) {
        throw new IllegalArgumentException(
            "MultiCumulative needs one height per task for each resource.");
      }
      checkInput(h, i -> i >= 0, "heights must not be negative");
    }
    for (IntVar l : limits) {
      if (l.min() < 0) {
        throw new IllegalArgumentException("MultiCumulative needs resource limits that are >= 0.");
      }
    }

    this.queueIndex = 2;
    this.numberId = idNumber.incrementAndGet();

    start = Arrays.copyOf(starts, n);
    dur = Arrays.copyOf(durations, n);
    this.heights = new int[heights.length][];
    for (int r = 0; r < heights.length; r++) {
      this.heights[r] = Arrays.copyOf(heights[r], n);
    }
    this.limits = Arrays.copyOf(limits, limits.length);

    usedResources = new int[n][];
    usedHeights = new int[n][];
    for (int i = 0; i < n; i++) {
      int k = 0;
      for (int[] h : heights) {
        if (h[i] > 0) {
          k++;
        }
      }
      usedResources[i] = new int[k];
      usedHeights[i] = new int[k];
      k = 0;
      for (int r = 0; r < heights.length; r++) {
        if (heights[r][i] > 0) {
          usedResources[i][k] = r;
          usedHeights[i][k] = heights[r][i];
          k++;
        }
      }
    }

    resourceMask = new long[n];
    for (int i = 0; i < n; i++) {
      for (int r : usedResources[i]) {
        resourceMask[i] |= heights.length > 64 ? -1L : 1L << r;
      }
    }

    maxHeight = new int[heights.length];
    for (int r = 0; r < heights.length; r++) {
      for (int i = 0; i < n; i++) {
        if (dur[i] > 0) {
          maxHeight[r] = Math.max(maxHeight[r], heights[r][i]);
        }
      }
    }

    eventKeys = new long[4 * n];
    eventIndex = new int[4 * n];
    profile = new int[limits.length];
    limitMax = new int[limits.length];
    tasksToPrune = new BitSet(n);
    inProfile = new boolean[n];
    startExcluded = new int[n];
    startConsidered = new boolean[n];
    // only the tasks that use a resource and last are swept
    int active = 0;
    int[] map = new int[n];
    for (int i = 0; i < n; i++) {
      if (usedResources[i].length > 0 && dur[i] > 0) {
        map[active++] = i;
      }
    }
    activeMap = Arrays.copyOf(map, active);

    setScope(Stream.concat(Arrays.stream(starts), Arrays.stream(limits)));

    activePnt = new TimeStamp<>(limits[0].getStore(), 0);
  }

  @Override
  public void consistency(Store store) {

    do {

      store.propagationHasOccurred = false;

      sweepPruning(store);

    } while (store.propagationHasOccurred);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  private static int date(long key) {
    return (int) (key >> 32);
  }

  private static int type(long key) {
    return (int) (key >>> 30) & 3;
  }

  private static int sequence(long key) {
    return (int) key & SEQUENCE_MASK;
  }

  private void addEvent(int seq, int type, int index, int date) {
    eventKeys[seq] = ((long) date << 32) | ((long) type << 30) | seq;
    eventIndex[seq] = index;
  }

  // fills the event arrays and returns the number of events
  private int buildSweepEventArray() {
    int j = 0;
    int minProfile = Integer.MAX_VALUE;
    int maxProfile = Integer.MIN_VALUE;
    int first = activePnt.value();
    for (int i = first; i < activeMap.length; i++) {
      int k = activeMap[i];

      int min = start[k].max();
      int max = start[k].min() + dur[k];
      if (min < max) {
        addEvent(j++, PROFILE_START, k, min);
        addEvent(j++, PROFILE_END, k, max);
        minProfile = Math.min(min, minProfile);
        maxProfile = Math.max(max, maxProfile);
      }
    }
    if (j == 0) {
      return 0;
    }

    for (int i = first; i < activeMap.length; i++) {
      int k = activeMap[i];

      if (!start[k].singleton()) {
        int min = start[k].min();
        int max = start[k].max() + dur[k];
        if (min <= maxProfile && max >= minProfile) {
          addEvent(j++, PRUNE_START, k, min);
          addEvent(j++, PRUNE_END, k, max);
        }
      }
    }

    return j;
  }

  // the sweep of CumulativePrimary with a profile per resource
  private void sweepPruning(Store store) {

    noStartLeft = null;
    for (int r = 0; r < limits.length; r++) {
      // a task that lasts must fit under the limit wherever it starts
      if (maxHeight[r] > limits[r].max()) {
        throw Store.failException;
      }
    }
    int count = buildSweepEventArray();
    if (count == 0) {
      return;
    }

    for (int r = 0; r < limits.length; r++) {
      limitMax[r] = limits[r].max();
    }
    Arrays.fill(profile, 0);

    // sorts by date and type; the sequence number in the low bits keeps the order stable
    Arrays.sort(eventKeys, 0, count);

    tasksToPrune.clear();
    Arrays.fill(inProfile, false);
    Arrays.fill(startConsidered, false);

    // the resources whose profile changed since the last profile change was handled
    long changed = 0;
    for (int i = 0; i < count; i++) {

      long key = eventKeys[i];
      int date = date(key);
      int type = type(key);
      int index = eventIndex[sequence(key)];

      switch (type) {
        case PROFILE_START, PROFILE_END:
          int sign = type == PROFILE_START ? 1 : -1;
          int[] rs = usedResources[index];
          int[] hs = usedHeights[index];
          for (int u = 0; u < rs.length; u++) {
            profile[rs[u]] += sign * hs[u];
          }
          inProfile[index] = type == PROFILE_START;
          changed |= resourceMask[index];
          if (i == count - 1
              || type(eventKeys[i + 1]) > PROFILE_END
              || date < date(eventKeys[i + 1])) {
            profileChanged(store, date, changed);
            changed = 0;
          }
          break;
        case PRUNE_START:
          if (!inProfile[index] && !fits(index)) {
            startExcluded[index] = date;
            startConsidered[index] = true;
          }
          tasksToPrune.set(index);
          break;
        case PRUNE_END:
          if (startConsidered[index]) {
            try {
              start[index].domain.inMax(store.level, start[index], startExcluded[index] - 1);
            } catch (FailException e) {
              noStartLeft = start[index];
              throw e;
            }
          }
          startConsidered[index] = false;
          tasksToPrune.clear(index);
          break;
        default:
          throw new IllegalStateException("Unknown event type");
      }
    }

    if (!store.propagationHasOccurred) {
      removeNotUsedProfileTasks();
    }
  }

  // whether task i fits on every resource next to the current profile
  private boolean fits(int i) {
    int[] rs = usedResources[i];
    int[] hs = usedHeights[i];
    for (int u = 0; u < rs.length; u++) {
      int r = rs[u];
      if (limitMax[r] - profile[r] < hs[u]) {
        return false;
      }
    }
    return true;
  }

  private void profileChanged(Store store, int date, long changed) {
    for (int r = 0; r < limits.length; r++) {
      if (profile[r] > limits[r].min()) {
        limits[r].domain.inMin(store.level, limits[r], profile[r]);
      }
    }
    for (int ti = tasksToPrune.nextSetBit(0); ti >= 0; ti = tasksToPrune.nextSetBit(ti + 1)) {
      // a task fits as before if none of its resources changed; its own profile events change
      // its resources
      if ((resourceMask[ti] & changed) == 0) {
        continue;
      }
      boolean free = inProfile[ti] || fits(ti);
      if (!startConsidered[ti]) {
        if (!free) {
          startExcluded[ti] = date - dur[ti] + 1;
          startConsidered[ti] = true;
        }
      } else if (free) {
        try {
          TimetableSweep.removeStarts(store, start[ti], startExcluded[ti], date - 1);
        } catch (FailException e) {
          noStartLeft = start[ti];
          throw e;
        }
        startConsidered[ti] = false;
      }
    }
  }

  // moves out of the sweep the fixed tasks that end before or start after every task to prune
  private void removeNotUsedProfileTasks() {
    int minPrune = Integer.MAX_VALUE;
    int maxPrune = Integer.MIN_VALUE;
    int first = activePnt.value();
    for (int i = first; i < activeMap.length; i++) {
      int k = activeMap[i];
      if (!start[k].singleton()) {
        minPrune = Math.min(start[k].min(), minPrune);
        maxPrune = Math.max(start[k].max() + dur[k], maxPrune);
      }
    }

    for (int i = first; i < activeMap.length; i++) {
      int k = activeMap[i];
      int s = start[k].min();
      int e = start[k].max() + dur[k];
      if (start[k].singleton() && (s > maxPrune || e < minPrune)) {
        int tmp = activeMap[first];
        activeMap[first] = activeMap[i];
        activeMap[i] = tmp;
        first++;
      }
    }
    activePnt.update(first);
  }

  /**
   * Finds the {@link Cumulative} constraints over tasks with fixed durations and resource uses that
   * share tasks (the same start variable, not fixed, with the same duration), and gives each group
   * of two or more one {@link MultiCumulative} that does their time tabling; the cumulative
   * constraints keep their other rules. Constraints that are not in a group are returned unchanged.
   *
   * @param constraints the constraints to impose.
   * @return the constraints with a MultiCumulative added for each group, or the same list if there
   *     is no group.
   */
  public static List<Constraint> merge(List<Constraint> constraints) {
    List<Cumulative> candidates = new ArrayList<>();
    List<List<TaskKey>> keys = new ArrayList<>();
    int fixedTasks = 0;
    for (Constraint c : constraints) {
      if (c instanceof Cumulative cu
          && c.getClass() == Cumulative.class
          && cu.doTimeTable
          && cu.cumulativeForConstants != null) {
        List<TaskKey> tasks = new ArrayList<>();
        for (TaskView t : cu.taskNormal) {
          // a fixed start, often one constant shared by the model, does not make a task shared
          int fixed = t.start.singleton() ? ++fixedTasks : 0;
          tasks.add(new TaskKey(t.start, t.dur.value(), fixed));
        }
        // a task given twice cannot be told apart from two tasks with the same start
        if (new HashSet<>(tasks).size() == tasks.size()) {
          candidates.add(cu);
          keys.add(tasks);
        }
      }
    }
    if (candidates.size() < 2) {
      return constraints;
    }

    // groups of cumulative constraints connected by shared tasks
    int[] parent = new int[candidates.size()];
    Map<TaskKey, Integer> owner = new HashMap<>();
    for (int i = 0; i < candidates.size(); i++) {
      parent[i] = i;
      for (TaskKey t : keys.get(i)) {
        Integer j = owner.putIfAbsent(t, i);
        if (j != null) {
          parent[root(parent, i)] = root(parent, j);
        }
      }
    }
    Map<Integer, List<Integer>> groups = new LinkedHashMap<>();
    for (int i = 0; i < candidates.size(); i++) {
      groups.computeIfAbsent(root(parent, i), k -> new ArrayList<>()).add(i);
    }

    List<Constraint> result = new ArrayList<>(constraints);
    boolean merged = false;
    for (List<Integer> group : groups.values()) {
      if (group.size() < 2) {
        continue;
      }
      Map<TaskKey, Integer> index = new LinkedHashMap<>();
      for (int i : group) {
        for (TaskKey t : keys.get(i)) {
          index.putIfAbsent(t, index.size());
        }
      }
      int n = index.size();
      IntVar[] starts = new IntVar[n];
      int[] durations = new int[n];
      for (Map.Entry<TaskKey, Integer> e : index.entrySet()) {
        starts[e.getValue()] = e.getKey().start;
        durations[e.getValue()] = e.getKey().duration;
      }
      int[][] heights = new int[group.size()][n];
      IntVar[] limits = new IntVar[group.size()];
      for (int r = 0; r < group.size(); r++) {
        Cumulative cu = candidates.get(group.get(r));
        List<TaskKey> tasks = keys.get(group.get(r));
        for (int i = 0; i < tasks.size(); i++) {
          heights[r][index.get(tasks.get(i))] = cu.taskNormal[i].res.value();
        }
        limits[r] = cu.limit;
        cu.doTimeTable(false);
      }
      result.add(new MultiCumulative(starts, durations, heights, limits));
      merged = true;
    }
    return merged ? result : constraints;
  }

  private static int root(int[] parent, int i) {
    while (parent[i] != i) {
      parent[i] = parent[parent[i]];
      i = parent[i];
    }
    return i;
  }

  // a task of a cumulative constraint: its start variable, its fixed duration and, for a fixed
  // start, a number of its own
  private record TaskKey(IntVar start, int duration, int fixed) {}

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : multiCumulative([");
    for (int i = 0; i < start.length; i++) {
      if (i > 0) {
        result.append(", ");
      }
      result.append("[").append(start[i]).append(", ").append(dur[i]).append(", ");
      result.append("[");
      for (int r = 0; r < heights.length; r++) {
        result.append(r > 0 ? ", " : "").append(heights[r][i]);
      }
      result.append("]]");
    }
    result.append("], limits = ").append(Arrays.toString(limits)).append(")");
    return result.toString();
  }

  @Override
  public MultiCumulative copy(VarMap map) {
    return new MultiCumulative(map.get(start), dur, heights, map.get(limits));
  }
}
