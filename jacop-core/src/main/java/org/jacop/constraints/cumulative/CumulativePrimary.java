/*
 * CumulativePrimary.java
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

import java.util.Arrays;
import java.util.BitSet;
import java.util.Comparator;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;

/*
 * CumulativePrimary implements the cumulative constraint using time tabling
 * algorithm.
 *
 * The sweep follows the scalable sweep of A. Letort, N. Beldiceanu and M. Carlsson, "A Scalable
 * Sweep Algorithm for the cumulative Constraint", CP 2012, LNCS 7514, pp. 439-454: the tasks under
 * pruning are kept by resource use, and at each change of the profile only the tasks whose use
 * crosses the gap between the profile and the limit are touched, instead of every task under
 * pruning. Unlike that paper, which computes the earliest start only, the sweep keeps removing
 * every start that overlaps a point without room (holes), as before; the tasks are kept in two
 * bit sets over the order of increasing resource use, which scans faster than the paper's heaps
 * when, as on largescheduling, tasks cross the gap at almost every profile change.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */

@Slf4j
class CumulativePrimary extends Constraint implements Copyable<CumulativePrimary> {

  private static final boolean DEBUG = false;
  private static final boolean DEBUG_NARR = false;
  // event type
  private static final int PROFILE = 0;
  private static final int PRUNE_START = 1;
  private static final int PRUNE_END = 2;
  private static final AtomicInteger idNumber = new AtomicInteger(0);
  /*
   * It specifies the limit of the PROFILE of cumulative use of resources.
   */
  protected final IntVar limit;
  /*
   * start times of tasks
   */
  private final IntVar[] start;

  /** The start that lost all its values when the last sweep failed, or null. */
  IntVar noStartLeft;

  /*
   * All durations and resources of the constraint
   */
  private final int[] dur;
  private final int[] res;
  private static final int SEQUENCE_MASK = (1 << 30) - 1;

  // events: (date, type, sequence number) in the key, task index and profile change by sequence
  private final long[] eventKeys;
  private final int[] eventIndex;
  private final int[] eventValue;

  // sweep state, reused between calls: the state of each task and the waiting tasks (use at most
  // the gap) and conflicting tasks (use more), as bit sets over the order by resource use
  private static final byte NONE = 0;
  private static final byte WAITING = 1;
  private static final byte CONFLICT = 2;
  private static final byte IN_PROFILE = 3;
  private final byte[] state;
  // tasks by rank, the order of increasing resource use (ties by index)
  private final int[] rank;
  private final int[] taskOfRank;
  private final int[] resOfRank;
  private final BitSet waiting;
  private final BitSet conflict;
  private final int[] releaseBuffer;
  private int releaseCount;
  private final int[] startExcluded;
  private final int[] activeMap;
  private final TimeStamp<Integer> activePnt;

  /*
   * It creates a cumulative constraint.
   *
   * @param starts    variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit     the overall limit of resources which has to be used.
   */
  public CumulativePrimary(IntVar[] starts, int[] durations, int[] resources, IntVar limit) {

    checkInputForNullness(
        new String[] {"starts", "durations", "resources", "limit"},
        starts,
        new Object[] {durations},
        new Object[] {resources},
        new Object[] {limit});
    checkInput(durations, i -> i >= 0, "durations must not be negative");
    checkInput(resources, i -> i >= 0, "resources must not be negative");

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
      throw new IllegalArgumentException("Cumulative needs to have resource limit that is >= 0.");
    }

    this.queueIndex = 2;
    this.numberId = idNumber.incrementAndGet();

    dur = Arrays.copyOf(durations, durations.length);
    res = Arrays.copyOf(resources, resources.length);
    start = Arrays.copyOf(starts, starts.length);
    eventKeys = new long[4 * start.length];
    eventIndex = new int[4 * start.length];
    eventValue = new int[4 * start.length];
    state = new byte[start.length];
    taskOfRank =
        IntStream.range(0, start.length)
            .boxed()
            .sorted(Comparator.comparingInt((Integer i) -> res[i]).thenComparingInt(i -> i))
            .mapToInt(Integer::intValue)
            .toArray();
    rank = new int[start.length];
    resOfRank = new int[start.length];
    for (int r = 0; r < start.length; r++) {
      rank[taskOfRank[r]] = r;
      resOfRank[r] = res[taskOfRank[r]];
    }
    waiting = new BitSet(start.length);
    conflict = new BitSet(start.length);
    releaseBuffer = new int[start.length];
    startExcluded = new int[start.length];
    activeMap = new int[start.length];
    for (int i = 0; i < start.length; i++) {
      activeMap[i] = i;
    }

    setScope(Stream.concat(Arrays.stream(starts), Stream.of(limit)));

    activePnt = new TimeStamp<>(limit.getStore(), 0);
  }

  /*
   * It creates a cumulative constraint.
   *
   * @param starts    variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit     the overall limit of resources which has to be used.
   */
  public CumulativePrimary(
      List<? extends IntVar> starts,
      List<? extends Integer> durations,
      List<? extends Integer> resources,
      IntVar limit) {

    this(
        starts.toArray(IntVar[]::new),
        durations.stream().mapToInt(i -> i).toArray(),
        resources.stream().mapToInt(i -> i).toArray(),
        limit);
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

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : cumulativePrimary([ ");
    for (int i = 0; i < start.length - 1; i++) {
      result
          .append("[")
          .append(start[i])
          .append(", ")
          .append(dur[i])
          .append(", ")
          .append(res[i])
          .append("], ");
    }

    result
        .append("[")
        .append(start[start.length - 1])
        .append(", ")
        .append(dur[start.length - 1])
        .append(", ")
        .append(res[start.length - 1])
        .append("]");

    result.append(" ]").append(", limit = ").append(limit).append(" )");

    return result.toString();
  }

  // Sweep algorithm for PROFILE
  void sweepPruning(Store store) {

    noStartLeft = null;
    int count = buildSweepEventArray();
    if (count == 0) {
      return;
    }

    final int limitMax = limit.max();

    // sorts by date and type; the sequence number in the low bits keeps the order stable
    Arrays.sort(eventKeys, 0, count);

    logDebugNarrIfEnabled(count, limitMax);

    Arrays.fill(state, NONE);
    waiting.clear();
    conflict.clear();
    releaseCount = 0;

    // current value of the PROFILE for mandatory parts
    int curProfile = 0;

    for (int i = 0; i < count; i++) {

      long key = eventKeys[i];
      int date = date(key);
      int type = type(key);
      int seq = sequence(key);
      int index = eventIndex[seq];

      switch (type) {
        case PROFILE:
          curProfile += eventValue[seq];
          if (state[index] != NONE) {
            sweepPruningHandleOwnProfile(index, eventValue[seq] > 0);
          }
          if (i == count - 1
              || type(eventKeys[i + 1]) != PROFILE
              || date < date(eventKeys[i + 1])) {
            sweepPruningHandleProfileEnd(store, date, curProfile, limitMax);
          }
          break;
        case PRUNE_START:
          sweepPruningHandlePruneStart(index, date, limitMax, curProfile);
          break;
        case PRUNE_END:
          sweepPruningHandlePruneEnd(store, index);
          break;
        default:
          throw new RuntimeException("Internal error in " + getClass().getName());
      }
    }

    if (!store.propagationHasOccurred) {
      removeNotUsedProfleTasks();
    }
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

  private void addEvent(int seq, int type, int index, int date, int value) {
    eventKeys[seq] = ((long) date << 32) | ((long) type << 30) | seq;
    eventIndex[seq] = index;
    eventValue[seq] = value;
  }

  // fills the event arrays and returns the number of events
  private int buildSweepEventArray() {
    int j = 0;
    int minProfile = Integer.MAX_VALUE;
    int maxProfile = Integer.MIN_VALUE;
    int first = activePnt.value();
    for (int i = first; i < start.length; i++) {
      int k = activeMap[i];

      int min = start[k].max();
      int max = start[k].min() + dur[k];
      if (min < max) {
        addEvent(j++, PROFILE, k, min, res[k]);
        addEvent(j++, PROFILE, k, max, -res[k]);
        minProfile = Math.min(min, minProfile);
        maxProfile = Math.max(max, maxProfile);
      }
    }

    for (int i = first; i < start.length; i++) {
      int k = activeMap[i];

      // a task with zero duration or zero resource use does not occupy the resource
      if (!start[k].singleton() && dur[k] > 0 && res[k] > 0) {
        int min = start[k].min();
        int max = start[k].max() + dur[k];
        if (min <= maxProfile && max >= minProfile) {
          addEvent(j++, PRUNE_START, k, min, 0);
          addEvent(j++, PRUNE_END, k, max, 0);
        }
      }
    }

    return j;
  }

  private void logDebugNarrIfEnabled(int count, int limitMax) {
    if (DEBUG_NARR) {
      for (int i = 0; i < count; i++) {
        int seq = sequence(eventKeys[i]);
        log.debug(
            "({}, {}, {}, {})",
            type(eventKeys[i]),
            eventIndex[seq],
            date(eventKeys[i]),
            eventValue[seq]);
      }
      log.debug("limit.max() = {}", limitMax);
      log.debug("===========================");
    }
  }

  private void sweepPruningHandleProfileEnd(Store store, int date, int curProfile, int limitMax) {
    if (DEBUG) {
      log.debug("Profile at {}: {}", date, curProfile);
    }
    if (curProfile > limit.min()) {
      limit.domain.inMin(store.level, limit, curProfile);
    }
    // waiting tasks use at most the gap, conflicting tasks more; the tasks of rank from k on use
    // more
    int k = firstRankAbove(limitMax - curProfile);
    // tasks in conflict that fit again; the tasks whose compulsory part started at this date are
    // in the buffer already
    for (int r = conflict.nextSetBit(0); r >= 0 && r < k; r = conflict.nextSetBit(r + 1)) {
      conflict.clear(r);
      int ti = taskOfRank[r];
      state[ti] = WAITING;
      releaseBuffer[releaseCount++] = ti;
    }
    if (releaseCount > 0) {
      // the pruning happens in task order, as in the loop over all tasks
      if (releaseCount > 1) {
        Arrays.sort(releaseBuffer, 0, releaseCount);
      }
      int n = releaseCount;
      releaseCount = 0;
      for (int r = 0; r < n; r++) {
        int ti = releaseBuffer[r];
        if (DEBUG_NARR) {
          log.debug(
              ">>> CumulativePrimary Profile 1. Narrowed {} \\ {}",
              start[ti],
              new IntervalDomain(startExcluded[ti], date - 1));
          log.debug(" => {}", start[ti]);
        }
        try {
          TimetableSweep.removeStarts(store, start[ti], startExcluded[ti], date - 1);
        } catch (FailException e) {
          noStartLeft = start[ti];
          throw e;
        }
        if (state[ti] == WAITING) {
          waiting.set(rank[ti]);
        }
      }
    }
    // waiting tasks that do not fit any more
    for (int r = waiting.nextSetBit(k); r >= 0; r = waiting.nextSetBit(r + 1)) {
      waiting.clear(r);
      int ti = taskOfRank[r];
      startExcluded[ti] = date - dur[ti] + 1;
      state[ti] = CONFLICT;
      conflict.set(r);
    }
  }

  // the first rank whose task uses more than gap
  private int firstRankAbove(int gap) {
    int lo = 0;
    int hi = resOfRank.length;
    while (lo < hi) {
      int mid = (lo + hi) >>> 1;
      if (resOfRank[mid] <= gap) {
        lo = mid + 1;
      } else {
        hi = mid;
      }
    }
    return lo;
  }

  // the compulsory part of a task starts or ends; it does not conflict with itself
  private void sweepPruningHandleOwnProfile(int ti, boolean in) {
    if (in) {
      if (state[ti] == CONFLICT) {
        conflict.clear(rank[ti]);
        releaseBuffer[releaseCount++] = ti;
        state[ti] = IN_PROFILE;
      } else if (state[ti] == WAITING) {
        waiting.clear(rank[ti]);
        state[ti] = IN_PROFILE;
      }
    } else if (state[ti] == IN_PROFILE) {
      state[ti] = WAITING;
      waiting.set(rank[ti]);
    }
  }

  private void sweepPruningHandlePruneStart(int ti, int date, int limitMax, int curProfile) {
    if (limitMax - curProfile < res[ti]) {
      startExcluded[ti] = date;
      state[ti] = CONFLICT;
      conflict.set(rank[ti]);
    } else {
      state[ti] = WAITING;
      waiting.set(rank[ti]);
    }
  }

  private void sweepPruningHandlePruneEnd(Store store, int ti) {
    if (state[ti] == CONFLICT) {
      conflict.clear(rank[ti]);
      if (DEBUG_NARR) {
        log.debug(
            ">>> CumulativePrimary Profile 2. Narrowed {} inMax {} => {}",
            start[ti],
            startExcluded[ti] - 1,
            start[ti]);
      }
      try {
        start[ti].domain.inMax(store.level, start[ti], startExcluded[ti] - 1);
      } catch (FailException e) {
        noStartLeft = start[ti];
        throw e;
      }
    } else if (state[ti] == WAITING) {
      waiting.clear(rank[ti]);
    }
    state[ti] = NONE;
  }

  private void removeNotUsedProfleTasks() {

    // remove ground tasks that make PROFILE but do not contribute
    // to pruning of other tasks; they are located outside the
    // range of tasks
    int minPrune = Integer.MAX_VALUE;
    int maxPrune = Integer.MIN_VALUE;
    int first = activePnt.value();
    for (int i = first; i < start.length; i++) {
      int k = activeMap[i];

      if (!start[k].singleton()) {
        int min = start[k].min();
        int max = start[k].max() + dur[k];
        minPrune = Math.min(min, minPrune);
        maxPrune = Math.max(max, maxPrune);
      }
    }

    for (int i = first; i < start.length; i++) {
      int k = activeMap[i];

      int s = start[k].min();
      int e = start[k].max() + dur[k];
      if (start[k].singleton() && (s > maxPrune || e < minPrune)) {
        swap(first, i);
        first++;
      }
    }
    activePnt.update(first);
  }

  private void swap(int i, int j) {
    if (i != j) {
      int tmp = activeMap[i];
      activeMap[i] = activeMap[j];
      activeMap[j] = tmp;
    }
  }

  @Override
  public CumulativePrimary copy(VarMap map) {
    return new CumulativePrimary(map.get(start), dur, res, map.get(limit));
  }
}
