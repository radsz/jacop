/*
 * CumulativesExplanation.java
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
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Lazy clause generation reasons of {@link Cumulatives}. Every rule of the sweep rests on the least
 * load of the other tasks at one time on one machine, so a reason is that load re-derived from the
 * bounds just before the explained atom: the tasks whose compulsory part covers the time (their
 * presence, machine, start, duration and height), the least heights of the tasks that may run there
 * with a negative height, the atoms that keep the other tasks with negative heights away, and the
 * bound of the machine. The rules add what makes the task run at that time: its start range for a
 * forbidden time, the compulsory part of another task when the task is forced to run. Heights and
 * bounds are in the upper form, the lower form negates them.
 */
final class CumulativesExplanation {

  private final Cumulatives c;
  private final int n;
  private final EntryList scratch = new EntryList();

  // the trail and position the reason is built at
  private AtomicTrail trail;
  private int pos;

  // times at which the least load of the other tasks of a machine may change, sorted
  private long[] times;
  private int timeCount;

  // the least load at a time and whether a compulsory part covers it, from load()
  private long loadValue;
  private boolean active;

  CumulativesExplanation(Cumulatives c) {
    this.c = c;
    this.n = c.starts.length;
    this.times = new long[4 * n];
  }

  boolean explain(AtomicTrail t, int entry, EntryList out) {
    trail = t;
    pos = entry;
    IntVar x = trail.variable(entry);
    int kind = trail.kind(entry);
    int value = trail.value(entry);
    int mark = out.size();
    for (int i = 0; i < n; i++) {
      if (c.starts[i] == x && explainStart(i, kind, value, out)
          || c.machines[i] == x && explainMachine(i, kind, value, out)
          || c.durations[i] == x && explainDuration(i, kind, value, out)
          || c.heights[i] == x && explainHeight(i, kind, value, out)
          || c.present != null && c.present[i] == x && explainPresence(i, kind, out)) {
        out.sortUnique(mark);
        return true;
      }
      out.truncate(mark);
    }
    for (int k = 0; k < c.bounds.length; k++) {
      if (c.bounds[k] == x && explainBound(k, kind, value, out)) {
        out.sortUnique(mark);
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  boolean explainFailure(AtomicTrail t, EntryList out) {
    trail = t;
    pos = trail.size();
    int mark = out.size();
    EntryList best = null;
    EntryList candidate = new EntryList();
    // the overloaded time with the smallest reason
    for (int k = 0; k < c.bounds.length; k++) {
      long b = bound(k);
      collectTimes(k, -1);
      for (int a = 0; a < timeCount; a++) {
        long time = times[a];
        load(k, time, -1);
        if (active && loadValue > b) {
          candidate.clear();
          if (addLoad(k, time, -1, b + 1, true, candidate) && addBoundAtom(k, b, candidate)) {
            candidate.sortUnique(0);
            if (best == null || candidate.size() < best.size()) {
              best = candidate;
              candidate = new EntryList();
            }
          }
        }
      }
    }
    // a task whose starts all meet forbidden times, or that cannot run where it is forced to
    for (int i = 0; i < n; i++) {
      candidate.clear();
      if (taskFailure(i, candidate)) {
        candidate.sortUnique(0);
        if (best == null || candidate.size() < best.size()) {
          best = candidate;
          candidate = new EntryList();
        }
      }
    }
    if (best == null) {
      return false;
    }
    for (int a = 0; a < best.size(); a++) {
      out.addFrom(best, a);
    }
    out.sortUnique(mark);
    return true;
  }

  // a reason why task i has no place: no start of a fixed task avoids the forbidden times, or a
  // time it is forced to run at is out of its reach
  private boolean taskFailure(int i, EntryList out) {
    IntVar s = c.starts[i];
    int smin = trail.minBefore(s, pos);
    int smax = trail.maxBefore(s, pos);
    int dmax = trail.maxBefore(c.durations[i], pos);
    long forcedOn = -1;
    long firstForced = Long.MIN_VALUE;
    for (int k = 0; k < c.bounds.length; k++) {
      int mark = out.size();
      if (onlyMachine(i, k)
          && surelyPresent(i)
          && smin <= smax
          && addAtom(s, true, smin, out)
          && addAtom(s, false, smax, out)
          && coverStarts(i, k, smin, smax, out)
          && addRunning(i, k, out)) {
        return true;
      }
      out.truncate(mark);
      long early = forcedTime(i, k, Long.MIN_VALUE, Long.MAX_VALUE, true);
      if (early == Long.MIN_VALUE) {
        continue;
      }
      long late = forcedTime(i, k, Long.MIN_VALUE, Long.MAX_VALUE, false);
      int machine = c.firstMachine + k;
      if (excludedAtom(c.machines[i], machine, out) && addForced(i, k, early, out)
          || c.present != null
              && trail.maxBefore(c.present[i], pos) == 0
              && addAtom(c.present[i], false, 0, out)
              && addForced(i, k, early, out)
          || early < smin && addAtom(s, true, smin, out) && addForced(i, k, early, out)
          || (long) smax + dmax <= late
              && addAtom(s, false, smax, out)
              && addAtom(c.durations[i], false, dmax, out)
              && addForced(i, k, late, out)
          || late - early + 1 > dmax
              && addAtom(c.durations[i], false, late - early, out)
              && addForced(i, k, early, out)
              && addForced(i, k, late, out)) {
        return true;
      }
      out.truncate(mark);
      if (forcedOn >= 0) {
        // forced on two machines
        if (addForced(i, (int) forcedOn, firstForced, out) && addForced(i, k, early, out)) {
          return true;
        }
        out.truncate(mark);
      } else {
        forcedOn = k;
        firstForced = early;
      }
    }
    return false;
  }

  // ---------------------------------------------------------------- rules

  private boolean explainStart(int i, int kind, int value, EntryList out) {
    IntVar s = c.starts[i];
    int prevMin = trail.minBefore(s, pos);
    int prevMax = trail.maxBefore(s, pos);
    for (int k = 0; k < c.bounds.length; k++) {
      if (!onlyMachine(i, k) || !surelyPresent(i)) {
        continue;
      }
      int mark = out.size();
      // forced to run: s <= t for a forced time t <= value, or s + dmax > t for t >= value + dmax -
      // 1
      if (kind == AtomicTrail.LE && forcedReason(i, k, prevMin, value, true, out)) {
        return true;
      }
      out.truncate(mark);
      if (kind == AtomicTrail.GE) {
        int dmax = trail.maxBefore(c.durations[i], pos);
        long t = forcedTime(i, k, (long) value + dmax - 1, (long) prevMax + dmax, false);
        if (t != Long.MIN_VALUE
            && addForced(i, k, t, out)
            && addAtom(c.durations[i], false, t - value + 1, out)) {
          return true;
        }
        out.truncate(mark);
      }
      // forbidden times: every removed start that is not a hole meets one
      long lo =
          kind == AtomicTrail.GE ? prevMin : kind == AtomicTrail.LE ? (long) value + 1 : value;
      long hi =
          kind == AtomicTrail.GE ? (long) value - 1 : kind == AtomicTrail.LE ? prevMax : value;
      if (kind == AtomicTrail.GE && !addAtom(s, true, prevMin, out)
          || kind == AtomicTrail.LE && !addAtom(s, false, prevMax, out)) {
        out.truncate(mark);
        continue;
      }
      if (coverStarts(i, k, lo, hi, out) && addRunning(i, k, out)) {
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  private boolean explainMachine(int i, int kind, int value, EntryList out) {
    IntVar m = c.machines[i];
    // forced to one machine
    for (int k = 0; k < c.bounds.length; k++) {
      int machine = c.firstMachine + k;
      if (removes(m, kind, value, machine) || excluded(m, machine)) {
        continue;
      }
      int mark = out.size();
      long t = forcedTime(i, k, Long.MIN_VALUE, Long.MAX_VALUE, true);
      if (t != Long.MIN_VALUE && addForced(i, k, t, out)) {
        return true;
      }
      out.truncate(mark);
    }
    // no start avoids the forbidden times of the removed machines
    if (!surelyPresent(i) || !addPresent(i, out)) {
      return false;
    }
    int lo =
        kind == AtomicTrail.GE
            ? trail.minBefore(m, pos)
            : kind == AtomicTrail.LE ? value + 1 : value;
    int hi =
        kind == AtomicTrail.GE
            ? value - 1
            : kind == AtomicTrail.LE ? trail.maxBefore(m, pos) : value;
    if (kind == AtomicTrail.GE && !addAtom(m, true, lo, out)
        || kind == AtomicTrail.LE && !addAtom(m, false, hi, out)) {
      return false;
    }
    IntVar s = c.starts[i];
    int smin = trail.minBefore(s, pos);
    int smax = trail.maxBefore(s, pos);
    if (!addAtom(s, true, smin, out) || !addAtom(s, false, smax, out)) {
      return false;
    }
    if (!addAtom(c.durations[i], true, trail.minBefore(c.durations[i], pos), out)
        || !addHeight(i, height(i), out)) {
      return false;
    }
    for (int machine = lo; machine <= hi; machine++) {
      int k = machine - c.firstMachine;
      if (k < 0 || k >= c.bounds.length) {
        return false;
      }
      if (excludedAtom(m, machine, out)) {
        continue;
      }
      if (!coverStarts(i, k, smin, smax, out)) {
        return false;
      }
    }
    return true;
  }

  private boolean explainDuration(int i, int kind, int value, EntryList out) {
    for (int k = 0; k < c.bounds.length; k++) {
      if (!onlyMachine(i, k) || !surelyPresent(i)) {
        continue;
      }
      int mark = out.size();
      if (kind == AtomicTrail.GE) {
        // forced to run at t >= smax + value - 1
        int smax = trail.maxBefore(c.starts[i], pos);
        long t = forcedTime(i, k, (long) smax + value - 1, Long.MAX_VALUE, false);
        if (t != Long.MIN_VALUE
            && addForced(i, k, t, out)
            && addAtom(c.starts[i], false, t - value + 1, out)) {
          return true;
        }
      } else if (kind == AtomicTrail.LE) {
        // a fixed start s runs into a forbidden time s + value
        int s = trail.minBefore(c.starts[i], pos);
        long t = (long) s + value;
        if (trail.maxBefore(c.starts[i], pos) == s
            && forbidden(i, k, t)
            && addAtom(c.starts[i], true, s, out)
            && addAtom(c.starts[i], false, t, out)
            && addForbidden(i, k, t, out)
            && addPresent(i, out)
            && addMachine(i, k, out)
            && addHeight(i, height(i), out)) {
          return true;
        }
      }
      out.truncate(mark);
    }
    return false;
  }

  private boolean explainHeight(int i, int kind, int value, EntryList out) {
    // the largest height in the upper form
    if (c.upper ? kind != AtomicTrail.LE : kind != AtomicTrail.GE) {
      return false;
    }
    long cap = c.upper ? value : -(long) value;
    for (int k = 0; k < c.bounds.length; k++) {
      if (!onlyMachine(i, k) || !surelyPresent(i)) {
        continue;
      }
      long b = bound(k);
      collectTimes(k, i);
      int mark = out.size();
      // over its compulsory part
      long from = trail.maxBefore(c.starts[i], pos);
      long to = (long) trail.minBefore(c.starts[i], pos) + trail.minBefore(c.durations[i], pos);
      for (long t : candidates(from, to - 1)) {
        load(k, t, i);
        if (loadValue >= b - cap
            && addLoad(k, t, i, b - cap, false, out)
            && addBoundAtom(k, b, out)
            && addCompulsory(i, k, t, out)) {
          return true;
        }
        out.truncate(mark);
      }
      // at a time it is forced to run
      for (long t : candidates(Long.MIN_VALUE, Long.MAX_VALUE)) {
        load(k, t, i);
        if (active
            && loadValue > b
            && loadValue >= b - cap
            && addLoad(k, t, i, Math.max(b + 1, b - cap), true, out)
            && addBoundAtom(k, b, out)) {
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  private boolean explainPresence(int i, int kind, EntryList out) {
    if (kind != AtomicTrail.GE) {
      return false;
    }
    for (int k = 0; k < c.bounds.length; k++) {
      if (excluded(c.machines[i], c.firstMachine + k)) {
        continue;
      }
      int mark = out.size();
      long t = forcedTime(i, k, Long.MIN_VALUE, Long.MAX_VALUE, true);
      if (t != Long.MIN_VALUE && addForced(i, k, t, out)) {
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  private boolean explainBound(int k, int kind, int value, EntryList out) {
    if (c.upper ? kind != AtomicTrail.GE : kind != AtomicTrail.LE) {
      return false;
    }
    long needed = c.upper ? value : -(long) value;
    collectTimes(k, -1);
    for (int a = 0; a < timeCount; a++) {
      long t = times[a];
      load(k, t, -1);
      if (active && loadValue >= needed) {
        int mark = out.size();
        if (addLoad(k, t, -1, needed, true, out)) {
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  // ---------------------------------------------------------------- forbidden and forced times

  // the starts in [lo, hi] are holes or meet a forbidden time of task i on machine k
  private boolean coverStarts(int i, int k, long lo, long hi, EntryList out) {
    IntVar s = c.starts[i];
    int dmin = trail.minBefore(c.durations[i], pos);
    if (dmin <= 0) {
      return false;
    }
    collectTimes(k, i);
    long u = lo;
    while (u <= hi) {
      if (excludedAtom(s, (int) u, out)) {
        u++;
        continue;
      }
      // the latest forbidden time that [u, u + dmin) meets covers the most starts
      long found = Long.MIN_VALUE;
      long[] cand = candidates(u, u + dmin - 1);
      for (int a = cand.length - 1; a >= 0; a--) {
        if (forbiddenLatest(i, k, cand[a], u + dmin - 1)) {
          found = lastForbidden;
          break;
        }
      }
      if (found == Long.MIN_VALUE || !addForbidden(i, k, found, out)) {
        return false;
      }
      u = found + 1;
    }
    return true;
  }

  private long lastForbidden;

  // a forbidden time in [t, limit] at which the load is that of t, the latest one
  private boolean forbiddenLatest(int i, int k, long t, long limit) {
    if (!forbidden(i, k, t)) {
      return false;
    }
    long next = limit;
    for (int a = 0; a < timeCount; a++) {
      if (times[a] > t) {
        next = Math.min(limit, times[a] - 1);
        break;
      }
    }
    lastForbidden = next;
    return true;
  }

  // task i running on machine k at t takes the least load above the bound
  private boolean forbidden(int i, int k, long t) {
    load(k, t, i);
    return loadValue + height(i) > bound(k);
  }

  private boolean addForbidden(int i, int k, long t, EntryList out) {
    long b = bound(k);
    return addLoad(k, t, i, b - height(i) + 1, false, out) && addBoundAtom(k, b, out);
  }

  /**
   * A time in [from, to] at which task i must run on machine k: a compulsory part of another task
   * covers it and the others exceed the bound. With earliest, the earliest such time, else the
   * latest.
   */
  private long forcedTime(int i, int k, long from, long to, boolean earliest) {
    if (height(i) >= 0) {
      return Long.MIN_VALUE;
    }
    long b = bound(k);
    collectTimes(k, i);
    long[] cand = candidates(from, to);
    long found = Long.MIN_VALUE;
    for (long t : cand) {
      load(k, t, i);
      if (active && loadValue > b) {
        found = t;
        if (earliest) {
          return found;
        }
      }
    }
    return found;
  }

  // forced times t in [from, to]: s <= t gives s <= to (upper) or s >= ...
  private boolean forcedReason(
      int i, int k, long from, long to, boolean upperBound, EntryList out) {
    long t = forcedTime(i, k, from, to, upperBound);
    return t != Long.MIN_VALUE && addForced(i, k, t, out);
  }

  // task i must run on machine k at t; with the start bound s <= t it gives the atom
  private boolean addForced(int i, int k, long t, EntryList out) {
    long b = bound(k);
    return addLoad(k, t, i, b + 1, true, out) && addBoundAtom(k, b, out);
  }

  // ---------------------------------------------------------------- loads

  // the times of the other tasks' profile events on machine k, with lower bounds just before pos
  private void collectTimes(int k, int exclude) {
    timeCount = 0;
    for (int j = 0; j < n; j++) {
      if (j == exclude || !possiblyOn(j, k)) {
        continue;
      }
      int smin = trail.minBefore(c.starts[j], pos);
      int smax = trail.maxBefore(c.starts[j], pos);
      add(smin);
      add((long) smax + trail.maxBefore(c.durations[j], pos));
      add(smax);
      add((long) smin + trail.minBefore(c.durations[j], pos));
    }
    Arrays.sort(times, 0, timeCount);
    int w = 0;
    for (int a = 0; a < timeCount; a++) {
      if (w == 0 || times[w - 1] != times[a]) {
        times[w++] = times[a];
      }
    }
    timeCount = w;
  }

  private void add(long t) {
    if (timeCount == times.length) {
      times = Arrays.copyOf(times, 2 * times.length);
    }
    times[timeCount++] = t;
  }

  // the event times in [from, to], with from itself first when it is finite
  private long[] candidates(long from, long to) {
    long[] r = new long[timeCount + 1];
    int count = 0;
    if (from != Long.MIN_VALUE && from <= to) {
      r[count++] = from;
    }
    for (int a = 0; a < timeCount; a++) {
      if (times[a] > from && times[a] <= to || from == Long.MIN_VALUE && times[a] <= to) {
        r[count++] = times[a];
      }
    }
    return Arrays.copyOf(r, count);
  }

  // the least load of the tasks other than exclude on machine k at t, into loadValue and active
  private void load(int k, long t, int exclude) {
    long sum = 0;
    boolean covered = false;
    for (int j = 0; j < n; j++) {
      if (j == exclude) {
        continue;
      }
      if (compulsory(j, k, t)) {
        sum += height(j);
        covered = true;
      } else if (canRun(j, k, t)) {
        sum += Math.min(0, height(j));
      }
    }
    loadValue = sum;
    active = covered;
  }

  /**
   * Adds the atoms that keep the least load of the tasks other than exclude on machine k at t at
   * least needed, with a compulsory part there when mustCover. Compulsory parts with positive
   * heights are kept only while the load needs them, and the tasks kept off the time only while it
   * is short, so that the reason holds as widely as it can.
   */
  private boolean addLoad(
      int k, long t, int exclude, long needed, boolean mustCover, EntryList out) {
    // 0: not counted, 1: compulsory part with a positive height, 2: other compulsory part,
    // 3: may run there with a negative least height, 4: kept off
    int[] role = new int[n];
    long sum = 0;
    int cover = -1;
    for (int j = 0; j < n; j++) {
      if (j == exclude) {
        continue;
      }
      int h = height(j);
      if (compulsory(j, k, t)) {
        role[j] = h > 0 ? 1 : 2;
        sum += h;
        if (h <= 0 && cover < 0) {
          cover = j;
        }
      } else if (h < 0) {
        role[j] = canRun(j, k, t) ? 3 : 4;
        sum += h;
      }
    }
    // keep off the tasks that cannot run there, the largest heights first, while the load is short
    while (sum < needed) {
      int best = -1;
      for (int j = 0; j < n; j++) {
        if (role[j] == 4 && (best < 0 || height(j) < height(best))) {
          best = j;
        }
      }
      if (best < 0) {
        return false;
      }
      sum -= height(best);
      role[best] = 5;
    }
    // drop compulsory parts with positive heights, the smallest first, while the load stays enough
    while (true) {
      int best = -1;
      for (int j = 0; j < n; j++) {
        if (role[j] == 1 && (best < 0 || height(j) < height(best))) {
          best = j;
        }
      }
      if (best < 0 || sum - height(best) < needed) {
        break;
      }
      sum -= height(best);
      role[best] = 6;
    }
    if (mustCover && cover < 0) {
      for (int j = 0; j < n && cover < 0; j++) {
        if (role[j] == 1) {
          cover = j;
        }
      }
      if (cover < 0) {
        // a dropped compulsory part covers the time again
        for (int j = 0; j < n && cover < 0; j++) {
          if (role[j] == 6) {
            cover = j;
            role[j] = 1;
          }
        }
      }
      if (cover < 0) {
        return false;
      }
    }
    for (int j = 0; j < n; j++) {
      int h = height(j);
      boolean ok =
          switch (role[j]) {
            case 1 -> addCompulsory(j, k, t, out) && addHeight(j, h, out);
            case 2 ->
                (j != cover || !mustCover || addCompulsory(j, k, t, out)) && addHeight(j, h, out);
            case 3, 4 -> addHeight(j, h, out);
            case 5 -> addAway(j, k, t, out);
            default -> rootHeight(j) >= 0 || j == exclude || addHeight(j, Math.min(0, h), out);
          };
      if (!ok) {
        return false;
      }
    }
    return true;
  }

  // atoms that keep task j off machine k at t
  private boolean addAway(int j, int k, long t, EntryList out) {
    if (c.present != null && trail.maxBefore(c.present[j], pos) == 0) {
      return addAtom(c.present[j], false, 0, out);
    }
    if (trail.maxBefore(c.durations[j], pos) == 0) {
      return addAtom(c.durations[j], false, 0, out);
    }
    if (excludedAtom(c.machines[j], c.firstMachine + k, out)) {
      return true;
    }
    if (trail.minBefore(c.starts[j], pos) > t) {
      return addAtom(c.starts[j], true, t + 1, out);
    }
    int smax = trail.maxBefore(c.starts[j], pos);
    int dmax = trail.maxBefore(c.durations[j], pos);
    return (long) smax + dmax <= t
        && addAtom(c.starts[j], false, smax, out)
        && addAtom(c.durations[j], false, t - smax, out);
  }

  // task j is present and on machine k, and its compulsory part covers t
  private boolean addCompulsory(int j, int k, long t, EntryList out) {
    int dmin = trail.minBefore(c.durations[j], pos);
    return addPresent(j, out)
        && addMachine(j, k, out)
        && addAtom(c.starts[j], false, t, out)
        && addAtom(c.starts[j], true, t - dmin + 1, out)
        && addAtom(c.durations[j], true, dmin, out);
  }

  // task i is present, on machine k, lasts and has its least height
  private boolean addRunning(int i, int k, EntryList out) {
    return addPresent(i, out)
        && addMachine(i, k, out)
        && addAtom(c.durations[i], true, trail.minBefore(c.durations[i], pos), out)
        && addHeight(i, height(i), out);
  }

  private boolean addPresent(int j, EntryList out) {
    return c.present == null || addAtom(c.present[j], true, 1, out);
  }

  private boolean addMachine(int j, int k, EntryList out) {
    int machine = c.firstMachine + k;
    return addAtom(c.machines[j], true, machine, out)
        && addAtom(c.machines[j], false, machine, out);
  }

  // the height of task j in the upper form is at least h
  private boolean addHeight(int j, long h, EntryList out) {
    return c.upper ? addAtom(c.heights[j], true, h, out) : addAtom(c.heights[j], false, -h, out);
  }

  // the bound of machine k in the upper form is at most b
  private boolean addBoundAtom(int k, long b, EntryList out) {
    return c.upper ? addAtom(c.bounds[k], false, b, out) : addAtom(c.bounds[k], true, -b, out);
  }

  // the weakest atom x >= v (lower) or x <= v before pos; false when it does not hold
  private boolean addAtom(IntVar x, boolean lower, long v, EntryList out) {
    int e = lower ? trail.earliestLowerBound(x, v, pos) : trail.earliestUpperBound(x, v, pos);
    if (e == Integer.MAX_VALUE) {
      return false;
    }
    if (e >= 0) {
      out.add(e);
    }
    return true;
  }

  // ---------------------------------------------------------------- domains just before pos

  private boolean excluded(IntVar x, int v) {
    scratch.clear();
    return trail.excludedBefore(x, v, pos, scratch);
  }

  private boolean excludedAtom(IntVar x, int v, EntryList out) {
    scratch.clear();
    if (!trail.excludedBefore(x, v, pos, scratch)) {
      return false;
    }
    for (int a = 0; a < scratch.size(); a++) {
      out.add(scratch.get(a));
    }
    return true;
  }

  // the atom removes value v
  private static boolean removes(IntVar x, int kind, int value, int v) {
    return switch (kind) {
      case AtomicTrail.GE -> v < value;
      case AtomicTrail.LE -> v > value;
      default -> v == value;
    };
  }

  private boolean surelyPresent(int j) {
    return c.present == null || trail.minBefore(c.present[j], pos) == 1;
  }

  private boolean onlyMachine(int j, int k) {
    int machine = c.firstMachine + k;
    return trail.minBefore(c.machines[j], pos) == machine
        && trail.maxBefore(c.machines[j], pos) == machine;
  }

  private boolean possiblyOn(int j, int k) {
    return (c.present == null || trail.maxBefore(c.present[j], pos) == 1)
        && trail.maxBefore(c.durations[j], pos) > 0
        && !excluded(c.machines[j], c.firstMachine + k);
  }

  private boolean compulsory(int j, int k, long t) {
    return surelyPresent(j)
        && onlyMachine(j, k)
        && trail.maxBefore(c.starts[j], pos) <= t
        && (long) trail.minBefore(c.starts[j], pos) + trail.minBefore(c.durations[j], pos) > t;
  }

  private boolean canRun(int j, int k, long t) {
    return possiblyOn(j, k)
        && trail.minBefore(c.starts[j], pos) <= t
        && (long) trail.maxBefore(c.starts[j], pos) + trail.maxBefore(c.durations[j], pos) > t;
  }

  private int height(int j) {
    return c.upper ? trail.minBefore(c.heights[j], pos) : -trail.maxBefore(c.heights[j], pos);
  }

  private int rootHeight(int j) {
    return c.upper ? trail.rootDomain(c.heights[j]).min() : -trail.rootDomain(c.heights[j]).max();
  }

  private long bound(int k) {
    return c.upper ? trail.maxBefore(c.bounds[k], pos) : -(long) trail.minBefore(c.bounds[k], pos);
  }
}
