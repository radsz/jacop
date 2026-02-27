/*
 * Cumulative.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.TreeSet;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * Cumulative implements the cumulative/4 constraint using edge-finding algorithm and profile
 * information on the resource use.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Cumulative extends Constraint implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);
  private static final boolean DEBUG = false;
  private static final boolean DEBUG_NARR = false;
  private static boolean debugEnabled = DEBUG;
  private static boolean debugNarrEnabled = DEBUG_NARR;
  private final CumulativeProfiles cumulativeProfiles = new CumulativeProfiles();
  private final Task[] ts;
  private final Comparator<IntDomain> domainMaxComparator = (o1, o2) -> o2.max() - o1.max();
  private final Comparator<IntDomain> domainMinComparator = Comparator.comparingInt(IntDomain::min);
  private final Comparator<Task> taskAscEctComparator = Comparator.comparingInt(Task::ect);
  private final Comparator<Task> taskDescLstComparator = (o1, o2) -> o2.lst() - o1.lst();

  /** It specifies the limit of the profile of cumulative use of resources. */
  private IntVar limit;

  /** It specifies/stores start variables for each corresponding task. */
  private IntVar[] starts;

  /** It specifies/stores duration variables for each corresponding task. */
  private IntVar[] durations;

  /** It specifies/stores resource variable for each corresponding task. */
  private IntVar[] resources;

  /** It specifies if the edge finding algorithm should be used. */
  protected boolean doEdgeFinding;

  /** It specifies if the profiles should be computed to propagate onto limit variable. */
  protected boolean doProfile;

  /** It specifies if the data from profiles should be used to propagate onto limit variable. */
  protected boolean setLimit = true;

  /** It contains information about maximal profile contributed by tasks. */
  private Profile maxProfile;

  /**
   * It contains information about minimal profile contributed by regions for certain occupied by
   * tasks.
   */
  private Profile minProfile;

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param doEdgeFinding true if edge finding algorithm should be used.
   * @param doProfile specifies if the profiles should be computed in order to reduce limit
   *     variable.
   */
  public Cumulative(
      IntVar[] starts,
      IntVar[] durations,
      IntVar[] resources,
      IntVar limit,
      boolean doEdgeFinding,
      boolean doProfile) {

    checkInputForNullness(
        new String[] {"starts", "durations", "resources", "limit"},
        starts,
        durations,
        resources,
        new Object[] {limit});

    checkInput(durations, d -> d.min() >= 0, "duration can not have negative values in the domain");
    checkInput(
        resources,
        r -> r.min() >= 0,
        "resource consumption can not have negative values in the domain");

    if (limit.min() >= 0) {
      this.limit = limit;
    } else {
      throw new IllegalArgumentException("\nResource limit must be >= 0 in cumulative");
    }

    if (starts.length != durations.length) {
      throw new IllegalArgumentException("Starts and durations list have different length");
    }
    if (resources.length != durations.length) {
      throw new IllegalArgumentException("Resources and durations list have different length");
    }

    this.queueIndex = 2;
    this.numberId = idNumber.incrementAndGet();

    this.ts = new Task[starts.length];
    this.starts = Arrays.copyOf(starts, starts.length);
    this.durations = Arrays.copyOf(durations, durations.length);
    this.resources = Arrays.copyOf(resources, resources.length);

    for (int i = 0; i < starts.length; i++) {
      ts[i] = new Task(starts[i], durations[i], resources[i]);
    }

    this.doEdgeFinding = doEdgeFinding;
    this.doProfile = doProfile;

    // check for possible overflow
    for (Task t : ts) {
      Math.multiplyExact(t.start().max() + t.dur().max(), limit.max());
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
   * @param doEdgeFinding true if edge finding algorithm should be used.
   * @param doProfile specifies if the profiles should be computed in order to reduce limit
   *     variable.
   * @param setLimit specifies if limit variable will be prunded.
   */
  public Cumulative(
      IntVar[] starts,
      IntVar[] durations,
      IntVar[] resources,
      IntVar limit,
      boolean doEdgeFinding,
      boolean doProfile,
      boolean setLimit) {

    this(starts, durations, resources, limit, doEdgeFinding, doProfile);
    this.setLimit = setLimit;
  }

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public Cumulative(
      List<? extends IntVar> starts,
      List<? extends IntVar> durations,
      List<? extends IntVar> resources,
      IntVar limit) {

    this(
        starts.toArray(IntVar[]::new),
        durations.toArray(IntVar[]::new),
        resources.toArray(IntVar[]::new),
        limit,
        true,
        true);
  }

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param edgeFinding true if edge finding algorithm should be used.
   */
  public Cumulative(
      List<? extends IntVar> starts,
      List<? extends IntVar> durations,
      List<? extends IntVar> resources,
      IntVar limit,
      boolean edgeFinding) {
    this(starts, durations, resources, limit, edgeFinding, true);
  }

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param edgeFinding true if edge finding algorithm should be used.
   * @param profile specifies if the profiles should be computed in order to reduce limit variable.
   */
  public Cumulative(
      List<? extends IntVar> starts,
      List<? extends IntVar> durations,
      List<? extends IntVar> resources,
      IntVar limit,
      boolean edgeFinding,
      boolean profile) {

    this(
        starts.toArray(IntVar[]::new),
        durations.toArray(IntVar[]::new),
        resources.toArray(IntVar[]::new),
        limit,
        edgeFinding,
        profile);
  }

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public Cumulative(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit) {

    this(starts, durations, resources, limit, true, true);
  }

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param edgeFinding true if edge finding algorithm should be used.
   */
  public Cumulative(
      IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit, boolean edgeFinding) {

    this(starts, durations, resources, limit, edgeFinding, true);
  }

  boolean after(Task l, List<Task> tasks) {

    int startS = IntDomain.MAX_INT;
    long a = 0;
    boolean afterS = true;

    if (!tasks.isEmpty()) {
      if (debugEnabled) {
        log.debug("Checking if {} can be after {}", l, tasks);
      }
      for (Task t : tasks) {
        startS = Math.min(startS, t.est());
        a += t.areaMin();
      }

      afterS = (long) (l.lct() - startS) * limit.max() - a >= l.areaMin();

      if (debugEnabled) {
        log.debug("s(S')= {},  c(l)= {},  a(Sp)= {},  afterS= {}", startS, l.lct(), a, afterS);
      }
    }
    return afterS;
  }

  private boolean before(Task l, List<Task> tasks) {
    int completionS = IntDomain.MIN_INT;
    long a = 0;
    boolean beforeS = true;

    if (!tasks.isEmpty()) {
      if (debugEnabled) {
        log.debug("Checking if {} can be before tasks in {}", l, tasks);
      }
      for (Task t : tasks) {
        completionS = Math.max(completionS, t.lct());
        a += t.areaMin();
      }

      beforeS = (long) (completionS - l.est()) * limit.max() >= a + l.areaMin();

      if (debugEnabled) {
        log.debug(
            "s(l)= {},  c(S')= {},  a(Sp)= {},  beforeS= {}", l.est(), completionS, a, beforeS);
      }
    }
    return beforeS;
  }

  boolean between(Task l, List<Task> tasks) {
    int completionS = IntDomain.MIN_INT;
    int startS = IntDomain.MAX_INT;
    long a = 0;
    long larea;
    boolean betweenS = true;

    if (!tasks.isEmpty()) {
      if (debugEnabled) {
        log.debug("Checking if {} can be between tasks in {}", l, tasks);
      }
      for (Task t : tasks) {
        completionS = Math.max(completionS, t.lct());
        startS = Math.min(startS, t.est());
        a += minOverlap(t, startS, completionS);
      }
      larea = minOverlap(l, startS, completionS);

      betweenS = (long) (completionS - startS) * limit.max() >= a + larea;
      if (debugEnabled) {
        log.debug(
            "s(S')= {},  c(S')= {},  a(Sp)= {}, l_area= {},  betweenS= {}",
            startS,
            completionS,
            a,
            larea,
            betweenS);
      }
    }
    return betweenS;
  }

  @Override
  public void consistency(Store store) {

    do {

      store.propagationHasOccurred = false;

      if (doProfile) {
        propagateUsingProfile(store);
      }

      // max limit is 1 (heuristic) !!!
      if (doEdgeFinding && !store.propagationHasOccurred) {
        // Phase-up - from highest lct down
        edgeFindingUp(store);
        // Phase-down - from lowest est up
        edgeFindingDown(store);
      }

    } while (store.propagationHasOccurred);

    minProfile = null;
    maxProfile = null;
  }

  private void propagateUsingProfile(Store store) {

    cumulativeProfiles.make(ts, setLimit);

    minProfile = cumulativeProfiles.minProfile();
    if (setLimit) {
      maxProfile = cumulativeProfiles.maxProfile();
    }

    if (debugEnabled) {
      log.debug(
          "\n--------------------------------------\nMinProfile for {} :{}\nMaxProfile for {} :{}\n--------------------------------------",
          id(),
          minProfile,
          id(),
          maxProfile);
    }

    if (setLimit) {
      limit.domain.in(store.level, limit, minProfile.max(), maxProfile.max());
    } else if (limit.max() < minProfile.max()) {
      throw Store.failException;
    }

    updateTasksRes(store);

    profileCheckTasks(store);
  }

  private void edgeFindingDown(Store store) {

    TreeSet<IntDomain> estUpList = new TreeSet<>(domainMinComparator);

    if (debugEnabled) {
      log.debug(
          "------------------------------------------------\nEdge Finding Down\n------------------------------------------------");
    }
    for (Task t : ts) {
      if (t.nonZeroTask()) {
        estUpList.add(t.start().dom());
      }
    }

    for (IntDomain est : estUpList) {
      int est0 = est.min();
      if (debugEnabled) {
        log.debug("est0 = {}\n=================", est0);
      }

      List<Task> setS = new ArrayList<>(ts.length);
      List<Task> setL = new ArrayList<>(ts.length);
      for (Task t : ts) {
        if (t.nonZeroTask()) {
          if (t.est() >= est0) {
            setS.add(t);
          } else if (t.lct() > est0) {
            setL.add(t);
          }
        }
      }
      if (debugEnabled) {
        log.debug("S = {}", setS);
        log.debug("L = {}", setL);
      }

      // update upper bound if tt cannot be the last in S
      for (Task t : setS) {
        notLast(store, t, setS);
      }

      if (!setS.isEmpty() && !fitTasksAfter(setS, est0)) {
        throw Store.failException;
      }

      while (!setS.isEmpty() && !setL.isEmpty()) {
        int indexOfl = maxArea(setL);
        Task l = setL.get(indexOfl);
        processDownL(store, setS, setL, indexOfl, l);
      }
    }
  }

  private void processDownL(Store store, List<Task> setS, List<Task> setL, int indexOfl, Task l) {
    int lLct = l.lct();
    final int limitMax = limit.max();
    int startOfS = IntDomain.MAX_INT;
    int completionOfS = IntDomain.MIN_INT;
    long area1 = 0;
    long area2 = 0;
    if (debugEnabled) {
      log.debug("Checking if {} can be after {}", l, setS);
    }
    for (Task t : setS) {
      startOfS = Math.min(startOfS, t.est());
      completionOfS = Math.max(completionOfS, t.lct());
      area1 += t.areaMin();
      area2 += minOverlap(t, startOfS, completionOfS);
    }
    final long totalArea = area1;
    final int estS = startOfS;
    boolean after = (long) (lLct - startOfS) * limitMax - area1 >= l.areaMin();
    long larea = minOverlap(l, startOfS, completionOfS);
    boolean between = (long) (completionOfS - startOfS) * limitMax >= area2 + larea;

    if (after && between) {
      setL.remove(indexOfl);
      removeFromSlct(setS);
    } else if (between) {
      updateDownLBetween(store, setS, setL, indexOfl, l, totalArea, estS, lLct);
    } else if (after) {
      setL.remove(indexOfl);
    } else {
      propagateDownLBefore(store, setS, setL, indexOfl, l);
    }
  }

  private void updateDownLBetween(
      Store store,
      List<Task> setS,
      List<Task> setL,
      int indexOfl,
      Task l,
      long totalArea,
      int estS,
      int lLct) {
    final int limitMax = limit.max();
    final int maxuse = limitMax - l.res().min();
    long slack = (long) (lLct - estS) * limitMax - totalArea - l.areaMin();
    int j = 0;
    Task[] tasks = new Task[setS.size()];
    int tasksLength = 0;
    while (slack < 0 && j < setS.size()) {
      Task t = setS.get(j);
      if (t.res().min() <= maxuse || lLct <= t.lst()) {
        slack += t.areaMin();
      } else {
        tasks[tasksLength++] = t;
      }
      j++;
    }
    if (slack < 0 && tasksLength != 0) {
      Arrays.sort(tasks, 0, tasksLength, taskDescLstComparator);
      j = 0;
      int limitMin = limit.min();
      int compl = lLct;
      while (slack < 0 && j < tasksLength) {
        Task t = tasks[j];
        j++;
        int newCompl = t.lst();
        slack = slack - (long) (compl - newCompl) * limitMin + t.areaMin();
        compl = newCompl;
      }
      int newStartl = compl - l.dur().min();
      if (newStartl < l.lst()) {
        if (debugNarrEnabled) {
          log.debug(
              ">>> Cumulative EF <<< 2. Narrowed {} in {}..{}",
              l.start(),
              IntDomain.MIN_INT,
              newStartl);
        }
        l.start().domain.inMax(store.level, l.start(), newStartl);
      }
    }
    if (before(l, setS)) {
      setL.remove(indexOfl);
    } else {
      removeFromSlct(setS);
    }
  }

  private void propagateDownLBefore(
      Store store, List<Task> setS, List<Task> setL, int indexOfl, Task l) {
    if (debugEnabled) {
      log.debug("after={} between={}!!!", false, false);
    }
    long areaOfS = 0;
    int compl = 0;
    for (Task t : setS) {
      areaOfS += t.areaMin();
      if (t.lct() > compl) {
        compl = t.lct();
      }
    }
    long finish = compl - (areaOfS + l.areaMin()) / limit.max();
    if (l.start().max() > finish) {
      if (debugNarrEnabled) {
        log.debug(
            "{} must be before\n{}\n>>> Cumulative EF <<< 3. Narrowed {} in {}..{}",
            l,
            setS,
            l.start(),
            IntDomain.MIN_INT,
            finish);
      }
      l.start().domain.inMax(store.level, l.start(), (int) finish);
    }
    setL.remove(indexOfl);
  }

  private void edgeFindingUp(Store store) {

    TreeSet<IntDomain> lctDownList = new TreeSet<>(domainMaxComparator);

    if (debugEnabled) {
      log.debug(
          "------------------------------------------------\nEdge Finding Up\n------------------------------------------------");
    }
    for (Task t : ts) {
      if (t.nonZeroTask()) {
        lctDownList.add(t.completion());
      }
    }

    for (IntDomain lct : lctDownList) {

      int lct0 = lct.max();
      if (debugEnabled) {
        log.debug("lct0 = {}\n=================", lct0);
      }

      List<Task> setS = new ArrayList<>(ts.length);
      List<Task> setL = new ArrayList<>(ts.length);
      for (Task t : ts) {
        if (t.nonZeroTask()) {
          if (t.lct() <= lct0) {
            setS.add(t);
          } else if (t.est() < lct0) {
            setL.add(t);
          }
        }
      }
      if (debugEnabled) {
        log.debug("\nS = {}", setS);
        log.debug("L = {}", setL);
      }

      // update lower bound if tt cannot be the first in S
      for (Task t : setS) {
        notFirst(store, t, setS);
      }

      if (!setS.isEmpty() && !fitTasksBefore(setS, lct0)) {
        throw Store.failException;
      }

      while (!setS.isEmpty() && !setL.isEmpty()) {
        int indexOfl = maxArea(setL);
        Task l = setL.get(indexOfl);
        processUpL(store, setS, setL, indexOfl, l);
      }
    }
  }

  private void processUpL(Store store, List<Task> setS, List<Task> setL, int indexOfl, Task l) {
    int lEst = l.est();
    final int limitMax = limit.max();
    int completionOfS = IntDomain.MIN_INT;
    int startOfS = IntDomain.MAX_INT;
    long area1 = 0;
    long area2 = 0;
    if (debugEnabled) {
      log.debug("Checking if {} can be before or between tasks in {}", l, setS);
    }
    for (Task t : setS) {
      completionOfS = Math.max(completionOfS, t.lct());
      startOfS = Math.min(startOfS, t.est());
      area1 += t.areaMin();
      area2 += minOverlap(t, startOfS, completionOfS);
    }
    final long totalArea = area1;
    final int lctS = completionOfS;
    boolean before = (long) (completionOfS - lEst) * limitMax >= area1 + l.areaMin();
    long larea = minOverlap(l, startOfS, completionOfS);
    boolean between = (long) (completionOfS - startOfS) * limitMax >= area2 + larea;

    if (debugEnabled) {
      log.debug(
          "before={} between={} completionOfS={} startOfS={} area2={}  larea={}\nS = {}\nl = {}",
          before,
          between,
          completionOfS,
          startOfS,
          area2,
          larea,
          setS,
          l);
    }

    if (before && between) {
      setL.remove(indexOfl);
      removeFromSest(setS);
    } else if (between) {
      updateUpLBetween(store, setS, setL, indexOfl, l, totalArea, lctS, lEst);
    } else if (before) {
      setL.remove(indexOfl);
    } else {
      propagateUpLAfter(store, setS, setL, indexOfl, l, startOfS);
    }
  }

  private void updateUpLBetween(
      Store store,
      List<Task> setS,
      List<Task> setL,
      int indexOfl,
      Task l,
      long totalArea,
      int lctS,
      int lEst) {
    final int limitMax = limit.max();
    final int maxuse = limitMax - l.res().min();
    long slack = (long) (lctS - lEst) * limitMax - totalArea - l.areaMin();
    int j = 0;
    Task[] tasks = new Task[setS.size()];
    int tasksLength = 0;
    while (slack < 0 && j < setS.size()) {
      Task t = setS.get(j);
      if (t.res().min() <= maxuse || lEst >= t.ect()) {
        slack += t.areaMin();
      } else {
        tasks[tasksLength++] = t;
      }
      j++;
    }
    int newStartl = IntDomain.MIN_INT;
    int startl = lEst;
    if (slack < 0 && tasksLength != 0) {
      Arrays.sort(tasks, 0, tasksLength, taskAscEctComparator);
      j = 0;
      int limitMin = limit.min();
      while (slack < 0 && j < tasksLength) {
        Task t = tasks[j];
        j++;
        newStartl = t.ect();
        slack = slack - (long) (newStartl - startl) * limitMin + t.areaMin();
        startl = newStartl;
      }
    }
    if (newStartl > lEst) {
      if (debugNarrEnabled) {
        log.debug(
            ">>> Cumulative EF <<< 0. Narrowed {} in {}..{}", l.start(), startl, IntDomain.MAX_INT);
      }
      l.start().domain.inMin(store.level, l.start(), newStartl);
    }
    if (after(l, setS)) {
      setL.remove(indexOfl);
    } else {
      removeFromSest(setS);
    }
  }

  private void propagateUpLAfter(
      Store store, List<Task> setS, List<Task> setL, int indexOfl, Task l, int startOfS) {
    if (debugEnabled) {
      log.debug("before={} between={}!!!", false, false);
    }
    long areaOfS = 0;
    for (Task t : setS) {
      areaOfS += t.areaMin();
    }
    int start = startOfS + (int) (areaOfS / limit.max());
    if (start > l.start().min()) {
      if (debugNarrEnabled) {
        log.debug(
            "{} must be after\n{}\n>>> Cumulative EF <<< 1. Narrowed {} in {}..{}",
            l,
            setS,
            l.start(),
            start,
            IntDomain.MAX_INT);
      }
      l.start().domain.inMin(store.level, l.start(), start);
    }
    setL.remove(indexOfl);
  }

  private int est(List<Task> tasks) {
    int estS = IntDomain.MAX_INT;

    for (Task t : tasks) {
      int tEst = t.est();
      if (tEst < estS) {
        estS = tEst;
      }
    }
    return estS;
  }

  private boolean fitTasksAfter(List<Task> s, int est0) {
    int areaS = 0;
    int lctOfS = IntDomain.MIN_INT;
    int minDur = IntDomain.MAX_INT;
    int minRes = IntDomain.MAX_INT;
    boolean fitAfter;

    for (Task t : s) {
      int dur = t.dur().min();
      int res = t.res().min();

      lctOfS = Math.max(lctOfS, t.lct());
      minDur = Math.min(minDur, dur);
      minRes = Math.min(minRes, res);

      areaS += dur * res;
    }

    int limitMax = limit.max();
    long availableArea = (long) (lctOfS - est0) * limitMax;
    if (debugEnabled) {
      log.debug("Fit tasks of {} after {} = {}", s, est0, availableArea >= areaS);
    }
    fitAfter = availableArea >= areaS;

    if (fitAfter) {
      fitAfter = (lctOfS - est0) / minDur * (limitMax / minRes) >= s.size();
    }
    return fitAfter;
  }

  private boolean fitTasksBefore(List<Task> s, int lct0) {
    int areaS = 0;
    int estOfS = IntDomain.MAX_INT;
    int minDur = IntDomain.MAX_INT;
    int minRes = IntDomain.MAX_INT;
    boolean fitBefore;

    for (Task t : s) {
      int dur = t.dur().min();
      int res = t.res().min();

      estOfS = Math.min(estOfS, t.est());
      minDur = Math.min(minDur, dur);
      minRes = Math.min(minRes, res);

      areaS += dur * res;
    }

    int limitMax = limit.max();
    long availableArea = (long) (lct0 - estOfS) * limitMax;
    if (debugEnabled) {
      log.debug(
          "Fit tasks of {} before {} = Available are: {} Area: {}", s, lct0, availableArea, areaS);
    }

    fitBefore = availableArea >= areaS;
    if (fitBefore) {
      fitBefore = (lct0 - estOfS) / minDur * (limitMax / minRes) >= s.size();
    }
    return fitBefore;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  Task[] getTasks() {
    return ts;
  }

  private boolean intervalOverlap(int min1, int max1, int min2, int max2) {
    return min1 < max2 && max1 > min2;
  }

  private int lct(List<Task> tasks) {
    int lctS = IntDomain.MIN_INT;

    for (Task t : tasks) {
      lctS = Math.max(lctS, t.lct());
    }
    return lctS;
  }

  private int maxArea(List<Task> ts) {
    long area = 0;
    int index = 0;

    // Select task with the maximal area
    int i = 0;
    for (Task t : ts) {
      long newArea = t.areaMin();
      if (area < newArea) {
        area = newArea;
        index = i;
      }
      i++;
    }
    return index;
  }

  private long minOverlap(Task t, int est, int lct) {
    int tDurMin = computeMinOverlapDuration(t, est, lct);
    return (long) tDurMin * t.res().min();
  }

  private int computeMinOverlapDuration(Task t, int est, int lct) {
    int tdur = t.dur().min();
    int tect = t.ect();
    int tlst = t.lst();
    if (est <= tlst) {
      return tect >= lct ? Math.min(lct - tlst, tdur) : tdur;
    }
    if (tect <= est) {
      return 0;
    }
    if (tect <= lct) {
      return Math.min(tect - est, tdur);
    }
    return Math.min(lct - est, tdur);
  }

  private void notFirst(Store store, Task s, List<Task> tasks) {
    if (tasks.size() <= 1) {
      return;
    }

    int sEst = s.est();
    long maxuse = (long) limit.max() - s.res().min();
    long slack = computeNotFirstSlack(s, tasks, sEst);

    if (debugEnabled) {
      log.debug("Not first {} in {}", s, tasks);
    }
    int completionS = computeNotFirstCompletionS(s, tasks);
    long a = computeNotFirstArea(s, tasks);
    if (debugEnabled) {
      boolean notBeforeS = slack < 0;
      log.debug(
          "s(l)= {},  c(S')= {},  a(S)= {},  notBeforeS= {}", sEst, completionS, a, notBeforeS);
    }

    Task[] taskArray = new Task[tasks.size() - 1];
    long[] slackHolder = new long[] {slack};
    int tasksLength = fillNotFirstTaskArray(tasks, s, sEst, maxuse, taskArray, slackHolder);

    if (slackHolder[0] < 0 && tasksLength != 0) {
      propagateNotFirstMinStart(store, s, sEst, taskArray, tasksLength, slackHolder[0]);
    }
  }

  private int computeNotFirstCompletionS(Task s, List<Task> tasks) {
    int completionS = IntDomain.MIN_INT;
    for (Task t : tasks) {
      if (t != s) {
        completionS = Math.max(completionS, t.lct());
      }
    }
    return completionS;
  }

  private long sumAreaMinExcluding(Task exclude, List<Task> tasks) {
    long a = 0;
    for (Task t : tasks) {
      if (t != exclude) {
        a += t.areaMin();
      }
    }
    return a;
  }

  private long computeNotFirstArea(Task s, List<Task> tasks) {
    return sumAreaMinExcluding(s, tasks);
  }

  private long computeNotFirstSlack(Task s, List<Task> tasks, int sEst) {
    int completionS = computeNotFirstCompletionS(s, tasks);
    long a = computeNotFirstArea(s, tasks);
    return (long) (completionS - sEst) * limit.max() - a - s.areaMin();
  }

  private int fillNotFirstTaskArray(
      List<Task> tasks, Task s, int sEst, long maxuse, Task[] taskArray, long[] slackHolder) {
    int tasksLength = 0;
    int j = 0;
    while (slackHolder[0] < 0 && j < tasks.size()) {
      Task t = tasks.get(j);
      if (t != s) {
        if (t.res().min() <= maxuse || sEst >= t.ect()) {
          slackHolder[0] += t.areaMin();
        } else {
          taskArray[tasksLength++] = t;
        }
      }
      j++;
    }
    return tasksLength;
  }

  private void propagateNotFirstMinStart(
      Store store, Task s, int sEst, Task[] taskArray, int tasksLength, long slack) {
    Arrays.sort(taskArray, 0, tasksLength, taskAscEctComparator);
    int j = 0;
    int limitMin = limit.min();
    int startl = sEst;
    int newStartl = IntDomain.MIN_INT;
    while (slack < 0 && j < tasksLength) {
      Task t = taskArray[j];
      j++;
      newStartl = t.ect();
      slack = slack - (long) (newStartl - startl) * limitMin + t.areaMin();
      startl = newStartl;
    }
    if (newStartl > sEst) {
      if (debugNarrEnabled) {
        log.debug(
            ">>> Cumulative EF <<< 4. Narrowed {} in {}..{}", s.start(), startl, IntDomain.MAX_INT);
      }
      s.start().domain.inMin(store.level, s.start(), newStartl);
    }
  }

  private void notLast(Store store, Task s, List<Task> tasks) {
    if (tasks.size() <= 1) {
      return;
    }

    int sLct = s.lct();
    long maxuse = (long) limit.max() - s.res().min();
    int startS = computeNotLastStartS(s, tasks);
    long a = computeNotLastArea(s, tasks);
    long slack = (long) (sLct - startS) * limit.max() - a - s.areaMin();

    if (debugEnabled) {
      log.debug("Not last {} in {}", s, tasks);
    }
    if (debugEnabled) {
      boolean notLastInS = slack < 0;
      log.debug("s(S')= {},  c(l)= {},  a(S)= {},  notLastInS= {}", startS, sLct, a, notLastInS);
    }

    Task[] taskArray = new Task[tasks.size() - 1];
    long[] slackHolder = new long[] {slack};
    int tasksLength = fillNotLastTaskArray(tasks, s, sLct, maxuse, taskArray, slackHolder);

    if (slackHolder[0] < 0 && tasksLength != 0) {
      propagateNotLastMaxStart(store, s, sLct, taskArray, tasksLength, slackHolder[0]);
    }
  }

  private int computeNotLastStartS(Task s, List<Task> tasks) {
    int startS = IntDomain.MAX_INT;
    for (Task t : tasks) {
      if (t != s) {
        startS = Math.min(startS, t.est());
      }
    }
    return startS;
  }

  private long computeNotLastArea(Task s, List<Task> tasks) {
    return sumAreaMinExcluding(s, tasks);
  }

  private int fillNotLastTaskArray(
      List<Task> tasks, Task s, int sLct, long maxuse, Task[] taskArray, long[] slackHolder) {
    int tasksLength = 0;
    int j = 0;
    while (slackHolder[0] < 0 && j < tasks.size()) {
      Task t = tasks.get(j);
      if (t != s) {
        if (t.res().min() <= maxuse || sLct <= t.lst()) {
          slackHolder[0] += t.areaMin();
        } else {
          taskArray[tasksLength++] = t;
        }
      }
      j++;
    }
    return tasksLength;
  }

  private void propagateNotLastMaxStart(
      Store store, Task s, int sLct, Task[] taskArray, int tasksLength, long slack) {
    Arrays.sort(taskArray, 0, tasksLength, taskDescLstComparator);
    int j = 0;
    int limitMin = limit.min();
    int compl = sLct;
    while (slack < 0 && j < tasksLength) {
      Task t = taskArray[j];
      j++;
      int newCompl = t.lst();
      slack = slack - (long) (compl - newCompl) * limitMin + t.areaMin();
      compl = newCompl;
    }
    int newStartl = compl - s.dur().min();
    if (newStartl < s.start().max()) {
      if (debugNarrEnabled) {
        log.debug(
            ">>> Cumulative EF <<< 5. Narrowed {} in {}..{}",
            s.start(),
            IntDomain.MIN_INT,
            newStartl);
      }
      s.start().domain.inMax(store.level, s.start(), newStartl);
    }
  }

  private void profileCheckInterval(
      Store store,
      IntVar start,
      IntVar duration,
      Interval i,
      IntVar resources,
      int mustUseMin,
      int mustUseMax) {

    for (ProfileItem p : minProfile) {
      if (debugEnabled) {
        log.debug("Comparing {} with profile item {}", i, p);
      }

      if (intervalOverlap(i.min(), i.max() + duration.min(), p.min, p.max)) {
        if (debugEnabled) {
          log.debug("Overlapping");
        }
        profileCheckOverlapping(store, start, duration, resources, mustUseMin, mustUseMax, p);
      } else {
        profileCheckNonOverlapping(store, start, duration, resources, p);
      }
    }
  }

  private void profileCheckOverlapping(
      Store store,
      IntVar start,
      IntVar duration,
      IntVar resources,
      int mustUseMin,
      int mustUseMax,
      ProfileItem p) {
    if (limit.max() - p.value < resources.min()) {
      if (mustUseMin != -1) {
        profileCheckOverlappingWithMustUse(
            store, start, duration, resources, mustUseMin, mustUseMax, p);
      } else {
        profileNarrowStartFromProfile(store, start, duration, p.min, p.max);
      }
    } else {
      if (mustUseMin != -1 && mustUseMax > p.getMin() && mustUseMin < p.getMax()) {
        int offset =
            intervalOverlap(p.getMin(), p.getMax(), mustUseMin, mustUseMax) ? resources.min() : 0;
        if (debugNarrEnabled) {
          log.debug(
              ">>> Cumulative Profile 8. Narrowed {} in 0..{}",
              resources,
              limit.max() - p.value + offset);
        }
        resources.domain.in(store.level, resources, 0, limit.max() - p.value + offset);
      }
    }
  }

  private void profileCheckOverlappingWithMustUse(
      Store store,
      IntVar start,
      IntVar duration,
      IntVar resources,
      int mustUseMin,
      int mustUseMax,
      ProfileItem p) {
    ProfileItem use = new ProfileItem(mustUseMin, mustUseMax, resources.min());
    ProfileItem left = new ProfileItem();
    ProfileItem right = new ProfileItem();
    p.subtract(use, left, right);

    if (left.min != -1) {
      applyProfileLeftNarrow(store, start, duration, left);
    }
    if (right.min != -1) {
      applyProfileRightNarrow(store, start, duration, right);
    }
    if (start.max() < right.min && start.dom().noIntervals() == 1) {
      int rs = right.min - start.min();
      if (rs < duration.max()) {
        if (debugNarrEnabled) {
          log.debug(">>> Cumulative Profile 9. Narrow {} in 0..{}", duration, rs);
        }
        duration.domain.inMax(store.level, duration, rs);
      }
    }
  }

  private void applyProfileLeftNarrow(
      Store store, IntVar start, IntVar duration, ProfileItem left) {
    int updateMin = left.min - duration.min() + 1;
    int updateMax = left.max - 1;
    if (updateMin <= start.max() && updateMax >= start.min() && updateMin <= updateMax) {
      if (debugNarrEnabled) {
        log.debug(
            ">>> Cumulative Profile 7a. Narrowed {} \\ {} => {}",
            start,
            new IntervalDomain(updateMin, updateMax),
            start);
      }
      start.domain.inComplement(store.level, start, updateMin, updateMax);
    }
  }

  private void applyProfileRightNarrow(
      Store store, IntVar start, IntVar duration, ProfileItem right) {
    int updateMin = right.min - duration.min() + 1;
    int updateMax = right.max - 1;
    if (updateMin <= start.max() && updateMax >= start.min() && updateMin <= updateMax) {
      if (debugNarrEnabled) {
        log.debug(
            ">>> Cumulative Profile 7b. Narrowed {} \\ {} => {}",
            start,
            new IntervalDomain(updateMin, updateMax),
            start);
      }
      start.domain.inComplement(store.level, start, updateMin, updateMax);
    }
  }

  private void profileNarrowStartFromProfile(
      Store store, IntVar start, IntVar duration, int pMin, int pMax) {
    int updateMin = pMin - duration.min() + 1;
    int updateMax = pMax - 1;
    if (updateMin <= start.max() && updateMax >= start.min() && updateMin <= updateMax) {
      if (debugNarrEnabled) {
        log.debug(
            ">>> Cumulative Profile 6. Narrowed {} \\ {} => {}",
            start,
            new IntervalDomain(updateMin, updateMax),
            start);
      }
      start.domain.inComplement(store.level, start, updateMin, updateMax);
    }
  }

  private void profileCheckNonOverlapping(
      Store store, IntVar start, IntVar duration, IntVar resources, ProfileItem p) {
    if (start.max() < p.min && start.dom().noIntervals() == 1) {
      int ps = p.min - start.min();
      if (ps < duration.max() && limit.max() - p.value < resources.min()) {
        if (debugNarrEnabled) {
          log.debug(">>> Cumulative Profile 10. Narrowed {} in 0..{}", duration, ps);
        }
        duration.domain.inMax(store.level, duration, ps);
      }
    }
  }

  private void profileCheckTasks(Store store) {
    IntTask minUse = new IntTask();

    for (Task t : ts) {
      // check only for tasks which cannot allow to have duration or resources = 0
      if (t.nonZeroTask()) {
        int a = -1;
        int b = -1;
        if (t.minUse(minUse)) {
          a = minUse.start();
          b = minUse.stop();
        }

        IntVar resUse = t.res();
        IntVar dur = t.dur();

        if (debugEnabled) {
          log.debug(
              "Start time = {}, resource use = {}, minimal use = {{{}..{}}}",
              t.start(),
              resUse,
              a,
              b);
        }

        IntDomain tStartDom = t.start().dom();

        for (int m = 0; m < tStartDom.noIntervals(); m++) {
          profileCheckInterval(store, t.start(), dur, tStartDom.getInterval(m), resUse, a, b);
        }
      }
    }
  }

  private void removeFromSest(List<Task> s) {
    int estS = est(s);
    int l = s.size();
    int i = 0;
    while (i < l) {
      Task t = s.get(i);
      if (estS == t.est()) {
        s.remove(i);
        l--;
      } else {
        i++;
      }
    }
  }

  private void removeFromSlct(List<Task> s) {
    int lctS = lct(s);
    int l = s.size();
    int i = 0;
    while (i < l) {
      Task t = s.get(i);
      if (lctS == t.lct()) {
        s.remove(i);
        l--;
      } else {
        i++;
      }
    }
  }

  @Override
  public boolean satisfied() {

    // if profile has been computed make a quick check
    if (minProfile != null && maxProfile != null) {
      return (minProfile.max() == maxProfile.max())
          && limit.singleton()
          && minProfile.max() == limit.min();
    } else {
      throw new IllegalStateException(
          "Satisfied function can only be called after call to consistency().");
    }
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : cumulative([ ");
    for (int i = 0; i < ts.length - 1; i++) {
      result.append(ts[i]).append(", ");
    }

    result.append(ts[ts.length - 1]);

    result
        .append(" ]")
        .append(", limit = ")
        .append(limit)
        .append(", ")
        .append(doEdgeFinding)
        .append(", ")
        .append(doProfile)
        .append(" )");

    return result.toString();
  }

  private void updateTasksRes(Store store) {
    int limitMax = limit.max();
    for (Task t : ts) {
      t.res().domain.inMax(store.level, t.res(), limitMax);
    }
  }
}
