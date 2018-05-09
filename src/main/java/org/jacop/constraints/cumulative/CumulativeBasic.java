/*
 * CumulativeBasic.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */


package org.jacop.constraints.cumulative;

import org.jacop.constraints.Constraint;
import org.jacop.core.*;

import java.util.Arrays;
import java.util.BitSet;
import java.util.Comparator;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * CumulativeBasic implements the cumulative constraint using time tabling
 * algorithm.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class CumulativeBasic extends Constraint {

    final private static AtomicInteger idNumber = new AtomicInteger(0);

    private static final boolean debug = false, debugNarr = false;

    private Comparator<Event> eventComparator = ( Event o1, Event o2 ) -> {
            int dateDiff = o1.date() - o2.date();
            return (dateDiff == 0) ? (o1.type() - o2.type()) : dateDiff;
    };

    /**
     * All tasks of the constraint
     */
    final TaskView[] taskNormal;

    /**
     * It specifies the limit of the profile of cumulative use of resources.
     */
    final public IntVar limit;

    /**
     * It specifies whether there possibly exist tasks that have duration or resource variable min value equal zero.
     */
    boolean possibleZeroTasks = false;

    CumulativePrimary cumulativeForConstants = null;

    /**
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     */
    public CumulativeBasic(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit) {

        checkInputForNullness(new String[] {"starts", "durations", "resources", "limit"},
            new Object[][] {starts, durations, resources, {limit}});
        checkInput(durations, i -> i.min() >= 0, "durations can not allow non-negative values");
        checkInput(resources, i -> i.min() >= 0, "resources can not allow non-negative values");

        if (starts.length != durations.length)
            throw new IllegalArgumentException("Cumulative constraint needs to have starts and durations lists the same length.");
        if (starts.length != resources.length)
            throw new IllegalArgumentException("Cumulative constraint needs to have starts and resources lists the same length.");

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
            if (durations[i].min() == 0 || resources[i].min() == 0)
                possibleZeroTasks = true;
        }

        if (grounded(durations) && grounded(resources)) {
            int[] durInt = new int[durations.length];
            for (int i = 0; i < durations.length; i++)
                durInt[i] = durations[i].value();
            int[] resInt = new int[resources.length];
            for (int i = 0; i < resources.length; i++)
                resInt[i] = resources[i].value();

            cumulativeForConstants = new CumulativePrimary(starts, durInt, resInt, limit);
        }

        setScope(Stream.concat(Stream.concat(Arrays.stream(starts), Arrays.stream(durations)),
            Stream.concat(Arrays.stream(resources), Stream.of(limit))));
    }

    /**
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     */
    public CumulativeBasic(List<? extends IntVar> starts, List<? extends IntVar> durations, List<? extends IntVar> resources,
        IntVar limit) {

        this(starts.toArray(new IntVar[starts.size()]), durations.toArray(new IntVar[durations.size()]),
            resources.toArray(new IntVar[resources.size()]), limit);

    }

    @Override public void consistency(Store store) {

        do {

            store.propagationHasOccurred = false;
            profileProp(store);

        } while (store.propagationHasOccurred);

    }

    void profileProp(Store store) {

        if (cumulativeForConstants == null) {
            sweepPruning(store);
            updateTasksRes(store);
        } else
            cumulativeForConstants.sweepPruning(store);

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    private void updateTasksRes(Store store) {
        int limitMax = limit.max();
        for (TaskView t : taskNormal)
            t.res.domain.inMax(store.level, t.res, limitMax);
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : cumulativeBasic([ ");
        for (int i = 0; i < taskNormal.length - 1; i++)
            result.append(taskNormal[i]).append(", ");

        result.append(taskNormal[taskNormal.length - 1]);

        result.append(" ]").append(", limit = ").append(limit).append(" )");

        return result.toString();

    }

    // Sweep algorithm for profile
    private void sweepPruning(Store store) {

        Event[] es = new Event[4 * taskNormal.length];
        int limitMax = limit.max();

        boolean mandatoryExists = false;
        int j = 0;
        int minProfile = Integer.MAX_VALUE, maxProfile = Integer.MIN_VALUE;
        for (int i = 0; i < taskNormal.length; i++) {
            TaskView t = taskNormal[i];
            t.index = i;

            // mandatory task parts to create profile
            int min = t.lst(), max = t.ect();
            if (min < max && t.res.min() > 0) {
                es[j++] = new Event(profile, t, min, t.res.min());
                es[j++] = new Event(profile, t, max, -t.res.min());
                minProfile = (min < minProfile) ? min : minProfile;
                maxProfile = (max > maxProfile) ? max : maxProfile;
                mandatoryExists = true;
            }
        }
        if (!mandatoryExists)
            return;

        for (TaskView t : taskNormal) {
            // overlapping tasks for pruning
            // from start to end
            int min = t.est();
            int max = t.lct();
            if (t.maxNonZero())  // t.dur.max() > 0 && t.res.max() > 0
                if (!(min > maxProfile || max < minProfile)) {
                    es[j++] = new Event(pruneStart, t, min, 0);
                    es[j++] = new Event(pruneEnd, t, max, 0);
                }
        }

        int N = j;
        Arrays.sort(es, 0, N, eventComparator);

        if (debugNarr) {
            System.out.println(Arrays.asList(es));
            System.out.println("limit.max() = " + limitMax);
            System.out.println("===========================");
        }

        BitSet tasksToPrune = new BitSet(taskNormal.length);
        boolean[] inProfile = new boolean[taskNormal.length];

        // current value of the profile for mandatory parts
        int curProfile = 0;

        // used for start variable pruning
        int[] startExcluded = new int[taskNormal.length];
        Arrays.fill(startExcluded, Integer.MAX_VALUE);

        // used for duration variable pruning
        int[] lastBarier = new int[taskNormal.length];
        Arrays.fill(lastBarier, Integer.MAX_VALUE);
        boolean[] startAtEnd = new boolean[taskNormal.length];

        for (int i = 0; i < N; i++) {

            Event e = es[i];
            Event ne = null;  // next event
            if (i < N - 1)
                ne = es[i + 1];

            switch (e.type()) {

                case profile: // =========== profile event ===========

                    curProfile += e.value();
                    inProfile[e.task().index] = (e.value() > 0);

                    if (ne == null || ne.type() != profile || e.date < ne.date()) {
                        // check the tasks for pruning only at the end of all profile events

                        if (debug)
                            System.out.println("Profile at " + e.date() + ": " + curProfile);

                        // prune limit variable
                        if (curProfile > limit.min())
                            limit.domain.inMin(store.level, limit, curProfile);

                        for (int ti = tasksToPrune.nextSetBit(0); ti >= 0; ti = tasksToPrune.nextSetBit(ti + 1)) {
                            TaskView t = taskNormal[ti];

                            int profileValue = curProfile;
                            if (inProfile[ti])
                                profileValue -= t.res.min();

                            // ========= Pruning start variable
                            if (t.exists()) // t.res.min() > 0 && t.dur.min() > 0
                                if (startExcluded[ti] == Integer.MAX_VALUE) {
                                    if (limitMax - profileValue < t.res.min()) {
                                        startExcluded[ti] = e.date() - t.dur.min() + 1;
                                    }
                                } else //startExcluded[ti] != Integer.MAX_VALUE
                                    if (limitMax - profileValue >= t.res.min()) {
                                        // end of excluded interval

                                        if (debugNarr)
                                            System.out.print(
                                                ">>> CumulativeBasic Profile 1. Narrowed " + t.start + " \\ " + new IntervalDomain(
                                                    startExcluded[ti], (e.date() - 1)));

                                        t.start.domain.inComplement(store.level, t.start, startExcluded[ti], e.date() - 1);

                                        if (debugNarr)
                                            System.out.println(" => " + t.start);

                                        startExcluded[ti] = Integer.MAX_VALUE;
                                    }

                            // ========= for duration pruning
                            if (e.date() <= t.start.max())
                                if (limitMax - profileValue < t.res.min())
                                    startAtEnd[ti] = false;
                                else  // limitMax - profileValue >= t.res.min()
                                    startAtEnd[ti] = true;

                            if (lastBarier[ti] == Integer.MAX_VALUE && limitMax - profileValue < t.res.min() && e.date() >= t.start.max())
                                lastBarier[ti] = e.date();

                            // ========= resource pruning;

                            // cannot use more efficient inProfile[ti] (instead of t.lst() <= e.date() && e.date() < t.ect())
                            // since tasks with res = 0 are not in the profile :(
                            if (limit.max() - profileValue < t.res.max() && t.lst() <= e.date() && e.date() < t.ect())
                                t.res.domain.inMax(store.level, t.res, limit.max() - profileValue);
                        }
                    }

                    break;

                case pruneStart:  // =========== start of a task ===========
                    int profileValue = curProfile;
                    TaskView t = e.task();
                    int ti = t.index;

                    if (inProfile[ti])
                        profileValue -= t.res.min();

                    // ========= for start pruning
                    if (t.exists()) // t.res.min() > 0 && t.dur.min() > 0
                        if (limitMax - profileValue < t.res.min()) {
                            startExcluded[ti] = e.date();
                        }

                    // ========= for duration pruning
                    startAtEnd[ti] = true;

                    // ========= resource pruning
                    if (limit.max() - profileValue < t.res.max() && t.lst() <= e.date() && e.date() < t.ect())
                        t.res.domain.inMax(store.level, t.res, limit.max() - profileValue);

                    tasksToPrune.set(ti);
                    break;

                case pruneEnd: // =========== end of a task ===========
                    profileValue = curProfile;
                    t = e.task();
                    ti = t.index;

                    if (inProfile[ti])
                        profileValue -= t.res.min();

                    // ========= pruning start variable
                    if (t.exists())
                        if (startExcluded[ti] != Integer.MAX_VALUE) {
                            // task ends and we remove forbidden area

                            if (debugNarr)
                                System.out.print(
                                    ">>> CumulativeBasic Profile 2. Narrowed " + t.start + " inMax " + (startExcluded[ti] - 1));

                            t.start.domain.inMax(store.level, t.start, startExcluded[ti] - 1);

                            if (debugNarr)
                                System.out.println(" => " + t.start);

                        }

                    startExcluded[ti] = Integer.MAX_VALUE;

                    // ========= resource pruning
                    if (limit.max() - profileValue < t.res.max() && t.lst() <= e.date() && e.date() < t.ect())
                        t.res.domain.inMax(store.level, t.res, limit.max() - profileValue);

                    // ========= duration pruning
                    if (startAtEnd[ti]) {
                        int maxDuration = Integer.MIN_VALUE;
                        Interval lastInterval = null;

                        for (IntervalEnumeration e1 = t.start.dom().intervalEnumeration(); e1.hasMoreElements(); ) {
                            Interval i1 = e1.nextElement();
                            maxDuration = Math.max(maxDuration, i1.max() - i1.min() + t.dur.min());
                            lastInterval = i1;
                        }
                        maxDuration = Math.max(maxDuration, lastBarier[ti] - lastInterval.min());

                        if (maxDuration < t.dur.max()) {
                            if (debugNarr)
                                System.out.print(">>> CumulativeBasic Profile 3. Narrowed " + t.dur + " in 0.." + maxDuration);

                            t.dur.domain.inMax(store.level, t.dur, maxDuration);

                            if (debugNarr)
                                System.out.println(" => " + t.dur);
                        }
                    }

                    tasksToPrune.set(ti, false);
                    break;

                default:
                    throw new RuntimeException("Internal error in " + getClass().getName());
            }
        }
    }

    // event type
    private static final int profile = 0, pruneStart = 1, pruneEnd = 2;


    private static class Event {
        int type;
        TaskView t;
        int date;
        int value;

        Event(int type, TaskView t, int date, int value) {
            this.type = type;
            this.t = t;
            this.date = date;
            this.value = value;
        }

        int date() {
            return date;
        }

        int type() {
            return type;
        }

        int value() {
            return value;
        }

        TaskView task() {
            return t;
        }

        @Override public String toString() {
            String result = "(";
            result += (type == profile) ? "profile, " : (type == pruneStart) ? "pruneStart, " : "pruneEnd, ";
            result += t + ", " + date + ", " + value + ")\n";
            return result;
        }
    }

}
