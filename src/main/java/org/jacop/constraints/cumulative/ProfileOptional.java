/*
 * ProfileOptional.java
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

// import org.jacop.constraints.Constraint;
import org.jacop.core.*;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Comparator;
import java.util.List;
import java.util.ArrayList;
// import java.util.concurrent.atomic.AtomicInteger;
// import java.util.stream.Stream;

/*
 * ProfileOptional implements the cumulative profile and propagation
 * for optional tasks.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */

public class ProfileOptional {

    boolean debugNarr = false;
    boolean debug = false;
    
    private Comparator<Event> eventComparator = (Event o1, Event o2) -> {
        int dateDiff = o1.date() - o2.date();
        return (dateDiff == 0) ? (o1.type() - o2.type()) : dateDiff;
    };

    /*
     * All tasks of the constraint
     */
    // final TaskView[] taskNormal;

    /**
     * It specifies the limit of the profile of cumulative use of resources.
     */
    private final IntVar limit;

    List<Event> utilizationProfile;

    boolean existsOpt = true;

    /**
     * It creates a profile for optional tasks.
     *
     * @param limit     the overall limit of resources which has to be used.
     */
    public ProfileOptional(IntVar limit) {
        this.limit = limit;
    }

    void updateTasksRes(Store store, TaskView[] ts) {
        int limitMax = limit.max();
        for (TaskView t : ts)
            t.res.domain.inMax(store.level, t.res, limitMax);
    }

    TaskView[] filterOptionalTasks(TaskView[] ts, IntVar[] opt) {

        TaskView[] nonOptionalTasks = new TaskView[ts.length];
        int k = 0;

        for (int i = 0; i < ts.length; i++)
            if (opt[i].min() != 0) {
                nonOptionalTasks[k] = ts[i];
                ts[i].index = k++;
            }

        if (k == 0)
            return null;
        TaskView[] t = new TaskView[k];
        System.arraycopy(nonOptionalTasks, 0, t, 0, k);
        return t;
    }

    @Override public String toString() {

        return "";
    }

    int minStartOpt(TaskView[] ts, IntVar[] opt) {
        existsOpt = false;
        int min = Integer.MAX_VALUE;
        for (int i = 0; i < ts.length; i++) {

            if (min > ts[i].start().min())
                min = ts[i].start().min();

            if (!opt[i].singleton())
                existsOpt = true;
        }
        return min;
    }
    
    // Sweep algorithm for profile
    void sweepPruning(Store store, TaskView[] tn, IntVar[] opt) {

        utilizationProfile = new ArrayList<>();

        TaskView[] ts = filterOptionalTasks(tn, opt);
        if (ts == null)
            return;

        int optMin = minStartOpt(tn, opt);

        Event[] es = new Event[4 * ts.length];
        int limitMax = limit.max();

        int j = 0;
        int minProfile = Integer.MAX_VALUE;
        int maxProfile = Integer.MIN_VALUE;
        for (int i = 0; i < ts.length; i++) {
            TaskView t = ts[i];
            t.index = i;

            // mandatory task parts to create profile
            int min = t.lst();
            int max = t.ect();
            int tResMin = t.res.min();
            if (min < max && tResMin > 0) {
                es[j++] = new Event(profile, t, min, tResMin);
                es[j++] = new Event(profile, t, max, -tResMin);
                minProfile = (min < minProfile) ? min : minProfile;
                maxProfile = (max > maxProfile) ? max : maxProfile;
            }
        }
        if (j == 0)
            return;

        for (TaskView t : ts) {
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

        BitSet tasksToPrune = new BitSet(ts.length);
        boolean[] inProfile = new boolean[ts.length];

        // current value of the profile for mandatory parts
        int curProfile = 0;

        // used for start variable pruning
        int[] startExcluded = new int[ts.length];
        boolean[] startConsidered = new boolean[ts.length];

        // used for duration variable pruning
        int[] maxDuration = new int[ts.length];
        // value Integer.MIN_VALUE for maxDuration means that the
        // duration does not need to be prunned
        Arrays.fill(maxDuration, Integer.MIN_VALUE);
        int[] lastStart = new int[ts.length];
        Arrays.fill(lastStart, Integer.MAX_VALUE);
        int[] lastFree = new int[ts.length];
        Arrays.fill(lastFree, Integer.MAX_VALUE);
        boolean[] barier = new boolean[ts.length];

        int profilePointer = 0;
        if (existsOpt) {
            // System.out.println("%=================");
            utilizationProfile.add(new Event(profile, null, optMin, 0));
        }
        for (int i = 0; i < N; i++) {

            Event e = es[i];
            Event ne = null;  // next event
            if (i < N - 1)
                ne = es[i + 1];

            switch (e.type()) {

                case profile: // =========== profile event ===========

                    // ====> profile to be used by optional tasks
                    if (existsOpt) {
                        // System.out.println("% "+e);

                        Event ce = utilizationProfile.get(profilePointer);
                        if (ce.date() == e.date()) {
                            ce.value += e.value();
                            if (ce.date() > 0
                                && ce.value == utilizationProfile.get(profilePointer - 1).value())
                                utilizationProfile.remove(profilePointer--);
                        } else {
                            utilizationProfile.add(new Event(profile, null, e.date(),
                                                             ce.value() + e.value()));
                            profilePointer++;
                        }
                    }   
                    // <==== profile to be used by optional tasks

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
                            TaskView t = ts[ti];

                            int profileValue = curProfile;
                            if (inProfile[ti])
                                profileValue -= t.res.min();
                            boolean noSpace = limitMax - profileValue < t.res.min();

                            // ========= Pruning start variable
                            if (t.exists()) // t.res.min() > 0 && t.dur.min() > 0
                                if (! startConsidered[ti]) {
                                    if (noSpace) {
                                        startExcluded[ti] = e.date() - t.dur.min() + 1;
                                        startConsidered[ti] = true;
                                    }
                                } else //startExcluded[ti] != Integer.MAX_VALUE
                                    if (! noSpace) {
                                        // end of excluded interval

                                        if (debugNarr)
                                            System.out.print(
                                                ">>> CumulativeBasic Profile 1. Narrowed " + t.start + " \\ " + new IntervalDomain(
                                                    startExcluded[ti], (e.date() - 1)));

                                        t.start.domain.inComplement(store.level, t.start, startExcluded[ti], e.date() - 1);

                                        if (debugNarr)
                                            System.out.println(" => " + t.start);

                                        startConsidered[ti] = false;
                                    }

                            // ========= for duration pruning
                            if (noSpace) {
                                maxDuration[ti] = Math.max(maxDuration[ti], e.date() - lastFree[ti]);
                                barier[ti] = true;
                            } else if (barier[ti]) { // free to go
                                barier[ti] = false;
                                lastFree[ti] = e.date();
                                if (e.date() <= t.start.max()) 
                                    lastStart[ti] = e.date();
                            }

                            // ========= resource pruning;

                            // cannot use more efficient inProfile[ti] (instead of t.lst() <= e.date() && e.date() < t.ect())
                            // since tasks with res = 0 are not in the profile :(
                            if (limitMax - profileValue < t.res.max() && t.lst() <= e.date() && e.date() < t.ect())
                                t.res.domain.inMax(store.level, t.res, limitMax - profileValue);
                        }
                    }

                    break;

                case pruneStart:  // =========== start of a task ===========
                    int profileValue = curProfile;
                    TaskView t = e.task();
                    int ti = t.index;

                    if (inProfile[ti])
                        profileValue -= t.res.min();
                    boolean noSpace = limitMax - profileValue < t.res.min();

                    // ========= for start pruning
                    if (t.exists()) // t.res.min() > 0 && t.dur.min() > 0
                        if (noSpace) {
                            startExcluded[ti] = e.date();
                            startConsidered[ti] = true;
                        }

                    // ========= for duration pruning
                    if (noSpace)
                        barier[ti] = true;
                    else {
                        lastStart[ti] = t.start.min();
                        lastFree[ti] = t.start.min();
                        barier[ti] = false;
                    }

                    // ========= resource pruning
                    if (limitMax - profileValue < t.res.max() && t.lst() <= e.date() && e.date() < t.ect())
                        t.res.domain.inMax(store.level, t.res, limitMax - profileValue);

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
                        if (startConsidered[ti]) {
                            // task ends and we remove forbidden area

                            if (debugNarr)
                                System.out
                                    .print(">>> CumulativeBasic Profile 2. Narrowed " + t.start + " inMax " + (startExcluded[ti] - 1));

                            t.start.domain.inMax(store.level, t.start, startExcluded[ti] - 1);

                            if (debugNarr)
                                System.out.println(" => " + t.start);

                        }

                    startConsidered[ti] = false;

                    // ========= resource pruning
                    if (limitMax - profileValue < t.res.max() && t.lst() <= e.date() && e.date() < t.ect())
                        t.res.domain.inMax(store.level, t.res, limitMax - profileValue);

                    // ========= duration pruning
                    if (lastStart[ti] >= lastFree[ti] && limitMax - profileValue >= t.res.min())
                            maxDuration[ti] = Math.max(maxDuration[ti], e.date() - lastStart[ti]);

                    if (lastStart[ti] == Integer.MAX_VALUE)  // no room for the task; must have 0 duration
                        maxDuration[ti] = 0;

                    if (maxDuration[ti] != Integer.MIN_VALUE && maxDuration[ti] < t.dur.max()) {
                        if (debugNarr)
                            System.out.print(">>> CumulativeBasic Profile 3. Narrowed " + t.dur + " in 0.." + maxDuration[ti]);

                        t.dur.domain.inMax(store.level, t.dur, maxDuration[ti]);

                        if (debugNarr)
                            System.out.println(" => " + t.dur);
                    }

                    tasksToPrune.set(ti, false);
                    break;

                default:
                    throw new RuntimeException("Internal error in " + getClass().getName());
            }
        }

        if (existsOpt)
            pruneOpt(store, tn, opt);
    }

    void pruneOpt(Store store, TaskView[] tn, IntVar[] opt) {

        int limit = this.limit.max();
        int n = utilizationProfile.size();

        L1: for (int i = 0; i < tn.length; i++) {
            if (!opt[i].singleton()) {
                int dur = tn[i].dur().min();
                int res = tn[i].res().min();
                int sMin = tn[i].start().min();
                int sMax = tn[i].start().max();

                boolean ok = false;
                for (int j = 0; j < n; j++) {
                    Event e = utilizationProfile.get(j);
                    int t = e.date();
                    int u = e.value();

                    if (sMin + dur <= t) {
                        ok = true;
                        break;
                    }
                    if (u + res > limit && j + 1 < n) {
                            sMin =  utilizationProfile.get(j + 1).date();
                            if (sMin > sMax) {
                                opt[i].domain.in(store.level, opt[i], 0, 0);
                                continue L1;
                            }
                    }
                }
                if (sMax > utilizationProfile.get(n - 1).date())
                    continue;

                if (!ok) {
                    opt[i].domain.in(store.level, opt[i], 0, 0);
                }
            }
        }
    }
    
    // event type
    private static final int profile = 0;
    private static final int pruneStart = 1;
    private static final int pruneEnd = 2;


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
            result += t + ", " + date + ", " + value + ")";
            return result;
        }
    }
}
