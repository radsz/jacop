/**
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.constraints.Constraint;

import java.util.BitSet;

/**
 * CumulativeBasic implements the cumulative constraint using time tabling
 * algorithm.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.4
 */

public class CumulativeBasic extends Constraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    static final boolean debug = false, debugNarr = false;

    EventIncComparator<Event> eventComparator = new EventIncComparator<Event>();
  
    Store store;

    /*
     * All tasks of the constraint
     */ TaskView[] taskNormal;

    /**
     * It specifies the limit of the profile of cumulative use of resources.
     */
    public IntVar limit;

    /**
     * It specifies the arguments required to be saved by an XML format as well as
     * the constructor being called to recreate an object from an XML format.
     */
    public static String[] xmlAttributes = {"starts", "durations", "resources", "limit", "doEdgeFinding", "doProfile"};

    /**
     * It creates a cumulative constraint.
     * @param starts variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit the overall limit of resources which has to be used.
     */
    public CumulativeBasic(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit) {

        assert (starts != null) : "Variable in starts list is null";
        assert (durations != null) : "Variable in durations list is null";
        assert (resources != null) : "Variable in resource list is null";
        assert (limit != null) : "Variable limit is null";
        assert (starts.length == durations.length) : "Starts and durations list have different length";
        assert (resources.length == durations.length) : "Resources and durations list have different length";

        this.numberArgs = (short) (numberArgs * 3 + 1);
        this.queueIndex = 2;
        this.numberId = idNumber.incrementAndGet();

        if (starts.length == durations.length && durations.length == resources.length) {

            this.taskNormal = new TaskNormalView[starts.length];

            for (int i = 0; i < starts.length; i++) {

                assert (starts[i] != null) : i + "-th variable in starts list is null";
                assert (durations[i] != null) : i + "-th variable in durations list is null";
                assert (resources[i] != null) : i + "-th variable in resources list is null";
                assert (durations[i].min() >= 0) : i + "-th duration is specified as possibly negative";
                assert (resources[i].min() >= 0) : i + "-th resource consumption is specified as possibly negative";

                if (durations[i].min() >= 0 && resources[i].min() >= 0) {
                    taskNormal[i] = new TaskNormalView(new Task(starts[i], durations[i], resources[i]));
                    taskNormal[i].index = i;
                } else
                    throw new IllegalArgumentException("\nDurations and resources must be >= 0 in cumulative");
            }

            if (limit.min() >= 0) {
                this.limit = limit;
                numberArgs++;
            } else {
                throw new IllegalArgumentException("\nResource limit must be >= 0 in cumulative");
            }
        } else {
            throw new IllegalArgumentException("\nNot equal sizes of Variable vectors in cumulative");
        }
    }

    /**
     * It creates a cumulative constraint.
     * @param starts variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit the overall limit of resources which has to be used.
     */
    public CumulativeBasic(ArrayList<? extends IntVar> starts, ArrayList<? extends IntVar> durations, ArrayList<? extends IntVar> resources,
        IntVar limit) {

        this(starts.toArray(new IntVar[starts.size()]), durations.toArray(new IntVar[durations.size()]),
            resources.toArray(new IntVar[resources.size()]), limit);

    }


    @Override public ArrayList<Var> arguments() {

        ArrayList<Var> variables = new ArrayList<Var>(1);

        for (TaskView t : taskNormal)
            variables.add(t.start);
        for (TaskView t : taskNormal)
            variables.add(t.dur);
        for (TaskView t : taskNormal)
            variables.add(t.res);
        variables.add(limit);
        return variables;
    }

    @Override public void consistency(Store store) {

        do {

            store.propagationHasOccurred = false;

            profileProp();

        } while (store.propagationHasOccurred);

    }

    void profileProp() {

        sweepPruning();
        updateTasksRes(store);

    }


    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        return IntDomain.BOUND;
    }

    @Override public void impose(Store store) {

        for (TaskView t : taskNormal) {
            t.start.putModelConstraint(this, getConsistencyPruningEvent(t.start));
            t.dur.putModelConstraint(this, getConsistencyPruningEvent(t.dur));
            t.res.putModelConstraint(this, getConsistencyPruningEvent(t.res));
        }

        limit.putModelConstraint(this, getConsistencyPruningEvent(limit));

        store.addChanged(this);
        store.countConstraint();

        this.store = store;
    }

    void updateTasksRes(Store store) {
        int limitMax = limit.max();
        for (TaskView t : taskNormal)
            t.res.domain.inMax(store.level, t.res, limitMax);
    }

    @Override public void removeConstraint() {
        for (TaskView t : taskNormal) {
            t.start.removeConstraint(this);
            t.dur.removeConstraint(this);
            t.res.removeConstraint(this);
        }
        limit.removeConstraint(this);
    }

    @Override public boolean satisfied() {

        Task t;
        boolean sat = true;

        // expensive checking
        if (limit.singleton()) {
            int i = 0;
            while (sat && i < taskNormal.length) {
                t = taskNormal[i];
                i++;
                sat = sat && t.start.singleton() && t.dur.singleton() && t.res.singleton();
            }
            return sat;
        } else
            return false;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());

        result.append(" : cumulativeBasic([ ");
        for (int i = 0; i < taskNormal.length - 1; i++)
            result.append(taskNormal[i]).append(", ");

        result.append(taskNormal[taskNormal.length - 1]);

        result.append(" ]").append(", limit = ").append(limit).append(" )");

        return result.toString();

    }

    @Override public void increaseWeight() {
        if (increaseWeight) {
            limit.weight++;
            for (TaskView t : taskNormal) {
                t.dur.weight++;
                t.res.weight++;
                t.start.weight++;
            }
        }
    }

    String intArrayToString(int[] a) {
        StringBuffer result = new StringBuffer("[");

        for (int i = 0; i < a.length; i++) {
            if (i != 0)
                result.append(", ");
            result.append(a[i]);
        }
        result.append("]");

        return result.toString();
    }

    // Sweep algorithm for profile
    void sweepPruning() {

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
                    es[j++] = new Event(pruneStart, t, min, t.res.max());
                    es[j++] = new Event(pruneEnd, t, max, -t.res.max());
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
        Arrays.fill(startAtEnd, false);

        for (int i = 0; i < N; i++) {

            Event e = es[i];
            Event ne = null;  // next event
            if (i < N - 1)
                ne = es[i + 1];

            switch (e.type()) {

                case profile: // =========== profile event ===========

                    curProfile += e.value();
                    inProfile[e.task().index] = (e.value() > 0);

                    if (ne == null || ne.type() != profile || e.date < ne
                        .date()) { // check the tasks for pruning only at the end of all profile events

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

                                        if (!(startExcluded[ti] > t.start.max() || e.date() - 1 < t.start.min())) {

                                            if (debugNarr)
                                                System.out.print(
                                                    ">>> CumulativeBasic Profile 1. Narrowed " + t.start + " \\ " + new IntervalDomain(
                                                        startExcluded[ti], (int) (e.date() - 1)));

                                            t.start.domain.inComplement(store.level, t.start, startExcluded[ti], e.date() - 1);

                                            if (debugNarr)
                                                System.out.println(" => " + t.start);

                                        }
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

                            // ========= resource pruning
                            if (t.lst() <= e.date() && e.date() < t.ect() && limit.max() - profileValue < t.res.max())
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
                    if (t.lst() <= e.date() && e.date() < t.ect() && limit.max() - profileValue < t.res.max())
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
                    if (t.exists()) // t.res.min() > 0 && t.dur.min() > 0
                        if (startExcluded[ti] != Integer.MAX_VALUE) {
                            // task ends and we remove forbidden area

                            if (!(startExcluded[ti] > t.start.max() || e.date() < t.start.min())) {
                                if (debugNarr)
                                    System.out.print(
                                        ">>> CumulativeBasic Profile 2. Narrowed " + t.start + " inMax " + (int) (startExcluded[ti] - 1));

                                t.start.domain.inMax(store.level, t.start, startExcluded[ti] - 1);

                                if (debugNarr)
                                    System.out.println(" => " + t.start);

                            }
                        }

                    startExcluded[ti] = Integer.MAX_VALUE;

                    // ========= resource pruning
                    if (t.lst() <= e.date() && e.date() < t.ect() && limit.max() - profileValue < t.res.max())
                        t.res.domain.inMax(store.level, t.res, limit.max() - profileValue);

                    // ========= duration pruning
                    int maxDuration = Integer.MIN_VALUE;
                    Interval lastInterval = null;

                    for (IntervalEnumeration e1 = t.start.dom().intervalEnumeration(); e1.hasMoreElements(); ) {
                        Interval i1 = e1.nextElement();
                        maxDuration = Math.max(maxDuration, i1.max() - i1.min() + t.dur.min());
                        lastInterval = i1;
                    }
                    if (startAtEnd[ti])
                        maxDuration = Math.max(maxDuration, lastBarier[ti] - lastInterval.min());

                    if (maxDuration < t.dur.max()) {
                        if (debugNarr)
                            System.out.print(">>> CumulativeBasic Profile 3. Narrowed " + t.dur + " in 0.." + maxDuration);

                        t.dur.domain.inMax(store.level, t.dur, maxDuration);

                        if (debugNarr)
                            System.out.println(" => " + t.dur);
                    }

                    tasksToPrune.set(ti, false);
                    break;

	    default:
		    throw new RuntimeException("Internal error in " + getClass().getName());
            }
        }
    }

    // event type
    static final int profile = 0, pruneStart = 1, pruneEnd = 2;


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


  private static class EventIncComparator<T extends Event> implements Comparator<T>, java.io.Serializable {

        EventIncComparator() {
        }

        public int compare(T o1, T o2) {
            return (o1.date() == o2.date()) ? (o1.type() - o2.type()) : (o1.date() - o2.date());
        }
    }
}
