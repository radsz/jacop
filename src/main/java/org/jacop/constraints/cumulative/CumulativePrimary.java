/*
 * CumulativePrimary.java
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
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Comparator;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/*
 * CumulativePrimary implements the cumulative constraint using time tabling
 * algorithm.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */

class CumulativePrimary extends Constraint {

    private static AtomicInteger idNumber = new AtomicInteger(0);

    private static final boolean debug = false;
    private static final boolean debugNarr = false;

    private Comparator<Event> eventComparator = (o1, o2) -> {
        int dateDiff = o1.date() - o2.date();
        return (dateDiff == 0) ? (o1.type() - o2.type()) : dateDiff;
    };

    /*
     * start times of tasks
     */
    private final IntVar[] start;

    /*
     * All durations and resources of the constraint
     */
    private final int[] dur;
    private final int[] res;

    private int[] activeMap;
    private TimeStamp<Integer> activePnt;

    /*
     * It specifies the limit of the profile of cumulative use of resources.
     */
    public final IntVar limit;

    /*
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     */
    public CumulativePrimary(IntVar[] starts, int[] durations, int[] resources, IntVar limit) {

        checkInputForNullness(new String[] {"starts", "durations", "resources", "limit"},
            new Object[][] {starts, {durations}, {resources}, {limit}});
        checkInput(durations, i -> i > 0, "durations must be greater than 0");
        checkInput(resources, i -> i > 0, "resources must be greater than 0");

        if (starts.length != durations.length)
            throw new IllegalArgumentException("Cumulative constraint needs to have starts and durations lists the same length.");
        if (starts.length != resources.length)
            throw new IllegalArgumentException("Cumulative constraint needs to have starts and resources lists the same length.");

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
        activeMap = new int[start.length];
        for (int i = 0; i < start.length; i++)
            activeMap[i] = i;

        setScope(Stream.concat(Arrays.stream(starts), Stream.of(limit)));

        activePnt = new TimeStamp<Integer>(starts[0].getStore(), 0);

    }

    /*
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     */
    public CumulativePrimary(List<? extends IntVar> starts, List<? extends Integer> durations, List<? extends Integer> resources,
        IntVar limit) {

        this(starts.toArray(new IntVar[starts.size()]), durations.stream().mapToInt(i -> i).toArray(),
            resources.stream().mapToInt(i -> i).toArray(), limit);

    }

    @Override public void consistency(Store store) {

        do {

            store.propagationHasOccurred = false;

            sweepPruning(store);

        } while (store.propagationHasOccurred);

    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : cumulativePrimary([ ");
        for (int i = 0; i < start.length - 1; i++)
            result.append("[").append(start[i]).append(", ").append(dur[i]).append(", ").append(res[i]).append("], ");

        result.append("[").append(start[start.length - 1]).append(", ").append(dur[start.length - 1]).append(", ")
            .append(res[start.length - 1]).append("]");

        result.append(" ]").append(", limit = ").append(limit).append(" )");

        return result.toString();

    }

    // Sweep algorithm for profile
    void sweepPruning(Store store) {

        Event[] es = new Event[4 * start.length];
        int limitMax = limit.max();

        int j = 0;
        int minProfile = Integer.MAX_VALUE;
        int maxProfile = Integer.MIN_VALUE;
        int first = activePnt.value();
        for (int i = first; i < start.length; i++) {
            int k = activeMap[i];

            // mandatory task parts to create profile
            int min = start[k].max(); // t.lst()
            int max = start[k].min() + dur[k];  // t.ect()
            if (min < max) {
                es[j++] = new Event(profile, k, min, res[k]);
                es[j++] = new Event(profile, k, max, -res[k]);
                minProfile = (min < minProfile) ? min : minProfile;
                maxProfile = (max > maxProfile) ? max : maxProfile;
            }
        }
        if (j == 0)  // no mandatory parts
            return;

        for (int i = first; i < start.length; i++) {
            // overlapping tasks for pruning
            // from start to end
            int k = activeMap[i];

            if (!start[k].singleton()) {  // task that are ground are considered for manadatory tasks
                int min = start[k].min(); //t.est();
                int max = start[k].max() + dur[k]; //t.lct();
                if (!(min > maxProfile || max < minProfile)) {
                    es[j++] = new Event(pruneStart, k, min, 0); // res[i]);
                    es[j++] = new Event(pruneEnd, k, max, 0);   // -res[i]);
                }
            }
        }

        int N = j;
        Arrays.sort(es, 0, N, eventComparator);

        if (debugNarr) {
            System.out.println(Arrays.asList(es));
            System.out.println("limit.max() = " + limitMax);
            System.out.println("===========================");
        }

        BitSet tasksToPrune = new BitSet(start.length);
        boolean[] inProfile = new boolean[start.length];

        // current value of the profile for mandatory parts
        int curProfile = 0;

        // used for start variable pruning
        int[] startExcluded = new int[start.length];
        boolean[] startConsidered = new boolean[start.length];

        for (int i = 0; i < N; i++) {

            Event e = es[i];
            Event ne = null;  // next event
            if (i < N - 1)
                ne = es[i + 1];

            switch (e.type()) {

                case profile: // =========== profile event ===========

                    curProfile += e.value();
                    inProfile[e.index] = (e.value() > 0);

                    if (ne == null || ne.type() != profile || e.date < ne.date()) {
                        // check the tasks for pruning only at the end of all profile events

                        if (debug)
                            System.out.println("Profile at " + e.date() + ": " + curProfile);

                        // prune limit variable
                        if (curProfile > limit.min())
                            limit.domain.inMin(store.level, limit, curProfile);

                        for (int ti = tasksToPrune.nextSetBit(0); ti >= 0; ti = tasksToPrune.nextSetBit(ti + 1)) {

                            // ========= Pruning start variable
                            if (! startConsidered[ti]) {
                                if (!inProfile[ti] && limitMax - curProfile < res[ti]) {
                                    startExcluded[ti] = e.date() - dur[ti] + 1;
                                    startConsidered[ti] = true;
                                }
                            } else //startExcluded[ti] != Integer.MAX_VALUE
                                if (inProfile[ti] || limitMax - curProfile >= res[ti]) {
                                    // end of excluded interval

                                    if (debugNarr)
                                        System.out.print(
                                            ">>> CumulativePrimary Profile 1. Narrowed " + start[ti] + " \\ " + new IntervalDomain(
                                                startExcluded[ti], e.date() - 1));

                                    start[ti].domain.inComplement(store.level, start[ti], startExcluded[ti], e.date() - 1);

                                    if (debugNarr)
                                        System.out.println(" => " + start[ti]);

                                    startConsidered[ti] = false;
                                }
                        }
                    }

                    break;

                case pruneStart:  // =========== start of a task ===========
                    int ti = e.index;

                    // ========= for start pruning
                    if (!inProfile[ti] && limitMax - curProfile < res[ti]) {
                        startExcluded[ti] = e.date();
                        startConsidered[ti] = true;
                    }

                    tasksToPrune.set(ti);
                    break;

                case pruneEnd: // =========== end of a task ===========
                    ti = e.index;

                    // ========= pruning start variable
                    if (startConsidered[ti]) {
                        // task ends and we remove forbidden area

                        if (debugNarr)
                            System.out
                                .print(">>> CumulativePrimary Profile 2. Narrowed " + start[ti] + " inMax " + (startExcluded[ti] - 1));

                        start[ti].domain.inMax(store.level, start[ti], startExcluded[ti] - 1);

                        if (debugNarr)
                            System.out.println(" => " + start[ti]);

                    }

                    startConsidered[ti] = false;

                    tasksToPrune.set(ti, false);
                    break;

                default:
                    throw new RuntimeException("Internal error in " + getClass().getName());
            }
        }

        if (!store.propagationHasOccurred)
            removeNotUsedProfleTasks();

    }

    private void removeNotUsedProfleTasks() {

        // remove ground tasks that make profile but do not contribute
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
                minPrune = (min < minPrune) ? min : minPrune;
                maxPrune = (max > maxPrune) ? max : maxPrune;
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

    // event type
    private static final int profile = 0;
    private static final int pruneStart = 1;
    private static final int pruneEnd = 2;


    private static class Event {
        int type;
        int index;
        int date;
        int value;

        Event(int type, int t, int date, int value) {
            this.type = type;
            this.index = t;
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

        int task() {
            return index;
        }

        @Override public String toString() {
            String result = "(";
            result += (type == profile) ? "profile, " : (type == pruneStart) ? "pruneStart, " : "pruneEnd, ";
            result += index + ", " + date + ", " + value + ")\n";
            return result;
        }
    }

}
