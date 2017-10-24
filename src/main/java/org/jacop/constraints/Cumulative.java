/*
 * Cumulative.java
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


package org.jacop.constraints;

import org.jacop.api.SatisfiedPresent;
import org.jacop.core.*;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * Cumulative implements the cumulative/4 constraint using edge-finding
 * algorithm and profile information on the resource use.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Cumulative extends Constraint implements SatisfiedPresent {

    static AtomicInteger idNumber = new AtomicInteger(0);

    private static final boolean debug = false, debugNarr = false;

    /**
     * It contains information about maximal profile contributed by tasks.
     */
    private Profile maxProfile = null;

    /**
     * It contains information about minimal profile contributed by regions
     * for certain occupied by tasks.
     */
    private Profile minProfile = null;

    private CumulativeProfiles cumulativeProfiles = new CumulativeProfiles();

    private Task Ts[];

    /**
     * It specifies if the edge finding algorithm should be used.
     */
    private boolean doEdgeFinding = true;

    /**
     * It specifies if the profiles should be computed to propagate
     * onto limit variable.
     */
    private boolean doProfile = true;

    /**
     * It specifies if the data from profiles should be used to propagate
     * onto limit variable.
     */
    private boolean setLimit = true;

    /**
     * It specifies the limit of the profile of cumulative use of resources.
     */
    public IntVar limit;

    /**
     * It specifies/stores start variables for each corresponding task.
     */
    public IntVar[] starts;

    /**
     * It specifies/stores duration variables for each corresponding task.
     */
    public IntVar[] durations;

    /**
     * It specifies/stores resource variable for each corresponding task.
     */
    public IntVar[] resources;

    private Comparator<IntDomain> domainMaxComparator = (o1, o2) -> (o2.max() - o1.max());

    private Comparator<IntDomain> domainMinComparator = (o1, o2) -> (o1.min() - o2.min());

    private Comparator<Task> taskAscEctComparator = (o1, o2) -> (o1.ect() - o2.ect());

    private Comparator<Task> taskDescLstComparator = (o1, o2) -> (o2.lst() - o1.lst());

    /**
     * It creates a cumulative constraint.
     *
     * @param starts        variables denoting starts of the tasks.
     * @param durations     variables denoting durations of the tasks.
     * @param resources     variables denoting resource usage of the tasks.
     * @param limit         the overall limit of resources which has to be used.
     * @param doEdgeFinding true if edge finding algorithm should be used.
     * @param doProfile     specifies if the profiles should be computed in order to reduce limit variable.
     */
    public Cumulative(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit, boolean doEdgeFinding, boolean doProfile) {

        checkInputForNullness(new String[] {"starts", "durations", "resources", "limit"},
                              new Object[][] { starts,   durations,   resources, { limit } });

        checkInput(durations, d -> d.min() >= 0, "duration can not have negative values in the domain" );
        checkInput(resources, r -> r.min() >= 0, "resource consumption can not have negative values in the domain" );

        if (limit.min() >= 0) {
            this.limit = limit;
        } else {
            throw new IllegalArgumentException("\nResource limit must be >= 0 in cumulative");
        }

        assert (starts.length == durations.length) : "Starts and durations list have different length";
        assert (resources.length == durations.length) : "Resources and durations list have different length";

        this.queueIndex = 2;
        this.numberId = idNumber.incrementAndGet();

        if (starts.length == durations.length && durations.length == resources.length) {

            this.Ts = new Task[starts.length];
            this.starts = Arrays.copyOf(starts, starts.length);
            this.durations = Arrays.copyOf(durations, durations.length);
            this.resources = Arrays.copyOf(resources, resources.length);

            for (int i = 0; i < starts.length; i++) {
                Ts[i] = new Task(starts[i], durations[i], resources[i]);
            }

        } else {
            throw new IllegalArgumentException("\nNot equal sizes of Variable vectors in cumulative");
        }

        this.doEdgeFinding = doEdgeFinding;
        this.doProfile = doProfile;

        // check for possible overflow
        for (Task t : Ts)
            Math.multiplyExact((t.start.max() + t.dur.max()), limit.max());

        setScope(Stream.concat(Stream.concat(Arrays.stream(starts), Arrays.stream(durations)),
            Stream.concat(Arrays.stream(resources), Stream.of(limit))));

    }

    /**
     * It creates a cumulative constraint.
     *
     * @param starts        variables denoting starts of the tasks.
     * @param durations     variables denoting durations of the tasks.
     * @param resources     variables denoting resource usage of the tasks.
     * @param limit         the overall limit of resources which has to be used.
     * @param doEdgeFinding true if edge finding algorithm should be used.
     * @param doProfile     specifies if the profiles should be computed in order to reduce limit variable.
     * @param setLimit      specifies if limit variable will be prunded.
     */
    public Cumulative(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit, boolean doEdgeFinding, boolean doProfile,
        boolean setLimit) {

        this(starts, durations, resources, limit, doEdgeFinding, doProfile);
        this.setLimit = setLimit;

    }

    /**
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     */
    public Cumulative(List<? extends IntVar> starts, List<? extends IntVar> durations, List<? extends IntVar> resources,
        IntVar limit) {

        this(starts.toArray(new IntVar[starts.size()]), durations.toArray(new IntVar[durations.size()]),
            resources.toArray(new IntVar[resources.size()]), limit, true, true);

    }

    /**
     * It creates a cumulative constraint.
     *
     * @param starts      variables denoting starts of the tasks.
     * @param durations   variables denoting durations of the tasks.
     * @param resources   variables denoting resource usage of the tasks.
     * @param limit       the overall limit of resources which has to be used.
     * @param edgeFinding true if edge finding algorithm should be used.
     */

    public Cumulative(List<? extends IntVar> starts, List<? extends IntVar> durations, List<? extends IntVar> resources,
        IntVar limit, boolean edgeFinding) {
        this(starts, durations, resources, limit, edgeFinding, true);
    }

    /**
     * It creates a cumulative constraint.
     *
     * @param starts      variables denoting starts of the tasks.
     * @param durations   variables denoting durations of the tasks.
     * @param resources   variables denoting resource usage of the tasks.
     * @param limit       the overall limit of resources which has to be used.
     * @param edgeFinding true if edge finding algorithm should be used.
     * @param profile     specifies if the profiles should be computed in order to reduce limit variable.
     */


    public Cumulative(List<? extends IntVar> starts, List<? extends IntVar> durations, List<? extends IntVar> resources,
        IntVar limit, boolean edgeFinding, boolean profile) {

        this(starts.toArray(new IntVar[starts.size()]), durations.toArray(new IntVar[durations.size()]),
            resources.toArray(new IntVar[resources.size()]), limit, edgeFinding, profile);
    }

    /**
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     */
    public Cumulative(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit) {

        this(starts, durations, resources, limit, true, true);
    }

    /**
     * It creates a cumulative constraint.
     *
     * @param starts      variables denoting starts of the tasks.
     * @param durations   variables denoting durations of the tasks.
     * @param resources   variables denoting resource usage of the tasks.
     * @param limit       the overall limit of resources which has to be used.
     * @param edgeFinding true if edge finding algorithm should be used.
     */

    public Cumulative(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit, boolean edgeFinding) {

        this(starts, durations, resources, limit, edgeFinding, true);

    }



    boolean after(Task l, List<Task> S) {

        int startS = IntDomain.MaxInt;
        long a = 0;
        boolean afterS = true;

        if (S.size() > 0) {
            if (debug)
                System.out.println("Checking if " + l + " can be after " + S);
            for (Task t : S) {
                startS = Math.min(startS, t.est());
                a += t.areaMin();
            }

            afterS = ((l.lct() - startS) * limit.max() - a >= l.areaMin());

            if (debug)
                System.out.println("s(S')= " + startS + ",  c(l)= " + l.lct() + ",  a(Sp)= " + a + ",  afterS= " + afterS);
        }
        return afterS;
    }

    private boolean before(Task l, List<Task> S) {
        int completionS = IntDomain.MinInt;
        int a = 0;
        boolean beforeS = true;

        if (S.size() > 0) {
            if (debug)
                System.out.println("Checking if " + l.toString() + " can be before tasks in " + S.toString());
            for (Task t : S) {
                completionS = Math.max(completionS, t.lct());
                a += t.areaMin();
            }

            beforeS = ((completionS - l.est()) * limit.max() >= a + l.areaMin());

            if (debug)
                System.out.println("s(l)= " + l.est() + ",  c(S')= " + completionS + ",  a(Sp)= " + a + ",  beforeS= " + beforeS);
        }
        return beforeS;
    }

    boolean between(Task l, List<Task> S) {
        int completionS = IntDomain.MinInt, startS = IntDomain.MaxInt;
        long a = 0, larea = 0;
        boolean betweenS = true;

        if (S.size() > 0) {
            if (debug)
                System.out.println("Checking if " + l + " can be between tasks in " + S);
            for (Task t : S) {
                completionS = Math.max(completionS, t.lct());
                startS = Math.min(startS, t.est());
                a += minOverlap(t, startS, completionS);
            }
            larea = minOverlap(l, startS, completionS);

            betweenS = ((completionS - startS) * limit.max() >= a + larea);
            if (debug)
                System.out.println(
                    "s(S')= " + startS + ",  c(S')= " + completionS + ",  a(Sp)= " + a + ", l_area= " + larea + ",  betweenS= " + betweenS);
        }
        return betweenS;
    }

    @Override public void consistency(Store store) {


        do {

            store.propagationHasOccurred = false;

            if (doProfile) {

                cumulativeProfiles.make(Ts, setLimit);

                minProfile = cumulativeProfiles.minProfile();
                if (setLimit)
                    maxProfile = cumulativeProfiles.maxProfile();

                if (debug)
                    System.out.println(
                        "\n--------------------------------------" + "\nMinProfile for " + id() + " :" + minProfile + "\nMaxProfile for "
                            + id() + " :" + maxProfile + "\n--------------------------------------");

                if (setLimit)
                    limit.domain.in(store.level, limit, minProfile.max(), maxProfile.max());
                else if (limit.max() < minProfile.max())
                    throw Store.failException;

                updateTasksRes(store);

                profileCheckTasks(store);
            }

            // Do edge finding only the last time and when
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

    private void edgeFindingDown(Store store) {

        TreeSet<IntDomain> estUpList = new TreeSet<>(domainMinComparator);

        if (debug)
            System.out.println("------------------------------------------------\n" + "Edge Finding Down\n"
                + "------------------------------------------------");
        for (Task t : Ts)
            if (t.nonZeroTask())
                estUpList.add(t.start.dom());

        for (IntDomain est : estUpList) {
            int est0 = est.min();
            if (debug)
                System.out.println("est0 = " + est0 + "\n=================");

            // Create S = {t|EST(t) >= est0}
            // Create L = {t|EST(t) < est0 && LCT(t) > est0}
            List<Task> S = new ArrayList<Task>(Ts.length), L = new ArrayList<Task>(Ts.length);
            for (Task t : Ts) {
                if (t.nonZeroTask()) {
                    if (t.est() >= est0)
                        S.add(t);
                    else if (t.lct() > est0) // tt.est() < est0 && 
                        L.add(t);
                }
            }
            if (debug) {
                System.out.println("S = " + S);
                System.out.println("L = " + L);
            }

            // update upper bound if tt cannot be the last in S
            for (Task t : S)
                notLast(store, t, S);

            if (S.size() != 0 && !fitTasksAfter(S, est0))
                throw Store.failException;

            while (S.size() != 0 && L.size() != 0) {
                // Select task l from L with the maximal area
                int indexOfl = maxArea(L);
                Task l = L.get(indexOfl);
                int l_LCT = l.lct();
                int limitMax = limit.max();
                // System.out.println("Maxumum area task= " + l);
                // Checking if l can be between and after S

                boolean after = true, between = true;

                int startOfS = IntDomain.MaxInt, completionOfS = IntDomain.MinInt;
                long area1 = 0, area2 = 0, larea = 0;
                if (debug)
                    System.out.println("Checking if " + l + " can be after " + S);
                for (Task t : S) {
                    startOfS = Math.min(startOfS, t.est());
                    completionOfS = Math.max(completionOfS, t.lct());
                    area1 += t.areaMin();
                    area2 += minOverlap(t, startOfS, completionOfS);
                }
                long totalArea = area1;
                int estS = startOfS;
                after = ((l_LCT - startOfS) * limitMax - area1 >= l.areaMin());

                // larea = l.dur.min()*l.res.min();
                larea = minOverlap(l, startOfS, completionOfS);
                between = ((completionOfS - startOfS) * limitMax >= area2 + larea);

                if (after && between) {
                    L.remove(indexOfl);
                    removeFromS_Lct(S);
                } else {
                    if (between && !after) {
                        // update upper bound of l
                        long slack, a = 0;
                        int newCompl = IntDomain.MaxInt, startS, newStartl = IntDomain.MinInt;
                        int maxuse = limitMax - l.res.min();

                        int compl = l_LCT;
                        a = totalArea;
                        startS = estS;
                        slack = (l_LCT - startS) * limitMax - a - l.areaMin();

                        int j = 0;
                        Task[] tasks = new Task[S.size()];
                        int tasksLength = 0;
                        while (slack < 0 && j < S.size()) {
                            Task t = S.get(j);

                            if (t.res.min() <= maxuse || l_LCT <= t.lst()) {
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
                            while (slack < 0 && j < tasksLength) {
                                Task t = tasks[j];
                                j++;
                                newCompl = t.lst();
                                slack = slack - (compl - newCompl) * limitMin + t.areaMin();
                                compl = newCompl;
                            }

                            newStartl = compl - l.dur.min();
                            if (newStartl < l.lst()) {
                                if (debugNarr)
                                    System.out.println(
                                        ">>> Cumulative EF <<< 2. Narrowed " + l.start + " in " + IntDomain.MinInt + ".." + newStartl);

                                l.start.domain.inMax(store.level, l.start, newStartl);

                            }
                        }

                        if (before(l, S))
                            L.remove(indexOfl);
                        else
                            removeFromS_Lct(S);
                    } else {
                        if (!between && after)
                            L.remove(indexOfl);
                        else {
                            // ! between && ! after => before
                            // l must be before S
                            // update upper bound of l.Start and l.Dur

                            if (debug)
                                System.out.println("after=" + after + " between=" + between + "!!!");

                            int areaOfS = 0;
                            int compl = 0;
                            for (Task t : S) {
                                areaOfS += t.areaMin();
                                if (t.lct() > compl) {
                                    compl = t.lct();
                                }
                            }

                            long finish = compl - (areaOfS + l.areaMin()) / limit.max();
                            if (l.start.max() > finish) {
                                if (debugNarr)
                                    System.out.println(
                                        l + " must be before\n" + S + "\n>>> Cumulative EF <<< 3. Narrowed " + l.start + " in "
                                            + IntDomain.MinInt + ".." + finish);

                                l.start.domain.inMax(store.level, l.start, (int) finish);
                            }

                            L.remove(indexOfl);
                        }
                    }
                }
            }
        }
    }

    private void edgeFindingUp(Store store) {

        TreeSet<IntDomain> lctDownList = new TreeSet<IntDomain>( domainMaxComparator );

        if (debug)
            System.out.println("------------------------------------------------\n" + "Edge Finding Up\n"
                + "------------------------------------------------");
        for (Task t : Ts)
            if (t.nonZeroTask())
                lctDownList.add(t.completion());

        for (IntDomain lct : lctDownList) {

            int lct0 = lct.max();
            if (debug)
                System.out.println("lct0 = " + lct0 + "\n=================");

            // Create S = {t|EST(t) <= lct0}
            // Create L = {t|EST(t) < lct0 && LCT(t) > lct0}
            List<Task> S = new ArrayList<Task>(Ts.length), L = new ArrayList<Task>(Ts.length);
            for (Task t : Ts) {
                if (t.nonZeroTask()) {
                    if (t.lct() <= lct0)
                        S.add(t);
                    else if (t.est() < lct0) // && tt.lct() > lct0
                        L.add(t);
                }
            }
            if (debug) {
                System.out.println("\nS = " + S);
                System.out.println("L = " + L);
            }

            // update lower bound if tt cannot be the first in S
            for (Task t : S)
                notFirst(store, t, S);

            if (S.size() != 0 && !fitTasksBefore(S, lct0))
                throw Store.failException;

            while (S.size() != 0 && L.size() != 0) {
                // Select task l from L with the maximal area
                int indexOfl = maxArea(L);
                Task l = L.get(indexOfl);
                int l_EST = l.est();
                int limitMax = limit.max();
                // System.out.println("Maxumum area task= " + l);
                // Checking if l can be between and before S

                boolean before = true, between = true;

                int completionOfS = IntDomain.MinInt, startOfS = IntDomain.MaxInt;
                long area1 = 0, area2 = 0, larea = 0;
                if (debug)
                    System.out.println("Checking if " + l + " can be before or between tasks in " + S);

                for (Task t : S) {
                    completionOfS = Math.max(completionOfS, t.lct());
                    startOfS = Math.min(startOfS, t.est());
                    area1 += t.areaMin();
                    area2 += minOverlap(t, startOfS, completionOfS);
                }

                long totalArea = area1;
                int lctS = completionOfS;
                before = ((completionOfS - l_EST) * limitMax >= area1 + l.areaMin());

                // larea = l.dur.min()*l.res.min();
                larea = minOverlap(l, startOfS, completionOfS);
                between = ((completionOfS - startOfS) * limitMax >= area2 + larea);

                if (debug)
                    System.out.println(
                        "before=" + before + " between=" + between + " completionOfS=" + completionOfS + " startOfS=" + startOfS + " area2="
                            + area2 + "  larea=" + larea + "\nS = " + S + "\nl = " + l);

                if (before && between) {
                    L.remove(indexOfl);
                    removeFromS_Est(S);
                } else {
                    if (between && !before) {
                        // update lower bound of l

                        long slack, a = 0;
                        int completionS, newStartl = IntDomain.MinInt;
                        int maxuse = limitMax - l.res.min();

                        int startl = l_EST;
                        a = totalArea;
                        completionS = lctS;
                        slack = (completionS - l_EST) * limitMax - a - l.areaMin();

                        int j = 0;
                        Task[] tasks = new Task[S.size()];
                        int tasksLength = 0;
                        while (slack < 0 && j < S.size()) {
                            Task t = S.get(j);

                            if (t.res.min() <= maxuse || l_EST >= t.ect()) {
                                slack += t.areaMin();
                            } else {
                                tasks[tasksLength++] = t;
                            }
                            j++;
                        }

                        if (slack < 0 && tasksLength != 0) {
                            Arrays.sort(tasks, 0, tasksLength, taskAscEctComparator);

                            j = 0;
                            int limitMin = limit.min();
                            while (slack < 0 && j < tasksLength) {
                                Task t = tasks[j];
                                j++;
                                newStartl = t.ect();
                                slack = slack - (newStartl - startl) * limitMin + t.areaMin();
                                startl = newStartl;
                            }
                        }

                        if (newStartl > l_EST) {
                            if (debugNarr)
                                System.out
                                    .println(">>> Cumulative EF <<< 0. Narrowed " + l.start + " in " + startl + ".." + IntDomain.MaxInt);

                            l.start.domain.inMin(store.level, l.start, newStartl);

                        }

                        if (after(l, S))
                            L.remove(indexOfl);
                        else
                            removeFromS_Est(S);
                    } else {
                        if (!between && before)
                            L.remove(indexOfl);
                        else {
                            // ! between && ! before => after S
                            // l must be after S
                            // update lower bound of l
                            if (debug)
                                System.out.println("before=" + before + " between=" + between + "!!!");

                            int areaOfS = 0;
                            for (Task t : S)
                                areaOfS += t.areaMin();

                            int start = startOfS + areaOfS / limit.max();
                            if (start > l.start.min()) {
                                if (debugNarr)
                                    System.out.println(
                                        l + " must be after\n" + S + "\n>>> Cumulative EF <<< 1. Narrowed " + l.start + " in " + start
                                            + ".." + IntDomain.MaxInt);
                                l.start.domain.inMin(store.level, l.start, start);
                            }

                            L.remove(indexOfl);
                        }
                    }
                }
            }
        }
    }

    private int est(List<Task> S) {
        int estS = IntDomain.MaxInt;

        for (Task t : S) {
            int tEST = t.est();
            if (tEST < estS)
                estS = tEST;
        }
        return estS;
    }

    private boolean fitTasksAfter(List<Task> s, int est0) {
        int areaS = 0, lctOfS = IntDomain.MinInt, minDur = IntDomain.MaxInt, minRes = IntDomain.MaxInt;
        boolean FitAfter;

        for (Task t : s) {
            int dur = t.dur.min();
            int res = t.res.min();

            lctOfS = Math.max(lctOfS, t.lct());
            minDur = Math.min(minDur, dur);
            minRes = Math.min(minRes, res);

            areaS += dur * res;
        }

        int limitMax = limit.max();
        long availableArea = (lctOfS - est0) * limitMax;
        if (debug)
            System.out.println("Fit tasks of " + s + " after " + est0 + " = " + (availableArea >= areaS));
        FitAfter = availableArea >= areaS;

        if (FitAfter)
            FitAfter = ((lctOfS - est0) / minDur) * (limitMax / minRes) >= s.size();
        return FitAfter;
    }

    private boolean fitTasksBefore(List<Task> s, int lct0) {
        int areaS = 0, estOfS = IntDomain.MaxInt, minDur = IntDomain.MaxInt, minRes = IntDomain.MaxInt;
        boolean FitBefore;

        for (Task t : s) {
            int dur = t.dur.min();
            int res = t.res.min();

            estOfS = Math.min(estOfS, t.est());
            minDur = Math.min(minDur, dur);
            minRes = Math.min(minRes, res);

            areaS += dur * res;
        }

        int limitMax = limit.max();
        long availableArea = (lct0 - estOfS) * limitMax;
        if (debug)
            System.out.println("Fit tasks of " + s + " before " + lct0 + " = " + " Available are: " + availableArea + " Area: " + areaS);

        FitBefore = availableArea >= areaS;
        if (FitBefore)
            FitBefore = ((lct0 - estOfS) / minDur) * (limitMax / minRes) >= s.size();
        return FitBefore;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    Task[] getTasks() {
        return Ts;
    }

    private boolean intervalOverlap(int min1, int max1, int min2, int max2) {
        return !(min1 >= max2 || max1 <= min2);
    }

    private int lct(List<Task> S) {
        int lctS = IntDomain.MinInt;

        for (Task t : S) {
            lctS = Math.max(lctS, t.lct());
        }
        return lctS;
    }

    private int maxArea(List<Task> Ts) {
        long area = 0;
        int index = 0;

        // Select task with the maximal area
        int i = 0;
        for (Task t : Ts) {
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

        int tDur_min = 0;
        int tdur = t.dur.min();
        int tect = t.ect();
        int tlst = t.lst();

        if (est <= tlst)
            if (tect >= lct) {
                // |---t----|
                // |--------------|
                // est lct
                int temp2 = lct - tlst;
                tDur_min = temp2 < tdur ? temp2 : tdur;
            } else
                // tect < lct
                // |---t----|
                // |--------------|
                // est lct
                tDur_min = tdur;
        else
            // est > tlst
            if (tect > est)
                if (tect <= lct) {
                    // |---t----|
                    // |--------------|
                    // est lct
                    int temp1 = tect - est;
                    tDur_min = temp1 < tdur ? temp1 : tdur;
                } else
                    // tect > lct
                    // |--------t---------|
                    // |--------------|
                    // est lct
                    tDur_min = lct - est < tdur ? lct - est : tdur;
            else
                // tect <= est
                tDur_min = 0;
        return tDur_min * t.res.min();
    }

    private void notFirst(Store store, Task s, List<Task> S) {
        int sEST = s.est(); // sLCT = s.LCT();
        int completionS = IntDomain.MinInt, newStartl = IntDomain.MinInt, startl = sEST;
        long a = 0, slack, maxuse = limit.max() - s.res.min();

        if (S.size() > 1) {

            if (debug)
                System.out.println("Not first " + s + " in " + S);
            for (Task t : S) {
                if (t != s) {
                    completionS = Math.max(completionS, t.lct());
                    a += t.areaMin();
                }
            }
            slack = (completionS - sEST) * limit.max() - a - s.areaMin();
            // System.out.println("slack = "+ slack);
            if (debug) {
                boolean notBeforeS = (slack < 0);
                System.out.println("s(l)= " + sEST + ",  c(S')= " + completionS + ",  a(S)= " + a + ",  notBeforeS= " + notBeforeS);
            }

            // Upadate LB for task s

            int j = 0;
            Task[] tasks = new Task[S.size() - 1];
            int tasksLength = 0;
            while (slack < 0 && j < S.size()) {
                Task t = S.get(j);

                if (t != s) {
                    if (t.res.min() <= maxuse || sEST >= t.ect()) {
                        slack += t.areaMin();
                    } else {
                        tasks[tasksLength++] = t;
                    }
                }
                j++;
            }

            // System.out.println("slack after = " + slack + "tasks = " + tasks );
            if (slack < 0 && tasksLength != 0) {
                Arrays.sort(tasks, 0, tasksLength, taskAscEctComparator );
                j = 0;
                int limitMin = limit.min();
                while (slack < 0 && j < tasksLength) {
                    Task t = tasks[j];
                    j++;
                    newStartl = t.ect();
                    slack = slack - (newStartl - startl) * limitMin + t.areaMin();
                    startl = newStartl;
                }

                if (newStartl > sEST) {
                    if (debugNarr)
                        System.out.println(">>> Cumulative EF <<< 4. Narrowed " + s.start + " in " + startl + ".." + IntDomain.MaxInt);

                    s.start.domain.inMin(store.level, s.start, newStartl);
                }
            }
        }
    }

    private void notLast(Store store, Task s, List<Task> S) {
        int sLCT = s.lct();
        int compl = sLCT;

        int startS = IntDomain.MaxInt, newCompl = IntDomain.MaxInt, newStartl = IntDomain.MinInt;
        long a = 0, slack, maxuse = limit.max() - s.res.min();

        if (S.size() > 1) {

            if (debug)
                System.out.println("Not last " + s + " in " + S);
            for (Task t : S) {
                if (t != s) {
                    startS = Math.min(startS, t.est());
                    a += t.areaMin();
                }
            }
            slack = (sLCT - startS) * limit.max() - a - s.areaMin();

            if (debug) {
                boolean notLastInS = (slack < 0);
                System.out.println("s(S')= " + startS + ",  c(l)= " + sLCT + ",  a(S)= " + a + ",  notLastInS= " + notLastInS);
            }

            // Upadate UB for task s

            int j = 0;
            Task[] tasks = new Task[S.size() - 1];
            int tasksLength = 0;
            while (slack < 0 && j < S.size()) {
                Task t = S.get(j);
                if (t != s) {

                    if (t.res.min() <= maxuse || sLCT <= t.lst()) {
                        slack += t.areaMin();
                    } else {
                        tasks[tasksLength++] = t;
                    }
                }
                j++;
            }

            if (slack < 0 && tasksLength != 0) {
                Arrays.sort(tasks, 0, tasksLength, taskDescLstComparator);

                j = 0;
                int limitMin = limit.min();
                while (slack < 0 && j < tasksLength) {
                    Task t = tasks[j];
                    j++;
                    newCompl = t.lst();
                    slack = slack - (compl - newCompl) * limitMin + t.areaMin();
                    compl = newCompl;
                }

                newStartl = compl - s.dur.min();
                if (newStartl < s.start.max()) {
                    if (debugNarr)
                        System.out.println(">>> Cumulative EF <<< 5. Narrowed " + s.start + " in " + IntDomain.MinInt + ".." + newStartl);

                    s.start.domain.inMax(store.level, s.start, newStartl);
                }
            }
        }
    }

    private void profileCheckInterval(Store store, IntVar Start, IntVar Duration, Interval i, IntVar Resources, int mustUseMin,
        int mustUseMax) {

        for (ProfileItem p : minProfile) {
            if (debug)
                System.out.println("Comparing " + i + " with profile item " + p);

            if (intervalOverlap(i.min, i.max + Duration.min(), p.min, p.max)) {
                if (debug)
                    System.out.println("Overlapping");
                if (limit.max() - p.value < Resources.min()) {
                    // Check for possible narrowing or fail
                    if (mustUseMin != -1) {
                        ProfileItem use = new ProfileItem(mustUseMin, mustUseMax, Resources.min());
                        ProfileItem left = new ProfileItem();
                        ProfileItem right = new ProfileItem();
                        p.subtract(use, left, right);

                        if (left.min != -1) {
                            int UpdateMin = left.min - Duration.min() + 1, UpdateMax = left.max - 1;
                            if (!(UpdateMin > Start.max() || UpdateMax < Start.min())) {
                                if (debugNarr)
                                    System.out.print(
                                        ">>> Cumulative Profile 7a. Narrowed " + Start + " \\ " + new IntervalDomain(UpdateMin, UpdateMax));

                                if (UpdateMin <= UpdateMax)
                                    Start.domain.inComplement(store.level, Start, UpdateMin, UpdateMax);
                                if (debugNarr)
                                    System.out.println(" => " + Start);
                            }
                        }

                        if (right.min != -1) {
                            int UpdateMin = right.min - Duration.min() + 1, UpdateMax = right.max - 1;
                            if (!(UpdateMin > Start.max() || UpdateMax < Start.min())) {
                                if (debugNarr)
                                    System.out.print(
                                        ">>> Cumulative Profile 7b. Narrowed " + Start + " \\ " + new IntervalDomain(UpdateMin, UpdateMax));

                                if (UpdateMin <= UpdateMax)
                                    Start.domain.inComplement(store.level, Start, UpdateMin, UpdateMax);
                                if (debugNarr)
                                    System.out.println(" => " + Start);
                            }
                        }

                        if (Start.max() < right.min && Start.dom().noIntervals() == 1) {
                            int rs = right.min - Start.min();
                            if (rs < Duration.max()) {
                                if (debugNarr)
                                    System.out.println(">>> Cumulative Profile 9. Narrow " + Duration + " in 0.." + rs);
                                Duration.domain.inMax(store.level, Duration, rs);
                            }
                        }
                    } else { // (mustUse.min() == -1 )
                        int UpdateMin = p.min - Duration.min() + 1, UpdateMax = p.max - 1;
                        if (!(UpdateMin > Start.max() || UpdateMax < Start.min())) {
                            if (debugNarr)
                                System.out.print(
                                    ">>> Cumulative Profile 6. Narrowed " + Start + " \\ " + new IntervalDomain(UpdateMin, UpdateMax));
                            if (UpdateMin <= UpdateMax)
                                Start.domain.inComplement(store.level, Start, UpdateMin, UpdateMax);

                            if (debugNarr)
                                System.out.println(" => " + Start);
                        }
                    }
                } else { // ( Overlapping &&
                    // limit.max() - p.Value >= Resources.min() )
                    if (mustUseMin != -1 && !(mustUseMax <= p.min() || mustUseMin >= p.max())) {
                        int offset = 0;
                        if (intervalOverlap(p.min(), p.max(), mustUseMin, mustUseMax))
                            offset = Resources.min();
                        if (debugNarr)
                            System.out.println(
                                ">>> Cumulative Profile 8. Narrowed " + Resources + " in 0.." + (limit.max() - p.value + offset));

                        Resources.domain.in(store.level, Resources, 0, limit.max() - p.value + offset);
                    }
                }
            } else { // ( ( i.min() >= p.max() || i.max()+dur <= p.min()) )
                if (Start.max() < p.min && Start.dom().noIntervals() == 1) {
                    // System.out.println("Nonoverlaping "+Start+", "+i+", "+p);
                    int ps = p.min - Start.min();
                    if (ps < Duration.max() && limit.max() - p.value < Resources.min()) {
                        if (debugNarr)
                            System.out.println(">>> Cumulative Profile 10. Narrowed " + Duration + " in 0.." + ps);

                        Duration.domain.inMax(store.level, Duration, ps);
                    }
                }
            }
        }
    }

    private void profileCheckTasks(Store store) {
        IntTask minUse = new IntTask();

        for (Task t : Ts) {
            // check only for tasks which cannot allow to have duration or resources = 0
            if (t.nonZeroTask()) {
                int a = -1, b = -1;
                if (t.minUse(minUse)) {
                    a = minUse.start();
                    b = minUse.stop();
                }

                IntVar resUse = t.res;
                IntVar dur = t.dur;

                if (debug)
                    System.out.println("Start time = " + t.start + ", resource use = " + resUse + ", minimal use = {" + a + ".." + b + "}");

                IntDomain tStartDom = t.start.dom();

                for (int m = 0; m < tStartDom.noIntervals(); m++)
                    profileCheckInterval(store, t.start, dur, tStartDom.getInterval(m), resUse, a, b);
            }
        }
    }

    private void removeFromS_Est(List<Task> s) {

        // s = s \ {t in s | est(t) = est(s)}
        int estS = est(s);
        int l = s.size();
        int i = 0;
        while (i < l) {
            Task t = s.get(i);
            if (estS == t.est()) {
                s.remove(i);
                l--;
            } else
                i++;
        }
    }

    private void removeFromS_Lct(List<Task> s) {

        // s = s \ {t in s | lct(t) = lct(s)}
        int lctS = lct(s);
        int l = s.size();
        int i = 0;
        while (i < l) {
            Task t = s.get(i);
            if (lctS == t.lct()) {
                s.remove(i);
                l--;
            } else
                i++;
        }
    }

    @Override public boolean satisfied() {

        // if profile has been computed make a quick check
        if (minProfile != null && maxProfile != null) {
            return (minProfile.max() == maxProfile.max()) && limit.singleton() && minProfile.max() == limit.min();
        } else {
            throw new IllegalStateException("Satisfied function can only be called after call to consistency().");
        }
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : cumulative([ ");
        for (int i = 0; i < Ts.length - 1; i++)
            result.append(Ts[i]).append(", ");

        result.append(Ts[Ts.length - 1]);

        result.append(" ]").append(", limit = ").append(limit).append(" )");

        return result.toString();

    }

    private void updateTasksRes(Store store) {
        int limitMax = limit.max();
        for (Task t : Ts)
            t.res.domain.inMax(store.level, t.res, limitMax);
    }

}
