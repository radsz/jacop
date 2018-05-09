/*
 * Diffn.java
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


package org.jacop.constraints.diffn;

import org.jacop.core.*;

import java.util.*;

/**
 * Diffn constraint assures that any two rectangles from a vector of rectangles
 * does not overlap in at least one direction. It is a simple implementation which
 * does not use sophisticated techniques for efficient backtracking.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class Diffn extends Nooverlap {

    private static final boolean debug = false, debugNarr = false;

    Comparator<Event> eventComparator = (o1, o2) -> (o1.date() == o2.date()) ? o1.type() - o2.type() : o1.date() - o2.date();

    /**
     * It specifies a diff constraint.
     *
     * @param rectangles list of rectangles which can not overlap in at least one dimension.
     */
    public Diffn(IntVar[][] rectangles) {
        super(rectangles);
    }

    /**
     * It specifies a diff constraint.
     *
     * @param rectangles list of rectangles which can not overlap in at least one dimension.
     * @param strict     true- zero size rectangles need to be between other rectangles; false- these rectangles can be anywhere
     */
    public Diffn(IntVar[][] rectangles, boolean strict) {
        super(rectangles, strict);
    }

    /**
     * It constructs a diff constraint.
     *
     * @param origin1 list of variables denoting origin of the rectangle in the first dimension.
     * @param origin2 list of variables denoting origin of the rectangle in the second dimension.
     * @param length1 list of variables denoting length of the rectangle in the first dimension.
     * @param length2 list of variables denoting length of the rectangle in the second dimension.
     */

    public Diffn(IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2) {
        super(origin1, origin2, length1, length2);
    }

    /**
     * It constructs a diff constraint.
     *
     * @param origin1 list of variables denoting origin of the rectangle in the first dimension.
     * @param origin2 list of variables denoting origin of the rectangle in the second dimension.
     * @param length1 list of variables denoting length of the rectangle in the first dimension.
     * @param length2 list of variables denoting length of the rectangle in the second dimension.
     * @param strict  true- zero size rectangles need to be between other rectangles; false- these rectangles can be anywhere
     */

    public Diffn(IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2, boolean strict) {
        super(origin1, origin2, length1, length2, strict);
    }


    /**
     * It specifies a diffn constraint.
     *
     * @param rectangles list of rectangles which can not overlap in at least one dimension.
     */
    public Diffn(List<? extends List<? extends IntVar>> rectangles) {
        super(rectangles);
    }

    /**
     * It specifies a diffn constraint.
     *
     * @param rectangles list of rectangles which can not overlap in at least one dimension.
     * @param strict     true- zero size rectangles need to be between other rectangles; false- these rectangles can be anywhere
     */
    public Diffn(List<? extends List<? extends IntVar>> rectangles, boolean strict) {
        super(rectangles, strict);
    }


    /**
     * It constructs a diff constraint.
     *
     * @param o1 list of variables denoting origin of the rectangle in the first dimension.
     * @param o2 list of variables denoting origin of the rectangle in the second dimension.
     * @param l1 list of variables denoting length of the rectangle in the first dimension.
     * @param l2 list of variables denoting length of the rectangle in the second dimension.
     */
    public Diffn(List<? extends IntVar> o1, List<? extends IntVar> o2, List<? extends IntVar> l1, List<? extends IntVar> l2) {
        super(o1, o2, l1, l2);
    }

    /**
     * It constructs a diff constraint.
     *
     * @param o1     list of variables denoting origin of the rectangle in the first dimension.
     * @param o2     list of variables denoting origin of the rectangle in the second dimension.
     * @param l1     list of variables denoting length of the rectangle in the first dimension.
     * @param l2     list of variables denoting length of the rectangle in the second dimension.
     * @param strict true- zero size rectangles need to be between other rectangles; false- these rectangles can be anywhere
     */
    public Diffn(List<? extends IntVar> o1, List<? extends IntVar> o2, List<? extends IntVar> l1, List<? extends IntVar> l2,
        boolean strict) {
        super(o1, o2, l1, l2, strict);
    }

    public void consistency(Store store) {

        this.store = store;

        do {
            store.propagationHasOccurred = false;

            pruning();

            if (doAreaCheck)
                areaCheck();

            profile();

        } while (store.propagationHasOccurred);
    }

    private void areaCheck() {
        for (int k = 0; k < rectangle.length; k++) {
            Rectangle r = rectangle[k];
            BitSet o = overlapping[k].value();

            if (o.cardinality() > 0) {

                // calculate area within rectangle r possible placement
                int commonArea = 0;
                for (int j = o.nextSetBit(0); j >= 0; j = o.nextSetBit(j + 1)) {
                    int partialCommonArea = 1;
                    Rectangle s = rectangle[j];

                    for (int i = 0; i < 2; i++) {
                        int r_min = r.est(i);
                        int r_max = r.lct(i);
                        int sLengthMin = s.length(i).min();

                        if (s.origin(i).min() <= r_min) {
                            if (s.origin(i).max() + s.length(i).min() <= r_max) {
                                int distance1 = s.ect(i) - r_min;
                                sLengthMin = (distance1 > 0) ? distance1 : 0;
                            } else {
                                // s.origin(i).max() + slength(i).min()> r_max)
                                int rmax = r.origin(i).max() + r.length(i).min();

                                int distance1 = s.ect(i) - r_min;
                                int distance2 = -s.origin(i).max() + rmax;
                                distance1 = Math.min(distance1, rmax - r_min);
                                distance2 = Math.min(distance2, rmax - r_min);
                                if (distance1 < distance2)
                                    sLengthMin = (distance1 > 0) ? distance1 : 0;
                                else if (distance2 > 0) {
                                    if (distance2 < s.length(i).min())
                                        sLengthMin = distance2;
                                } else
                                    sLengthMin = 0;
                            }
                        } else // s.origin(i).min() > r_min
                            if (s.origin(i).max() + s.length(i).min() > r_max) {
                                int distance2 = -s.origin(i).max() + r.origin[i].max() + r.length[i].min();
                                if (distance2 > 0) {
                                    if (distance2 < s.length(i).min())
                                        sLengthMin = distance2;
                                } else
                                    sLengthMin = 0;
                            }
                        partialCommonArea = partialCommonArea * sLengthMin;
                    }
                    commonArea += partialCommonArea;
                }
                if (commonArea + r.length(x).min() * r.length(y).min() > (r.lct(x) - r.est(x)) * (r.lct(y) - r.est(y))) {
                    throw Store.failException;
                }
            }
        }
    }

    private void profile() {

        for (int i = 0; i < rectangle.length; i++) {
            Rectangle r = rectangle[i];
            BitSet o = overlapping[i].value();

            if (o.cardinality() > 0) {
                sweepPruning(r, o, 0);
                sweepPruning(r, o, 1);
            }
        }
    }

    private void sweepPruning(Rectangle r, BitSet o, int dim) {

        int oDim = (dim == 0) ? 1 : 0;

        Event[] es = new Event[2 * o.cardinality() + 2];

        boolean mandatoryExists = false;
        int j = 0;
        int minLimit = r.est(oDim), maxLimit = r.lct(oDim);
        for (int i = o.nextSetBit(0); i >= 0; i = o.nextSetBit(i + 1)) {
            Rectangle rr = rectangle[i];
            rr.index = i;

            // mandatory task parts to create profile
            int min = rr.lst(dim), max = rr.ect(dim);
            if (min < max && rr.length(oDim).min() > 0) {
                if (rr.est(oDim) >= r.est(oDim) && rr.lct(oDim) <= r.lct(oDim)) {
                    // for profile take only rectangles with their area laying within the considered rectangle
                    int oMin = rr.lst(oDim), oMax = rr.ect(oDim);
                    if (oMin < oMax) {
                        Interval block = new Interval(oMin, oMax);
                        int lMin = rr.length(oDim).min();
                        es[j++] = new Event(profileAdd, rr, min, lMin, block);
                        es[j++] = new Event(profileSubtract, rr, max, -lMin, block);
                    } else {
                        int lMin = rr.length(oDim).min();
                        es[j++] = new Event(profileAdd, rr, min, lMin, null);
                        es[j++] = new Event(profileSubtract, rr, max, -lMin, null);
                    }
                    minLimit = Math.min(rr.est(oDim), minLimit);
                    maxLimit = Math.max(rr.lct(oDim), maxLimit);
                    mandatoryExists = true;
                } else {
                    int oMin = rr.lst(oDim), oMax = rr.ect(oDim);
                    if (oMin < oMax) {
                        Interval block = new Interval(oMin, oMax);
                        es[j++] = new Event(profileAdd, rr, min, 0, block);
                        es[j++] = new Event(profileSubtract, rr, max, 0, block);
                    }
                    mandatoryExists = true;
                }
            }
        }
        if (!mandatoryExists)
            return;

        int limit = maxLimit - minLimit;

        // overlapping rectangle for pruning
        // from start to end
        int min = r.est(dim);
        int max = r.lct(dim);
        if (r.length(dim).max() > 0 && r.length(oDim).max() > 0) {
            es[j++] = new Event(pruneStart, r, min, 0, null);
            es[j++] = new Event(pruneEnd, r, max, 0, null);
        } else
            return;

        int N = j;
        Arrays.sort(es, 0, N, eventComparator);
        // Arrays.parallelSort(es, 0, N, new EventIncComparator<Event>());

        if (debugNarr) {
            System.out.println("===========================");
            System.out.println("Profile in dimension " + dim);
            System.out.println(Arrays.asList(es));
            System.out.println("limit = " + limit);
            System.out.println("===========================");
        }

        boolean considerR = false;

        boolean[] inProfile = new boolean[rectangle.length];

        // current value of the profile for mandatory parts
        int curProfile = 0;
        // current value of the sweep line
        List<Interval> sweepLine = new ArrayList<>();

        // used for start variable pruning
        int startExcluded = Integer.MAX_VALUE;

        // used for duration variable pruning
        int lastBarier = Integer.MAX_VALUE;
        boolean startAtEnd = false;

        for (int i = 0; i < N; i++) {

            Event e = es[i];
            Event ne = null;  // next event
            if (i < N - 1)
                ne = es[i + 1];

            switch (e.type()) {

                case profileSubtract: // =========== profileSubtract event ===========
                case profileAdd: // =========== profileAdd event ===========

                    curProfile += e.value();
                    inProfile[e.rect().index] = (e.value() > 0);

                    if (e.block() != null)
                        updateSweepLine(sweepLine, e);

                    if (ne == null || ne.type() > profileAdd || e.date < ne
                        .date()) { // check the tasks for pruning only at the end of all profile events

                        if (debug)
                            System.out.println("Profile at " + e.date() + ": " + curProfile);

                        // fail if we go over limit limit variable
                        if (curProfile > limit)
                            throw Store.failException;

                        if (considerR) {

                            int ri = r.index;

                            int profileValue = curProfile;
                            if (inProfile[ri])
                                profileValue -= r.length(oDim).min();

                            boolean blocking = blocking(sweepLine, r.origin(oDim).min(), r.origin(oDim).max() + r.length(oDim).min(),
                                r.length(oDim).min());

                            // ========= Pruning start variable
                            if (r.exists()) //(r.length(oDim).min() > 0 && r.length(dim).min() > 0)
                                if (startExcluded == Integer.MAX_VALUE) {
                                    if (limit - profileValue < r.length(oDim).min() || blocking) {
                                        startExcluded = e.date() - r.length(dim).min() + 1;
                                    }
                                } else //startExcluded != Integer.MAX_VALUE
                                    if (limit - profileValue >= r.length(oDim).min() && !blocking) {
                                        // end of excluded interval

                                        if (startExcluded <= r.lst(dim)) {

                                            if (debugNarr)
                                                System.out.print(">>> Diffn (" + dim + ") Profile 1. Narrowed " + r.origin(dim) + " \\ "
                                                    + new IntervalDomain(startExcluded, (e.date() - 1)));

                                            IntervalDomain update = new IntervalDomain(IntDomain.MinInt, startExcluded - 1);
                                            update.unionAdapt(e.date(), IntDomain.MaxInt);
                                            r.origin(dim).domain.in(store.level, r.origin(dim), update);

                                            // r.origin(dim).domain.inComplement(store.level, r.origin(dim), startExcluded, e.date() - 1);

                                            if (debugNarr)
                                                System.out.println(" => " + r.origin(dim));

                                        }
                                        startExcluded = Integer.MAX_VALUE;
                                    }

                            // ========= for duration pruning
                            if (e.date() <= r.lst(dim))
                                if (limit - profileValue < r.length(oDim).min())
                                    startAtEnd = false;
                                else  // limit - profileValue >= t.length(oDim).min()
                                    startAtEnd = true;

                            if (lastBarier == Integer.MAX_VALUE && e.date() >= r.lst(dim) && (limit - profileValue < r.length(oDim).min()
                                || blocking))
                                lastBarier = e.date();

                            // ========= resource pruning
                            if (r.lst(dim) <= e.date() && e.date() < r.ect(dim) && limit - profileValue < r.length(oDim).max())
                                r.length(oDim).domain.inMax(store.level, r.length(oDim), limit - profileValue);

                        }
                    }

                    break;

                case pruneStart:  // =========== start of a task ===========
                    int profileValue = curProfile;
                    Rectangle rr = e.rect();
                    int ri = rr.index;

                    considerR = true;

                    if (inProfile[ri])
                        profileValue -= rr.length(oDim).min();

                    // ========= for start pruning
                    if (rr.exists()) //(rr.length(oDim).min() > 0 && rr.length(dim).min() > 0)
                        if (limit - profileValue < rr.length(oDim).min() || blocking(sweepLine, rr.origin(oDim).min(),
                            rr.origin(oDim).max() + rr.length(oDim).min(), rr.length(oDim).min())) {
                            startExcluded = e.date();
                        }

                    // ========= for duration pruning
                    startAtEnd = true;

                    // ========= resource pruning
                    if (rr.lst(dim) <= e.date() && e.date() < rr.ect(dim) && limit - profileValue < rr.length(oDim).max())
                        rr.length(oDim).domain.inMax(store.level, rr.length(oDim), limit - profileValue);

                    break;

                case pruneEnd: // =========== end of a task ===========
                    profileValue = curProfile;
                    rr = e.rect();
                    ri = rr.index;

                    considerR = false;

                    if (inProfile[ri])
                        profileValue -= rr.length(oDim).min();

                    // ========= pruning start variable
                    if (rr.exists()) //(rr.length(oDim).min() > 0 && rr.length(dim).min() > 0)
                        if (startExcluded != Integer.MAX_VALUE) {
                            // task ends and we remove forbidden area

                            if (startExcluded - 1 <= rr.lst(dim)) {
                                if (debugNarr)
                                    System.out.print(
                                        ">>> Diffn Profile 2. Narrowed " + rr.origin(dim) + " \\ " + new IntervalDomain(startExcluded,
                                            e.date()));

                                rr.origin(dim).domain.inMax(store.level, rr.origin(dim), startExcluded - 1);
                                // rr.origin(dim).domain.inComplement(store.level, rr.origin(dim), startExcluded, e.date());

                                if (debugNarr)
                                    System.out.println(" => " + rr.origin(dim));

                            }
                        }

                    startExcluded = Integer.MAX_VALUE;

                    // ========= resource pruning
                    if (rr.lst(dim) <= e.date() && e.date() < rr.ect(dim) && limit - profileValue < rr.length(oDim).max())
                        rr.length(oDim).domain.inMax(store.level, rr.length(oDim), limit - profileValue);

                    // ========= duration pruning
                    int maxDuration = Integer.MIN_VALUE;
                    Interval lastInterval = null;

                    for (IntervalEnumeration e1 = rr.origin(dim).dom().intervalEnumeration(); e1.hasMoreElements(); ) {
                        Interval i1 = e1.nextElement();
                        maxDuration = Math.max(maxDuration, i1.max() - i1.min() + rr.length(dim).min());
                        lastInterval = i1;
                    }
                    if (startAtEnd)
                        maxDuration = Math.max(maxDuration, lastBarier - lastInterval.min());

                    if (maxDuration < rr.length(dim).max()) {
                        if (debugNarr)
                            System.out.print(">>> Diffn Profile 3. Narrowed " + rr.length(dim) + " in 0.." + maxDuration);

                        rr.length(dim).domain.inMax(store.level, rr.length(dim), maxDuration);

                        if (debugNarr)
                            System.out.println(" => " + rr.length(dim));
                    }

                    break;
                default:
                    throw new RuntimeException("Internal error in " + getClass().getName());
            }
        }
    }

    private void updateSweepLine(List<Interval> sweepLine, Event e) {

        Interval eBlock = e.block();

        if (sweepLine.size() == 0) {
            sweepLine.add(eBlock);
            return;
        }

        if (e.type() == profileAdd) {// add
            Interval previous = new Interval(IntDomain.MinInt, IntDomain.MinInt);
            for (int i = 0; i < sweepLine.size(); i++) {
                Interval sweepLineElement = sweepLine.get(i);
                if ((eBlock.max() > sweepLineElement.min() && eBlock.max() <= sweepLineElement.max()) || (
                    eBlock.min() >= sweepLineElement.min() && eBlock.min() < sweepLineElement.max())) {
                    throw Store.failException; // overlap
                }
                if (eBlock.max() <= sweepLineElement.min() && eBlock.min() >= previous.max()) {
                    sweepLine.add(i, eBlock);
                    return;
                }
                previous = sweepLineElement;
            }

            // add at the end
            if (sweepLine.get(sweepLine.size() - 1).max() <= eBlock.min())
                sweepLine.add(eBlock);
        } else // e.type() == profileSubtract; remove
            for (int i = 0; i < sweepLine.size(); i++) {
                Interval sweepLineElement = sweepLine.get(i);
                if (sweepLineElement.min() == eBlock.min() && sweepLineElement.max() == eBlock.max()) {
                    sweepLine.remove(i);
                    return;
                }
            }
    }

    private boolean blocking(List<Interval> sweepLine, int start, int end, int length) {

        if (sweepLine.size() == 0)
            return false;

        int s = start;
        for (Interval sweepLineElement : sweepLine) {

            if (sweepLineElement.min() <= s) {
                s = Math.min(sweepLineElement.max(), end);
                continue;
            }
            if (sweepLineElement.min() - s >= length) {
                return false;
            }
            if (sweepLineElement.max() >= end) {
                return true;
            }
            s = Math.min(sweepLineElement.max(), end);
        }
        return end - s < length;
    }

    // event type
    static final int profileSubtract = 0, profileAdd = 1, pruneStart = 2, pruneEnd = 3;


    private static class Event {
        int type;
        Rectangle r;
        int date;
        int value;
        Interval block;

        Event(int type, Rectangle r, int date, int value, Interval block) {
            this.type = type;
            this.r = r;
            this.date = date;
            this.value = value;
            this.block = block;
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

        Rectangle rect() {
            return r;
        }

        Interval block() {
            return block;
        }

        @Override public String toString() {
            String result = "(";
            switch (type) {
                case profileSubtract:
                    result += "profileSubtract, ";
                    break;
                case profileAdd:
                    result += "profileAdd, ";
                    break;
                case pruneStart:
                    result += "pruneStart, ";
                    break;
                case pruneEnd:
                    result += "pruneEnd, ";
                    break;
                default:
                    result += "--";
            }
            result += r + ", " + date + ", " + value + ", " + block + ")\n";
            return result;
        }
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : diffn([");

        int i = 0;
        for (Rectangle r : rectangle) {
            result.append(r);
            if (i < rectangle.length - 1)
                result.append(", ");
            i++;
        }
        return result.append("], ").append(strict).append(")").toString();
    }

}
