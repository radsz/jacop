/*
 * Disjoint.java
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

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Disjoint constraint assures that any two rectangles from a vector of
 * rectangles does not overlap in at least one direction.
 *
 * Zero-width rectangles does not overlap with any other rectangle. 
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Disjoint extends Diff {

    static AtomicInteger idNumber = new AtomicInteger(0);

    Diff2Var evalRects[];

    /**
     *
     * @param rectangles a list of rectangles.
     * @param doProfile should profile be computed and used.
     *
     */
    public Disjoint(Rectangle[] rectangles, boolean doProfile) {

        checkInputForNullness("rectangles", rectangles);
        checkInput(rectangles, r -> r.dim == 2, "rectangle has to have exactly two dimensions");

        this.queueIndex = 2;

        this.rectangles = Arrays.copyOf(rectangles, rectangles.length);
        this.doProfile = doProfile;
        this.numberId = idNumber.incrementAndGet();

        setScope(Rectangle.getStream(this.rectangles));
    }

    /**
     * It creates a diff2 constraint.
     * @param o1 list of variables denoting the origin in the first dimension.
     * @param o2 list of variables denoting the origin in the second dimension.
     * @param l1 list of variables denoting the length in the first dimension.
     * @param l2 list of variables denoting the length in the second dimension.
     * @param profile specifies if the profile should be computed.
     */
    public Disjoint(List<IntVar> o1, List<IntVar> o2, List<IntVar> l1, List<IntVar> l2, boolean profile) {
        this(o1, o2, l1, l2);
        doProfile = profile;
    }

    /**
     * It creates a diff2 constraint.
     * @param rectangles list of rectangles with origins and lengths in both dimensions.
     */

    public Disjoint(List<? extends List<? extends IntVar>> rectangles) {

        queueIndex = 2;
        this.rectangles = Rectangle.toArrayOf2DRectangles(rectangles);
        numberId = idNumber.incrementAndGet();

        setScope(Rectangle.getStream(this.rectangles));

    }

    /**
     * It creates a diff2 constraint.
     * @param rectangles list of rectangles with origins and lengths in both dimensions.
     * @param profile specifies if the profile is computed and used.
     */

    public Disjoint(List<? extends List<? extends IntVar>> rectangles, boolean profile) {
        this(rectangles);
        doProfile = profile;
    }


    /**
     * It creates a diff2 constraint.
     * @param o1 list of variables denoting the origin in the first dimension.
     * @param o2 list of variables denoting the origin in the second dimension.
     * @param l1 list of variables denoting the length in the first dimension.
     * @param l2 list of variables denoting the length in the second dimension.
     */
    public Disjoint(List<? extends IntVar> o1, List<? extends IntVar> o2, List<? extends IntVar> l1,
        List<? extends IntVar> l2) {

        this(o1.toArray(new IntVar[o1.size()]), o2.toArray(new IntVar[o2.size()]), l1.toArray(new IntVar[l1.size()]),
            l2.toArray(new IntVar[l2.size()]));

    }

    /**
     * It creates a diff2 constraint.
     * @param origin1 list of variables denoting the origin in the first dimension.
     * @param origin2 list of variables denoting the origin in the second dimension.
     * @param length1 list of variables denoting the length in the first dimension.
     * @param length2 list of variables denoting the length in the second dimension.
     */

    public Disjoint(IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2) {

        checkInputForNullness(new String[]{"origin1", "origin2", "length1", "length2"},
            new Object[][]{origin1, origin2, length1, length2});

        queueIndex = 2;
        this.rectangles = Rectangle.toArrayOf2DRectangles(origin1, origin2, length1, length2);
        numberId = idNumber.incrementAndGet();

        setScope(Rectangle.getStream(this.rectangles));
    }

    /**
     * It creates a diff2 constraint.
     * @param o1 list of variables denoting the origin in the first dimension.
     * @param o2 list of variables denoting the origin in the second dimension.
     * @param l1 list of variables denoting the length in the first dimension.
     * @param l2 list of variables denoting the length in the second dimension.
     * @param profile specifies if the profile should be computed.
     */
    public Disjoint(IntVar[] o1, IntVar[] o2, IntVar[] l1, IntVar[] l2, boolean profile) {
        this(o1, o2, l1, l2);
        doProfile = profile;
    }

    /**
     * It creates a diff2 constraint.
     * @param rectangles list of rectangles with origins and lengths in both dimensions.
     */

    public Disjoint(IntVar[][] rectangles) {

        assert (rectangles != null) : "Rectangles list is null";

        queueIndex = 2;
        this.rectangles = Rectangle.toArrayOf2DRectangles(rectangles);
        numberId = idNumber.incrementAndGet();

        setScope(Rectangle.getStream(this.rectangles));

    }

    /**
     * It creates a diff2 constraint.
     * @param rectangles list of rectangles with origins and lengths in both dimensions.
     * @param profile specifies if the profile is computed and used.
     */

    public Disjoint(IntVar[][] rectangles, boolean profile) {
        this(rectangles);
        doProfile = profile;
    }

    public void impose(Store store) {

        super.impose(store);

        evalRects = new Diff2Var[rectangles.length];

        for (int j = 0; j < evalRects.length; j++)
            evalRects[j] = new Diff2Var(store, rectangles);

    }

    @Override void narrowRectangles(Set<IntVar> fdvQueue) {

        boolean needToNarrow = false;

        for (int l = 0; l < rectangles.length; l++) {
            Rectangle r = rectangles[l];

            boolean settled = true, minLengthEq0 = false;
            int maxLevel = 0;
            for (int i = 0; i < r.dim(); i++) {
                IntDomain rOrigin = r.origin[i].dom();
                IntDomain rLength = r.length[i].dom();
                settled = settled && rOrigin.singleton() && rLength.singleton();

                minLengthEq0 = minLengthEq0 || (rLength.min() < 0);

                int originStamp = rOrigin.stamp, lengthStamp = rLength.stamp;
                if (maxLevel < originStamp)
                    maxLevel = originStamp;
                if (maxLevel < lengthStamp)
                    maxLevel = lengthStamp;
            }

            if (!minLengthEq0 && // Check for rectangle r which has
                // all lengths > 0
                !(settled && maxLevel < currentStore.level)) {
                // and are not fixed already

                needToNarrow = needToNarrow || containsChangedVariable(r, fdvQueue);

                List<IntRectangle> UsedRect = new ArrayList<IntRectangle>();
                List<Rectangle> ProfileCandidates = new ArrayList<Rectangle>();
                List<Rectangle> OverlappingRects = new ArrayList<Rectangle>();
                boolean ntN = findRectangles(r, l, UsedRect, ProfileCandidates, OverlappingRects, fdvQueue);

                needToNarrow = needToNarrow || ntN;

                // Checking r against all s with minUse in the domain of r
                if (needToNarrow) {

                    if (OverlappingRects.size() != ((Diff2VarValue) evalRects[l].value()).Rects.length) {
                        Diff2VarValue newRects = new Diff2VarValue();
                        newRects.setValue(OverlappingRects);
                        evalRects[l].update(newRects);
                    }

                    narrowRectangle(r, UsedRect, ProfileCandidates);
                }
            }
        }
    }

    private boolean findRectangles(Rectangle r, int index, List<IntRectangle> UsedRect, List<Rectangle> ProfileCandidates,
        List<Rectangle> OverlappingRects, Set<IntVar> fdvQueue) {

        boolean contains = false, checkArea = false;

        long area = 0;
        long commonArea = 0;
        int totalNumberOfRectangles = 0;
        int dim = r.dim();
        int startMin[] = new int[dim];
        int stopMax[] = new int[dim];
        int minLength[] = new int[dim];
        int r_min[] = new int[dim], r_max[] = new int[dim];
        for (int i = 0; i < startMin.length; i++) {
            IntDomain rLengthDom = r.length[i].dom();
            startMin[i] = IntDomain.MaxInt;
            stopMax[i] = 0;
            minLength[i] = rLengthDom.min();

            IntDomain rOriginDom = r.origin[i].dom();
            r_min[i] = rOriginDom.min();
            r_max[i] = rOriginDom.max() + rLengthDom.max();
        }

        for (Rectangle s : ((Diff2VarValue) evalRects[index].value()).Rects) {
            boolean overlap = true;

            if (r != s) {

                boolean sChanged = containsChangedVariable(s, fdvQueue);

                IntRectangle Use = new IntRectangle(dim);
                long sArea = 1;
                long partialCommonArea = 1;

                boolean use = true, minLength0 = false;
                int s_min, s_max, start, stop;
                int m = 0, j = 0;
                int sOriginMin[] = new int[dim], sOriginMax[] = new int[dim], sLengthMin[] = new int[dim];

                while (overlap && m < dim) {
                    // check if domains of r and s overlap
                    IntDomain sOriginIdom = s.origin[m].dom();
                    IntDomain sLengthIdom = s.length[m].dom();
                    int sLengthIMin = sLengthIdom.min();
                    int sOriginIMax = sOriginIdom.max();
                    s_min = sOriginIdom.min();
                    s_max = sOriginIMax + sLengthIdom.max();
                    overlap = overlap && intervalOverlap(r_min[m], r_max[m], s_min, s_max);

                    // min start, max stop and min length
                    sOriginMin[m] = s_min;
                    sOriginMax[m] = sOriginIMax + sLengthIMin;
                    sLengthMin[m] = sLengthIMin;

                    // check if s occupies some space
                    start = sOriginIMax;
                    stop = s_min + sLengthIMin;
                    if (start <= stop) {
                        Use.add(start, stop - start);
                        j++;
                    } else
                        use = false;

                    minLength0 = minLength0 || (sLengthMin[m] <= 0);

                    m++;
                }

                if (overlap) {

                    OverlappingRects.add(s);

                    if (use) { // rectangles taking space
                        UsedRect.add(Use);
                        contains = contains || sChanged;
                    }

                    if (!minLength0) { // profile candiates
                        if (j > 0) {
                            ProfileCandidates.add(s);
                            contains = contains || sChanged;
                        }

                        checkArea = true;
                        totalNumberOfRectangles++;
                        for (int i = 0; i < dim; i++) {
                            if (sOriginMin[i] < startMin[i])
                                startMin[i] = sOriginMin[i];
                            if (sOriginMax[i] > stopMax[i])
                                stopMax[i] = sOriginMax[i];
                            if (minLength[i] > sLengthMin[i])
                                minLength[i] = sLengthMin[i];

                            sArea = sArea * sLengthMin[i];
                        }
                        area += sArea;
                    } // profile candidate end

                    // calculate area within rectangle r possible placement
                    for (int i = 0; i < dim; i++) {
                        if (sOriginMin[i] <= r_min[i]) {
                            if (sOriginMax[i] <= r_max[i]) {
                                int distance1 = sOriginMin[i] + sLengthMin[i] - r_min[i];
                                sLengthMin[i] = (distance1 > 0) ? distance1 : 0;
                            } else {
                                // sOriginMax[i] > r_max[i])
                                int rmax = r.origin[i].max() + r.length[i].min();

                                int distance1 = sOriginMin[i] + sLengthMin[i] - r_min[i];
                                int distance2 = sLengthMin[i] - (sOriginMax[i] - rmax);
                                if (distance1 > rmax - r_min[i])
                                    distance1 = rmax - r_min[i];
                                if (distance2 > rmax - r_min[i])
                                    distance2 = rmax - r_min[i];
                                if (distance1 < distance2)
                                    sLengthMin[i] = (distance1 > 0) ? distance1 : 0;
                                else if (distance2 > 0) {
                                    if (distance2 < sLengthMin[i])
                                        sLengthMin[i] = distance2;
                                } else
                                    sLengthMin[i] = 0;
                            }
                        } else // sOriginMin[i] > r_min[i]
                            if (sOriginMax[i] > r_max[i]) {
                                int distance2 = sLengthMin[i] - (sOriginMax[i] - (r.origin[i].max() + r.length[i].min()));
                                if (distance2 > 0) {
                                    if (distance2 < sLengthMin[i])
                                        sLengthMin[i] = distance2;
                                } else
                                    sLengthMin[i] = 0;
                            }
                        partialCommonArea = partialCommonArea * sLengthMin[i];
                    }
                    commonArea += partialCommonArea;
                }
                if (commonArea + r.minArea() > (r_max[0] - r_min[0]) * (r_max[1] - r_min[1]))
                    throw Store.failException;
            }
        }

        if (checkArea) { // check whether there is
            // enough room for all rectangles
            area += r.minArea();
            long availArea = 1;
            long rectNumber = 1;
            for (int i = 0; i < startMin.length; i++) {
                IntDomain rOriginIdom = r.origin[i].dom();
                IntDomain rLengthIdom = r.length[i].dom();
                int rOriginIMin = rOriginIdom.min(), rOriginIMax = rOriginIdom.max(), rLengthIMin = rLengthIdom.min();
                if (rOriginIMin < startMin[i])
                    startMin[i] = rOriginIMin;
                if (rOriginIMax + rLengthIMin > stopMax[i])
                    stopMax[i] = rOriginIMax + rLengthIMin;
            }
            boolean minEqZero = false;
            for (int i = 0; i < startMin.length; i++) {
                availArea = availArea * (stopMax[i] - startMin[i]);
                if (minLength[i] == 0) {
                    minEqZero = true;
                } else
                    rectNumber = rectNumber * ((stopMax[i] - startMin[i]) / minLength[i]);
            }
            if (minEqZero)
                rectNumber = Long.MAX_VALUE;

            if (availArea < area)
                throw Store.failException;
            else
                // check whether there is enough room for
                // all minimal rectangles
                if (rectNumber < (totalNumberOfRectangles + 1))
                    throw Store.failException;
        }

        return contains;
    }

    @Override void profileNarrowing(int i, Rectangle r, List<Rectangle> ProfileCandidates) {
        // check profile first

        IntDomain rOriginIdom = r.origin[i].dom();
        int rOriginIdomMin = rOriginIdom.min();
        int rOriginIdomMax = rOriginIdom.max();
        DiffnProfile Profile = new DiffnProfile();

        for (int j = 0; j < r.dim; j++) {
            if (j != i && r.length[i].min() != 0) {

                Profile.make(j, i, r, rOriginIdomMin, rOriginIdomMax + r.length[i].min(), ProfileCandidates);

                if (Profile.size() != 0) {
                    if (trace) {
                        System.out.println(" *** " + r + "\n" + ProfileCandidates);
                        System.out.println("Profile in dimension " + i + " and " + j + "\n" + Profile);
                    }

                    profileCheckRectangle(Profile, r, i, j);

                }
            }
        }
    }

    @Override public boolean satisfied() {
        boolean sat = true;

        Rectangle recti, rectj;
        int i = 0;
        while (sat && i < rectangles.length) {
            recti = rectangles[i];
            int j = 0;
            Rectangle[] toEvaluate = ((Diff2VarValue) evalRects[i].value()).Rects;
            while (sat && j < toEvaluate.length) {
                rectj = toEvaluate[j];
                sat = sat && !recti.domOverlap(rectj);
                j++;
            }
            i++;
        }
        return sat;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());

        result.append(" : disjoint( ");

        for (int i = 0; i < rectangles.length - 1; i++) {
            result.append(rectangles[i]);
            result.append(", ");

        }
        result.append(rectangles[rectangles.length - 1]);
        result.append(")");

        return result.toString();

    }

}
