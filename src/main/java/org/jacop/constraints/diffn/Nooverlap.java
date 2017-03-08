/**
 * Nooverlap.java
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

import java.util.ArrayList;
import java.util.BitSet;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.constraints.Constraint;
import org.jacop.core.TimeStamp;

/**
 * Nooverlap constraint assures that any two rectangles from a vector of rectangles
 * does not overlap in at least one direction. It is a simple implementation which
 * does not use sophisticated techniques for efficient backtracking.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class Nooverlap extends Constraint {

    static int IdNumber = 1;

    static final boolean trace = false, traceNarr = false;

    static final int x = 0, y = 1;

    /*
     * defines how to treat rectangles with width zero
     * strict = true means they still need to be between other rectangles
     * strict = false these rectangles can be anywhere
     */ boolean strict = true;

    Store store;

    /**
     * It specifies the list of rectangles which are of interest for this diff constraint.
     */
    Rectangle[] rectangle;

    /*
     * Defines first position of the variable that is not ground to 1
     */ TimeStamp<BitSet>[] overlapping;

    /*
     * current stamp
     */ int stamp = 0;

    /**
     * It specifies the arguments required to be saved by an XML format as well as
     * the constructor being called to recreate an object from an XML format.
     */
    public static String[] xmlAttributes = {"rectangle"};

    /**
     * It specifies a diff constraint.
     * @param rectangle list of rectangles which can not overlap in at least one dimension.
     */
    public Nooverlap(IntVar[][] rectangle) {

        assert (rectangle != null) : "Rectangles list is null";

        this.queueIndex = 2;
        this.numberId = IdNumber++;

        this.rectangle = new Rectangle[rectangle.length];

        for (int i = 0; i < rectangle.length; i++) {
            assert (rectangle[i] != null) : i + "-th rectangle in the list is null";
            assert (rectangle[i].length == 4) : "The rectangle has to have exactly two dimensions";
            this.rectangle[i] = new Rectangle(rectangle[i][0], rectangle[i][1], rectangle[i][2], rectangle[i][3]);
            this.rectangle[i].index = i;
        }

    }

    /**
     * It specifies a diff constraint.
     * @param rectangle list of rectangles which can not overlap in at least one dimension.
     * @param strict true- zero size rectangles need to be between other rectangles; false- these rectangles can be anywhere
     */
    public Nooverlap(IntVar[][] rectangle, boolean strict) {
        this(rectangle);
        this.strict = strict;
    }

    /**
     * It constructs a diff constraint.
     * @param origin1 list of variables denoting origin of the rectangle in the first dimension.
     * @param origin2 list of variables denoting origin of the rectangle in the second dimension.
     * @param length1 list of variables denoting length of the rectangle in the first dimension.
     * @param length2 list of variables denoting length of the rectangle in the second dimension.
     */

    public Nooverlap(IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2) {

        assert (origin1 != null) : "o1 list is null";
        assert (origin2 != null) : "o2 list is null";
        assert (length1 != null) : "l1 list is null";
        assert (length2 != null) : "l2 list is null";

        int size = origin1.length;
        if (size == origin1.length && size == origin2.length && size == length1.length && size == length2.length) {

            this.queueIndex = 2;

            this.numberId = IdNumber++;
            this.numberArgs = (short) (numberArgs * 4);

            this.rectangle = new Rectangle[size];

            for (int i = 0; i < size; i++) {
                this.rectangle[i] = new Rectangle(origin1[i], origin2[i], length1[i], length2[i]);
                this.rectangle[i].index = i;
            }
        } else {
            String s = "\nNot equal sizes of Variable vectors in Nooverlap";
            throw new IllegalArgumentException(s);
        }
    }

    /**
     * It constructs a diff constraint.
     * @param origin1 list of variables denoting origin of the rectangle in the first dimension.
     * @param origin2 list of variables denoting origin of the rectangle in the second dimension.
     * @param length1 list of variables denoting length of the rectangle in the first dimension.
     * @param length2 list of variables denoting length of the rectangle in the second dimension.
     * @param strict true- zero size rectangles need to be between other rectangles; false- these rectangles can be anywhere
     */

    public Nooverlap(IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2, boolean strict) {
        this(origin1, origin2, length1, length2);
        this.strict = strict;
    }

    /**
     * It specifies a diffn constraint.
     * @param rectangle list of rectangles which can not overlap in at least one dimension.
     */
    public Nooverlap(ArrayList<? extends ArrayList<? extends IntVar>> rectangle) {

        queueIndex = 2;
        numberId = IdNumber++;

        this.rectangle = new Rectangle[rectangle.size()];

        int i = 0;
        numberArgs = (short) (numberArgs * 4);

        for (ArrayList<? extends IntVar> r : rectangle)
            if (r.size() == 4) {
                for (int j = 0; j < r.size(); j++) {
                    this.rectangle[i] =
                        new Rectangle(rectangle.get(i).get(0), rectangle.get(i).get(1), rectangle.get(i).get(2), rectangle.get(i).get(3));
                    this.rectangle[i].index = i;
                    i++;
                }
            } else {
                String s = "\nNot equal sizes of rectangle vectors in Nooverlap";
                throw new IllegalArgumentException(s);
            }
    }


    /**
     * It specifies a diffn constraint.
     * @param rectangle list of rectangles which can not overlap in at least one dimension.
     * @param strict true- zero size rectangles need to be between other rectangles; false- these rectangles can be anywhere
     */
    public Nooverlap(ArrayList<? extends ArrayList<? extends IntVar>> rectangle, boolean strict) {
        this(rectangle);
        this.strict = strict;
    }

    /**
     * It constructs a diff constraint.
     * @param o1 list of variables denoting origin of the rectangle in the first dimension.
     * @param o2 list of variables denoting origin of the rectangle in the second dimension.
     * @param l1 list of variables denoting length of the rectangle in the first dimension.
     * @param l2 list of variables denoting length of the rectangle in the second dimension.
     */
    public Nooverlap(ArrayList<? extends IntVar> o1, ArrayList<? extends IntVar> o2, ArrayList<? extends IntVar> l1,
        ArrayList<? extends IntVar> l2) {

        this(o1.toArray(new IntVar[o1.size()]), o2.toArray(new IntVar[o2.size()]), l1.toArray(new IntVar[l1.size()]),
            l2.toArray(new IntVar[l2.size()]));

    }

    /**
     * It constructs a diff constraint.
     * @param o1 list of variables denoting origin of the rectangle in the first dimension.
     * @param o2 list of variables denoting origin of the rectangle in the second dimension.
     * @param l1 list of variables denoting length of the rectangle in the first dimension.
     * @param l2 list of variables denoting length of the rectangle in the second dimension.
     * @param strict true- zero size rectangles need to be between other rectangles; false- these rectangles can be anywhere
     */
    public Nooverlap(ArrayList<? extends IntVar> o1, ArrayList<? extends IntVar> o2, ArrayList<? extends IntVar> l1,
        ArrayList<? extends IntVar> l2, boolean strict) {
        this(o1, o2, l1, l2);
        this.strict = strict;
    }

    @Override public ArrayList<Var> arguments() {

        ArrayList<Var> variables = new ArrayList<Var>();

        for (Rectangle r : rectangle) {
            for (int i = 0; i < 4; i++)
                variables.add(r.origin(0));
            variables.add(r.origin(1));
            variables.add(r.length(0));
            variables.add(r.length(1));
        }
        return variables;
    }

    @Override public void consistency(Store store) {

        this.store = store;

        do {
            store.propagationHasOccurred = false;

            pruning();

        } while (store.propagationHasOccurred);
    }

    void pruning() {

        for (int j = 0; j < rectangle.length; j++) {
            Rectangle r = rectangle[j];

            BitSet os = overlapping[j].value();
            BitSet o = (BitSet) os.clone();
            if (r.instantiatedBefore(store)) {
                o.clear();
                overlapping[j].update(o);
                continue;
            }
            for (int i = o.nextSetBit(0); i >= 0; i = o.nextSetBit(i + 1)) {
                if (!r.possibleOverlap(rectangle[i])) {
                    o.set(i, false);
                }
            }
            overlapping[j].update(o);

            energyCheck(r, o);

            prune(r, o);
        }
    }

    void prune(Rectangle r, BitSet rects) {

        for (int i = rects.nextSetBit(0); i >= 0; i = rects.nextSetBit(i + 1)) {
            for (int dim = 0; dim < 2; dim++) {
                int oDim = (dim == 0) ? 1 : 0;
                if (r.overlap(rectangle[i], dim))
                    prune(r, rectangle[i], oDim);
            }
        }
    }

    private void prune(Rectangle ri, Rectangle rj, int dim) {

        int lstI = ri.lst(dim);
        int ectI = ri.ect(dim);
        int lstJ = rj.lst(dim);
        int ectJ = rj.ect(dim);

        if (lstI < ectI || lstJ < ectJ) {
            IntVar riOrigin = ri.origin(dim);
            IntVar rjOrigin = rj.origin(dim);

            if (lstI < ectJ) {  // i before j
                IntVar riLength = ri.length(dim);

                if (strict || (ri.exists() && rj.exists())) {
                    rjOrigin.domain.inMin(store.level, rjOrigin, ectI);
                    riOrigin.domain.inMax(store.level, riOrigin, lstJ - riLength.min());
                    riLength.domain.inMax(store.level, riLength, lstJ - ri.est(dim));
                }
            } else if (lstJ < ectI) {  // j before i
                IntVar rjLength = rj.length(dim);

                if (strict || (ri.exists() && rj.exists())) {
                    riOrigin.domain.inMin(store.level, riOrigin, ectJ);
                    rjOrigin.domain.inMax(store.level, rjOrigin, lstI - rjLength.min());
                    rjLength.domain.inMax(store.level, rjLength, lstI - rj.est(dim));
                }
            }
        }
    }

    void energyCheck(Rectangle r, BitSet rects) {

        int xMin = r.est(x);
        int xMax = r.lct(x);
        int yMin = r.est(y);
        int yMax = r.lct(y);
        int xLengthMin = r.length(x).min(), yLengthMin = r.length(y).min();
        int minArea = xLengthMin * yLengthMin;
        for (int j = rects.nextSetBit(0); j >= 0; j = rects.nextSetBit(j + 1)) {
            Rectangle rectj = rectangle[j];
            xMin = Math.min(xMin, rectj.est(x));
            xMax = Math.max(xMax, rectj.lct(x));
            yMin = Math.min(yMin, rectj.est(y));
            yMax = Math.max(yMax, rectj.lct(y));
            int rjXLength = rectj.length(x).min(), rjYLength = rectj.length(y).min();
            xLengthMin = Math.min(xLengthMin, rjXLength);
            yLengthMin = Math.min(yLengthMin, rjYLength);
            minArea += rjXLength * rjYLength;
            if (minArea > (xMax - xMin) * (yMax - yMin))
                throw Store.failException;
        }
        if (xLengthMin > 0 && yLengthMin > 0) {
            int maxNumberRectangles = ((xMax - xMin) / xLengthMin) * ((yMax - yMin) / yLengthMin);
            if (maxNumberRectangles < rects.cardinality() + 1)
                throw Store.failException;
        }
    }

    @Override public int getConsistencyPruningEvent(Var var) {

        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        return IntDomain.ANY;
    }

    // registers the constraint in the constraint store
    @Override @SuppressWarnings("unchecked") public void impose(Store store) {
        IntVar v;

        for (int i = 0; i < rectangle.length; i++) {
            Rectangle r = rectangle[i];
            for (int j = 0; j < 2; j++) {
                v = r.origin(j);
                v.putModelConstraint(this, getConsistencyPruningEvent(v));
            }

            for (int j = 0; j < 2; j++) {
                v = r.length(j);
                v.putModelConstraint(this, getConsistencyPruningEvent(v));
            }
        }

        overlapping = new TimeStamp[rectangle.length];
        for (int i = 0; i < rectangle.length; i++) {
            BitSet bs = new BitSet(rectangle.length);
            bs.flip(0, rectangle.length); // set all bits to true == all rectangles overlap
            bs.set(i, false);             // rectangle does not overlaps with itself
            overlapping[i] = new TimeStamp(store, bs);
        }

        store.addChanged(this);
        store.countConstraint();
    }

    @Override public void removeConstraint() {
        for (Rectangle r : rectangle) {
            for (int i = 0; i < 2; i++) {
                Var v = r.origin(i);
                v.removeConstraint(this);
                v = r.length(i);
                v.removeConstraint(this);
            }
        }
    }

    @Override public boolean satisfied() {
        boolean sat = true;

        int i = 0;
        while (sat && i < rectangle.length) {
            int j = i + 1;
            while (sat && j < rectangle.length) {
                sat = sat && !rectangle[i].overlap(rectangle[j], 0) && !rectangle[i].overlap(rectangle[j], 1);
                j++;
            }
            i++;
        }
        return sat;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());

        result.append(" : nooverlap([");

        int i = 0;
        for (Rectangle r : rectangle) {
            result.append(r);
            if (i < rectangle.length - 1)
                result.append(", ");
            i++;
        }
        return result.append("], " + strict + ")").toString();
    }


    @Override public void increaseWeight() {
        if (increaseWeight) {
            for (Rectangle r : rectangle) {
                for (int i = 0; i < 2; i++)
                    r.origin(i).weight++;
                for (int i = 0; i < 2; i++)
                    r.length(i).weight++;
            }
        }
    }

}
