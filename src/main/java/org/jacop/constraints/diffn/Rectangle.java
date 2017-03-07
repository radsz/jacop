/**
 * Rectangle.java
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

import org.jacop.core.IntVar;

/**
 * Defines a rectangle used in the diffn constraint.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class Rectangle {

    int index;

    /**
     * It specifies the the rectangle.
     */
    public IntVar[] origin;
    public IntVar[] length;


    /**
     * It constructs a rectangle.
     *
     * @param o1 origin in dimension 0
     * @param o2 origin in dimension 1
     * @param l1 length in dimension 0
     * @param l2 length in dimension 1
     *
     */
    public Rectangle(IntVar o1, IntVar o2, IntVar l1, IntVar l2) {
        int dim = 2;
        origin = new IntVar[dim];
        length = new IntVar[dim];
        origin[0] = o1;
        origin[1] = o2;
        length[0] = l1;
        length[1] = l2;
    }

    /**
     * It constructs a rectangle.
     *
     * @param list it specifies for each dimension (one after the other) its origin and length.
     *
     */
    public Rectangle(IntVar[] list) {
        int dim = 2;
        origin = new IntVar[dim];
        length = new IntVar[dim];
        for (int i = 0; i < dim; i++) {
            origin[i] = list[i];
            length[i] = list[i + dim];
        }
    }

    /**
     * It constructs a rectangle.
     *
     * @param list it specifies for each dimension (one after the other) its origin and length.
     *
     */
    public Rectangle(ArrayList<? extends IntVar> list) {
        this(list.toArray(new IntVar[list.size()]));
    }

    IntVar origin(int dim) {
        return origin[dim];
    }

    IntVar length(int dim) {
        return length[dim];
    }

    int est(int dim) {
        return origin[dim].min();
    }

    int lst(int dim) {
        return origin[dim].max();
    }

    int ect(int dim) {
        return origin[dim].min() + length[dim].min();
    }

    int lct(int dim) {
        return origin[dim].max() + length[dim].max();
    }

    /*
     * This rectangle and rectangle r must overlap
     *
     * @param r the other rectangle
     * @param dim dimension of overlapping
     * @return true if overlapping, false otherwise
     */
    boolean overlap(Rectangle r, int dim) {

        return (lst(dim) < ect(dim) && r.ect(dim) > lst(dim) && ect(dim) > r.lst(dim)) || (r.lst(dim) < r.ect(dim) && ect(dim) > r.lst(dim)
            && r.ect(dim) > lst(dim));
    }


    boolean noOverlap(Rectangle r, int dim) {
        return est(dim) >= r.lct(dim) || r.est(dim) >= lct(dim);
    }

    boolean possibleOverlap(Rectangle r) {
        if (noOverlap(r, 0) || noOverlap(r, 1)) {
            return false;
        }
        return true;
    }

    boolean instantiated() {
        return origin[0].singleton() && origin[1].singleton() && length[0].singleton() && length[1].singleton();
    }

    boolean instantiatedBefore(org.jacop.core.Store store) {
        int level = store.level;
        return origin[0].singleton() && origin[1].singleton() && origin[0].domain.stamp < level && origin[1].domain.stamp < level
            && length[0].singleton() && length[1].singleton() && length[0].domain.stamp < level && length[1].domain.stamp < level;
    }

    boolean exists() {
        return length[0].min() > 0 && length[1].min() > 0;
    }

    @Override public String toString() {
        int dim = 2;
        String S = "[" + index + ": ";
        for (int i = 0; i < dim; i++) {
            S += origin[i] + ", ";
        }
        for (int i = 0; i < dim; i++) {
            S += length[i];
            if (i < dim - 1)
                S += ", ";
        }
        S += "]";
        return S;
    }

}
