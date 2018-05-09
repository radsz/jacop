/*
 * RectangleWithCondition.java
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

import org.jacop.core.IntVar;

import java.util.List;

/**
 * Defines a rectangle used in the diffn constraint.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

class RectangleWithCondition extends Rectangle {

    IntVar c;

    int index = 0;

    public RectangleWithCondition(int i, List<? extends IntVar> R, IntVar cond) {
        super(R);
        c = cond;
        index = i;
    }

    public RectangleWithCondition(int i, IntVar[] R, IntVar cond) {
        super(R);
        c = cond;
        index = i;
    }

    public RectangleWithCondition(int i, Rectangle R, IntVar cond) {
        super(R);
        c = cond;
        index = i;
    }

    public IntVar condition() {
        return c;
    }

    @Override public String toString() {
        String s = "[" + index + ", ";
        s = s + super.toString();
        s = s + ", " + c + "]";
        return s;
    }
}
