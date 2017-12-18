/*
 * SumFloat.java
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

package org.jacop.floats.constraints;


import org.jacop.floats.core.FloatVar;
import org.jacop.core.Store;

/**
 * SumFloat constraint implements the weighted summation over several
 * Variable's . It provides the weighted sum from all Variable's on the list.
 *
 * This version works as argument to Reified and Xor constraints.  For
 * other constraints And, Or, Not, Eq, IfThen, IfThenElse it does not
 * work currently.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class SumFloat extends LinearFloat {


    /**
     * @param store current store
     * @param list variables which are being multiplied by weights.
     * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum variable containing the sum of weighted variables.
     * @deprecated SumFloat constraint does not use Store parameter any longer.
     */
    @Deprecated
    public SumFloat(Store store, FloatVar[] list, String rel, FloatVar sum) {

        super(store, list, getFilledArray(list.length), rel, sum);
    }

    /**
     * @param list variables which are being multiplied by weights.
     * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}", "{@literal >=}", "{@literal !=}"
     * @param sum variable containing the sum of weighted variables.
     */
    public SumFloat(FloatVar[] list, String rel, FloatVar sum) {

        super(list, getFilledArray(list.length), rel, sum);
    }


    private static double[] getFilledArray(int n) {
        double[] a = new double[n];
        java.util.Arrays.fill(a, 1);
        return a;
    }
}
