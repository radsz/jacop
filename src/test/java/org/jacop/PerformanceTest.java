/*
 * PerformanceTest.java
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

package org.jacop;

import org.jacop.constraints.LinearInt;
import org.jacop.constraints.SumWeight;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.Test;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

/**
 * It is performing testing for performance comparisons.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */
public class PerformanceTest extends TestHelper {

    @Test public void testSumWeightPerformance() {

        Store store = new Store();

        int xLength = 15;
        int xSize = 3;

        IntVar[] x = getIntVars(store, "x", xLength, xSize + 1);
        IntVar n = new IntVar(store, "sum", 10, 40);
        SumWeight sum = new SumWeight(x, new int[] {1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5}, n);

        store.impose(sum);

        int noOfSolutions = noOfAllSolutionsNoRecord(store, x, new IntVar[] {n});

        assertThat(noOfSolutions, is(31733221));

    }

    @Test public void testLinearIntPerformance() {

        Store store = new Store();

        int xLength = 15;
        int xSize = 3;

        IntVar[] x = getIntVars(store, "x", xLength, xSize + 1);
        IntVar n = new IntVar(store, "sum", 10, 40);
        LinearInt sum = new LinearInt(x, new int[] {1, 2, 3, 4, 5, 1, 2, 3, 4, 5, 1, 2, 3, 4, 5}, "==", n);

        store.impose(sum);

        int noOfSolutions = noOfAllSolutionsNoRecord(store, x, new IntVar[] {n});

        assertThat(noOfSolutions, is(31733221));

    }

    @Test public void testSumWeightPerformance2() {

        Store store = new Store();

        int xLength = 50;
        int xSize = 2;

        IntVar[] x = getIntVars(store, "x", xLength, xSize + 1);
        IntVar n = new IntVar(store, "sum", 237, 240);
        int weights[] = new int[xLength];
        for (int i = 0; i < weights.length; i++)
            weights[i] = i % 6;

        SumWeight sum = new SumWeight(x, weights, n);

        store.impose(sum);

        int noOfSolutions = noOfAllSolutionsNoRecord(store, x, new IntVar[] {n});

        assertThat(noOfSolutions, is(81428571));

    }


    @Test public void testLinearIntPerformance2() {

        Store store = new Store();

        int xLength = 50;
        int xSize = 2;

        IntVar[] x = getIntVars(store, "x", xLength, xSize + 1);
        IntVar n = new IntVar(store, "sum", 237, 240);
        int weights[] = new int[xLength];
        for (int i = 0; i < weights.length; i++)
            weights[i] = i % 6;

        LinearInt sum = new LinearInt(x, weights, "==", n);

        store.impose(sum);

        int noOfSolutions = noOfAllSolutionsNoRecord(store, x, new IntVar[] {n});

        assertThat(noOfSolutions, is(81428571));

    }


}
