/*
 * TestHelper.java
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

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatVar;
import org.jacop.search.*;

import java.util.Arrays;

/**
 * It is helper class that allows perform quickly operation to setup tests.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */
public class TestHelper {

    protected IntVar[] getIntVars(Store store, String idPrefix, int xLength, int xSize) {
        IntVar[] y = new IntVar[xLength];

        for (int i = 0; i < y.length; i++) {
            y[i] = new IntVar(store, idPrefix + i, 0, xSize - 1);
        }
        return y;
    }

    protected IntVar[] getShiftedIntVars(Store store, String idPrefix, int xLength, int xSize) {

        IntVar[] x = new IntVar[xLength];
        for (int i = 0; i < x.length; i++) {
            x[i] = new IntVar(store, idPrefix + i, i, i + xSize - 1);
        }
        return x;
    }

    private FloatVar[] getShiftedFloatVars(Store store, String idPrefix, int xLength, int xSize) {

        FloatVar[] x = new FloatVar[xLength];
        for (int i = 0; i < x.length; i++) {
            x[i] = new FloatVar(store, idPrefix + i, i, i + xSize - 1);
        }
        return x;
    }

    protected int noOfAllSolutions(Store store, IntVar[]... variables) {

        SelectChoicePoint<IntVar> select =
            new SimpleSelect<IntVar>(Arrays.stream(variables).map(Arrays::stream).flatMap(i -> i).toArray(IntVar[]::new),
                new MostConstrainedStatic<IntVar>(), new IndomainMin<IntVar>());

        DepthFirstSearch search = new DepthFirstSearch<IntVar>();

        search.getSolutionListener().searchAll(true);
        search.getSolutionListener().recordSolutions(true);
        search.setAssignSolution(true);

        boolean result = search.labeling(store, select);

        //search.printAllSolutions();
        return search.getSolutionListener().solutionsNo();

    }

    protected int noOfAllSolutionsNoRecord(Store store, IntVar[]... variables) {

        SelectChoicePoint<IntVar> select =
            new SimpleSelect<IntVar>(Arrays.stream(variables).map(Arrays::stream).flatMap(i -> i).toArray(IntVar[]::new),
                new MostConstrainedStatic<IntVar>(), new IndomainMin<IntVar>());

        DepthFirstSearch search = new DepthFirstSearch<IntVar>();

        search.getSolutionListener().searchAll(true);
        search.getSolutionListener().recordSolutions(false);
        search.setAssignSolution(true);

        boolean result = search.labeling(store, select);

        //search.printAllSolutions();
        return search.getSolutionListener().solutionsNo();

    }
}
