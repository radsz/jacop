package org.jacop;

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatVar;
import org.jacop.search.*;

import java.util.Arrays;

/**
 * Author : Radoslaw Szymanek
 *
 *
 * Copyright 2012, All rights reserved.
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
