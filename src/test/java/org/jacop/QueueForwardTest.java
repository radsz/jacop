/*
 * QueueForwardTest.java
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

import org.jacop.constraints.Not;
import org.jacop.constraints.Reified;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.fz.Fz2jacop;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrintOutListener;
import org.jacop.search.Search;
import org.junit.Ignore;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

/**
 * It is performing testing for QueueForward functionality that makes it possible to
 * forward queueVariable events to nested constraints in a generic fashion no matter
 * in what constraint it is being used in.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */
public class QueueForwardTest {

    //   String nl = System.lineSeparator();
    String nl = "\n";

    @Test public void testQueueForwardNot() {

        Store store = new Store();

        FloatVar x = new FloatVar(store, "x", 0.1, 0.1);
        FloatVar y = new FloatVar(store, "y", 0.5, 0.5);

        FloatVar[] v = {x, y};

        store.impose(new Not(new LinearFloat(v, new double[] {1, -1}, "==", 0)));

        System.out.println("Precision = " + FloatDomain.precision());

        // search for solutions and print results
        Search<FloatVar> label = new DepthFirstSearch<FloatVar>();
        SplitSelectFloat<FloatVar> select = new SplitSelectFloat<FloatVar>(store, v, null);
        label.setSolutionListener(new PrintOutListener<FloatVar>());

        boolean result = label.labeling(store, select);

        if (result) {
            System.out.println("Solutions: ");
            label.printAllSolutions();
        } else
            System.out.println("*** No");

        assertEquals(true, result);

    }


    @Test public void testQueueForwardReified() {

        Store store = new Store();

        FloatVar x = new FloatVar(store, "x", 0.1, 0.4);
        FloatVar y = new FloatVar(store, "y", 0.5, 1.0);

        FloatVar[] v = {x, y};

        IntVar one = new IntVar(store, "one", 1, 1);
        store.impose(new Reified(new LinearFloat(v, new double[] {1, -1}, "==", 0), one));

        System.out.println("Precision = " + FloatDomain.precision());

        // search for solutions and print results
        Search<FloatVar> label = new DepthFirstSearch<FloatVar>();
        SplitSelectFloat<FloatVar> select = new SplitSelectFloat<FloatVar>(store, v, null);
        label.setSolutionListener(new PrintOutListener<FloatVar>());

        boolean result = label.labeling(store, select);

        if (result) {
            System.out.println("Solutions: ");
            label.printAllSolutions();
        } else
            System.out.println("*** No");

        assertEquals(false, result);

    }

    @Test public void testQueueForwardNestedReifiedNot() {

        Store store = new Store();

        FloatVar x = new FloatVar(store, "x", 0.1, 0.4);
        FloatVar y = new FloatVar(store, "y", 0.5, 1.0);

        FloatVar[] v = {x, y};

        IntVar one = new IntVar(store, "one", 1, 1);

        store.impose(new Reified(new Not(new LinearFloat(v, new double[] {1, -1}, "!=", 0)), one));

        // search for solutions and print results
        Search<FloatVar> label = new DepthFirstSearch<FloatVar>();
        SplitSelectFloat<FloatVar> select = new SplitSelectFloat<FloatVar>(store, v, null);
        label.setSolutionListener(new PrintOutListener<FloatVar>());

        boolean result = label.labeling(store, select);

        if (result) {
            System.out.println("Solutions: ");
            label.printAllSolutions();
        } else
            System.out.println("*** No");

        assertEquals(false, result);

    }

    @Test public void testQueueForwardNoException() {

        Fz2jacop fz2jacop = new Fz2jacop();

        // Just checking if does not throw an exception.
        fz2jacop.main(new String[] {"src/test/fz/queueForwardTest.fzn"});

    }

    @Test public void testConstraintImposition() {

        Fz2jacop fz2jacop = new Fz2jacop();

        // Just checking if does not throw an exception.
        fz2jacop.main(new String[] {"src/test/fz/upTo5sec/3_jugs2/3_jugs2.fzn"});

    }

    @Test @Ignore public void testBoundEventCorrection() {

        Fz2jacop fz2jacop = new Fz2jacop();

        // Just checking if does not throw an exception.
        fz2jacop.main(new String[] {"-n 69", "-s", "-a", "-v", "src/test/fz/cc_base.fzn"});


    }

    @Test public void testWolfCabbage() {

        Fz2jacop fz2jacop = new Fz2jacop();

        // Just checking if does not throw an exception.
        fz2jacop.main(new String[] {"-sat", "src/test/fz/wolf_goat_cabbage.fzn"});

    }

    @Test public void testPatternSetMining() {

        Fz2jacop fz2jacop = new Fz2jacop();

        // Just checking if does not throw an exception.
        fz2jacop.main(new String[] {"--verbose", "src/test/fz/upTo5sec/pattern_set_mining/pattern_set_mining.fzn"});

    }


    @Test public void testRemoveConstraint() {

        Fz2jacop fz2jacop = new Fz2jacop();

        // Just checking if does not throw an exception.
        fz2jacop.main(new String[] {"--statistics", "-debug", "--verbose", "src/test/fz/upTo5min/removal-large/nmseq.fzn"});

    }

}
