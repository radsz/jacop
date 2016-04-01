package org.jacop;

import junit.framework.Assert;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Not;
import org.jacop.constraints.Reified;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.fz.Fz2jacop;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrintOutListener;
import org.jacop.search.Search;
import org.jacop.util.QueueForward;
import org.junit.Test;

/**
 * Author : Radoslaw Szymanek
 * Email : radoslaw.szymanek@osolpro.com
 * <p/>
 * Copyright 2012, All rights reserved.
 */
public class QueueForwardTest {

    @Test
    public void testQueueForwardNot() {

        Store store = new Store();

        FloatVar x = new FloatVar(store, "x", 0.1, 0.1);
        FloatVar y = new FloatVar(store, "y", 0.5, 0.5);

        FloatVar[] v = {x, y};

        store.impose(new Not(new LinearFloat(store, v, new double[] {1,-1}, "==", 0)));

        System.out.println ("Precision = " + FloatDomain.precision());

        // search for solutions and print results
        Search<FloatVar> label = new DepthFirstSearch<FloatVar>();
        SplitSelectFloat<FloatVar> select = new SplitSelectFloat<FloatVar>(store, v, null);
        label.setSolutionListener(new PrintOutListener<FloatVar>());

        boolean result = label.labeling(store, select);

        if ( result ) {
            System.out.println("Solutions: ");
            label.printAllSolutions();
        }
        else
            System.out.println("*** No");

        Assert.assertEquals(true, result);

    }


    @Test
    public void testQueueForwardReified() {

        Store store = new Store();

        FloatVar x = new FloatVar(store, "x", 0.1, 0.4);
        FloatVar y = new FloatVar(store, "y", 0.5, 1.0);

        FloatVar[] v = {x, y};

        IntVar one = new IntVar(store, "one", 1, 1);
        store.impose(new Reified(new LinearFloat(store, v, new double[] {1,-1}, "==", 0), one));

        System.out.println ("Precision = " + FloatDomain.precision());

        // search for solutions and print results
        Search<FloatVar> label = new DepthFirstSearch<FloatVar>();
        SplitSelectFloat<FloatVar> select = new SplitSelectFloat<FloatVar>(store, v, null);
        label.setSolutionListener(new PrintOutListener<FloatVar>());

        boolean result = label.labeling(store, select);

        if ( result ) {
            System.out.println("Solutions: ");
            label.printAllSolutions();
        }
        else
            System.out.println("*** No");

        Assert.assertEquals(false, result);

    }

    @Test
    public void testQueueForwardNestedReifiedNot() {

        Store store = new Store();

        FloatVar x = new FloatVar(store, "x", 0.1, 0.4);
        FloatVar y = new FloatVar(store, "y", 0.5, 1.0);

        FloatVar[] v = {x, y};

        IntVar one = new IntVar(store, "one", 1, 1);

        store.impose(new Reified(new Not(new LinearFloat(store, v, new double[] {1,-1}, "!=", 0)), one));

        // search for solutions and print results
        Search<FloatVar> label = new DepthFirstSearch<FloatVar>();
        SplitSelectFloat<FloatVar> select = new SplitSelectFloat<FloatVar>(store, v, null);
        label.setSolutionListener(new PrintOutListener<FloatVar>());

        boolean result = label.labeling(store, select);

        if ( result ) {
            System.out.println("Solutions: ");
            label.printAllSolutions();
        }
        else
            System.out.println("*** No");

        Assert.assertEquals(false, result);

    }

    @Test
    public void testQueueForwardNoException() {

        Fz2jacop fz2jacop = new Fz2jacop();

        // Just checking if does not throw an exception.
        fz2jacop.main(new String[] { "src/test/fz/queueForwardTest.fzn" } );


    }

}
