/**
 *  QueueForwardTest.java
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver.
 *
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
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
import org.jacop.fz.Options;
import org.jacop.fz.Parser;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrintOutListener;
import org.jacop.search.Search;
import org.junit.Test;

import java.io.*;
import java.util.Scanner;


import static java.lang.System.in;
import static org.junit.Assert.*;


/**
 *
 * It is performing testing for QueueForward functionality that makes it possible to
 * forward queueVariable events to nested constraints in a generic fashion no matter
 * in what constraint it is being used in.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.4
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

            assertEquals(true, result);

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

            assertEquals(false, result);

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

            assertEquals(false, result);

        }

        @Test
        public void testQueueForwardNoException() {

            Fz2jacop fz2jacop = new Fz2jacop();

            // Just checking if does not throw an exception.
            fz2jacop.main(new String[] { "src/test/fz/queueForwardTest.fzn" } );


        }

    @Test
    public void testMinizinc() throws IOException {

        Fz2jacop fz2jacop = new Fz2jacop();

        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        PrintStream old = System.out;
        System.setOut(new PrintStream(baos));
        // Just checking if does not throw an exception.
        fz2jacop.main(new String[]{"src/test/fz/CostasArrayTest.fzn"});

        System.out.flush();
        System.setOut(old);

        String result = baos.toString();
        System.out.println(result);

        String filePath = new File("src/test/fz/CostasArrayTest.out").getAbsolutePath();
        FileReader fileReader = new FileReader(filePath);
        BufferedReader bufferedReader = new BufferedReader(fileReader);

        String textLine = bufferedReader.readLine();
        String expected = "";

        do {
            expected += textLine + "\n";
            textLine = bufferedReader.readLine();

        } while(textLine != null);

        bufferedReader.close();

        assertEquals(expected, result);
    }


    @Test
    public void testCvrp() {

        Fz2jacop fz2jacop = new Fz2jacop();

        // Just checking if does not throw an exception.
       // fz2jacop.main(new String[]{"src/test/fz/cvrp.fzn"});


    }


    @Test
    public void testFreePizza() {

        Fz2jacop fz2jacop = new Fz2jacop();

        // Just checking if does not throw an exception.
       // fz2jacop.main(new String[]{"src/test/fz/freepizza.fzn"});


    }


    @Test
    public void testQueueForwardTest() {

        Fz2jacop fz2jacop = new Fz2jacop();

        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        PrintStream old = System.out;
        System.setOut(new PrintStream(baos));

        // Just checking if does not throw an exception.
        fz2jacop.main(new String[]{"src/test/fz/queueForwardTest.fzn"});

        System.out.flush();
        System.setOut(old);

        String result = baos.toString();
        System.out.println(result);

        assertEquals("x1 = 0;\n" +
                "x2 = -1;\n" +
                "x3 = 0;\n" +
                "x4 = true;\n" +
                "----------\n", result);
    }


    @Test
    public void testGridColoring() {

        Fz2jacop fz2jacop = new Fz2jacop();

       // ByteArrayOutputStream baos = new ByteArrayOutputStream();
       // PrintStream old = System.out;
       // System.setOut(new PrintStream(baos));

        // Just checking if does not throw an exception.
        fz2jacop.main(new String[]{"src/test/fz/GridColoring.fzn"});

       // System.out.flush();
       // System.setOut(old);

        //String result = baos.toString();
        //System.out.println(result);


/*assertEquals("x1 = 0;\n" +
                "x2 = -1;\n" +
                "x3 = 0;\n" +
                "x4 = true;\n" +
                "----------\n", result);*/

    }


    @Test
    public void testModel() {

        Fz2jacop fz2jacop = new Fz2jacop();

        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        PrintStream old = System.out;
        System.setOut(new PrintStream(baos));

        // Just checking if does not throw an exception.
        fz2jacop.main(new String[]{"src/test/fz/model.fzn"});

        System.out.flush();
        System.setOut(old);

        String result = baos.toString();
        System.out.println(result);

        assertEquals("objective = 210944;\n" +
                "def = array1d(0..49, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0]);\n" +
                "loc = array1d(0..49, [31, 0, 31, 31, 0, 31, 0, 31, 31, 0, 31, 0, 31, 31, 0, 31, 0, 34, 31, 0, 31, 31, 31, 0, 31, 31, 31, 31, 0, 31, 0, 31, 0, 31, 0, 31, 0, 31, 31, 31, 0, 31, 0, 0, 31, 31, 0, 31, 31, 0]);\n" +
                "sel = array1d(0..115, [true, false, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, true]);\n" +
                "place = array1d(0..115, [2, 5, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 5, 5, 1, 5, 5, 0, 5, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 5, 5, 1, 5, 5, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 5, 5, 5, 5, 5, 5, 5, 1, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0]);\n" +
                "succ = array1d(0..5, [4, 3, 5, 2, 1, 0]);\n" +
                "----------\n" +
                "==========\n", result);
    }

    @Test
    public void testLargeCumulative() {

        Fz2jacop fz2jacop = new Fz2jacop();

        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        PrintStream old = System.out;
        System.setOut(new PrintStream(baos));

        // Just checking if does not throw an exception.
        fz2jacop.main(new String[]{"src/test/fz/model.fzn"});

        System.out.flush();
        System.setOut(old);

        String result = baos.toString();
        System.out.println(result);

        assertEquals("objective = 210944;\n" +
                "def = array1d(0..49, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 2, 0]);\n" +
                "loc = array1d(0..49, [31, 0, 31, 31, 0, 31, 0, 31, 31, 0, 31, 0, 31, 31, 0, 31, 0, 34, 31, 0, 31, 31, 31, 0, 31, 31, 31, 31, 0, 31, 0, 31, 0, 31, 0, 31, 0, 31, 31, 31, 0, 31, 0, 0, 31, 31, 0, 31, 31, 0]);\n" +
                "sel = array1d(0..115, [true, false, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, true, true, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, true]);\n" +
                "place = array1d(0..115, [2, 5, 3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 5, 5, 1, 5, 5, 0, 5, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 5, 5, 1, 5, 5, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0, 5, 5, 5, 5, 5, 5, 5, 1, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0]);\n" +
                "succ = array1d(0..5, [4, 3, 5, 2, 1, 0]);\n" +
                "----------\n" +
                "==========\n", result);
    }

}
