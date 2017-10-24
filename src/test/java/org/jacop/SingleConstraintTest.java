/*
 * SingleConstraintTest.java
 * <p>
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

import org.jacop.constraints.*;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.table.SimpleTable;
import org.jacop.constraints.table.Table;
import org.jacop.core.*;
import org.jacop.examples.fd.PerfectSquare;
import org.jacop.floats.core.FloatVar;
import org.jacop.search.*;
import org.junit.Ignore;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TestRule;
import org.junit.rules.TestWatcher;
import org.junit.runner.Description;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

/**
 * It is performing testing based on simple problems containing only one constraint.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */
public class SingleConstraintTest extends TestHelper {

    @Rule
    public TestRule watcher = new TestWatcher() {
        protected void starting(Description description) {
            System.out.println("Starting test: " + description.getMethodName());
        }
    };

    @Test public void testAnonymousConstraint() {

        Function<IntVar[], Constraint> listXeqY = ( IntVar[] list ) -> new Constraint(list) {
            
            @Override public void consistency(Store store) {

                do {

                    store.propagationHasOccurred = false;

                    for (int i = 0; i < list.length - 1; i++ ) {

                        IntVar x = list[i];
                        IntVar y = list[i+1];

                        x.domain.in(store.level, x, y.domain);
                        y.domain.in(store.level, y, x.domain);

                    }

                } while (store.propagationHasOccurred);

            }

            @Override public int getDefaultConsistencyPruningEvent() {
                return IntDomain.ANY;
            }
        };

        Store store = new Store();

        int xLength = 3;
        int xSize = 2;
        IntVar[] x = getIntVars(store, "vars", xLength, xSize);

        store.impose(listXeqY.apply(x));

        store.print();
        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(2));


    }

    @Test public void testNegatedIfThen() {

        Store store = new Store();

        int xLength = 3;
        int xSize = 2;
        IntVar[] x = getIntVars(store, "x", xLength, xSize);

        IfThen ifThen = new IfThen(new XneqY(x[0], x[1]), new XeqY(x[1], x[2]));
        
        Not not = new Not(ifThen);
        store.impose(not);

        store.print();
        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(2));

    }

    @Test(expected = IllegalArgumentException.class)
    public void testInvalidTable() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 3;
        IntVar[] x = getIntVars(store, "x", xLength, xSize);
        int[][] tuples = { {0, 0, 0}, {1, 1, 1}, {2, 2, 2}, {1, 2, 1}, {2, 2, 1}, {2, 0, 0} };

        Table c = new Table(x, tuples);
        store.impose(c);

    }

    @Test(expected = IllegalArgumentException.class)
    public void testInvalidSimpleTable() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 3;
        IntVar[] x = getIntVars(store, "x", xLength, xSize);
        int[][] tuples = { {0, 0, 0}, {1, 1, 1}, {2, 2, 2}, {1, 2, 1}, {2, 2, 1}, {2, 0, 0} };

        SimpleTable c = new SimpleTable(x, tuples);
        store.impose(c);

    }


    @Test public void testSimpleTable() {

        Store store = new Store();

        int xLength = 3;
        int xSize = 3;
        IntVar[] x = getIntVars(store, "x", xLength, xSize);
        int[][] tuples = { {0, 0, 0}, {1, 1, 1}, {2, 2, 2}, {1, 2, 1}, {2, 2, 1}, {2, 0, 0} };
        
        SimpleTable c = new SimpleTable(x, tuples);
        store.impose(c);

        store.print();
        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(6));

    }


    @Test public void testBinpacking() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 3;
        IntVar[] items = getIntVars(store, "item", xLength, xSize);
        int[] itemSize = {1, 2, 1, 2};
        IntVar[] binLoad = getIntVars(store, "binLoad", xSize, 4);
        Binpacking c = new Binpacking(items, binLoad, itemSize, 0);
        store.impose(c);

        store.print();
        int noOfSolutions = noOfAllSolutions(store, Stream.concat( Arrays.stream(items), Arrays.stream(binLoad) ).toArray(IntVar[]::new));

        assertThat(noOfSolutions, is(42));

    }

    @Test public void testGeost() {

        assertThat( PerfectSquare.testUsingGeost(new String[]{"1"}), is(true));

    }
    @Test public void testCheckForInputDuplicationSkippsingSingletons2() {

        Store store = new Store();
        int xLength = 4;
        IntVar[] list = getIntVars(store, "list", xLength, 2);
        IntVar dubleton = new IntVar(store, "dubleton", 2, 3);
        IntVar[] parameters = Arrays.copyOf(list, xLength + 2);
        parameters[xLength] = dubleton;
        parameters[xLength + 1] = dubleton;

        Set<Var> dubletons = DecomposedConstraint.getDubletonsSkipSingletons(parameters);

        assertThat(dubletons.size(), is(1));
    }


    @Test public void testCheckForInputDuplicationSkippsingSingletons1() {

        Store store = new Store();
        int xLength = 4;
        IntVar[] list = getIntVars(store, "list", xLength, 2);
        IntVar dubleton = new IntVar(store, "dubleton", 2, 2);
        IntVar[] parameters = Arrays.copyOf(list, xLength + 2);
        parameters[xLength] = dubleton;
        parameters[xLength + 1] = dubleton;
        
        Set<Var> dubletons = DecomposedConstraint.getDubletonsSkipSingletons(parameters);

        assertThat(dubletons.size(), is(0));
    }

    @Test public void testSubcircuit() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 5;
        IntVar[] list = getIntVars(store, "list", xLength, xSize);
        Subcircuit c = new Subcircuit(list);
        store.impose(c);

        store.print();
        int noOfSolutions = noOfAllSolutions(store, list);

        assertThat(noOfSolutions, is(21));

    }

    @Test(expected = IllegalArgumentException.class) public void testInvalidSubcircuit() {

        Store store = new Store();
        IntVar[] list = getIntVars(store, "list", 3, 3);
        list[list.length - 1] = list[0];
        Subcircuit c = new Subcircuit(list);

    }

    @Test(expected = IllegalArgumentException.class) public void testInvalidStretch() {
        IntVar[] list = null;
        Stretch stretch = new Stretch(null, null, null, list);
    }

    @Test public void testStretch() {

        Store store = new Store();

        int[] values = {1, 2};
        int[] min = {1, 2};
        int[] max = {2, 3};
        int xLength = 4;
        int xSize = 4;
        IntVar[] x = getIntVars(store, "x", xLength, xSize);

        Stretch stretch = new Stretch(values, min, max, x);

        store.imposeDecomposition(stretch);

        store.print();
        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(5));

    }


    @Test(expected = IllegalArgumentException.class) public void testInvalidElementVariable() {

        Store store = new Store();
        IntVar x = new IntVar(store, "x", 0, 4);
        IntVar[] list = null;
        ElementVariable c = new ElementVariable(x, list, x);

    }


    @Test(expected = IllegalArgumentException.class) public void testInvalidAmong3() {

        Store store = new Store();
        IntVar min = new IntVar(store, "x", 0, 4);
        IntVar[] list = getIntVars(store, "list", 3, 3);
        list[list.length - 1] = null;
        Among c = new Among(list, new IntervalDomain(1, 2), null);

    }

    @Test(expected = IllegalArgumentException.class) public void testInvalidAmong2() {

        Store store = new Store();

        IntVar[] list = getIntVars(store, "list", 3, 3);
        Among c = new Among(list, new IntervalDomain(1, 2), null);

    }

    @Test(expected = IllegalArgumentException.class) public void testInvalidAmong1() {

        Store store = new Store();

        IntVar min = new IntVar(store, "x", 0, 4);
        IntVar[] list = getIntVars(store, "list", 3, 3);
        Among c = new Among(list, null, min);

    }

    @Test(expected = IllegalArgumentException.class) public void testInvalidMin2() {

        Store store = new Store();

        IntVar min = new IntVar(store, "x", 0, 4);
        IntVar[] list = getIntVars(store, "list", 3, 3);
        list[list.length - 1] = null;
        Min c = new Min(list, min);

    }

    @Test(expected = IllegalArgumentException.class) public void testInvalidMin1() {

        Store store = new Store();

        IntVar min = new IntVar(store, "x", 0, 4);
        IntVar[] list = null;

        Min c = new Min(list, min);

    }


    @Test(expected = IllegalArgumentException.class) public void testInvalidAbs() {

        Store store = new Store();

        IntVar x = new IntVar(store, "x", 0, 4);
        IntVar y = null;

        AbsXeqY absXeqY = new AbsXeqY(x, y);

    }


    @Test public void testExtensionalConflictVA() {

        Store store = new Store();

        int xLength = 2;
        int xSize = 2;
        IntVar[] x = getIntVars(store, "x", xLength, xSize);

        int[][] tuples = new int[][] {{0, 0}, {1, 1}};
        ExtensionalConflictVA extensionalConflictVA = new ExtensionalConflictVA(x, tuples);

        store.impose(extensionalConflictVA);

        store.print();
        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(xSize * xSize - 2));

    }

    @Test public void testIfThenBool() {

        Store store = new Store();

        IntVar x = new IntVar(store, "x", 0, 1);
        IntVar y = new IntVar(store, "y", 0, 1);
        IntVar b = new IntVar(store, "b", 0, 1);

        IfThenBool ifThenBool = new IfThenBool(x, y, b);

        store.impose(ifThenBool);

        store.print();
        int noOfSolutions = noOfAllSolutions(store, new IntVar[] {x, y, b});

        assertThat(noOfSolutions, is(4));

    }

    @Test public void testXor() {

        Store store = new Store();

        IntVar x = new IntVar(store, "x", 0, 4);
        IntVar y = new IntVar(store, "y", 1, 2);
        IntVar b = new IntVar(store, "b", 0, 1);

        PrimitiveConstraint c = new XeqY(x, y);
        Xor xor = new Xor(c, b);

        store.impose(xor);

        store.print();
        int noOfSolutions = noOfAllSolutions(store, new IntVar[] {x, y, b});

        assertThat(noOfSolutions, is(10));

    }

    @Test public void testXexpYeqZ() {

        Store store = new Store();

        IntVar x = new IntVar(store, "x", 0, 4);
        IntVar y = new IntVar(store, "y", 1, 2);
        IntVar z = new IntVar(store, "z", 0, 16);

        XexpYeqZ xexpYeqZ = new XexpYeqZ(x, y, z);

        store.impose(xexpYeqZ);

        store.print();
        int noOfSolutions = noOfAllSolutions(store, new IntVar[] {x, y, z});

        assertThat(noOfSolutions, is(10));

    }

    @Test public void testXmulYeqC() {

        Store store = new Store();

        int xLength = 2;
        int xSize = 3;
        IntVar[] x = getIntVars(store, "x", xLength, xSize);

        XmulCeqZ xmulCeqZ = new XmulCeqZ(x[0], 2, x[1]);

        store.impose(xmulCeqZ);

        store.print();
        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(2));

    }


    @Test public void testXplusYplusCeqZ() {

        Store store = new Store();

        int xLength = 3;
        int xSize = 3;
        IntVar[] x = getIntVars(store, "x", xLength, xSize);

        XplusYplusCeqZ xplusYplusQgtC = new XplusYplusCeqZ(x[0], x[1], 1, x[2]);

        store.impose(xplusYplusQgtC);

        store.print();
        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(xSize));

    }

    @Test public void testXplusYplusQgtC() {

        Store store = new Store();

        int xLength = 3;
        int xSize = 3;
        IntVar[] x = getIntVars(store, "x", xLength, xSize);

        XplusYplusQgtC xplusYplusQgtC = new XplusYplusQgtC(x[0], x[1], x[2], 2);

        store.impose(xplusYplusQgtC);

        store.print();
        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(17));

    }

    @Test public void testAlldiff() {

        Store store = new Store();

        int xLength = 2;
        int xSize = xLength * 2 + 2;
        IntVar[] x = getIntVars(store, "x", xLength, xSize);

        Alldiff alldiff = new Alldiff(x);

        store.impose(alldiff);

        store.print();
        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(30));

    }

    @Test public void testXgtCwithHelperSimpleConstraintsToAvoidNoConstraintBeingActiveSmall() {

        Store store = new Store();

        int xLength = 2;
        int xSize = xLength * 2 + 2;
        IntVar[] x = getIntVars(store, "x", xLength, xSize);

        Arrays.stream(x).forEach(i -> store.impose(new XgtC(i, i.min() + xSize / 2)));
        store.impose(new Alldiff(x));

        store.print();

        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(2));

    }


    @Test public void testXgtCwithHelperSimpleConstraintsToAvoidNoConstraintBeingActive() {

        Store store = new Store();

        int xLength = 4;
        int xSize = xLength * 2 + 2;
        IntVar[] x = getIntVars(store, "x", xLength, xSize);

        Arrays.stream(x).forEach(i -> store.impose(new XgtC(i, i.min() + xSize / 2)));
        store.impose(new Alldiff(x));

        store.print();

        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(24));

    }

    @Test @Ignore
    // TODO, BUG weird problem that has all constraints satisfied immediately int the first search node, making search not explore
    // search space
    public void testXgtC() {

        Store store = new Store();

        int xLength = 1;
        int xSize = 4;
        IntVar[] x = getIntVars(store, "x", xLength, xSize);

        Arrays.stream(x).forEach(i -> store.impose(new XgtC(i, i.min() + xSize / 2)));

        store.print();

        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(16));

    }


    @Test public void testArgMin() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 6;

        IntVar[] x = getShiftedIntVars(store, "x", xLength, xSize + 1);
        IntVar index = new IntVar(store, "index", 0, xLength);
        ArgMin argMin = new ArgMin(x, index, -1, true);

        store.impose(argMin);

        int noOfSolutions = noOfAllSolutions(store, x, new IntVar[] {index});

        assertThat(noOfSolutions, is(2401));

    }

    @Test
    // BUG, problem with using BoundDomain, SmallDenseDomain and asserts, need to investigate.
    // The same problem and fixed applied for ArgMin. Keep this for investigation of the buggy scenario.
    public void testArgMax() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 6;

        IntVar[] x = getShiftedIntVars(store, "x", xLength, xSize + 1);
        IntVar index = new IntVar(store, "index", 0, xLength);
        ArgMax argMax = new ArgMax(x, index, -1, true);

        store.impose(argMax);

        int noOfSolutions = noOfAllSolutions(store, x, new IntVar[] {index});

        assertThat(noOfSolutions, is(2401));

    }

    @Test public void testSum() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 2;

        IntVar[] x = getShiftedIntVars(store, "x", xLength, xSize + 1);
        IntVar sum = new IntVar(store, "sum", 0, xLength * xSize);

        Sum sumConstraint = new Sum(x, sum);

        store.impose(sumConstraint);

        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(15));

    }



    @Test public void testLinear() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 2;

        IntVar[] x = getShiftedIntVars(store, "x", xLength, xSize + 1);

        Linear linear = new Linear(store, x, new int[] {2, 1, 3, 1}, ">=", 5);

        store.impose(linear);

        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(81));

    }

    @Test @Ignore
    // TODO, BUG to be investigated.
    public void testSumWeightDom() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 2;

        IntVar[] x = getIntVars(store, "x", xLength, xSize + 1);

        SumWeightDom sum = new SumWeightDom(x, new int[] {1, 2, 3, 4}, 4);

        store.impose(sum);

        int noOfSolutions = noOfAllSolutions(store, x);

        assertThat(noOfSolutions, is(81));

    }

    @Test public void testIfThenElse() {

        Store store = new Store();

        int size = 3;

        IntVar x = new IntVar(store, "x", 0, size);
        IntVar y = new IntVar(store, "y", 0, size);
        IntVar z = new IntVar(store, "z", 0, size);

        PrimitiveConstraint ifCond = new XeqY(x, y);
        PrimitiveConstraint thenCond = new XneqY(y, z);
        PrimitiveConstraint elseCond = new XeqY(y, z);

        IfThenElse ifThenElse = new IfThenElse(ifCond, thenCond, elseCond);

        store.impose(ifThenElse);

        int noOfSolutions = noOfAllSolutions(store, new IntVar[] {x, y, z});

        assertThat(noOfSolutions, is(24));

    }

    @Test public void testElementIntegerFast() {

        Store store = new Store();

        int size = 3;
        int length = 1000;

        IntVar x = new IntVar(store, "x", 0, length);
        IntVar z = new IntVar(store, "z", 0, length);

        int[] values = IntStream.iterate(1, i -> i + 1).map(i -> i / size).limit(length).toArray();

        ElementIntegerFast ifThenElse = new ElementIntegerFast(x, values, z);

        store.impose(ifThenElse);

        int noOfSolutions = noOfAllSolutions(store, new IntVar[] {x, z});

        assertThat(noOfSolutions, is(length));

    }



    @Test public void testEqBool() {

        Store store = new Store();

        int xLength = 4;

        IntVar[] x = getIntVars(store, "x", xLength, 2);
        IntVar n = new IntVar(store, "sum", 0, 1);
        EqBool eqBool = new EqBool(x, n);

        store.impose(eqBool);

        int noOfSolutions = noOfAllSolutions(store, x, new IntVar[] {n});

        assertThat(noOfSolutions, is(16));

    }



    @Test public void testLex() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 2;

        IntVar[] x1 = getShiftedIntVars(store, "a", xLength, xSize + 1);
        IntVar[] x2 = getIntVars(store, "b", xLength + xSize, xLength);

        Lex lex = new Lex(new IntVar[][] {x1, x2}, true);

        store.imposeDecomposition(lex);

        int noOfSolutions = noOfAllSolutions(store, x1, x2);

        assertThat(noOfSolutions, is(188640));

    }


    @Test public void testGCC() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 2;

        IntVar[] x = getShiftedIntVars(store, "x", xLength, xSize + 1);

        IntVar[] counters = getIntVars(store, "counters", xLength + xSize, xLength);

        GCC gcc = new GCC(x, counters);

        store.impose(gcc);

        int noOfSolutions = noOfAllSolutions(store, x, counters);

        assertThat(noOfSolutions, is(81));

    }


    @Test public void testAmongVar() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 3;
        int nMax = 3;

        IntVar[] x = getShiftedIntVars(store, "x", xLength, xSize);

        IntVar[] y = getIntVars(store, "y", xLength + xSize, xSize);

        IntVar n = new IntVar(store, "n", 0, nMax);
        AmongVar amongVar = new AmongVar(x, y, n);

        store.impose(amongVar);

        int noOfSolutions = noOfAllSolutions(store, x, y, new IntVar[] {n});

        assertThat(noOfSolutions, is(177147));

    }


    @Test public void testDiff() {

        Store store = new Store();

        int noOfRectangles = 4;
        int xSize = 2;
        int ySize = 2;
        int durationSize = 3;

        IntVar[] origin1 = getShiftedIntVars(store, "OX", noOfRectangles, xSize);
        IntVar[] origin2 = getIntVars(store, "OY", noOfRectangles, ySize);

        IntVar[] length1 = getShiftedIntVars(store, "DX", noOfRectangles, durationSize);
        IntVar[] length2 = getIntVars(store, "DY", noOfRectangles, durationSize);

        Diff diff = new Diff(origin1, origin2, length1, length2);

        store.impose(diff);

        int noOfSolutions = noOfAllSolutions(store, origin1, origin2, length1, length2);

        assertThat(noOfSolutions, is(741642));

    }

    @Test public void testDisjoint() {

        Store store = new Store();

        int noOfRectangles = 4;
        int xSize = 2;
        int ySize = 2;
        int durationSize = 3;

        IntVar[] origin1 = getShiftedIntVars(store, "OX", noOfRectangles, xSize);
        IntVar[] origin2 = getIntVars(store, "OY", noOfRectangles, ySize);

        IntVar[] length1 = getShiftedIntVars(store, "DX", noOfRectangles, durationSize);
        IntVar[] length2 = getIntVars(store, "DY", noOfRectangles, durationSize);

        Disjoint diff = new Disjoint(origin1, origin2, length1, length2);

        store.impose(diff);

        int noOfSolutions = noOfAllSolutions(store, origin1, origin2, length1, length2);

        assertThat(noOfSolutions, is(699189));

    }

    @Test public void testDiff2() {

        Store store = new Store();

        int noOfRectangles = 4;
        int xSize = 2;
        int ySize = 2;
        int durationSize = 3;

        IntVar[] origin1 = getShiftedIntVars(store, "OX", noOfRectangles, xSize);
        IntVar[] origin2 = getIntVars(store, "OY", noOfRectangles, ySize);

        IntVar[] length1 = getShiftedIntVars(store, "DX", noOfRectangles, durationSize);
        IntVar[] length2 = getIntVars(store, "DY", noOfRectangles, durationSize);

        Diff2 diff2 = new Diff2(origin1, origin2, length1, length2);

        store.impose(diff2);

        int noOfSolutions = noOfAllSolutions(store, origin1, origin2, length1, length2);

        assertThat(noOfSolutions, is(791208));

    }

    @Test public void testDisjointConditional() {

        Store store = new Store();

        int noOfRectangles = 3;
        int xSize = 2;
        int ySize = 2;
        int durationSize = 3;

        IntVar[] origin1 = getShiftedIntVars(store, "OX", noOfRectangles, xSize);
        IntVar[] origin2 = getIntVars(store, "OY", noOfRectangles, ySize);

        IntVar[] length1 = getShiftedIntVars(store, "DX", noOfRectangles, durationSize);
        IntVar[] length2 = getIntVars(store, "DY", noOfRectangles, durationSize);

        List<List<Integer>> conditionalPairs = new ArrayList<>();
        conditionalPairs.add(new ArrayList<>(Arrays.asList(new Integer[] {1, 3})));
        conditionalPairs.add(new ArrayList<>(Arrays.asList(new Integer[] {2, 3})));

        IntVar[] exceptionCondition = getIntVars(store, "condition", 2, 2);

        Diff disjointConditional = new DisjointConditional(origin1, origin2, length1, length2, conditionalPairs,
            Arrays.asList(exceptionCondition));

        store.impose(disjointConditional);

        int noOfSolutions = noOfAllSolutions(store, origin1, origin2, length1, length2, exceptionCondition);

        assertThat(noOfSolutions, is(141141));

    }


    @Test public void testValues() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 7;

        IntVar[] x = getIntVars(store, "x", xLength, xSize);
        IntVar n = new IntVar(store, "sum", 0, 1);
        Values values = new Values(x, n);

        store.impose(values);

        int noOfSolutions = noOfAllSolutions(store, x, new IntVar[] {n});

        assertThat(noOfSolutions, is(xSize));

    }

    @Test public void testValues2() {

        Store store = new Store();

        int xLength = 4;
        int xSize = 4;

        IntVar[] x = getIntVars(store, "x", xLength, xSize);
        IntVar n = new IntVar(store, "sum", 1, 2);
        Values values = new Values(x, n);

        store.impose(values);

        int noOfSolutions = noOfAllSolutions(store, x, new IntVar[] {n});

        assertThat(noOfSolutions, is(88));

    }


}
