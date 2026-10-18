/*
 * SingleConstraintTest.java
 * <p>
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Among;
import org.jacop.constraints.AmongVar;
import org.jacop.constraints.ArgMax;
import org.jacop.constraints.ArgMin;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.Diff;
import org.jacop.constraints.Diff2;
import org.jacop.constraints.Disjoint;
import org.jacop.constraints.DisjointConditional;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.ElementVariable;
import org.jacop.constraints.EqBool;
import org.jacop.constraints.ExtensionalConflictVa;
import org.jacop.constraints.GCC;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.IfThenBool;
import org.jacop.constraints.IfThenElse;
import org.jacop.constraints.Lex;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Min;
import org.jacop.constraints.NoGood;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.SoftAlldifferent;
import org.jacop.constraints.Stretch;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.Values;
import org.jacop.constraints.ViolationMeasure;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XexpYeqZ;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.Xor;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.geost.ExternalConstraint;
import org.jacop.constraints.geost.Geost;
import org.jacop.constraints.geost.GeostObject;
import org.jacop.constraints.geost.NonOverlapping;
import org.jacop.constraints.geost.Shape;
import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.constraints.table.SimpleTable;
import org.jacop.constraints.table.Table;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.BeforeEachCallback;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.api.extension.ExtensionContext;

/**
 * It is performing testing based on simple problems containing only one constraint.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@ExtendWith(SingleConstraintTest.TestWatcherExtension.class)
@Slf4j
class SingleConstraintTest extends TestHelper {

  @Test
  void testAnonymousConstraint() {

    Function<IntVar[], Constraint> listXeqY =
        (IntVar[] list) ->
            new Constraint(list) {

              @Override
              public void consistency(Store store) {

                do {

                  store.propagationHasOccurred = false;

                  for (int i = 0; i < list.length - 1; i++) {

                    IntVar x = list[i];
                    IntVar y = list[i + 1];

                    x.domain.in(store.level, x, y.domain);
                    y.domain.in(store.level, y, x.domain);
                  }

                } while (store.propagationHasOccurred);
              }
            };

    Store store = new Store();

    int xLength = 3;
    int xSize = 2;
    IntVar[] x = getIntVars(store, "vars", xLength, xSize);

    store.impose(listXeqY.apply(x));

    store.print();
    int noOfSolutions = noOfAllSolutions(store, x);

    assertThat(noOfSolutions).isEqualTo(2);
  }

  @Test
  void testNegatedIfThen() {

    Store store = new Store();

    int xLength = 3;
    int xSize = 2;
    IntVar[] x = getIntVars(store, "x", xLength, xSize);

    IfThen ifThen = new IfThen(new XneqY(x[0], x[1]), new XeqY(x[1], x[2]));

    Not not = new Not(ifThen);
    store.impose(not);

    store.print();
    int noOfSolutions = noOfAllSolutions(store, x);

    assertThat(noOfSolutions).isEqualTo(2);
  }

  @Test
  void testInvalidTable() {

    Store store = new Store();

    int xLength = 4;
    int xSize = 3;
    IntVar[] x = getIntVars(store, "x", xLength, xSize);
    int[][] tuples = {{0, 0, 0}, {1, 1, 1}, {2, 2, 2}, {1, 2, 1}, {2, 2, 1}, {2, 0, 0}};

    assertThatThrownBy(() -> new Table(x, tuples)).isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testInvalidSimpleTable() {

    Store store = new Store();

    int xLength = 4;
    int xSize = 3;
    IntVar[] x = getIntVars(store, "x", xLength, xSize);
    int[][] tuples = {{0, 0, 0}, {1, 1, 1}, {2, 2, 2}, {1, 2, 1}, {2, 2, 1}, {2, 0, 0}};

    assertThatThrownBy(() -> new SimpleTable(x, tuples))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testSimpleTable() {

    Store store = new Store();

    int xLength = 3;
    int xSize = 3;
    IntVar[] x = getIntVars(store, "x", xLength, xSize);
    int[][] tuples = {{0, 0, 0}, {1, 1, 1}, {2, 2, 2}, {1, 2, 1}, {2, 2, 1}, {2, 0, 0}};

    SimpleTable c = new SimpleTable(x, tuples);
    store.impose(c);

    store.print();
    int noOfSolutions = noOfAllSolutions(store, x);

    assertThat(noOfSolutions).isEqualTo(6);
  }

  @Test
  void testBinpacking() {

    Store store = new Store();

    int xLength = 4;
    int xSize = 3;
    IntVar[] items = getIntVars(store, "item", xLength, xSize);
    int[] itemSize = {1, 2, 1, 2};
    IntVar[] binLoad = getIntVars(store, "binLoad", xSize, 4);
    Binpacking c = new Binpacking(items, binLoad, itemSize, 0);
    store.impose(c);

    store.print();
    int noOfSolutions =
        noOfAllSolutions(
            store,
            Stream.concat(Arrays.stream(items), Arrays.stream(binLoad)).toArray(IntVar[]::new));

    assertThat(noOfSolutions).isEqualTo(42);
  }

  @Test
  void testCheckForInputDuplicationSkippsingSingletons2() {

    Store store = new Store();
    int xLength = 4;
    IntVar[] list = getIntVars(store, "list", xLength, 2);
    IntVar dubleton = new IntVar(store, "dubleton", 2, 3);
    IntVar[] parameters = Arrays.copyOf(list, xLength + 2);
    parameters[xLength] = dubleton;
    parameters[xLength + 1] = dubleton;

    Set<Var> dubletons = DecomposedConstraint.getDubletonsSkipSingletons(parameters);

    assertThat(dubletons).hasSize(1);
  }

  @Test
  void testCheckForInputDuplicationSkippsingSingletons1() {

    Store store = new Store();
    int xLength = 4;
    IntVar[] list = getIntVars(store, "list", xLength, 2);
    IntVar dubleton = new IntVar(store, "dubleton", 2, 2);
    IntVar[] parameters = Arrays.copyOf(list, xLength + 2);
    parameters[xLength] = dubleton;
    parameters[xLength + 1] = dubleton;

    Set<Var> dubletons = DecomposedConstraint.getDubletonsSkipSingletons(parameters);

    assertThat(dubletons).isEmpty();
  }

  @Test
  void testSubcircuit() {

    Store store = new Store();

    int xLength = 4;
    int xSize = 5;
    IntVar[] list = getIntVars(store, "list", xLength, xSize);
    Subcircuit c = new Subcircuit(list);
    store.impose(c);

    store.print();
    int noOfSolutions = noOfAllSolutions(store, list);

    assertThat(noOfSolutions).isEqualTo(21);
  }

  @Test
  void testInvalidSubcircuit() {

    Store store = new Store();
    IntVar[] list = getIntVars(store, "list", 3, 3);
    list[list.length - 1] = list[0];
    assertThatThrownBy(() -> new Subcircuit(list)).isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testInvalidStretch() {
    IntVar[] list = null;
    assertThatThrownBy(() -> new Stretch(null, null, null, list))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testStretch() {

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

    assertThat(noOfSolutions).isEqualTo(5);
  }

  @Test
  void testInvalidElementVariable() {

    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 4);
    IntVar[] list = null;
    assertThatThrownBy(() -> new ElementVariable(x, list, x))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testInvalidAmong3() {

    Store store = new Store();
    IntVar[] list = getIntVars(store, "list", 3, 3);
    list[list.length - 1] = null;
    assertThatThrownBy(() -> new Among(list, new IntervalDomain(1, 2), null))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testInvalidAmong2() {

    Store store = new Store();

    IntVar[] list = getIntVars(store, "list", 3, 3);
    assertThatThrownBy(() -> new Among(list, new IntervalDomain(1, 2), null))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testInvalidAmong1() {

    Store store = new Store();

    IntVar min = new IntVar(store, "x", 0, 4);
    IntVar[] list = getIntVars(store, "list", 3, 3);
    assertThatThrownBy(() -> new Among(list, null, min))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testInvalidMin2() {

    Store store = new Store();

    IntVar min = new IntVar(store, "x", 0, 4);
    IntVar[] list = getIntVars(store, "list", 3, 3);
    list[list.length - 1] = null;
    assertThatThrownBy(() -> new Min(list, min)).isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testInvalidMin1() {

    Store store = new Store();

    IntVar min = new IntVar(store, "x", 0, 4);
    IntVar[] list = null;

    assertThatThrownBy(() -> new Min(list, min)).isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testInvalidAbs() {

    Store store = new Store();

    IntVar x = new IntVar(store, "x", 0, 4);
    IntVar y = null;

    assertThatThrownBy(() -> new AbsXeqY(x, y)).isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testExtensionalConflictVA() {

    Store store = new Store();

    int xLength = 2;
    int xSize = 2;
    IntVar[] x = getIntVars(store, "x", xLength, xSize);

    int[][] tuples = new int[][] {{0, 0}, {1, 1}};
    ExtensionalConflictVa extensionalConflictVA = new ExtensionalConflictVa(x, tuples);

    store.impose(extensionalConflictVA);

    store.print();
    int noOfSolutions = noOfAllSolutions(store, x);

    assertThat(noOfSolutions).isEqualTo(xSize * xSize - 2);
  }

  @Test
  void testIfThenBool() {

    Store store = new Store();

    IntVar x = new IntVar(store, "x", 0, 1);
    IntVar y = new IntVar(store, "y", 0, 1);
    IntVar b = new IntVar(store, "b", 0, 1);

    IfThenBool ifThenBool = new IfThenBool(x, y, b);

    store.impose(ifThenBool);

    store.print();
    int noOfSolutions = noOfAllSolutions(store, new IntVar[] {x, y, b});

    assertThat(noOfSolutions).isEqualTo(4);
  }

  @Test
  void testXor() {

    Store store = new Store();

    IntVar x = new IntVar(store, "x", 0, 4);
    IntVar y = new IntVar(store, "y", 1, 2);
    IntVar b = new IntVar(store, "b", 0, 1);

    PrimitiveConstraint c = new XeqY(x, y);
    Xor xor = new Xor(c, b);

    store.impose(xor);

    store.print();
    int noOfSolutions = noOfAllSolutions(store, new IntVar[] {x, y, b});

    assertThat(noOfSolutions).isEqualTo(10);
  }

  @Test
  void testXexpYeqZ() {

    Store store = new Store();

    IntVar x = new IntVar(store, "x", 0, 4);
    IntVar y = new IntVar(store, "y", 1, 2);
    IntVar z = new IntVar(store, "z", 0, 16);

    XexpYeqZ xexpYeqZ = new XexpYeqZ(x, y, z);

    store.impose(xexpYeqZ);

    store.print();
    int noOfSolutions = noOfAllSolutions(store, new IntVar[] {x, y, z});

    assertThat(noOfSolutions).isEqualTo(10);
  }

  @Test
  void testXmulYeqC() {

    Store store = new Store();

    int xLength = 2;
    int xSize = 3;
    IntVar[] x = getIntVars(store, "x", xLength, xSize);

    XmulCeqZ xmulCeqZ = new XmulCeqZ(x[0], 2, x[1]);

    store.impose(xmulCeqZ);

    store.print();
    int noOfSolutions = noOfAllSolutions(store, x);

    assertThat(noOfSolutions).isEqualTo(2);
  }

  @Test
  void testAlldiff() {

    Store store = new Store();

    int xLength = 2;
    int xSize = xLength * 2 + 2;
    IntVar[] x = getIntVars(store, "x", xLength, xSize);

    Alldiff alldiff = new Alldiff(x);

    store.impose(alldiff);

    store.print();
    int noOfSolutions = noOfAllSolutions(store, x);

    assertThat(noOfSolutions).isEqualTo(30);
  }

  @Test
  void testXgtCwithHelperSimpleConstraintsToAvoidNoConstraintBeingActiveSmall() {

    Store store = new Store();

    int xLength = 2;
    int xSize = xLength * 2 + 2;
    IntVar[] x = getIntVars(store, "x", xLength, xSize);

    Arrays.stream(x).forEach(i -> store.impose(new XgtC(i, i.min() + xSize / 2)));
    store.impose(new Alldiff(x));

    store.print();

    int noOfSolutions = noOfAllSolutions(store, x);

    assertThat(noOfSolutions).isEqualTo(2);
  }

  @Test
  void testXgtCwithHelperSimpleConstraintsToAvoidNoConstraintBeingActive() {

    Store store = new Store();

    int xLength = 4;
    int xSize = xLength * 2 + 2;
    IntVar[] x = getIntVars(store, "x", xLength, xSize);

    Arrays.stream(x).forEach(i -> store.impose(new XgtC(i, i.min() + xSize / 2)));
    store.impose(new Alldiff(x));

    store.print();

    int noOfSolutions = noOfAllSolutions(store, x);

    assertThat(noOfSolutions).isEqualTo(24);
  }

  @Test
  void testArgMin() {

    Store store = new Store();

    int xLength = 4;
    int xSize = 6;

    IntVar[] x = getShiftedIntVars(store, "x", xLength, xSize + 1);
    IntVar index = new IntVar(store, "index", 0, xLength);
    ArgMin argMin = new ArgMin(x, index, -1);

    store.impose(argMin);

    int noOfSolutions = noOfAllSolutions(store, x, new IntVar[] {index});

    assertThat(noOfSolutions).isEqualTo(2401);
  }

  @Test
  // BUG, problem with using BoundDomain, SmallDenseDomain and asserts, need to investigate.
  // The same problem and fixed applied for ArgMin. Keep this for investigation of the buggy
  // scenario.
  void testArgMax() {

    Store store = new Store();

    int xLength = 4;
    int xSize = 6;

    IntVar[] x = getShiftedIntVars(store, "x", xLength, xSize + 1);
    IntVar index = new IntVar(store, "index", 0, xLength);
    ArgMax argMax = new ArgMax(x, index, -1);

    store.impose(argMax);

    int noOfSolutions = noOfAllSolutions(store, x, new IntVar[] {index});

    assertThat(noOfSolutions).isEqualTo(2401);
  }

  @Test
  void testSum() {

    Store store = new Store();

    int xLength = 4;
    int xSize = 2;

    IntVar[] x = getShiftedIntVars(store, "x", xLength, xSize + 1);
    IntVar sum = new IntVar(store, "sum", 0, xLength * xSize);

    SumInt sumConstraint = new SumInt(x, "==", sum);

    store.impose(sumConstraint);

    int noOfSolutions = noOfAllSolutions(store, x);

    assertThat(noOfSolutions).isEqualTo(15);
  }

  @Test
  void testLinear() {

    Store store = new Store();

    int xLength = 4;
    int xSize = 2;

    IntVar[] x = getShiftedIntVars(store, "x", xLength, xSize + 1);

    LinearInt linear = new LinearInt(x, new int[] {2, 1, 3, 1}, ">=", 5);

    store.impose(linear);

    int noOfSolutions = noOfAllSolutions(store, x);

    assertThat(noOfSolutions).isEqualTo(81);
  }

  @Test
  void testIfThenElse() {

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

    assertThat(noOfSolutions).isEqualTo(24);
  }

  @Test
  void testElementIntegerFast() {

    Store store = new Store();

    int size = 3;
    int length = 1000;

    IntVar x = new IntVar(store, "x", 0, length);
    IntVar z = new IntVar(store, "z", 0, length);

    int[] values = IntStream.iterate(1, i -> i + 1).map(i -> i / size).limit(length).toArray();

    ElementIntegerFast ifThenElse = new ElementIntegerFast(x, values, z);

    store.impose(ifThenElse);

    int noOfSolutions = noOfAllSolutions(store, new IntVar[] {x, z});

    assertThat(noOfSolutions).isEqualTo(length);
  }

  @Test
  void testEqBool() {

    Store store = new Store();

    int xLength = 4;

    IntVar[] x = getIntVars(store, "x", xLength, 2);
    IntVar n = new IntVar(store, "sum", 0, 1);
    EqBool eqBool = new EqBool(x, n);

    store.impose(eqBool);

    int noOfSolutions = noOfAllSolutions(store, x, new IntVar[] {n});

    assertThat(noOfSolutions).isEqualTo(16);
  }

  @Test
  void testLex() {

    Store store = new Store();

    int xLength = 4;
    int xSize = 2;

    IntVar[] x1 = getShiftedIntVars(store, "a", xLength, xSize + 1);
    IntVar[] x2 = getIntVars(store, "b", xLength + xSize, xLength);

    Lex lex = new Lex(new IntVar[][] {x1, x2}, true);

    store.imposeDecomposition(lex);

    int noOfSolutions = noOfAllSolutions(store, x1, x2);

    assertThat(noOfSolutions).isEqualTo(188640);
  }

  @Test
  void testGCC() {

    Store store = new Store();

    int xLength = 4;
    int xSize = 2;

    IntVar[] x = getShiftedIntVars(store, "x", xLength, xSize + 1);

    IntVar[] counters = getIntVars(store, "counters", xLength + xSize, xLength);

    GCC gcc = new GCC(x, counters);

    store.impose(gcc);

    int noOfSolutions = noOfAllSolutions(store, x, counters);

    assertThat(noOfSolutions).isEqualTo(81);
  }

  @Test
  void testAmongVar() {

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

    assertThat(noOfSolutions).isEqualTo(177147);
  }

  @Test
  void testDiff() {

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

    assertThat(noOfSolutions).isEqualTo(741642);
  }

  @Test
  void testDisjoint() {

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

    assertThat(noOfSolutions).isEqualTo(699189);
  }

  @Test
  void testDiff2() {

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

    assertThat(noOfSolutions).isEqualTo(791208);
  }

  @Test
  void testDisjointConditional() {

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

    Diff disjointConditional =
        new DisjointConditional(
            origin1,
            origin2,
            length1,
            length2,
            conditionalPairs,
            Arrays.asList(exceptionCondition));

    store.impose(disjointConditional);

    int noOfSolutions =
        noOfAllSolutions(store, origin1, origin2, length1, length2, exceptionCondition);

    assertThat(noOfSolutions).isEqualTo(141141);
  }

  @Test
  void testValues() {

    Store store = new Store();

    int xLength = 4;
    int xSize = 7;

    IntVar[] x = getIntVars(store, "x", xLength, xSize);
    IntVar n = new IntVar(store, "sum", 0, 1);
    Values values = new Values(x, n);

    store.impose(values);

    int noOfSolutions = noOfAllSolutions(store, x, new IntVar[] {n});

    assertThat(noOfSolutions).isEqualTo(xSize);
  }

  @Test
  void testValues2() {

    Store store = new Store();

    int xLength = 4;
    int xSize = 4;

    IntVar[] x = getIntVars(store, "x", xLength, xSize);
    IntVar n = new IntVar(store, "sum", 1, 2);
    Values values = new Values(x, n);

    store.impose(values);

    int noOfSolutions = noOfAllSolutions(store, x, new IntVar[] {n});

    assertThat(noOfSolutions).isEqualTo(88);
  }

  // Regression test for https://github.com/radsz/jacop/issues/78
  @Test
  void testNoGoodViolatedOverSingletons() {

    Store store = new Store();
    IntVar[] x = {new IntVar(store, "x1", 1, 1), new IntVar(store, "x2", 2, 2)};

    store.impose(new NoGood(x, new int[] {1, 2}));

    assertThat(store.consistency()).isFalse();
  }

  // Regression test for https://github.com/radsz/jacop/issues/78
  @Test
  void testNoGoodSatisfiedOverSingletons() {

    Store store = new Store();
    IntVar[] x = {new IntVar(store, "x1", 1, 1), new IntVar(store, "x2", 3, 3)};

    store.impose(new NoGood(x, new int[] {1, 2}));

    assertThat(store.consistency()).isTrue();
  }

  // Regression test for https://github.com/radsz/jacop/issues/78
  @Test
  void testNoGoodWithSingletonsAndOneFreeVariable() {

    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x1", 1, 1), new IntVar(store, "x2", 1, 3), new IntVar(store, "x3", 2, 2)
    };

    store.impose(new NoGood(x, new int[] {1, 2, 2}));

    assertThat(store.consistency()).isTrue();
    assertThat(x[1].dom().contains(2)).isFalse();
    assertThat(noOfAllSolutions(store, x)).isEqualTo(2);
  }

  // Regression test for https://github.com/radsz/jacop/issues/64
  @Test
  void testGeostFailsWhenGroundedStartPlusDurationDiffersFromEnd() {

    // object 1 is grounded in time with start 0, duration 1 and end 3, which is inconsistent.
    Store store = new Store();
    IntVar[] vars = geostTimeModel(store, new IntVar(store, "duration1", 1, 1));

    assertThat(noOfAllSolutions(store, vars)).isZero();
  }

  // Regression test for https://github.com/radsz/jacop/issues/64
  @Test
  void testGeostEnforcesPositiveDuration() {

    // object 1 must have start 0 + duration 3 = end 3; duration 0 is not allowed.
    Store store = new Store();
    IntVar[] vars = geostTimeModel(store, new IntVar(store, "duration1", 0, 3));

    // object 0 (x in 0..2, start 1, duration 1..2) overlaps object 1 (x 0, time 0..3)
    // in time, so it must not overlap it in space: x0 in 2..2, duration0 in 1..2.
    assertThat(noOfAllSolutions(store, vars)).isEqualTo(2);
  }

  /**
   * Two objects of length 2 in one dimension plus time. Object 0: x in 0..2, start 1, duration in
   * 1..2, end in 0..4. Object 1: x 0, start 0, the given duration, end 3.
   */
  private IntVar[] geostTimeModel(Store store, IntVar duration1) {

    List<Shape> shapes =
        List.of(
            new Shape(0, new int[] {0}, new int[] {2}), new Shape(1, new int[] {0}, new int[] {2}));

    IntVar x0 = new IntVar(store, "x0", 0, 2);
    IntVar start0 = new IntVar(store, "start0", 1, 1);
    IntVar duration0 = new IntVar(store, "duration0", 1, 2);
    IntVar end0 = new IntVar(store, "end0", 0, 4);
    IntVar x1 = new IntVar(store, "x1", 0, 0);
    IntVar start1 = new IntVar(store, "start1", 0, 0);
    IntVar end1 = new IntVar(store, "end1", 3, 3);

    List<GeostObject> objects =
        List.of(
            new GeostObject(
                0, new IntVar[] {x0}, new IntVar(store, "shape0", 0, 0), start0, duration0, end0),
            new GeostObject(
                1, new IntVar[] {x1}, new IntVar(store, "shape1", 1, 1), start1, duration1, end1));
    List<ExternalConstraint> constraints = List.of(new NonOverlapping(objects, new int[] {0, 1}));

    store.impose(new Geost(objects, constraints, shapes));

    return new IntVar[] {x0, start0, duration0, end0, x1, start1, duration1, end1};
  }

  // Regression test for https://github.com/radsz/jacop/issues/46
  @Test
  void testAmongVarWithGroundedX() {

    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 0, 2),
      new IntVar(store, "x1", 0, 0),
      new IntVar(store, "x2", 0, 2),
      new IntVar(store, "x3", 2, 2)
    };
    IntVar[] y = {new IntVar(store, "y0", 0, 0), new IntVar(store, "y1", 1, 2)};
    IntVar n = new IntVar(store, "n", 1, 2);

    store.impose(new AmongVar(x, y, n));

    assertThat(noOfAllSolutions(store, x, y, new IntVar[] {n})).isEqualTo(6);
  }

  // Compares AmongVar with a brute-force count on random small instances; it found that
  // grounded Y could be skipped after being reordered (https://github.com/radsz/jacop/issues/46).
  @Test
  void testAmongVarAgainstBruteForce() {

    Random random = new Random(46);
    for (int trial = 0; trial < 300; trial++) {
      int[][] xDomains = randomDomains(random, 1 + random.nextInt(4));
      int[][] yDomains = randomDomains(random, 1 + random.nextInt(4));
      int nMin = random.nextInt(2);
      int nMax = nMin + random.nextInt(xDomains.length + 1);

      Store store = new Store();
      IntVar[] x = new IntVar[xDomains.length];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, xDomains[i][0], xDomains[i][1]);
      }
      IntVar[] y = new IntVar[yDomains.length];
      for (int i = 0; i < y.length; i++) {
        y[i] = new IntVar(store, "y" + i, yDomains[i][0], yDomains[i][1]);
      }
      IntVar n = new IntVar(store, "n", nMin, nMax);

      store.impose(new AmongVar(x, y, n));

      assertThat(noOfAllSolutions(store, x, y, new IntVar[] {n}))
          .as(
              "AmongVar x=%s y=%s n=%d..%d",
              Arrays.deepToString(xDomains), Arrays.deepToString(yDomains), nMin, nMax)
          .isEqualTo(amongVarBruteForce(xDomains, yDomains, nMin, nMax));
    }
  }

  private static int[][] randomDomains(Random random, int size) {
    int[][] domains = new int[size][];
    for (int i = 0; i < size; i++) {
      int min = random.nextInt(3);
      domains[i] = new int[] {min, random.nextBoolean() ? min : min + random.nextInt(4)};
    }
    return domains;
  }

  private static int amongVarBruteForce(int[][] xDomains, int[][] yDomains, int nMin, int nMax) {
    int[][] domains =
        Stream.concat(Arrays.stream(xDomains), Arrays.stream(yDomains)).toArray(int[][]::new);
    return amongVarBruteForce(domains, xDomains.length, new int[domains.length], 0, nMin, nMax);
  }

  private static int amongVarBruteForce(
      int[][] domains, int xLength, int[] values, int index, int nMin, int nMax) {
    if (index == domains.length) {
      Set<Integer> yValues = new HashSet<>();
      for (int i = xLength; i < values.length; i++) {
        yValues.add(values[i]);
      }
      long count = IntStream.range(0, xLength).filter(i -> yValues.contains(values[i])).count();
      return count >= nMin && count <= nMax ? 1 : 0;
    }
    int solutions = 0;
    for (int v = domains[index][0]; v <= domains[index][1]; v++) {
      values[index] = v;
      solutions += amongVarBruteForce(domains, xLength, values, index + 1, nMin, nMax);
    }
    return solutions;
  }

  // Regression test for https://github.com/radsz/jacop/issues/71
  @Test
  void testNetworkFlowCostMissingSolutions() {

    Store store = new Store();
    IntVar a = new IntVar(store, "A", 0, 0);
    a.addDom(2, 2);
    IntVar b = new IntVar(store, "B", 0, 0);
    b.addDom(4, 4);
    IntVar c = new IntVar(store, "C", 0, 4);
    IntVar h = new IntVar(store, "H", 0, 0);
    h.addDom(4, 4);
    IntVar cost = new IntVar(store, "J", 0, 60);

    int[][] arcs = {
      {0, 1}, {0, 2}, {0, 3}, {1, 0}, {1, 2}, {1, 3}, {2, 0}, {2, 1}, {2, 3}, {3, 0}, {3, 1}, {3, 2}
    };
    int[] weights = {1, 2, 2, 2, 1, 2, 2, 1, 2, 0, 0, 1};
    IntVar[] flows = {
      new IntVar(store, 2, 2),
      new IntVar(store, 4, 4),
      a,
      new IntVar(store, 0, 0),
      new IntVar(store, 4, 4),
      new IntVar(store, 4, 4),
      c,
      new IntVar(store, 3, 3),
      h,
      b,
      new IntVar(store, 2, 2),
      new IntVar(store, 4, 4)
    };
    int[] balance = {4, 1, -5, 0};

    NetworkBuilder net = new NetworkBuilder();
    Node[] nodes = new Node[balance.length];
    for (int i = 0; i < balance.length; i++) {
      nodes[i] = net.addNode("n" + i, balance[i]);
    }
    for (int i = 0; i < arcs.length; i++) {
      // weights are variables as in the FlatZinc interface
      net.addArc(
          nodes[arcs[i][0]],
          nodes[arcs[i][1]],
          new IntVar(store, weights[i], weights[i]),
          flows[i]);
    }
    net.setCostVariable(cost);
    store.impose(net.build());

    // (J, A, B, C, H) = (41, 2, 0, 4, 0) and (41, 2, 4, 0, 4); J is labelled first as in the issue
    assertThat(noOfAllSolutions(store, new IntVar[] {cost, a, b, c, h})).isEqualTo(2);
  }

  // Regression test for https://github.com/radsz/jacop/issues/71: when the lower bound of the cost
  // variable is above the optimal flow cost, values of valid solutions were pruned.
  @Test
  void testSoftAlldifferentWithCostAboveOptimum() {

    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 0, 0), new IntVar(store, "x1", 0, 1), new IntVar(store, "x2", 0, 0)
    };
    IntVar cost = new IntVar(store, "cost", 2, 2);

    store.imposeDecomposition(new SoftAlldifferent(x, cost, ViolationMeasure.VARIABLE_BASED));

    assertThat(noOfAllSolutions(store, x, new IntVar[] {cost})).isEqualTo(1);
  }

  // Compares network flow with a brute-force count on random small networks.
  @Test
  void testNetworkFlowAgainstBruteForce() {

    Random random = new Random(71);
    for (int trial = 0; trial < 300; trial++) {
      int nodeCount = 2 + random.nextInt(3);
      int arcCount = 1 + random.nextInt(5);
      int[][] arcs = new int[arcCount][2];
      int[] weights = new int[arcCount];
      int[][] flowDomains = new int[arcCount][2];
      int[] balance = new int[nodeCount];
      for (int i = 0; i < arcCount; i++) {
        arcs[i][0] = random.nextInt(nodeCount);
        arcs[i][1] = (arcs[i][0] + 1 + random.nextInt(nodeCount - 1)) % nodeCount;
        weights[i] = random.nextInt(4);
        int min = random.nextInt(2);
        flowDomains[i] = new int[] {min, min + random.nextInt(3)};
        // balances come from a random flow so that most networks are feasible
        int flow = min + random.nextInt(flowDomains[i][1] - min + 1);
        balance[arcs[i][0]] += flow;
        balance[arcs[i][1]] -= flow;
      }
      int costMin = random.nextInt(6);
      int costMax = costMin + random.nextInt(10);

      Store store = new Store();
      NetworkBuilder net = new NetworkBuilder();
      Node[] nodes = new Node[nodeCount];
      for (int i = 0; i < nodeCount; i++) {
        nodes[i] = net.addNode("n" + i, balance[i]);
      }
      IntVar[] flows = new IntVar[arcCount];
      for (int i = 0; i < arcCount; i++) {
        flows[i] = new IntVar(store, "f" + i, flowDomains[i][0], flowDomains[i][1]);
        net.addArc(nodes[arcs[i][0]], nodes[arcs[i][1]], weights[i], flows[i]);
      }
      IntVar cost = new IntVar(store, "cost", costMin, costMax);
      net.setCostVariable(cost);
      store.impose(net.build());

      assertThat(noOfAllSolutions(store, flows, new IntVar[] {cost}))
          .as(
              "network arcs=%s weights=%s flows=%s balance=%s cost=%d..%d",
              Arrays.deepToString(arcs),
              Arrays.toString(weights),
              Arrays.deepToString(flowDomains),
              Arrays.toString(balance),
              costMin,
              costMax)
          .isEqualTo(
              networkFlowBruteForce(
                  arcs, weights, flowDomains, balance, costMin, costMax, new int[arcCount], 0));
    }
  }

  private static int networkFlowBruteForce(
      int[][] arcs,
      int[] weights,
      int[][] flowDomains,
      int[] balance,
      int costMin,
      int costMax,
      int[] flows,
      int index) {
    if (index == flows.length) {
      int[] actual = new int[balance.length];
      int cost = 0;
      for (int i = 0; i < flows.length; i++) {
        actual[arcs[i][0]] += flows[i];
        actual[arcs[i][1]] -= flows[i];
        cost += weights[i] * flows[i];
      }
      return Arrays.equals(actual, balance) && cost >= costMin && cost <= costMax ? 1 : 0;
    }
    int solutions = 0;
    for (int f = flowDomains[index][0]; f <= flowDomains[index][1]; f++) {
      flows[index] = f;
      solutions +=
          networkFlowBruteForce(
              arcs, weights, flowDomains, balance, costMin, costMax, flows, index + 1);
    }
    return solutions;
  }

  static class TestWatcherExtension implements BeforeEachCallback {
    @Override
    public void beforeEach(ExtensionContext context) {
      log.info("Starting test: " + context.getDisplayName());
    }
  }
}
