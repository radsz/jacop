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

import java.io.StringReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Among;
import org.jacop.constraints.AmongVar;
import org.jacop.constraints.ArgMax;
import org.jacop.constraints.ArgMin;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.Diff;
import org.jacop.constraints.Diff2;
import org.jacop.constraints.Disjoint;
import org.jacop.constraints.DisjointConditional;
import org.jacop.constraints.Distance;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.ElementVariable;
import org.jacop.constraints.EqBool;
import org.jacop.constraints.ExtensionalConflictVa;
import org.jacop.constraints.GCC;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.IfThenBool;
import org.jacop.constraints.IfThenElse;
import org.jacop.constraints.In;
import org.jacop.constraints.Lex;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.MaxSimple;
import org.jacop.constraints.Min;
import org.jacop.constraints.MinSimple;
import org.jacop.constraints.NoGood;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.SoftAlldifferent;
import org.jacop.constraints.SoftGCC;
import org.jacop.constraints.Stretch;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.Values;
import org.jacop.constraints.ViolationMeasure;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XexpYeqZ;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XgtY;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XmodYeqZ;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.Xor;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.constraints.geost.ExternalConstraint;
import org.jacop.constraints.geost.Geost;
import org.jacop.constraints.geost.GeostObject;
import org.jacop.constraints.geost.NonOverlapping;
import org.jacop.constraints.geost.Shape;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.constraints.regular.Regular;
import org.jacop.constraints.table.SimpleTable;
import org.jacop.constraints.table.Table;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.SmallDenseDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;
import org.jacop.util.fsm.RegularExpressionParser;
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
  void absXeqYBoundConsistencyReachesFixpoint() {
    // When pruning x left only non-negative values, y kept the lower bound 0, and the constraint
    // was not run again. In all_interval this left |1| = {0..1} and gave non-solutions.
    Store store = new Store();
    IntVar x = new IntVar(store, "x");
    x.addDom(-3, -3);
    x.addDom(1, 2);
    x.addDom(4, 5);
    IntVar y = new IntVar(store, "y");
    y.addDom(0, 0);
    y.addDom(2, 2);
    y.addDom(6, 7);

    store.impose(new AbsXeqY(x, y));

    assertThat(store.consistency()).isTrue();
    assertThat(x.singleton(2)).as("x = %s", x.dom()).isTrue();
    assertThat(y.singleton(2)).as("y = %s", y.dom()).isTrue();
  }

  @Test
  void distanceIsNeverNegative() {
    // |x - y| = z: the value -2 of z has no support, but the propagator only imposed z >= 0 when
    // a flag that was never initialised to true was set.
    Store store = new Store();
    IntVar x = new IntVar(store, "x", -4, 2);
    IntVar y = new IntVar(store, "y", -4, 3);
    IntVar z = new IntVar(store, "z", -2, 7);
    store.impose(new Distance(x, y, z));

    assertThat(store.consistency()).isTrue();
    assertThat(z.min()).isEqualTo(0);
  }

  @Test
  void absXeqYPrunesOnlyUnsupportedValuesAndReachesFixpoint() {
    Random random = new Random(7);
    for (int run = 0; run < 2000; run++) {
      boolean domainConsistency = run % 2 == 0;
      Store store = new Store();
      IntVar x = randomSubsetVar(store, "x", -5, 5, random);
      IntVar y = randomSubsetVar(store, "y", -2, 6, random);
      int[] xValues = valuesOf(x);
      int[] yValues = valuesOf(y);
      AbsXeqY abs = new AbsXeqY(x, y, domainConsistency);
      store.impose(abs);

      boolean supported = false;
      for (int v : xValues) {
        supported |= y.domain.contains(Math.abs(v));
      }
      boolean consistent = store.consistency();
      String instance =
          "run " + run + " x " + Arrays.toString(xValues) + " y " + Arrays.toString(yValues);
      if (!supported) {
        // bounds propagation may miss a failure that the search finds later
        continue;
      }
      assertThat(consistent).as(instance).isTrue();
      for (int v : xValues) {
        if (Arrays.stream(yValues).anyMatch(w -> w == Math.abs(v))) {
          assertThat(x.domain.contains(v)).as(instance).isTrue();
          assertThat(y.domain.contains(Math.abs(v))).as(instance).isTrue();
        }
      }
      String afterPropagation = x.dom() + " " + y.dom();
      store.setLevel(store.level + 1);
      abs.consistency(store);
      assertThat(x.dom() + " " + y.dom()).as(instance).isEqualTo(afterPropagation);
    }
  }

  @Test
  void linearIntDomWakesUpOnHoleRemoval() {
    // LinearIntDom is domain consistent but inherited the BOUND pruning event of LinearInt, so
    // removing an inner value of a variable did not re-run it.
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 1);
    IntVar y = new IntVar(store, "y", 2, 4);
    IntVar z = new IntVar(store, "z", 5, 13);
    // x + 4 * y - z = 4, so z = 4 * y - 3
    store.impose(new LinearIntDom(new IntVar[] {x, y, z}, new int[] {1, 4, -1}, "==", 4));
    assertThat(store.consistency()).isTrue();
    assertThat(z.dom().toString()).isEqualTo("{5, 9, 13}");

    store.setLevel(store.level + 1);
    y.domain.inComplement(store.level, y, 3);
    assertThat(store.consistency()).isTrue();

    assertThat(z.dom().toString()).isEqualTo("{5, 13}");
  }

  @Test
  void xmodYeqZWakesUpOnHoleRemoval() {
    // With y ground XmodYeqZ filters x with the holes of z, but it inherited the BOUND pruning
    // event of AbstractXopYeqZ, so removing an inner value of z did not re-run it.
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 5);
    IntVar y = new IntVar(store, "y", 5, 5);
    IntVar z = new IntVar(store, "z", 0, 4);
    store.impose(new XmodYeqZ(x, y, z));
    assertThat(store.consistency()).isTrue();
    assertThat(x.dom().toString()).isEqualTo("{1..5}");

    store.setLevel(store.level + 1);
    z.domain.inComplement(store.level, z, 1);
    assertThat(store.consistency()).isTrue();

    // 1 mod 5 = 1 is no longer in z
    assertThat(x.dom().toString()).isEqualTo("{2..5}");
  }

  @Test
  void xexpYeqZWakesUpOnHoleRemoval() {
    // XexpYeqZ keeps only supported values but inherited the BOUND pruning event of
    // AbstractXopYeqZ, so removing an inner value of z did not re-run it.
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 2, 4);
    IntVar y = new IntVar(store, "y", 2, 2);
    IntVar z = new IntVar(store, "z", 4, 16);
    store.impose(new XexpYeqZ(x, y, z));
    assertThat(store.consistency()).isTrue();
    assertThat(z.dom().toString()).isEqualTo("{4, 9, 16}");

    store.setLevel(store.level + 1);
    z.domain.inComplement(store.level, z, 9);
    assertThat(store.consistency()).isTrue();

    assertThat(x.dom().toString()).isEqualTo("{2, 4}");
  }

  @Test
  void circuitWakesUpOnHoleRemoval() {
    // Circuit inherited the BOUND pruning event of Alldiff, so removing an inner value did not
    // re-run it. Here no variable can take 3 any more, so node 3 has no predecessor.
    Store store = new Store();
    IntVar[] x = new IntVar[4];
    x[0] = new IntVar(store, "x0", 2, 4);
    x[1] = new IntVar(store, "x1");
    x[1].addDom(1, 1);
    x[1].addDom(4, 4);
    x[2] = new IntVar(store, "x2");
    x[2].addDom(1, 2);
    x[2].addDom(4, 4);
    x[3] = new IntVar(store, "x3", 1, 2);
    store.impose(new Circuit(x));
    assertThat(store.consistency()).isTrue();

    store.setLevel(store.level + 1);
    x[0].domain.inComplement(store.level, x[0], 3);

    assertThat(store.consistency()).isFalse();
  }

  @Test
  void minSimpleReachesFixpoint() {
    // Intersecting x2 with min.dom() lowered x2.max, but min.max was not recomputed in the same
    // call and the constraint is not re-run for its own changes, leaving min = 0 unsupported.
    Store store = new Store();
    IntVar x1 = new IntVar(store, "x1", 1, 1);
    IntVar x2 = new IntVar(store, "x2");
    x2.addDom(-4, -2);
    x2.addDom(1, 1);
    x2.addDom(5, 6);
    IntVar min = new IntVar(store, "min");
    min.addDom(-4, -2);
    min.addDom(0, 0);
    min.addDom(5, 5);

    store.impose(new MinSimple(x1, x2, min));

    assertThat(store.consistency()).isTrue();
    assertThat(min.dom().toString()).isEqualTo("{-4..-2}");
    assertThat(x2.dom().toString()).isEqualTo("{-4..-2}");
  }

  @Test
  void minAndMaxSimpleKeepSupportsAndReachFixpoint() {
    Random random = new Random(11);
    for (int run = 0; run < 2000; run++) {
      boolean minimum = run % 2 == 0;
      Store store = new Store();
      IntVar x1 = randomSubsetVar(store, "x1", -4, 6, random);
      IntVar x2 = randomSubsetVar(store, "x2", -4, 6, random);
      IntVar r = randomSubsetVar(store, "r", -4, 6, random);
      int[] x1Values = valuesOf(x1);
      int[] x2Values = valuesOf(x2);
      int[] rValues = valuesOf(r);
      Constraint c = minimum ? new MinSimple(x1, x2, r) : new MaxSimple(x1, x2, r);
      store.impose(c);

      Set<Integer> x1Support = new HashSet<>();
      Set<Integer> x2Support = new HashSet<>();
      Set<Integer> rSupport = new HashSet<>();
      for (int a : x1Values) {
        for (int b : x2Values) {
          int v = minimum ? Math.min(a, b) : Math.max(a, b);
          if (Arrays.stream(rValues).anyMatch(w -> w == v)) {
            x1Support.add(a);
            x2Support.add(b);
            rSupport.add(v);
          }
        }
      }
      String instance =
          (minimum ? "min" : "max")
              + " run "
              + run
              + " x1 "
              + Arrays.toString(x1Values)
              + " x2 "
              + Arrays.toString(x2Values)
              + " r "
              + Arrays.toString(rValues);
      boolean consistent = store.consistency();
      if (rSupport.isEmpty()) {
        continue;
      }
      assertThat(consistent).as(instance).isTrue();
      x1Support.forEach(v -> assertThat(x1.domain.contains(v)).as(instance).isTrue());
      x2Support.forEach(v -> assertThat(x2.domain.contains(v)).as(instance).isTrue());
      rSupport.forEach(v -> assertThat(r.domain.contains(v)).as(instance).isTrue());

      String afterPropagation = x1.dom() + " " + x2.dom() + " " + r.dom();
      store.setLevel(store.level + 1);
      c.consistency(store);
      assertThat(x1.dom() + " " + x2.dom() + " " + r.dom())
          .as(instance)
          .isEqualTo(afterPropagation);
    }
  }

  @Test
  void testRegularPrunesAllUnsupportedValues() {

    // Words of length 2 accepted by the automaton; with x1 = 1 only x0 = 3 has a support. The
    // pruning loop of Regular removes values from a domain while enumerating it, and the
    // enumeration stopped after the first removed value, so x0 = 4 stayed.
    FsmState[] s = new FsmState[4];
    Fsm fsm = new Fsm();
    for (int i = 0; i < s.length; i++) {
      s[i] = new FsmState();
      fsm.allStates.add(s[i]);
    }
    fsm.initState = s[0];
    fsm.finalStates.add(s[2]);
    IntervalDomain oneOrFour = new IntervalDomain(1, 1);
    oneOrFour.unionAdapt(4, 4);
    s[0].addTransition(new FsmTransition(oneOrFour, s[0]));
    s[0].addTransition(new FsmTransition(new IntervalDomain(3, 3), s[2]));
    s[0].addTransition(new FsmTransition(new IntervalDomain(2, 2), s[3]));
    s[2].addTransition(new FsmTransition(new IntervalDomain(1, 1), s[2]));
    s[3].addTransition(new FsmTransition(new IntervalDomain(3, 3), s[2]));

    Store store = new Store();
    IntVar x0 = new IntVar(store, "x0", 1, 4);
    IntVar x1 = new IntVar(store, "x1", 1, 4);
    store.impose(new Regular(fsm, new IntVar[] {x0, x1}));
    assertThat(store.consistency()).isTrue();

    store.setLevel(1);
    x0.domain.inComplement(1, x0, 2);
    x1.domain.inComplement(1, x1, 3);

    assertThat(store.consistency()).isTrue();
    assertThat(x1.value()).isEqualTo(1);
    assertThat(x0.singleton()).isTrue();
    assertThat(x0.value()).isEqualTo(3);
  }

  // On graphs large enough for Regular to remove nodes a level at a time and to compact its
  // adjacency arrays, its domains must equal those of its decomposition into a chain of ternary
  // tables, which is domain consistent too because the chain is Berge-acyclic. Both stores take the
  // same random dives and backtrack out of them again and again.
  @Test
  void testRegularMatchesDecompositionOnLargeGraphs() {

    Random random = new Random(11);
    for (int trial = 0; trial < 6; trial++) {
      int n = 40 + random.nextInt(30);
      int states = 120 + random.nextInt(60);
      Fsm fsm = new Fsm();
      FsmState[] s = new FsmState[states];
      for (int q = 0; q < states; q++) {
        s[q] = new FsmState();
        fsm.allStates.add(s[q]);
      }
      fsm.initState = s[0];
      for (int q = 0; q < states; q++) {
        if (random.nextInt(4) > 0) {
          fsm.finalStates.add(s[q]);
        }
        for (int c = 0; c < 4; c++) {
          Set<Integer> successors = new HashSet<>();
          for (int k = random.nextInt(3); k >= 0; k--) {
            successors.add(random.nextInt(states));
          }
          for (int next : successors) {
            s[q].addTransition(new FsmTransition(new IntervalDomain(c, c), s[next]));
          }
        }
      }

      Store regularStore = new Store();
      Store tableStore = new Store();
      IntVar[] x = new IntVar[n];
      IntVar[] y = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(regularStore, "x" + i, 0, 3);
        y[i] = new IntVar(tableStore, "x" + i, 0, 3);
      }
      regularStore.impose(new Regular(fsm, x));
      new Regular(fsm, y).imposeDecomposition(tableStore);
      String instance = "trial " + trial;
      assertThat(regularStore.consistency()).as(instance).isEqualTo(tableStore.consistency());
      assertThat(Arrays.toString(x)).as(instance).isEqualTo(Arrays.toString(y));

      // Level 1 fixes most of the variables, so most edges are removed below it. Every
      // value left is in an accepted word, so any choice is consistent.
      regularStore.setLevel(1);
      tableStore.setLevel(1);
      for (int i = 0; i < 3 * n / 4; i++) {
        int[] values = valuesOf(x[i]);
        int value = values[random.nextInt(values.length)];
        x[i].domain.in(1, x[i], value, value);
        y[i].domain.in(1, y[i], value, value);
        assertThat(regularStore.consistency()).as(instance).isTrue();
        assertThat(tableStore.consistency()).as(instance).isTrue();
      }
      assertThat(Arrays.toString(x)).as(instance).isEqualTo(Arrays.toString(y));

      for (int dive = 0; dive < 200; dive++) {
        int base = regularStore.level;
        String atBase = Arrays.toString(x);
        boolean consistent = true;
        while (consistent) {
          List<Integer> free =
              IntStream.range(0, n).filter(i -> !x[i].singleton()).boxed().toList();
          if (free.isEmpty()) {
            break;
          }
          int i = free.get(random.nextInt(free.size()));
          int[] values = valuesOf(x[i]);
          int value = values[random.nextInt(values.length)];
          regularStore.setLevel(regularStore.level + 1);
          tableStore.setLevel(tableStore.level + 1);
          if (random.nextInt(5) == 0) {
            x[i].domain.in(regularStore.level, x[i], value, value);
            y[i].domain.in(tableStore.level, y[i], value, value);
          } else {
            x[i].domain.inComplement(regularStore.level, x[i], value);
            y[i].domain.inComplement(tableStore.level, y[i], value);
          }
          consistent = regularStore.consistency();
          assertThat(consistent).as(instance).isEqualTo(tableStore.consistency());
          if (consistent) {
            assertThat(Arrays.toString(x)).as(instance).isEqualTo(Arrays.toString(y));
          }
        }
        // Backtrack to a random level below level 2, so that many dives share the subtree of
        // level 2, and sometimes to level 1, which removes that subtree.
        int deepest = regularStore.level;
        int target =
            deepest < 2 || random.nextInt(40) == 0
                ? Math.min(1, deepest)
                : 2 + random.nextInt(deepest - 1);
        while (regularStore.level > target) {
          regularStore.removeLevel(regularStore.level);
          regularStore.setLevel(regularStore.level - 1);
          tableStore.removeLevel(tableStore.level);
          tableStore.setLevel(tableStore.level - 1);
        }
        assertThat(Arrays.toString(x)).as(instance).isEqualTo(Arrays.toString(y));
        if (target == base) {
          assertThat(Arrays.toString(x)).as(instance).isEqualTo(atBase);
        }
      }
    }
  }

  // Regular on random (possibly non-deterministic) automata must keep every domain equal to the
  // values that appear in some accepted word, after each pruning step of a dive and after
  // backtracking out of it, and must fail exactly when no accepted word remains.
  @Test
  void testRegularIsDomainConsistentAcrossBacktracking() {

    Random random = new Random(7);
    for (int trial = 0; trial < 400; trial++) {
      int n = 1 + random.nextInt(6);
      int states = 1 + random.nextInt(5);
      // transitions[q][c] is the set of successors of state q on value c (bit mask).
      int[][] transitions = new int[states][4];
      FsmState[] s = new FsmState[states];
      Fsm fsm = new Fsm();
      for (int q = 0; q < states; q++) {
        s[q] = new FsmState();
        fsm.allStates.add(s[q]);
      }
      fsm.initState = s[0];
      boolean[] accepting = new boolean[states];
      for (int q = 0; q < states; q++) {
        accepting[q] = random.nextInt(3) > 0;
        if (accepting[q]) {
          fsm.finalStates.add(s[q]);
        }
        for (int t = random.nextInt(2 * states + 3); t > 0; t--) {
          int c = random.nextInt(4);
          int next = random.nextInt(states);
          if ((transitions[q][c] & (1 << next)) == 0) {
            transitions[q][c] |= 1 << next;
            s[q].addTransition(new FsmTransition(new IntervalDomain(c, c), s[next]));
          }
        }
      }
      Predicate<int[]> accepts =
          word -> {
            int current = 1;
            for (int c : word) {
              int next = 0;
              for (int q = 0; q < states; q++) {
                if ((current & (1 << q)) != 0) {
                  next |= transitions[q][c];
                }
              }
              current = next;
            }
            for (int q = 0; q < states; q++) {
              if ((current & (1 << q)) != 0 && accepting[q]) {
                return true;
              }
            }
            return false;
          };

      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 3);
        if (random.nextInt(4) == 0) {
          x[i].domain.inComplement(0, x[i], random.nextInt(4));
        }
      }
      String instance = "trial " + trial + " " + Arrays.deepToString(transitions);
      store.impose(new Regular(fsm, x));

      List<String> domainsAtLevel = new ArrayList<>();
      boolean consistent = store.consistency();
      assertRegularDomainConsistent(x, accepts, consistent, instance);
      while (consistent) {
        domainsAtLevel.add(Arrays.toString(x));
        List<IntVar> free = Arrays.stream(x).filter(v -> !v.singleton()).toList();
        if (free.isEmpty()) {
          break;
        }
        IntVar v = free.get(random.nextInt(free.size()));
        int[] values = valuesOf(v);
        store.setLevel(store.level + 1);
        v.domain.inComplement(store.level, v, values[random.nextInt(values.length)]);
        consistent = store.consistency();
        assertRegularDomainConsistent(x, accepts, consistent, instance);
      }
      // Backtrack level by level; domains must come back and propagation must still be correct.
      while (store.level > 0) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
        if (store.level < domainsAtLevel.size()) {
          assertThat(Arrays.toString(x)).as(instance).isEqualTo(domainsAtLevel.get(store.level));
        }
        List<IntVar> free = Arrays.stream(x).filter(v -> !v.singleton()).toList();
        if (!free.isEmpty() && random.nextBoolean()) {
          IntVar v = free.get(random.nextInt(free.size()));
          store.setLevel(store.level + 1);
          v.domain.in(store.level, v, v.min(), v.min());
          assertRegularDomainConsistent(x, accepts, store.consistency(), instance);
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
          if (store.level < domainsAtLevel.size()) {
            assertThat(Arrays.toString(x)).as(instance).isEqualTo(domainsAtLevel.get(store.level));
          }
        }
      }
    }
  }

  private static void assertRegularDomainConsistent(
      IntVar[] x, Predicate<int[]> accepts, boolean consistent, String instance) {
    if (!consistent) {
      assertThat(bruteForce(x, accepts)).as(instance + " failed with solutions").isEmpty();
      return;
    }
    List<int[]> solutions = bruteForce(x, accepts);
    assertThat(solutions).as(instance + " no solution " + Arrays.toString(x)).isNotEmpty();
    for (int i = 0; i < x.length; i++) {
      int position = i;
      int[] supported = solutions.stream().mapToInt(w -> w[position]).distinct().sorted().toArray();
      assertThat(valuesOf(x[i])).as(instance + " " + Arrays.toString(x)).containsExactly(supported);
    }
  }

  @Test
  void testValueEnumerationContinuesAfterDomainChange() {

    // Remove the value just returned and the next one, as Regular does while it prunes.
    for (IntDomain domain : new IntDomain[] {new IntervalDomain(), new SmallDenseDomain()}) {
      for (int v : new int[] {1, 3, 5}) {
        domain.unionAdapt(v, v);
      }
      List<Integer> values = new ArrayList<>();
      for (ValueEnumeration e = domain.valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        values.add(v);
        if (v == 1) {
          domain.subtractAdapt(1);
          domain.subtractAdapt(3);
          e.domainHasChanged();
        }
      }
      assertThat(values).as(domain.getClass().getSimpleName()).containsExactly(1, 5);
    }
  }

  private static List<int[]> bruteForce(IntVar[] vars, Predicate<int[]> constraint) {
    List<int[]> solutions = new ArrayList<>();
    int[][] domains = Arrays.stream(vars).map(SingleConstraintTest::valuesOf).toArray(int[][]::new);
    int[] index = new int[vars.length];
    while (true) {
      int[] assignment = new int[vars.length];
      for (int i = 0; i < vars.length; i++) {
        assignment[i] = domains[i][index[i]];
      }
      if (constraint.test(assignment)) {
        solutions.add(assignment);
      }
      int k = 0;
      while (k < vars.length && ++index[k] == domains[k].length) {
        index[k] = 0;
        k++;
      }
      if (k == vars.length) {
        return solutions;
      }
    }
  }

  private static String domainsOf(IntVar[] vars) {
    return Arrays.stream(vars).map(v -> v.dom().toString()).collect(Collectors.joining(" "));
  }

  private static String rerunAtNewLevel(Store store, Constraint c, IntVar[] vars) {
    int level = store.level;
    store.setLevel(level + 1);
    String result;
    try {
      c.consistency(store);
      result = domainsOf(vars);
    } catch (FailException e) {
      result = "FAIL";
    }
    store.removeLevel(level + 1);
    store.setLevel(level);
    return result;
  }

  /**
   * Propagates, then makes random decisions. After each propagation it checks that no solution
   * listed by the solver for the domains before propagation was removed, and that re-running the
   * constraint does not prune anything more.
   */
  private static void checkSupportsAndFixpointAlongRandomWalk(
      String instance,
      Store store,
      IntVar[] vars,
      Function<IntVar[], List<int[]>> solver,
      Supplier<String> rerun,
      Random random) {
    List<int[]> solutions = solver.apply(vars);
    for (int step = 0; step < 6; step++) {
      boolean consistent = store.consistency();
      if (solutions.isEmpty()) {
        // propagation does not have to detect every failure
        return;
      }
      String state = instance + " step " + step;
      assertThat(consistent).as(state).isTrue();
      for (int[] solution : solutions) {
        for (int i = 0; i < vars.length; i++) {
          assertThat(vars[i].domain.contains(solution[i]))
              .as(state + " keeps solution " + Arrays.toString(solution))
              .isTrue();
        }
      }
      String propagated = domainsOf(vars);
      assertThat(rerun.get()).as(state + " re-run").isEqualTo(propagated);

      IntVar v = vars[random.nextInt(vars.length)];
      if (v.singleton()) {
        continue;
      }
      store.setLevel(store.level + 1);
      int value = valuesOf(v)[random.nextInt(v.getSize())];
      if (random.nextBoolean()) {
        v.domain.inValue(store.level, v, value);
      } else {
        v.domain.inComplement(store.level, v, value);
      }
      solutions = solver.apply(vars);
    }
  }

  @Test
  void countWithCounterInTheListReachesFixpoint() {
    // magicseq: count(4, [x0, x1, x2, x3], x3). Narrowing the counter x3 to {0..3} removed the
    // value 4 from x3, which is also in the list, so the maximal count dropped to 2 but the
    // constraint was not run again for its own change.
    Store store = new Store();
    IntVar x0 = new IntVar(store, "x0", 1, 1);
    IntVar x1 = new IntVar(store, "x1");
    x1.addDom(1, 2);
    x1.addDom(4, 4);
    IntVar x2 = new IntVar(store, "x2", 0, 4);
    IntVar x3 = new IntVar(store, "x3", 0, 4);

    store.impose(new Count(new IntVar[] {x0, x1, x2, x3}, x3, 4));

    assertThat(store.consistency()).isTrue();
    assertThat(x3.dom().toString()).isEqualTo("{0..2}");
  }

  @Test
  void countAppliesCountedCaseAfterNarrowingCounter() {
    // Narrowing counter {0, 5..9} to [0, 3] makes it 0, so value 1 must be removed from the list
    // in the same call.
    Store store = new Store();
    IntVar[] list = {
      new IntVar(store, "y0", 0, 1), new IntVar(store, "y1", 0, 1), new IntVar(store, "y2", 0, 1)
    };
    IntVar counter = new IntVar(store, "c");
    counter.addDom(0, 0);
    counter.addDom(5, 9);

    store.impose(new Count(list, counter, 1));

    assertThat(store.consistency()).isTrue();
    assertThat(counter.singleton(0)).isTrue();
    for (IntVar y : list) {
      assertThat(y.singleton(0)).as("%s", y).isTrue();
    }
  }

  @Test
  void countKeepsSupportsAndReachesFixpoint() {
    Random random = new Random(17);
    for (int run = 0; run < 2000; run++) {
      Store store = new Store();
      int n = 2 + random.nextInt(3);
      IntVar[] list = new IntVar[n];
      for (int i = 0; i < n; i++) {
        list[i] = randomSubsetVar(store, "x" + i, 0, 4, random);
      }
      boolean aliased = random.nextBoolean();
      IntVar counter =
          aliased ? list[random.nextInt(n)] : randomSubsetVar(store, "c", 0, 4, random);
      int value = random.nextInt(5);
      IntVar[] vars =
          aliased
              ? list
              : Stream.concat(Arrays.stream(list), Stream.of(counter)).toArray(IntVar[]::new);
      int counterIndex = Arrays.asList(vars).indexOf(counter);
      String instance =
          "run " + run + " count(" + value + ", list, " + counter.id() + ") " + domainsOf(vars);
      Count count = new Count(list, counter, value);
      store.impose(count);
      checkSupportsAndFixpointAlongRandomWalk(
          instance,
          store,
          vars,
          vs ->
              bruteForce(
                  vs,
                  a -> IntStream.range(0, n).filter(i -> a[i] == value).count() == a[counterIndex]),
          () -> rerunAtNewLevel(store, count, vars),
          random);
    }
  }

  @Test
  void channelReifWithSharedBooleanReachesFixpoint() {
    // self_referential_quiz: the same b is used for q = 1 and q = 4. Value 4 is not in q, so b
    // becomes 0, but the item for value 1 had already been visited and q kept the value 1.
    Store store = new Store();
    IntVar q = new IntVar(store, "q");
    q.addDom(1, 3);
    q.addDom(5, 5);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar b2 = new IntVar(store, "b2", 0, 1);
    IntVar b3 = new IntVar(store, "b3", 0, 1);

    store.impose(new ChannelReif(q, new IntVar[] {b2, b3, b, b}, new int[] {2, 3, 1, 4}));

    assertThat(store.consistency()).isTrue();
    assertThat(b.singleton(0)).isTrue();
    assertThat(q.dom().toString()).isEqualTo("{2..3, 5}");
  }

  @Test
  void channelReifKeepsSupportsAndReachesFixpoint() {
    Random random = new Random(19);
    for (int run = 0; run < 2000; run++) {
      Store store = new Store();
      IntVar x = randomSubsetVar(store, "x", 0, 5, random);
      int k = 2 + random.nextInt(3);
      IntVar[] pool = new IntVar[1 + random.nextInt(k)];
      for (int i = 0; i < pool.length; i++) {
        pool[i] = new IntVar(store, "b" + i, 0, 1);
      }
      List<Integer> candidates = new ArrayList<>(List.of(0, 1, 2, 3, 4, 5));
      java.util.Collections.shuffle(candidates, random);
      int[] values = new int[k];
      int[] bIndex = new int[k];
      IntVar[] bs = new IntVar[k];
      for (int i = 0; i < k; i++) {
        values[i] = candidates.get(i);
        bIndex[i] = random.nextInt(pool.length);
        bs[i] = pool[bIndex[i]];
      }
      IntVar[] vars = Stream.concat(Stream.of(x), Arrays.stream(pool)).toArray(IntVar[]::new);
      String instance =
          "run "
              + run
              + " values "
              + Arrays.toString(values)
              + " b "
              + Arrays.toString(bIndex)
              + " "
              + domainsOf(vars);
      ChannelReif channel = new ChannelReif(x, bs, values);
      store.impose(channel);
      checkSupportsAndFixpointAlongRandomWalk(
          instance,
          store,
          vars,
          vs ->
              bruteForce(
                  vs,
                  a ->
                      IntStream.range(0, k)
                          .allMatch(i -> (a[1 + bIndex[i]] == 1) == (a[0] == values[i]))),
          () -> rerunAtNewLevel(store, channel, vars),
          random);
    }
  }

  @Test
  void amongReRunAfterLowerBorderReachesNDoesNotFail() {
    // hakank_among_global: once the lower border reaches n the remaining variables are pruned
    // out of the set and moved behind the new upper border; they are still in the variable queue.
    // A variable at position ub (outside the half-open range [lb, ub)) was not skipped and was
    // moved out a second time, so a re-run failed (or threw ArrayIndexOutOfBoundsException).
    Store store = new Store();
    IntVar[] list = {
      new IntVar(store, "a0", 0, 3),
      new IntVar(store, "a1", 0, 3),
      new IntVar(store, "a2", 0, 3),
      new IntVar(store, "a3", 0, 3)
    };
    IntVar n = new IntVar(store, "n", 2, 2);
    Among among = new Among(list, new IntervalDomain(1, 3), n);
    store.impose(among);
    assertThat(store.consistency()).isTrue();

    store.setLevel(store.level + 1);
    list[0].domain.inValue(store.level, list[0], 1);
    list[1].domain.inValue(store.level, list[1], 2);
    assertThat(store.consistency()).isTrue();
    assertThat(list[2].singleton(0)).isTrue();
    assertThat(list[3].singleton(0)).isTrue();

    String propagated = domainsOf(list) + " " + n.dom();
    store.setLevel(store.level + 1);
    among.consistency(store);
    assertThat(domainsOf(list) + " " + n.dom()).isEqualTo(propagated);
  }

  @Test
  void amongKeepsSupportsAndReachesFixpoint() {
    Random random = new Random(23);
    for (int run = 0; run < 2000; run++) {
      Store store = new Store();
      int size = 2 + random.nextInt(3);
      IntVar[] list = new IntVar[size];
      for (int i = 0; i < size; i++) {
        list[i] = randomSubsetVar(store, "x" + i, 0, 4, random);
      }
      int low = random.nextInt(4);
      int high = low + random.nextInt(3);
      IntVar n = randomSubsetVar(store, "n", 0, size, random);
      IntVar[] vars = Stream.concat(Arrays.stream(list), Stream.of(n)).toArray(IntVar[]::new);
      String instance = "run " + run + " kset " + low + ".." + high + " " + domainsOf(vars);
      Among among = new Among(list, new IntervalDomain(low, high), n);
      store.impose(among);
      checkSupportsAndFixpointAlongRandomWalk(
          instance,
          store,
          vars,
          vs ->
              bruteForce(
                  vs,
                  a ->
                      IntStream.range(0, size).filter(i -> a[i] >= low && a[i] <= high).count()
                          == a[size]),
          () -> rerunAtNewLevel(store, among, vars),
          random);
    }
  }

  @Test
  void alldiffBoundsReasoningOnHolesReachesFixpoint() {
    // latin-squares-fd2/07: after x32 = 1 the Hall interval {5..7} lowers x30.max to 4, which lands
    // on the hole and makes x30 = 2. Neither the new bound nor the new singleton was propagated,
    // so x29 kept 2 and x31 kept 2 and 3.
    Store store = new Store();
    IntVar x28 = new IntVar(store, "x28", 6, 6);
    IntVar x31 = new IntVar(store, "x31", 2, 4);
    IntVar x29 = new IntVar(store, "x29", 1, 3);
    IntVar x30 = new IntVar(store, "x30");
    x30.addDom(2, 2);
    x30.addDom(5, 5);
    x30.addDom(7, 7);
    IntVar x32 = new IntVar(store, "x32");
    x32.addDom(1, 1);
    x32.addDom(4, 4);
    IntVar x34 = new IntVar(store, "x34");
    x34.addDom(1, 1);
    x34.addDom(5, 5);
    x34.addDom(7, 7);
    IntVar x33 = new IntVar(store, "x33");
    x33.addDom(5, 5);
    x33.addDom(7, 7);
    store.impose(new Alldiff(new IntVar[] {x28, x31, x29, x30, x32, x34, x33}));
    assertThat(store.consistency()).isTrue();

    store.setLevel(store.level + 1);
    x32.domain.inValue(store.level, x32, 1);

    assertThat(store.consistency()).isTrue();
    assertThat(x30.singleton(2)).as("x30 = %s", x30.dom()).isTrue();
    assertThat(x29.singleton(3)).as("x29 = %s", x29.dom()).isTrue();
    assertThat(x31.singleton(4)).as("x31 = %s", x31.dom()).isTrue();
  }

  @Test
  void alldiffKeepsSupportsAndReachesFixpoint() {
    Random random = new Random(29);
    for (int run = 0; run < 2000; run++) {
      Store store = new Store();
      int n = 3 + random.nextInt(3);
      IntVar[] vars = new IntVar[n];
      for (int i = 0; i < n; i++) {
        vars[i] = randomSubsetVar(store, "x" + i, 0, n, random);
      }
      String instance = "run " + run + " " + domainsOf(vars);
      Alldiff alldiff = new Alldiff(vars);
      store.impose(alldiff);
      checkSupportsAndFixpointAlongRandomWalk(
          instance,
          store,
          vars,
          vs -> bruteForce(vs, a -> Arrays.stream(a).distinct().count() == a.length),
          () -> rerunAtNewLevel(store, alldiff, vars),
          random);
    }
  }

  private static String knapsackOnCopies(int[] profits, int[] weights, IntVar[] vars) {
    Store copyStore = new Store();
    IntVar[] copies = new IntVar[vars.length];
    for (int i = 0; i < vars.length; i++) {
      copies[i] = new IntVar(copyStore, vars[i].id());
      copies[i].addDom(vars[i].dom());
    }
    int n = profits.length;
    copyStore.impose(
        new Knapsack(profits, weights, Arrays.copyOf(copies, n), copies[n], copies[n + 1]));
    return copyStore.consistency() ? domainsOf(copies) : "FAIL";
  }

  private static List<int[]> knapsackSolutions(int[] profits, int[] weights, IntVar[] vars) {
    int n = profits.length;
    List<int[]> solutions = new ArrayList<>();
    for (int[] q : bruteForce(Arrays.copyOf(vars, n), a -> true)) {
      int capacity = 0;
      int profit = 0;
      for (int i = 0; i < n; i++) {
        capacity += weights[i] * q[i];
        profit += profits[i] * q[i];
      }
      if (vars[n].domain.contains(capacity) && vars[n + 1].domain.contains(profit)) {
        int[] solution = Arrays.copyOf(q, n + 2);
        solution[n] = capacity;
        solution[n + 1] = profit;
        solutions.add(solution);
      }
    }
    return solutions;
  }

  @Test
  void knapsackReachesFixpoint() {
    // Raising the minimal profit made the mandatory part raise the used capacity, which allows a
    // stronger capacity bound, but the pass was not repeated and the store does not re-run the
    // constraint for its own changes.
    int[] weights = {15, 11, 10, 15, 11, 11, 14, 6};
    int[] profits = {18, 20, 25, 9, 10, 19, 24, 22};
    Store store = new Store();
    IntVar[] vars = new IntVar[weights.length + 2];
    for (int i = 0; i < weights.length; i++) {
      vars[i] = new IntVar(store, "q" + i, 0, i == 4 ? 3 : 1);
    }
    vars[weights.length] = new IntVar(store, "capacity", 0, 115);
    vars[weights.length + 1] = new IntVar(store, "profit", 0, 167);
    IntVar profit = vars[weights.length + 1];
    store.impose(
        new Knapsack(
            profits, weights, Arrays.copyOf(vars, weights.length), vars[weights.length], profit));
    assertThat(store.consistency()).isTrue();

    store.setLevel(store.level + 1);
    profit.domain.inMin(store.level, profit, 162);

    assertThat(store.consistency()).isTrue();
    assertThat(knapsackOnCopies(profits, weights, vars)).isEqualTo(domainsOf(vars));
  }

  @Test
  void knapsackKeepsSupportsAndReachesFixpoint() {
    Random random = new Random(31);
    for (int run = 0; run < 2000; run++) {
      Store store = new Store();
      int n = 2 + random.nextInt(5);
      int[] weights = new int[n];
      int[] profits = new int[n];
      IntVar[] vars = new IntVar[n + 2];
      int weightSum = 0;
      int profitSum = 0;
      for (int i = 0; i < n; i++) {
        weights[i] = 1 + random.nextInt(12);
        profits[i] = 1 + random.nextInt(20);
        int max = random.nextBoolean() ? 1 : 1 + random.nextInt(3);
        vars[i] = new IntVar(store, "q" + i, 0, max);
        weightSum += weights[i] * max;
        profitSum += profits[i] * max;
      }
      vars[n] = new IntVar(store, "capacity", 0, weightSum);
      vars[n + 1] = new IntVar(store, "profit", 0, profitSum);
      String instance =
          "run "
              + run
              + " weights "
              + Arrays.toString(weights)
              + " profits "
              + Arrays.toString(profits)
              + " "
              + domainsOf(vars);
      store.impose(new Knapsack(profits, weights, Arrays.copyOf(vars, n), vars[n], vars[n + 1]));
      checkSupportsAndFixpointAlongRandomWalk(
          instance,
          store,
          vars,
          vs -> knapsackSolutions(profits, weights, vs),
          () -> knapsackOnCopies(profits, weights, vars),
          random);
    }
  }

  private static IntVar randomSubsetVar(Store store, String name, int min, int max, Random random) {
    IntVar v = new IntVar(store, name);
    for (int i = min; i <= max; i++) {
      if (random.nextInt(3) > 0) {
        v.addDom(i, i);
      }
    }
    if (v.domain.isEmpty()) {
      v.addDom(min, min);
    }
    return v;
  }

  private static int[] valuesOf(IntVar v) {
    int[] values = new int[v.getSize()];
    int i = 0;
    for (ValueEnumeration e = v.domain.valueEnumeration(); e.hasMoreElements(); ) {
      values[i++] = e.nextElement();
    }
    return values;
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

  // The cost of a flow was summed with an early exit once it passed the cost bound, which is wrong
  // when later arcs have negative costs: a feasible flow was taken as too expensive.
  @Test
  void testNetworkFlowWithNegativeCosts() {

    Store store = new Store();
    IntVar f0 = new IntVar(store, "f0", 1, 3);
    IntVar f1 = new IntVar(store, "f1", 1, 3);
    IntVar cost = new IntVar(store, "cost", -4, 6);

    NetworkBuilder net = new NetworkBuilder();
    Node n0 = net.addNode("n0", 0);
    Node n1 = net.addNode("n1", 0);
    net.addArc(n0, n1, -1, f0);
    net.addArc(n1, n0, 3, f1);
    net.setCostVariable(cost);
    store.impose(net.build());

    // f0 = f1 = f and cost = 2 * f; f1 is labelled first, so the flow 3 is tried first
    assertThat(noOfAllSolutions(store, new IntVar[] {f1, f0, cost})).isEqualTo(3);
  }

  // Compares network flow with a brute-force count on random small networks with negative costs,
  // negative flows and loops (arcs from a node to itself).
  @Test
  void testNetworkFlowWithNegativeValuesAndLoopsAgainstBruteForce() {

    Random random = new Random(1185);
    for (int trial = 0; trial < 300; trial++) {
      int nodeCount = 2 + random.nextInt(3);
      int arcCount = 1 + random.nextInt(5);
      int[][] arcs = new int[arcCount][2];
      int[] weights = new int[arcCount];
      int[][] flowDomains = new int[arcCount][2];
      int[] balance = new int[nodeCount];
      for (int i = 0; i < arcCount; i++) {
        arcs[i][0] = random.nextInt(nodeCount);
        arcs[i][1] =
            random.nextInt(5) == 0
                ? arcs[i][0]
                : (arcs[i][0] + 1 + random.nextInt(nodeCount - 1)) % nodeCount;
        weights[i] = random.nextInt(7) - 3;
        int min = random.nextInt(5) - 2;
        flowDomains[i] = new int[] {min, min + random.nextInt(4)};
        // balances come from a random flow so that most networks are feasible
        int flow = min + random.nextInt(flowDomains[i][1] - min + 1);
        balance[arcs[i][0]] += flow;
        balance[arcs[i][1]] -= flow;
      }
      int costMin = random.nextInt(14) - 6;
      int costMax = costMin + random.nextInt(12);

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

  @Test
  void testNetworkFlowFixesCostWhenFlowsAreFixed() {

    Store store = new Store();
    IntVar f0 = new IntVar(store, "f0", 0, 3);
    IntVar f1 = new IntVar(store, "f1", 0, 3);
    IntVar cost = new IntVar(store, "cost", 0, 100);

    NetworkBuilder net = new NetworkBuilder();
    Node source = net.addNode("source", 3);
    Node sink = net.addNode("sink", -3);
    net.addArc(source, sink, 1, f0);
    net.addArc(source, sink, 2, f1);
    net.setCostVariable(cost);
    store.impose(net.build());
    assertThat(store.consistency()).isTrue();

    store.setLevel(store.level + 1);
    f1.domain.in(store.level, f1, 2, 2);
    assertThat(store.consistency()).isTrue();
    assertThat(f0.value()).isEqualTo(1);
    assertThat(cost.singleton()).isTrue();
    assertThat(cost.value()).isEqualTo(5);
  }

  // The cost of an arc with a variable weight is bounded by the smallest weight, which is only a
  // lower bound for flows that are not negative.
  @Test
  void testNetworkFlowRejectsVariableWeightOnNegativeFlow() {

    Store store = new Store();
    NetworkBuilder net = new NetworkBuilder();
    Node n0 = net.addNode("n0", 0);
    Node n1 = net.addNode("n1", 0);
    IntVar weight = new IntVar(store, "w", 1, 2);
    IntVar flow = new IntVar(store, "f", -2, 0);

    assertThatThrownBy(() -> net.addArc(n0, n1, weight, flow))
        .isInstanceOf(IllegalArgumentException.class);
  }

  // A variable whose domain had values that are not counted got the arc for those values once per
  // counted value, and the copies pruned each other, so solutions were lost.
  @Test
  void testSoftGccWithValuesThatAreNotCounted() {

    // x2 has the domain {1, 3}
    int[][] domains = {{0, 3}, {0, 3}, {1, 1}};
    int[] values = {1, 2};
    int[][] hard = {{1, 3}, {0, 3}};
    int[][] soft = {{1, 1}, {2, 3}};

    int[] counts = new int[2];
    for (boolean network : new boolean[] {true, false}) {
      Store store = new Store();
      IntVar[] x = new IntVar[domains.length];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, domains[i][0], domains[i][1]);
      }
      x[2].addDom(3, 3);
      IntVar[] hardCounters = new IntVar[values.length];
      IntVar[] softCounters = new IntVar[values.length];
      for (int i = 0; i < values.length; i++) {
        hardCounters[i] = new IntVar(store, "h" + i, hard[i][0], hard[i][1]);
        softCounters[i] = new IntVar(store, "s" + i, soft[i][0], soft[i][1]);
      }
      IntVar cost = new IntVar(store, "cost", 1, 5);
      SoftGCC softGcc =
          new SoftGCC(x, hardCounters, values, softCounters, cost, ViolationMeasure.VALUE_BASED);
      if (network) {
        store.imposeDecomposition(softGcc);
      } else {
        softGcc.primitiveDecomposition(store).forEach(store::impose);
      }
      counts[network ? 0 : 1] =
          noOfAllSolutions(store, x, hardCounters, softCounters, new IntVar[] {cost});
    }
    assertThat(counts[1]).isPositive();
    assertThat(counts[0]).isEqualTo(counts[1]);
  }

  @Test
  void testComparisonsOverInconsistentDomainsFailWithoutException() {

    Store store = new Store();
    IntVar two = new IntVar(store, "two", 2, 2);
    IntVar small = new IntVar(store, "small", 1, 2);
    store.impose(new XltY(two, small));
    assertThat(store.consistency()).isFalse();

    store = new Store();
    two = new IntVar(store, "two", 2, 2);
    small = new IntVar(store, "small", 1, 2);
    store.impose(new XgtY(small, two));
    assertThat(store.consistency()).isFalse();

    store = new Store();
    two = new IntVar(store, "two", 2, 2);
    IntVar alsoTwo = new IntVar(store, "alsoTwo", 2, 2);
    store.impose(new XneqY(two, alsoTwo));
    assertThat(store.consistency()).isFalse();
  }

  // Regression test for https://github.com/radsz/jacop/issues/47 (fails with
  // -Djacop.asserts.enabled=true before the fix).
  @Test
  void testSoftAlldifferentOnInfeasibleStore() {

    Store store = new Store();
    IntVar cost = new IntVar(store, "cost", 0, 2);
    IntVar[] vars = {new IntVar(store, "v_0", 0, 1), new IntVar(store, "v_1", 0, 1)};
    store.impose(new In(cost, new IntervalDomain(0, 0)));
    store.impose(new In(vars[0], new IntervalDomain(0, 0)));
    store.impose(new In(vars[1], new IntervalDomain(0, 0)));

    store.imposeDecomposition(
        new SoftAlldifferent(vars, cost, ViolationMeasure.DECOMPOSITION_BASED));

    assertThat(store.consistency()).isFalse();
  }

  // Regression test for https://github.com/radsz/jacop/issues/47 (fails with
  // -Djacop.asserts.enabled=true before the fix).
  @Test
  void testSoftGccOnInfeasibleStore() {

    Store store = new Store();
    IntVar cost = new IntVar(store, "cost", 0, 2);
    IntVar[] xVars = {new IntVar(store, "x0", 0, 1), new IntVar(store, "x1", 0, 1)};
    IntVar[] hardCounters = {
      new IntVar(store, "hardCounter0", 0, 2), new IntVar(store, "hardCounter1", 0, 2)
    };
    IntVar[] softCounters = {
      new IntVar(store, "softCounter0", 0, 2), new IntVar(store, "softCounter1", 0, 2)
    };
    store.impose(new In(xVars[0], new IntervalDomain(0, 0)));
    store.impose(new In(xVars[1], new IntervalDomain(0, 0)));
    store.impose(new In(hardCounters[0], new IntervalDomain(2, 2)));
    store.impose(new In(softCounters[0], new IntervalDomain(1, 1)));
    store.impose(new In(softCounters[1], new IntervalDomain(2, 2)));
    store.impose(new In(cost, new IntervalDomain(1, 1)));

    store.imposeDecomposition(
        new SoftGCC(xVars, hardCounters, softCounters, cost, ViolationMeasure.VALUE_BASED));

    assertThat(store.consistency()).isFalse();
  }

  // Regression test for https://github.com/radsz/jacop/issues/30
  @Test
  void testRegularExpressionParser() {

    assertThat(parseRegularExpression("(32.14*)").toString()).isEqualTo("32.(14)*");
    assertThat(parseRegularExpression("1+2.3*").toString()).isEqualTo("(1+2.(3)*)");
    // literals in a sum are kept first and in reverse order
    assertThat(parseRegularExpression("(1+2).3").toString()).isEqualTo("(2+1).3");

    assertThatThrownBy(() -> parseRegularExpression("(.32*)"))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> parseRegularExpression("(32.*)"))
        .isInstanceOf(IllegalArgumentException.class);
    // a missing operator between ")" and "17" used to silently drop the rest of the input
    assertThatThrownBy(() -> parseRegularExpression("(32.14*)17*.23"))
        .isInstanceOf(IllegalArgumentException.class);
  }

  // Regression test for https://github.com/radsz/jacop/issues/30: compares the words accepted by a
  // Regular constraint built from a parsed expression with java.util.regex on random expressions.
  @Test
  void testRegularExpressionAgainstJavaRegex() {

    Random random = new Random(30);
    for (int trial = 0; trial < 300; trial++) {
      String[] expression = randomRegularExpression(random, 1 + random.nextInt(4));
      int length = 1 + random.nextInt(4);

      Fsm fsm = parseRegularExpression(expression[0]).parseToFsm();
      Store store = new Store();
      IntVar[] x = new IntVar[length];
      for (int i = 0; i < length; i++) {
        x[i] = new IntVar(store, "x" + i, 1, 3);
      }
      store.impose(new Regular(fsm, x));

      Pattern pattern = Pattern.compile(expression[1]);
      int expected = 0;
      for (int code = 0; code < Math.pow(3, length); code++) {
        StringBuilder word = new StringBuilder();
        for (int i = 0, c = code; i < length; i++, c /= 3) {
          word.append(1 + c % 3);
        }
        if (pattern.matcher(word).matches()) {
          expected++;
        }
      }

      assertThat(noOfAllSolutions(store, x))
          .as("expression %s, length %d", expression[0], length)
          .isEqualTo(expected);
    }
  }

  private static RegularExpressionParser.Expression parseRegularExpression(String expression) {
    return new RegularExpressionParser(new StringReader(expression)).parse(false);
  }

  /** Returns a random expression over 1..3 in JaCoP syntax and in java.util.regex syntax. */
  private static String[] randomRegularExpression(Random random, int depth) {
    int kind = depth <= 0 ? 0 : random.nextInt(4);
    if (kind == 0) {
      String digit = String.valueOf(1 + random.nextInt(3));
      return new String[] {digit, digit};
    }
    String[] a = randomRegularExpression(random, depth - 1);
    if (kind == 3) {
      return new String[] {"(" + a[0] + ")*", "(?:" + a[1] + ")*"};
    }
    String[] b = randomRegularExpression(random, depth - 1);
    if (kind == 1) {
      return new String[] {"(" + a[0] + "." + b[0] + ")", "(?:" + a[1] + b[1] + ")"};
    }
    return new String[] {"(" + a[0] + "+" + b[0] + ")", "(?:" + a[1] + "|" + b[1] + ")"};
  }

  @Test
  void testCumulativeOptionalAllPresent() {

    // All tasks present, so the optional profile is never used; this only ran into the
    // reflective event accessors that could not read ProfileOptional events.
    assertThat(cumulativeSolutions(true, 3, 4, 1, new int[] {1, 2, 1}, 2, false))
        .isEqualTo(cumulativeBruteForce(3, 4, 1, new int[] {1, 2, 1}, 2, false));
  }

  @Test
  void testCumulativeVariableDurations() {

    // Two tasks that can never overload the resource; edge finding used a capacity map built for
    // the original task order after the tasks had been reordered, and pruned valid starts.
    assertThat(cumulativeSolutions(false, 2, 2, 3, new int[] {2, 1}, 3, false))
        .isEqualTo(cumulativeBruteForce(2, 2, 3, new int[] {2, 1}, 3, false));
    assertThat(cumulativeSolutions(false, 4, 4, 2, new int[] {1, 2, 1, 1}, 2, false))
        .isEqualTo(cumulativeBruteForce(4, 4, 2, new int[] {1, 2, 1, 1}, 2, false));
  }

  @Test
  void testCumulativeOptional() {

    // An optional task that fits right after the profile of the present tasks was made absent.
    assertThat(cumulativeSolutions(true, 2, 2, 1, new int[] {1, 1}, 1, true))
        .isEqualTo(cumulativeBruteForce(2, 2, 1, new int[] {1, 1}, 1, true));
    assertThat(cumulativeSolutions(true, 4, 4, 2, new int[] {1, 2, 1, 1}, 2, true))
        .isEqualTo(cumulativeBruteForce(4, 4, 2, new int[] {1, 2, 1, 1}, 2, true));
  }

  /**
   * Counts the solutions of a cumulative constraint over tasks with starts in 0..horizon-1,
   * durations in 1..maxDuration and the given resource requirements.
   */
  private int cumulativeSolutions(
      boolean optionalConstraint,
      int noOfTasks,
      int horizon,
      int maxDuration,
      int[] resources,
      int limit,
      boolean optionalTasks) {

    Store store = new Store();

    IntVar[] starts = getIntVars(store, "s", noOfTasks, horizon);
    IntVar[] durations = new IntVar[noOfTasks];
    IntVar[] res = new IntVar[noOfTasks];
    IntVar[] present = new IntVar[noOfTasks];
    for (int i = 0; i < noOfTasks; i++) {
      durations[i] = new IntVar(store, "d" + i, 1, maxDuration);
      res[i] = new IntVar(store, "r" + i, resources[i], resources[i]);
      present[i] = new IntVar(store, "o" + i, optionalTasks ? 0 : 1, 1);
    }
    IntVar limitVar = new IntVar(store, "limit", limit, limit);

    if (optionalConstraint) {
      store.impose(new CumulativeOptional(starts, durations, res, limitVar, present));
    } else {
      store.impose(new Cumulative(starts, durations, res, limitVar));
    }

    return noOfAllSolutions(store, starts, durations, present);
  }

  /** Counts the same solutions as {@link #cumulativeSolutions} by enumerating all assignments. */
  private static int cumulativeBruteForce(
      int noOfTasks,
      int horizon,
      int maxDuration,
      int[] resources,
      int limit,
      boolean optionalTasks) {

    int perTask = horizon * maxDuration * (optionalTasks ? 2 : 1);
    int combinations = (int) Math.pow(perTask, noOfTasks);
    int count = 0;
    for (int code = 0; code < combinations; code++) {
      int rest = code;
      int[] s = new int[noOfTasks];
      int[] d = new int[noOfTasks];
      boolean[] o = new boolean[noOfTasks];
      for (int i = 0; i < noOfTasks; i++) {
        s[i] = rest % horizon;
        rest /= horizon;
        d[i] = 1 + rest % maxDuration;
        rest /= maxDuration;
        o[i] = !optionalTasks || rest % 2 == 1;
        if (optionalTasks) {
          rest /= 2;
        }
      }
      boolean ok = true;
      for (int t = 0; t < horizon + maxDuration && ok; t++) {
        int load = 0;
        for (int i = 0; i < noOfTasks; i++) {
          if (o[i] && s[i] <= t && t < s[i] + d[i]) {
            load += resources[i];
          }
        }
        ok = load <= limit;
      }
      if (ok) {
        count++;
      }
    }
    return count;
  }

  static class TestWatcherExtension implements BeforeEachCallback {
    @Override
    public void beforeEach(ExtensionContext context) {
      log.info("Starting test: " + context.getDisplayName());
    }
  }
}
