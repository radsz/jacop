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
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
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
import org.jacop.constraints.AllEqual;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.AlldifferentExcept;
import org.jacop.constraints.AlldifferentExceptZero;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Among;
import org.jacop.constraints.AmongVar;
import org.jacop.constraints.ArgMax;
import org.jacop.constraints.ArgMin;
import org.jacop.constraints.Assignment;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.Decreasing;
import org.jacop.constraints.Diff2;
import org.jacop.constraints.Disjoint;
import org.jacop.constraints.DisjointConditional;
import org.jacop.constraints.Distance;
import org.jacop.constraints.ElementBool;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.ElementVariable;
import org.jacop.constraints.EqBool;
import org.jacop.constraints.ExtensionalConflictVa;
import org.jacop.constraints.GCC;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.IfThenBool;
import org.jacop.constraints.IfThenElse;
import org.jacop.constraints.In;
import org.jacop.constraints.Increasing;
import org.jacop.constraints.Lex;
import org.jacop.constraints.LinearBool;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.MaxSimple;
import org.jacop.constraints.Member;
import org.jacop.constraints.Min;
import org.jacop.constraints.MinSimple;
import org.jacop.constraints.NoGood;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Sequence;
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
import org.jacop.constraints.XgteqY;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmodYeqZ;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.Xor;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusClteqZImplied;
import org.jacop.constraints.XplusCneqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.constraints.geost.Dbox;
import org.jacop.constraints.geost.ExternalConstraint;
import org.jacop.constraints.geost.Geost;
import org.jacop.constraints.geost.GeostObject;
import org.jacop.constraints.geost.NonOverlapping;
import org.jacop.constraints.geost.Shape;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.constraints.knapsack.KnapsackDP;
import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.constraints.regular.Regular;
import org.jacop.constraints.table.SimpleTable;
import org.jacop.constraints.table.Table;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.SmallDenseDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.util.DominatorTree;
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

  // Among ignored events on the count variable, so when the count variable was also in the list
  // its value was never counted and wrong solutions were accepted, e.g. x = [3, 3, 1] with
  // n = x[2] and K = {1}. Such models are now rejected.
  @Test
  void testAmongRejectsCountVariableInList() {

    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 0, 3), new IntVar(store, "x1", 1, 3), new IntVar(store, "x2", 0, 3)
    };

    assertThatThrownBy(() -> new Among(x, new IntervalDomain(1, 1), x[2]))
        .isInstanceOf(IllegalArgumentException.class);
  }

  // AmongVar gave wrong solutions and removed supported values when x, y and n shared variables,
  // e.g. x = [a], y = [n, b, c] removed a supported value of a. Such models are now rejected.
  @Test
  void testAmongVarRejectsSharedVariables() {

    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 3);
    IntVar b = new IntVar(store, "b", 0, 3);
    IntVar n = new IntVar(store, "n", 0, 3);

    assertThatThrownBy(() -> new AmongVar(new IntVar[] {a}, new IntVar[] {n, b}, n))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new AmongVar(new IntVar[] {a, b}, new IntVar[] {b}, n))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new AmongVar(new IntVar[] {a, n}, new IntVar[] {b}, n))
        .isInstanceOf(IllegalArgumentException.class);
  }

  // Bins numbered from a negative value: the lower bound pruning indexed a BitSet by bin number
  // and threw NegativeArraySizeException or IndexOutOfBoundsException.
  @Test
  void testBinpackingNegativeBinNumbers() {

    Store store = new Store();
    IntVar[] items = {
      new IntVar(store, "i0", -4, -2),
      new IntVar(store, "i1", -4, -2),
      new IntVar(store, "i2", -4, -2)
    };
    IntVar[] binLoad = getIntVars(store, "binLoad", 3, 7);
    store.impose(new Binpacking(items, binLoad, new int[] {3, 2, 1}, -4));

    int noOfSolutions =
        noOfAllSolutions(
            store,
            Stream.concat(Arrays.stream(items), Arrays.stream(binLoad)).toArray(IntVar[]::new));

    assertThat(noOfSolutions).isEqualTo(27);
  }

  // Items of weight zero were dropped from the constraint, so their bin variables could take
  // values outside the bins (MiniZinc bin_packing_capa and bin_packing_load require every item
  // to be in one of the bins).
  @Test
  void testBinpackingZeroWeightItemInExistingBin() {

    Store store = new Store();
    IntVar[] items = {new IntVar(store, "i0", 0, 3), new IntVar(store, "i1", 0, 3)};
    IntVar[] binLoad = getIntVars(store, "binLoad", 2, 3);
    store.impose(new Binpacking(items, binLoad, new int[] {0, 2}, 1));

    int noOfSolutions =
        noOfAllSolutions(
            store,
            Stream.concat(Arrays.stream(items), Arrays.stream(binLoad)).toArray(IntVar[]::new));

    // i0 in {1, 2}, i1 in {1, 2}
    assertThat(noOfSolutions).isEqualTo(4);
  }

  // The constructor without minBin computes the first bin from items of non-zero weight, but it
  // started from the first item even when its weight was zero, shifting all bins.
  @Test
  void testBinpackingDefaultMinBinIgnoresZeroWeightItems() {

    Store store = new Store();
    IntVar[] items = {
      new IntVar(store, "i0", 0, 2), new IntVar(store, "i1", 1, 2), new IntVar(store, "i2", 2, 2)
    };
    IntVar[] binLoad = {new IntVar(store, "l1", 0, 0), new IntVar(store, "l2", 4, 4)};
    store.impose(new Binpacking(items, binLoad, new int[] {0, 3, 1}));

    int noOfSolutions =
        noOfAllSolutions(
            store,
            Stream.concat(Arrays.stream(items), Arrays.stream(binLoad)).toArray(IntVar[]::new));

    // bins are 1 and 2: i1 = i2 = 2, i0 in {1, 2}
    assertThat(noOfSolutions).isEqualTo(2);
  }

  // The total weight of all items exceeded Integer.MAX_VALUE and overflowed, so the constraint
  // failed on a satisfiable problem.
  @Test
  void testBinpackingTotalWeightAboveIntRange() {

    Store store = new Store();
    IntVar[] items = getIntVars(store, "item", 5, 5);
    IntVar[] binLoad = new IntVar[5];
    for (int i = 0; i < binLoad.length; i++) {
      binLoad[i] = new IntVar(store, "binLoad" + i, 0, IntDomain.MAX_INT);
    }
    int[] w = new int[5];
    Arrays.fill(w, 500_000_000);
    store.impose(new Binpacking(items, binLoad, w, 0));

    // one item per bin
    assertThat(noOfAllSolutions(store, items)).isEqualTo(120);
  }

  // Changes made by Binpacking itself are not queued again by the store, and bins affected by its
  // own pruning were not processed again. Here the propagator fixed item 0 to bin 3 and removed
  // bin 3 from item 2, but did not process bin 1 again, whose load can then be at most 10.
  @Test
  void testBinpackingReachesFixpoint() {

    Store store = new Store();
    int[][] binDomains = {{1, 3}, {0, 1, 2}, {0, 2, 3}, {0, 1, 2}, {0, 1, 2}, {3}, {1}};
    IntVar[] items = new IntVar[binDomains.length];
    for (int i = 0; i < items.length; i++) {
      items[i] = new IntVar(store, "item" + i);
      for (int v : binDomains[i]) {
        items[i].addDom(v, v);
      }
    }
    IntVar[] binLoad = {
      new IntVar(store, "l0"),
      new IntVar(store, "l1", 1, 11),
      new IntVar(store, "l2", 0, 11),
      new IntVar(store, "l3", 9, 11)
    };
    binLoad[0].addDom(0, 2);
    binLoad[0].addDom(6, 11);
    store.impose(new Binpacking(items, binLoad, new int[] {5, 1, 3, 5, 8, 5, 1}, 0));

    assertThat(store.consistency()).isTrue();
    assertThat(items[0].value()).isEqualTo(3);
    assertThat(binLoad[3].value()).isEqualTo(10);
    assertThat(binLoad[1].max()).isEqualTo(10);
  }

  // Bins of capacity 9 hold 3, 2, 6 and 6, so their free space is 6, 7, 3 and 3: the items 5, 5
  // and 4 cannot all be packed. The bin-count lower bound used capacity 9 and padded only bins
  // with items (reduction R0), and was switched off once every bin was used; with the largest free
  // space as capacity (reduction RMin) it detects the failure.
  @Test
  void testBinpackingLowerBoundWithAllBinsUsed() {

    Store store = new Store();
    IntVar[] items = new IntVar[9];
    for (int i = 0; i < 4; i++) {
      items[i] = new IntVar(store, "f" + i, i, i);
    }
    for (int i = 4; i < 9; i++) {
      items[i] = new IntVar(store, "x" + i, 0, 3);
    }
    IntVar[] binLoad = getIntVars(store, "binLoad", 4, 10);
    store.impose(new Binpacking(items, binLoad, new int[] {3, 2, 6, 6, 5, 1, 2, 4, 5}, 0));

    assertThat(store.consistency()).isFalse();
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

  // Subcircuit picks the dominance root at random; the choice must come from a fixed seed so the
  // same model explores the same search tree on every run.
  @Test
  void testSubcircuitSearchIsReproducible() {

    Set<Integer> failures = new HashSet<>();
    for (int run = 0; run < 4; run++) {
      Store store = new Store();
      IntVar[] x = new IntVar[8];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, 1, x.length);
      }
      store.impose(new Subcircuit(x));
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      search.setPrintInfo(false);
      search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()));
      // 1 + sum over k = 2..8 of C(8, k) * (k - 1)! subcircuits
      assertThat(search.getSolutionListener().solutionsNo()).isEqualTo(16_065);
      failures.add(search.getWrongDecisions());
    }
    assertThat(failures).hasSize(1);
  }

  // x is a subcircuit when x[i] = i + 1 marks node i as outside the circuit and the other nodes
  // follow x as successors around exactly one cycle (no cycle at all is allowed too).
  private static boolean isSubcircuit(int[] x) {
    int n = x.length;
    int start = -1;
    int inCircuit = 0;
    for (int i = 0; i < n; i++) {
      if (x[i] < 1 || x[i] > n) {
        return false;
      }
      if (x[i] != i + 1) {
        start = i;
        inCircuit++;
      }
    }
    if (inCircuit == 0) {
      return true;
    }
    int length = 0;
    int node = start;
    do {
      node = x[node] - 1;
      length++;
    } while (node != start && length <= n);
    return node == start && length == inCircuit;
  }

  // Domains mix values inside 1..n with values outside it, so the first propagation also has to
  // trim the list to 1..n.
  private static IntVar[] randomSubcircuitVars(Store store, int n, Random random) {
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = randomSubsetVar(store, "x" + (i + 1), random.nextInt(4) == 0 ? 0 : 1, n, random);
      if (random.nextInt(8) == 0) {
        x[i].addDom(n + 1, n + 1);
      }
    }
    return x;
  }

  // Subcircuit is not idempotent on purpose: dominator pruning pauses after calls that find
  // nothing. So the walk checks that no solution is lost, and not the fixpoint.
  @Test
  void subcircuitKeepsSupports() {
    Random random = new Random(31);
    for (int run = 0; run < 3000; run++) {
      Store store = new Store();
      IntVar[] x = randomSubcircuitVars(store, 1 + random.nextInt(6), random);
      String instance = "run " + run + " subcircuit " + domainsOf(x);
      store.impose(new Subcircuit(x));
      checkSupportsAndFixpointAlongRandomWalk(
          instance,
          store,
          x,
          vs -> bruteForce(vs, SingleConstraintTest::isSubcircuit),
          () -> domainsOf(x),
          random);
    }
  }

  // Nodes 3, 4 and 5 must be on the circuit, so nodes 1 and 2 stay out. Their component is found
  // inside the search that starts at node 1, and the component pruning used to leave it unchecked.
  @Test
  void subcircuitKeepsNodesOutsideTheCircuitComponentOut() {
    Store store = new Store();
    IntVar x1 = new IntVar(store, "x1", 1, 3);
    IntVar x2 = new IntVar(store, "x2", 1, 2);
    IntVar x3 = new IntVar(store, "x3", 4, 5);
    IntVar x4 = new IntVar(store, "x4", 3, 3);
    x4.addDom(5, 5);
    IntVar x5 = new IntVar(store, "x5", 3, 4);
    // only the component pruning, dominator pruning would find this too
    System.setProperty("sub_circuit_dominance_pruning", "false");
    try {
      store.impose(new Subcircuit(new IntVar[] {x1, x2, x3, x4, x5}));
    } finally {
      System.clearProperty("sub_circuit_dominance_pruning");
    }

    assertThat(store.consistency()).isTrue();
    assertThat(x1.singleton(1)).as("%s", x1).isTrue();
    assertThat(x2.singleton(2)).as("%s", x2).isTrue();
  }

  @Test
  void subcircuitFindsExactlyTheBruteForceSolutions() {
    Random random = new Random(37);
    for (int run = 0; run < 1500; run++) {
      Store store = new Store();
      IntVar[] x = randomSubcircuitVars(store, 1 + random.nextInt(6), random);
      String instance = "run " + run + " subcircuit " + domainsOf(x);
      Set<String> expected =
          bruteForce(x, SingleConstraintTest::isSubcircuit).stream()
              .map(Arrays::toString)
              .collect(Collectors.toSet());
      store.impose(new Subcircuit(x));

      Set<String> found = new HashSet<>();
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      search.getSolutionListener().searchAll(true);
      search.setSolutionListener(
          new SimpleSolutionListener<>() {
            @Override
            public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> sel) {
              int[] solution = Arrays.stream(x).mapToInt(IntVar::value).toArray();
              assertThat(isSubcircuit(solution))
                  .as(instance + " " + Arrays.toString(solution))
                  .isTrue();
              found.add(Arrays.toString(solution));
              return super.executeAfterSolution(s, sel);
            }
          });
      search.getSolutionListener().searchAll(true);
      search.labeling(store, new SimpleSelect<>(x, null, new IndomainRandom<>(run)));
      assertThat(found).as(instance).isEqualTo(expected);
    }
  }

  // a dominates b iff b cannot be reached from the root once a is removed (a != root)
  @Test
  void dominatorTreeMatchesReachability() {
    Random random = new Random(41);
    for (int run = 0; run < 500; run++) {
      int n = 1 + random.nextInt(9);
      boolean[][] arc = new boolean[n][n];
      DominatorTree tree = new DominatorTree(n);
      for (int u = 0; u < n; u++) {
        for (int v = 0; v < n; v++) {
          if (random.nextInt(4) == 0) {
            arc[u][v] = true;
            tree.addArc(u, v);
          }
        }
      }
      int root = random.nextInt(n);
      boolean allReached = reached(arc, root, -1).cardinality() == n;
      assertThat(tree.compute(root)).as("run " + run).isEqualTo(allReached);
      if (!allReached) {
        continue;
      }
      for (int a = 0; a < n; a++) {
        BitSet withoutA = a == root ? new BitSet() : reached(arc, root, a);
        for (int b = 0; b < n; b++) {
          boolean expected = a == b || !withoutA.get(b);
          assertThat(tree.dominates(a, b))
              .as("run " + run + " " + a + " dom " + b)
              .isEqualTo(expected);
        }
      }
    }
  }

  private static BitSet reached(boolean[][] arc, int root, int removed) {
    BitSet seen = new BitSet();
    if (root == removed) {
      return seen;
    }
    Deque<Integer> todo = new ArrayDeque<>();
    seen.set(root);
    todo.push(root);
    while (!todo.isEmpty()) {
      int u = todo.pop();
      for (int v = 0; v < arc.length; v++) {
        if (arc[u][v] && v != removed && !seen.get(v)) {
          seen.set(v);
          todo.push(v);
        }
      }
    }
    return seen;
  }

  @Test
  void testSeededRandomIsReproducible() {

    try {
      Store.setSeed(17);
      int[] first = IntStream.range(0, 20).map(i -> Store.getRandom().nextInt(1000)).toArray();
      Store.setSeed(17);
      int[] second = IntStream.range(0, 20).map(i -> Store.getRandom().nextInt(1000)).toArray();
      assertThat(second).containsExactly(first);

      IndomainRandom<IntVar> a = new IndomainRandom<>(5);
      IndomainRandom<IntVar> b = new IndomainRandom<>(5);
      Store store = new Store();
      IntVar v = new IntVar(store, "v", 0, 1000);
      for (int i = 0; i < 20; i++) {
        assertThat(b.indomain(v)).isEqualTo(a.indomain(v));
      }
    } finally {
      Store.resetSeed();
    }
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
  void xmulYeqZPrunesFactorWhenOtherFactorSpansZero() {
    // x * y = -11 with y in -3..2: over the reals x = -11 / y is at least 11 / 3 for y < 0 and at
    // most -5.5 for y > 0, so only x = 4 is left in -3..4; y = -11 / 4 is no integer, so it fails.
    Store store = new Store();
    IntVar x = new IntVar(store, "x", -3, 4);
    IntVar y = new IntVar(store, "y", -3, 2);
    IntVar z = new IntVar(store, "z", -11, -11);
    store.impose(new XmulYeqZ(x, y, z));
    assertThat(store.consistency()).isFalse();

    // with z = -8, x in -3..4 and y in -3..2: y < 0 gives x >= 8 / 3, y > 0 gives x <= -4
    store = new Store();
    x = new IntVar(store, "x", -3, 4);
    y = new IntVar(store, "y", -3, 2);
    z = new IntVar(store, "z", -8, -8);
    store.impose(new XmulYeqZ(x, y, z));
    assertThat(store.consistency()).isTrue();
    assertThat(x.dom().toString()).isEqualTo("4");
    assertThat(y.dom().toString()).isEqualTo("-2");
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
  void xexpYeqZKeepsNegativePowers() {
    // computeZi returned -1 to mean "no value", so every negative power such as (-2)^3 or
    // (-1)^-1 was dropped. A negative exponent truncates towards zero, as in Gecode.
    Store store = new Store();
    IntVar x = new IntVar(store, "x", -3, 3);
    IntVar y = new IntVar(store, "y", -3, 3);
    IntVar z = new IntVar(store, "z", -30, 30);
    store.impose(new XexpYeqZ(x, y, z));

    int expected = 0;
    for (int xi = -3; xi <= 3; xi++) {
      for (int yi = -3; yi <= 3; yi++) {
        if (xi != 0 || yi >= 0) {
          long zi = (long) Math.pow(xi, yi);
          if (zi >= -30 && zi <= 30) {
            expected++;
          }
        }
      }
    }
    assertThat(expected).isEqualTo(46);
    assertThat(noOfAllSolutions(store, new IntVar[] {x, y, z})).isEqualTo(expected);
  }

  @Test
  void circuitAndSubcircuitSolutionCountsMatchBruteForce() {
    Random random = new Random(5);
    for (int trial = 0; trial < 300; trial++) {
      int n = 2 + random.nextInt(5);
      int[][] domains = new int[n][];
      for (int i = 0; i < n; i++) {
        domains[i] =
            random.ints(1, n + 1).limit(1 + random.nextInt(n)).distinct().sorted().toArray();
      }
      for (boolean sub : new boolean[] {false, true}) {
        Store store = new Store();
        IntVar[] x = new IntVar[n];
        for (int i = 0; i < n; i++) {
          x[i] = new IntVar(store, "x" + i);
          for (int v : domains[i]) {
            x[i].addDom(v, v);
          }
        }
        store.impose(sub ? new Subcircuit(x) : new Circuit(x));
        int expected = circuitSolutions(domains, new int[n], 0, sub);
        int actual = store.consistency() ? noOfAllSolutions(store, x) : 0;
        assertThat(actual)
            .as("trial %d, subcircuit %b, domains %s", trial, sub, Arrays.deepToString(domains))
            .isEqualTo(expected);
      }
    }
  }

  private static int circuitSolutions(int[][] domains, int[] values, int i, boolean sub) {
    int n = values.length;
    if (i == n) {
      boolean[] seen = new boolean[n];
      int inCycle = 0;
      int start = -1;
      for (int j = 0; j < n; j++) {
        if (seen[values[j] - 1]) {
          return 0;
        }
        seen[values[j] - 1] = true;
        if (values[j] != j + 1) {
          inCycle++;
          start = j;
        }
      }
      if (!sub && inCycle < n) {
        return 0;
      }
      if (start < 0) {
        return 1;
      }
      int length = 0;
      int j = start;
      do {
        j = values[j] - 1;
        length++;
      } while (j != start);
      return length == inCycle ? 1 : 0;
    }
    int count = 0;
    for (int v : domains[i]) {
      values[i] = v;
      count += circuitSolutions(domains, values, i + 1, sub);
    }
    return count;
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
  void assignmentRejectsArraysOfDifferentLength() {
    // a shorter ds threw ArrayIndexOutOfBoundsException, a longer one NullPointerException later
    Store store = new Store();
    IntVar[] x = {new IntVar(store, 0, 2), new IntVar(store, 0, 2)};
    IntVar[] d = {new IntVar(store, 0, 1), new IntVar(store, 0, 1), new IntVar(store, 0, 1)};
    assertThatThrownBy(() -> new Assignment(x, d)).isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new Assignment(d, x)).isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void assignmentPropagatesVariablesSharedByBothArraysInBothRoles() {
    // A variable occurring in both xs and ds was only propagated as an x when its domain changed,
    // so it pruned less than the same model with a separate copy joined by XeqY.
    Random random = new Random(3);
    for (int trial = 0; trial < 400; trial++) {
      int n = 2 + random.nextInt(4);
      int[][] domains = new int[2 * n][];
      for (int i = 0; i < 2 * n; i++) {
        domains[i] =
            random.ints(0, n).limit(1 + random.nextInt(n + 1)).distinct().sorted().toArray();
      }
      int[] shared = new int[n]; // ds[j] is xs[shared[j]] when shared[j] >= 0
      for (int j = 0; j < n; j++) {
        shared[j] = random.nextInt(3) == 0 ? random.nextInt(n) : -1;
      }
      String[] result = new String[2];
      for (int copy = 0; copy < 2; copy++) {
        Store store = new Store();
        IntVar[] v = new IntVar[2 * n];
        for (int i = 0; i < 2 * n; i++) {
          v[i] = new IntVar(store, "v" + i);
          for (int value : domains[i]) {
            v[i].addDom(value, value);
          }
        }
        IntVar[] xs = Arrays.copyOfRange(v, 0, n);
        IntVar[] ds = Arrays.copyOfRange(v, n, 2 * n);
        for (int j = 0; j < n; j++) {
          if (shared[j] >= 0) {
            if (copy == 0) {
              ds[j] = xs[shared[j]];
            } else {
              ds[j] = new IntVar(store, "copy" + j, 0, n - 1);
              store.impose(new XeqY(ds[j], xs[shared[j]]));
            }
          }
        }
        store.impose(new Assignment(xs, ds));
        boolean consistent = store.consistency();
        // compare the variables that both models have: xs and the ds that are not shared
        StringBuilder domainsAfter = new StringBuilder();
        for (int i = 0; i < 2 * n; i++) {
          if (i < n || shared[i - n] < 0) {
            domainsAfter.append(v[i].dom()).append(' ');
          }
        }
        result[copy] = consistent ? domainsAfter.toString() : "fail";
      }
      if (!result[1].equals("fail")) {
        assertThat(result[0])
            .as(
                "trial %d, shared %s, domains %s",
                trial, Arrays.toString(shared), Arrays.deepToString(domains))
            .isEqualTo(result[1]);
      }
    }
  }

  @Test
  void circuitFailsWhenGraphIsNotStronglyConnected() {
    // No successor domain contains 1 (first graph), or nodes 3..6 never lead back to 1 or 2
    // (second graph), so no Hamiltonian circuit exists. The SCC check only failed when the DFS
    // from node 1 had not yet visited all nodes at the moment it closed a component; here the
    // component without node 1 is closed after all nodes have been visited.
    int[][][] graphs = {
      {{2, 3}, {3, 4, 5}, {2, 4, 5}, {2, 3, 5}, {2, 3, 4}},
      {{2}, {1, 3}, {4, 5, 6}, {3, 5, 6}, {3, 4, 6}, {3, 4, 5}}
    };
    for (int[][] graph : graphs) {
      assertThat(circuitSolutions(graph, new int[graph.length], 0, false)).isZero();
      Store store = new Store();
      IntVar[] x = new IntVar[graph.length];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + (i + 1));
        for (int v : graph[i]) {
          x[i].addDom(v, v);
        }
      }
      store.impose(new Circuit(x));
      assertThat(store.consistency()).as(Arrays.deepToString(graph)).isFalse();
    }
  }

  @Test
  void circuitOnLargeGraphDoesNotOverflowTheStack() throws InterruptedException {
    // The SCC check was a recursive DFS, one Java frame per node, and threw StackOverflowError
    // for circuits of a few ten thousand nodes with the default thread stack. Every node i may go
    // to i - 1 or i + 1 (cyclic). Run on a thread with a 512 KB stack, since tests use -Xss100m.
    int n = 100_000;
    boolean[] result = new boolean[1];
    Throwable[] error = new Throwable[1];
    Thread thread =
        new Thread(
            null,
            () -> {
              try {
                Store store = new Store();
                IntVar[] x = new IntVar[n];
                for (int i = 0; i < n; i++) {
                  x[i] = new IntVar(store, "x" + i);
                  x[i].addDom((i + 1) % n + 1, (i + 1) % n + 1);
                  x[i].addDom((i + n - 1) % n + 1, (i + n - 1) % n + 1);
                }
                store.impose(new Circuit(x));
                result[0] = store.consistency();
              } catch (Throwable t) {
                error[0] = t;
              }
            },
            "small-stack",
            512 * 1024);
    thread.start();
    thread.join();
    assertThat(error[0]).isNull();
    assertThat(result[0]).isTrue();
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

  // Alldistinct must keep exactly the values that appear in some solution (domain consistency)
  // after every propagation of a dive, also when several domains change between two calls, after
  // backtracking (the matching is reused), and for dense, interval and sparse value sets.
  @Test
  void testAlldistinctIsDomainConsistentAcrossBacktracking() {

    Random random = new Random(23);
    Predicate<int[]> distinct = a -> Arrays.stream(a).distinct().count() == a.length;
    for (int trial = 0; trial < 2000; trial++) {
      int n = 1 + random.nextInt(6);
      int m = n + random.nextInt(3);
      int kind = trial % 3;
      // kind 0: SmallDenseDomain, 1: IntervalDomain, 2: IntervalDomain with sparse values
      int[] base = IntStream.range(0, m).map(k -> kind == 2 ? 100_000 * k - 7 : k - 2).toArray();

      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        IntDomain dom = kind == 0 ? new SmallDenseDomain() : new IntervalDomain();
        for (int k = 0; k < m; k++) {
          if (random.nextInt(3) > 0) {
            dom.unionAdapt(base[k], base[k]);
          }
        }
        if (dom.isEmpty()) {
          int k = random.nextInt(m);
          dom.unionAdapt(base[k], base[k]);
        }
        x[i] = new IntVar(store, "x" + i, dom);
      }
      String instance = "trial " + trial + " " + Arrays.toString(x);
      store.impose(new Alldistinct(x));

      // imposition raises the level before the first propagation
      Map<Integer, String> domainsAtLevel = new HashMap<>();
      boolean consistent = store.consistency();
      assertRegularDomainConsistent(x, distinct, consistent, instance);
      while (consistent) {
        domainsAtLevel.put(store.level, Arrays.toString(x));
        List<IntVar> free = Arrays.stream(x).filter(v -> !v.singleton()).toList();
        if (free.isEmpty()) {
          break;
        }
        store.setLevel(store.level + 1);
        for (int change = 1 + random.nextInt(2); change > 0; change--) {
          IntVar v = free.get(random.nextInt(free.size()));
          if (v.singleton()) {
            continue;
          }
          int[] values = valuesOf(v);
          int value = values[random.nextInt(values.length)];
          if (random.nextInt(3) == 0) {
            v.domain.in(store.level, v, value, value);
          } else {
            v.domain.inComplement(store.level, v, value);
          }
        }
        consistent = store.consistency();
        assertRegularDomainConsistent(x, distinct, consistent, instance);
      }
      while (store.level > 0) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
        if (domainsAtLevel.containsKey(store.level)) {
          assertThat(Arrays.toString(x)).as(instance).isEqualTo(domainsAtLevel.get(store.level));
        }
        List<IntVar> free = Arrays.stream(x).filter(v -> !v.singleton()).toList();
        if (!free.isEmpty() && random.nextBoolean()) {
          IntVar v = free.get(random.nextInt(free.size()));
          store.setLevel(store.level + 1);
          v.domain.in(store.level, v, v.max(), v.max());
          assertRegularDomainConsistent(x, distinct, store.consistency(), instance);
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
          if (domainsAtLevel.containsKey(store.level)) {
            assertThat(Arrays.toString(x)).as(instance).isEqualTo(domainsAtLevel.get(store.level));
          }
        }
      }
    }
  }

  // Alldiff must be bounds(Z) consistent: after propagation the minimum and the maximum of every
  // variable take part in an all different assignment where every variable ranges over the interval
  // between its bounds. It must also never remove a solution, along random dives and after
  // backtracking.
  @Test
  void testAlldiffIsBoundsConsistentAcrossBacktracking() {

    Random random = new Random(29);
    for (int trial = 0; trial < 2000; trial++) {
      int n = 1 + random.nextInt(6);
      int m = n + random.nextInt(3);
      boolean dense = trial % 2 == 0;

      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        IntDomain dom = dense ? new SmallDenseDomain() : new IntervalDomain();
        for (int k = 0; k < m; k++) {
          if (random.nextInt(3) > 0) {
            dom.unionAdapt(k, k);
          }
        }
        if (dom.isEmpty()) {
          int k = random.nextInt(m);
          dom.unionAdapt(k, k);
        }
        x[i] = new IntVar(store, "x" + i, dom);
      }
      String instance = "trial " + trial + " " + Arrays.toString(x);
      store.impose(new Alldiff(x));

      List<int[]> solutions = bruteForce(x, SingleConstraintTest::allDifferent);
      boolean consistent = store.consistency();
      assertAlldiffBoundsConsistent(x, solutions, consistent, instance);
      while (consistent) {
        List<IntVar> free = Arrays.stream(x).filter(v -> !v.singleton()).toList();
        if (free.isEmpty()) {
          break;
        }
        store.setLevel(store.level + 1);
        for (int change = 1 + random.nextInt(2); change > 0; change--) {
          IntVar v = free.get(random.nextInt(free.size()));
          if (v.singleton()) {
            continue;
          }
          int[] values = valuesOf(v);
          int value = values[random.nextInt(values.length)];
          if (random.nextInt(3) == 0) {
            v.domain.in(store.level, v, value, value);
          } else {
            v.domain.inComplement(store.level, v, value);
          }
        }
        solutions = bruteForce(x, SingleConstraintTest::allDifferent);
        consistent = store.consistency();
        assertAlldiffBoundsConsistent(x, solutions, consistent, instance);
      }
      while (store.level > 0) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
        List<IntVar> free = Arrays.stream(x).filter(v -> !v.singleton()).toList();
        if (!free.isEmpty() && random.nextBoolean()) {
          IntVar v = free.get(random.nextInt(free.size()));
          store.setLevel(store.level + 1);
          v.domain.in(store.level, v, v.max(), v.max());
          solutions = bruteForce(x, SingleConstraintTest::allDifferent);
          assertAlldiffBoundsConsistent(x, solutions, store.consistency(), instance);
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
        }
      }
    }
  }

  private static boolean allDifferent(int[] a) {
    return Arrays.stream(a).distinct().count() == a.length;
  }

  private static void assertAlldiffBoundsConsistent(
      IntVar[] x, List<int[]> solutionsBefore, boolean consistent, String instance) {
    String state = instance + " " + Arrays.toString(x);
    if (!consistent) {
      assertThat(solutionsBefore).as(state + " failed with solutions").isEmpty();
      return;
    }
    for (int[] solution : solutionsBefore) {
      for (int i = 0; i < x.length; i++) {
        assertThat(x[i].domain.contains(solution[i]))
            .as(state + " keeps solution " + Arrays.toString(solution))
            .isTrue();
      }
    }
    IntVar[] relaxed = new IntVar[x.length];
    Store relaxedStore = new Store();
    for (int i = 0; i < x.length; i++) {
      relaxed[i] = new IntVar(relaxedStore, x[i].min(), x[i].max());
    }
    List<int[]> relaxedSolutions = bruteForce(relaxed, SingleConstraintTest::allDifferent);
    for (int i = 0; i < x.length; i++) {
      int position = i;
      assertThat(relaxedSolutions.stream().anyMatch(w -> w[position] == x[position].min()))
          .as(state + " min of x" + i + " supported")
          .isTrue();
      assertThat(relaxedSolutions.stream().anyMatch(w -> w[position] == x[position].max()))
          .as(state + " max of x" + i + " supported")
          .isTrue();
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

  // LinearBool keeps the bounds of the sum in time stamps updated when a 0/1 variable is fixed, so
  // counting all solutions by search checks that the sums are restored on backtracking; repeated
  // variables, variables fixed before imposing and both kinds of right hand side are covered.
  @Test
  void testLinearBoolCountsMatchBruteForce() {

    Random random = new Random(41);
    String[] relations = {"==", "<=", ">="};
    for (int trial = 0; trial < 1500; trial++) {
      Store store = new Store();
      int n = 3 + random.nextInt(5);
      IntVar[] distinct = new IntVar[n];
      for (int i = 0; i < n; i++) {
        distinct[i] =
            random.nextBoolean()
                ? new BooleanVar(store, "b" + i)
                : new IntVar(store, "b" + i, 0, 1);
        if (random.nextInt(6) == 0) {
          distinct[i].domain.in(store.level, distinct[i], random.nextInt(2), 1);
        }
      }
      // a few positions repeat an earlier variable, so that the weights are merged
      int m = n + random.nextInt(3);
      IntVar[] b = new IntVar[m];
      int[] w = new int[m];
      for (int i = 0; i < m; i++) {
        b[i] = i < n ? distinct[i] : distinct[random.nextInt(n)];
        w[i] = (1 + random.nextInt(6)) * (random.nextBoolean() ? 1 : -1);
      }
      String rel = relations[random.nextInt(relations.length)];
      boolean constant = random.nextBoolean();
      int c = random.nextInt(15) - 7;
      IntVar z = new IntVar(store, "z");
      for (int v = -10; v <= 14; v++) {
        if (random.nextInt(3) > 0) {
          z.addDom(v, v);
        }
      }
      if (z.getSize() == 0) {
        z.addDom(0, 0);
      }
      IntVar[] all =
          constant
              ? distinct
              : Stream.concat(Arrays.stream(distinct), Stream.of(z)).toArray(IntVar[]::new);
      Predicate<int[]> holds =
          a -> {
            long sum = 0;
            for (int i = 0; i < m; i++) {
              sum += (long) w[i] * a[Arrays.asList(distinct).indexOf(b[i])];
            }
            long rhs = constant ? c : a[n];
            return switch (rel) {
              case "==" -> sum == rhs;
              case "<=" -> sum <= rhs;
              default -> sum >= rhs;
            };
          };
      int expected = bruteForce(all, holds).size();

      store.impose(constant ? new LinearBool(b, w, rel, c) : new LinearBool(b, w, rel, z));
      List<IntVar> order = new ArrayList<>(Arrays.asList(all));
      Collections.shuffle(order, random);
      assertThat(countSolutions(store, order.toArray(new IntVar[0]), random))
          .as("trial %d: %s %s %s", trial, Arrays.toString(w), rel, constant ? c : z)
          .isEqualTo(expected);
    }
  }

  @Test
  void testLinearBoolRejectsInvalidArguments() {

    Store store = new Store();
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar x = new IntVar(store, "x", 0, 2);
    assertThatThrownBy(() -> new LinearBool(new IntVar[] {b, x}, new int[] {1, 1}, "==", 1))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new LinearBool(new IntVar[] {b}, new int[] {1}, "==", b))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new LinearBool(new IntVar[] {b}, new int[] {1}, "!=", 0))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new LinearBool(new IntVar[] {b}, new int[] {1, 2}, "==", 0))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testXplusCneqZCountsMatchBruteForce() {

    Random random = new Random(43);
    for (int trial = 0; trial < 1000; trial++) {
      Store store = new Store();
      IntVar x = randomVar(store, "x", -4, 4, random);
      IntVar z = randomVar(store, "z", -4, 4, random);
      int c = random.nextInt(9) - 4;
      IntVar[] all = {x, z};
      int expected = bruteForce(all, a -> a[0] + c != a[1]).size();

      store.impose(new XplusCneqZ(x, c, z));
      assertThat(countSolutions(store, random.nextBoolean() ? all : new IntVar[] {z, x}, random))
          .as("trial %d: %s + %d != %s", trial, x, c, z)
          .isEqualTo(expected);
    }
  }

  @Test
  void testXplusCneqZOnTheSameVariable() {

    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    store.impose(new XplusCneqZ(x, 2, x));
    assertThat(store.consistency()).isTrue();
    assertThat(x.getSize()).isEqualTo(4);
    assertThatThrownBy(() -> store.impose(new XplusCneqZ(x, 0, x)))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testXplusClteqZImpliedCountsMatchBruteForce() {

    Random random = new Random(47);
    for (int trial = 0; trial < 1000; trial++) {
      Store store = new Store();
      IntVar b = random.nextBoolean() ? new BooleanVar(store, "b") : new IntVar(store, "b", 0, 1);
      IntVar x = randomVar(store, "x", -4, 4, random);
      IntVar z = randomVar(store, "z", -4, 4, random);
      int c = random.nextInt(9) - 4;
      IntVar[] all = {b, x, z};
      int expected = bruteForce(all, a -> a[0] == 0 || a[1] + c <= a[2]).size();

      store.impose(new XplusClteqZImplied(b, x, c, z));
      List<IntVar> order = new ArrayList<>(Arrays.asList(all));
      Collections.shuffle(order, random);
      assertThat(countSolutions(store, order.toArray(new IntVar[0]), random))
          .as("trial %d: %s => %s + %d <= %s", trial, b, x, c, z)
          .isEqualTo(expected);
    }
  }

  // An entailed constraint is only marked during search: it is not woken and not counted by
  // sizeConstraints until the store backtracks below the level of the mark, when it propagates
  // again. At the root it is still detached from its variables.
  @Test
  void testEntailedConstraintIsSkippedUntilBacktrack() {

    Store store = new Store();
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar x = new IntVar(store, "x", 0, 10);
    IntVar y = new IntVar(store, "y", 0, 10);
    XplusClteqZImplied c = new XplusClteqZImplied(b, x, 0, y);
    store.impose(c);
    assertThat(store.consistency()).isTrue();
    int attached = x.sizeConstraints();

    store.setLevel(1);
    b.domain.in(store.level, b, 0, 0);
    assertThat(store.consistency()).isTrue();
    assertThat(c.isEntailed()).isTrue();
    assertThat(x.sizeConstraints()).isEqualTo(attached - 1);
    assertThat(x.dom().constraints()).doesNotContain(c);

    store.setLevel(2);
    x.domain.in(store.level, x, 6, 10);
    assertThat(store.changed[c.getQueueIndex()].contains(c)).isFalse();
    assertThat(store.consistency()).isTrue();
    store.removeLevel(2);
    store.setLevel(1);
    store.removeLevel(1);
    store.setLevel(0);

    assertThat(c.isEntailed()).isFalse();
    assertThat(x.sizeConstraints()).isEqualTo(attached);
    store.setLevel(1);
    b.domain.in(store.level, b, 1, 1);
    x.domain.in(store.level, x, 6, 10);
    assertThat(store.consistency()).isTrue();
    assertThat(y.min()).isEqualTo(6);
    store.removeLevel(1);
    store.setLevel(0);

    b.domain.in(store.level, b, 0, 0);
    assertThat(store.consistency()).isTrue();
    assertThat(c.isEntailed()).isFalse();
    assertThat(x.sizeConstraints()).isEqualTo(attached - 1);
  }

  // A constraint that reads one bound of a variable is attached with the MIN_EVENT or MAX_EVENT
  // event and is
  // not woken when only the other bound changes.
  @Test
  void testBoundConstraintIsWokenOnlyByTheBoundItReads() {

    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 10);
    IntVar z = new IntVar(store, "z", 0, 10);
    XplusClteqZ c = new XplusClteqZ(x, 2, z);
    store.impose(c);
    assertThat(store.consistency()).isTrue();
    assertThat(x.dom().modelConstraints[IntDomain.MIN_EVENT]).contains(c);
    assertThat(z.dom().modelConstraints[IntDomain.MAX_EVENT]).contains(c);

    store.setLevel(1);
    x.domain.inMax(store.level, x, 7);
    z.domain.inMin(store.level, z, 3);
    assertThat(store.changed[c.getQueueIndex()].contains(c)).isFalse();
    x.domain.inMin(store.level, x, 2);
    assertThat(store.changed[c.getQueueIndex()].contains(c)).isTrue();
    assertThat(store.consistency()).isTrue();
    assertThat(z.min()).isEqualTo(4);
    z.domain.inMax(store.level, z, 6);
    assertThat(store.consistency()).isTrue();
    assertThat(x.max()).isEqualTo(4);

    // with the same variable on both sides, or an event set by the user, both bounds are watched
    XlteqY same = new XlteqY(x, x);
    assertThat(same.getBoundPruningEvent(x)).isEqualTo(IntDomain.BOUND);
    XplusClteqZ set = new XplusClteqZ(x, 1, z);
    set.setConsistencyPruningEvent(x, IntDomain.BOUND);
    store.impose(set);
    assertThat(x.dom().modelConstraints[IntDomain.BOUND]).contains(set);
  }

  // Constraints attached with MIN_EVENT or MAX_EVENT keep every solution and reach a fixpoint after
  // any
  // decision, including decisions that change only one bound.
  @Test
  void testBoundSideConstraintsKeepSupportsAndReachFixpoint() {

    record Case(
        String name, int arity, Function<IntVar[], Constraint> constraint, Predicate<int[]> test) {}

    List<Case> cases =
        List.of(
            new Case("x <= y", 2, v -> new XlteqY(v[0], v[1]), t -> t[0] <= t[1]),
            new Case("x < y", 2, v -> new XltY(v[0], v[1]), t -> t[0] < t[1]),
            new Case("x >= y", 2, v -> new XgteqY(v[0], v[1]), t -> t[0] >= t[1]),
            new Case("x > y", 2, v -> new XgtY(v[0], v[1]), t -> t[0] > t[1]),
            new Case("x + 2 <= z", 2, v -> new XplusClteqZ(v[0], 2, v[1]), t -> t[0] + 2 <= t[1]),
            new Case(
                "x + y <= z", 3, v -> new XplusYlteqZ(v[0], v[1], v[2]), t -> t[0] + t[1] <= t[2]),
            new Case(
                "b => x - 1 <= z",
                3,
                v -> new XplusClteqZImplied(v[0], v[1], -1, v[2]),
                t -> t[0] == 0 || t[1] - 1 <= t[2]),
            new Case(
                "2x - 3y + z <= 4",
                3,
                v -> new LinearInt(v, new int[] {2, -3, 1}, "<=", 4),
                t -> 2 * t[0] - 3 * t[1] + t[2] <= 4),
            new Case(
                "2x - 3y + z < 4",
                3,
                v -> new LinearInt(v, new int[] {2, -3, 1}, "<", 4),
                t -> 2 * t[0] - 3 * t[1] + t[2] < 4),
            new Case(
                "x - 2y + 3z >= 5",
                3,
                v -> new LinearInt(v, new int[] {1, -2, 3}, ">=", 5),
                t -> t[0] - 2 * t[1] + 3 * t[2] >= 5),
            new Case(
                "x - 2y + 3z > 5",
                3,
                v -> new LinearInt(v, new int[] {1, -2, 3}, ">", 5),
                t -> t[0] - 2 * t[1] + 3 * t[2] > 5),
            new Case(
                "x + y <= z (sum)",
                3,
                v -> new SumInt(new IntVar[] {v[0], v[1]}, "<=", v[2]),
                t -> t[0] + t[1] <= t[2]),
            new Case(
                "x + y > z (sum)",
                3,
                v -> new SumInt(new IntVar[] {v[0], v[1]}, ">", v[2]),
                t -> t[0] + t[1] > t[2]));

    Random random = new Random(53);
    for (Case c : cases) {
      for (int run = 0; run < 300; run++) {
        Store store = new Store();
        IntVar[] vars = new IntVar[c.arity()];
        for (int i = 0; i < vars.length; i++) {
          vars[i] =
              c.name().startsWith("b ") && i == 0
                  ? new IntVar(store, "b", 0, 1)
                  : randomVar(store, "v" + i, -3, 6, random);
        }
        Constraint constraint = c.constraint().apply(vars);
        store.impose(constraint);
        String instance = c.name() + " run " + run + " " + domainsOf(vars);
        checkSupportsAndFixpoint(
            instance,
            store,
            vars,
            v -> bruteForce(v, c.test()),
            () -> rerunAtNewLevel(store, constraint, vars),
            random,
            true);
      }
    }
  }

  private static void decideOnBound(Store store, IntVar v, int value, Random random) {
    switch (random.nextInt(4)) {
      case 0 -> v.domain.inMin(store.level, v, value);
      case 1 -> v.domain.inMax(store.level, v, value);
      case 2 -> v.domain.inComplement(store.level, v, value);
      default -> v.domain.inComplement(store.level, v, random.nextBoolean() ? v.min() : v.max());
    }
  }

  private static IntVar randomVar(Store store, String name, int lo, int hi, Random random) {
    IntVar v = new IntVar(store, name);
    for (int k = lo; k <= hi; k++) {
      if (random.nextInt(4) > 0) {
        v.addDom(k, k);
      }
    }
    if (v.getSize() == 0) {
      v.addDom(lo, lo);
    }
    return v;
  }

  private static int countSolutions(Store store, IntVar[] vars, Random random) {
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    boolean found =
        search.labeling(
            store, new SimpleSelect<>(vars, null, new IndomainRandom<>(random.nextInt())));
    return found ? search.getSolutionListener().solutionsNo() : 0;
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
    checkSupportsAndFixpoint(instance, store, vars, solver, rerun, random, false);
  }

  /**
   * Checks supports and fixpoint along a random walk. With bound decisions, the decisions also move
   * a single bound, so that a constraint that misses the event of the bound it reads leaves values
   * it should prune.
   */
  private static void checkSupportsAndFixpoint(
      String instance,
      Store store,
      IntVar[] vars,
      Function<IntVar[], List<int[]>> solver,
      Supplier<String> rerun,
      Random random,
      boolean boundDecisions) {
    List<int[]> solutions = solver.apply(vars);
    for (int step = 0; step < (boundDecisions ? 8 : 6); step++) {
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
      if (boundDecisions) {
        decideOnBound(store, v, value, random);
      } else if (random.nextBoolean()) {
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
        new Knapsack(profits, weights, Arrays.copyOf(copies, n), copies[n], copies[n + 1])
            .dynamicProgramming(false));
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
                profits, weights, Arrays.copyOf(vars, weights.length), vars[weights.length], profit)
            .dynamicProgramming(false));
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
      store.impose(
          new Knapsack(profits, weights, Arrays.copyOf(vars, n), vars[n], vars[n + 1])
              .dynamicProgramming(false));
      checkSupportsAndFixpointAlongRandomWalk(
          instance,
          store,
          vars,
          vs -> knapsackSolutions(profits, weights, vs),
          () -> knapsackOnCopies(profits, weights, vars),
          random);
    }
  }

  /**
   * Imposes Knapsack on quantities in lo..hi, capacity in capacityMin..capacityMax and profit in
   * profitMin..profitMax, and checks that propagation keeps every solution.
   */
  private static void assertKnapsackKeepsAllSolutions(
      int[] weights,
      int[] profits,
      int[] lo,
      int[] hi,
      int capacityMin,
      int capacityMax,
      int profitMin,
      int profitMax) {
    int n = weights.length;
    Store store = new Store();
    IntVar[] vars = new IntVar[n + 2];
    for (int i = 0; i < n; i++) {
      vars[i] = new IntVar(store, "q" + i, lo[i], hi[i]);
    }
    vars[n] = new IntVar(store, "capacity", capacityMin, capacityMax);
    vars[n + 1] = new IntVar(store, "profit", profitMin, profitMax);
    List<int[]> solutions = knapsackSolutions(profits, weights, vars);
    assertThat(solutions).isNotEmpty();
    store.impose(new Knapsack(profits, weights, Arrays.copyOf(vars, n), vars[n], vars[n + 1]));
    assertThat(store.consistency()).as(domainsOf(vars)).isTrue();
    for (int[] solution : solutions) {
      for (int i = 0; i < vars.length; i++) {
        assertThat(vars[i].domain.contains(solution[i]))
            .as(domainsOf(vars) + " keeps solution " + Arrays.toString(solution))
            .isTrue();
      }
    }
  }

  @Test
  void knapsackKeepsSolutionsWithEquallyEfficientItems() {
    // The search for the weight replaceable by less efficient items stopped at a leaf reached by
    // descending the tree without checking its neighbor, and divided by a zero efficiency loss when
    // the next item was as efficient. Item 0 was wrongly made mandatory.
    int[] ones = {1, 1, 1, 1, 1, 1, 1, 1, 1, 1};
    assertKnapsackKeepsAllSolutions(
        new int[] {3, 2, 2, 1, 3, 1, 3, 3, 2, 1},
        new int[] {6, 2, 4, 2, 6, 2, 6, 3, 2, 2},
        new int[10],
        ones,
        11,
        11,
        22,
        36);
    // An already fixed item between two equally efficient items hid the second one.
    assertKnapsackKeepsAllSolutions(
        new int[] {3, 2, 5, 5, 1, 1, 1},
        new int[] {6, 2, 5, 10, 2, 2, 2},
        new int[] {0, 1, 0, 0, 0, 0, 0},
        new int[] {1, 1, 1, 1, 1, 0, 1},
        0,
        7,
        12,
        26);
    // The constraint failed although x8 = x9 = x10 = 1 plus any other item is a solution.
    assertKnapsackKeepsAllSolutions(
        new int[] {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1},
        new int[] {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1},
        new int[] {0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0},
        new int[] {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1},
        2,
        5,
        6,
        7);
  }

  @Test
  void knapsackHandlesLargeQuantitiesWithoutOverflow() {
    // Sums of weights and profits were kept in int and overflowed, so the constraint failed.
    Store store = new Store();
    IntVar[] q = {
      new IntVar(store, "q0", 0, IntDomain.MAX_INT), new IntVar(store, "q1", 0, IntDomain.MAX_INT)
    };
    IntVar capacity = new IntVar(store, "capacity", 0, 100);
    IntVar profit = new IntVar(store, "profit", 0, IntDomain.MAX_INT);
    store.impose(new Knapsack(new int[] {3, 4}, new int[] {5, 7}, q, capacity, profit));
    assertThat(store.consistency()).isTrue();
    assertThat(q[0].max()).isEqualTo(20);
    assertThat(q[1].max()).isEqualTo(14);

    store = new Store();
    q = new IntVar[3];
    for (int i = 0; i < q.length; i++) {
      q[i] = new IntVar(store, "q" + i, 100, 100);
    }
    capacity = new IntVar(store, "capacity", 0, 500_000_000);
    profit = new IntVar(store, "profit", 0, 500_000_000);
    int[] large = {1_000_000, 1_000_000, 1_000_000};
    store.impose(new Knapsack(large, large, q, capacity, profit));
    assertThat(store.consistency()).isTrue();
    assertThat(capacity.value()).isEqualTo(300_000_000);
    assertThat(profit.value()).isEqualTo(300_000_000);
  }

  @Test
  void knapsackUpdatesItemsChangedAfterBacktrack() {
    // The position up to which the changed items of a level were applied to the tree was shared
    // by all levels. After backtracking from a level with more changes, items changed again at the
    // lower level were skipped, so the tree kept their old minimal quantities.
    // Sixteen items, so that a few changes are applied incrementally instead of by recomputing.
    Store store = new Store();
    IntVar[] q = new IntVar[16];
    int[] weights = new int[q.length];
    int[] profits = new int[q.length];
    for (int i = 0; i < q.length; i++) {
      q[i] = new IntVar(store, "q" + i, 0, 2);
      weights[i] = i + 1;
      profits[i] = q.length - i;
    }
    IntVar capacity = new IntVar(store, "capacity", 0, 1000);
    IntVar profit = new IntVar(store, "profit", 0, 1000);
    store.impose(new Knapsack(profits, weights, q, capacity, profit));
    assertThat(store.consistency()).isTrue();

    store.setLevel(1);
    q[0].domain.in(store.level, q[0], 1, 2);
    assertThat(store.consistency()).isTrue();

    store.setLevel(2);
    for (int i = 1; i < 4; i++) {
      q[i].domain.in(store.level, q[i], 1, 2);
    }
    assertThat(store.consistency()).isTrue();
    store.removeLevel(2);
    store.setLevel(1);

    q[1].domain.in(store.level, q[1], 2, 2);
    q[2].domain.in(store.level, q[2], 2, 2);
    assertThat(store.consistency()).isTrue();
    assertThat(capacity.min()).isEqualTo(1 + 2 * 2 + 2 * 3);
    assertThat(profit.min()).isEqualTo(16 + 2 * 15 + 2 * 14);
  }

  @Test
  void knapsackSortsManyEquallyEfficientItems() {
    // The item comparator returned 1 for two items with the same weight and profit in both
    // directions, so sorting 32 or more items threw "Comparison method violates its general
    // contract".
    int[] profits = {
      3, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1
    };
    int[] weights = new int[profits.length];
    Arrays.fill(weights, 1);
    Store store = new Store();
    IntVar[] q = new IntVar[profits.length];
    for (int i = 0; i < q.length; i++) {
      q[i] = new IntVar(store, "q" + i, 0, 1);
    }
    IntVar capacity = new IntVar(store, "capacity", 0, 22);
    IntVar profit = new IntVar(store, "profit", 0, 43);
    store.impose(new Knapsack(profits, weights, q, capacity, profit));
    assertThat(store.consistency()).isTrue();
    // The 22 most profitable items give 2 * 3 + 7 * 2 + 13 * 1 = 33.
    assertThat(profit.max()).isEqualTo(33);
  }

  /**
   * The maximal profit of the linear relaxation (Dantzig bound) when item skip is left out, the
   * other quantities lie in their bounds and the weight is at most capacity; minus infinity if the
   * minimal quantities exceed the capacity.
   */
  private static double knapsackRelaxation(
      int[] weights, int[] profits, IntVar[] vars, int skip, double capacity) {
    double profit = 0;
    List<Integer> order = new ArrayList<>();
    for (int i = 0; i < weights.length; i++) {
      if (i != skip) {
        capacity -= (double) vars[i].min() * weights[i];
        profit += (double) vars[i].min() * profits[i];
        order.add(i);
      }
    }
    if (capacity < -1e-9) {
      return Double.NEGATIVE_INFINITY;
    }
    order.sort(
        (a, b) -> Long.compare((long) profits[b] * weights[a], (long) profits[a] * weights[b]));
    for (int i : order) {
      double take = Math.min(vars[i].max() - vars[i].min(), capacity / weights[i]);
      profit += take * profits[i];
      capacity -= take * weights[i];
    }
    return profit;
  }

  @Test
  void knapsackReachesRelaxationConsistencyAndDominatesLinearDecomposition() {
    // Every bound of a quantity must have a support in the linear relaxation (capacity at most its
    // maximum, profit at least its minimum), as in Fahle and Sellmann or Katriel et al., including
    // the critical item. The pruning must also include what the two linear equalities give.
    Random random = new Random(7);
    for (int run = 0; run < 3000; run++) {
      int n = 1 + random.nextInt(8);
      int[] weights = new int[n];
      int[] profits = new int[n];
      Store store = new Store();
      IntVar[] vars = new IntVar[n + 2];
      int weightSum = 0;
      int profitSum = 0;
      for (int i = 0; i < n; i++) {
        weights[i] = 1 + random.nextInt(10);
        profits[i] = random.nextBoolean() ? weights[i] : 1 + random.nextInt(10);
        int min = random.nextInt(4) == 0 ? 1 : 0;
        int max = min + random.nextInt(3);
        vars[i] = new IntVar(store, "q" + i, min, max);
        weightSum += weights[i] * max;
        profitSum += profits[i] * max;
      }
      int capacityMin = random.nextInt(weightSum / 3 + 1);
      int capacityMax = Math.max(capacityMin, random.nextInt(weightSum + 1));
      int profitMin = random.nextInt(profitSum + 1);
      vars[n] = new IntVar(store, "capacity", capacityMin, capacityMax);
      vars[n + 1] =
          new IntVar(store, "profit", profitMin, profitMin + random.nextInt(profitSum + 2));
      String instance =
          "run "
              + run
              + " weights "
              + Arrays.toString(weights)
              + " profits "
              + Arrays.toString(profits)
              + " "
              + domainsOf(vars);
      store.impose(
          new Knapsack(profits, weights, Arrays.copyOf(vars, n), vars[n], vars[n + 1])
              .dynamicProgramming(false));
      if (!store.consistency()) {
        continue;
      }
      String state = instance + " -> " + domainsOf(vars);
      for (int i = 0; i < n; i++) {
        for (int bound : new int[] {vars[i].min(), vars[i].max()}) {
          double best =
              (double) bound * profits[i]
                  + knapsackRelaxation(
                      weights, profits, vars, i, vars[n].max() - (double) bound * weights[i]);
          assertThat(best)
              .as(state + " q" + i + " = " + bound)
              .isGreaterThan(vars[n + 1].min() - 1e-6);
        }
      }
      Store linearStore = new Store();
      IntVar[] copies = new IntVar[n + 2];
      for (int i = 0; i < copies.length; i++) {
        copies[i] = new IntVar(linearStore, vars[i].id(), vars[i].dom().cloneLight());
      }
      IntVar[] weighted = Arrays.copyOf(copies, n + 1);
      int[] coefficients = Arrays.copyOf(weights, n + 1);
      coefficients[n] = -1;
      linearStore.impose(new LinearInt(weighted, coefficients, "==", 0));
      weighted = weighted.clone();
      weighted[n] = copies[n + 1];
      coefficients = Arrays.copyOf(profits, n + 1);
      coefficients[n] = -1;
      linearStore.impose(new LinearInt(weighted, coefficients, "==", 0));
      assertThat(linearStore.consistency()).as(state).isTrue();
      assertThat(domainsOf(copies)).as(state).isEqualTo(domainsOf(vars));
    }
  }

  @Test
  void knapsackDpReachesDomainConsistency() {
    // With a maximal profit that does not restrict, the dynamic program keeps exactly the values of
    // the quantities and of the capacity that belong to a solution, and the exact profit bounds.
    Random random = new Random(11);
    for (int run = 0; run < 1500; run++) {
      int n = 1 + random.nextInt(6);
      int[] weights = new int[n];
      int[] profits = new int[n];
      Store store = new Store();
      IntVar[] vars = new IntVar[n + 2];
      int weightSum = 0;
      int profitSum = 0;
      for (int i = 0; i < n; i++) {
        weights[i] = 1 + random.nextInt(8);
        profits[i] = random.nextInt(9);
        vars[i] = randomSubsetVar(store, "q" + i, random.nextInt(2), 3, random);
        weightSum += weights[i] * vars[i].max();
        profitSum += profits[i] * vars[i].max();
      }
      vars[n] = randomSubsetVar(store, "capacity", 0, weightSum, random);
      vars[n + 1] = new IntVar(store, "profit", random.nextInt(profitSum + 1), profitSum);
      String instance =
          "run "
              + run
              + " weights "
              + Arrays.toString(weights)
              + " profits "
              + Arrays.toString(profits)
              + " "
              + domainsOf(vars);
      List<int[]> solutions = knapsackSolutions(profits, weights, vars);
      store.impose(
          new KnapsackDP(profits, weights, Arrays.copyOf(vars, n), vars[n], vars[n + 1])
              .adaptive(false));
      boolean consistent = store.consistency();
      assertThat(consistent).as(instance).isEqualTo(!solutions.isEmpty());
      if (!consistent) {
        continue;
      }
      for (int i = 0; i <= n; i++) {
        int k = i;
        int[] supported = solutions.stream().mapToInt(a -> a[k]).distinct().sorted().toArray();
        assertThat(valuesOf(vars[i]))
            .as(instance + " " + domainsOf(vars))
            .containsExactly(supported);
      }
      int profitMin = solutions.stream().mapToInt(a -> a[n + 1]).min().getAsInt();
      int profitMax = solutions.stream().mapToInt(a -> a[n + 1]).max().getAsInt();
      assertThat(vars[n + 1].max()).as(instance).isEqualTo(profitMax);
      assertThat(vars[n + 1].min()).as(instance).isLessThanOrEqualTo(profitMin);
    }
  }

  @Test
  void knapsackDpKeepsSupportsAndReachesFixpoint() {
    Random random = new Random(13);
    for (int run = 0; run < 1500; run++) {
      Store store = new Store();
      int n = 2 + random.nextInt(4);
      int[] weights = new int[n];
      int[] profits = new int[n];
      IntVar[] vars = new IntVar[n + 2];
      int weightSum = 0;
      int profitSum = 0;
      for (int i = 0; i < n; i++) {
        weights[i] = random.nextInt(10);
        profits[i] = random.nextInt(12);
        vars[i] = randomSubsetVar(store, "q" + i, 0, 1 + random.nextInt(3), random);
        weightSum += weights[i] * vars[i].max();
        profitSum += profits[i] * vars[i].max();
      }
      vars[n] = randomSubsetVar(store, "capacity", 0, weightSum, random);
      vars[n + 1] = randomSubsetVar(store, "profit", 0, profitSum, random);
      String instance =
          "run "
              + run
              + " weights "
              + Arrays.toString(weights)
              + " profits "
              + Arrays.toString(profits)
              + " "
              + domainsOf(vars);
      store.impose(
          new KnapsackDP(profits, weights, Arrays.copyOf(vars, n), vars[n], vars[n + 1])
              .adaptive(false));
      checkSupportsAndFixpointAlongRandomWalk(
          instance,
          store,
          vars,
          vs -> knapsackSolutions(profits, weights, vs),
          () -> {
            Store copyStore = new Store();
            IntVar[] copies = new IntVar[vars.length];
            for (int i = 0; i < vars.length; i++) {
              copies[i] = new IntVar(copyStore, vars[i].id());
              copies[i].addDom(vars[i].dom());
            }
            copyStore.impose(
                new KnapsackDP(profits, weights, Arrays.copyOf(copies, n), copies[n], copies[n + 1])
                    .adaptive(false));
            return copyStore.consistency() ? domainsOf(copies) : "FAIL";
          },
          random);
    }
  }

  @Test
  void knapsackDpAdaptiveFindsAllSolutions() {
    // The adaptive mode skips calls, so it is checked through search: alone and inside Knapsack it
    // must find exactly the solutions of the brute force.
    Random random = new Random(17);
    for (int run = 0; run < 300; run++) {
      int n = 2 + random.nextInt(5);
      int[] weights = new int[n];
      int[] profits = new int[n];
      int[] maxima = new int[n];
      int weightSum = 0;
      int profitSum = 0;
      for (int i = 0; i < n; i++) {
        weights[i] = random.nextInt(8);
        profits[i] = random.nextInt(9);
        maxima[i] = 1 + random.nextInt(2);
        weightSum += weights[i] * maxima[i];
        profitSum += profits[i] * maxima[i];
      }
      int capacityMin = random.nextInt(weightSum / 2 + 1);
      int profitMin = random.nextInt(profitSum / 2 + 1);
      long expected = -1;
      for (boolean withKnapsack : new boolean[] {false, true}) {
        Store store = new Store();
        IntVar[] vars = new IntVar[n + 2];
        for (int i = 0; i < n; i++) {
          vars[i] = new IntVar(store, "q" + i, 0, maxima[i]);
        }
        vars[n] = new IntVar(store, "capacity", capacityMin, weightSum);
        vars[n + 1] = new IntVar(store, "profit", profitMin, profitSum);
        if (expected < 0) {
          expected = knapsackSolutions(profits, weights, vars).size();
        }
        IntVar[] q = Arrays.copyOf(vars, n);
        if (withKnapsack
            && Arrays.stream(weights).allMatch(w -> w > 0)
            && Arrays.stream(profits).allMatch(p -> p > 0)) {
          store.impose(new Knapsack(profits, weights, q, vars[n], vars[n + 1]));
        } else {
          store.impose(new KnapsackDP(profits, weights, q, vars[n], vars[n + 1]));
        }
        long found = 0;
        if (store.consistency()) {
          DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
          search.getSolutionListener().searchAll(true);
          search.getSolutionListener().recordSolutions(false);
          search.setPrintInfo(false);
          search.labeling(store, new SimpleSelect<>(vars, null, new IndomainMin<>()));
          found = search.getSolutionListener().solutionsNo();
        }
        assertThat(found)
            .as(
                "run %d weights %s profits %s",
                run, Arrays.toString(weights), Arrays.toString(profits))
            .isEqualTo(expected);
      }
    }
  }

  @Test
  void knapsackDpSkipsAboveLimit() {
    Store store = new Store();
    IntVar[] q = {new IntVar(store, "q0", 0, 10), new IntVar(store, "q1", 0, 10)};
    IntVar capacity = new IntVar(store, "capacity", 0, 1000);
    IntVar profit = new IntVar(store, "profit", 0, 1000);
    store.impose(new KnapsackDP(new int[] {3, 5}, new int[] {7, 11}, q, capacity, profit, 10));
    assertThat(store.consistency()).isTrue();
    assertThat(capacity.max()).isEqualTo(1000);
    assertThat(q[0].max()).isEqualTo(10);
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
  void argMinMaxSatisfiedRespectsFirstIndexTieBreak() {
    // satisfied() accepted an index whose value ties with an earlier element, and ArgMax read the
    // value of a non-singleton index.
    Store store = new Store();
    IntVar[] x = {new IntVar(store, "x1", 3, 3), new IntVar(store, "x2", 3, 3)};
    IntVar second = new IntVar(store, "second", 2, 2);
    IntVar first = new IntVar(store, "first", 1, 1);
    IntVar any = new IntVar(store, "any", 1, 2);

    assertThat(new ArgMax(x, second).satisfied()).isFalse();
    assertThat(new ArgMin(x, second).satisfied()).isFalse();
    assertThat(new ArgMax(x, first).satisfied()).isTrue();
    assertThat(new ArgMin(x, first).satisfied()).isTrue();
    assertThat(new ArgMax(x, any).satisfied()).isFalse();
    assertThat(new ArgMin(x, any).satisfied()).isFalse();
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
  void elementVariableRemovesEveryPositionOfRepeatedVariable() {
    // A variable repeated on the list kept its first position when it became disjoint from the
    // value, so the index could still select it.
    Store store = new Store();
    IntVar index = new IntVar(store, "index", 1, 3);
    IntVar value = new IntVar(store, "value", 1, 2);
    IntVar y = new IntVar(store, "y", 0, 1);
    IntVar z = new IntVar(store, "z", 2, 2);
    store.impose(new ElementVariable(index, new IntVar[] {y, y, z}, value));
    assertThat(store.consistency()).isTrue();

    store.setLevel(store.level + 1);
    y.domain.in(store.level, y, 0, 0);

    assertThat(store.consistency()).isTrue();
    assertThat(index.singleton(3)).isTrue();
  }

  @Test
  void elementVariableStaysAttachedToIndexOnTheList() {
    // The index is also on the list, at a position it cannot take. Removing that position
    // detached the index from the constraint, which then ignored the index being fixed.
    Store store = new Store();
    IntVar index = new IntVar(store, "index", 1, 1);
    index.addDom(3, 3);
    IntVar value = new IntVar(store, "value", 5, 6);
    IntVar a = new IntVar(store, "a", 5, 6);
    IntVar b = new IntVar(store, "b", 5, 7);
    store.impose(new ElementVariable(index, new IntVar[] {a, index, b}, value));
    assertThat(store.consistency()).isTrue();

    store.setLevel(store.level + 1);
    index.domain.in(store.level, index, 3, 3);

    assertThat(store.consistency()).isTrue();
    assertThat(b.max()).isEqualTo(6);
  }

  @Test
  void elementIntegerWithoutDuplicateCheck() {
    // The constructor option checkDuplicates = false left the duplicate structures null, so the
    // first consistency call threw a NullPointerException.
    Store store = new Store();
    IntVar index = new IntVar(store, "index", 1, 4);
    IntVar value = new IntVar(store, "value", 0, 9);
    store.impose(new ElementInteger(index, new int[] {3, 1, 3, 7}, value, 0, false));
    assertThat(store.consistency()).isTrue();
    assertThat(value.dom().toString()).isEqualTo("{1, 3, 7}");

    int noOfSolutions = noOfAllSolutions(store, new IntVar[] {index, value});
    assertThat(noOfSolutions).isEqualTo(4);
  }

  @Test
  void elementVariableLooksForSupportsWithinIndex() {
    // A value that lost its support was given a new support at a position the index can no
    // longer take, so it stayed in the value domain.
    Store store = new Store();
    IntVar index = new IntVar(store, "index", 1, 3);
    IntVar value = new IntVar(store, "value", 1, 3);
    IntVar a = new IntVar(store, "a", 1, 3);
    IntVar b = new IntVar(store, "b", 1, 3);
    IntVar c = new IntVar(store, "c", 1, 1);
    c.addDom(3, 3);
    store.impose(new ElementVariable(index, new IntVar[] {a, b, c}, value));
    assertThat(store.consistency()).isTrue();

    store.setLevel(store.level + 1);
    index.domain.inComplement(store.level, index, 1);
    assertThat(store.consistency()).isTrue();

    store.setLevel(store.level + 1);
    b.domain.in(store.level, b, 3, 3);
    assertThat(store.consistency()).isTrue();
    assertThat(value.domain.contains(2)).isFalse();
  }

  @Test
  void elementBoolRejectsNonBooleanList() {
    // Positions holding a value other than 0 or 1 were never removed from the index, so with
    // list [2, 0] and value in 0..1 the solution index = 1, value = 0 was accepted.
    Store store = new Store();
    IntVar index = new IntVar(store, "index", 1, 2);
    IntVar value = new IntVar(store, "value", 0, 1);
    assertThatThrownBy(() -> new ElementBool(index, new int[] {2, 0}, value, 0))
        .isInstanceOf(IllegalArgumentException.class);
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

    DisjointConditional disjointConditional =
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
  void allEqualNegatedKeepsCallerArrayOrder() {
    // not all_equal(x) moved fixed variables to the front of the array it was given, so the
    // caller's array (in FlatZinc the output array) was reordered during search
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 1, 3),
      new IntVar(store, "x1", 1, 3),
      new IntVar(store, "x2", 1, 3),
      new IntVar(store, "x3", 1, 1)
    };
    IntVar[] original = x.clone();
    store.impose(new Reified(new AllEqual(x), new IntVar(store, "b", 0, 0)));

    assertThat(noOfAllSolutions(store, x)).isEqualTo(26);
    assertThat(x).containsExactly(original);
  }

  @Test
  void allEqualNegatedOnOneVariableFails() {
    // a single variable is always all equal, so its negation has no solution
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 1);
    store.impose(new Not(new AllEqual(new IntVar[] {x})));

    assertThat(store.consistency()).isFalse();
  }

  @Test
  void allEqualReifiedFalseWithoutCommonValue() {
    // the domains intersect pairwise but have no common value, so b must be 0
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 1, 1), new IntVar(store, "x1", 2, 3), new IntVar(store, "x2", 1, 2)
    };
    x[0].addDom(3, 3);
    IntVar b = new IntVar(store, "b", 0, 1);
    store.impose(new Reified(new AllEqual(x), b));

    assertThat(store.consistency()).isTrue();
    assertThat(b.dom().toString()).isEqualTo("0");
  }

  @Test
  void increasingWithRepeatedVariableReachesFixpoint() {
    // [x, y, x] increasing means x = y; strictly decreasing [x, x] has no solution
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 2, 5);
    store.impose(new Increasing(new IntVar[] {x, y, x}));
    assertThat(store.consistency()).isTrue();
    assertThat(x.dom().toString()).isEqualTo("{2..3}");
    assertThat(y.dom().toString()).isEqualTo("{2..3}");

    Store store2 = new Store();
    IntVar z = new IntVar(store2, "z", 0, 2);
    store2.impose(new Decreasing(new IntVar[] {z, z}, true));
    assertThat(store2.consistency()).isFalse();
  }

  @Test
  void disjointConditionalProfileCountsOverlappingPairOnce() {
    // rectangles 3 and 4 may overlap when c1 = 0; the profile built for rectangle 2 lost track
    // of which rectangles a profile segment holds and counted both, removing y2 = 0
    Store store = new Store();
    IntVar[][] r = {
      {new IntVar(store, "x1", 0, 2), new IntVar(store, 1, 1), one(store), one(store)},
      {new IntVar(store, 1, 1), new IntVar(store, "y2", 0, 2), oneTwo(store), oneTwo(store)},
      {new IntVar(store, 2, 2), new IntVar(store, 0, 0), one(store), oneTwo(store)},
      {new IntVar(store, 2, 2), new IntVar(store, 0, 0), one(store), new IntVar(store, 2, 2)}
    };
    IntVar[] c = {new IntVar(store, "c0", 0, 1), new IntVar(store, "c1", 0, 1)};
    List<List<Integer>> pairs = List.of(List.of(1, 2), List.of(3, 4));
    store.impose(new DisjointConditional(r, pairs, Arrays.asList(c)));

    IntVar[] all =
        Stream.concat(Arrays.stream(r).flatMap(Arrays::stream), Arrays.stream(c))
            .toArray(IntVar[]::new);
    int expected =
        bruteForce(
                all,
                a -> {
                  for (int i = 0; i < 4; i++) {
                    for (int j = i + 1; j < 4; j++) {
                      int p = pairs.indexOf(List.of(i + 1, j + 1));
                      boolean apart =
                          a[4 * i] + a[4 * i + 2] <= a[4 * j]
                              || a[4 * j] + a[4 * j + 2] <= a[4 * i]
                              || a[4 * i + 1] + a[4 * i + 3] <= a[4 * j + 1]
                              || a[4 * j + 1] + a[4 * j + 3] <= a[4 * i + 1];
                      if (!apart && (p < 0 || a[16 + p] == 1)) {
                        return false;
                      }
                    }
                  }
                  return true;
                })
            .size();

    // label the variables on the path to the lost solution first
    IntVar[] labeled =
        Stream.concat(Stream.of(r[1][3], c[0], r[2][3], c[1], r[0][0]), Arrays.stream(all))
            .distinct()
            .toArray(IntVar[]::new);
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, new SimpleSelect<>(labeled, null, new IndomainMin<>()));

    assertThat(search.getSolutionListener().solutionsNo()).isEqualTo(expected);
  }

  private static IntVar one(Store store) {
    return new IntVar(store, 1, 1);
  }

  private static IntVar oneTwo(Store store) {
    return new IntVar(store, 1, 2);
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

  // with at most 2 values, x2 must share a value with x0 (1..2) or with x1 (4..5)
  @Test
  void testValuesPrunesValuesNeedingTooManyValues() {
    Store store = new Store();
    IntVar x0 = new IntVar(store, "x0", 1, 2);
    IntVar x1 = new IntVar(store, "x1", 4, 5);
    IntVar x2 = new IntVar(store, "x2", 1, 5);
    IntVar count = new IntVar(store, "count", 0, 2);
    store.impose(new Values(new IntVar[] {x0, x1, x2}, count));

    assertThat(store.consistency()).isTrue();

    assertThat(count.dom().toString()).isEqualTo("2");
    assertThat(x2.dom().toString()).isEqualTo("{1..2, 4..5}");
  }

  // with at least 3 values, x0 and x1 take 1 and 2, so x2 must take 3
  @Test
  void testValuesPrunesValuesGivingTooFewValues() {
    Store store = new Store();
    IntVar x0 = new IntVar(store, "x0", 1, 2);
    IntVar x1 = new IntVar(store, "x1", 1, 2);
    IntVar x2 = new IntVar(store, "x2", 1, 3);
    IntVar x3 = new IntVar(store, "x3", 1, 3);
    IntVar count = new IntVar(store, "count", 3, 4);
    store.impose(new Values(new IntVar[] {x0, x1, x2, x3}, count));

    assertThat(store.consistency()).isTrue();

    assertThat(count.dom().toString()).isEqualTo("3");
    assertThat(x2.dom().toString()).isEqualTo("{1..3}");

    x3.domain.in(store.level, x3, 1, 2);
    assertThat(store.consistency()).isTrue();
    assertThat(x2.dom().toString()).isEqualTo("3");
  }

  // Values switches between dense value arrays and a hash map when a variable keeps a far value;
  // the singleton pruning must use the values of the current path after each switch
  @Test
  void testValuesWithFarValueMatchesBruteForce() {
    int far = 1_000_000;
    int[][] domains = {{0, 1, 2}, {0, 1, 2}, {0, 1, 2}, {0, 1, 2, far}};
    for (int countMin = 1; countMin <= 4; countMin++) {
      for (int countMax = countMin; countMax <= 4; countMax++) {
        int expected = 0;
        for (int a : domains[0]) {
          for (int b : domains[1]) {
            for (int c : domains[2]) {
              for (int d : domains[3]) {
                long different = IntStream.of(a, b, c, d).distinct().count();
                if (countMin <= different && different <= countMax) {
                  expected++;
                }
              }
            }
          }
        }

        Store store = new Store();
        IntVar[] x = new IntVar[domains.length];
        for (int i = 0; i < x.length; i++) {
          x[i] = new IntVar(store, "x" + i);
          for (int v : domains[i]) {
            x[i].addDom(v, v);
          }
        }
        IntVar count = new IntVar(store, "count", countMin, countMax);
        store.impose(new Values(x, count));

        DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
        search.setPrintInfo(false);
        search.getSolutionListener().searchAll(true);
        search.getSolutionListener().recordSolutions(false);
        boolean found = search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()));

        assertThat(found ? search.getSolutionListener().solutionsNo() : 0)
            .as("count in %d..%d", countMin, countMax)
            .isEqualTo(expected);
      }
    }
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

  @Test
  void geostKeepsInterleavedShapesApartAtNegativeCoordinates() {
    // Shape = cells x and x + 2. With object 0 at x0 the cells x0 + 1 and x0 + 3 are free, so
    // object 1 fits at x0 + 1. The frame of the fixed object was rounded with % 4, which is
    // negative for negative coordinates, and covered the hole whenever x0 <= -1.
    for (int x0 = -6; x0 <= 3; x0++) {
      Store store = new Store();
      List<Dbox> cells =
          List.of(new Dbox(new int[] {0}, new int[] {1}), new Dbox(new int[] {2}, new int[] {1}));
      List<Shape> shapes = List.of(new Shape(0, new int[] {0}, new int[] {1}), new Shape(1, cells));
      IntVar[] x = {new IntVar(store, "x0", x0, x0), new IntVar(store, "x1", x0 - 3, x0 + 3)};
      List<GeostObject> objects = new ArrayList<>();
      for (int i = 0; i < 2; i++) {
        objects.add(
            new GeostObject(
                i,
                new IntVar[] {x[i]},
                new IntVar(store, 1, 1),
                new IntVar(store, 0, 0),
                new IntVar(store, 1, 1),
                new IntVar(store, 1, 1)));
      }
      store.impose(
          new Geost(objects, List.of(new NonOverlapping(objects, new int[] {0, 1})), shapes));

      assertThat(store.consistency()).as("x0 = %d", x0).isTrue();
      // x1 = x0 - 3, x0 - 1, x0 + 1, x0 + 3 interleave or touch; x0 +- 2 and x0 overlap
      assertThat(noOfAllSolutions(store, x)).as("x0 = %d", x0).isEqualTo(4);
    }
  }

  @Test
  void geostNonOverlappingWithoutTimeKeepsObjectsApart() {
    // Two unit squares, object 0 at (0, 0), object 1 at (x1, 0) with x1 in 0..1. NonOverlapping
    // over the spatial dimensions only (no time dimension, 2) must forbid x1 = 0, and so must
    // NonOverlapping over dimension 0 only. The filter of useful internal constraints overflowed
    // on the unbounded time extent and dropped the obstacle, which accepted x1 = 0.
    for (int[] dims : new int[][] {{0, 1}, {0}, {0, 1, 2}}) {
      Store store = new Store();
      List<Shape> shapes = List.of(new Shape(0, new int[] {0, 0}, new int[] {1, 1}));
      IntVar x1 = new IntVar(store, "x1", 0, 1);
      IntVar[][] coords = {
        {new IntVar(store, 0, 0), new IntVar(store, 0, 0)}, {x1, new IntVar(store, 0, 0)}
      };
      List<GeostObject> objects = new ArrayList<>();
      for (int i = 0; i < 2; i++) {
        objects.add(
            new GeostObject(
                i,
                coords[i],
                new IntVar(store, 0, 0),
                new IntVar(store, 0, 0),
                new IntVar(store, 1, 1),
                new IntVar(store, 1, 1)));
      }
      store.impose(new Geost(objects, List.of(new NonOverlapping(objects, dims)), shapes));

      assertThat(noOfAllSolutions(store, new IntVar[] {x1}))
          .as("dims %s", Arrays.toString(dims))
          .isEqualTo(1);
    }
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
  void testCumulativeZeroDurationTaskWithFixedDurations() {

    // With fixed durations and resources the sweep of CumulativePrimary also pruned the start of
    // a task of zero duration, which does not occupy the resource, against the profile.
    Store store = new Store();
    IntVar[] s = {new IntVar(store, 0, 0), new IntVar(store, 0, 1)};
    IntVar[] d = {new IntVar(store, 1, 1), new IntVar(store, 0, 0)};
    IntVar[] r = {new IntVar(store, 1, 1), new IntVar(store, 3, 3)};
    store.impose(new Cumulative(s, d, r, new IntVar(store, 3, 3)));
    assertThat(store.consistency()).isTrue();
    assertThat(s[1].min()).isZero();
  }

  @Test
  void testCumulativeOptionalZeroDurationTask() {

    // An optional task of zero duration was made absent when the profile had no room at its
    // start, although it does not occupy the resource.
    Store store = new Store();
    IntVar[] s = {new IntVar(store, 3, 3), new IntVar(store, 3, 3), new IntVar(store, 1, 1)};
    IntVar[] d = {new IntVar(store, 1, 1), new IntVar(store, 0, 0), new IntVar(store, 2, 2)};
    IntVar[] r = {new IntVar(store, 2, 2), new IntVar(store, 1, 1), new IntVar(store, 2, 2)};
    IntVar[] o = {new IntVar(store, 1, 1), new IntVar(store, 0, 1), new IntVar(store, 1, 1)};
    store.impose(new CumulativeOptional(s, d, r, new IntVar(store, 2, 2), o));
    assertThat(store.consistency()).isTrue();
    assertThat(o[1].max()).isEqualTo(1);
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

  /**
   * Fingerprints the search of the rectangle constraints built on AbstractDiff: for each kind, the
   * solutions found, in order, and the search statistics on seeded random instances. Refactoring
   * that engine must leave every fingerprint unchanged, which means the same search tree and not
   * only the same solutions.
   */
  @Test
  void rectangleConstraintsKeepTheirSearchTrees() {
    Map<String, String> actual = new LinkedHashMap<>();
    for (String kind :
        List.of(
            "Diff2",
            "Diff2NoProfile",
            "Diff2Exclusive",
            "Disjoint",
            "DisjointNoProfile",
            "DisjointConditional",
            "DisjointConditionalNoProfile")) {
      actual.put(kind, rectangleSearchFingerprint(kind));
    }

    assertThat(actual)
        .isEqualTo(
            Map.of(
                "Diff2",
                "solutions=261426 nodes=271150 decisions=266268 wrong=4882 hash=67a9b6d05bb56939",
                "Diff2NoProfile",
                "solutions=261426 nodes=275572 decisions=268479 wrong=7093 hash=1d2a26df1730729",
                "Diff2Exclusive",
                "solutions=274199 nodes=281043 decisions=277601 wrong=3442 hash=e3ba8c5362d530ad",
                "Disjoint",
                "solutions=250703 nodes=258629 decisions=254646 wrong=3983 hash=688d304cb8d0f443",
                "DisjointNoProfile",
                "solutions=250683 nodes=263587 decisions=257115 wrong=6472 hash=37879c275e329ec3",
                "DisjointConditional",
                "solutions=737646 nodes=765448 decisions=751527 wrong=13921 hash=f7e9e3977ef731a1",
                "DisjointConditionalNoProfile",
                "solutions=737646 nodes=766920 decisions=752263 wrong=14657 hash=5f89905bc162726d"));
  }

  private static String rectangleSearchFingerprint(String kind) {
    Random random = new Random(20261024L);
    long solutions = 0;
    long nodes = 0;
    long decisions = 0;
    long wrongDecisions = 0;
    long[] hash = {17};
    for (int instance = 0; instance < 40; instance++) {
      Store store = new Store();
      int n = 2 + random.nextInt(2);
      List<List<? extends IntVar>> rectangles = new ArrayList<>();
      List<IntVar> vars = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        List<IntVar> r =
            List.of(
                rectangleVar(store, random, 0, 3),
                rectangleVar(store, random, 0, 3),
                rectangleVar(store, random, 0, 2),
                rectangleVar(store, random, 0, 2));
        rectangles.add(r);
        vars.addAll(r);
      }
      List<List<Integer>> pairs = new ArrayList<>();
      for (int i = 1; i <= n; i++) {
        for (int j = i + 1; j <= n; j++) {
          if (random.nextInt(3) == 0) {
            pairs.add(List.of(i, j));
          }
        }
      }
      List<IntVar> conditions = new ArrayList<>();
      for (int p = 0; p < pairs.size(); p++) {
        conditions.add(new IntVar(store, "c" + p, 0, 1));
      }
      switch (kind) {
        case "Diff2" -> store.impose(new Diff2(rectangles));
        case "Diff2NoProfile" -> store.impose(new Diff2(rectangles, false));
        case "Diff2Exclusive" -> store.impose(new Diff2(rectangles, pairs));
        case "Disjoint" -> store.impose(new Disjoint(rectangles));
        case "DisjointNoProfile" -> store.impose(new Disjoint(rectangles, false));
        case "DisjointConditional" ->
            store.impose(new DisjointConditional(rectangles, pairs, conditions));
        case "DisjointConditionalNoProfile" ->
            store.impose(new DisjointConditional(rectangles, pairs, conditions, false));
        default -> throw new IllegalArgumentException(kind);
      }
      if (kind.startsWith("DisjointConditional")) {
        vars.addAll(conditions);
      }
      Collections.shuffle(vars, random);

      IntVar[] order = vars.toArray(IntVar[]::new);
      SelectChoicePoint<IntVar> select =
          new SimpleSelect<>(
              order,
              null,
              instance % 2 == 0 ? new IndomainMin<>() : new IndomainRandom<>(instance));
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      // hashes every solution in the order the search finds it
      search.setSolutionListener(
          new SimpleSolutionListener<>() {
            @Override
            public boolean executeAfterSolution(
                Search<IntVar> s, SelectChoicePoint<IntVar> choicePoint) {
              long value = 0;
              for (IntVar v : order) {
                value = value * 31 + v.value();
              }
              hash[0] = hash[0] * 1_000_003 + value;
              return super.executeAfterSolution(s, choicePoint);
            }
          });
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      search.labeling(store, select);

      solutions += search.getSolutionListener().solutionsNo();
      nodes += search.getNodes();
      decisions += search.getDecisions();
      wrongDecisions += search.getWrongDecisions();
    }
    return "solutions="
        + solutions
        + " nodes="
        + nodes
        + " decisions="
        + decisions
        + " wrong="
        + wrongDecisions
        + " hash="
        + Long.toHexString(hash[0]);
  }

  @Test
  void equalityShiftsReachFixpointWhenTheFirstVariableOnlyKeepsBounds() {
    // A boolean x keeps only bounds, so pruning x from z leaves it at 0..1 and then z gets fixed;
    // one more pass is needed to fix x to 0.
    List<Function<IntVar[], Constraint>> constraints =
        List.of(
            v -> new XeqY(v[0], v[1]),
            v -> new XplusCeqZ(v[0], 0, v[1]),
            v -> new Not(new XplusCneqZ(v[0], 0, v[1])),
            v -> new XplusYeqZ(v[0], v[2], v[1]),
            v -> new XplusYeqZ(v[2], v[0], v[1]),
            v -> new XplusYeqC(v[1], v[0], 5));
    for (Function<IntVar[], Constraint> constraint : constraints) {
      Store store = new Store();
      IntVar x = new BooleanVar(store, "x");
      IntVar z = new IntVar(store, "z", 0, 0);
      z.addDom(5, 5);
      IntVar zero = new IntVar(store, "zero", 0, 0);
      Constraint c = constraint.apply(new IntVar[] {x, z, zero});
      store.impose(c);
      assertThat(store.consistency()).isTrue();
      assertThat(x.max()).as(c.toString()).isEqualTo(0);
      assertThat(z.singleton()).as(c.toString()).isTrue();
    }
  }

  @Test
  void memberIncludedAgainDuringSearchSurvivesBacktracking() {
    // A wrapper includes its nested constraints each time it is imposed, also at a search level,
    // and calls their consistency without imposing them. include() created a new position stamp
    // each time, so after backtracking below that level the stamp had no value and consistency
    // threw ArrayIndexOutOfBoundsException.
    Store store = new Store();
    IntVar[] x = getIntVars(store, "x", 3, 3);
    IntVar e = new IntVar(store, "e", 3, 3);
    x[1].addDom(3, 3);
    Member member = new Member(x, e);
    member.include(store);
    store.setLevel(1);
    member.include(store);
    store.removeLevel(1);
    store.setLevel(0);

    member.consistency(store);
    assertThat(x[1].singleton(3)).isTrue();

    // included first at a search level, its stamp is gone after backtracking and is replaced
    Store other = new Store();
    IntVar[] y = getIntVars(other, "y", 3, 3);
    IntVar f = new IntVar(other, "f", 3, 3);
    y[1].addDom(3, 3);
    Member late = new Member(y, f);
    other.setLevel(1);
    late.include(other);
    other.removeLevel(1);
    other.setLevel(0);
    late.include(other);

    late.consistency(other);
    assertThat(y[1].singleton(3)).isTrue();
  }

  @Test
  void alldifferentExceptAcceptsRepeatedExceptionValues() {
    // [0, 0, 1] and [4, 4, 1] satisfy the constraints: exception values may repeat
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 0, 0), new IntVar(store, "x1", 0, 0), new IntVar(store, "x2", 1, 1)
    };
    IntVar[] y = {
      new IntVar(store, "y0", 4, 4), new IntVar(store, "y1", 4, 4), new IntVar(store, "y2", 1, 1)
    };
    AlldifferentExceptZero zero = new AlldifferentExceptZero(x);
    AlldifferentExcept except = new AlldifferentExcept(y, new IntervalDomain(4, 4));
    store.impose(zero);
    store.impose(except);

    assertThat(store.consistency()).isTrue();
    assertThat(zero.satisfied()).isTrue();
    assertThat(zero.notSatisfied()).isFalse();
    assertThat(except.satisfied()).isTrue();
    assertThat(except.notSatisfied()).isFalse();
  }

  @Test
  void linearIntWithManyVariablesHasTheSolutionCountOfBruteForce() {
    // a LinearInt with more than three variables stops reading the variables that get fixed and
    // reads them again after backtracking, which an all-solution search exercises
    String[] relations = {"==", "<=", "<", "!=", ">", ">="};
    Random random = new Random(7);
    for (int run = 0; run < 600; run++) {
      int n = 4 + random.nextInt(4);
      int[] weights = new int[n];
      for (int i = 0; i < n; i++) {
        weights[i] = (1 + random.nextInt(3)) * (random.nextBoolean() ? 1 : -1);
      }
      String rel = relations[run % relations.length];
      int b = random.nextInt(9) - 4;
      Store store = new Store();
      IntVar[] vars = new IntVar[n];
      for (int i = 0; i < n; i++) {
        vars[i] = randomVar(store, "v" + i, -2, 3, random);
      }
      if (run % 5 == 0) {
        vars[n - 1] = vars[0];
      }
      String instance =
          "run "
              + run
              + " "
              + Arrays.toString(weights)
              + " "
              + rel
              + " "
              + b
              + " "
              + domainsOf(vars);
      int expected = countLinearSolutions(vars, weights, rel, b, new int[n], 0);
      store.impose(new LinearInt(vars, weights, rel, b));
      assertThat(noOfAllSolutionsNoRecord(store, vars)).as(instance).isEqualTo(expected);
    }
  }

  /** Counts the assignments of vars[i..] that satisfy the relation, given values[0..i). */
  private static int countLinearSolutions(
      IntVar[] vars, int[] weights, String rel, int b, int[] values, int i) {
    if (i == vars.length) {
      int sum = 0;
      for (int j = 0; j < vars.length; j++) {
        sum += weights[j] * values[j];
      }
      return switch (rel) {
        case "==" -> sum == b ? 1 : 0;
        case "<=" -> sum <= b ? 1 : 0;
        case "<" -> sum < b ? 1 : 0;
        case "!=" -> sum != b ? 1 : 0;
        case ">" -> sum > b ? 1 : 0;
        default -> sum >= b ? 1 : 0;
      };
    }
    for (int j = 0; j < i; j++) {
      if (vars[j] == vars[i]) {
        // a repeated variable takes the value it already has
        values[i] = values[j];
        return countLinearSolutions(vars, weights, rel, b, values, i + 1);
      }
    }
    int count = 0;
    for (ValueEnumeration e = vars[i].dom().valueEnumeration(); e.hasMoreElements(); ) {
      values[i] = e.nextElement();
      count += countLinearSolutions(vars, weights, rel, b, values, i + 1);
    }
    return count;
  }

  private static IntVar rectangleVar(Store store, Random random, int min, int max) {
    IntVar v = new IntVar(store);
    for (int value = min; value <= max; value++) {
      if (random.nextInt(3) != 0) {
        v.addDom(value, value);
      }
    }
    if (v.dom().isEmpty()) {
      v.addDom(min, min);
    }
    return v;
  }

  static class TestWatcherExtension implements BeforeEachCallback {
    @Override
    public void beforeEach(ExtensionContext context) {
      log.info("Starting test: " + context.getDisplayName());
    }
  }

  @Test
  void testSequenceWithBoundsOutsideWindowHasNoSolution() {

    // a window of 2 holds at most 2 values of the set, so min = 3 or max = -1 cannot be met
    for (int[] minMax : new int[][] {{3, 3}, {-1, -1}}) {
      Store store = new Store();
      IntVar[] x = new IntVar[3];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 1);
      }

      store.imposeDecomposition(new Sequence(x, new IntervalDomain(1, 1), 2, minMax[0], minMax[1]));

      assertThat(noOfAllSolutions(store, x)).isZero();
    }
  }

  @Test
  void testSequenceWithWindowLongerThanListHoldsTrivially() {

    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
    }

    // no window of 4 fits in 3 variables, so every assignment is a solution
    store.imposeDecomposition(new Sequence(x, new IntervalDomain(1, 1), 4, 1, 1));

    assertThat(noOfAllSolutions(store, x)).isEqualTo(8);
  }

  @Test
  void testSequenceRejectsNonPositiveWindow() {

    Store store = new Store();
    IntVar[] x = getIntVars(store, "x", 3, 2);

    assertThatThrownBy(() -> new Sequence(x, new IntervalDomain(1, 1), 0, 0, 0))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testStretchForbidsValueWithZeroMaximalLength() {

    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 2);
    }

    // value 2 may form stretches of length 0 only, so x must be [1, 1, 1]
    store.imposeDecomposition(new Stretch(new int[] {1, 2}, new int[] {1, 0}, new int[] {3, 0}, x));

    assertThat(noOfAllSolutions(store, x)).isEqualTo(1);
  }

  @Test
  void testStretchRejectsRepeatedValues() {

    Store store = new Store();
    IntVar[] x = getIntVars(store, "x", 2, 2);

    // with value 1 listed twice, [1, 1] was accepted as two stretches of length 1
    assertThatThrownBy(() -> new Stretch(new int[] {1, 1}, new int[] {1, 1}, new int[] {1, 1}, x))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testStretchRejectsArraysOfDifferentLengths() {

    Store store = new Store();
    IntVar[] x = getIntVars(store, "x", 2, 2);

    assertThatThrownBy(() -> new Stretch(new int[] {1, 2}, new int[] {1}, new int[] {2, 2}, x))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testBoundDomainInEmptyDomainFails() {

    Store store = new Store();
    // Boolean variables have a BoundDomain
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < x.length; i++) {
      x[i] = new BooleanVar(store, "x" + i);
    }

    // the automaton has no accepting word, so Regular restricts x to empty domains
    store.imposeDecomposition(new Sequence(x, new IntervalDomain(1, 1), 2, -1, -1));

    assertThat(store.consistency()).isFalse();
  }
}
