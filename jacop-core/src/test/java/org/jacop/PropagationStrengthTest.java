/*
 * PropagationStrengthTest.java
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

import java.util.Arrays;
import java.util.Random;
import java.util.function.BiFunction;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.AlldifferentExcept;
import org.jacop.constraints.AlldifferentExceptZero;
import org.jacop.constraints.And;
import org.jacop.constraints.Eq;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.IfThenElse;
import org.jacop.constraints.Implies;
import org.jacop.constraints.InterDistance;
import org.jacop.constraints.MultiInterDistance;
import org.jacop.constraints.Not;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SeqPrecedeChain;
import org.jacop.constraints.SoftGCC;
import org.jacop.constraints.Sort;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.ValuePrecede;
import org.jacop.constraints.ViolationMeasure;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.Xor;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.junit.jupiter.api.Test;

/**
 * Checks that constraints wake up on every change their consistency method can use, so that the
 * store reaches the same fixpoint as re-running the constraint would.
 */
class PropagationStrengthTest {

  @Test
  void testXplusYeqZWakesOnRemovedValue() {

    // x = 3, so z = y + 3; removing 2 and 3 from inside y must remove 5 and 6 from z.
    Store store = new Store();
    IntVar x = variable(store, "x", 3);
    IntVar y = new IntVar(store, "y", 1, 4);
    IntVar z = new IntVar(store, "z", 4, 7);
    store.impose(new XplusYeqZ(x, y, z));
    assertThat(store.consistency()).isTrue();

    assertThat(removeValues(store, y, 2, 3)).isTrue();
    assertThat(z.dom().toString()).isEqualTo("{4, 7}");
  }

  @Test
  void testXmulYeqZWakesOnRemovedValue() {

    // x = 1, so z = y; removing 8 from inside y must remove it from z.
    Store store = new Store();
    IntVar x = variable(store, "x", 1);
    IntVar y = variable(store, "y", 5, 8, 100);
    IntVar z = new IntVar(store, "z", 1, 100);
    store.impose(new XmulYeqZ(x, y, z));
    assertThat(store.consistency()).isTrue();
    assertThat(z.dom().toString()).isEqualTo("{5, 8, 100}");

    assertThat(removeValues(store, y, 8)).isTrue();
    assertThat(z.dom().toString()).isEqualTo("{5, 100}");
  }

  @Test
  void testReifiedWakesOnRemovedValue() {

    assertThat(nestedXplusCeqZPrunes(Reified::new)).isEqualTo("{1, 4}");
  }

  @Test
  void testImpliesWakesOnRemovedValue() {

    assertThat(nestedXplusCeqZPrunes((c, b) -> new Implies(b, c))).isEqualTo("{1, 4}");
  }

  // the constraints composed of others woke only on the events that decide whether their parts are
  // satisfied, GROUND and BOUND for XplusCeqZ, not on the ANY event its consistency() prunes on
  @Test
  void testComposedConstraintsWakeOnRemovedValue() {

    assertThat(nestedXplusCeqZPrunes((c, b) -> new And(c, new XeqC(b, 1)))).isEqualTo("{1, 4}");
    assertThat(nestedXplusCeqZPrunes((c, b) -> new Or(c, new XeqC(b, 0)))).isEqualTo("{1, 4}");
    assertThat(nestedXplusCeqZPrunes((c, b) -> new Not(new Not(c)))).isEqualTo("{1, 4}");
    assertThat(nestedXplusCeqZPrunes((c, b) -> new Xor(new Not(c), b))).isEqualTo("{1, 4}");
    assertThat(nestedXplusCeqZPrunes((c, b) -> new Eq(new XeqC(b, 1), c))).isEqualTo("{1, 4}");
    assertThat(nestedXplusCeqZPrunes((c, b) -> new IfThen(new XeqC(b, 1), c))).isEqualTo("{1, 4}");
    assertThat(nestedXplusCeqZPrunes((c, b) -> new IfThenElse(new XeqC(b, 1), c, new XeqC(b, 1))))
        .isEqualTo("{1, 4}");
    assertThat(nestedXplusCeqZPrunes((c, b) -> new Reified(new And(c, new XeqC(b, 1)), b)))
        .isEqualTo("{1, 4}");
  }

  // Not(x != y) woke on the event deciding that x != y fails, GROUND, while it makes x and y equal
  @Test
  void testNegatedDisequalityWakesOnRemovedValue() {

    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);
    store.impose(new Not(new XneqY(x, y)));
    assertThat(store.consistency()).isTrue();

    assertThat(removeValues(store, y, 1)).isTrue();
    assertThat(x.dom().toString()).isEqualTo("{0, 2..3}");
  }

  // Or(x + y = 4, w <= -2) woke on the event that decides x + y = 4 is satisfied, GROUND, so the
  // bounds of y did not reach x once w <= -2 had failed
  @Test
  void testDisjunctionWakesOnBoundsOfItsLastConstraint() {

    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 4);
    IntVar y = new IntVar(store, "y", 0, 4);
    IntVar w = new IntVar(store, "w", 0, 2);
    store.impose(new Or(new XplusYeqC(x, y, 4), new XlteqC(w, -2)));
    assertThat(store.consistency()).isTrue();

    store.setLevel(store.level + 1);
    y.domain.in(store.level, y, 1, 2);
    assertThat(store.consistency()).isTrue();
    assertThat(x.dom().toString()).isEqualTo("{2..3}");
  }

  /**
   * Imposes b -> x + 1 = z with b = 1, removes 3 and 4 from inside z and returns the domain of x.
   * XplusCeqZ only needs a ground variable to become satisfied, but once b is 1 its consistency()
   * prunes x on any change of z.
   */
  private static String nestedXplusCeqZPrunes(
      BiFunction<PrimitiveConstraint, IntVar, PrimitiveConstraint> reify) {

    Store store = new Store();
    IntVar b = variable(store, "b", 1);
    IntVar x = new IntVar(store, "x", 1, 4);
    IntVar z = new IntVar(store, "z", 2, 5);
    store.impose(reify.apply(new XplusCeqZ(x, 1, z), b));
    assertThat(store.consistency()).isTrue();

    assertThat(removeValues(store, z, 3, 4)).isTrue();
    return x.dom().toString();
  }

  @Test
  void testAlldifferentExceptZeroChecksMatchingWhenZeroIsRemoved() {

    // Three variables over {3, 4} cannot all differ, so x2 has to take 0 as soon as x1 loses 6,
    // which does not fix x1. Once 0 is removed as well, the constraint fails.
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 3, 4), variable(store, "x1", 3, 4, 6), variable(store, "x2", 0, 3, 4)
    };
    store.impose(new AlldifferentExceptZero(x));
    assertThat(store.consistency()).isTrue();
    assertThat(x[2].dom().toString()).isEqualTo("{0, 3..4}");

    assertThat(removeValues(store, x[1], 6)).isTrue();
    assertThat(x[2].singleton(0)).isTrue();
  }

  @Test
  void testAlldifferentExceptChecksMatchingWhenAVariableLosesAValue() {

    // Except 4: once x1 loses 7, x0 and x1 take 1 and 5 between them, so x2 loses 1 and 5. Neither
    // change fixes a variable, so the filtering must run on other domain changes; removing 6 and 4
    // from x2 then fails.
    Store store = new Store();
    IntDomain s = new IntervalDomain(4, 4);
    IntVar[] x = {
      variable(store, "x0", 1, 5), variable(store, "x1", 1, 5, 7), variable(store, "x2", 1, 4, 5, 6)
    };
    store.impose(new AlldifferentExcept(x, s));
    assertThat(store.consistency()).isTrue();
    assertThat(x[2].dom().toString()).isEqualTo("{1, 4..6}");

    assertThat(removeValues(store, x[1], 7)).isTrue();
    assertThat(x[2].dom().toString()).isEqualTo("{4, 6}");
    assertThat(removeValues(store, x[2], 6)).isTrue();
    assertThat(x[2].singleton(4)).isTrue();
  }

  @Test
  void testAlldifferentExceptZeroPrunesWithZeroAsJoker() {

    // x0 and x1 take 1 and 2 between them, so x2 can only take the exception value 0.
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 1, 2), new IntVar(store, "x1", 1, 2), new IntVar(store, "x2", 0, 2)
    };
    store.impose(new AlldifferentExceptZero(x));
    assertThat(store.consistency()).isTrue();

    assertThat(x[2].singleton(0)).isTrue();
  }

  @Test
  void testAlldifferentExceptPrunesAHallSetFromVariablesWithoutExceptionValues() {

    // Except 0: x0, x1 over {1, 2} are a Hall set, so x2 (without 0) loses 1 and 2, while x3
    // keeps 0 and 3 and loses 1 and 2.
    Store store = new Store();
    IntVar[] x = {
      variable(store, "x0", 1, 2),
      variable(store, "x1", 1, 2),
      variable(store, "x2", 1, 2, 3, 4),
      variable(store, "x3", 0, 1, 2, 3)
    };
    store.impose(new AlldifferentExcept(x, new IntervalDomain(0, 0)));
    assertThat(store.consistency()).isTrue();

    assertThat(x[2].dom().toString()).isEqualTo("{3..4}");
    assertThat(x[3].dom().toString()).isEqualTo("{0, 3}");
  }

  @Test
  void testAlldifferentChecksMatchingWhenAVariableLosesAValue() {

    // Three variables end up over {1, 5} and cannot all differ. Neither change fixes a variable,
    // so the matching check must run on other domain changes.
    Store store = new Store();
    IntVar[] x = {
      variable(store, "x0", 1, 5), variable(store, "x1", 1, 5), variable(store, "x2", 1, 4, 5, 6)
    };
    store.impose(new Alldifferent(x));
    assertThat(store.consistency()).isTrue();

    assertThat(removeValues(store, x[2], 6)).isTrue();
    assertThat(removeValues(store, x[2], 4)).isFalse();
  }

  @Test
  void testAlldifferentFailsAtEveryInfeasibleNode() {

    // Random dives with backtracking that remove values and narrow bounds without fixing
    // variables: Alldifferent must fail exactly when its variables cannot all take different
    // values, at every node, also after its matching was repaired on deeper levels.
    Random random = new Random(11);
    int infeasible = 0;
    for (int instance = 0; instance < 3000; instance++) {
      Store store = new Store();
      int n = 2 + random.nextInt(5);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i);
        for (int v = 0; v <= n + 1; v++) {
          if (random.nextInt(3) > 0) {
            x[i].addDom(v, v);
          }
        }
        if (x[i].getSize() == 0) {
          x[i].addDom(0, 0);
        }
      }
      store.impose(new Alldifferent(x));
      boolean ok = store.consistency();
      assertThat(ok).as(Arrays.toString(x)).isEqualTo(hasDistinctAssignment(x, 0, new int[n]));
      for (int step = 0; ok && step < 3 * n; step++) {
        if (random.nextInt(4) == 0 && store.level > 0) {
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
          continue;
        }
        IntVar v = x[random.nextInt(n)];
        if (v.singleton()) {
          continue;
        }
        String before = Arrays.toString(x);
        store.setLevel(store.level + 1);
        int value = v.min() + random.nextInt(v.max() - v.min() + 1);
        switch (random.nextInt(3)) {
          case 0 -> v.domain.inComplement(store.level, v, value);
          case 1 -> v.domain.inMax(store.level, v, Math.max(value, v.min()));
          default -> v.domain.inMin(store.level, v, Math.min(value, v.max()));
        }
        boolean consistent = store.consistency();
        boolean feasible = consistent && hasDistinctAssignment(x, 0, new int[n]);
        if (!consistent) {
          infeasible++;
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
        } else {
          assertThat(feasible).as(before + " then " + v + " gives " + Arrays.toString(x)).isTrue();
        }
      }
    }
    assertThat(infeasible).isPositive();
  }

  private static boolean hasDistinctAssignment(IntVar[] x, int i, int[] values) {
    if (i == x.length) {
      return true;
    }
    for (ValueEnumeration e = x[i].dom().valueEnumeration(); e.hasMoreElements(); ) {
      int value = e.nextElement();
      boolean used = false;
      for (int j = 0; j < i; j++) {
        used |= values[j] == value;
      }
      if (!used) {
        values[i] = value;
        if (hasDistinctAssignment(x, i + 1, values)) {
          return true;
        }
      }
    }
    return false;
  }

  @Test
  void testNetworkFlowWakesOnRemovedValue() {

    // The flows around a cycle of three nodes are equal; removing 3 from inside one of them must
    // remove it from the other two.
    Store store = new Store();
    IntVar[] flow = {
      new IntVar(store, "x0", 0, 5), new IntVar(store, "x1", 0, 5), new IntVar(store, "x2", 0, 5)
    };
    NetworkBuilder net = new NetworkBuilder(new IntVar(store, "cost", 0, 0));
    Node[] nodes = {net.addNode("n0", 0), net.addNode("n1", 0), net.addNode("n2", 0)};
    for (int i = 0; i < nodes.length; i++) {
      net.addArc(nodes[i], nodes[(i + 1) % nodes.length], 0, flow[i]);
    }
    store.impose(net.build());
    assertThat(store.consistency()).isTrue();

    assertThat(removeValues(store, flow[0], 3)).isTrue();
    assertThat(flow[1].dom().toString()).isEqualTo("{0..2, 4..5}");
    assertThat(flow[2].dom().toString()).isEqualTo("{0..2, 4..5}");
  }

  @Test
  void testSubcircuitAppliesDominanceAtFixpoint() {

    // x2 = 1 and x3 in {1, 2}; x0 = 3, x1 = 4 would give the two cycles 0-2-0 and 1-3-1, which
    // the strongly connected components do not detect, but dominance from node 0 does.
    Store store = new Store();
    IntVar[] x = {
      variable(store, "x0", 2, 3, 4),
      variable(store, "x1", 1, 3, 4),
      variable(store, "x2", 1),
      variable(store, "x3", 1, 2)
    };
    store.impose(new Subcircuit(x));
    assertThat(store.consistency()).isTrue();

    assertThat(x[0].dom().toString()).isEqualTo("4");
    assertThat(x[1].dom().toString()).isEqualTo("3");
  }

  @Test
  void testValuePrecedeForcesFirstWhenLaterValueIsFixed() {

    // 0 must precede 2; only x0 can take 0, so fixing x1 = 2 must fix x0 = 0. Before, the first
    // occurrence of 2 was not recorded when no second position for 0 existed.
    Store store = new Store();
    IntVar[] x = {new IntVar(store, "x0", 0, 2), new IntVar(store, "x1", 1, 2)};
    store.impose(new ValuePrecede(0, 2, x));
    assertThat(store.consistency()).isTrue();
    assertThat(x[0].dom().toString()).isEqualTo("{0..1}");

    store.setLevel(store.level + 1);
    x[1].domain.in(store.level, x[1], 2, 2);
    assertThat(store.consistency()).isTrue();
    assertThat(x[0].dom().toString()).isEqualTo("0");
  }

  @Test
  void testSeqPrecedeChainFixesWholeChain() {

    // x3 = 3 needs 1 and 2 before it, and 2 can only be at x1, so 1 can only be at x0. The
    // backward pass overwrote the latest positions of values with domain minima.
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", -1, 1),
      new IntVar(store, "x1", -1, 2),
      new IntVar(store, "x2", -1, 1),
      variable(store, "x3", 3)
    };
    store.impose(new SeqPrecedeChain(x));
    assertThat(store.consistency()).isTrue();

    assertThat(x[0].dom().toString()).isEqualTo("1");
    assertThat(x[1].dom().toString()).isEqualTo("2");
  }

  @Test
  void testSortBoundsYFromBothMatchings() {

    // y2 is the largest value, at least x2 = 3, and the hole moves it to 4, which some other x
    // must take; x2 then sits at y0 or y1, so y1 >= 3. The sorted minima of x alone give y1 >= 1.
    Store store = new Store();
    IntVar[] x = {
      variable(store, "x0", 1, 2, 4), new IntVar(store, "x1", 0, 4), new IntVar(store, "x2", 3, 3)
    };
    IntVar[] y = {
      new IntVar(store, "y0", 0, 3),
      new IntVar(store, "y1", 0, 4),
      variable(store, "y2", 0, 1, 2, 4)
    };
    store.impose(new Sort(x, y));
    assertThat(store.consistency()).isTrue();

    assertThat(y[2].dom().toString()).isEqualTo("4");
    assertThat(y[1].dom().toString()).isEqualTo("{3..4}");
    assertThat(y[0].dom().toString()).isEqualTo("{0..3}");
  }

  @Test
  void testSortNarrowsXToThePositionsOfItsComponent() {

    // y = [0, 5, 5] and x0 can only be 0, so x1 and x2 take the two 5s
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 0, 1), new IntVar(store, "x1", 0, 9), new IntVar(store, "x2", 0, 9)
    };
    IntVar[] y = {
      new IntVar(store, "y0", 0, 0), new IntVar(store, "y1", 5, 5), new IntVar(store, "y2", 5, 5)
    };
    store.impose(new Sort(x, y));
    assertThat(store.consistency()).isTrue();

    assertThat(x[0].dom().toString()).isEqualTo("0");
    assertThat(x[1].dom().toString()).isEqualTo("5");
    assertThat(x[2].dom().toString()).isEqualTo("5");
  }

  @Test
  void testSortPermutationBoundsYByForcedPositions() {

    // z1 in 1..2 puts x1 >= 3 at position 1 or 2 (numbered from 1), so y1 and y2 are at least 3
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 0, 4), new IntVar(store, "x1", 3, 4), new IntVar(store, "x2", 0, 4)
    };
    IntVar[] y = {
      new IntVar(store, "y0", 0, 4), new IntVar(store, "y1", 0, 4), new IntVar(store, "y2", 0, 4)
    };
    IntVar[] z = {
      new IntVar(store, "z0", 1, 3), new IntVar(store, "z1", 1, 2), new IntVar(store, "z2", 1, 3)
    };
    store.impose(new Sort(x, y, z, 1));
    assertThat(store.consistency()).isTrue();

    assertThat(y[0].dom().toString()).isEqualTo("{0..4}");
    assertThat(y[1].dom().toString()).isEqualTo("{3..4}");
    assertThat(y[2].dom().toString()).isEqualTo("{3..4}");

    // fixing z1 = 1 makes x1 the smallest value
    store.setLevel(store.level + 1);
    z[1].domain.in(store.level, z[1], 1, 1);
    assertThat(store.consistency()).isTrue();
    assertThat(y[0].dom().toString()).isEqualTo("{3..4}");
    assertThat(x[0].dom().toString()).isEqualTo("{3..4}");
    assertThat(x[2].dom().toString()).isEqualTo("{3..4}");
  }

  @Test
  void testNetworkFlowPropagatesItsOwnPruningOfACounter() {

    // Value 0 must occur 0 or 3 times; x1 = 1 rules out 3, so the network prunes the counter to 0
    // and must then remove 0 from x0 and x2 in the same propagation.
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 0, 1), new IntVar(store, "x1", 1, 1), new IntVar(store, "x2", 0, 1)
    };
    IntVar[] counter = {variable(store, "h", 0, 3)};
    IntVar cost = new IntVar(store, "cost", 0, 6);
    store.imposeDecomposition(
        new SoftGCC(
            x,
            counter,
            new int[] {0},
            new int[] {0},
            new int[] {2},
            cost,
            ViolationMeasure.VALUE_BASED));

    assertThat(store.consistency()).isTrue();
    assertThat(counter[0].dom().toString()).isEqualTo("0");
    assertThat(x[0].dom().toString()).isEqualTo("1");
    assertThat(x[2].dom().toString()).isEqualTo("1");
  }

  @Test
  void testSeqPrecedeChainOfValuesIsStrongerThanPairs() {

    // Walsh's example with values 5, 3, 8, 9 in the roles of 1..4: every pair of consecutive
    // values is consistent, but the chain forbids x1 = 5 (then 3 would come after 8 in x2).
    Store store = new Store();
    IntVar[] x = {
      variable(store, "x0", 5),
      variable(store, "x1", 3, 5),
      variable(store, "x2", 5, 8),
      variable(store, "x3", 8, 9)
    };
    store.impose(new SeqPrecedeChain(x, new int[] {5, 3, 8, 9}));
    assertThat(store.consistency()).isTrue();

    assertThat(x[1].dom().toString()).isEqualTo("3");
  }

  private static IntVar variable(Store store, String name, int... values) {
    IntVar v = new IntVar(store, name);
    for (int value : values) {
      v.addDom(value, value);
    }
    return v;
  }

  /** Removes the values from v at a new store level, as search would, and propagates. */
  private static boolean removeValues(Store store, IntVar v, int... values) {
    store.setLevel(store.level + 1);
    for (int value : values) {
      v.domain.inComplement(store.level, v, value);
    }
    return store.consistency();
  }

  /** Tasks of length p on some machines, as the inter-distance global or as a cumulative. */
  private static IntVar[] equalLengthTasks(
      Store store, int[] lo, int[] hi, int p, int machines, boolean global) {
    int n = lo.length;
    IntVar[] x = new IntVar[n];
    IntVar[] d = new IntVar[n];
    IntVar[] r = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, lo[i], hi[i]);
      d[i] = new IntVar(store, p, p);
      r[i] = new IntVar(store, 1, 1);
    }
    IntVar limit = new IntVar(store, machines, machines);
    if (machines == 1) {
      store.impose(global ? new InterDistance(x, p) : new CumulativeUnary(x, d, r, limit, true));
    } else {
      store.impose(
          global ? new MultiInterDistance(x, machines, p) : new Cumulative(x, d, r, limit));
    }
    return x;
  }

  @Test
  void testInterDistanceIsBoundsConsistentWhereTheUnaryResourceIsNot() {

    // x3 = 9 or 10 leaves x0 in 8..12 and x2 in 9..14 both at 12 or later, 3 apart: impossible
    int[] lo = {6, 0, 9, 9, 5};
    int[] hi = {12, 3, 14, 16, 6};
    Store store = new Store();
    IntVar[] x = equalLengthTasks(store, lo, hi, 3, 1, true);
    assertThat(store.consistency()).isTrue();
    assertThat(x[3].min()).isEqualTo(11);

    Store unaryStore = new Store();
    IntVar[] y = equalLengthTasks(unaryStore, lo, hi, 3, 1, false);
    assertThat(unaryStore.consistency()).isTrue();
    assertThat(y[3].min()).isEqualTo(9);
  }

  @Test
  void testInterDistanceRemovesTheNeighbourhoodOfAFixedTask() {

    Store store = new Store();
    IntVar[] x = equalLengthTasks(store, new int[] {5, 0, 0}, new int[] {5, 20, 20}, 3, 1, true);
    assertThat(store.consistency()).isTrue();
    assertThat(x[1].dom().toString()).isEqualTo("{0..2, 8..20}");
    assertThat(x[2].dom().toString()).isEqualTo("{0..2, 8..20}");
  }

  @Test
  void testMultiInterDistanceIsStrongerThanCumulative() {

    // two machines, tasks of length 4
    int[] lo = {8, 6, 9, 9, 8};
    int[] hi = {12, 10, 10, 16, 13};
    Store store = new Store();
    IntVar[] x = equalLengthTasks(store, lo, hi, 4, 2, true);
    assertThat(store.consistency()).isTrue();
    assertThat(x[3].min()).isEqualTo(14);
    assertThat(x[1].max()).isEqualTo(8);

    Store cumulativeStore = new Store();
    IntVar[] y = equalLengthTasks(cumulativeStore, lo, hi, 4, 2, false);
    assertThat(cumulativeStore.consistency()).isTrue();
    assertThat(y[3].min()).isEqualTo(12);
  }
}
