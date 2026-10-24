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

import java.util.function.BiFunction;
import org.jacop.constraints.AlldifferentExceptZero;
import org.jacop.constraints.Implies;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SeqPrecedeChain;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.ValuePrecede;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
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

    // Three variables over {3, 4} cannot all differ; the third one only joins the matching check
    // once 0 is removed from its domain, which does not fix it.
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 3, 4), new IntVar(store, "x1", 3, 4), variable(store, "x2", 0, 3, 4)
    };
    store.impose(new AlldifferentExceptZero(x));
    assertThat(store.consistency()).isTrue();

    assertThat(removeValues(store, x[2], 0)).isFalse();
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
}
