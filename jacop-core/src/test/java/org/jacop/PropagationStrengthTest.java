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
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusYeqZ;
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
