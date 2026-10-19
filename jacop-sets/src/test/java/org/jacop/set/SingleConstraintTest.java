/*
 * SingleConstraintTest.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.set;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Arrays;
import java.util.Random;
import java.util.function.Function;
import org.jacop.constraints.Constraint;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.constraints.CardAeqX;
import org.jacop.set.constraints.PartitionSet;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;
import org.junit.jupiter.api.Test;

/** Tests of single set constraints and of the set domain. */
class SingleConstraintTest {
  @Test
  void testBoundSetDomainInFailsWhenGlbLeavesLub() {

    Store store = new Store();
    SetVar x =
        new SetVar(
            store, "x", new BoundSetDomain(new IntervalDomain(1, 1), new IntervalDomain(1, 4)));
    store.setLevel(1);

    boolean failed = false;
    try {
      // The new lub {2..3} does not contain the current glb {1}.
      x.domain.in(1, x, new IntervalDomain(), new IntervalDomain(2, 3));
    } catch (FailException e) {
      failed = true;
    }
    assertThat(failed).isTrue();
  }

  @Test
  void testBoundSetDomainInUpdatesCardinality() {

    Store store = new Store();
    SetVar x =
        new SetVar(
            store, "x", new BoundSetDomain(new IntervalDomain(1, 1), new IntervalDomain(1, 4)));
    store.setLevel(1);
    x.domain.in(1, x, new IntervalDomain(1, 2), new IntervalDomain(1, 3));

    assertThat(x.dom().card().eq(new IntervalDomain(2, 3))).isTrue();

    // At the same level: glb {1..2} already has the maximal cardinality 2, so x = {1..2}.
    x.domain.inCardinality(1, x, 2, 2);
    store.setLevel(2);
    SetVar y =
        new SetVar(
            store, "y", new BoundSetDomain(new IntervalDomain(5, 5), new IntervalDomain(5, 7)));
    y.domain.inCardinality(2, y, 2, 2);
    y.domain.in(2, y, new IntervalDomain(5, 6), new IntervalDomain(5, 7));

    assertThat(x.singleton()).isTrue();
    assertThat(y.singleton()).isTrue();
    assertThat(y.dom().glb().eq(new IntervalDomain(5, 6))).isTrue();
  }

  @Test
  void testPartitionSetWakesOnCardinalityChange() {

    // Two sets of cardinality 1 cannot partition {1..4}. Only the cardinalities change, which
    // generates a CARDINALITY_EVENT that must reach constraints registered for ANY.
    Store store = new Store();
    SetVar x = new SetVar(store, "x", 1, 4);
    SetVar y = new SetVar(store, "y", 1, 4);
    IntVar card = new IntVar(store, "card", 0, 4);
    store.impose(new PartitionSet(new SetVar[] {x, y}, new IntervalDomain(1, 4)));
    store.impose(new CardAeqX(x, card));
    store.impose(new CardAeqX(y, card));
    assertThat(store.consistency()).isTrue();

    store.setLevel(1);
    card.domain.in(1, card, 1, 1);

    assertThat(store.consistency()).isFalse();
  }

  /**
   * Imposes many random instances of a constraint and counts those for which a second call of
   * consistency() after store.consistency() still changes a domain or fails.
   */
  private int countNotAtFixpoint(Random random, Function<Store, Constraint> factory) {

    int notAtFixpoint = 0;
    for (int trial = 0; trial < 3000; trial++) {
      Store store = new Store();
      Constraint constraint = factory.apply(store);
      if (constraint == null) {
        continue;
      }
      store.impose(constraint);
      if (!store.consistency()) {
        continue;
      }
      String before = domains(constraint);
      store.setLevel(store.level + 1);
      String after;
      try {
        constraint.consistency(store);
        after = domains(constraint);
      } catch (FailException e) {
        after = "fail";
      }
      if (!after.equals(before)) {
        notAtFixpoint++;
      }
    }
    return notAtFixpoint;
  }

  private static String domains(Constraint constraint) {
    return Arrays.toString(constraint.arguments().stream().map(Var::toString).sorted().toArray());
  }

  private static SetVar randomSetVar(Store store, Random random, String name, int max) {
    IntDomain lub = randomSet(random, 1, max, 0.7);
    IntDomain glb = lub.intersect(randomSet(random, 1, max, 0.25));
    SetVar s = new SetVar(store, name, new BoundSetDomain(glb, lub));
    if (random.nextBoolean()) {
      int min = glb.getSize() + random.nextInt(lub.getSize() - glb.getSize() + 1);
      s.domain.inCardinality(store.level, s, min, min + random.nextInt(2));
    }
    return s;
  }

  private static IntDomain randomSet(Random random, int min, int max, double probability) {
    IntervalDomain d = new IntervalDomain();
    for (int v = min; v <= max; v++) {
      if (random.nextDouble() < probability) {
        d.unionAdapt(v, v);
      }
    }
    return d;
  }

  private static IntDomain dom(int... values) {
    IntervalDomain d = new IntervalDomain();
    for (int v : values) {
      d.unionAdapt(v, v);
    }
    return d;
  }
}
