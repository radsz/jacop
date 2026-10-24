/*
 * SetRelationsTest.java
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

import org.jacop.constraints.Not;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.set.constraints.AinS;
import org.jacop.set.constraints.SinA;
import org.jacop.set.constraints.XeqA;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;
import org.junit.jupiter.api.Test;

/** Regression tests of the set relation constraints (inclusion, equality, order, membership). */
class SetRelationsTest {

  /** A set variable whose domain is the single value {@code values}. */
  private static SetVar groundSetVar(Store store, String name, int... values) {
    return new SetVar(store, name, new BoundSetDomain(dom(values), dom(values)));
  }

  @Test
  void testGroundSetVarWithWiderCardinalityUnderNotXeqA() {
    Store store = new Store();
    // a = {1} is ground, but it is created with a cardinality range 0..1
    SetVar a = new SetVar(store, "a", new BoundSetDomain(dom(1), dom(1), new IntervalDomain(0, 1)));
    IntVar x = new IntVar(store, "x", 1, 1);
    assertThat(a.domain.card().min()).isEqualTo(1);

    store.impose(new Not(new XeqA(x, a)));
    assertThat(store.consistency()).isFalse();

    // a = {} is ground; satisfied() must not ask for the minimum of the empty glb
    Store store2 = new Store();
    SetVar e =
        new SetVar(store2, "e", new BoundSetDomain(dom(), dom(1, 3), new IntervalDomain(0, 1)));
    e.domain.inValue(store2.level, e, dom());
    IntVar y = new IntVar(store2, "y", 0, 0);
    XeqA xeqa = new XeqA(y, e);
    assertThat(xeqa.satisfied()).isFalse();
    assertThat(xeqa.notSatisfied()).isTrue();
  }

  @Test
  void testAinSSatisfiedMeansInclusion() {
    Store store = new Store();
    SetVar a = groundSetVar(store, "a", 5);
    // {5} is a subset of {0, 2, 5} although it is lexicographically larger
    assertThat(new AinS(a, dom(0, 2, 5)).satisfied()).isTrue();
    // {1, 3, 4, 5} is not a subset of {1, 4} although it is lexicographically smaller
    SetVar b = groundSetVar(store, "b", 1, 3, 4, 5);
    assertThat(new AinS(b, dom(1, 4), true).satisfied()).isFalse();
  }

  @Test
  void testAinSStrictFailsWhenTheSetEqualsTheGlb() {
    Store store = new Store();
    SetVar a = groundSetVar(store, "a", 1, 3, 4, 5);
    store.impose(new AinS(a, dom(1, 3, 4, 5), true));
    assertThat(store.consistency()).isFalse();
  }

  @Test
  void testSinASatisfiedMeansInclusion() {
    Store store = new Store();
    // {3} is not a subset of {} although {} is lexicographically smaller
    assertThat(new SinA(dom(3), groundSetVar(store, "a")).satisfied()).isFalse();
    assertThat(new SinA(dom(3), groundSetVar(store, "b", 3, 4), true).satisfied()).isTrue();
  }

  @Test
  void testNotSinAStrictMakesTheVariableEqualToTheSet() {
    Store store = new Store();
    SetVar a = new SetVar(store, "a", new BoundSetDomain(dom(3), dom(3, 4)));
    // not ({3} strictly in a) with 3 in a leaves only a = {3}
    store.impose(new Not(new SinA(dom(3), a, true)));
    assertThat(store.consistency()).isTrue();
    assertThat(a.domain.singleton(dom(3))).isTrue();
  }

  private static IntDomain dom(int... values) {
    IntervalDomain d = new IntervalDomain();
    for (int v : values) {
      d.unionAdapt(v, v);
    }
    return d;
  }
}
