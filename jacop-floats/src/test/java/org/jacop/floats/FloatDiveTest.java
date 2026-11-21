/*
 * FloatDiveTest.java
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

package org.jacop.floats;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.jacop.core.FailException;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.FloatDive;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/** Checks the sampling dives of float optimisation ({@link FloatDive}). */
class FloatDiveTest {

  private double precision;

  @BeforeEach
  void setPrecision() {
    precision = FloatDomain.precision();
    FloatDomain.setPrecision(1e-6);
  }

  @AfterEach
  void restorePrecision() {
    FloatDomain.setPrecision(precision);
  }

  @Test
  void diveNarrowsEveryVariableAndLeavesTheLevelsToTheCaller() {
    Store store = new Store();
    FloatVar x = new FloatVar(store, "x", 0, 1);
    FloatVar y = new FloatVar(store, "y", 0, 1);
    FloatVar z = new FloatVar(store, "z", 0, 1);
    // y = 1 - x and z = x * y: the dive samples x only, propagation narrows y and z
    store.impose(new LinearFloat(new FloatVar[] {x, y}, new double[] {1, 1}, "==", 1));
    store.impose(new PmulQeqR(x, y, z));
    assertTrue(store.consistency());
    int base = store.level;
    FloatDive dive = new FloatDive(store, new Var[] {x, y, z}, null, 7);
    assertTrue(dive.dive());
    assertTrue(x.singleton() && y.singleton() && z.singleton(), x + " " + y + " " + z);
    assertTrue(Math.abs(x.min() + y.min() - 1) < 1e-5);
    assertTrue(store.level > base);
    while (store.level > base) {
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
    }
    assertEquals(0, x.min());
    assertEquals(1, x.max());
    assertEquals(1, dive.dives());
  }

  @Test
  void divesUnderTheCostBoundReachTheMinimum() {
    // cost = (x - 0.3)^2 + (y - 0.7)^2 + (w - 0.2)^2, minimum 0 at (0.3, 0.7, 0.2)
    Store store = new Store();
    FloatVar[] v = new FloatVar[3];
    FloatVar[] squares = new FloatVar[3];
    double[] target = {0.3, 0.7, 0.2};
    for (int i = 0; i < 3; i++) {
      v[i] = new FloatVar(store, "v" + i, 0, 1);
      FloatVar d = new FloatVar(store, "d" + i, -1, 1);
      store.impose(
          new LinearFloat(new FloatVar[] {v[i], d}, new double[] {1, -1}, "==", target[i]));
      squares[i] = new FloatVar(store, "s" + i, 0, 1);
      store.impose(new PmulQeqR(d, d, squares[i]));
    }
    FloatVar cost = new FloatVar(store, "cost", 0, 3);
    store.impose(new LinearFloat(squares, new double[] {1, 1, 1}, "==", cost));
    assertTrue(store.consistency());
    int base = store.level;
    FloatDive dive = new FloatDive(store, v, cost, 20261118L);
    double best = Double.MAX_VALUE;
    for (int d = 0; d < 2000; d++) {
      store.setLevel(base + 1);
      boolean better = false;
      try {
        if (best != Double.MAX_VALUE) {
          cost.domain.inMax(store.level, cost, best - 1e-6);
        }
        if (store.consistency() && dive.dive()) {
          better = true;
          best = cost.max();
        }
      } catch (FailException _) {
        store.clearChanged();
      }
      while (store.level > base) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }
      if (better) {
        dive.improved();
      } else {
        dive.failed();
      }
    }
    // uniform samples alone get within about 0.01 in 2000 dives; the local ones much closer
    assertTrue(best < 1e-4, "best " + best);
    assertTrue(dive.improvements() > 5);
  }
}
