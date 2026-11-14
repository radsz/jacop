/*
 * AccumulatedFailureCountTest.java
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

package org.jacop.search;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Checks that accumulated failure count (AFC) weights decay globally: at every failure all weights
 * are multiplied by the decay factor and the failing constraint gets one more.
 */
class AccumulatedFailureCountTest {

  private static final class Model {
    final Store store = new Store();
    final IntVar[] x = new IntVar[4];
    final XneqY[] c = new XneqY[2];

    Model(double decay) {
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 1);
      }
      for (int i = 0; i < c.length; i++) {
        c[i] = new XneqY(x[2 * i], x[2 * i + 1]);
        store.impose(c[i]);
      }
      assertTrue(store.consistency());
      new AfcMax<IntVar>(store, decay);
    }

    /** Makes constraint i fail once, in a search level that is then removed. */
    void fail(int i) {
      store.setLevel(store.level + 1);
      x[2 * i].domain.in(store.level, x[2 * i], 0, 0);
      x[2 * i + 1].domain.in(store.level, x[2 * i + 1], 0, 0);
      assertFalse(store.consistency());
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
    }
  }

  private static void failAndCompare(double decay, int[] failures) {
    Model model = new Model(decay);
    double[] expected = {1.0d, 1.0d};
    for (int failing : failures) {
      model.fail(failing);
      for (int i = 0; i < expected.length; i++) {
        expected[i] = expected[i] * decay + (i == failing ? 1.0d : 0.0d);
      }
    }
    double ratio = model.c[0].afc() / model.c[1].afc();
    assertTrue(Double.isFinite(model.c[0].afc()) && Double.isFinite(model.c[1].afc()));
    assertEquals(expected[0] / expected[1], ratio, 1e-9 * expected[0] / expected[1]);
  }

  private static int[] failures(int first, int firstCount, int second, int secondCount) {
    int[] result = new int[firstCount + secondCount];
    for (int i = 0; i < result.length; i++) {
      result[i] = i < firstCount ? first : second;
    }
    return result;
  }

  @Test
  void oldFailuresWeighLessThanRecentOnes() {
    // c0 fails 100 times, then c1 fails 20 times: with decay 0.9, c1 must weigh more
    Model model = new Model(0.9d);
    for (int failing : failures(0, 100, 1, 20)) {
      model.fail(failing);
    }
    assertTrue(model.c[1].afc() > model.c[0].afc());
  }

  @Test
  void weightsFollowGlobalDecay() {
    failAndCompare(0.9d, failures(0, 100, 1, 20));
    failAndCompare(0.99d, failures(1, 7, 0, 3));
    failAndCompare(1.0d, failures(0, 5, 1, 3));
  }

  @Test
  void weightsFollowGlobalDecayAcrossRescaling() {
    // with decay 0.5 the increment passes the rescaling limit after about 67 failures
    failAndCompare(0.5d, failures(0, 150, 1, 10));
    failAndCompare(0.8d, failures(1, 300, 0, 40));
  }
}
