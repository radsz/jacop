/*
 * SymmetricAlldifferentTest.java
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

import java.util.Random;
import org.jacop.constraints.SymmetricAlldifferent;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/** Brute-force checks of {@link SymmetricAlldifferent}: domain consistency and solution counts. */
class SymmetricAlldifferentTest {

  // -Dsymmetricalldifferent.instances=20000 for a longer run
  private static final int INSTANCES = Integer.getInteger("symmetricalldifferent.instances", 500);

  /** Three variables that may each take either of the other two form an odd cycle: no solution. */
  @Test
  void oddCycleFailsAtTheRoot() {
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x1", domain(2, 3)),
      new IntVar(store, "x2", domain(1, 3)),
      new IntVar(store, "x3", domain(1, 2))
    };
    store.impose(new SymmetricAlldifferent(x, 1));
    assertFalse(store.consistency());
  }

  /** Fixed points are allowed: x[1] = 1, and then x[2], x[3] swap or are both fixed points. */
  @Test
  void fixedPointIsKept() {
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x1", 1, 2), new IntVar(store, "x2", 2, 3), new IntVar(store, "x3", 1, 3)
    };
    store.impose(new SymmetricAlldifferent(x, 1));
    store.consistency();
    assertEquals("[1, {2..3}, {2..3}]", values(x));
  }

  /**
   * Random domains over the indexes and a little outside, and random dives: after every decision
   * the propagator keeps exactly the values some solution of the domains before it uses, and the
   * search finds every solution once.
   */
  @Test
  void domainConsistentOnRandomDives() {
    Random rnd = new Random(7);
    for (int instance = 0; instance < INSTANCES; instance++) {
      int n = 1 + rnd.nextInt(7);
      int offset = rnd.nextInt(3) - 1;
      int[][] doms = new int[n][];
      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        IntervalDomain d = new IntervalDomain();
        for (int v = offset - 1; v <= offset + n; v++) {
          if (rnd.nextInt(3) > 0) {
            d.unionAdapt(v, v);
          }
        }
        if (d.isEmpty()) {
          d.unionAdapt(offset + i, offset + i);
        }
        x[i] = new IntVar(store, "x" + i, d);
      }
      store.impose(new SymmetricAlldifferent(x, offset));
      String where = "instance " + instance;
      if (!propagateAndCheck(store, x, offset, where)) {
        continue;
      }
      assertEquals(count(snapshot(x), offset), solutions(store, x), where);
      for (int step = 0; step < 2 * n; step++) {
        store.setLevel(store.level + 1);
        IntVar v = x[rnd.nextInt(n)];
        if (v.singleton()) {
          continue;
        }
        int value = v.dom().getElementAt(rnd.nextInt(v.getSize()));
        try {
          if (rnd.nextBoolean()) {
            v.domain.in(store.level, v, value, value);
          } else {
            v.domain.inComplement(store.level, v, value);
          }
        } catch (FailException e) {
          break;
        }
        if (!propagateAndCheck(store, x, offset, where + " step " + step)) {
          break;
        }
      }
    }
  }

  /**
   * The light mode, which only channels x[i] = j with x[j] = i and checks that a perfect matching
   * exists, fails exactly when there is no solution and finds every solution once.
   */
  @Test
  void matchingModeFindsEverySolution() {
    Random rnd = new Random(11);
    for (int instance = 0; instance < INSTANCES; instance++) {
      int n = 1 + rnd.nextInt(7);
      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        IntervalDomain d = new IntervalDomain();
        for (int v = 0; v <= n; v++) {
          if (rnd.nextInt(3) > 0) {
            d.unionAdapt(v, v);
          }
        }
        if (d.isEmpty()) {
          d.unionAdapt(i, i);
        }
        x[i] = new IntVar(store, "x" + i, d);
      }
      long expected = count(snapshot(x), 0);
      store.impose(new SymmetricAlldifferent(x, 0, false));
      String where = "instance " + instance;
      if (!store.consistency()) {
        assertEquals(0, expected, where + " failed with a solution");
        continue;
      }
      for (IntVar v : x) {
        for (int k = 0; k < v.getSize(); k++) {
          int j = v.dom().getElementAt(k);
          assertEquals(true, x[j].dom().contains(indexOf(x, v)), where + " channel " + v);
        }
      }
      assertEquals(expected, solutions(store, x), where);
    }
  }

  private static int indexOf(IntVar[] x, IntVar v) {
    for (int i = 0; i < x.length; i++) {
      if (x[i] == v) {
        return i;
      }
    }
    return -1;
  }

  // runs consistency and compares it with the supports of the domains before it
  private static boolean propagateAndCheck(Store store, IntVar[] x, int offset, String where) {
    int[][] before = snapshot(x);
    boolean[][] supported = new boolean[x.length][x.length];
    boolean any = supports(before, offset, supported);
    if (!store.consistency()) {
      assertFalse(any, where + " failed with a solution");
      return false;
    }
    assertEquals(true, any, where + " missed a failure");
    for (int i = 0; i < x.length; i++) {
      IntervalDomain expected = new IntervalDomain();
      for (int j = 0; j < x.length; j++) {
        if (supported[i][j]) {
          expected.unionAdapt(j + offset, j + offset);
        }
      }
      assertEquals(expected.toString(), x[i].dom().toString(), where + " " + x[i]);
    }
    return true;
  }

  private static int[][] snapshot(IntVar[] x) {
    int[][] d = new int[x.length][];
    for (int i = 0; i < x.length; i++) {
      d[i] = new int[x[i].getSize()];
      for (int k = 0; k < d[i].length; k++) {
        d[i][k] = x[i].dom().getElementAt(k);
      }
    }
    return d;
  }

  private static boolean supports(int[][] doms, int offset, boolean[][] supported) {
    int n = doms.length;
    boolean[] found = {false};
    enumerate(
        new int[n],
        doms,
        offset,
        t -> {
          found[0] = true;
          for (int i = 0; i < n; i++) {
            supported[i][t[i]] = true;
          }
        });
    return found[0];
  }

  private static long count(int[][] doms, int offset) {
    long[] c = {0};
    enumerate(new int[doms.length], doms, offset, t -> c[0]++);
    return c[0];
  }

  // every involution t of 0..n-1 with t[i] + offset in doms[i] and i + offset in doms[t[i]]
  private static void enumerate(
      int[] t, int[][] doms, int offset, java.util.function.Consumer<int[]> out) {
    java.util.Arrays.fill(t, -1);
    pair(0, t, doms, offset, out);
  }

  private static void pair(
      int i, int[] t, int[][] doms, int offset, java.util.function.Consumer<int[]> out) {
    int n = t.length;
    while (i < n && t[i] >= 0) {
      i++;
    }
    if (i == n) {
      out.accept(t);
      return;
    }
    for (int j = i; j < n; j++) {
      if (t[j] < 0 && has(doms[i], j + offset) && has(doms[j], i + offset)) {
        t[i] = j;
        t[j] = i;
        pair(i + 1, t, doms, offset, out);
        t[i] = -1;
        t[j] = -1;
      }
    }
  }

  private static boolean has(int[] dom, int v) {
    for (int w : dom) {
      if (w == v) {
        return true;
      }
    }
    return false;
  }

  private static long solutions(Store store, IntVar[] x) {
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()));
    return search.getSolutionListener().solutionsNo();
  }

  private static IntDomain domain(int a, int b) {
    IntervalDomain d = new IntervalDomain(a, a);
    d.unionAdapt(b, b);
    return d;
  }

  private static String values(IntVar[] x) {
    StringBuilder s = new StringBuilder("[");
    for (int i = 0; i < x.length; i++) {
      s.append(i > 0 ? ", " : "").append(x[i].dom());
    }
    return s.append(']').toString();
  }
}
