/*
 * DiffnSkippingTest.java
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

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.function.BiFunction;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.constraints.diffn.DiffnExaminingAll;
import org.jacop.constraints.diffn.Nooverlap;
import org.jacop.constraints.diffn.NooverlapExaminingAll;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Checks that Diffn and Nooverlap, which examine only the rectangles whose neighbourhood changed
 * and wake only on bound changes, prune exactly as when they examine every rectangle at every call:
 * on random instances, a store with the constraint and a store with the reference make the same
 * random dives with backtracking, and after each step both fail or both reach the same domains.
 */
class DiffnSkippingTest {

  /** Random instances per constraint; the {@code min} profile lowers it. */
  private static final int TRIALS = Integer.getInteger("diffn.skipping.trials", 400);

  private static final int STEPS = 80;

  /** Builds the variables of an instance in a store, the same for both stores of a trial. */
  private interface Variables {
    IntVar[] make(Store store);
  }

  @Test
  void diffnPrunesAsWhenExaminingAllRectangles() {
    rectangles(true);
  }

  @Test
  void nooverlapPrunesAsWhenExaminingAllRectangles() {
    rectangles(false);
  }

  private static void rectangles(boolean diffn) {
    long[] calls = new long[2];
    for (int t = 0; t < TRIALS; t++) {
      Random r = new Random(t);
      int n = 2 + r.nextInt(7);
      int size = 3 + r.nextInt(6);
      boolean strict = r.nextBoolean();
      long seed = r.nextLong();
      Variables vars =
          s -> {
            Random d = new Random(seed);
            IntVar[] x = new IntVar[4 * n];
            for (int i = 0; i < n; i++) {
              x[4 * i] = new IntVar(s, "x" + i, randomDomain(d, 0, size));
              x[4 * i + 1] = new IntVar(s, "y" + i, randomDomain(d, 0, size));
              int l = d.nextInt(3);
              x[4 * i + 2] = new IntVar(s, "lx" + i, l, l + d.nextInt(3));
              l = d.nextInt(3);
              x[4 * i + 3] = new IntVar(s, "ly" + i, l, l + d.nextInt(3));
            }
            return x;
          };
      long noiseSeed = r.nextLong();
      BiFunction<IntVar[], Boolean, List<Constraint>> model =
          (x, reference) -> {
            List<List<IntVar>> rects = new ArrayList<>();
            for (int i = 0; i < n; i++) {
              rects.add(List.of(x[4 * i], x[4 * i + 1], x[4 * i + 2], x[4 * i + 3]));
            }
            List<Constraint> cs = new ArrayList<>();
            if (diffn) {
              cs.add(reference ? new DiffnExaminingAll(rects, strict) : new Diffn(rects, strict));
            } else {
              cs.add(
                  reference
                      ? new NooverlapExaminingAll(rects, strict)
                      : new Nooverlap(rects, strict));
            }
            cs.addAll(noise(new Random(noiseSeed), x, 0));
            return cs;
          };
      long[] c = dive(t, vars, model);
      calls[0] += c[0];
      calls[1] += c[1];
    }
    assertThat(calls[0]).isLessThanOrEqualTo(calls[1]);
  }

  /** A few binary constraints between the variables, so that changes also come from outside. */
  private static List<Constraint> noise(Random d, IntVar[] x, int from) {
    List<Constraint> cs = new ArrayList<>();
    int k = d.nextInt(3);
    for (int j = 0; j < k; j++) {
      IntVar a = x[from + d.nextInt(x.length - from)];
      IntVar b = x[from + d.nextInt(x.length - from)];
      if (a == b) {
        continue;
      }
      switch (d.nextInt(3)) {
        case 0 -> cs.add(new XltY(a, b));
        case 1 -> cs.add(new XneqY(a, b));
        default -> cs.add(new XplusClteqZ(a, d.nextInt(3), b));
      }
    }
    return cs;
  }

  private static IntDomain randomDomain(Random d, int lo, int hi) {
    IntervalDomain dom = new IntervalDomain();
    for (int v = lo; v <= hi; v++) {
      if (d.nextInt(4) != 0) {
        dom.unionAdapt(v, v);
      }
    }
    if (dom.isEmpty()) {
      dom.unionAdapt(lo, lo);
    }
    return dom;
  }

  /**
   * Makes the same random dive in a store with the tested constraints and in one with the
   * references, and checks after each step that both failed or both have the same domains.
   *
   * @return the consistency calls of the tested store and of the reference store.
   */
  private static long[] dive(
      int trial, Variables vars, BiFunction<IntVar[], Boolean, List<Constraint>> model) {
    Store[] store = {new Store(), new Store()};
    IntVar[][] x = new IntVar[2][];
    for (int k = 0; k < 2; k++) {
      x[k] = vars.make(store[k]);
      for (Constraint c : model.apply(x[k], k == 1)) {
        store[k].impose(c);
      }
    }
    String what = "trial " + trial;
    if (!same(store, x, what + " at the root")) {
      return calls(store);
    }
    Random r = new Random(trial * 31L + 7);
    for (int step = 0; step < STEPS; step++) {
      int level = store[0].level;
      if (level > 0 && r.nextInt(4) == 0) {
        for (Store s : store) {
          s.removeLevel(level);
          s.setLevel(level - 1);
        }
        continue;
      }
      int i = r.nextInt(x[0].length);
      IntDomain d = x[0][i].dom();
      if (d.singleton()) {
        continue;
      }
      int v = d.getElementAt(r.nextInt(d.getSize()));
      int kind = r.nextInt(4);
      for (int k = 0; k < 2; k++) {
        store[k].setLevel(level + 1);
        IntVar y = x[k][i];
        switch (kind) {
          case 0 -> y.domain.in(level + 1, y, v, v);
          case 1 -> y.domain.inComplement(level + 1, y, v);
          case 2 -> y.domain.inMax(level + 1, y, v);
          default -> y.domain.inMin(level + 1, y, v);
        }
      }
      String at = what + " step " + step + " decision " + kind + " on " + x[0][i] + " value " + v;
      if (!same(store, x, at)) {
        for (Store s : store) {
          s.removeLevel(level + 1);
          s.setLevel(level);
        }
      }
    }
    return calls(store);
  }

  private static long[] calls(Store[] store) {
    return new long[] {store[0].numberConsistencyCalls, store[1].numberConsistencyCalls};
  }

  // runs consistency in both stores; false if both failed
  private static boolean same(Store[] store, IntVar[][] x, String what) {
    boolean ok0 = store[0].consistency();
    boolean ok1 = store[1].consistency();
    assertThat(ok0).as(what + ": failure").isEqualTo(ok1);
    if (!ok0) {
      return false;
    }
    for (int i = 0; i < x[0].length; i++) {
      assertThat(x[0][i].dom().toString())
          .as(what + ": " + x[1][i])
          .isEqualTo(x[1][i].dom().toString());
    }
    return true;
  }
}
