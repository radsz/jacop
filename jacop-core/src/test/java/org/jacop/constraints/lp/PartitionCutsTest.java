/*
 * PartitionCutsTest.java
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

package org.jacop.constraints.lp;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/** Checks the triangle, clique and 2-partition cuts of {@link PartitionCuts} by brute force. */
class PartitionCutsTest {

  private static final int TRIALS = Integer.getInteger("partition.trials", 400);

  /** The fewest pairs inside the classes when s nodes are split into k classes. */
  @Test
  void leastPairsSplitsEvenly() {
    assertThat(PartitionCuts.leastPairs(4, 3)).isEqualTo(1);
    assertThat(PartitionCuts.leastPairs(3, 3)).isZero();
    assertThat(PartitionCuts.leastPairs(7, 3)).isEqualTo(3 + 1 + 1);
    assertThat(PartitionCuts.leastPairs(8, 2)).isEqualTo(12);
  }

  /** Two values and three nodes: some pair is in one class; the cut is found at all-zero. */
  @Test
  void cliqueCutOfTwoClasses() {
    Store store = new Store();
    IntVar[] x = vars(store, 4, 2);
    List<Constraint> cs = new ArrayList<>();
    IntVar[] b = new IntVar[6];
    int k = 0;
    for (int i = 0; i < 4; i++) {
      for (int j = i + 1; j < 4; j++) {
        b[k] = new IntVar(store, "b" + k, 0, 1);
        cs.add(new Reified(new XeqY(x[i], x[j]), b[k++]));
      }
    }
    List<PartitionCuts> ps = PartitionCuts.of(cs);
    assertThat(ps).hasSize(1);
    List<PartitionCuts.Cut> cuts = ps.get(0).separate(new double[6], 100);
    assertThat(cuts).isNotEmpty();
    assertThat(cuts.get(0).efficacy()).isPositive();
  }

  /**
   * On random models (pairs reified as equalities or disequalities, some missing, some pairs fixed
   * apart or equal, value Booleans of some variables) every cut separated at random points holds at
   * every solution.
   */
  @Test
  void cutsHoldAtEverySolution() {
    Random random = new Random(7);
    int checked = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      Store store = new Store();
      int n = 4 + random.nextInt(3);
      int k = 2 + random.nextInt(2);
      IntVar[] x = vars(store, n, k);
      if (random.nextBoolean()) {
        x[0] = new IntVar(store, "x0fixed", 1, 1);
      }
      List<Constraint> cs = new ArrayList<>();
      List<IntVar> lits = new ArrayList<>();
      List<int[]> meaning = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        for (int j = i + 1; j < n; j++) {
          int r = random.nextInt(10);
          if (r < 6) {
            IntVar b = new IntVar(store, "b" + i + "_" + j, 0, 1);
            boolean eq = r < 4;
            cs.add(new Reified(eq ? new XeqY(x[i], x[j]) : new XneqY(x[i], x[j]), b));
            lits.add(b);
            meaning.add(new int[] {i, j, eq ? 1 : 0});
          } else if (r == 6) {
            cs.add(new XneqY(x[i], x[j]));
          } else if (r == 7) {
            cs.add(new XeqY(x[i], x[j]));
          }
        }
        if (random.nextInt(3) == 0) {
          int v = 1 + random.nextInt(k);
          IntVar b = new IntVar(store, "v" + i + "_" + v, 0, 1);
          cs.add(new Reified(new XeqC(x[i], v), b));
          lits.add(b);
          meaning.add(new int[] {i, -v, 2});
        }
      }
      List<int[]> solutions = solutions(x, cs, n, k);
      for (PartitionCuts p : PartitionCuts.of(cs)) {
        IntVar[] pl = p.literals();
        for (int point = 0; point < 20; point++) {
          double[] value = new double[pl.length];
          for (int a = 0; a < value.length; a++) {
            value[a] = random.nextInt(3) == 0 ? random.nextInt(2) : random.nextDouble();
          }
          for (PartitionCuts.Cut cut : p.separate(value, 1000)) {
            for (int[] s : solutions) {
              long lhs = 0;
              for (int t = 0; t < cut.literals().length; t++) {
                IntVar lit = pl[cut.literals()[t]];
                lhs += cut.weights()[t] * literalValue(lit, lits, meaning, s);
              }
              assertThat(lhs)
                  .as("cut %s at %s", cut, java.util.Arrays.toString(s))
                  .isLessThanOrEqualTo(cut.rhs());
              checked++;
            }
          }
        }
      }
    }
    assertThat(checked).isPositive();
  }

  private static IntVar[] vars(Store store, int n, int k) {
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 1, k);
    }
    return x;
  }

  private static int literalValue(IntVar lit, List<IntVar> lits, List<int[]> meaning, int[] s) {
    int[] m = meaning.get(lits.indexOf(lit));
    if (m[2] == 2) {
      return s[m[0]] == -m[1] ? 1 : 0;
    }
    boolean same = s[m[0]] == s[m[1]];
    return same == (m[2] == 1) ? 1 : 0;
  }

  // the assignments of x in their domains that satisfy the unreified constraints
  private static List<int[]> solutions(IntVar[] x, List<Constraint> cs, int n, int k) {
    List<int[]> out = new ArrayList<>();
    int[] s = new int[n];
    enumerate(x, cs, s, 0, k, out);
    return out;
  }

  private static void enumerate(
      IntVar[] x, List<Constraint> cs, int[] s, int i, int k, List<int[]> out) {
    if (i == s.length) {
      for (Constraint c : cs) {
        if (c instanceof XneqY ne && s[index(x, ne.x())] == s[index(x, ne.y())]) {
          return;
        }
        if (c instanceof XeqY eq && s[index(x, eq.x())] != s[index(x, eq.y())]) {
          return;
        }
      }
      out.add(s.clone());
      return;
    }
    for (int v = x[i].min(); v <= x[i].max(); v++) {
      s[i] = v;
      enumerate(x, cs, s, i + 1, k, out);
    }
  }

  private static int index(IntVar[] x, IntVar v) {
    for (int i = 0; i < x.length; i++) {
      if (x[i] == v) {
        return i;
      }
    }
    throw new IllegalArgumentException(v.id());
  }
}
