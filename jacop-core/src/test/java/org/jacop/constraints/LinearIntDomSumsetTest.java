/*
 * LinearIntDomSumsetTest.java
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
package org.jacop.constraints;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.BitSet;
import java.util.Random;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Checks the sumset propagation of {@link LinearIntDom}: the bitset shifts against {@link BitSet},
 * the pruning of random equalities with holes in their domains against the enumeration, node by
 * node down random dives, and domain consistency on an equality too large for the enumeration.
 */
class LinearIntDomSumsetTest {

  private static final int TRIALS = Integer.getInteger("sumset.trials", 3000);

  @Test
  void shiftsMatchBitSet() {
    Random r = new Random(1);
    for (int t = 0; t < 5000; t++) {
      int srcBits = 1 + r.nextInt(300);
      int dstBits = 1 + r.nextInt(300);
      long[] src = new long[(srcBits + 63) / 64];
      long[] dst = new long[(dstBits + 63) / 64];
      BitSet s = new BitSet();
      BitSet d = new BitSet();
      for (int i = 0; i < srcBits; i++) {
        if (r.nextInt(4) == 0) {
          src[i >>> 6] |= 1L << i;
          s.set(i);
        }
      }
      for (int i = 0; i < dstBits; i++) {
        if (r.nextInt(4) == 0) {
          dst[i >>> 6] |= 1L << i;
          d.set(i);
        }
      }
      long shift = r.nextInt(700) - 350;
      boolean meets = false;
      for (int i = s.nextSetBit(0); i >= 0; i = s.nextSetBit(i + 1)) {
        long j = i + shift;
        if (j >= 0 && j < dst.length * 64L && d.get((int) j)) {
          meets = true;
        }
      }
      assertThat(LinearIntDom.intersectsShifted(src, dst, shift)).isEqualTo(meets);
      long[] or = dst.clone();
      LinearIntDom.orShifted(src, or, shift);
      BitSet expected = (BitSet) d.clone();
      for (int i = s.nextSetBit(0); i >= 0; i = s.nextSetBit(i + 1)) {
        long j = i + shift;
        if (j >= 0 && j < dst.length * 64L) {
          expected.set((int) j);
        }
      }
      for (int i = 0; i < dst.length * 64; i++) {
        assertThat((or[i >>> 6] >>> i & 1L) != 0).isEqualTo(expected.get(i));
      }
    }
  }

  /** The two stores of one instance: sumsets always, and the enumeration only. */
  private record Pair(Store s1, IntVar[] x1, Store s2, IntVar[] x2) {}

  private static Pair instance(Random r) {
    int n = 2 + r.nextInt(6);
    int[] w = new int[n];
    int[][] dom = new int[n][];
    for (int i = 0; i < n; i++) {
      w[i] = (r.nextInt(5) + 1) * (r.nextBoolean() ? 1 : -1);
      int lo = r.nextInt(9) - 6;
      int hi = lo + r.nextInt(9);
      dom[i] = new int[] {lo, hi};
    }
    int b = r.nextInt(21) - 10;
    Store s1 = new Store();
    Store s2 = new Store();
    IntVar[] x1 = new IntVar[n];
    IntVar[] x2 = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x1[i] = new IntVar(s1, "x" + i, dom[i][0], dom[i][1]);
      x2[i] = new IntVar(s2, "x" + i, dom[i][0], dom[i][1]);
      for (int v = dom[i][0]; v <= dom[i][1]; v++) {
        if (r.nextInt(4) == 0 && x1[i].getSize() > 1) {
          x1[i].domain.inComplement(0, x1[i], v);
          x2[i].domain.inComplement(0, x2[i], v);
        }
      }
    }
    LinearIntDom c1 = new LinearIntDom(x1, w, "==", b);
    c1.sumset = LinearIntDom.SUMSET_ALWAYS;
    LinearIntDom c2 = new LinearIntDom(x2, w, "==", b);
    c2.sumset = LinearIntDom.SUMSET_OFF;
    s1.impose(c1);
    s2.impose(c2);
    return new Pair(s1, x1, s2, x2);
  }

  private static boolean consistent(Store s) {
    try {
      return s.consistency();
    } catch (FailException e) {
      return false;
    }
  }

  @Test
  void sumsetsPruneAsTheEnumeration() {
    Random r = new Random(7);
    int nodes = 0;
    for (int t = 0; t < TRIALS; t++) {
      Pair p = instance(r);
      boolean ok1 = consistent(p.s1());
      boolean ok2 = consistent(p.s2());
      assertThat(ok1).as("trial %d", t).isEqualTo(ok2);
      int level = 0;
      while (ok1) {
        nodes++;
        for (int i = 0; i < p.x1().length; i++) {
          assertThat(p.x1()[i].dom().eq(p.x2()[i].dom()))
              .as("trial %d var %d: %s vs %s", t, i, p.x1()[i], p.x2()[i])
              .isTrue();
        }
        int i = r.nextInt(p.x1().length);
        if (p.x1()[i].singleton()) {
          break;
        }
        level++;
        p.s1().setLevel(level);
        p.s2().setLevel(level);
        int v = p.x1()[i].min() + r.nextInt(p.x1()[i].max() - p.x1()[i].min() + 1);
        switch (r.nextInt(3)) {
          case 0 -> {
            p.x1()[i].domain.inMax(level, p.x1()[i], v);
            p.x2()[i].domain.inMax(level, p.x2()[i], v);
          }
          case 1 -> {
            p.x1()[i].domain.inMin(level, p.x1()[i], v);
            p.x2()[i].domain.inMin(level, p.x2()[i], v);
          }
          default -> {
            if (p.x1()[i].domain.contains(v)) {
              p.x1()[i].domain.inComplement(level, p.x1()[i], v);
              p.x2()[i].domain.inComplement(level, p.x2()[i], v);
            }
          }
        }
        ok1 = consistent(p.s1());
        ok2 = consistent(p.s2());
        assertThat(ok1).as("trial %d level %d", t, level).isEqualTo(ok2);
      }
    }
    assertThat(nodes).isGreaterThan(TRIALS);
  }

  // 3 x_0 + ... + 3 x_29 + y = 46 over 0..9: the product of the domain sizes, 10^31, is beyond
  // the enumeration, which bounds only; the sumsets leave y the values 1, 4 and 7 only
  @Test
  void longEqualityIsDomainConsistent() {
    Store store = new Store();
    IntVar[] x = new IntVar[31];
    int[] w = new int[31];
    for (int i = 0; i < 30; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 9);
      w[i] = 3;
    }
    x[30] = new IntVar(store, "y", 0, 9);
    w[30] = 1;
    LinearIntDom c = new LinearIntDom(x, w, "==", 46);
    store.impose(c);
    assertThat(store.consistency()).isTrue();
    assertThat(x[30].dom().toString()).isEqualTo("{1, 4, 7}");
    assertThat(c.sumsetPasses).isPositive();
    assertThat(x[0].max()).isEqualTo(9);
    assertThat(x[0].min()).isZero();
  }
}
