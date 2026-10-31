/*
 * VeriPbProofTest.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.lcg;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;

import java.io.ByteArrayOutputStream;
import java.nio.charset.StandardCharsets;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.AtLeast;
import org.jacop.constraints.AtMost;
import org.jacop.constraints.ChannelImply;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Count;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.LinearBool;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Max;
import org.jacop.constraints.Min;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.junit.jupiter.api.Test;

/** VeriPB proofs of LCG searches, checked by {@link RupChecker}. */
class VeriPbProofTest {

  private final ByteArrayOutputStream model = new ByteArrayOutputStream();
  private final ByteArrayOutputStream proof = new ByteArrayOutputStream();

  private LcgSolver withProof(Store store) {
    LcgSolver lcg = new LcgSolver(store);
    lcg.setProof(model, proof);
    return lcg;
  }

  private String opb() {
    return model.toString(StandardCharsets.US_ASCII);
  }

  @Test
  void pigeonholeIsRefuted() {
    Store store = new Store();
    int pigeons = 5;
    int holes = 4;
    BooleanVar[][] p = new BooleanVar[pigeons][holes];
    for (int i = 0; i < pigeons; i++) {
      for (int h = 0; h < holes; h++) {
        p[i][h] = new BooleanVar(store, "p" + i + "_" + h);
      }
      store.impose(new SumBool(p[i], ">=", new IntVar(store, 1, 1)));
    }
    for (int h = 0; h < holes; h++) {
      IntVar[] column = new IntVar[pigeons];
      for (int i = 0; i < pigeons; i++) {
        column[i] = p[i][h];
      }
      store.impose(new SumBool(column, "<=", new IntVar(store, 0, 1)));
    }
    assertThat(withProof(store).solve()).isEqualTo(CdclSolver.UNSAT);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("UNSAT");
    assertThat(checker.steps).isPositive();
  }

  // a bounded knapsack over integers, whose optimum (46) needs search and explanations of bounds
  private static IntVar knapsack(Store store) {
    int[] w = {12, 7, 11, 8, 9, 6};
    int[] p = {24, 13, 23, 15, 16, 11};
    IntVar[] q = new IntVar[w.length];
    for (int i = 0; i < q.length; i++) {
      q[i] = new IntVar(store, "q" + i, 0, 2);
    }
    store.impose(new LinearInt(q, w, "<=", 22));
    IntVar obj = new IntVar(store, "obj", -60, 0);
    IntVar[] all = new IntVar[q.length + 1];
    int[] a = new int[q.length + 1];
    for (int i = 0; i < q.length; i++) {
      all[i] = q[i];
      a[i] = p[i];
    }
    all[q.length] = obj;
    a[q.length] = 1;
    store.impose(new LinearInt(all, a, "==", 0));
    return obj;
  }

  @Test
  void knapsackOptimumIsProved() {
    Store store = new Store();
    IntVar obj = knapsack(store);
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    assertThat(lcg.value(obj)).isEqualTo(-46);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS -46 -46");
  }

  @Test
  void checkerRejectsAProofOfAWeakerModel() {
    Store store = new Store();
    IntVar obj = knapsack(store);
    withProof(store).minimize(obj);
    // without the capacity constraint, the explanations that cite it do not follow
    String weaker = opb().replaceFirst("\n-12 [^\n]*>= -22 ;\n", "\n");
    assertThat(weaker).isNotEqualTo(opb());
    String steps = proof.toString(StandardCharsets.US_ASCII).replaceFirst("\nf \\d+ ;", "");
    String problem = new RupChecker().check(weaker, steps);
    assertThat(problem).startsWith("rup step");
  }

  @Test
  void reifiedAndDisequalityModelIsSolved() {
    Store store = new Store();
    IntVar[] x = new IntVar[4];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 3);
    }
    BooleanVar b = new BooleanVar(store, "b");
    store.impose(new XneqY(x[0], x[1]));
    store.impose(new XneqY(x[1], x[2]));
    store.impose(new XneqY(x[0], x[2]));
    store.impose(new Reified(new XlteqY(x[3], x[0]), b));
    store.impose(new LinearInt(new IntVar[] {x[0], x[3], b}, new int[] {1, 1, 2}, "==", 7));
    assertThat(withProof(store).solve()).isEqualTo(CdclSolver.SAT);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("SAT");
  }

  // four variables over three values with holes, each value used once through the channels' 0/1
  // variables
  @Test
  void channelPigeonholeIsRefuted() {
    Store store = new Store();
    int[] values = {1, 3, 5};
    BooleanVar[][] b = new BooleanVar[4][values.length];
    for (int i = 0; i < b.length; i++) {
      IntVar x = new IntVar(store, "x" + i, 1, 1);
      x.addDom(3, 3);
      x.addDom(5, 5);
      for (int v = 0; v < values.length; v++) {
        b[i][v] = new BooleanVar(store, "b" + i + "_" + v);
      }
      store.impose(
          i % 2 == 0 ? new ChannelReif(x, b[i], values) : new ChannelImply(x, b[i], values));
      store.impose(new SumBool(b[i], ">=", new IntVar(store, 1, 1)));
    }
    for (int v = 0; v < values.length; v++) {
      IntVar[] column = new IntVar[b.length];
      for (int i = 0; i < b.length; i++) {
        column[i] = b[i][v];
      }
      store.impose(new SumBool(column, "<=", new IntVar(store, 0, 1)));
    }
    assertThat(withProof(store).solve()).isEqualTo(CdclSolver.UNSAT);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("UNSAT");
  }

  // weighted 0/1 sums: 3 a + 2 b + 2 c + d >= 5 and a + b + c + d <= 2 leave a with b or c
  @Test
  void weightedBooleanSumsAreSolved() {
    Store store = new Store();
    BooleanVar[] x = new BooleanVar[4];
    for (int i = 0; i < x.length; i++) {
      x[i] = new BooleanVar(store, "x" + i);
    }
    store.impose(new LinearBool(x, new int[] {3, 2, 2, 1}, ">=", 5));
    store.impose(new LinearBool(x, new int[] {1, 1, 1, 1}, "<=", 2));
    assertThat(withProof(store).solve()).isEqualTo(CdclSolver.SAT);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("SAT");
    assertThat(opb()).contains("3 x");
  }

  // two different items by element tables of weight and cost: least cost of weight at least 9
  @Test
  void elementOptimumIsProved() {
    Store store = new Store();
    int[] weight = {2, 7, 4, 5, 3, 6};
    int[] cost = {1, 9, 3, 6, 2, 7};
    IntVar[] item = new IntVar[2];
    IntVar[] w = new IntVar[2];
    IntVar[] c = new IntVar[2];
    for (int k = 0; k < 2; k++) {
      item[k] = new IntVar(store, "i" + k, 1, weight.length);
      w[k] = new IntVar(store, "w" + k, 0, 10);
      c[k] = new IntVar(store, "c" + k, 0, 10);
      store.impose(new ElementInteger(item[k], weight, w[k], 0));
      store.impose(new ElementIntegerFast(item[k], cost, c[k], 0));
    }
    store.impose(new XneqY(item[0], item[1]));
    store.impose(new LinearInt(w, new int[] {1, 1}, ">=", 9));
    IntVar obj = new IntVar(store, "obj", 0, 20);
    store.impose(new LinearInt(new IntVar[] {c[0], c[1], obj}, new int[] {1, 1, -1}, "==", 0));
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    // weights 4 + 5 (cost 3 + 6) and 3 + 6 (cost 2 + 7) are the cheapest that reach 9
    assertThat(lcg.value(obj)).isEqualTo(9);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS 9 9");
  }

  // five variables over 1..4: two of them are 2, at most one is 4, and the spread max - min is
  // smallest; the counting and min/max encodings carry the proof
  @Test
  void countAndMaxOptimumIsProved() {
    Store store = new Store();
    IntVar[] x = new IntVar[5];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 4);
    }
    store.impose(new Count(x, new IntVar(store, "two", 2, 2), 2));
    store.impose(new AtMost(x, 1, 4));
    store.impose(new AtLeast(x, 1, 1));
    IntVar hi = new IntVar(store, "hi", 1, 4);
    IntVar lo = new IntVar(store, "lo", 1, 4);
    store.impose(new Max(x, hi));
    store.impose(new Min(x, lo));
    IntVar obj = new IntVar(store, "obj", 0, 3);
    store.impose(new LinearInt(new IntVar[] {hi, lo, obj}, new int[] {1, -1, -1}, "==", 0));
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    // a 1 and two 2s give a spread of at least 1, reached by 1, 2, 2, 1, 1
    assertThat(lcg.value(obj)).isEqualTo(1);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS 1 1");
  }

  // a chain x0, x1, x2, x3 of allowed pairs whose sum is largest
  @Test
  void tableOptimumIsProved() {
    Store store = new Store();
    int[][] pairs = {{1, 3}, {3, 2}, {2, 4}, {4, 1}, {3, 3}, {2, 2}};
    IntVar[] x = new IntVar[4];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 4);
    }
    for (int i = 0; i + 1 < x.length; i++) {
      store.impose(new HybridTable(new IntVar[] {x[i], x[i + 1]}, pairs));
    }
    store.impose(new XneqY(x[0], x[3]));
    IntVar obj = new IntVar(store, "obj", -16, 0);
    store.impose(
        new LinearInt(
            new IntVar[] {x[0], x[1], x[2], x[3], obj}, new int[] {1, 1, 1, 1, 1}, "==", 0));
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    // 3 3 2 4 sums to 12; 3 3 3 3 (12 too) has x0 = x3
    assertThat(lcg.value(obj)).isEqualTo(-12);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS -12 -12");
  }

  @Test
  void unsupportedConstraintIsRefused() {
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 3);
    }
    store.impose(new Alldistinct(x));
    LcgSolver lcg = withProof(store);
    assertThatThrownBy(lcg::solve)
        .isInstanceOf(UnsupportedOperationException.class)
        .hasMessageContaining("Alldistinct");
  }
}
