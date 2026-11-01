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
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Random;
import java.util.function.BiFunction;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.AllEqual;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.AtLeast;
import org.jacop.constraints.AtMost;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.ChannelImply;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.ConditionalSelect;
import org.jacop.constraints.Count;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.ElementVariableFast;
import org.jacop.constraints.GCC;
import org.jacop.constraints.Implies;
import org.jacop.constraints.In;
import org.jacop.constraints.LexOrder;
import org.jacop.constraints.LinearBool;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Max;
import org.jacop.constraints.MaxSimple;
import org.jacop.constraints.Member;
import org.jacop.constraints.Min;
import org.jacop.constraints.MinSimple;
import org.jacop.constraints.Not;
import org.jacop.constraints.OrBoolSimple;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XorBool;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.diffn.Nooverlap;
import org.jacop.constraints.regular.Regular;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.lcg.AtomicTrail;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMax;
import org.jacop.search.IndomainMin;
import org.jacop.search.SimpleSelect;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;
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

  /**
   * The OPB model; with the system property {@code veripb.dump} set to a directory, the model and
   * the proof are also written there, named after the test, for a check by VeriPB itself.
   */
  private String opb() {
    return opb(caller());
  }

  private static String caller() {
    return StackWalker.getInstance().walk(f -> f.skip(2).findFirst().orElseThrow().getMethodName());
  }

  private String opb(String name) {
    String dir = System.getProperty("veripb.dump");
    if (dir != null) {
      try {
        Files.writeString(Path.of(dir, name + ".opb"), model.toString(StandardCharsets.US_ASCII));
        Files.writeString(Path.of(dir, name + ".pbp"), proof.toString(StandardCharsets.US_ASCII));
      } catch (IOException e) {
        throw new UncheckedIOException(e);
      }
    }
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
  void regularOptimumIsProved() {
    Store store = new Store();
    // no two 3s in a row
    Fsm fsm = new Fsm();
    FsmState other = new FsmState();
    FsmState three = new FsmState();
    fsm.initState = other;
    fsm.allStates.add(other);
    fsm.allStates.add(three);
    fsm.finalStates.add(other);
    fsm.finalStates.add(three);
    other.transitions.add(new FsmTransition(new IntervalDomain(1, 2), other));
    other.transitions.add(new FsmTransition(new IntervalDomain(3, 3), three));
    three.transitions.add(new FsmTransition(new IntervalDomain(1, 2), other));
    IntVar[] x = new IntVar[5];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 3);
    }
    store.impose(new Regular(fsm, x));
    IntVar obj = new IntVar(store, "obj", -15, 0);
    store.impose(
        new LinearInt(
            new IntVar[] {x[0], x[1], x[2], x[3], x[4], obj},
            new int[] {1, 1, 1, 1, 1, 1},
            "==",
            0));
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    // 3 2 3 2 3
    assertThat(lcg.value(obj)).isEqualTo(-13);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS -13 -13");
  }

  @Test
  void allDifferentOptimumIsProved() {
    for (int kind = 0; kind < 3; kind++) {
      Store store = new Store();
      IntVar[] x = new IntVar[5];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, 1, 5);
      }
      store.impose(
          switch (kind) {
            case 0 -> new Alldistinct(x);
            case 1 -> new Alldiff(x);
            default -> new Alldifferent(x);
          });
      store.impose(new LinearInt(new IntVar[] {x[0], x[1], x[2]}, new int[] {1, 1, 1}, "<=", 7));
      IntVar obj = new IntVar(store, "obj", -100, 0);
      store.impose(
          new LinearInt(
              new IntVar[] {x[0], x[1], x[2], x[3], x[4], obj},
              new int[] {5, 4, 3, 2, 1, 1},
              "==",
              0));
      proof.reset();
      model.reset();
      LcgSolver lcg = withProof(store);
      assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
      // 4 2 1 5 3
      assertThat(lcg.value(obj)).isEqualTo(-44);
      RupChecker checker = new RupChecker();
      assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
      assertThat(checker.conclusion).isEqualTo("BOUNDS -44 -44");
    }
  }

  @Test
  void globalCardinalityOptimumIsProved() {
    Store store = new Store();
    IntVar[] x = new IntVar[6];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 4);
    }
    IntVar[] counters = new IntVar[4];
    for (int v = 0; v < counters.length; v++) {
      counters[v] = new IntVar(store, "c" + (v + 1), v == 3 ? 1 : 0, 2);
    }
    store.impose(new GCC(x, counters));
    IntVar obj = new IntVar(store, "obj", 0, 100);
    store.impose(
        new LinearInt(
            new IntVar[] {x[0], x[1], x[2], x[3], x[4], x[5], obj},
            new int[] {5, 4, 3, 2, 1, 1, -1},
            "==",
            0));
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    // 1 1 2 2 3 4
    assertThat(lcg.value(obj)).isEqualTo(26);
    String pbp = proof.toString(StandardCharsets.US_ASCII);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), pbp)).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS 26 26");
    assertThat(pbp).contains("\npol ");
  }

  // the shortest makespan of five tasks on a resource of capacity 3, by the time-indexed encoding
  // of the time table
  @Test
  void cumulativeMakespanIsProved() {
    int[] d = {3, 2, 2, 1, 2};
    int[] r = {2, 1, 2, 1, 2};
    int horizon = 8;
    Store store = new Store();
    IntVar[] s = new IntVar[d.length];
    IntVar[] dur = new IntVar[d.length];
    IntVar[] res = new IntVar[d.length];
    IntVar obj = new IntVar(store, "obj", 0, horizon + 3);
    for (int i = 0; i < d.length; i++) {
      s[i] = new IntVar(store, "s" + i, 0, horizon);
      dur[i] = new IntVar(store, "d" + i, d[i], d[i]);
      res[i] = new IntVar(store, "r" + i, r[i], r[i]);
      store.impose(new LinearInt(new IntVar[] {s[i], obj}, new int[] {1, -1}, "<=", -d[i]));
    }
    store.impose(new CumulativeBasic(s, dur, res, new IntVar(store, "cap", 3, 3)));
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    assertThat(lcg.value(obj)).isEqualTo(shortestMakespan(d, r, 3, horizon));
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS " + lcg.value(obj) + " " + lcg.value(obj));
  }

  /**
   * Five tasks of length 2 and use 1 start in 0..2 under a capacity of 2: no time point is
   * overloaded by compulsory parts, but the window [0, 4) needs 10 units of energy and gives 8. The
   * energy rules of Cumulative find the failure; the proof sums the load lines of the window with
   * the definitions of the tasks' covering literals and order lines.
   */
  @Test
  void energyOverloadIsRefuted() {
    Store store = new Store();
    int n = 5;
    IntVar[] s = new IntVar[n];
    IntVar[] dur = new IntVar[n];
    IntVar[] res = new IntVar[n];
    for (int i = 0; i < n; i++) {
      s[i] = new IntVar(store, "s" + i, 0, 2);
      dur[i] = new IntVar(store, "d" + i, 2, 2);
      res[i] = new IntVar(store, "r" + i, 1, 1);
    }
    AtomicTrail rootTrail = new AtomicTrail(store);
    store.impose(new Cumulative(s, dur, res, new IntVar(store, "cap", 2, 2)));
    assertThat(store.consistency()).isFalse();
    LcgSolver.proveRootFailure(store, rootTrail, model, proof);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("UNSAT");
  }

  // random fixed tasks under Cumulative (edge finding and energy rules): every reason is a rup
  // step once its overloaded window is summed, and the optimum is the brute-force one
  @Test
  void edgeFindingMakespanIsProved() {
    Random random = new Random(11);
    for (int run = 0; run < 6; run++) {
      model.reset();
      proof.reset();
      int n = 5;
      int[] d = new int[n];
      int[] r = new int[n];
      for (int i = 0; i < n; i++) {
        d[i] = 1 + random.nextInt(3);
        r[i] = 1 + random.nextInt(3);
      }
      int horizon = 9;
      Store store = new Store();
      IntVar[] s = new IntVar[n];
      IntVar[] dur = new IntVar[n];
      IntVar[] res = new IntVar[n];
      IntVar obj = new IntVar(store, "obj", 0, horizon + 3);
      for (int i = 0; i < n; i++) {
        s[i] = new IntVar(store, "s" + i, 0, horizon);
        dur[i] = new IntVar(store, "d" + i, d[i], d[i]);
        res[i] = new IntVar(store, "r" + i, r[i], r[i]);
        store.impose(new LinearInt(new IntVar[] {s[i], obj}, new int[] {1, -1}, "<=", -d[i]));
      }
      Cumulative cumulative = new Cumulative(s, dur, res, new IntVar(store, "cap", 3, 3));
      cumulative.doEdgeFind(true);
      store.impose(cumulative);
      LcgSolver lcg = withProof(store);
      assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
      assertThat(lcg.value(obj)).isEqualTo(shortestMakespan(d, r, 3, horizon));
      RupChecker checker = new RupChecker();
      assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII)))
          .as("run " + run)
          .isNull();
    }
  }

  // variable durations and resource uses, from 0: three tasks under a capacity of 3 that should
  // start early, use much and run long but for the last one, which starts late, uses more than
  // the capacity and so has length 0; the solutions logged fix every literal of the encoding
  @Test
  void cumulativeOfVariableTasksIsProved() {
    int n = 3;
    int[] weight = {1, 2, -1};
    Store store = new Store();
    IntVar[] s = new IntVar[n];
    IntVar[] dur = new IntVar[n];
    IntVar[] res = new IntVar[n];
    IntVar[] terms = new IntVar[3 * n + 1];
    int[] w = new int[3 * n + 1];
    for (int i = 0; i < n; i++) {
      s[i] = new IntVar(store, "s" + i, 0, 4);
      dur[i] = new IntVar(store, "d" + i, 0, 2);
      res[i] = new IntVar(store, "r" + i, i == 0 ? 2 : i == n - 1 ? 3 : 0, i == n - 1 ? 5 : 3);
      terms[3 * i] = s[i];
      w[3 * i] = weight[i];
      terms[3 * i + 1] = dur[i];
      w[3 * i + 1] = i == n - 1 ? 3 : -3;
      terms[3 * i + 2] = res[i];
      w[3 * i + 2] = -2;
    }
    IntVar obj = new IntVar(store, "obj", -100, 100);
    terms[3 * n] = obj;
    w[3 * n] = -1;
    store.impose(new LinearInt(terms, w, "==", 0));
    store.impose(new CumulativeBasic(s, dur, res, new IntVar(store, "cap", 3, 3)));
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    // every start, duration and use, by enumeration
    int best = Integer.MAX_VALUE;
    int[] x = new int[3 * n];
    for (int k = 0; k < Math.pow(90, n); k++) {
      int rest = k;
      int value = 0;
      for (int i = 0; i < n; i++) {
        x[3 * i] = rest % 5;
        x[3 * i + 1] = rest / 5 % 3;
        x[3 * i + 2] = rest / 15 % 6;
        rest /= 90;
        value += weight[i] * x[3 * i] + (i == n - 1 ? 3 : -3) * x[3 * i + 1] - 2 * x[3 * i + 2];
      }
      boolean fits = x[2] >= 2 && x[2] <= 3 && x[5] <= 3 && x[3 * n - 1] >= 3;
      for (int t = 0; t < 7 && fits; t++) {
        int load = 0;
        for (int i = 0; i < n; i++) {
          load += x[3 * i] <= t && t < x[3 * i] + x[3 * i + 1] ? x[3 * i + 2] : 0;
        }
        fits = load <= 3;
      }
      if (fits) {
        best = Math.min(best, value);
      }
    }
    assertThat(lcg.value(obj)).isEqualTo(best);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS " + best + " " + best);
  }

  // two tasks of length 0, one at its latest start and one at its earliest: the solution logged
  // fixes the literals of both at their starts (fuzz seed 1739)
  @Test
  void cumulativeTasksOfLengthZeroAreFixedInTheSolution() {
    Store store = new Store();
    IntVar[] s = {new IntVar(store, "sa", -1, 1), new IntVar(store, "sb", 1, 5)};
    IntVar[] dur = {new IntVar(store, "da", 0, 1), new IntVar(store, "db", 0, 2)};
    IntVar[] res = {new IntVar(store, "ra", 2, 4), new IntVar(store, "rb", 1, 1)};
    store.impose(new CumulativeBasic(s, dur, res, new IntVar(store, "cap", 2, 2)));
    IntVar obj = new IntVar(store, "obj", -20, 20);
    store.impose(
        new LinearInt(
            new IntVar[] {s[0], dur[0], res[0], s[1], dur[1], obj},
            new int[] {-1, 1, 1, 1, 1, -1},
            "==",
            0));
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    assertThat(lcg.value(obj)).isEqualTo(2);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS 2 2");
  }

  // the shortest makespan over every start from 0 to horizon of each task
  // reified, implied and negated In, AllEqual, AtMost, AtLeast, XorBool and AndBoolSimple, and
  // AbsXeqY, MaxSimple, MinSimple and OrBoolSimple, against the optimum of a depth-first search
  @Test
  void reifiedNonLinearConstraintsAreProved() {
    optimaAreProved(12, VeriPbProofTest::mixedModel);
  }

  // y = x[k] for the first k with b[k] = 1 (if_then_else_int), over branches with holes
  @Test
  void conditionalSelectIsProved() {
    optimaAreProved(
        12,
        (store, random) -> {
          int n = 3 + random.nextInt(2);
          IntVar[] b = new IntVar[n];
          IntVar[] x = new IntVar[n];
          for (int i = 0; i < n; i++) {
            b[i] = new IntVar(store, "b" + i, 0, 1);
            x[i] = new IntVar(store, "x" + i, -3, 5);
            for (int h = 0; h < 3; h++) {
              x[i].domain.inComplement(0, x[i], random.nextInt(9) - 3);
            }
          }
          IntVar y = new IntVar(store, "y", -2, 4);
          y.domain.inComplement(0, y, random.nextInt(7) - 2);
          store.impose(new ConditionalSelect(b, x, y));
          store.impose(new XneqY(x[0], x[1]));
          IntVar[] terms = Arrays.copyOf(x, 2 * n + 2);
          System.arraycopy(b, 0, terms, n, n);
          terms[2 * n] = y;
          IntVar obj = new IntVar(store, "obj", -500, 500);
          terms[2 * n + 1] = obj;
          int[] w = new int[terms.length];
          for (int i = 0; i < 2 * n + 1; i++) {
            w[i] = random.nextInt(9) - 4;
          }
          w[2 * n + 1] = -1;
          store.impose(new LinearInt(terms, w, "==", 0));
          return obj;
        });
  }

  // x <=lex y or x <lex y over vectors with holes, twice, against an objective that pulls them
  // apart
  @Test
  void lexOrderIsProved() {
    optimaAreProved(
        12,
        (store, random) -> {
          int n = 3 + random.nextInt(2);
          IntVar[][] v = new IntVar[3][n];
          for (int k = 0; k < 3; k++) {
            for (int i = 0; i < n; i++) {
              v[k][i] = new IntVar(store, "v" + k + "_" + i, 0, 4);
              v[k][i].domain.inComplement(0, v[k][i], random.nextInt(5));
            }
          }
          store.impose(new LexOrder(v[0], v[1], random.nextBoolean()));
          store.impose(new LexOrder(v[1], v[2], random.nextBoolean()));
          IntVar[] terms = new IntVar[3 * n + 1];
          int[] w = new int[terms.length];
          for (int k = 0; k < 3; k++) {
            for (int i = 0; i < n; i++) {
              terms[k * n + i] = v[k][i];
              w[k * n + i] = (k == 1 ? -1 : 1) * (1 + random.nextInt(3)) * (n - i);
            }
          }
          IntVar obj = new IntVar(store, "obj", -500, 500);
          terms[3 * n] = obj;
          w[3 * n] = -1;
          store.impose(new LinearInt(terms, w, "==", 0));
          return obj;
        });
  }

  // tables of random tuples, among them equal ones, whose literals each solution must fix, and
  // tuples whose accepted values are removed one by one (lot-sizing pigment20a)
  @Test
  void tablesOfValuesAreProved() {
    optimaAreProved(
        300,
        (store, random) -> {
          IntVar[] x = new IntVar[4];
          for (int i = 0; i < x.length; i++) {
            x[i] = new IntVar(store, "x" + i, 0, 7);
          }
          for (int k = 0; k < 2; k++) {
            int[][] tuples = new int[6 + random.nextInt(6)][3];
            for (int[] t : tuples) {
              for (int i = 0; i < 3; i++) {
                t[i] = random.nextInt(8);
              }
            }
            store.impose(new HybridTable(new IntVar[] {x[k], x[k + 1], x[k + 2]}, tuples));
          }
          store.impose(new XneqY(x[0], x[3]));
          IntVar obj = new IntVar(store, "obj", -500, 500);
          IntVar[] terms = {x[0], x[1], x[2], x[3], obj};
          int[] w = new int[terms.length];
          for (int i = 0; i < 4; i++) {
            w[i] = random.nextInt(9) - 4;
          }
          w[4] = -1;
          store.impose(new LinearInt(terms, w, "==", 0));
          return obj;
        });
  }

  // BoolClause, reified and negated
  @Test
  void boolClausesAreProved() {
    optimaAreProved(
        12,
        (store, random) -> {
          IntVar[] b = new IntVar[8];
          for (int i = 0; i < b.length; i++) {
            b[i] = new IntVar(store, "b" + i, 0, 1);
          }
          for (int k = 0; k < 6; k++) {
            IntVar[] x = {b[random.nextInt(8)], b[random.nextInt(8)]};
            IntVar[] y = {b[random.nextInt(8)]};
            BoolClause c = new BoolClause(x, y);
            switch (k % 3) {
              case 0 -> store.impose(c);
              case 1 -> store.impose(new Reified(c, b[random.nextInt(8)]));
              default -> store.impose(new Not(c));
            }
          }
          int[] w = new int[9];
          for (int i = 0; i < 8; i++) {
            w[i] = random.nextInt(9) - 4;
          }
          w[8] = -1;
          IntVar obj = new IntVar(store, "obj", -50, 50);
          IntVar[] terms = Arrays.copyOf(b, 9);
          terms[8] = obj;
          store.impose(new LinearInt(terms, w, "==", 0));
          return obj;
        });
  }

  /**
   * Minimizes the objective of a model per seed with a proof, checks the proof and compares the
   * optimum, or that there is no solution, with a depth-first search over the same model.
   */
  private void optimaAreProved(int seeds, BiFunction<Store, Random, IntVar> builder) {
    String test = caller();
    for (int seed = 0; seed < seeds; seed++) {
      model.reset();
      proof.reset();
      Store reference = new Store();
      IntVar cost = builder.apply(reference, new Random(seed));
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      IntVar[] all = new IntVar[reference.size()];
      for (int i = 0; i < all.length; i++) {
        all[i] = (IntVar) reference.vars[i];
      }
      boolean feasible =
          search.labeling(reference, new SimpleSelect<>(all, null, new IndomainMin<>()), cost);
      Store store = new Store();
      IntVar obj = builder.apply(store, new Random(seed));
      LcgSolver lcg = withProof(store);
      int status = lcg.minimize(obj);
      assertThat(status)
          .as("seed %d", seed)
          .isEqualTo(feasible ? CdclSolver.SAT : CdclSolver.UNSAT);
      if (feasible) {
        assertThat(lcg.value(obj)).as("seed %d", seed).isEqualTo(search.getCostValue());
      }
      RupChecker checker = new RupChecker();
      assertThat(checker.check(opb(test + seed), proof.toString(StandardCharsets.US_ASCII)))
          .as("seed %d", seed)
          .isNull();
    }
  }

  private static IntVar mixedModel(Store store, Random random) {
    int n = 5;
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, -3, 4);
      for (int h = 0; h < 2; h++) {
        x[i].domain.inComplement(0, x[i], random.nextInt(8) - 3);
      }
    }
    IntVar[] b = new IntVar[8];
    for (int i = 0; i < b.length; i++) {
      b[i] = new IntVar(store, "b" + i, 0, 1);
    }
    IntervalDomain set = new IntervalDomain();
    for (int v = -3; v <= 4; v++) {
      if (random.nextBoolean()) {
        set.unionAdapt(v, v);
      }
    }
    store.impose(new Reified(new In(x[0], set), b[0]));
    store.impose(new Implies(b[1], new In(x[1], set)));
    store.impose(new Not(new In(x[4], set)));
    store.impose(new Reified(new AllEqual(new IntVar[] {x[0], x[2], x[3]}), b[2]));
    store.impose(new Reified(new AtMost(x, 1 + random.nextInt(2), random.nextInt(4)), b[3]));
    store.impose(new Implies(b[4], new Not(new AtLeast(x, 2, random.nextInt(4)))));
    store.impose(new Reified(new XorBool(new IntVar[] {b[0], b[1], b[2]}, b[5]), b[6]));
    store.impose(new Reified(new AndBoolSimple(b[3], b[4], b[5]), b[7]));
    IntVar or = new IntVar(store, "or", 0, 1);
    store.impose(new OrBoolSimple(b[6], b[7], or));
    IntVar abs = new IntVar(store, "abs", -1, 4);
    store.impose(new AbsXeqY(x[2], abs));
    IntVar max = new IntVar(store, "max", -3, 4);
    store.impose(new MaxSimple(x[3], x[4], max));
    IntVar min = new IntVar(store, "min", -3, 4);
    store.impose(new MinSimple(x[0], x[1], min));
    IntVar[] terms = {x[0], x[1], x[2], x[3], x[4], b[0], b[2], b[5], or, abs, max, min};
    int[] w = new int[terms.length + 1];
    for (int i = 0; i < terms.length; i++) {
      w[i] = random.nextInt(9) - 4;
    }
    w[terms.length] = -1;
    IntVar obj = new IntVar(store, "obj", -500, 500);
    IntVar[] all = Arrays.copyOf(terms, terms.length + 1);
    all[terms.length] = obj;
    store.impose(new LinearInt(all, w, "==", 0));
    return obj;
  }

  private static int shortestMakespan(int[] d, int[] r, int capacity, int horizon) {
    int n = d.length;
    int[] start = new int[n];
    int best = Integer.MAX_VALUE;
    for (long k = 0; k < Math.pow(horizon + 1, n); k++) {
      long rest = k;
      int end = 0;
      for (int i = 0; i < n; i++) {
        start[i] = (int) (rest % (horizon + 1));
        rest /= horizon + 1;
        end = Math.max(end, start[i] + d[i]);
      }
      boolean fits = true;
      for (int t = 0; t < end && fits; t++) {
        int load = 0;
        for (int i = 0; i < n; i++) {
          load += start[i] <= t && t < start[i] + d[i] ? r[i] : 0;
        }
        fits = load <= capacity;
      }
      if (fits) {
        best = Math.min(best, end);
      }
    }
    return best;
  }

  @Test
  void sumOverARemovedValueIsProved() {
    // x + y = z fails when x and z are fixed together and y must take the value b removed. Its
    // explanation, x >= -3, x <= -3, z <= 1, y >= 3, y != 4, was no rup step: unit propagation
    // over the order literals of the sum gives no y >= 4 (any of y >= 4, 5, 6 would do) without
    // the lemma that the hypotheses imply y >= 4
    Store store = new Store();
    IntVar x = new IntVar(store, "x", -4, -1);
    IntVar y = new IntVar(store, "y", 2, 6);
    IntVar z = new IntVar(store, "z", 1, 3);
    BooleanVar b = new BooleanVar(store, "b");
    BooleanVar c = new BooleanVar(store, "c");
    BooleanVar d = new BooleanVar(store, "d");
    store.impose(new XplusYeqZ(x, y, z));
    store.impose(new Reified(new XneqC(y, 4), b));
    store.impose(new Reified(new XgteqC(y, 3), d));
    store.impose(new Reified(new XeqC(x, -3), c));
    store.impose(new Reified(new XeqC(z, 1), c));
    LcgSolver lcg = withProof(store);
    lcg.setAnnotation(new SimpleSelect<>(new IntVar[] {b, d, c}, null, new IndomainMax<>()), false);
    assertThat(lcg.solve()).isEqualTo(CdclSolver.SAT);
    String pbp = proof.toString(StandardCharsets.US_ASCII);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), pbp)).isNull();
    assertThat(checker.conclusion).isEqualTo("SAT");
  }

  @Test
  void rootPropagationIsDerived() {
    // the OPB states the domains before the root propagation; the proof derives its changes, the
    // Hall set {x0, x1} of the all different constraint with a pol step
    Store store = new Store();
    IntVar[] x = {
      new IntVar(store, "x0", 1, 2), new IntVar(store, "x1", 1, 2), new IntVar(store, "x2", 1, 4)
    };
    IntVar obj = new IntVar(store, "obj", 0, 100);
    // attached after the variables are created: it states their domains then
    AtomicTrail rootTrail = new AtomicTrail(store);
    store.imposeWithConsistency(new Alldistinct(x));
    store.imposeWithConsistency(
        new LinearInt(new IntVar[] {x[0], x[1], x[2], obj}, new int[] {1, 2, 3, -1}, "==", 0));
    assertThat(x[2].min()).isEqualTo(3);
    LcgSolver lcg = new LcgSolver(store);
    lcg.setRootTrail(rootTrail);
    lcg.setProof(model, proof);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    assertThat(lcg.value(obj)).isEqualTo(13);
    String pbp = proof.toString(StandardCharsets.US_ASCII);
    assertThat(opb()).contains(" is x2 {1..4}\n");
    assertThat(pbp).contains("root changes derived, 0 taken into").contains("\npol ");
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), pbp)).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS 13 13");
  }

  @Test
  void rootFailureIsRefuted() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 5);
    IntVar y = new IntVar(store, "y", 1, 5);
    IntVar z = new IntVar(store, "z", 9, 9);
    AtomicTrail rootTrail = new AtomicTrail(store);
    store.imposeWithConsistency(new XneqC(x, 4));
    assertThat(store.consistency()).isTrue();
    // x + y = 9 gives x >= 4, so x = 5 past the hole, and y = x fails
    store.impose(new XeqY(x, y));
    store.impose(new XplusYeqZ(x, y, z));
    assertThat(store.consistency()).isFalse();
    LcgSolver.proveRootFailure(store, rootTrail, model, proof);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("UNSAT");
  }

  @Test
  void clauseFalseAtTheRootIsRefuted() {
    // the clause's only literal is false at the root; the proof refutes it by unit propagation
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    BooleanVar b = new BooleanVar(store, "b", 0, 0);
    IntVar obj = new IntVar(store, "obj", 0, 10);
    store.impose(new LinearInt(new IntVar[] {x, obj}, new int[] {2, -1}, "==", 0));
    LcgSolver lcg = withProof(store);
    lcg.addClause(new IntVar[] {b}, new IntVar[0]);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.UNSAT);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS INF INF");
  }

  // five rectangles in a 6 x 4 box, found by search; with each "before" literal as a linear line
  // over the order literals, a reason that moves a bound through it is not a rup step
  @Test
  void nooverlapPackingIsProved() {
    int[][] sides = {{2, 3}, {1, 3}, {2, 3}, {1, 3}, {2, 1}};
    Store store = new Store();
    IntVar[][] r = new IntVar[sides.length][];
    for (int i = 0; i < sides.length; i++) {
      int lx = sides[i][0];
      int ly = sides[i][1];
      r[i] =
          new IntVar[] {
            new IntVar(store, "x" + i, 0, 6 - lx),
            new IntVar(store, "y" + i, 0, 4 - ly),
            new IntVar(store, "lx" + i, lx, lx),
            new IntVar(store, "ly" + i, ly, ly)
          };
    }
    store.impose(new Nooverlap(r, true).pairwiseOnly());
    assertThat(withProof(store).solve()).isEqualTo(CdclSolver.SAT);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("SAT");
  }

  // rectangles of lengths 0..2 in a strip of height 2, the width they need minimised
  @Test
  void nooverlapOfVariableLengthsIsProved() {
    Store store = new Store();
    int n = 4;
    IntVar width = new IntVar(store, "w", 0, 8);
    IntVar[][] r = new IntVar[n][];
    IntVar[] area = new IntVar[n + 1];
    int[] a = new int[n + 1];
    for (int i = 0; i < n; i++) {
      IntVar x = new IntVar(store, "x" + i, 0, 6);
      IntVar lx = new IntVar(store, "lx" + i, 0, 2);
      r[i] =
          new IntVar[] {x, new IntVar(store, "y" + i, 0, 1), lx, new IntVar(store, "ly" + i, 1, 2)};
      store.impose(new LinearInt(new IntVar[] {x, lx, width}, new int[] {1, 1, -1}, "<=", 0));
      // the lengths in x add up to at least 5
      area[i] = lx;
      a[i] = 1;
    }
    area[n] = new IntVar(store, "five", 5, 5);
    a[n] = -1;
    store.impose(new LinearInt(area, a, ">=", 0));
    store.impose(new Nooverlap(r, false).pairwiseOnly());
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(width)).isEqualTo(CdclSolver.SAT);
    // two rows: lengths 2 + 1 and 2, so width 3; a rectangle of length 2 in y fills both rows
    assertThat(lcg.value(width)).isEqualTo(3);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS 3 3");
  }

  @Test
  void multiplicationIsProved() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", -6, 6);
    IntVar y = new IntVar(store, "y", -6, 6);
    IntVar z = new IntVar(store, "z", 6, 6);
    IntVar obj = new IntVar(store, "obj", -12, 12);
    store.impose(new XmulYeqZ(x, y, z));
    store.impose(new LinearInt(new IntVar[] {x, y, obj}, new int[] {1, 1, -1}, "==", 0));
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    assertThat(lcg.value(obj)).isEqualTo(-7);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS -7 -7");
  }

  // a weighted sum over variables with holes, minimised by core-guided search: the cores relax
  // order literals, a hole folds two levels into one soft literal, and the negative weight counts
  // from the upper bound; the optimum is checked by enumeration
  @Test
  void coreGuidedOptimumOfIntegersIsProved() {
    Store store = new Store();
    IntVar[] x = new IntVar[5];
    for (int i = 0; i < x.length; i++) {
      IntervalDomain d = new IntervalDomain(0, 1);
      d.unionAdapt(3, 4);
      x[i] = new IntVar(store, "x" + i, d);
    }
    int[][] atLeast = {{0, 1, 3}, {1, 2, 4}, {0, 4, 2}};
    for (int[] r : atLeast) {
      store.impose(new LinearInt(new IntVar[] {x[r[0]], x[r[1]]}, new int[] {1, 1}, ">=", r[2]));
    }
    store.impose(new LinearInt(new IntVar[] {x[2], x[3], x[4]}, new int[] {1, 1, 1}, ">=", 5));
    store.impose(new XneqY(x[3], x[4]));
    int[] w = {3, 2, 4, -2, 1};
    IntVar obj = new IntVar(store, "obj", -100, 100);
    IntVar[] all = {x[0], x[1], x[2], x[3], x[4], obj};
    store.impose(new LinearInt(all, new int[] {w[0], w[1], w[2], w[3], w[4], -1}, "==", 0));
    LcgSolver lcg = withProof(store);
    lcg.setCoreSearch(1.0, 1_000_000, 1_000_000);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    int[] values = {0, 1, 3, 4};
    int best = Integer.MAX_VALUE;
    for (int t = 0; t < 1024; t++) {
      int[] v = new int[5];
      for (int i = 0; i < 5; i++) {
        v[i] = values[t >> (2 * i) & 3];
      }
      boolean ok = v[0] + v[1] >= 3 && v[1] + v[2] >= 4 && v[0] + v[4] >= 2;
      ok &= v[2] + v[3] + v[4] >= 5 && v[3] != v[4];
      if (ok) {
        best = Math.min(best, w[0] * v[0] + w[1] * v[1] + w[2] * v[2] + w[3] * v[3] + w[4] * v[4]);
      }
    }
    assertThat(lcg.value(obj)).isEqualTo(best);
    assertThat(lcg.coreSearch()).isNotNull();
    assertThat(lcg.coreSearch().cores).isPositive();
    String steps = proof.toString(StandardCharsets.US_ASCII);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), steps)).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS " + best + " " + best);
  }

  // a weighted cover of 0/1 variables through two definitions (obj = cost + 5, cost = the sum),
  // whose cores of several literals add totalizers; the optimum is checked by enumeration
  @Test
  void coreGuidedOptimumOfBooleansIsProved() {
    Store store = new Store();
    int n = 7;
    BooleanVar[] b = new BooleanVar[n];
    for (int i = 0; i < n; i++) {
      b[i] = new BooleanVar(store, "b" + i);
    }
    int[][] sets = {{0, 1, 2}, {1, 3}, {2, 3, 4}, {4, 5}, {5, 6, 0}, {1, 6}, {3, 5}};
    for (int[] set : sets) {
      IntVar[] in = new IntVar[set.length];
      for (int k = 0; k < set.length; k++) {
        in[k] = b[set[k]];
      }
      store.impose(new SumBool(in, ">=", new IntVar(store, 1, 1)));
    }
    int[] w = {3, 5, 4, 2, 6, 3, 4};
    IntVar cost = new IntVar(store, "cost", 0, 100);
    IntVar[] all = new IntVar[n + 1];
    int[] a = new int[n + 1];
    for (int i = 0; i < n; i++) {
      all[i] = b[i];
      a[i] = w[i];
    }
    all[n] = cost;
    a[n] = -1;
    store.impose(new LinearInt(all, a, "==", 0));
    IntVar obj = new IntVar(store, "obj", 0, 200);
    store.impose(new LinearInt(new IntVar[] {obj, cost}, new int[] {1, -1}, "==", 5));
    LcgSolver lcg = withProof(store);
    lcg.setCoreSearch(1.0, 1_000_000, 1_000_000);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    int best = Integer.MAX_VALUE;
    for (int t = 0; t < 1 << n; t++) {
      boolean ok = true;
      for (int[] set : sets) {
        boolean covered = false;
        for (int i : set) {
          covered |= (t >> i & 1) == 1;
        }
        ok &= covered;
      }
      if (ok) {
        int c = 5;
        for (int i = 0; i < n; i++) {
          c += (t >> i & 1) * w[i];
        }
        best = Math.min(best, c);
      }
    }
    assertThat(lcg.value(obj)).isEqualTo(best);
    assertThat(lcg.coreSearch().cores).isPositive();
    String steps = proof.toString(StandardCharsets.US_ASCII);
    assertThat(steps).contains("red ");
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), steps)).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS " + best + " " + best);
  }

  // nine pigeons in eight holes at a cost of 1 each, which 300 conflicts do not refute: a
  // core per pigeon raises the lower bound to 9, and the proof concludes it, stated over the
  // objective's literals
  @Test
  void lowerBoundOfAStoppedSearchIsProved() {
    Store store = new Store();
    int pigeons = 9;
    int holes = 8;
    BooleanVar[][] p = new BooleanVar[pigeons][holes];
    IntVar[] all = new IntVar[pigeons * holes + 1];
    int[] a = new int[all.length];
    for (int i = 0; i < pigeons; i++) {
      for (int h = 0; h < holes; h++) {
        p[i][h] = new BooleanVar(store, "p" + i + "_" + h);
        all[i * holes + h] = p[i][h];
        a[i * holes + h] = 1;
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
    IntVar obj = new IntVar(store, "obj", 0, 1000);
    all[pigeons * holes] = obj;
    a[pigeons * holes] = -1;
    store.impose(new LinearInt(all, a, "==", 0));
    LcgSolver lcg = withProof(store);
    lcg.setCoreSearch(0.5, 1_000_000, 1_000_000);
    lcg.sat().setConflictLimit(300);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.UNKNOWN);
    long bound = lcg.coreSearch().lowerBound;
    assertThat(bound).isGreaterThanOrEqualTo(pigeons);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS " + bound + " INF");
  }

  // the shortest circuit through 7 cities, whose subtours the proof refutes by positions along
  // the circuit; the optimum is checked by enumeration of the circuits
  @Test
  void circuitOptimumIsProved() {
    int n = 7;
    int[][] cost = new int[n][n];
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        cost[i][j] = (7 * i + 3 * j + i * j) % 11 + 1;
      }
    }
    Store store = new Store();
    IntVar[] x = new IntVar[n];
    IntVar[] c = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 1, n);
      c[i] = new IntVar(store, "c" + i, 0, 12);
      store.impose(new ElementInteger(x[i], cost[i], c[i], 0));
    }
    store.impose(new Circuit(x));
    IntVar obj = new IntVar(store, "obj", 0, 100);
    IntVar[] all = new IntVar[n + 1];
    int[] a = new int[n + 1];
    for (int i = 0; i < n; i++) {
      all[i] = c[i];
      a[i] = 1;
    }
    all[n] = obj;
    a[n] = -1;
    store.impose(new LinearInt(all, a, "==", 0));
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    assertThat(lcg.value(obj)).isEqualTo(shortestCircuit(cost));
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).startsWith("BOUNDS");
  }

  // the length of the shortest circuit, over the orders of the nodes after node 0
  private static int shortestCircuit(int[][] cost) {
    int n = cost.length;
    int[] order = new int[n - 1];
    for (int k = 0; k < n - 1; k++) {
      order[k] = k + 1;
    }
    int best = Integer.MAX_VALUE;
    while (true) {
      int length = cost[0][order[0]] + cost[order[n - 2]][0];
      for (int k = 0; k + 1 < n - 1; k++) {
        length += cost[order[k]][order[k + 1]];
      }
      best = Math.min(best, length);
      // the next permutation
      int i = n - 3;
      while (i >= 0 && order[i] > order[i + 1]) {
        i--;
      }
      if (i < 0) {
        return best;
      }
      int j = n - 2;
      while (order[j] < order[i]) {
        j--;
      }
      int t = order[i];
      order[i] = order[j];
      order[j] = t;
      for (int l = i + 1, r = n - 2; l < r; l++, r--) {
        t = order[l];
        order[l] = order[r];
        order[r] = t;
      }
    }
  }

  /**
   * A run that overruns its time-out halts from another thread; the proof then ends after its last
   * whole step with no conclusion (it was cut in the middle of a step), and later steps are
   * dropped.
   */
  @Test
  void anAbandonedProofEndsAfterItsLastStep() {
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    VeriPbProof p = new VeriPbProof(out, d -> "x" + d);
    p.start(1);
    p.lemma("rup 1 x1 >= 1 ;\n");
    VeriPbProof.abandon();
    p.lemma("rup 1 x2 >= 1 ;\n");
    p.concludeNothing();
    try {
      p.close();
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    }
    assertThat(out.toString(StandardCharsets.US_ASCII))
        .isEqualTo(
            "pseudo-Boolean proof version 3.0\nf 1 ;\nrup 1 x1 >= 1 ;\n"
                + "output NONE ;\nconclusion NONE ;\nend pseudo-Boolean proof ;\n");
  }

  /**
   * A reason for a bound of the value skips a position whose variable has no value in common with
   * it while the index still has the position; unit propagation finds that the index is not there
   * only through the support literals of the value's values.
   */
  @Test
  void elementValueBoundsWithAnOpenIndexAreProved() {
    // seed 360 of a sweep has such a reason
    Random random = new Random(360);
    Store store = new Store();
    int n = 2 + random.nextInt(4);
    IntVar[] list = new IntVar[n];
    for (int k = 0; k < n; k++) {
      list[k] = new IntVar(store, "x" + k, -5, 8);
      for (int h = 0; h < 6; h++) {
        int u = random.nextInt(14) - 5;
        if (list[k].getSize() > 2) {
          list[k].domain.inComplement(0, list[k], u);
        }
      }
    }
    IntVar index = new IntVar(store, "i", 1, n);
    IntVar value = new IntVar(store, "v", -5, 8);
    for (int h = 0; h < 6; h++) {
      value.domain.inComplement(0, value, random.nextInt(14) - 5);
    }
    store.impose(new ElementVariableFast(index, list, value));
    for (int k = 0; k + 1 < n; k++) {
      store.impose(new XneqY(list[k], list[k + 1]));
    }
    IntVar[] terms = new IntVar[n + 3];
    int[] w = new int[n + 3];
    for (int k = 0; k < n; k++) {
      terms[k] = list[k];
      w[k] = random.nextInt(9) - 4;
    }
    terms[n] = value;
    w[n] = random.nextInt(9) - 4;
    terms[n + 1] = index;
    w[n + 1] = random.nextInt(9) - 4;
    IntVar obj = new IntVar(store, "obj", -500, 500);
    terms[n + 2] = obj;
    w[n + 2] = -1;
    store.impose(new LinearInt(terms, w, "==", 0));
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
  }

  // list[index] = value over variables with holes; the optimum is checked by enumeration
  @Test
  void elementOfVariablesIsProved() {
    Store store = new Store();
    int n = 4;
    IntVar[] list = new IntVar[n];
    for (int i = 0; i < n; i++) {
      list[i] = new IntVar(store, "x" + i, 0, 4);
      list[i].domain.inComplement(0, list[i], i);
    }
    IntVar index = new IntVar(store, "i", 1, n);
    IntVar value = new IntVar(store, "v", 2, 4);
    IntVar obj = new IntVar(store, "obj", -100, 100);
    store.impose(new ElementVariableFast(index, list, value));
    store.impose(new Alldiff(list));
    int[] w = {3, -2, 1, 2, -3, -1};
    IntVar[] terms = {list[0], list[1], list[2], list[3], value, index, obj};
    store.impose(new LinearInt(terms, new int[] {w[0], w[1], w[2], w[3], w[4], w[5], -1}, "==", 0));
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    int best = Integer.MAX_VALUE;
    for (int t = 0; t < 625 * n; t++) {
      int[] v = {t % 5, t / 5 % 5, t / 25 % 5, t / 125 % 5};
      int i = t / 625;
      boolean ok = v[i] >= 2;
      for (int a = 0; a < n && ok; a++) {
        ok = v[a] != a;
        for (int b = a + 1; b < n && ok; b++) {
          ok = v[a] != v[b];
        }
      }
      if (ok) {
        best =
            Math.min(
                best,
                w[0] * v[0]
                    + w[1] * v[1]
                    + w[2] * v[2]
                    + w[3] * v[3]
                    + w[4] * v[i]
                    + w[5] * (i + 1));
      }
    }
    assertThat(lcg.value(obj)).isEqualTo(best);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion).isEqualTo("BOUNDS " + best + " " + best);
  }

  /**
   * A LinearBool of 32 terms or more watches values instead of sitting in the domains' constraint
   * lists, which the store's constraint list is built from; the OPB model left it out (speck
   * optimisation easy_3), so the proof's steps that need it were not rup.
   */
  @Test
  void aLongBooleanSumIsInTheModel() {
    Store store = new Store();
    int n = LinearBool.WATCH_MIN_LENGTH + 2;
    IntVar[] x = new IntVar[n + 1];
    int[] ones = new int[n];
    int[] w = new int[n + 1];
    Random random = new Random(5);
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
      ones[i] = 1;
      w[i] = 3 + random.nextInt(20);
    }
    store.impose(new LinearBool(Arrays.copyOf(x, n), ones, ">=", 2));
    IntVar obj = new IntVar(store, "obj", 0, 1000);
    x[n] = obj;
    w[n] = -1;
    store.impose(new LinearInt(x, w, "==", 0));
    int[] sorted = Arrays.copyOf(w, n);
    Arrays.sort(sorted);
    LcgSolver lcg = withProof(store);
    assertThat(lcg.minimize(obj)).isEqualTo(CdclSolver.SAT);
    assertThat(lcg.value(obj)).isEqualTo(sorted[0] + sorted[1]);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
    assertThat(checker.conclusion)
        .isEqualTo("BOUNDS " + (sorted[0] + sorted[1]) + " " + (sorted[0] + sorted[1]));
  }

  @Test
  void unsupportedConstraintIsRefused() {
    Store store = new Store();
    IntVar[] x = new IntVar[3];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 1, 3);
    }
    store.impose(new Not(new Member(new IntVar[] {x[0], x[1]}, x[2])));
    LcgSolver lcg = withProof(store);
    assertThatThrownBy(lcg::solve)
        .isInstanceOf(UnsupportedOperationException.class)
        .hasMessageContaining("Not of Member");
  }

  /**
   * Elimination rounds during the search delete the learnt clauses satisfied at the root, among
   * them the binary reasons of root facts that precedences give; the proof keeps those facts as
   * units of their own, since a deleted reason takes its fact out of a VeriPB database.
   */
  @Test
  void rootFactsOutliveEliminationRounds() {
    // seed 27 has such a fact (found by a sweep over seeds)
    Random random = new Random(27);
    Store store = new Store();
    int n = 9;
    IntVar[] s = new IntVar[n];
    IntVar[] d = new IntVar[n];
    IntVar[] r = new IntVar[n];
    IntVar end = new IntVar(store, "end", 0, 60);
    for (int i = 0; i < n; i++) {
      int duration = 1 + random.nextInt(5);
      s[i] = new IntVar(store, "s" + i, 0, 60);
      d[i] = new IntVar(store, duration, duration);
      int use = 1 + random.nextInt(3);
      r[i] = new IntVar(store, use, use);
      store.impose(new XplusClteqZ(s[i], duration, end));
      if (i > 0 && random.nextBoolean()) {
        int j = random.nextInt(i);
        store.impose(new XplusClteqZ(s[j], d[j].min(), s[i]));
      }
    }
    store.impose(new CumulativeBasic(s, d, r, new IntVar(store, "cap", 4, 4)));
    LcgSolver lcg = withProof(store);
    lcg.sat().setEliminationInterval(3);
    assertThat(lcg.minimize(end)).isEqualTo(CdclSolver.SAT);
    RupChecker checker = new RupChecker();
    assertThat(checker.check(opb(), proof.toString(StandardCharsets.US_ASCII))).isNull();
  }
}
