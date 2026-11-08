/*
 * ClauseEncoderTest.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * Notwithstanding any other provisions of this License, the copyright
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

package org.jacop.jasat.lcg;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import java.util.function.BiFunction;
import org.jacop.constraints.*;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.jasat.cdcl.CdclSolver;
import org.junit.jupiter.api.Test;

/**
 * Checks {@link ClauseEncoder}: for random small constraints, the clauses with the order and value
 * axioms of the variables have exactly the solutions of the constraint, and unit propagation over
 * them is compared with the propagator on random subdomains.
 */
class ClauseEncoderTest {

  private static final int INSTANCES = Integer.getInteger("clauses.trials", 60);

  /** A constraint over fresh variables of a store. */
  private interface Factory extends BiFunction<Store, Random, Constraint> {}

  private static IntVar var(Store s, Random r, int min, int max) {
    int lo = min + r.nextInt(3);
    int hi = Math.min(max, lo + 1 + r.nextInt(5));
    IntVar x = new IntVar(s, lo, hi);
    CREATED.add(x);
    if (hi - lo >= 3 && r.nextBoolean()) {
      x.domain.subtract(lo + 1 + r.nextInt(hi - lo - 1));
    }
    return x;
  }

  private static IntVar v(Store s, Random r) {
    return var(s, r, -3, 6);
  }

  private static IntVar b(Store s) {
    IntVar x = new IntVar(s, 0, 1);
    CREATED.add(x);
    return x;
  }

  // the variables the factories made, in order, so that a rebuilt constraint maps to the first
  private static final List<IntVar> CREATED = new ArrayList<>();

  /** A fresh copy of the constraint of a seed: the store, the constraint and its variables. */
  private record Copy(Store store, Constraint c, List<IntVar> vars) {}

  private static Copy rebuild(Factory f, long seed) {
    CREATED.clear();
    Store s = new Store();
    Random r = new Random(seed);
    Constraint c = f.apply(s, r);
    return new Copy(s, c, new ArrayList<>(CREATED));
  }

  private static IntVar[] vs(Store s, Random r, int n) {
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = v(s, r);
    }
    return x;
  }

  private static IntVar[] bs(Store s, int n) {
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = b(s);
    }
    return x;
  }

  private static int[] ws(Random r, int n) {
    int[] w = new int[n];
    for (int i = 0; i < n; i++) {
      w[i] = (r.nextInt(5) - 2);
      if (w[i] == 0) {
        w[i] = 1;
      }
    }
    return w;
  }

  private static String rel(Random r) {
    return new String[] {"==", "<=", ">=", "<", ">", "!="}[r.nextInt(6)];
  }

  private static PrimitiveConstraint prim(Store s, Random r) {
    return switch (r.nextInt(9)) {
      case 0 -> new XeqC(v(s, r), r.nextInt(5));
      case 1 -> new XlteqC(v(s, r), r.nextInt(5));
      case 2 -> new XneqC(v(s, r), r.nextInt(5));
      case 3 -> new XgteqC(v(s, r), r.nextInt(5));
      case 4 -> new XeqY(v(s, r), v(s, r));
      case 5 -> new XlteqY(v(s, r), v(s, r));
      case 6 -> new XneqY(v(s, r), v(s, r));
      case 7 -> new XplusClteqZ(v(s, r), r.nextInt(3) - 1, v(s, r));
      default -> {
        int n = 2 + r.nextInt(2);
        yield new LinearInt(vs(s, r, n), ws(r, n), rel(r), r.nextInt(7) - 3);
      }
    };
  }

  private static final Map<String, Factory> FACTORIES = new TreeMap<>();

  static {
    FACTORIES.put("XeqC", (s, r) -> new XeqC(v(s, r), r.nextInt(5)));
    FACTORIES.put("XneqY", (s, r) -> new XneqY(v(s, r), v(s, r)));
    FACTORIES.put("XeqY", (s, r) -> new XeqY(v(s, r), v(s, r)));
    FACTORIES.put("XltY", (s, r) -> new XltY(v(s, r), v(s, r)));
    FACTORIES.put("XlteqY", (s, r) -> new XlteqY(v(s, r), v(s, r)));
    FACTORIES.put("XplusYeqZ", (s, r) -> new XplusYeqZ(v(s, r), v(s, r), var(s, r, 0, 9)));
    FACTORIES.put("XplusCeqZ", (s, r) -> new XplusCeqZ(v(s, r), r.nextInt(5) - 2, v(s, r)));
    FACTORIES.put("XplusClteqZ", (s, r) -> new XplusClteqZ(v(s, r), r.nextInt(5) - 2, v(s, r)));
    FACTORIES.put("XplusYlteqZ", (s, r) -> new XplusYlteqZ(v(s, r), v(s, r), var(s, r, 0, 9)));
    FACTORIES.put(
        "LinearInt",
        (s, r) -> {
          int n = 2 + r.nextInt(3);
          return new LinearInt(vs(s, r, n), ws(r, n), rel(r), r.nextInt(9) - 4);
        });
    FACTORIES.put(
        "LinearIntVar",
        (s, r) -> {
          int n = 2 + r.nextInt(2);
          return new LinearInt(vs(s, r, n), ws(r, n), rel(r), v(s, r));
        });
    FACTORIES.put(
        "SumBool", (s, r) -> new SumBool(bs(s, 2 + r.nextInt(6)), rel(r), var(s, r, 0, 5)));
    FACTORIES.put(
        "SumBoolBig", (s, r) -> new SumBool(bs(s, 8 + r.nextInt(4)), rel(r), var(s, r, 1, 5)));
    FACTORIES.put("SumInt", (s, r) -> new SumInt(vs(s, r, 2 + r.nextInt(2)), rel(r), v(s, r)));
    FACTORIES.put(
        "SumWeight",
        (s, r) -> {
          int n = 2 + r.nextInt(2);
          return new SumWeight(vs(s, r, n), ws(r, n), v(s, r));
        });
    FACTORIES.put("XmulYeqZ", (s, r) -> new XmulYeqZ(v(s, r), v(s, r), var(s, r, -6, 12)));
    FACTORIES.put("XmulCeqZ", (s, r) -> new XmulCeqZ(v(s, r), r.nextInt(5) - 2, v(s, r)));
    FACTORIES.put("AbsXeqY", (s, r) -> new AbsXeqY(v(s, r), v(s, r)));
    FACTORIES.put("Max", (s, r) -> new Max(vs(s, r, 2 + r.nextInt(2)), v(s, r)));
    FACTORIES.put("Min", (s, r) -> new Min(vs(s, r, 2 + r.nextInt(2)), v(s, r)));
    FACTORIES.put("MaxSimple", (s, r) -> new MaxSimple(v(s, r), v(s, r), v(s, r)));
    FACTORIES.put("MinSimple", (s, r) -> new MinSimple(v(s, r), v(s, r), v(s, r)));
    FACTORIES.put(
        "ElementInteger", (s, r) -> new ElementInteger(var(s, r, 0, 6), randomList(r), v(s, r), 0));
    FACTORIES.put(
        "ElementIntegerFast",
        (s, r) -> new ElementIntegerFast(var(s, r, 0, 6), randomList(r), v(s, r), 0));
    FACTORIES.put(
        "ElementVariableFast",
        (s, r) -> new ElementVariableFast(var(s, r, 0, 3), vs(s, r, 4), v(s, r), 0));
    FACTORIES.put("CountBool", (s, r) -> new Count(bs(s, 3 + r.nextInt(8)), var(s, r, 0, 6), 1));
    FACTORIES.put(
        "LinearBoolVar",
        (s, r) -> {
          int n = 3 + r.nextInt(7);
          int[] w = new int[n + 1];
          for (int i = 0; i < n; i++) {
            w[i] = r.nextBoolean() ? 1 : -1;
          }
          w[n] = r.nextBoolean() ? 1 : -1;
          IntVar[] x = java.util.Arrays.copyOf(bs(s, n), n + 1);
          x[n] = var(s, r, -2, 6);
          return new LinearInt(x, w, rel(r), r.nextInt(5) - 2);
        });
    FACTORIES.put("Count", (s, r) -> new Count(vs(s, r, 2 + r.nextInt(3)), var(s, r, 0, 4), 2));
    FACTORIES.put("AtMost", (s, r) -> new AtMost(vs(s, r, 2 + r.nextInt(3)), 1 + r.nextInt(2), 2));
    FACTORIES.put(
        "AtLeast", (s, r) -> new AtLeast(vs(s, r, 2 + r.nextInt(3)), 1 + r.nextInt(2), 2));
    FACTORIES.put("In", (s, r) -> new In(v(s, r), new IntervalDomain(0, 1 + r.nextInt(3))));
    FACTORIES.put("AllEqual", (s, r) -> new AllEqual(vs(s, r, 2 + r.nextInt(2))));
    FACTORIES.put("AndBoolSimple", (s, r) -> new AndBoolSimple(b(s), b(s), b(s)));
    FACTORIES.put("OrBoolSimple", (s, r) -> new OrBoolSimple(b(s), b(s), b(s)));
    FACTORIES.put("AndBoolVector", (s, r) -> new AndBoolVector(bs(s, 2 + r.nextInt(4)), b(s)));
    FACTORIES.put("OrBoolVector", (s, r) -> new OrBoolVector(bs(s, 2 + r.nextInt(4)), b(s)));
    FACTORIES.put("XorBool", (s, r) -> new XorBool(bs(s, 2 + r.nextInt(3)), b(s)));
    FACTORIES.put(
        "BoolClause", (s, r) -> new BoolClause(bs(s, 1 + r.nextInt(3)), bs(s, r.nextInt(3))));
    FACTORIES.put(
        "ChannelReif",
        (s, r) -> {
          IntVar x = var(s, r, 0, 5);
          return new ChannelReif(x, bs(s, x.getSize()), x.dom());
        });
    FACTORIES.put(
        "Increasing", (s, r) -> new Increasing(vs(s, r, 2 + r.nextInt(2)), r.nextBoolean()));
    FACTORIES.put(
        "ConditionalSelect", (s, r) -> new ConditionalSelect(bs(s, 3), vs(s, r, 3), v(s, r)));
    FACTORIES.put(
        "HybridTable",
        (s, r) -> {
          IntVar[] x = vs(s, r, 2 + r.nextInt(2));
          int[][] t = new int[1 + r.nextInt(8)][x.length];
          for (int[] row : t) {
            for (int i = 0; i < x.length; i++) {
              row[i] = x[i].min() + r.nextInt(x[i].max() - x[i].min() + 1);
            }
          }
          return new HybridTable(x, t, Integer.MIN_VALUE);
        });
    FACTORIES.put("Reified", (s, r) -> new Reified(prim(s, r), b(s)));
    FACTORIES.put("Implies", (s, r) -> new Implies(b(s), prim(s, r)));
    FACTORIES.put("Not", (s, r) -> new Not(prim(s, r)));
  }

  private static int[] randomList(Random r) {
    int[] a = new int[7];
    for (int i = 0; i < a.length; i++) {
      a[i] = r.nextInt(7) - 2;
    }
    return a;
  }

  /** Literals of a CNF of its own: order and value literals with their axioms. */
  private static final class Cnf implements ClauseEncoder.Literals {
    final Map<IntVar, int[]> values = new IdentityHashMap<>();
    final Map<IntVar, int[]> ge = new IdentityHashMap<>(); // ge[k] = [x >= values[k]], k >= 1
    final Map<IntVar, int[]> eqs = new IdentityHashMap<>();
    final List<int[]> axioms = new ArrayList<>();
    int next = 1;

    void add(IntVar x) {
      if (values.containsKey(x)) {
        return;
      }
      int[] vals = vals(x.dom());
      int[] g = new int[vals.length];
      int[] e = new int[vals.length];
      for (int k = 1; k < vals.length; k++) {
        g[k] = next++;
        if (k > 1) {
          axioms.add(new int[] {-g[k], g[k - 1]});
        }
      }
      for (int k = 0; k < vals.length; k++) {
        e[k] = next++;
        // e <-> ge[k] and not ge[k + 1]
        if (k > 0) {
          axioms.add(new int[] {-e[k], g[k]});
        }
        if (k + 1 < vals.length) {
          axioms.add(new int[] {-e[k], -g[k + 1]});
        }
        List<Integer> back = new ArrayList<>();
        back.add(e[k]);
        if (k > 0) {
          back.add(-g[k]);
        }
        if (k + 1 < vals.length) {
          back.add(g[k + 1]);
        }
        axioms.add(back.stream().mapToInt(Integer::intValue).toArray());
      }
      values.put(x, vals);
      ge.put(x, g);
      eqs.put(x, e);
    }

    @Override
    public int atLeast(IntVar x, int v) {
      add(x);
      int[] vals = values.get(x);
      for (int k = 1; k < vals.length; k++) {
        if (vals[k] >= v) {
          return ge.get(x)[k];
        }
      }
      throw new IllegalStateException("constant");
    }

    @Override
    public int equal(IntVar x, int v) {
      add(x);
      int[] vals = values.get(x);
      for (int k = 0; k < vals.length; k++) {
        if (vals[k] == v) {
          return eqs.get(x)[k];
        }
      }
      throw new IllegalStateException("not in domain");
    }

    @Override
    public int auxiliary() {
      return next++;
    }

    @Override
    public IntDomain root(IntVar x) {
      return x.dom();
    }

    /** Unit literals that restrict x to a subset of its values. */
    void restrict(IntVar x, IntDomain d, List<Integer> units) {
      add(x);
      int[] vals = values.get(x);
      int[] e = eqs.get(x);
      for (int k = 0; k < vals.length; k++) {
        if (!d.contains(vals[k])) {
          units.add(-e[k]);
        }
      }
    }
  }

  private static int[] vals(IntDomain d) {
    int[] v = new int[d.getSize()];
    int k = 0;
    for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
      v[k++] = e.nextElement();
    }
    return v;
  }

  @Test
  void clausesHaveTheSolutionsOfTheConstraint() {
    Map<String, long[]> stats = new TreeMap<>();
    for (Map.Entry<String, Factory> f : FACTORIES.entrySet()) {
      long[] st = new long[6]; // encoded, rejected, solutions, cp-stronger, up-stronger, cases
      for (int i = 0; i < INSTANCES; i++) {
        long seed = 1000L * i + f.getKey().hashCode();
        check(f.getKey(), f.getValue(), seed, st, 4096, 4096);
      }
      stats.put(f.getKey(), st);
      // a low limit leaves 0/1 sums to the unary counter
      long[] low = new long[6];
      for (int i = 0; i < INSTANCES; i++) {
        long seed = 1000L * i + f.getKey().hashCode();
        check(f.getKey(), f.getValue(), seed, low, 4, 4096);
      }
      if (low[0] > 0) {
        stats.put(f.getKey() + "/counter", low);
      }
    }
    stats.forEach(
        (k, st) ->
            System.out.printf(
                "  %-20s encoded=%d rejected=%d solutions=%d cpStronger=%d upStronger=%d of %d%n",
                k, st[0], st[1], st[2], st[3], st[4], st[5]));
    assertThat(stats.get("XplusYeqZ")[0]).isPositive();
  }

  @Test
  void counterUnderReificationKeepsThePlainLimit() {
    Store store = new Store();
    BooleanVar[] x = new BooleanVar[12];
    for (int i = 0; i < x.length; i++) {
      x[i] = new BooleanVar(store, "x" + i);
    }
    BooleanVar b = new BooleanVar(store, "b");
    Cnf cnf = new Cnf();
    for (BooleanVar y : x) {
      cnf.add(y);
    }
    cnf.add(b);
    // alone, the sum of 12 0/1 terms >= 6 becomes a counter of about 300 clauses
    assertThat(new ClauseEncoder(cnf, 16, 4096).encode(new LinearInt(x, ones(x.length), ">=", 6)))
        .isNotNull();
    // reified (one sum of many, bnn-planner made 3.3 million clauses of them), the plain limit
    Constraint reified = new Reified(new LinearInt(x, ones(x.length), ">=", 6), b);
    assertThat(new ClauseEncoder(cnf, 16, 4096).encode(reified)).isNull();
  }

  private static int[] ones(int n) {
    int[] w = new int[n];
    Arrays.fill(w, 1);
    return w;
  }

  private static void check(
      String name, Factory factory, long seed, long[] st, int limit, int counterLimit) {
    Copy first = rebuild(factory, seed);
    Constraint c = first.c();
    Random r = new Random(seed + 7);
    List<Integer> pos = new ArrayList<>();
    List<IntVar> x = new ArrayList<>();
    for (var a : c.arguments()) {
      if (a instanceof IntVar iv && !iv.singleton()) {
        x.add(iv);
      }
    }
    for (IntVar y : x) {
      pos.add(first.vars().indexOf(y));
    }
    Cnf cnf = new Cnf();
    for (IntVar y : x) {
      cnf.add(y);
    }
    List<int[]> clauses = new ClauseEncoder(cnf, limit, counterLimit).encode(c);
    if (clauses == null) {
      st[1]++;
      return;
    }
    st[0]++;
    String where = name + " seed " + seed + ": " + c;
    // the solutions: every assignment of the variables
    int[][] dom = new int[x.size()][];
    for (int i = 0; i < x.size(); i++) {
      dom[i] = vals(x.get(i).dom());
    }
    int[] idx = new int[x.size()];
    CdclSolver whole = solver(cnf, clauses);
    while (true) {
      boolean cp = propagates(factory, seed, pos, dom, idx);
      List<Integer> units = new ArrayList<>();
      for (int i = 0; i < x.size(); i++) {
        units.add(cnf.equal(x.get(i), dom[i][idx[i]]));
      }
      boolean sat = satisfiable(whole, units);
      assertThat(sat).as(where + " at " + assignment(x, dom, idx)).isEqualTo(cp);
      if (cp) {
        st[2]++;
      }
      int k = 0;
      while (k < idx.length && ++idx[k] == dom[k].length) {
        idx[k++] = 0;
      }
      if (k == idx.length) {
        break;
      }
    }
    // propagation strength on random subdomains
    for (int t = 0; t < 8; t++) {
      IntDomain[] sub = new IntDomain[x.size()];
      for (int i = 0; i < x.size(); i++) {
        IntDomain d = new IntervalDomain();
        for (int v : dom[i]) {
          if (r.nextInt(3) > 0) {
            ((IntervalDomain) d).unionAdapt(v, v);
          }
        }
        sub[i] = d.isEmpty() ? x.get(i).dom().cloneLight() : d;
      }
      IntDomain[] byCp = narrowByCp(factory, seed, pos, sub);
      IntDomain[] byUp = narrowByUp(cnf, clauses, x, sub);
      st[5]++;
      boolean cpMore;
      boolean upMore;
      if (byCp == null || byUp == null) {
        cpMore = byCp == null && byUp != null;
        upMore = byUp == null && byCp != null;
      } else {
        cpMore = false;
        upMore = false;
        for (int i = 0; i < x.size(); i++) {
          cpMore |= byUp[i].getSize() > byCp[i].getSize();
          upMore |= byCp[i].getSize() > byUp[i].getSize();
        }
      }
      if (cpMore) {
        st[3]++;
      }
      if (upMore) {
        st[4]++;
      }
    }
  }

  private static String assignment(List<IntVar> x, int[][] dom, int[] idx) {
    StringBuilder b = new StringBuilder();
    for (int i = 0; i < x.size(); i++) {
      b.append(x.get(i).id()).append('=').append(dom[i][idx[i]]).append(' ');
    }
    return b.toString();
  }

  private static boolean propagates(
      Factory f, long seed, List<Integer> pos, int[][] dom, int[] idx) {
    IntDomain[] d = new IntDomain[pos.size()];
    for (int i = 0; i < pos.size(); i++) {
      d[i] = new IntervalDomain(dom[i][idx[i]], dom[i][idx[i]]);
    }
    return narrowByCp(f, seed, pos, d) != null;
  }

  private static IntDomain[] narrowByCp(Factory f, long seed, List<Integer> pos, IntDomain[] sub) {
    Copy copy = rebuild(f, seed);
    Store s = copy.store();
    IntDomain[] out = new IntDomain[pos.size()];
    try {
      for (int i = 0; i < pos.size(); i++) {
        IntVar y = copy.vars().get(pos.get(i));
        y.domain.in(s.level, y, sub[i]);
      }
      s.impose(copy.c());
      if (!s.consistency()) {
        return null;
      }
      for (int i = 0; i < pos.size(); i++) {
        out[i] = copy.vars().get(pos.get(i)).dom().cloneLight();
      }
    } catch (FailException e) {
      return null;
    }
    return out;
  }

  private static IntDomain[] narrowByUp(
      Cnf cnf, List<int[]> clauses, List<IntVar> x, IntDomain[] sub) {
    CdclSolver sat = solver(cnf, clauses);
    if (sat == null) {
      return null;
    }
    List<Integer> units = new ArrayList<>();
    for (int i = 0; i < x.size(); i++) {
      cnf.restrict(x.get(i), sub[i], units);
    }
    for (int u : units) {
      if (!sat.addClause(u)) {
        return null;
      }
    }
    IntDomain[] out = new IntDomain[x.size()];
    for (int i = 0; i < x.size(); i++) {
      IntervalDomain d = new IntervalDomain();
      int[] vals = cnf.values.get(x.get(i));
      int[] e = cnf.eqs.get(x.get(i));
      int[] g = cnf.ge.get(x.get(i));
      for (int k = 0; k < vals.length; k++) {
        boolean out1 = sat.value(e[k]) < 0;
        out1 |= k > 0 && sat.value(g[k]) < 0;
        out1 |= k + 1 < vals.length && sat.value(g[k + 1]) > 0;
        if (!out1) {
          d.unionAdapt(vals[k], vals[k]);
        }
      }
      out[i] = d;
    }
    return out;
  }

  private static CdclSolver solver(Cnf cnf, List<int[]> clauses) {
    CdclSolver sat = new CdclSolver();
    sat.setElimination(false);
    sat.newVariables(cnf.next);
    for (int[] a : cnf.axioms) {
      if (!sat.addClause(a)) {
        return null;
      }
    }
    for (int[] cl : clauses) {
      if (!sat.addClause(cl)) {
        return null;
      }
    }
    return sat;
  }

  private static boolean satisfiable(CdclSolver sat, List<Integer> units) {
    return sat != null
        && sat.solve(units.stream().mapToInt(Integer::intValue).toArray()) == CdclSolver.SAT;
  }
}
