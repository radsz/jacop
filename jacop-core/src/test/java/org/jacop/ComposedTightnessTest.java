/*
 * ComposedTightnessTest.java
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

package org.jacop;

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;
import java.util.function.BiFunction;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.AllEqual;
import org.jacop.constraints.And;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.AndBoolVector;
import org.jacop.constraints.AtLeast;
import org.jacop.constraints.AtMost;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Count;
import org.jacop.constraints.CountBounds;
import org.jacop.constraints.CountVar;
import org.jacop.constraints.Distance;
import org.jacop.constraints.Eq;
import org.jacop.constraints.EqBool;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.IfThenBool;
import org.jacop.constraints.IfThenElse;
import org.jacop.constraints.IfThenElseBool;
import org.jacop.constraints.Implies;
import org.jacop.constraints.ImpliesNot;
import org.jacop.constraints.In;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.Member;
import org.jacop.constraints.Not;
import org.jacop.constraints.Or;
import org.jacop.constraints.OrBoolSimple;
import org.jacop.constraints.OrBoolVector;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XgtY;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XgteqY;
import org.jacop.constraints.XltC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XmulYeqC;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.Xor;
import org.jacop.constraints.XorBool;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusClteqZImplied;
import org.jacop.constraints.XplusClteqZImpliedNot;
import org.jacop.constraints.XplusCneqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XplusYgtC;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Checks primitive and composed constraints on small random boxes against a brute force that
 * decides each complete assignment by imposing the constraint on fixed variables. For each box it
 * imposes {@code Reified(c, b)} with b open: b must not be fixed wrongly and no variable may lose a
 * value (soundness); b fixed while every tuple holds or none does is counted as entailment
 * detection (tightness). It then fixes b to 1 and to 0 after imposing, and with b fixed before
 * imposing, and compares the pruning with the brute-force supports of c and of its negation:
 * removing a supported value is a bug, keeping an unsupported one is counted. Finally c is imposed
 * on its own and must reach at least the pruning of the nested c, since a nested constraint that
 * prunes less than the imposed one points at a rule kept for the imposed case only.
 *
 * <p>Trials per case: {@code tightness.trials} (default 300). Cases listed in {@code EXACT} must
 * have no tightness gap; the others are reported only.
 */
class ComposedTightnessTest {

  static final int TRIALS = Integer.getInteger("tightness.trials", 300);
  static final long SEED = Long.getLong("tightness.seed", 1L);
  static final String ONLY = System.getProperty("tightness.cases", "");
  static final boolean REPORT = Boolean.getBoolean("tightness.report");

  static final int INTS = 3;
  static final int BOOLS = 3;

  /** A case: a name and a factory of the constraint over the variables, ints first, then bools. */
  record Case(String name, BiFunction<Random, IntVar[], PrimitiveConstraint> make) {}

  static int[] ints(Random r, int k) {
    int[] p = new int[k];
    for (int i = 0; i < k; i++) {
      p[i] = r.nextInt(INTS);
    }
    return p;
  }

  static int[] bools(Random r, int k) {
    int[] p = new int[k];
    for (int i = 0; i < k; i++) {
      p[i] = INTS + r.nextInt(BOOLS);
    }
    return p;
  }

  static IntVar[] pick(IntVar[] v, int[] p) {
    IntVar[] a = new IntVar[p.length];
    for (int i = 0; i < p.length; i++) {
      a[i] = v[p[i]];
    }
    return a;
  }

  static int c(Random r) {
    return r.nextInt(6) - 2;
  }

  static IntDomain dom(Random r) {
    IntervalDomain d = new IntervalDomain();
    for (int x = -2; x <= 3; x++) {
      if (r.nextBoolean()) {
        d.unionAdapt(x, x);
      }
    }
    if (d.isEmpty()) {
      d.unionAdapt(0, 0);
    }
    return d;
  }

  /** A random primitive constraint, nested to the given depth. */
  static PrimitiveConstraint atom(Random r, IntVar[] v, int depth) {
    int kinds = depth > 0 ? 34 : 26;
    int k = r.nextInt(kinds);
    int[] p = ints(r, 3);
    IntVar x = v[p[0]];
    IntVar y = v[p[1]];
    IntVar z = v[p[2]];
    IntVar b = v[INTS + r.nextInt(BOOLS)];
    IntVar[] bs = pick(v, bools(r, 2 + r.nextInt(2)));
    return switch (k) {
      case 0 -> new XeqC(x, c(r));
      case 1 -> new XneqC(x, c(r));
      case 2 -> new XltY(x, y);
      case 3 -> new XlteqY(x, y);
      case 4 -> new XeqY(x, y);
      case 5 -> new XneqY(x, y);
      case 6 -> new XplusYeqC(x, y, c(r));
      case 7 -> new XplusCeqZ(x, c(r), y);
      case 8 ->
          new LinearInt(
              new IntVar[] {x, y}, new int[] {1 + r.nextInt(2), -1 - r.nextInt(2)}, rel(r), c(r));
      case 9 -> new In(x, dom(r));
      case 10 -> new XgtC(x, c(r));
      case 11 -> new XlteqC(x, c(r));
      case 12 -> new XplusYlteqZ(x, y, z);
      case 13 -> new XplusYeqZ(x, y, z);
      case 14 -> new AndBoolSimple(bs[0], bs[1], b);
      case 15 -> new OrBoolSimple(bs[0], bs[1], b);
      case 16 -> new XorBool(bs, b);
      case 17 -> new EqBool(bs, b);
      case 18 -> new IfThenBool(bs[0], bs[1], b);
      case 19 -> new IfThenElseBool((BooleanVar) bs[0], (BooleanVar) bs[1], (BooleanVar) b);
      case 20 -> new AndBoolVector(bs, b);
      case 21 -> new OrBoolVector(bs, b);
      case 22 -> new SumBool(bs, rel(r), y);
      case 23 -> new Count(new IntVar[] {x, y}, z, c(r));
      case 24 -> new BoolClause(new IntVar[] {bs[0]}, new IntVar[] {bs[1]});
      case 25 ->
          new LinearIntDom(new IntVar[] {x, y}, new int[] {1, 1 + r.nextInt(2)}, rel(r), c(r));
      case 26 -> new And(atom(r, v, depth - 1), atom(r, v, depth - 1));
      case 27 -> new Or(atom(r, v, depth - 1), atom(r, v, depth - 1));
      case 28 -> new Not(atom(r, v, depth - 1));
      case 29 -> new Eq(atom(r, v, depth - 1), atom(r, v, depth - 1));
      case 30 -> new Implies(b, atom(r, v, depth - 1));
      case 31 -> new IfThen(atom(r, v, depth - 1), atom(r, v, depth - 1));
      case 32 ->
          new IfThenElse(atom(r, v, depth - 1), atom(r, v, depth - 1), atom(r, v, depth - 1));
      default -> new Xor(atom(r, v, depth - 1), b);
    };
  }

  static String rel(Random r) {
    return new String[] {"==", "!=", "<", "<=", ">", ">="}[r.nextInt(6)];
  }

  static List<Case> cases() {
    List<Case> l = new ArrayList<>();
    l.add(new Case("And", (r, v) -> new And(atom(r, v, 1), atom(r, v, 1))));
    l.add(new Case("Or", (r, v) -> new Or(atom(r, v, 1), atom(r, v, 1))));
    l.add(new Case("Not", (r, v) -> new Not(atom(r, v, 1))));
    l.add(new Case("Eq", (r, v) -> new Eq(atom(r, v, 1), atom(r, v, 1))));
    l.add(new Case("Xor", (r, v) -> new Xor(atom(r, v, 1), v[INTS + r.nextInt(BOOLS)])));
    l.add(new Case("Implies", (r, v) -> new Implies(v[INTS + r.nextInt(BOOLS)], atom(r, v, 1))));
    l.add(
        new Case(
            "ImpliesNot", (r, v) -> new ImpliesNot(v[INTS + r.nextInt(BOOLS)], atom(r, v, 1))));
    l.add(new Case("IfThen", (r, v) -> new IfThen(atom(r, v, 1), atom(r, v, 1))));
    l.add(
        new Case(
            "IfThenElse", (r, v) -> new IfThenElse(atom(r, v, 1), atom(r, v, 1), atom(r, v, 1))));
    l.add(new Case("Reified", (r, v) -> new Reified(atom(r, v, 1), v[INTS + r.nextInt(BOOLS)])));
    l.add(new Case("Atom", (r, v) -> atom(r, v, 0)));
    l.add(new Case("AndBoolSimple", (r, v) -> new AndBoolSimple(v[3], v[4], v[5])));
    l.add(new Case("OrBoolSimple", (r, v) -> new OrBoolSimple(v[3], v[4], v[5])));
    l.add(new Case("AndBoolVector", (r, v) -> new AndBoolVector(new IntVar[] {v[3], v[4]}, v[5])));
    l.add(new Case("OrBoolVector", (r, v) -> new OrBoolVector(new IntVar[] {v[3], v[4]}, v[5])));
    l.add(new Case("XorBool", (r, v) -> new XorBool(new IntVar[] {v[3], v[4]}, v[5])));
    l.add(new Case("EqBool", (r, v) -> new EqBool(new IntVar[] {v[3], v[4]}, v[5])));
    l.add(new Case("IfThenBool", (r, v) -> new IfThenBool(v[3], v[4], v[5])));
    l.add(
        new Case(
            "IfThenElseBool",
            (r, v) -> new IfThenElseBool((BooleanVar) v[3], (BooleanVar) v[4], (BooleanVar) v[5])));
    l.add(
        new Case(
            "BoolClause",
            (r, v) -> new BoolClause(new IntVar[] {v[3], v[4]}, new IntVar[] {v[5]})));
    l.add(
        new Case("SumBool", (r, v) -> new SumBool(new IntVar[] {v[3], v[4], v[5]}, rel(r), v[0])));
    l.add(new Case("SumInt", (r, v) -> new SumInt(new IntVar[] {v[0], v[1]}, rel(r), v[2])));
    l.add(
        new Case(
            "LinearInt",
            (r, v) ->
                new LinearInt(
                    new IntVar[] {v[0], v[1], v[2]},
                    new int[] {c(r), c(r), 1 + r.nextInt(2)},
                    rel(r),
                    c(r))));
    l.add(
        new Case(
            "LinearIntDom",
            (r, v) ->
                new LinearIntDom(
                    new IntVar[] {v[0], v[1], v[2]},
                    new int[] {c(r), c(r), 1 + r.nextInt(2)},
                    rel(r),
                    c(r))));
    l.add(new Case("AllEqual", (r, v) -> new AllEqual(new IntVar[] {v[0], v[1], v[2]})));
    l.add(new Case("Count", (r, v) -> new Count(new IntVar[] {v[0], v[1]}, v[2], c(r))));
    l.add(
        new Case(
            "CountBounds",
            (r, v) ->
                new CountBounds(
                    new IntVar[] {v[0], v[1], v[2]}, c(r), r.nextInt(2), 1 + r.nextInt(2))));
    l.add(
        new Case(
            "CountVar",
            (r, v) -> new CountVar(new IntVar[] {v[0], v[1]}, v[2], v[INTS + r.nextInt(BOOLS)])));
    l.add(
        new Case(
            "AtLeast", (r, v) -> new AtLeast(new IntVar[] {v[0], v[1], v[2]}, r.nextInt(3), c(r))));
    l.add(
        new Case(
            "AtMost", (r, v) -> new AtMost(new IntVar[] {v[0], v[1], v[2]}, r.nextInt(3), c(r))));
    l.add(new Case("Member", (r, v) -> new Member(new IntVar[] {v[0], v[1]}, v[2])));
    l.add(new Case("Distance", (r, v) -> new Distance(v[0], v[1], v[2])));
    l.add(new Case("AbsXeqY", (r, v) -> new AbsXeqY(v[0], v[1], r.nextBoolean())));
    l.add(new Case("XplusClteqZImplied", (r, v) -> new XplusClteqZImplied(v[3], v[0], c(r), v[1])));
    l.add(
        new Case(
            "XplusClteqZImpliedNot", (r, v) -> new XplusClteqZImpliedNot(v[3], v[0], c(r), v[1])));
    l.add(new Case("XmulCeqZ", (r, v) -> new XmulCeqZ(v[0], c(r), v[1])));
    l.add(new Case("XmulYeqC", (r, v) -> new XmulYeqC(v[0], v[1], c(r))));
    l.add(new Case("XplusYgtC", (r, v) -> new XplusYgtC(v[0], v[1], c(r))));
    l.add(new Case("XplusCneqZ", (r, v) -> new XplusCneqZ(v[0], c(r), v[1])));
    l.add(new Case("XplusClteqZ", (r, v) -> new XplusClteqZ(v[0], c(r), v[1])));
    l.add(new Case("XgteqY", (r, v) -> new XgteqY(v[0], v[1])));
    l.add(new Case("XgtY", (r, v) -> new XgtY(v[0], v[1])));
    l.add(new Case("XgteqC", (r, v) -> new XgteqC(v[0], c(r))));
    l.add(new Case("XltC", (r, v) -> new XltC(v[0], c(r))));
    return l;
  }

  /** The counts of one case. */
  static final class Stats {
    int instances;
    int rejected;
    int entailmentMissed;
    int disentailmentMissed;
    int trueGap;
    int falseGap;
    int fixedTrueGap;
    int nestedWeaker;
    final List<String> bugs = new ArrayList<>();
    String firstGap;

    void gap(String what) {
      if (firstGap == null) {
        firstGap = what;
      }
    }
  }

  IntVar[] vars(Store s, IntDomain[] d) {
    IntVar[] v = new IntVar[INTS + BOOLS];
    for (int i = 0; i < v.length; i++) {
      v[i] =
          i < INTS
              ? new IntVar(s, "x" + i, d[i].cloneLight())
              : new BooleanVar(s, "b" + i, d[i].min(), d[i].max());
    }
    return v;
  }

  boolean holds(Case cs, long seed, int[] t) {
    Store s = new Store();
    IntVar[] v = new IntVar[INTS + BOOLS];
    for (int i = 0; i < v.length; i++) {
      v[i] = i < INTS ? new IntVar(s, "x" + i, t[i], t[i]) : new BooleanVar(s, "b" + i, t[i], t[i]);
    }
    PrimitiveConstraint c = cs.make.apply(new Random(seed), v);
    try {
      s.impose(c);
      return s.consistency();
    } catch (org.jacop.core.FailException _) {
      return false;
    }
  }

  static void enumerate(IntDomain[] d, int i, int[] t, List<int[]> out) {
    if (i == d.length) {
      out.add(t.clone());
      return;
    }
    for (var e = d[i].valueEnumeration(); e.hasMoreElements(); ) {
      t[i] = e.nextElement();
      enumerate(d, i + 1, t, out);
    }
  }

  /** For each variable, the values that have a support among the tuples. */
  static IntDomain[] supports(List<int[]> tuples, int n) {
    IntDomain[] s = new IntDomain[n];
    for (int i = 0; i < n; i++) {
      s[i] = new IntervalDomain();
    }
    for (int[] t : tuples) {
      for (int i = 0; i < n; i++) {
        s[i].unionAdapt(t[i], t[i]);
      }
    }
    return s;
  }

  enum Mode {
    TRUE_LATE,
    FALSE_LATE,
    TRUE_EARLY,
    IMPOSED
  }

  /**
   * Runs one mode. Returns the domains after propagation, or null on failure; a thrown exception is
   * reported as a bug.
   */
  IntDomain[] run(Case cs, long seed, IntDomain[] d, Mode mode, int[] bOut) {
    Store s = new Store();
    IntVar[] v = vars(s, d);
    PrimitiveConstraint c = cs.make.apply(new Random(seed), v);
    BooleanVar b = new BooleanVar(s, "r", mode == Mode.TRUE_EARLY ? 1 : 0, 1);
    try {
      if (mode == Mode.IMPOSED) {
        s.impose(c);
      } else {
        s.impose(new Reified(c, b));
      }
      if (!s.consistency()) {
        return null;
      }
      if (mode == Mode.TRUE_LATE || mode == Mode.FALSE_LATE) {
        if (bOut != null) {
          bOut[0] = b.singleton() ? b.value() : -1;
        }
        s.setLevel(s.level + 1);
        int want = mode == Mode.TRUE_LATE ? 1 : 0;
        if (!b.domain.contains(want)) {
          return null;
        }
        b.domain.in(s.level, b, want, want);
        if (!s.consistency()) {
          return null;
        }
      }
    } catch (org.jacop.core.FailException _) {
      return null;
    }
    IntDomain[] out = new IntDomain[v.length];
    for (int i = 0; i < v.length; i++) {
      out[i] = v[i].dom().cloneLight();
    }
    return out;
  }

  /** Brute-force check of the pruning of one mode; returns false on a gap. */
  boolean check(
      Stats st, String tag, String where, IntDomain[] got, IntDomain[] sup, boolean expectFail) {
    if (got == null) {
      if (!expectFail) {
        st.bugs.add(tag + " failed with supported tuples: " + where);
      }
      return true;
    }
    if (expectFail) {
      st.gap(tag + " no failure without support: " + where);
      return false;
    }
    boolean exact = true;
    for (int i = 0; i < got.length; i++) {
      if (!got[i].contains(sup[i])) {
        st.bugs.add(
            tag
                + " removed a supported value of v"
                + i
                + " "
                + sup[i]
                + " -> "
                + got[i]
                + ": "
                + where);
        return true;
      }
      if (!sup[i].contains(got[i])) {
        exact = false;
      }
    }
    if (!exact) {
      st.gap(tag + " kept an unsupported value: " + where);
    }
    return exact;
  }

  Stats runCase(Case cs, Random master) {
    Stats st = new Stats();
    int n = INTS + BOOLS;
    for (int trial = 0; trial < TRIALS; trial++) {
      long seed = master.nextLong();
      Random dr = new Random(seed ^ 0x5DEECE66DL);
      IntDomain[] d = new IntDomain[n];
      for (int i = 0; i < n; i++) {
        if (i < INTS) {
          d[i] = dom(dr);
        } else {
          int k = dr.nextInt(4);
          d[i] = new IntervalDomain(k == 1 ? 1 : 0, k == 0 ? 0 : 1);
        }
      }
      try {
        // the constructor may reject the arguments
        cs.make.apply(new Random(seed), vars(new Store(), d));
      } catch (IllegalArgumentException _) {
        st.rejected++;
        continue;
      }
      st.instances++;
      List<int[]> all = new ArrayList<>();
      enumerate(d, 0, new int[n], all);
      List<int[]> yes = new ArrayList<>();
      List<int[]> no = new ArrayList<>();
      for (int[] t : all) {
        (holds(cs, seed, t) ? yes : no).add(t);
      }
      StringBuilder w = new StringBuilder();
      w.append(cs.make.apply(new Random(seed), vars(new Store(), d))).append(" seed ").append(seed);
      String where = w.toString();
      try {
        int[] bOpen = new int[1];
        IntDomain[] t1 = run(cs, seed, d, Mode.TRUE_LATE, bOpen);
        // with b open nothing may be fixed wrongly
        if (bOpen[0] == 1 && !no.isEmpty()) {
          st.bugs.add("b fixed to 1 with a tuple that violates c: " + where);
        } else if (bOpen[0] == 0 && !yes.isEmpty()) {
          st.bugs.add("b fixed to 0 with a tuple that satisfies c: " + where);
        }
        if (no.isEmpty() && bOpen[0] != 1) {
          st.entailmentMissed++;
          st.gap("entailment missed: " + where);
        }
        if (yes.isEmpty() && bOpen[0] != 0) {
          st.disentailmentMissed++;
          st.gap("disentailment missed: " + where);
        }
        IntDomain[] supYes = supports(yes, n);
        IntDomain[] supNo = supports(no, n);
        if (!check(st, "b=1 late", where, t1, supYes, yes.isEmpty())) {
          st.trueGap++;
        }
        IntDomain[] f1 = run(cs, seed, d, Mode.FALSE_LATE, null);
        if (!check(st, "b=0 late", where, f1, supNo, no.isEmpty())) {
          st.falseGap++;
        }
        IntDomain[] e1 = run(cs, seed, d, Mode.TRUE_EARLY, null);
        if (!check(st, "b=1 early", where, e1, supYes, yes.isEmpty())) {
          st.fixedTrueGap++;
        }
        IntDomain[] imp = run(cs, seed, d, Mode.IMPOSED, null);
        check(st, "imposed", where, imp, supYes, yes.isEmpty());
        if (imp != null && t1 == null) {
          // nested failed, imposed did not: fine
        } else if (imp != null) {
          for (int i = 0; i < n; i++) {
            if (!t1[i].contains(imp[i])) {
              st.nestedWeaker++;
              st.gap("imposed pruned less than nested on v" + i + ": " + where);
              break;
            }
            if (!imp[i].contains(t1[i])) {
              st.nestedWeaker++;
              st.gap(
                  "nested (b=1 late) pruned less than imposed on v"
                      + i
                      + " "
                      + imp[i]
                      + " vs "
                      + t1[i]
                      + ": "
                      + where);
              break;
            }
          }
        }
      } catch (RuntimeException | AssertionError e) {
        st.bugs.add("exception " + e + ": " + where);
      }
      if (st.bugs.size() > 5) {
        break;
      }
    }
    return st;
  }

  @Test
  void composedConstraintsAreSoundAndReportTheirGaps() {
    Random master = new Random(SEED);
    Map<String, Stats> all = new TreeMap<>();
    List<String> bugs = new ArrayList<>();
    for (Case cs : cases()) {
      Random r = new Random(master.nextLong());
      if (!ONLY.isEmpty() && !List.of(ONLY.split(",")).contains(cs.name)) {
        continue;
      }
      Stats st = runCase(cs, r);
      all.put(cs.name, st);
      for (String b : st.bugs) {
        bugs.add(cs.name + ": " + b);
      }
    }
    if (REPORT || !bugs.isEmpty()) {
      System.out.printf(
          "%-22s %6s %5s %6s %6s %6s %6s %6s %6s%n",
          "case", "inst", "rej", "ent", "disent", "b1", "b0", "b1early", "nested");
      for (var e : all.entrySet()) {
        Stats s = e.getValue();
        System.out.printf(
            "%-22s %6d %5d %6d %6d %6d %6d %6d %6d %s%n",
            e.getKey(),
            s.instances,
            s.rejected,
            s.entailmentMissed,
            s.disentailmentMissed,
            s.trueGap,
            s.falseGap,
            s.fixedTrueGap,
            s.nestedWeaker,
            s.firstGap == null ? "" : s.firstGap);
      }
    }
    for (String b : bugs) {
      System.out.println("BUG " + b);
    }
    assertTrue(
        bugs.isEmpty(),
        bugs.size() + " soundness failures, first: " + (bugs.isEmpty() ? "" : bugs.get(0)));
  }
}
