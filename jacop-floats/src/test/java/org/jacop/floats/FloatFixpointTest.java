/*
 * FloatFixpointTest.java
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

package org.jacop.floats;

import static org.junit.jupiter.api.Assertions.fail;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.And;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Eq;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.IfThenElse;
import org.jacop.constraints.Implies;
import org.jacop.constraints.Not;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Xor;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.FloatPropagationFuzzTest.Case;
import org.jacop.floats.FloatPropagationFuzzTest.Iv;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatVar;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Checks float constraints at the fixpoint of their propagation and in reifications, over the
 * single cases of {@link FloatPropagationFuzzTest}. Every check has a margin far above the
 * precision, since an interval narrower than the precision is one value.
 *
 * <p>{@link #propagationReachesTheFreshFixpoint}: random dives of splits over a box around a near
 * solution, the constraint plain, under {@link Not} or under {@link Reified}. At every node the
 * same constraint imposed in a fresh store over the current domains must not fail and must not
 * narrow a bound by more than a small part of its interval (a missed wake-up or a propagator that
 * does not propagate its own pruning); {@code satisfied()} must not hold while a sampled point of
 * the box violates the relation by the margin, nor {@code notSatisfied()} while the box holds a
 * solution the margin away from its ends.
 *
 * <p>{@link #reificationsDecideFixedTuples}: tuples of points that satisfy or violate the relations
 * by the margin, decided by imposing each primitive constraint alone on fixed variables. Composed
 * constraints (And, Or, Not, IfThen, IfThenElse, Implies, Xor, Eq) on the fixed tuple must succeed
 * exactly when their meaning holds, and {@code Reified(c, b)} must not give b a wrong value, with b
 * open, fixed before imposing or fixed after.
 *
 * <p>Margins and artefacts: a fresh store that narrows a bound by less than {@code floatfix.share}
 * (default 1 %) of its interval, or by less than the margin of the largest magnitude of the box, is
 * a slow convergence or rounding; a fresh store that fails while every interval is within that
 * margin is a residual of the rounding of the relation; a predicate tuple counts as true or false
 * only if it holds or fails over the margin around it, and a functional tuple as true only if it
 * holds exactly over the reals.
 *
 * <p>Trials per case: {@code floatfix.trials} (default 200, about six minutes for all cases);
 * {@code floats.fuzz.cases} selects cases by parts of their names. It is not in any profile; run it
 * on demand:
 *
 * <pre>
 * mvn -Pmin -pl jacop-floats -am test -Dtest=FloatFixpointTest -Dsurefire.failIfNoSpecifiedTests=false \
 *     -Dsurefire.rerunFailingTestsCount=0 -Dfloatfix.trials=1000 [-Dfloatfix.report=true]
 * </pre>
 */
class FloatFixpointTest {

  private static final int TRIALS = Integer.getInteger("floatfix.trials", 200);

  private static final long SEED = Long.getLong("floatfix.seed", 1L);

  /** A narrowing below this share of the interval is a slow convergence, not a missed event. */
  private static final double SHARE =
      Double.parseDouble(System.getProperty("floatfix.share", "0.01"));

  private static final boolean REPORT = Boolean.getBoolean("floatfix.report");

  static Stream<Arguments> cases() {
    return FloatPropagationFuzzTest.cases();
  }

  /** The margin a point violates or satisfies a relation by: far above the precision. */
  private static double margin(double magnitude) {
    return Math.max(100 * FloatDomain.precision(), 1e6 * Math.ulp(magnitude));
  }

  // ---------------------------------------------------------------------------------------------
  // fixpoint, satisfied() and notSatisfied() at the nodes of dives

  @ParameterizedTest(name = "{0}")
  @MethodSource("cases")
  void propagationReachesTheFreshFixpoint(String name, Case c) {
    Random random = new Random(SEED * 1_000_003L + name.hashCode());
    List<String> failures = new ArrayList<>();
    long[] counts = new long[3];
    for (int t = 0; t < TRIALS && failures.size() < 3; t++) {
      long seed = random.nextLong();
      String failure = dive(c, new Random(seed), counts);
      if (failure != null) {
        failures.add("trial seed " + seed + ": " + failure);
      }
    }
    if (REPORT) {
      System.out.printf(
          "%-40s nodes %6d slow %5d%s%n",
          name, counts[0], counts[1], counts[2] > 0 ? " fresh-narrower " + counts[2] : "");
    }
    if (!failures.isEmpty()) {
      fail(name + "\n  " + String.join("\n  ", failures));
    }
  }

  private enum Wrap {
    PLAIN,
    NOT,
    REIFIED
  }

  private static String dive(Case c, Random random, long[] counts) {
    int n = c.isFloat().length;
    double[] point = point(c, random);
    if (point == null) {
      return null;
    }
    Constraint[] probe;
    Store probeStore = new Store();
    try {
      probe = c.build().apply(vars(probeStore, c, box(c, point, random)));
    } catch (IllegalArgumentException e) {
      return null;
    }
    boolean primitive = probe.length == 1 && probe[0] instanceof PrimitiveConstraint;
    Wrap wrap = primitive ? Wrap.values()[random.nextInt(3)] : Wrap.PLAIN;
    double[][] box = box(c, point, random);
    Store store = new Store();
    Var[] x = vars(store, c, box);
    if (wrap == Wrap.REIFIED) {
      x = Arrays.copyOf(x, n + 1);
      x[n] = new IntVar(store, "b", 0, 1);
    }
    Constraint[] cs;
    try {
      cs = build(c, wrap, x);
      for (Constraint k : cs) {
        store.impose(k);
      }
    } catch (IllegalArgumentException _) {
      return null;
    } catch (FailException _) {
      return null;
    } catch (RuntimeException e) {
      return "impose threw " + e + " " + Arrays.toString(x);
    }
    StringBuilder path = new StringBuilder();
    String where = wrap + " " + Arrays.toString(cs) + " over " + Arrays.toString(x);
    boolean ok;
    try {
      ok = store.consistency();
    } catch (FailException _) {
      ok = false;
    } catch (RuntimeException e) {
      return "consistency threw " + e + "\n    " + where;
    }
    for (int depth = 0; depth < 60 && ok; depth++) {
      counts[0]++;
      String at = where + "\n    path:" + path + "\n    now " + Arrays.toString(x);
      String error = checkNode(c, wrap, x, cs, random, at, counts);
      if (error != null) {
        return error;
      }
      List<Integer> open = new ArrayList<>();
      for (int i = 0; i < x.length; i++) {
        if (!x[i].singleton()) {
          open.add(i);
        }
      }
      if (open.isEmpty()) {
        return null;
      }
      int i = open.get(random.nextInt(open.size()));
      double[] d = split(x[i], random);
      ok = false;
      for (int side = 0; side < 2 && !ok; side++) {
        store.setLevel(store.level + 1);
        double lo = d[2 * side];
        double hi = d[2 * side + 1];
        try {
          if (x[i] instanceof IntVar v) {
            v.domain.in(store.level, v, (int) lo, (int) hi);
          } else {
            FloatVar f = (FloatVar) x[i];
            f.domain.in(store.level, f, lo, hi);
          }
          ok = store.consistency();
        } catch (FailException _) {
          ok = false;
        } catch (RuntimeException e) {
          return "consistency threw " + e + "\n    " + at;
        }
        if (ok) {
          path.append(' ').append(x[i].id()).append(" in ").append(lo).append("..").append(hi);
        } else {
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
        }
      }
    }
    return null;
  }

  private static double[] split(Var v, Random random) {
    if (v instanceof IntVar x) {
      int value = x.min() + random.nextInt(x.max() - x.min());
      return random.nextBoolean()
          ? new double[] {x.min(), value, value + 1, x.max()}
          : new double[] {value + 1, x.max(), x.min(), value};
    }
    FloatVar f = (FloatVar) v;
    double lo = f.min();
    double hi = f.max();
    double mid = random.nextInt(3) == 0 ? lo + (hi - lo) * random.nextDouble() : lo / 2 + hi / 2;
    if (!(mid > lo && mid < hi)) {
      mid = lo / 2 + hi / 2;
    }
    return random.nextBoolean() ? new double[] {lo, mid, mid, hi} : new double[] {mid, hi, lo, mid};
  }

  private static Constraint[] build(Case c, Wrap wrap, Var[] x) {
    int n = c.isFloat().length;
    Constraint[] inner = c.build().apply(Arrays.copyOf(x, n));
    return switch (wrap) {
      case PLAIN -> inner;
      case NOT -> new Constraint[] {new Not((PrimitiveConstraint) inner[0])};
      case REIFIED -> new Constraint[] {new Reified((PrimitiveConstraint) inner[0], (IntVar) x[n])};
    };
  }

  private static String checkNode(
      Case c, Wrap wrap, Var[] x, Constraint[] cs, Random random, String at, long[] counts) {
    int n = c.isFloat().length;
    // satisfied() and notSatisfied() of the constraint and, under a wrapping, of the inner one
    List<PrimitiveConstraint> checked = new ArrayList<>();
    for (Constraint k : cs) {
      if (k instanceof Not not) {
        checked.add(not.negatedConstraint());
      } else if (k instanceof Reified reified) {
        checked.add(reified.c);
      } else if (k instanceof PrimitiveConstraint p) {
        checked.add(p);
      } else if (k instanceof SatisfiedPresent sp && cs.length == 1 && sp.satisfied()) {
        String violated = violated(c, x, random);
        if (violated != null) {
          return "satisfied() with the violating point " + violated + "\n    " + at;
        }
      }
    }
    if (cs.length == 1) {
      for (PrimitiveConstraint p : checked) {
        if (p.satisfied()) {
          String violated = violated(c, x, random);
          if (violated != null) {
            return p.getClass().getSimpleName()
                + ".satisfied() with the violating point "
                + violated
                + "\n    "
                + at;
          }
        }
        if (p.notSatisfied()) {
          String solution = solution(c, x, random);
          if (solution != null) {
            return p.getClass().getSimpleName()
                + ".notSatisfied() with the solution "
                + solution
                + "\n    "
                + at;
          }
        }
      }
    }
    return fresh(c, wrap, x, at, counts);
  }

  /** A point of the box that violates the relation by the margin, or null. */
  private static String violated(Case c, Var[] x, Random random) {
    int n = c.isFloat().length;
    for (int s = 0; s < 40; s++) {
      double[] p = new double[n];
      for (int i = 0; i < n; i++) {
        p[i] = sample(x[i], random);
      }
      if (c.holds().applyAsInt(widened(c, p)) == -1) {
        return Arrays.toString(p);
      }
    }
    return null;
  }

  /** A solution of the relation in the box, the margin away from the ends of its intervals. */
  private static String solution(Case c, Var[] x, Random random) {
    int n = c.isFloat().length;
    for (int s = 0; s < 40; s++) {
      double[] p = new double[n];
      for (int i = 0; i < n; i++) {
        p[i] = sample(x[i], random);
      }
      Iv[] box;
      if (c.fix() != null) {
        box = c.enclose().apply(points(p));
        if (box == null || box[c.dep()] == null || !box[c.dep()].bounded()) {
          continue;
        }
      } else {
        if (c.holds().applyAsInt(widened(c, p)) != 1) {
          continue;
        }
        box = points(p);
      }
      if (inside(x, box, c)) {
        return Arrays.toString(box);
      }
    }
    return null;
  }

  /** Whether each coordinate of the box lies in its domain the margin away from its ends. */
  private static boolean inside(Var[] x, Iv[] box, Case c) {
    for (int i = 0; i < box.length; i++) {
      if (x[i] instanceof IntVar v) {
        if (!box[i].isPoint() || !v.domain.contains((int) box[i].dlo())) {
          return false;
        }
        continue;
      }
      FloatDomain d = ((FloatVar) x[i]).dom();
      double lo = box[i].dlo();
      double hi = box[i].dhi();
      double m = margin(Math.max(Math.abs(lo), Math.abs(hi)));
      if (i == c.dep() || c.fix() == null) {
        boolean in = false;
        for (int k = 0; k < d.noIntervals() && !in; k++) {
          in = d.leftElement(k) + m <= lo && hi <= d.rightElement(k) - m;
        }
        if (!in) {
          return false;
        }
      } else if (!d.contains(lo) || !d.contains(hi)) {
        return false;
      }
    }
    return true;
  }

  private static Iv[] widened(Case c, double[] p) {
    Iv[] box = points(p);
    double largest = 0;
    for (int i = 0; i < p.length; i++) {
      if (c.isFloat()[i]) {
        largest = Math.max(largest, Math.abs(p[i]));
      }
    }
    BigDecimal m = new BigDecimal(margin(largest));
    for (int i = 0; i < p.length; i++) {
      if (c.isFloat()[i]) {
        box[i] = Iv.of(box[i].lo().subtract(m), box[i].hi().add(m));
      }
    }
    return box;
  }

  private static Iv[] points(double[] p) {
    Iv[] box = new Iv[p.length];
    for (int i = 0; i < p.length; i++) {
      box[i] = Iv.of(p[i]);
    }
    return box;
  }

  private static double sample(Var v, Random random) {
    if (v instanceof IntVar x) {
      return x.dom().getElementAt(random.nextInt(x.getSize()));
    }
    FloatDomain d = ((FloatVar) v).dom();
    int k = random.nextInt(d.noIntervals());
    double lo = d.leftElement(k);
    double hi = d.rightElement(k);
    return switch (random.nextInt(4)) {
      case 0 -> lo;
      case 1 -> hi;
      default -> Math.min(hi, lo + (hi - lo) * random.nextDouble());
    };
  }

  /** Imposes the constraint in a fresh store over the current domains: the difference, or null. */
  private static String fresh(Case c, Wrap wrap, Var[] x, String at, long[] counts) {
    Store store = new Store();
    Var[] y = new Var[x.length];
    for (int i = 0; i < x.length; i++) {
      if (x[i] instanceof IntVar v) {
        y[i] = new IntVar(store, x[i].id(), v.dom().cloneLight());
      } else {
        y[i] = new FloatVar(store, x[i].id(), (FloatDomain) ((FloatVar) x[i]).dom().cloneLight());
      }
    }
    boolean ok;
    try {
      for (Constraint k : build(c, wrap, y)) {
        store.impose(k);
      }
      ok = store.consistency();
    } catch (FailException _) {
      ok = false;
    } catch (IllegalArgumentException _) {
      return null;
    } catch (RuntimeException e) {
      return "a fresh store threw " + e + "\n    " + at;
    }
    if (!ok) {
      if (narrow(x)) {
        // every interval is within the rounding of its magnitude: a residual of the rounding
        return null;
      }
      return "a fresh store fails\n    " + at;
    }
    for (int i = 0; i < x.length; i++) {
      if (x[i] instanceof IntVar v) {
        if (!v.dom().eq(((IntVar) y[i]).dom())) {
          return "a fresh store prunes " + x[i] + " to " + y[i] + "\n    " + at;
        }
        continue;
      }
      FloatVar f = (FloatVar) x[i];
      FloatVar g = (FloatVar) y[i];
      double width = f.max() - f.min();
      double cut = Math.max(g.min() - f.min(), f.max() - g.max());
      if (cut > 0) {
        // the relation is decided at the largest magnitude of the box
        if (cut > margin(largest(x)) && cut > SHARE * width) {
          counts[2]++;
          return "a fresh store narrows " + x[i] + " to " + y[i] + "\n    " + at;
        }
        counts[1]++;
      }
    }
    return null;
  }

  /** The largest magnitude of a bound of a float variable. */
  private static double largest(Var[] x) {
    double largest = 0;
    for (Var v : x) {
      if (v instanceof FloatVar f) {
        largest = Math.max(largest, Math.max(Math.abs(f.min()), Math.abs(f.max())));
      }
    }
    return largest;
  }

  /**
   * Whether every float interval is narrower than the margin of the largest magnitude of the box,
   * at which the relation is decided in doubles.
   */
  private static boolean narrow(Var[] x) {
    double m = margin(largest(x));
    for (Var v : x) {
      if (v instanceof FloatVar f && f.max() - f.min() > m) {
        return false;
      }
    }
    return true;
  }

  // ---------------------------------------------------------------------------------------------
  // reifications and compositions on fixed tuples

  /** The primitive single cases, for compositions. */
  private static final List<Case> PRIMITIVES = primitives();

  private static List<Case> primitives() {
    List<Case> list = new ArrayList<>();
    for (Case c : FloatPropagationFuzzTest.singleCases()) {
      if (!c.primitive()) {
        continue;
      }
      list.add(c);
    }
    return list;
  }

  /** A fixed tuple of a case that satisfies or violates the relation by the margin. */
  private record Tuple(Case c, double[] p, boolean holds) {}

  @ParameterizedTest(name = "{0}")
  @MethodSource("cases")
  void reificationsDecideFixedTuples(String name, Case c) {
    if (!c.primitive()) {
      return;
    }
    Random random = new Random(SEED * 1_000_033L + name.hashCode());
    List<String> failures = new ArrayList<>();
    long[] missed = new long[2];
    for (int t = 0; t < TRIALS && failures.size() < 3; t++) {
      Tuple p = tuple(c, random);
      if (p == null) {
        continue;
      }
      String f = reified(p, random, missed);
      if (f == null) {
        Tuple q = tuple(PRIMITIVES.get(random.nextInt(PRIMITIVES.size())), random);
        Tuple r = tuple(PRIMITIVES.get(random.nextInt(PRIMITIVES.size())), random);
        if (q != null && r != null) {
          f = composed(p, q, r, random);
        }
      }
      if (f != null) {
        failures.add(f);
      }
    }
    if (REPORT) {
      System.out.printf(
          "%-40s missed entailment %d missed disentailment %d%n", name, missed[0], missed[1]);
    }
    if (!failures.isEmpty()) {
      fail(name + "\n  " + String.join("\n  ", failures));
    }
  }

  /** A tuple decided by imposing the constraint alone on fixed variables, or null. */
  private static Tuple tuple(Case c, Random random) {
    for (int attempt = 0; attempt < 20; attempt++) {
      double[] p = point(c, random);
      if (p == null) {
        continue;
      }
      int n = p.length;
      if (random.nextBoolean()) {
        // move a float coordinate away from the solution
        int i = random.nextInt(n);
        if (c.isFloat()[i]) {
          double m = margin(Math.abs(p[i]));
          p[i] += (random.nextBoolean() ? 1 : -1) * m * (2 + random.nextInt(1000));
        } else {
          p[i] += random.nextBoolean() ? 1 : -1;
        }
      }
      int h = c.holds().applyAsInt(widened(c, p));
      boolean holds;
      if (h == -1) {
        holds = false;
      } else if (h == 1 || c.fix() != null && c.holds().applyAsInt(points(p)) == 1) {
        // a point that satisfies a functional relation exactly, over the reals (a predicate must
        // hold over the margin, since values within the precision are one value)
        holds = true;
      } else {
        continue;
      }
      Boolean alone = alone(c, p);
      if (alone == null) {
        continue;
      }
      if (alone != holds) {
        // the constraint alone decides the tuple otherwise: FloatPropagationFuzzTest's domain
        continue;
      }
      return new Tuple(c, p, holds);
    }
    return null;
  }

  private static Boolean alone(Case c, double[] p) {
    Store store = new Store();
    try {
      for (Constraint k : c.build().apply(fixed(store, c, p))) {
        store.impose(k);
      }
      return store.consistency();
    } catch (FailException _) {
      return false;
    } catch (RuntimeException _) {
      return null;
    }
  }

  private static Var[] fixed(Store store, Case c, double[] p) {
    Var[] x = new Var[p.length];
    for (int i = 0; i < p.length; i++) {
      x[i] =
          c.isFloat()[i]
              ? new FloatVar(store, "f" + i, p[i], p[i])
              : new IntVar(store, "x" + i, (int) p[i], (int) p[i]);
    }
    return x;
  }

  private static PrimitiveConstraint primitive(Store store, Tuple t) {
    return (PrimitiveConstraint) t.c().build().apply(fixed(store, t.c(), t.p()))[0];
  }

  /** Reified(c, b) with b open, fixed before imposing and fixed after. */
  private static String reified(Tuple t, Random random, long[] missed) {
    String what =
        "Reified " + t.c().name() + " at " + Arrays.toString(t.p()) + " (" + t.holds() + ")";
    for (int mode = 0; mode < 5; mode++) {
      Store store = new Store();
      IntVar b = new IntVar(store, "b", 0, 1);
      int value = mode % 2;
      boolean ok;
      try {
        if (mode == 1 || mode == 2) {
          b.domain.in(store.level, b, value, value);
        }
        store.impose(new Reified(primitive(store, t), b));
        ok = store.consistency();
        if (ok && mode >= 3) {
          store.setLevel(store.level + 1);
          b.domain.in(store.level, b, value, value);
          ok = store.consistency();
        }
      } catch (FailException _) {
        ok = false;
      } catch (RuntimeException e) {
        return what + " mode " + mode + " threw " + e;
      }
      if (mode == 0) {
        if (!ok) {
          return what + ": fails with b open";
        }
        if (b.singleton() && (b.value() == 1) != t.holds()) {
          return what + ": sets b = " + b.value();
        }
        if (!b.singleton()) {
          missed[t.holds() ? 0 : 1]++;
        }
        continue;
      }
      boolean right = (value == 1) == t.holds();
      if (right && !ok) {
        return what
            + ": fails with b = "
            + value
            + (mode >= 3 ? " after impose" : " before impose");
      }
      if (!right && ok) {
        missed[t.holds() ? 1 : 0]++;
      }
    }
    return null;
  }

  /** The composed constraints of three fixed tuples. */
  private static String composed(Tuple p, Tuple q, Tuple r, Random random) {
    String what =
        p.c().name()
            + " at "
            + Arrays.toString(p.p())
            + " ("
            + p.holds()
            + "), "
            + q.c().name()
            + " at "
            + Arrays.toString(q.p())
            + " ("
            + q.holds()
            + "), "
            + r.c().name()
            + " at "
            + Arrays.toString(r.p())
            + " ("
            + r.holds()
            + ")";
    for (int kind = 0; kind < 9; kind++) {
      Store store = new Store();
      PrimitiveConstraint a = primitive(store, p);
      PrimitiveConstraint b = primitive(store, q);
      PrimitiveConstraint e = primitive(store, r);
      IntVar bool = new IntVar(store, "b", 0, 1);
      int bv = random.nextInt(2);
      boolean expected;
      Constraint k;
      switch (kind) {
        case 0 -> {
          k = new And(a, b);
          expected = p.holds() && q.holds();
        }
        case 1 -> {
          k = new Or(a, b);
          expected = p.holds() || q.holds();
        }
        case 2 -> {
          k = new Not(a);
          expected = !p.holds();
        }
        case 3 -> {
          k = new IfThen(a, b);
          expected = !p.holds() || q.holds();
        }
        case 4 -> {
          k = new IfThenElse(a, b, e);
          expected = p.holds() ? q.holds() : r.holds();
        }
        case 5 -> {
          bool.domain.in(store.level, bool, bv, bv);
          k = new Implies(bool, a);
          expected = bv == 0 || p.holds();
        }
        case 6 -> {
          bool.domain.in(store.level, bool, bv, bv);
          k = new Xor(a, bool);
          expected = p.holds() != (bv == 1);
        }
        case 7 -> {
          k = new Eq(a, b);
          expected = p.holds() == q.holds();
        }
        default -> {
          k = new Not(new Or(a, new And(b, e)));
          expected = !(p.holds() || q.holds() && r.holds());
        }
      }
      boolean ok;
      try {
        store.impose(k);
        ok = store.consistency();
      } catch (FailException _) {
        ok = false;
      } catch (RuntimeException ex) {
        return what + ": " + k + " threw " + ex;
      }
      if (ok != expected) {
        return what + ": " + k + (ok ? " accepts" : " fails") + " (b = " + bv + ")";
      }
    }
    return null;
  }

  // ---------------------------------------------------------------------------------------------
  // points and boxes

  /** A point near a solution of the case, or null. */
  private static double[] point(Case c, Random random) {
    int n = c.isFloat().length;
    for (int attempt = 0; attempt < 100; attempt++) {
      // short decimals in every coordinate now and then, so that a solution is exact
      boolean quarters = random.nextInt(3) == 0;
      double[] p = new double[n];
      for (int i = 0; i < n; i++) {
        p[i] =
            c.isFloat()[i]
                ? c.lo()[i] + (c.hi()[i] - c.lo()[i]) * random.nextDouble()
                : (int) c.lo()[i] + random.nextInt((int) c.hi()[i] - (int) c.lo()[i] + 1);
        if (c.isFloat()[i] && (quarters || random.nextInt(4) == 0)) {
          p[i] = Math.round(p[i] * 4) / 4.0;
        }
      }
      if (c.fix() != null) {
        p = c.fix().apply(p);
        if (p == null) {
          continue;
        }
        return p;
      }
      if (c.holds().applyAsInt(points(p)) >= 0 || random.nextInt(4) == 0) {
        return p;
      }
    }
    return null;
  }

  private static double[][] box(Case c, double[] p, Random random) {
    double[][] box = new double[p.length][2];
    for (int i = 0; i < p.length; i++) {
      if (!c.isFloat()[i]) {
        box[i][0] = p[i] - random.nextInt(3);
        box[i][1] = p[i] + random.nextInt(3);
        continue;
      }
      double scale = 1 + Math.abs(p[i]);
      double[] widths = {0, 1e-9, 1e-4, 0.1, 1, 10};
      box[i][0] = p[i] - widths[random.nextInt(widths.length)] * scale * random.nextDouble();
      box[i][1] = p[i] + widths[random.nextInt(widths.length)] * scale * random.nextDouble();
    }
    return box;
  }

  private static Var[] vars(Store store, Case c, double[][] box) {
    Var[] x = new Var[box.length];
    for (int i = 0; i < box.length; i++) {
      if (c.isFloat()[i]) {
        FloatIntervalDomain d = new FloatIntervalDomain();
        d.unionAdapt(box[i][0], box[i][1]);
        x[i] = new FloatVar(store, "f" + i, d);
      } else {
        x[i] = new IntVar(store, "x" + i, (int) box[i][0], (int) box[i][1]);
      }
    }
    return x;
  }
}
