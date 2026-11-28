/*
 * FloatPropagationFuzzTest.java
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

package org.jacop.floats;

import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

import java.math.BigDecimal;
import java.math.MathContext;
import java.math.RoundingMode;
import java.time.Duration;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.List;
import java.util.Random;
import java.util.function.DoubleUnaryOperator;
import java.util.function.Function;
import java.util.function.IntFunction;
import java.util.function.ToDoubleFunction;
import java.util.function.ToIntFunction;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.constraints.AbsPeqR;
import org.jacop.floats.constraints.AcosPeqR;
import org.jacop.floats.constraints.AsinPeqR;
import org.jacop.floats.constraints.AtanPeqR;
import org.jacop.floats.constraints.CeilPeqX;
import org.jacop.floats.constraints.CosPeqR;
import org.jacop.floats.constraints.ElementFloat;
import org.jacop.floats.constraints.ElementFloatVariable;
import org.jacop.floats.constraints.ExpPeqR;
import org.jacop.floats.constraints.FloorPeqX;
import org.jacop.floats.constraints.HyperbolicPeqR;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.LnPeqR;
import org.jacop.floats.constraints.Max;
import org.jacop.floats.constraints.Min;
import org.jacop.floats.constraints.PdivCeqR;
import org.jacop.floats.constraints.PdivQeqR;
import org.jacop.floats.constraints.PeqC;
import org.jacop.floats.constraints.PeqQ;
import org.jacop.floats.constraints.PgtC;
import org.jacop.floats.constraints.PgtQ;
import org.jacop.floats.constraints.PgteqC;
import org.jacop.floats.constraints.PgteqQ;
import org.jacop.floats.constraints.PltC;
import org.jacop.floats.constraints.PltQ;
import org.jacop.floats.constraints.PlteqC;
import org.jacop.floats.constraints.PlteqQ;
import org.jacop.floats.constraints.PminusCeqR;
import org.jacop.floats.constraints.PminusQeqR;
import org.jacop.floats.constraints.PmulCeqR;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.constraints.PneqC;
import org.jacop.floats.constraints.PneqQ;
import org.jacop.floats.constraints.PowPeqR;
import org.jacop.floats.constraints.PplusCeqR;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.RoundPeqX;
import org.jacop.floats.constraints.SinPeqR;
import org.jacop.floats.constraints.SqrtPeqR;
import org.jacop.floats.constraints.SumFloat;
import org.jacop.floats.constraints.TanPeqR;
import org.jacop.floats.constraints.XeqP;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.search.DepthFirstSearch;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Checks the float propagators against the real relation they stand for, by brute force over
 * sampled points, with no tolerance.
 *
 * <p>Each trial draws a solution of the relation (or, under {@link Not}, a point that violates it),
 * builds a random box of intervals around it (some variables singleton, some float domains with a
 * hole) and samples further points of the box: these are the witnesses. A witness is a box of
 * doubles that is known to contain a real solution. For a predicate it is a point that satisfies
 * the relation exactly over the reals (checked in {@link BigDecimal}); for a function it is the
 * point of the arguments and an enclosure of the real value of the function, exact or rounded
 * outward to the next doubles for +, -, *, / and the other rational operations, and widened by the
 * error bound of {@link Math} (1 ulp, 2.5 for sinh, cosh and tanh) for the transcendental ones. The
 * constraint is imposed, plain or under {@link Not} or {@link Reified} when it is primitive, and a
 * random dive splits the intervals until every variable is singleton. At every node:
 *
 * <ul>
 *   <li>propagation keeps a part of every witness that lies inside the decisions, and fails only
 *       where no such witness exists: interval propagation is sound over the reals;
 *   <li>a node where every variable is singleton is a box that may contain a solution, by exact
 *       interval evaluation of the relation over it: no wrong solution is accepted;
 *   <li>nothing but {@link FailException} is thrown;
 *   <li>removing a level restores exactly the domains it started from.
 * </ul>
 *
 * <p>The only slack is the documented one of float domains: an interval narrower than {@link
 * FloatDomain#precision()} is one value, so a witness counts as kept when the domain comes within
 * the precision of it. Trials per case are {@code floats.fuzz.trials} (lower in the {@code min}
 * profile). To run it at volume or on chosen cases:
 *
 * <pre>
 * mvn -Pmin -pl jacop-floats test -Dtest=FloatPropagationFuzzTest \
 *     -Dsurefire.rerunFailingTestsCount=0 -Dfloats.fuzz.trials=20000 -Dfloats.fuzz.seed=7 \
 *     -Dfloats.fuzz.cases=PmulQeqR,Linear
 * </pre>
 */
class FloatPropagationFuzzTest {

  private static final int TRIALS = Integer.getInteger("floats.fuzz.trials", 400);

  private static final long SEED = Long.getLong("floats.fuzz.seed", 1L);

  /** Comma-separated parts of case names to run, e.g. {@code -Dfloats.fuzz.cases=Sin,Max}. */
  private static final String FILTER = System.getProperty("floats.fuzz.cases", "");

  /** Points sampled in the box per trial; those that satisfy the relation become witnesses. */
  private static final int SAMPLES = 60;

  /** At most this many decisions in one dive (a split halves one interval). */
  private static final int MAX_DECISIONS = 400;

  /** Prints, per case, how many trials reached a ground node, failed, or had witnesses. */
  private static final boolean STATS = Boolean.getBoolean("floats.fuzz.stats");

  // per case: trials run, witnesses, dives that reached a node with every variable singleton,
  // dives that ended in a failure on both branches
  private static final ThreadLocal<long[]> COUNTS = ThreadLocal.withInitial(() -> new long[4]);

  /** How a trial wraps the constraint. */
  enum Wrap {
    PLAIN,
    NOT,
    REIFIED
  }

  /**
   * One relation with its constraint.
   *
   * @param name the case name
   * @param isFloat for each coordinate, a float variable if true and an int variable if false
   * @param lo for each coordinate, the low end of the range a solution is drawn from
   * @param hi for each coordinate, the high end of that range
   * @param fix for a functional relation, recomputes the dependent coordinates of a point so that
   *     it is near a solution (null when there is none); null for a predicate
   * @param enclose for a functional relation, replaces the dependent coordinates of a box by an
   *     enclosure of their real values over the other coordinates of the box; null for a predicate
   * @param holds whether the relation holds over a box: 1 at every real point of it, -1 at none, 0
   *     when the evaluation cannot tell
   * @param build the constraints over variables of the coordinates
   * @param primitive whether the constraint is one {@link PrimitiveConstraint}, which is also
   *     checked under {@link Not} and {@link Reified}
   * @param dep the coordinate that fix computes, or -1
   */
  record Case(
      String name,
      boolean[] isFloat,
      double[] lo,
      double[] hi,
      UnaryOperator<double[]> fix,
      UnaryOperator<Iv[]> enclose,
      ToIntFunction<Iv[]> holds,
      Function<Var[], Constraint[]> build,
      boolean primitive,
      int dep) {}

  /**
   * A box of doubles that contains a real solution: a point in every coordinate but the computed
   * ones.
   */
  record Witness(double[] lo, double[] hi) {

    /** The box, or null when a coordinate is unbounded or empty. */
    static Witness of(Iv[] box) {
      double[] lo = new double[box.length];
      double[] hi = new double[box.length];
      for (int i = 0; i < box.length; i++) {
        if (box[i] == null || !box[i].bounded()) {
          return null;
        }
        lo[i] = box[i].dlo();
        hi[i] = box[i].dhi();
      }
      return new Witness(lo, hi);
    }

    double mid(int i) {
      return lo[i] == hi[i] ? lo[i] : lo[i] / 2 + hi[i] / 2;
    }

    @Override
    public String toString() {
      StringBuilder b = new StringBuilder("[");
      for (int i = 0; i < lo.length; i++) {
        b.append(i == 0 ? "" : ", ").append(lo[i]);
        if (lo[i] != hi[i]) {
          b.append("..").append(hi[i]);
        }
      }
      return b.append(']').toString();
    }
  }

  static Stream<Arguments> cases() {
    return allCases().stream()
        .filter(
            c ->
                FILTER.isEmpty()
                    || Arrays.stream(FILTER.split(",")).anyMatch(part -> c.name().contains(part)))
        .map(c -> Arguments.of(c.name(), c));
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("cases")
  void propagationKeepsEverySolution(String name, Case c) {
    long seed = SEED * 1_000_003L + name.hashCode();
    double precision = FloatDomain.precision();
    FloatDomain.setPrecision(PRECISION);
    try {
      keepsEverySolution(name, c, seed);
    } finally {
      FloatDomain.setPrecision(precision);
    }
  }

  /**
   * The precision of float domains in {@link #propagationKeepsEverySolution}: a coarse one, as a
   * float_search annotation sets it, makes wide intervals singletons.
   */
  private static final double PRECISION =
      Double.parseDouble(
          System.getProperty("floats.fuzz.precision", String.valueOf(FloatDomain.precision())));

  private static void keepsEverySolution(String name, Case c, long seed) {
    assertTimeoutPreemptively(
        Duration.ofMinutes(5),
        () -> {
          Random random = new Random(seed);
          COUNTS.set(new long[4]);
          List<String> failures = new ArrayList<>();
          for (int t = 0; t < TRIALS && failures.size() < 5; t++) {
            long trialSeed = random.nextLong();
            String failure = trial(c, new Random(trialSeed));
            if (failure != null) {
              failures.add("trial seed " + trialSeed + ": " + failure);
            }
          }
          if (STATS) {
            long[] n = COUNTS.get();
            System.out.printf(
                "%-40s trials %d witnesses %d ground %d failed %d%n", name, n[0], n[1], n[2], n[3]);
          }
          if (!failures.isEmpty()) {
            fail(name + "\n  " + String.join("\n  ", failures));
          }
        });
  }

  /**
   * Imposes 2x - 3y - z = 0 with x and y fixed: the constant that x and y fold into is 16 ulps off
   * its real value when rounded, which cut off the real z (and failed with z >= that real value).
   */
  @Test
  void linearFoldsFixedVariablesExactly() {
    Store store = new Store();
    double x = -4.900545980347655;
    double y = -3.369761905148869;
    // 2x - 3y exactly
    double z = 0.30819375475129807;
    FloatVar[] list = {
      new FloatVar(store, "x", x, x), new FloatVar(store, "y", y, y), new FloatVar(store, "z", z, 1)
    };
    store.impose(new LinearFloat(list, new double[] {2, -3, -1}, "==", 0));
    assertTrue(store.consistency());
    assertTrue(list[2].dom().contains(z), list[2].toString());
  }

  /** Trials per case of the optimisation check, which runs a whole search per trial. */
  private static final int OPT_TRIALS = Integer.getInteger("floats.fuzz.opt.trials", 20);

  static Stream<Arguments> floatFunctionalCases() {
    return cases()
        .filter(
            a -> {
              Case c = (Case) a.get()[1];
              for (boolean f : c.isFloat()) {
                if (!f) {
                  return false;
                }
              }
              return c.fix() != null;
            });
  }

  /**
   * Minimises one variable with {@link SplitSelectFloat} and a step, and checks that the optimum
   * found is no worse than any witness by more than the step and the precision: a cost bound or a
   * split that loses solutions would end the search with a worse optimum.
   */
  @ParameterizedTest(name = "{0}")
  @MethodSource("floatFunctionalCases")
  void minimisationIsNoWorseThanAnyWitness(String name, Case c) {
    long seed = SEED * 1_000_033L + name.hashCode();
    double precision = FloatDomain.precision();
    double step = 1e-3;
    FloatDomain.setPrecision(1e-7);
    FloatDomain.setStep(step);
    try {
      assertTimeoutPreemptively(
          Duration.ofMinutes(5),
          () -> {
            Random random = new Random(seed);
            List<String> failures = new ArrayList<>();
            for (int t = 0; t < OPT_TRIALS && failures.size() < 5; t++) {
              long trialSeed = random.nextLong();
              String failure = minimise(c, new Random(trialSeed), step);
              if (failure != null) {
                failures.add("trial seed " + trialSeed + ": " + failure);
              }
            }
            if (!failures.isEmpty()) {
              fail(name + "\n  " + String.join("\n  ", failures));
            }
          });
    } finally {
      FloatDomain.setPrecision(precision);
      FloatDomain.setStep(0);
    }
  }

  private static String minimise(Case c, Random random, double step) {
    Trial t = new Trial(c, Wrap.PLAIN);
    Witness seedPoint = seedPoint(t, random);
    if (seedPoint == null) {
      return null;
    }
    buildBox(t, seedPoint, random);
    sampleWitnesses(t, seedPoint, random);
    Constraint[] constraints;
    try {
      constraints = wrapped(t);
    } catch (IllegalArgumentException _) {
      return null;
    }
    String where = describe(t, constraints);
    try {
      for (Constraint constraint : constraints) {
        t.store.impose(constraint);
      }
    } catch (FailException _) {
      return checkFailure(t, "impose", where);
    }
    int cost = random.nextInt(t.vars.length);
    FloatVar[] vars = Arrays.copyOf(t.vars, t.vars.length, FloatVar[].class);
    DepthFirstSearch<FloatVar> search = new DepthFirstSearch<>();
    SplitSelectFloat<FloatVar> select = new SplitSelectFloat<>(t.store, vars, null);
    select.leftFirst = random.nextBoolean();
    search.setPrintInfo(false);
    search.getSolutionListener().recordSolutions(false);
    search.setTimeOutMilliseconds(300);
    boolean found;
    try {
      found = search.labeling(t.store, select, vars[cost]);
    } catch (RuntimeException e) {
      return "search threw " + e + "\n    " + where;
    }
    if (search.timeOutOccured) {
      return null;
    }
    double best = found ? search.getCostValueFloat() : Double.POSITIVE_INFINITY;
    for (Witness w : t.witnesses) {
      // the cost of a solution is the middle of a singleton interval, at most the precision wide
      double slack = step + FloatDomain.precision() + ULP_SLACK * Math.ulp(w.hi()[cost]);
      if (agrees(t, w) && best > w.hi()[cost] + slack) {
        return "minimising "
            + vars[cost].id()
            + " ended with "
            + (found ? best : "no solution")
            + ", but "
            + w
            + " holds a solution\n    "
            + where;
      }
    }
    return null;
  }

  // ---------------------------------------------------------------------------------------------
  // one trial

  /** The variables of one trial and the witnesses, with the wrapping applied. */
  private static final class Trial {
    final Case c;
    final Wrap wrap;
    final Store store = new Store();
    // the variables in coordinate order; under REIFIED the last one is the 0/1 variable
    Var[] vars;
    final List<Witness> witnesses = new ArrayList<>();
    // the bounds the decisions of the dive so far allow, per coordinate
    double[] lo;
    double[] hi;
    // whether the last propagation failed
    boolean failed;

    Trial(Case c, Wrap wrap) {
      this.c = c;
      this.wrap = wrap;
    }

    int arity() {
      return c.isFloat().length + (wrap == Wrap.REIFIED ? 1 : 0);
    }

    /** Whether the wrapping holds over a full box (with the 0/1 coordinate under REIFIED). */
    int holds(Iv[] box) {
      int n = c.isFloat().length;
      int h = c.holds().applyAsInt(Arrays.copyOf(box, n));
      return switch (wrap) {
        case PLAIN -> h;
        case NOT -> -h;
        case REIFIED -> {
          Iv b = box[n];
          if (!b.isPoint()) {
            yield 0;
          }
          yield b.lo().signum() == 0 ? -h : h;
        }
      };
    }

    boolean wantTrue(double[] x) {
      int n = c.isFloat().length;
      return wrap == Wrap.PLAIN || wrap == Wrap.REIFIED && x[n] == 1;
    }

    /**
     * The witness of a point: for a functional relation that should hold, the point with the
     * enclosures of its dependent coordinates; otherwise the point itself if the wrapping holds at
     * it exactly. Null if there is none.
     */
    Witness witness(double[] x) {
      int n = c.isFloat().length;
      if (wantTrue(x) && c.fix() != null) {
        double[] fixed = c.fix().apply(Arrays.copyOf(x, n));
        if (fixed == null) {
          return null;
        }
        Iv[] box = points(x);
        Iv[] e = c.enclose().apply(points(fixed));
        System.arraycopy(e, 0, box, 0, n);
        return Witness.of(box);
      }
      return holds(widened(x)) == 1 ? Witness.of(points(x)) : null;
    }

    /**
     * The point with its float coordinates widened by the precision: a predicate witness must hold
     * over all of it, since a float interval narrower than the precision is one value, so that x !=
     * c may be taken for x == c when x lies within the precision of c.
     */
    Iv[] widened(double[] x) {
      Iv[] box = points(x);
      // a relation is decided in doubles at the magnitude of its largest coordinate (x + y = x
      // holds for |y| below the ulp of x), so the slack is at least a few ulps of that magnitude
      double largest = 0;
      for (int i = 0; i < c.isFloat().length; i++) {
        if (c.isFloat()[i]) {
          largest = Math.max(largest, Math.abs(x[i]));
        }
      }
      BigDecimal p =
          new BigDecimal(Math.max(FloatDomain.precision(), ULP_SLACK * Math.ulp(largest)));
      for (int i = 0; i < c.isFloat().length; i++) {
        if (c.isFloat()[i]) {
          box[i] = Iv.of(box[i].lo().subtract(p), box[i].hi().add(p));
        }
      }
      return box;
    }
  }

  private static Iv[] points(double[] x) {
    Iv[] box = new Iv[x.length];
    for (int i = 0; i < x.length; i++) {
      box[i] = Iv.of(x[i]);
    }
    return box;
  }

  private static String trial(Case c, Random random) {
    Wrap wrap = Wrap.PLAIN;
    if (c.primitive()) {
      int w = random.nextInt(4);
      wrap = w == 2 ? Wrap.NOT : w == 3 ? Wrap.REIFIED : Wrap.PLAIN;
    }
    Trial t = new Trial(c, wrap);
    Witness seedPoint = seedPoint(t, random);
    if (seedPoint == null) {
      return null;
    }
    buildBox(t, seedPoint, random);
    sampleWitnesses(t, seedPoint, random);

    Constraint[] constraints;
    try {
      constraints = wrapped(t);
    } catch (IllegalArgumentException _) {
      // a constructor may reject a box, for example a constant out of range
      return null;
    }
    String where = describe(t, constraints);
    try {
      for (Constraint constraint : constraints) {
        t.store.impose(constraint);
      }
    } catch (FailException _) {
      return checkFailure(t, "impose", where);
    } catch (RuntimeException e) {
      return "impose threw " + e + "\n    " + where;
    }
    return dive(t, random, where);
  }

  private static Constraint[] wrapped(Trial t) {
    int n = t.c.isFloat().length;
    Constraint[] inner = t.c.build().apply(Arrays.copyOf(t.vars, n));
    return switch (t.wrap) {
      case PLAIN -> inner;
      case NOT -> new Constraint[] {new Not((PrimitiveConstraint) inner[0])};
      case REIFIED ->
          new Constraint[] {new Reified((PrimitiveConstraint) inner[0], (IntVar) t.vars[n])};
    };
  }

  /** A witness of the wrapping, drawn from the ranges of the case. */
  private static Witness seedPoint(Trial t, Random random) {
    Case c = t.c;
    int n = c.isFloat().length;
    for (int attempt = 0; attempt < 200; attempt++) {
      double[] x = new double[t.arity()];
      for (int i = 0; i < n; i++) {
        x[i] = draw(c.isFloat()[i], c.lo()[i], c.hi()[i], random);
      }
      if (t.wrap == Wrap.REIFIED) {
        x[n] = random.nextInt(2);
      }
      Witness w = t.witness(x);
      if (w != null) {
        return w;
      }
    }
    return null;
  }

  private static double draw(boolean isFloat, double lo, double hi, Random random) {
    if (!isFloat) {
      return (int) lo + random.nextInt((int) hi - (int) lo + 1);
    }
    double x = lo + (hi - lo) * random.nextDouble();
    // now and then a short decimal, so that ends of intervals meet exactly
    return random.nextInt(4) == 0 ? Math.round(x * 4) / 4.0 : x;
  }

  /** Creates the variables over random intervals around the seed witness. */
  private static void buildBox(Trial t, Witness seed, Random random) {
    int n = t.arity();
    t.vars = new Var[n];
    t.lo = new double[n];
    t.hi = new double[n];
    for (int i = 0; i < n; i++) {
      boolean isFloat = i < t.c.isFloat().length && t.c.isFloat()[i];
      double v = seed.mid(i);
      if (!isFloat) {
        int value = (int) Math.round(v);
        int below = random.nextInt(4) == 0 ? 0 : random.nextInt(4);
        int above = random.nextInt(4) == 0 ? 0 : random.nextInt(4);
        if (i == t.c.isFloat().length) {
          // the 0/1 variable of Reified
          below = value - random.nextInt(value + 1);
          above = random.nextInt(2 - value);
        }
        IntVar x = new IntVar(t.store, "x" + i, value - below, value + above);
        t.vars[i] = x;
        t.lo[i] = x.min();
        t.hi[i] = x.max();
        continue;
      }
      double lo = seed.lo()[i] - width(v, random);
      double hi = seed.hi()[i] + width(v, random);
      FloatIntervalDomain d = new FloatIntervalDomain();
      double holeLo = lo + (hi - lo) * random.nextDouble();
      double holeHi = holeLo + (hi - holeLo) * random.nextDouble() * 0.5;
      if (random.nextInt(6) == 0
          && holeLo > lo
          && holeHi < hi
          && (seed.hi()[i] < holeLo || seed.lo()[i] > holeHi)) {
        d.unionAdapt(lo, holeLo);
        d.unionAdapt(holeHi, hi);
      } else {
        d.unionAdapt(lo, hi);
      }
      FloatVar f = new FloatVar(t.store, "f" + i, d);
      t.vars[i] = f;
      t.lo[i] = f.min();
      t.hi[i] = f.max();
    }
  }

  private static double width(double v, Random random) {
    return switch (random.nextInt(6)) {
      case 0 -> 0;
      case 1 -> random.nextDouble() * 1e-6 * (1 + Math.abs(v));
      case 2 -> random.nextDouble() * 0.1;
      case 3 -> random.nextDouble();
      case 4 -> random.nextDouble() * 10;
      default -> random.nextDouble() * 3 * (1 + Math.abs(v));
    };
  }

  /** The seed witness and the witnesses of points sampled in the box. */
  private static void sampleWitnesses(Trial t, Witness seed, Random random) {
    if (inDomains(t, seed)) {
      t.witnesses.add(seed);
    }
    COUNTS.get()[0]++;
    for (int s = 0; s < SAMPLES; s++) {
      Witness w = sampledWitness(t, random);
      if (w != null) {
        t.witnesses.add(w);
      }
    }
  }

  /** The witness of a point sampled in the current domains, if it lies in them, or null. */
  private static Witness sampledWitness(Trial t, Random random) {
    double[] x = new double[t.arity()];
    for (int i = 0; i < x.length; i++) {
      x[i] = sampleIn(t.vars[i], random);
    }
    Witness w = t.witness(x);
    return w != null && inDomains(t, w) ? w : null;
  }

  private static double sampleIn(Var v, Random random) {
    if (v instanceof IntVar x) {
      int k = random.nextInt(x.getSize());
      return x.dom().getElementAt(k);
    }
    FloatDomain d = ((FloatVar) v).dom();
    int k = random.nextInt(d.noIntervals());
    double lo = d.leftElement(k);
    double hi = d.rightElement(k);
    return switch (random.nextInt(5)) {
      case 0 -> lo;
      case 1 -> hi;
      default -> Math.min(hi, lo + (hi - lo) * random.nextDouble());
    };
  }

  /** Whether each coordinate box of w lies in the domain of its variable, exactly. */
  private static boolean inDomains(Trial t, Witness w) {
    for (int i = 0; i < w.lo().length; i++) {
      Var v = t.vars[i];
      double lo = w.lo()[i];
      double hi = w.hi()[i];
      if (v instanceof IntVar iv) {
        if (lo != hi || lo != Math.rint(lo) || !iv.domain.contains((int) lo)) {
          return false;
        }
        continue;
      }
      FloatDomain d = ((FloatVar) v).dom();
      boolean inside = false;
      for (int k = 0; k < d.noIntervals() && !inside; k++) {
        inside = d.leftElement(k) <= lo && hi <= d.rightElement(k);
      }
      if (!inside) {
        return false;
      }
    }
    return true;
  }

  // ---------------------------------------------------------------------------------------------
  // the dive

  private record Snapshot(String[] domains) {}

  private static Snapshot snapshot(Trial t) {
    String[] s = new String[t.vars.length];
    for (int i = 0; i < s.length; i++) {
      if (t.vars[i] instanceof FloatVar f) {
        FloatDomain d = f.dom();
        StringBuilder b = new StringBuilder();
        for (int k = 0; k < d.noIntervals(); k++) {
          b.append(d.leftElement(k)).append("..").append(d.rightElement(k)).append(' ');
        }
        s[i] = b.toString();
      } else {
        s[i] = ((IntVar) t.vars[i]).dom().toString();
      }
    }
    return new Snapshot(s);
  }

  private static String dive(Trial t, Random random, String where) {
    Store store = t.store;
    String result = propagate(t, "root", where);
    if (result != null || t.failed) {
      return result;
    }
    Deque<Snapshot> stack = new ArrayDeque<>();
    StringBuilder path = new StringBuilder();
    for (int decisions = 0; decisions < MAX_DECISIONS; decisions++) {
      int i = pickVariable(t, random);
      if (i < 0) {
        COUNTS.get()[1] += t.witnesses.size();
        COUNTS.get()[2]++;
        return checkGround(t, where + "\n    path:" + path);
      }
      Snapshot before = snapshot(t);
      double[] keptLo = t.lo.clone();
      double[] keptHi = t.hi.clone();
      double[] decision = decision(t.vars[i], random);
      boolean failed = false;
      for (int side = 0; side < 2; side++) {
        double dlo = side == 0 ? decision[0] : decision[2];
        double dhi = side == 0 ? decision[1] : decision[3];
        String step = " " + t.vars[i].id() + " in " + dlo + ".." + dhi;
        store.setLevel(store.level + 1);
        t.lo[i] = Math.max(t.lo[i], dlo);
        t.hi[i] = Math.min(t.hi[i], dhi);
        result = decide(t, i, dlo, dhi, where + "\n    path:" + path + step);
        if (result != null) {
          return result;
        }
        if (!t.failed) {
          path.append(step);
          stack.push(before);
          failed = false;
          break;
        }
        failed = true;
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
        t.failed = false;
        System.arraycopy(keptLo, 0, t.lo, 0, keptLo.length);
        System.arraycopy(keptHi, 0, t.hi, 0, keptHi.length);
        Snapshot after = snapshot(t);
        if (!Arrays.equals(before.domains(), after.domains())) {
          return "removeLevel did not restore the domains: "
              + Arrays.toString(before.domains())
              + " became "
              + Arrays.toString(after.domains())
              + "\n    "
              + where
              + "\n    path:"
              + path
              + step;
        }
      }
      if (failed) {
        COUNTS.get()[1] += t.witnesses.size();
        COUNTS.get()[3]++;
        // both branches failed: the node has no solution, which denser sampling checks
        Witness missed = resample(t, random);
        if (missed != null) {
          return "both branches failed on the solution "
              + missed
              + "\n    "
              + where
              + "\n    path:"
              + path;
        }
        break;
      }
    }
    // unwind: every level gives back the domains it started from
    while (!stack.isEmpty()) {
      Snapshot before = stack.pop();
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
      Snapshot after = snapshot(t);
      if (!Arrays.equals(before.domains(), after.domains())) {
        return "removeLevel did not restore the domains: "
            + Arrays.toString(before.domains())
            + " became "
            + Arrays.toString(after.domains())
            + "\n    "
            + where;
      }
    }
    return null;
  }

  /** A witness in the current domains that the decisions allow, sampled densely, or null. */
  private static Witness resample(Trial t, Random random) {
    for (int s = 0; s < 50 * SAMPLES; s++) {
      Witness w = sampledWitness(t, random);
      if (w != null && agrees(t, w)) {
        return w;
      }
    }
    return null;
  }

  /** A variable that is not singleton, or -1 when all are. */
  private static int pickVariable(Trial t, Random random) {
    List<Integer> open = new ArrayList<>();
    for (int i = 0; i < t.vars.length; i++) {
      if (!t.vars[i].singleton()) {
        open.add(i);
      }
    }
    return open.isEmpty() ? -1 : open.get(random.nextInt(open.size()));
  }

  /**
   * A split of the variable's interval: {lo1, hi1, lo2, hi2}, the first branch and the second
   * branch tried if the first fails.
   */
  private static double[] decision(Var v, Random random) {
    if (v instanceof IntVar x) {
      int value = x.dom().getElementAt(random.nextInt(x.getSize()));
      if (random.nextBoolean() && value < x.max()) {
        return new double[] {x.min(), value, value + 1, x.max()};
      }
      return new double[] {value, value, x.min(), x.max()};
    }
    FloatVar f = (FloatVar) v;
    double lo = f.min();
    double hi = f.max();
    double mid = random.nextInt(4) == 0 ? lo + (hi - lo) * random.nextDouble() : (lo + hi) / 2;
    if (!(mid > lo && mid < hi)) {
      mid = (lo + hi) / 2;
    }
    return random.nextBoolean() ? new double[] {lo, mid, mid, hi} : new double[] {mid, hi, lo, mid};
  }

  private static String decide(Trial t, int i, double lo, double hi, String where) {
    Store store = t.store;
    try {
      if (t.vars[i] instanceof IntVar x) {
        x.domain.in(store.level, x, (int) lo, (int) hi);
      } else {
        FloatVar f = (FloatVar) t.vars[i];
        f.domain.in(store.level, f, lo, hi);
      }
    } catch (FailException _) {
      t.failed = true;
      return checkFailure(t, "decision", where);
    }
    return propagate(t, "decision", where);
  }

  private static String propagate(Trial t, String what, String where) {
    Store store = t.store;
    boolean consistent;
    try {
      consistent = store.consistency();
    } catch (FailException _) {
      consistent = false;
    } catch (RuntimeException | StackOverflowError e) {
      return what + " consistency threw " + e + "\n    " + where;
    }
    if (!consistent) {
      t.failed = true;
      return checkFailure(t, what, where);
    }
    t.failed = false;
    for (Witness w : t.witnesses) {
      if (agrees(t, w)) {
        int lost = lostCoordinate(t, w);
        if (lost >= 0) {
          return what + " removed the solution " + w + ": " + t.vars[lost] + "\n    " + where;
        }
      }
    }
    return null;
  }

  /** A failure is right only if no witness lies inside the decisions. */
  private static String checkFailure(Trial t, String what, String where) {
    for (Witness w : t.witnesses) {
      if (agrees(t, w)) {
        return what + " failed with the solution " + w + "\n    " + where;
      }
    }
    return null;
  }

  /** Whether the box of a witness lies inside the bounds the decisions allow. */
  private static boolean agrees(Trial t, Witness w) {
    for (int i = 0; i < w.lo().length; i++) {
      if (w.lo()[i] < t.lo[i] || w.hi()[i] > t.hi[i]) {
        return false;
      }
    }
    return true;
  }

  /**
   * The first coordinate whose box no longer meets the domain of its variable, or -1. Float domains
   * count as meeting a box that they come within the precision of.
   */
  private static int lostCoordinate(Trial t, Witness w) {
    for (int i = 0; i < w.lo().length; i++) {
      Var v = t.vars[i];
      double lo = w.lo()[i];
      double hi = w.hi()[i];
      if (v instanceof IntVar x) {
        boolean kept = false;
        for (int k = (int) Math.ceil(lo); k <= hi && !kept; k++) {
          kept = x.domain.contains(k);
        }
        if (!kept) {
          return i;
        }
        continue;
      }
      FloatDomain d = ((FloatVar) v).dom();
      double slack = FloatDomain.precision();
      boolean kept = false;
      for (int k = 0; k < d.noIntervals() && !kept; k++) {
        kept = lo <= d.rightElement(k) + slack && d.leftElement(k) - slack <= hi;
      }
      if (!kept) {
        return i;
      }
    }
    return -1;
  }

  /**
   * A node where every variable is singleton must be a box that may hold a solution. A float
   * interval narrower than the precision is one value, and propagation stops narrowing at the
   * precision, so the box counts as holding a solution that lies within the precision of it.
   */
  /**
   * The slack of a relation over float variables: the precision, or a few ulps of the largest
   * magnitude among the float variables, at which the relation is decided in doubles.
   */
  private static double slack(Trial t) {
    double largest = 0;
    for (Var v : t.vars) {
      if (v instanceof FloatVar f) {
        largest = Math.max(largest, Math.max(Math.abs(f.min()), Math.abs(f.max())));
      }
    }
    return Math.max(FloatDomain.precision(), ULP_SLACK * Math.ulp(largest));
  }

  /** Ulps of the largest magnitude of a relation that its decision in doubles may be off by. */
  private static final int ULP_SLACK = 16;

  private static String checkGround(Trial t, String where) {
    Iv[] box = new Iv[t.vars.length];
    for (int i = 0; i < box.length; i++) {
      if (t.vars[i] instanceof IntVar v) {
        box[i] = Iv.of(v.value());
      } else {
        FloatVar f = (FloatVar) t.vars[i];
        BigDecimal p = new BigDecimal(slack(t));
        box[i] = Iv.of(new BigDecimal(f.min()).subtract(p), new BigDecimal(f.max()).add(p));
      }
    }
    if (t.holds(box) < 0) {
      return "accepted " + Arrays.toString(box) + ", which holds no solution\n    " + where;
    }
    return null;
  }

  private static String describe(Trial t, Constraint[] cs) {
    StringBuilder b = new StringBuilder();
    b.append(t.wrap);
    for (Constraint c : cs) {
      b.append(' ').append(c);
    }
    b.append(" over");
    for (Var v : t.vars) {
      b.append(' ').append(v);
    }
    return b.toString();
  }

  // ---------------------------------------------------------------------------------------------
  // exact interval arithmetic

  private static final MathContext DOWN = new MathContext(60, RoundingMode.FLOOR);
  private static final MathContext UP = new MathContext(60, RoundingMode.CEILING);

  /** The largest double at most r. */
  static double down(BigDecimal r) {
    double d = r.doubleValue();
    if (Double.isFinite(d) && new BigDecimal(d).compareTo(r) > 0) {
      d = Math.nextDown(d);
    }
    return d;
  }

  /** The smallest double at least r. */
  static double up(BigDecimal r) {
    double d = r.doubleValue();
    if (Double.isFinite(d) && new BigDecimal(d).compareTo(r) < 0) {
      d = Math.nextUp(d);
    }
    return d;
  }

  /** The double k ulps away from v, down if k is negative. */
  static double widen(double v, int k) {
    for (int i = 0; i < Math.abs(k); i++) {
      v = k < 0 ? Math.nextDown(v) : Math.nextUp(v);
    }
    return v;
  }

  /**
   * A closed interval of reals with exact ends: lo null is minus infinity, hi null plus infinity.
   */
  record Iv(BigDecimal lo, BigDecimal hi) {

    static final Iv ALL = new Iv(null, null);

    static Iv of(double v) {
      return of(v, v);
    }

    static Iv of(double lo, double hi) {
      if (Double.isNaN(lo) || Double.isNaN(hi)) {
        return ALL;
      }
      return new Iv(
          Double.isInfinite(lo) ? null : new BigDecimal(lo),
          Double.isInfinite(hi) ? null : new BigDecimal(hi));
    }

    static Iv of(BigDecimal lo, BigDecimal hi) {
      return new Iv(lo, hi);
    }

    boolean bounded() {
      return lo != null && hi != null;
    }

    boolean isPoint() {
      return bounded() && lo.compareTo(hi) == 0;
    }

    double dlo() {
      return lo == null ? Double.NEGATIVE_INFINITY : down(lo);
    }

    double dhi() {
      return hi == null ? Double.POSITIVE_INFINITY : up(hi);
    }

    boolean containsZero() {
      return (lo == null || lo.signum() <= 0) && (hi == null || hi.signum() >= 0);
    }

    Iv hull(Iv o) {
      if (o == null) {
        return this;
      }
      return new Iv(
          lo == null || o.lo == null ? null : lo.min(o.lo),
          hi == null || o.hi == null ? null : hi.max(o.hi));
    }

    @Override
    public String toString() {
      return isPoint() ? String.valueOf(dlo()) : dlo() + ".." + dhi();
    }
  }

  static Iv add(Iv a, Iv b) {
    if (!a.bounded() || !b.bounded()) {
      return Iv.ALL;
    }
    return Iv.of(a.lo().add(b.lo()), a.hi().add(b.hi()));
  }

  static Iv neg(Iv a) {
    return new Iv(a.hi() == null ? null : a.hi().negate(), a.lo() == null ? null : a.lo().negate());
  }

  static Iv sub(Iv a, Iv b) {
    return add(a, neg(b));
  }

  static Iv mul(Iv a, Iv b) {
    if (!a.bounded() || !b.bounded()) {
      return Iv.ALL;
    }
    BigDecimal[] p = {
      a.lo().multiply(b.lo()), a.lo().multiply(b.hi()),
      a.hi().multiply(b.lo()), a.hi().multiply(b.hi())
    };
    BigDecimal lo = p[0];
    BigDecimal hi = p[0];
    for (BigDecimal q : p) {
      lo = lo.min(q);
      hi = hi.max(q);
    }
    return Iv.of(lo, hi);
  }

  static Iv div(Iv a, Iv b) {
    if (!a.bounded() || !b.bounded() || b.containsZero()) {
      return Iv.ALL;
    }
    BigDecimal[] x = {a.lo(), a.hi()};
    BigDecimal[] y = {b.lo(), b.hi()};
    BigDecimal lo = null;
    BigDecimal hi = null;
    for (BigDecimal p : x) {
      for (BigDecimal q : y) {
        BigDecimal l = p.divide(q, DOWN);
        BigDecimal h = p.divide(q, UP);
        lo = lo == null ? l : lo.min(l);
        hi = hi == null ? h : hi.max(h);
      }
    }
    return Iv.of(lo, hi);
  }

  static Iv pow(Iv a, int k) {
    if (!a.bounded()) {
      return Iv.ALL;
    }
    BigDecimal l = a.lo().pow(k);
    BigDecimal h = a.hi().pow(k);
    if (k % 2 == 1) {
      return Iv.of(l, h);
    }
    BigDecimal top = l.max(h);
    return a.containsZero() ? Iv.of(BigDecimal.ZERO, top) : Iv.of(l.min(h), top);
  }

  static Iv abs(Iv a) {
    if (!a.bounded()) {
      return Iv.ALL;
    }
    if (a.lo().signum() >= 0) {
      return a;
    }
    if (a.hi().signum() <= 0) {
      return neg(a);
    }
    return Iv.of(BigDecimal.ZERO, a.lo().negate().max(a.hi()));
  }

  static Iv max(Iv[] xs) {
    BigDecimal lo = null;
    BigDecimal hi = null;
    for (Iv x : xs) {
      if (!x.bounded()) {
        return Iv.ALL;
      }
      lo = lo == null ? x.lo() : lo.max(x.lo());
      hi = hi == null ? x.hi() : hi.max(x.hi());
    }
    return Iv.of(lo, hi);
  }

  static Iv min(Iv[] xs) {
    return neg(max(Arrays.stream(xs).map(FloatPropagationFuzzTest::neg).toArray(Iv[]::new)));
  }

  static Iv linear(double[] w, Iv[] x) {
    Iv s = Iv.of(0);
    for (int i = 0; i < w.length; i++) {
      s = add(s, mul(Iv.of(w[i]), x[i]));
    }
    return s;
  }

  /**
   * A monotone function computed with {@link Math} within ulps of the real value, over an interval:
   * its values at the ends, widened by the error bound.
   */
  static Iv mono(Iv a, DoubleUnaryOperator f, int ulps, boolean increasing) {
    if (!a.bounded()) {
      return Iv.ALL;
    }
    double l = f.applyAsDouble(increasing ? a.dlo() : a.dhi());
    double h = f.applyAsDouble(increasing ? a.dhi() : a.dlo());
    if (!Double.isFinite(l) || !Double.isFinite(h)) {
      return Iv.ALL;
    }
    return Iv.of(widen(l, -ulps), widen(h, ulps));
  }

  /**
   * A smooth function that need not be monotone, over an interval at most 1e-9 wide: its values at
   * the ends, widened by the error bound. Inside so short an interval the function departs from the
   * hull of the ends by its second derivative times the square of the width, below an ulp of the
   * values here (the extrema of sin, cos and cosh are near 1).
   */
  static Iv smooth(Iv a, DoubleUnaryOperator f, int ulps) {
    if (!a.bounded() || a.dhi() - a.dlo() > 1e-9) {
      return Iv.ALL;
    }
    double l = f.applyAsDouble(a.dlo());
    double h = f.applyAsDouble(a.dhi());
    if (!Double.isFinite(l) || !Double.isFinite(h)) {
      return Iv.ALL;
    }
    return Iv.of(widen(Math.min(l, h), -ulps), widen(Math.max(l, h), ulps));
  }

  /**
   * The inverse of an increasing function computed with {@link Math} within ulps, over an interval:
   * doubles below and above the real inverse at each end, found by stepping out from a guess until
   * the forward function, widened by its error bound, brackets the end.
   */
  static Iv inverse(Iv a, DoubleUnaryOperator f, int ulps, DoubleUnaryOperator guess) {
    if (!a.bounded()) {
      return Iv.ALL;
    }
    double lo = bracket(a.dlo(), f, ulps, guess, -1);
    double hi = bracket(a.dhi(), f, ulps, guess, 1);
    return Iv.of(lo, hi);
  }

  private static double bracket(
      double x, DoubleUnaryOperator f, int ulps, DoubleUnaryOperator guess, int side) {
    double y = guess.applyAsDouble(x);
    if (!Double.isFinite(y)) {
      return side * Double.POSITIVE_INFINITY;
    }
    double step = Math.ulp(y);
    for (int k = 0; k < 2000; k++) {
      double v = f.applyAsDouble(y);
      // f(y) < x (side -1) or f(y) > x (side 1) for sure, so y is beyond the real inverse
      if (side < 0 ? widen(v, ulps) < x : widen(v, -ulps) > x) {
        return y;
      }
      y += side * step;
      step *= 2;
    }
    return side * Double.POSITIVE_INFINITY;
  }

  /** A monotone step function of doubles over an interval: its values at the ends. */
  static Iv steps(Iv a, DoubleUnaryOperator g) {
    if (!a.bounded()) {
      return Iv.ALL;
    }
    return Iv.of(g.applyAsDouble(a.dlo()), g.applyAsDouble(a.dhi()));
  }

  private static boolean disjoint(Iv a, Iv b) {
    return a.hi() != null && b.lo() != null && a.hi().compareTo(b.lo()) < 0
        || b.hi() != null && a.lo() != null && b.hi().compareTo(a.lo()) < 0;
  }

  /** a = b over boxes: 1 at every point, -1 at none, 0 otherwise. */
  static int eq(Iv a, Iv b) {
    if (a.isPoint() && b.isPoint() && a.lo().compareTo(b.lo()) == 0) {
      return 1;
    }
    return disjoint(a, b) ? -1 : 0;
  }

  static int ne(Iv a, Iv b) {
    return -eq(a, b);
  }

  /** a <= b over boxes. */
  static int le(Iv a, Iv b) {
    if (a.hi() != null && b.lo() != null && a.hi().compareTo(b.lo()) <= 0) {
      return 1;
    }
    return a.lo() != null && b.hi() != null && a.lo().compareTo(b.hi()) > 0 ? -1 : 0;
  }

  /** a < b over boxes. */
  static int lt(Iv a, Iv b) {
    if (a.hi() != null && b.lo() != null && a.hi().compareTo(b.lo()) < 0) {
      return 1;
    }
    return a.lo() != null && b.hi() != null && a.lo().compareTo(b.hi()) >= 0 ? -1 : 0;
  }

  /** Both hold: 1 if both surely do, -1 if one surely does not. */
  static int and(int a, int b) {
    return a < 0 || b < 0 ? -1 : a > 0 && b > 0 ? 1 : 0;
  }

  // ---------------------------------------------------------------------------------------------
  // the cases

  private static final boolean F = true;
  private static final boolean I = false;

  private static boolean[] kinds(boolean... k) {
    return k;
  }

  private static double[] r(double... v) {
    return v;
  }

  /**
   * A functional case: coordinate {@code dep} is f of the others, which {@code real} encloses over
   * a box (null when the box holds no argument that f is defined on).
   */
  private static Case function(
      String name,
      boolean[] kinds,
      double[] lo,
      double[] hi,
      int dep,
      ToDoubleFunction<double[]> f,
      Function<Iv[], Iv> real,
      Function<Var[], Constraint> build,
      boolean primitive) {
    return new Case(
        name,
        kinds,
        lo,
        hi,
        x -> {
          double v = f.applyAsDouble(x);
          if (!Double.isFinite(v) || !kinds[dep] && Math.abs(v) > 1e6) {
            return null;
          }
          double[] y = x.clone();
          y[dep] = v;
          return y;
        },
        box -> {
          Iv[] y = box.clone();
          y[dep] = real.apply(box);
          return y;
        },
        box -> {
          Iv e = real.apply(box);
          if (e == null) {
            return -1;
          }
          for (int i = 0; i < box.length; i++) {
            if (i != dep && !box[i].isPoint()) {
              return eq(e, box[dep]) < 0 ? -1 : 0;
            }
          }
          return eq(e, box[dep]);
        },
        v -> new Constraint[] {build.apply(v)},
        primitive,
        dep);
  }

  private static Case predicate(
      String name,
      boolean[] kinds,
      double[] lo,
      double[] hi,
      ToIntFunction<Iv[]> holds,
      Function<Var[], Constraint> build,
      boolean primitive) {
    return new Case(
        name,
        kinds,
        lo,
        hi,
        null,
        null,
        holds,
        v -> new Constraint[] {build.apply(v)},
        primitive,
        -1);
  }

  private static FloatVar fv(Var v) {
    return (FloatVar) v;
  }

  private static IntVar iv(Var v) {
    return (IntVar) v;
  }

  /** Round half away from zero, as {@link RoundPeqX} defines it. */
  private static double roundAway(double p) {
    return Math.signum(p) * Math.floor(Math.abs(p) + 0.5);
  }

  /**
   * Two functional cases that share a variable: coordinate {@code into} of b is the variable of
   * coordinate {@code from} of a. If {@code from} is a's dependent coordinate the two form a chain
   * (b of a), otherwise they constrain a common input.
   */
  private static Case compose(Case a, int from, Case b, int into) {
    int na = a.isFloat().length;
    int nb = b.isFloat().length;
    int n = na + nb - 1;
    // where each coordinate of b is in the composed point
    int[] map = new int[nb];
    boolean[] kinds = Arrays.copyOf(a.isFloat(), n);
    double[] lo = Arrays.copyOf(a.lo(), n);
    double[] hi = Arrays.copyOf(a.hi(), n);
    for (int j = 0, k = na; j < nb; j++) {
      if (j == into) {
        map[j] = from;
      } else {
        map[j] = k;
        kinds[k] = b.isFloat()[j];
        lo[k] = b.lo()[j];
        hi[k] = b.hi()[j];
        k++;
      }
    }
    return new Case(
        a.name() + " & " + b.name(),
        kinds,
        lo,
        hi,
        x -> {
          double[] ya = a.fix().apply(Arrays.copyOf(x, na));
          if (ya == null) {
            return null;
          }
          double[] z = x.clone();
          System.arraycopy(ya, 0, z, 0, na);
          double[] yb = b.fix().apply(part(z, map));
          if (yb == null) {
            return null;
          }
          for (int j = 0; j < nb; j++) {
            z[map[j]] = yb[j];
          }
          return z;
        },
        box -> {
          Iv[] z = box.clone();
          System.arraycopy(a.enclose().apply(Arrays.copyOf(box, na)), 0, z, 0, na);
          Iv[] yb = b.enclose().apply(part(z, map));
          for (int j = 0; j < nb; j++) {
            z[map[j]] = yb[j];
          }
          return z;
        },
        box ->
            and(a.holds().applyAsInt(Arrays.copyOf(box, na)), b.holds().applyAsInt(part(box, map))),
        v -> {
          Var[] vb = part(v, map);
          Constraint[] ca = a.build().apply(Arrays.copyOf(v, na));
          Constraint[] cb = b.build().apply(vb);
          Constraint[] all = Arrays.copyOf(ca, ca.length + cb.length);
          System.arraycopy(cb, 0, all, ca.length, cb.length);
          return all;
        },
        false,
        -1);
  }

  private static double[] part(double[] x, int[] map) {
    double[] y = new double[map.length];
    for (int j = 0; j < map.length; j++) {
      y[j] = x[map[j]];
    }
    return y;
  }

  private static <T> T[] part(T[] x, int[] map) {
    T[] y = Arrays.copyOf(x, map.length);
    for (int j = 0; j < map.length; j++) {
      y[j] = x[map[j]];
    }
    return y;
  }

  /**
   * Pairs of functional float cases chosen at random (fixed seed): chains, where the result of one
   * is an argument of the other, and pairs over a common argument.
   */
  private static List<Case> compositions(List<Case> singles) {
    List<Case> functional = new ArrayList<>();
    for (Case c : singles) {
      if (c.dep() >= 0 && c.fix() != null) {
        functional.add(c);
      }
    }
    Random random = new Random(20261105L);
    List<Case> pairs = new ArrayList<>();
    while (pairs.size() < 40) {
      Case a = functional.get(random.nextInt(functional.size()));
      Case b = functional.get(random.nextInt(functional.size()));
      boolean chain = random.nextBoolean();
      int from = chain ? a.dep() : random.nextInt(a.isFloat().length);
      if (!chain && from == a.dep()) {
        continue;
      }
      int into = random.nextInt(b.isFloat().length);
      if (into == b.dep() || a.isFloat()[from] != b.isFloat()[into]) {
        continue;
      }
      pairs.add(compose(a, from, b, into));
    }
    return pairs;
  }

  static List<Case> allCases() {
    List<Case> cases = singleCases();
    cases.addAll(compositions(cases));
    return cases;
  }

  /** Error bound of {@link Math#sinh}, {@link Math#cosh} and {@link Math#tanh}, rounded up. */
  private static final int HYPERBOLIC_ULPS = 3;

  /** Error bound of the other {@link Math} functions used here, one ulp, with one to spare. */
  private static final int ULPS = 2;

  static List<Case> singleCases() {
    List<Case> cases = new ArrayList<>();
    double[] a3 = r(-10, -10, -10);
    double[] b3 = r(10, 10, 10);
    double[] a2 = r(-10, -10);
    double[] b2 = r(10, 10);

    cases.add(
        function(
            "PplusQeqR",
            kinds(F, F, F),
            a3,
            b3,
            2,
            x -> x[0] + x[1],
            x -> add(x[0], x[1]),
            v -> new PplusQeqR(fv(v[0]), fv(v[1]), fv(v[2])),
            true));
    cases.add(
        function(
            "PminusQeqR",
            kinds(F, F, F),
            a3,
            b3,
            2,
            x -> x[0] - x[1],
            x -> sub(x[0], x[1]),
            v -> new PminusQeqR(fv(v[0]), fv(v[1]), fv(v[2])),
            true));
    cases.add(
        function(
            "PmulQeqR",
            kinds(F, F, F),
            a3,
            b3,
            2,
            x -> x[0] * x[1],
            x -> mul(x[0], x[1]),
            v -> new PmulQeqR(fv(v[0]), fv(v[1]), fv(v[2])),
            false));
    cases.add(
        function(
            "PdivQeqR",
            kinds(F, F, F),
            a3,
            b3,
            2,
            x -> x[1] == 0 ? Double.NaN : x[0] / x[1],
            x -> div(x[0], x[1]),
            v -> new PdivQeqR(fv(v[0]), fv(v[1]), fv(v[2])),
            false));
    for (double c : new double[] {-2.5, -1, 0.5, 3}) {
      Iv k = Iv.of(c);
      cases.add(
          function(
              "PplusCeqR " + c,
              kinds(F, F),
              a2,
              b2,
              1,
              x -> x[0] + c,
              x -> add(x[0], k),
              v -> new PplusCeqR(fv(v[0]), c, fv(v[1])),
              true));
      cases.add(
          function(
              "PminusCeqR " + c,
              kinds(F, F),
              a2,
              b2,
              1,
              x -> x[0] - c,
              x -> sub(x[0], k),
              v -> new PminusCeqR(fv(v[0]), c, fv(v[1])),
              true));
      cases.add(
          function(
              "PmulCeqR " + c,
              kinds(F, F),
              a2,
              b2,
              1,
              x -> x[0] * c,
              x -> mul(x[0], k),
              v -> new PmulCeqR(fv(v[0]), c, fv(v[1])),
              false));
      cases.add(
          function(
              "PdivCeqR " + c,
              kinds(F, F),
              a2,
              b2,
              1,
              x -> x[0] / c,
              x -> div(x[0], k),
              v -> new PdivCeqR(fv(v[0]), c, fv(v[1])),
              false));
    }
    cases.add(
        function(
            "PmulQeqR x*x",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> x[0] * x[0],
            x -> pow(x[0], 2),
            v -> new PmulQeqR(fv(v[0]), fv(v[0]), fv(v[1])),
            false));
    cases.add(
        function(
            "PplusQeqR x+x",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> x[0] + x[0],
            x -> mul(x[0], Iv.of(2)),
            v -> new PplusQeqR(fv(v[0]), fv(v[0]), fv(v[1])),
            true));
    cases.add(
        function(
            "PdivQeqR x/x",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> x[0] == 0 ? Double.NaN : 1,
            x -> x[0].containsZero() ? Iv.ALL : Iv.of(1),
            v -> new PdivQeqR(fv(v[0]), fv(v[0]), fv(v[1])),
            false));

    cases.add(
        function(
            "AbsPeqR",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> Math.abs(x[0]),
            x -> abs(x[0]),
            v -> new AbsPeqR(fv(v[0]), fv(v[1])),
            false));
    cases.add(
        function(
            "SqrtPeqR",
            kinds(F, F),
            r(0, 0),
            r(20, 20),
            1,
            x -> x[0] < 0 ? Double.NaN : Math.sqrt(x[0]),
            x -> real(x[0], 0, Math::sqrt, ULPS),
            v -> new SqrtPeqR(fv(v[0]), fv(v[1])),
            false));
    for (double e : new double[] {2, 3, 4, 5, 0.5, 1.5, 0.25}) {
      boolean integral = e == Math.rint(e);
      cases.add(
          function(
              "PowPeqR " + e,
              kinds(F, F),
              integral ? r(-4, -1100) : r(0, 0),
              integral ? r(4, 1100) : r(20, 100),
              1,
              x -> !integral && x[0] < 0 ? Double.NaN : Math.pow(x[0], e),
              x -> integral ? pow(x[0], (int) e) : real(x[0], 0, p -> Math.pow(p, e), ULPS),
              v -> new PowPeqR(fv(v[0]), e, fv(v[1])),
              false));
    }
    for (HyperbolicPeqR.Function h : HyperbolicPeqR.Function.values()) {
      DoubleUnaryOperator fh =
          switch (h) {
            case SINH -> Math::sinh;
            case COSH -> Math::cosh;
            case TANH -> Math::tanh;
          };
      cases.add(
          function(
              "HyperbolicPeqR " + h,
              kinds(F, F),
              r(-4, -30),
              r(4, 30),
              1,
              x -> fh.applyAsDouble(x[0]),
              x ->
                  h == HyperbolicPeqR.Function.COSH
                      ? smooth(x[0], fh, HYPERBOLIC_ULPS)
                      : mono(x[0], fh, HYPERBOLIC_ULPS, true),
              v -> new HyperbolicPeqR(fv(v[0]), h, fv(v[1])),
              false));
      if (h == HyperbolicPeqR.Function.COSH) {
        continue;
      }
      boolean tanh = h == HyperbolicPeqR.Function.TANH;
      DoubleUnaryOperator guess =
          tanh
              ? p -> 0.5 * Math.log1p(2 * p / (1 - p))
              : p -> Math.copySign(Math.log(Math.abs(p) + Math.sqrt(p * p + 1)), p);
      cases.add(
          function(
              "HyperbolicPeqR inverse " + h,
              kinds(F, F),
              r(tanh ? -1 : -30, -4),
              r(tanh ? 1 : 30, 4),
              1,
              x -> tanh && Math.abs(x[0]) >= 1 ? Double.NaN : guess.applyAsDouble(x[0]),
              x ->
                  tanh && (x[0].dlo() <= -1 || x[0].dhi() >= 1)
                      ? Iv.ALL
                      : inverse(x[0], fh, HYPERBOLIC_ULPS, guess),
              v -> new HyperbolicPeqR(fv(v[1]), h, fv(v[0])),
              false));
    }
    cases.add(
        function(
            "ExpPeqR",
            kinds(F, F),
            r(-8, -8),
            r(5, 5),
            1,
            x -> Math.exp(x[0]),
            x -> mono(x[0], Math::exp, ULPS, true),
            v -> new ExpPeqR(fv(v[0]), fv(v[1])),
            false));
    cases.add(
        function(
            "LnPeqR",
            kinds(F, F),
            r(0, -5),
            r(50, 5),
            1,
            x -> x[0] <= 0 ? Double.NaN : Math.log(x[0]),
            x -> x[0].dlo() <= 0 ? Iv.ALL : mono(x[0], Math::log, ULPS, true),
            v -> new LnPeqR(fv(v[0]), fv(v[1])),
            false));
    cases.add(
        function(
            "SinPeqR",
            kinds(F, F),
            r(-8, -1),
            r(8, 1),
            1,
            x -> Math.sin(x[0]),
            x -> smooth(x[0], Math::sin, ULPS),
            v -> new SinPeqR(fv(v[0]), fv(v[1])),
            false));
    cases.add(
        function(
            "CosPeqR",
            kinds(F, F),
            r(-8, -1),
            r(8, 1),
            1,
            x -> Math.cos(x[0]),
            x -> smooth(x[0], Math::cos, ULPS),
            v -> new CosPeqR(fv(v[0]), fv(v[1])),
            false));
    cases.add(
        function(
            "TanPeqR",
            kinds(F, F),
            r(-4, -10),
            r(4, 10),
            1,
            x -> Math.tan(x[0]),
            x -> smooth(x[0], Math::tan, ULPS),
            v -> new TanPeqR(fv(v[0]), fv(v[1])),
            false));
    cases.add(
        function(
            "AsinPeqR",
            kinds(F, F),
            r(-1, -2),
            r(1, 2),
            1,
            x -> Math.asin(x[0]),
            x -> x[0].dlo() < -1 || x[0].dhi() > 1 ? Iv.ALL : mono(x[0], Math::asin, ULPS, true),
            v -> new AsinPeqR(fv(v[0]), fv(v[1])),
            false));
    cases.add(
        function(
            "AcosPeqR",
            kinds(F, F),
            r(-1, 0),
            r(1, 3),
            1,
            x -> Math.acos(x[0]),
            x -> x[0].dlo() < -1 || x[0].dhi() > 1 ? Iv.ALL : mono(x[0], Math::acos, ULPS, false),
            v -> new AcosPeqR(fv(v[0]), fv(v[1])),
            false));
    cases.add(
        function(
            "AtanPeqR",
            kinds(F, F),
            r(-20, -2),
            r(20, 2),
            1,
            x -> Math.atan(x[0]),
            x -> mono(x[0], Math::atan, ULPS, true),
            v -> new AtanPeqR(fv(v[0]), fv(v[1])),
            false));

    cases.add(
        function(
            "XeqP",
            kinds(I, F),
            r(-6, -6),
            r(6, 6),
            1,
            x -> x[0],
            x -> x[0],
            v -> new XeqP(iv(v[0]), fv(v[1])),
            false));
    cases.add(
        function(
            "RoundPeqX",
            kinds(F, I),
            r(-6, -6),
            r(6, 6),
            1,
            x -> roundAway(x[0]),
            x -> steps(x[0], FloatPropagationFuzzTest::roundAway),
            v -> new RoundPeqX(fv(v[0]), iv(v[1])),
            false));
    cases.add(
        function(
            "FloorPeqX",
            kinds(F, I),
            r(-6, -6),
            r(6, 6),
            1,
            x -> Math.floor(x[0]),
            x -> steps(x[0], Math::floor),
            v -> new FloorPeqX(fv(v[0]), iv(v[1])),
            false));
    cases.add(
        function(
            "CeilPeqX",
            kinds(F, I),
            r(-6, -6),
            r(6, 6),
            1,
            x -> Math.ceil(x[0]),
            x -> steps(x[0], Math::ceil),
            v -> new CeilPeqX(fv(v[0]), iv(v[1])),
            false));

    cases.add(
        predicate(
            "PeqQ",
            kinds(F, F),
            a2,
            b2,
            x -> eq(x[0], x[1]),
            v -> new PeqQ(fv(v[0]), fv(v[1])),
            true));
    cases.add(
        function(
            "PeqQ functional",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> x[0],
            x -> x[0],
            v -> new PeqQ(fv(v[0]), fv(v[1])),
            true));
    cases.add(
        predicate(
            "PneqQ",
            kinds(F, F),
            a2,
            b2,
            x -> ne(x[0], x[1]),
            v -> new PneqQ(fv(v[0]), fv(v[1])),
            true));
    cases.add(
        predicate(
            "PltQ",
            kinds(F, F),
            a2,
            b2,
            x -> lt(x[0], x[1]),
            v -> new PltQ(fv(v[0]), fv(v[1])),
            true));
    cases.add(
        predicate(
            "PlteqQ",
            kinds(F, F),
            a2,
            b2,
            x -> le(x[0], x[1]),
            v -> new PlteqQ(fv(v[0]), fv(v[1])),
            true));
    cases.add(
        predicate(
            "PgtQ",
            kinds(F, F),
            a2,
            b2,
            x -> lt(x[1], x[0]),
            v -> new PgtQ(fv(v[0]), fv(v[1])),
            true));
    cases.add(
        predicate(
            "PgteqQ",
            kinds(F, F),
            a2,
            b2,
            x -> le(x[1], x[0]),
            v -> new PgteqQ(fv(v[0]), fv(v[1])),
            true));
    for (double c : new double[] {-1.5, 0, 2.25}) {
      Iv k = Iv.of(c);
      cases.add(
          function(
              "PeqC " + c,
              kinds(F),
              r(-10),
              r(10),
              0,
              x -> c,
              x -> k,
              v -> new PeqC(fv(v[0]), c),
              true));
      cases.add(
          predicate(
              "PneqC " + c,
              kinds(F),
              r(-10),
              r(10),
              x -> ne(x[0], k),
              v -> new PneqC(fv(v[0]), c),
              true));
      cases.add(
          predicate(
              "PltC " + c,
              kinds(F),
              r(-10),
              r(10),
              x -> lt(x[0], k),
              v -> new PltC(fv(v[0]), c),
              true));
      cases.add(
          predicate(
              "PlteqC " + c,
              kinds(F),
              r(-10),
              r(10),
              x -> le(x[0], k),
              v -> new PlteqC(fv(v[0]), c),
              true));
      cases.add(
          predicate(
              "PgtC " + c,
              kinds(F),
              r(-10),
              r(10),
              x -> lt(k, x[0]),
              v -> new PgtC(fv(v[0]), c),
              true));
      cases.add(
          predicate(
              "PgteqC " + c,
              kinds(F),
              r(-10),
              r(10),
              x -> le(k, x[0]),
              v -> new PgteqC(fv(v[0]), c),
              true));
    }

    double[][] weightSets = {{1, 1}, {2, -3}, {0.5, 1.5, -1}, {-1, -1, -1, 1}, {1e-3, 1}};
    for (double[] w : weightSets) {
      int n = w.length;
      boolean[] k = new boolean[n + 1];
      Arrays.fill(k, F);
      double[] lo = new double[n + 1];
      double[] hi = new double[n + 1];
      Arrays.fill(lo, -10);
      Arrays.fill(hi, 10);
      ToDoubleFunction<double[]> sum =
          x -> {
            double s = 0;
            for (int i = 0; i < n; i++) {
              s += w[i] * x[i];
            }
            return s;
          };
      Function<Iv[], Iv> exactSum = x -> linear(w, x);
      String ws = Arrays.toString(w);
      Function<Var[], FloatVar[]> list = v -> Arrays.copyOf(v, n, FloatVar[].class);
      cases.add(
          function(
              "LinearFloat == var " + ws,
              k,
              lo,
              hi,
              n,
              sum,
              exactSum,
              v -> new LinearFloat(list.apply(v), w, "==", fv(v[n])),
              true));
      Iv oneHalf = Iv.of(1.5);
      cases.add(
          predicate(
              "LinearFloat == const " + ws,
              Arrays.copyOf(k, n),
              Arrays.copyOf(lo, n),
              Arrays.copyOf(hi, n),
              x -> eq(exactSum.apply(x), oneHalf),
              v -> new LinearFloat(Arrays.copyOf(v, n, FloatVar[].class), w, "==", 1.5),
              true));
      Iv twoHalf = Iv.of(2.5);
      for (String rel : new String[] {"<", "<=", ">", ">=", "!="}) {
        cases.add(
            predicate(
                "LinearFloat " + rel + " var " + ws,
                k,
                lo,
                hi,
                x -> compare(exactSum.apply(x), rel, x[n]),
                v -> new LinearFloat(list.apply(v), w, rel, fv(v[n])),
                true));
        cases.add(
            predicate(
                "LinearFloat " + rel + " const " + ws,
                Arrays.copyOf(k, n),
                Arrays.copyOf(lo, n),
                Arrays.copyOf(hi, n),
                x -> compare(exactSum.apply(x), rel, twoHalf),
                v -> new LinearFloat(Arrays.copyOf(v, n, FloatVar[].class), w, rel, 2.5),
                true));
      }
    }
    cases.add(
        function(
            "SumFloat",
            kinds(F, F, F, F),
            r(-10, -10, -10, -10),
            r(10, 10, 10, 10),
            3,
            x -> x[0] + x[1] + x[2],
            x -> add(add(x[0], x[1]), x[2]),
            v -> new SumFloat(new FloatVar[] {fv(v[0]), fv(v[1]), fv(v[2])}, "==", fv(v[3])),
            true));
    cases.add(
        function(
            "LinearFloat x+x-y",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> 2 * x[0],
            x -> mul(x[0], Iv.of(2)),
            v ->
                new LinearFloat(
                    new FloatVar[] {fv(v[0]), fv(v[0])}, new double[] {1, 1}, "==", fv(v[1])),
            true));

    for (int n = 1; n <= 3; n++) {
      int m = n;
      boolean[] k = new boolean[n + 1];
      Arrays.fill(k, F);
      double[] lo = new double[n + 1];
      double[] hi = new double[n + 1];
      Arrays.fill(lo, -10);
      Arrays.fill(hi, 10);
      cases.add(
          function(
              "Max " + n,
              k,
              lo,
              hi,
              n,
              x -> Arrays.stream(x, 0, m).max().orElseThrow(),
              x -> max(Arrays.copyOf(x, m)),
              v -> new Max(Arrays.copyOf(v, m, FloatVar[].class), fv(v[m])),
              false));
      cases.add(
          function(
              "Min " + n,
              k,
              lo,
              hi,
              n,
              x -> Arrays.stream(x, 0, m).min().orElseThrow(),
              x -> min(Arrays.copyOf(x, m)),
              v -> new Min(Arrays.copyOf(v, m, FloatVar[].class), fv(v[m])),
              false));
    }

    double[] list = {-2.5, 0.75, 4, 0.75, -7, 3.125};
    cases.add(
        function(
            "ElementFloat",
            kinds(I, F),
            r(1, -10),
            r(list.length, 10),
            1,
            x -> x[0] >= 1 && x[0] <= list.length ? list[(int) x[0] - 1] : Double.NaN,
            x -> element(x[0], 1, i -> Iv.of(list[i - 1]), list.length),
            v -> new ElementFloat(iv(v[0]), list, fv(v[1])),
            false));
    cases.add(
        function(
            "ElementFloat offset -1",
            kinds(I, F),
            r(0, -10),
            r(list.length - 1, 10),
            1,
            x -> x[0] >= 0 && x[0] < list.length ? list[(int) x[0]] : Double.NaN,
            x -> element(x[0], 0, i -> Iv.of(list[i]), list.length - 1),
            v -> new ElementFloat(iv(v[0]), list, fv(v[1]), -1),
            false));
    cases.add(
        function(
            "ElementFloatVariable",
            kinds(I, F, F, F, F),
            r(1, -10, -10, -10, -10),
            r(3, 10, 10, 10, 10),
            4,
            x -> x[0] >= 1 && x[0] <= 3 ? x[(int) x[0]] : Double.NaN,
            x -> element(x[0], 1, i -> x[i], 3),
            v ->
                new ElementFloatVariable(
                    iv(v[0]), new FloatVar[] {fv(v[1]), fv(v[2]), fv(v[3])}, fv(v[4])),
            false));
    cases.addAll(repeatedCases());
    cases.addAll(scaledCases(cases));
    return cases;
  }

  /** Whether a box of one variable is the point 0 (1), excludes 0 (-1) or cannot tell (0). */
  private static int onlyZero(Iv[] x) {
    return x[0].isPoint() && x[0].lo().signum() == 0 ? 1 : x[0].containsZero() ? 0 : -1;
  }

  /** One variable at several positions of the scope, beyond x*x, x+x, x/x and x+x-y. */
  static List<Case> repeatedCases() {
    List<Case> cases = new ArrayList<>();
    double[] a2 = r(-10, -10);
    double[] b2 = r(10, 10);
    Iv zero = Iv.of(0);
    Iv one = Iv.of(1);
    cases.add(
        function(
            "PminusQeqR x-x",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> 0,
            x -> zero,
            v -> new PminusQeqR(fv(v[0]), fv(v[0]), fv(v[1])),
            true));
    cases.add(
        function(
            "PplusQeqR x+y=x",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> 0,
            x -> zero,
            v -> new PplusQeqR(fv(v[0]), fv(v[1]), fv(v[0])),
            true));
    cases.add(
        function(
            "PminusQeqR x-y=x",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> 0,
            x -> zero,
            v -> new PminusQeqR(fv(v[0]), fv(v[1]), fv(v[0])),
            true));
    cases.add(
        function(
            "PminusQeqR y-x=x",
            kinds(F, F),
            r(-5, -10),
            r(5, 10),
            1,
            x -> 2 * x[0],
            x -> mul(x[0], Iv.of(2)),
            v -> new PminusQeqR(fv(v[1]), fv(v[0]), fv(v[0])),
            true));
    cases.add(
        function(
            "PmulQeqR x*y=x",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> 1,
            x -> x[0].containsZero() ? Iv.ALL : one,
            v -> new PmulQeqR(fv(v[0]), fv(v[1]), fv(v[0])),
            false));
    cases.add(
        function(
            "PdivQeqR x/y=x",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> 1,
            x -> x[0].containsZero() ? Iv.ALL : one,
            v -> new PdivQeqR(fv(v[0]), fv(v[1]), fv(v[0])),
            false));
    cases.add(
        function(
            "PdivQeqR y/x=x",
            kinds(F, F),
            r(-3, -10),
            r(3, 10),
            1,
            x -> x[0] == 0 ? Double.NaN : x[0] * x[0],
            x -> pow(x[0], 2),
            v -> new PdivQeqR(fv(v[1]), fv(v[0]), fv(v[0])),
            false));
    cases.add(
        function(
            "Max x,y,x",
            kinds(F, F, F),
            r(-10, -10, -10),
            r(10, 10, 10),
            2,
            x -> Math.max(x[0], x[1]),
            x -> max(new Iv[] {x[0], x[1]}),
            v -> new Max(new FloatVar[] {fv(v[0]), fv(v[1]), fv(v[0])}, fv(v[2])),
            false));
    cases.add(
        predicate(
            "Max x,y = x",
            kinds(F, F),
            a2,
            b2,
            x -> le(x[1], x[0]),
            v -> new Max(new FloatVar[] {fv(v[0]), fv(v[1])}, fv(v[0])),
            false));
    cases.add(
        function(
            "Min x,y,x",
            kinds(F, F, F),
            r(-10, -10, -10),
            r(10, 10, 10),
            2,
            x -> Math.min(x[0], x[1]),
            x -> min(new Iv[] {x[0], x[1]}),
            v -> new Min(new FloatVar[] {fv(v[0]), fv(v[1]), fv(v[0])}, fv(v[2])),
            false));
    cases.add(
        predicate(
            "AbsPeqR x=x",
            kinds(F),
            r(-10),
            r(10),
            x ->
                x[0].lo() != null && x[0].lo().signum() >= 0
                    ? 1
                    : x[0].hi() != null && x[0].hi().signum() < 0 ? -1 : 0,
            v -> new AbsPeqR(fv(v[0]), fv(v[0])),
            false));
    cases.add(
        predicate(
            "ExpPeqR x=x",
            kinds(F),
            r(-10),
            r(10),
            x -> -1,
            v -> new ExpPeqR(fv(v[0]), fv(v[0])),
            false));
    cases.add(
        predicate(
            "LnPeqR x=x",
            kinds(F),
            r(-10),
            r(10),
            x -> -1,
            v -> new LnPeqR(fv(v[0]), fv(v[0])),
            false));
    cases.add(
        predicate(
            "SinPeqR x=x",
            kinds(F),
            r(-10),
            r(10),
            FloatPropagationFuzzTest::onlyZero,
            v -> new SinPeqR(fv(v[0]), fv(v[0])),
            false));
    cases.add(
        predicate(
            "AsinPeqR x=x",
            kinds(F),
            r(-10),
            r(10),
            FloatPropagationFuzzTest::onlyZero,
            v -> new AsinPeqR(fv(v[0]), fv(v[0])),
            false));
    cases.add(
        predicate(
            "AtanPeqR x=x",
            kinds(F),
            r(-10),
            r(10),
            FloatPropagationFuzzTest::onlyZero,
            v -> new AtanPeqR(fv(v[0]), fv(v[0])),
            false));
    cases.add(
        predicate(
            "SinhPeqR x=x",
            kinds(F),
            r(-10),
            r(10),
            FloatPropagationFuzzTest::onlyZero,
            v -> new HyperbolicPeqR(fv(v[0]), HyperbolicPeqR.Function.SINH, fv(v[0])),
            false));
    cases.add(
        predicate(
            "TanhPeqR x=x",
            kinds(F),
            r(-10),
            r(10),
            FloatPropagationFuzzTest::onlyZero,
            v -> new HyperbolicPeqR(fv(v[0]), HyperbolicPeqR.Function.TANH, fv(v[0])),
            false));
    cases.add(
        predicate(
            "CoshPeqR x=x",
            kinds(F),
            r(-10),
            r(10),
            x -> -1,
            v -> new HyperbolicPeqR(fv(v[0]), HyperbolicPeqR.Function.COSH, fv(v[0])),
            false));
    cases.add(
        predicate(
            "TanPeqR x=x",
            kinds(F),
            r(-1.5),
            r(1.5),
            FloatPropagationFuzzTest::onlyZero,
            v -> new TanPeqR(fv(v[0]), fv(v[0])),
            false));
    for (String rel : new String[] {"==", "!=", "<", "<=", ">", ">="}) {
      int holds = rel.equals("==") || rel.endsWith("=") && !rel.equals("!=") ? 1 : -1;
      cases.add(
          predicate(
              "Pcomp x " + rel + " x",
              kinds(F),
              r(-10),
              r(10),
              x -> holds,
              v ->
                  switch (rel) {
                    case "==" -> new PeqQ(fv(v[0]), fv(v[0]));
                    case "!=" -> new PneqQ(fv(v[0]), fv(v[0]));
                    case "<" -> new PltQ(fv(v[0]), fv(v[0]));
                    case "<=" -> new PlteqQ(fv(v[0]), fv(v[0]));
                    case ">" -> new PgtQ(fv(v[0]), fv(v[0]));
                    default -> new PgteqQ(fv(v[0]), fv(v[0]));
                  },
              true));
    }
    return cases;
  }

  /** Factors the ranges of some cases are scaled by: subnormal, tiny, huge and near overflow. */
  private static final double[] SCALES = {1e-310, 1e-160, 1e150, 1e300};

  /**
   * The cases whose relation holds at any magnitude (rational operations, abs, sqrt, comparisons,
   * linear rows, max and min) over the float ranges scaled by each of {@link #SCALES}; sin and atan
   * too, for the reduction of huge arguments and arguments near 0.
   */
  static List<Case> scaledCases(List<Case> singles) {
    List<Case> cases = new ArrayList<>();
    for (Case c : singles) {
      String n = c.name();
      boolean scalable =
          n.startsWith("Pplus")
              || n.startsWith("Pminus")
              || n.startsWith("PmulQ")
              || n.startsWith("PdivQ")
              || n.startsWith("AbsPeqR")
              || n.equals("SqrtPeqR")
              || n.equals("SinPeqR")
              || n.equals("AtanPeqR")
              || n.startsWith("PeqQ")
              || n.startsWith("PneqQ")
              || n.startsWith("PltQ")
              || n.startsWith("PlteqQ")
              || n.startsWith("LinearFloat") && n.contains(" var ")
              || n.startsWith("SumFloat")
              || n.startsWith("Max")
              || n.startsWith("Min");
      if (!scalable) {
        continue;
      }
      for (double scale : SCALES) {
        double[] lo = c.lo().clone();
        double[] hi = c.hi().clone();
        for (int i = 0; i < lo.length; i++) {
          if (c.isFloat()[i]) {
            lo[i] *= scale;
            hi[i] *= scale;
          }
        }
        cases.add(
            new Case(
                n + " scaled " + scale,
                c.isFloat(),
                lo,
                hi,
                c.fix(),
                c.enclose(),
                c.holds(),
                c.build(),
                c.primitive(),
                c.dep()));
      }
    }
    return cases;
  }

  /** A function on [from, ...) over an interval, or nothing at all below from. */
  private static Iv real(Iv a, double from, DoubleUnaryOperator f, int ulps) {
    return a.dlo() < from ? Iv.ALL : mono(a, f, ulps, true);
  }

  private static int compare(Iv s, String rel, Iv x) {
    return switch (rel) {
      case "<" -> lt(s, x);
      case "<=" -> le(s, x);
      case ">" -> lt(x, s);
      case ">=" -> le(x, s);
      default -> ne(s, x);
    };
  }

  /** The hull of the entries first..last that an index interval allows, or null if none. */
  private static Iv element(Iv index, int first, IntFunction<Iv> entry, int last) {
    int lo = (int) Math.max(first, Math.ceil(index.dlo()));
    int hi = (int) Math.min(last, Math.floor(index.dhi()));
    Iv e = null;
    for (int i = lo; i <= hi; i++) {
      Iv v = entry.apply(i);
      e = e == null ? v : v.hull(e);
    }
    return e;
  }
}
