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
import static org.junit.jupiter.api.Assertions.fail;

import java.time.Duration;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.List;
import java.util.Random;
import java.util.function.Function;
import java.util.function.ToDoubleFunction;
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
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Checks the float propagators against the real relation they stand for, by brute force over
 * sampled points.
 *
 * <p>Each trial draws a solution of the relation (or, under {@link Not}, a point that violates it),
 * builds a random box of intervals around it (some variables singleton, some float domains with a
 * hole) and samples further points of the box that satisfy the relation: these are the witnesses.
 * The constraint is imposed, plain or under {@link Not} or {@link Reified} when it is primitive,
 * and a random dive splits the intervals until every variable is singleton. At every node:
 *
 * <ul>
 *   <li>propagation keeps every witness that agrees with the decisions (up to a relative 1e-9), and
 *       fails only where no such witness exists: interval propagation is sound;
 *   <li>a node where every variable is singleton satisfies the relation up to 1e-6: no wrong
 *       solution is accepted;
 *   <li>nothing but {@link FailException} is thrown;
 *   <li>removing a level restores exactly the domains it started from.
 * </ul>
 *
 * <p>Trials per case are {@code floats.fuzz.trials} (lower in the {@code min} profile). To run it
 * at volume or on chosen cases:
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

  /** Relative slack within which a witness counts as kept, for the rounding of the reference. */
  private static final double KEEP_TOLERANCE = 1e-9;

  /** A sampled point is a witness of a predicate only if it holds by this relative margin. */
  private static final double STRICT_MARGIN = 1e-7;

  /** A point of singleton domains is accepted if the relation holds within this margin. */
  private static final double GROUND_TOLERANCE = 1e-6;

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
   *     it is a solution (null when there is none); null for a predicate, whose witnesses are the
   *     points that satisfy it by a margin
   * @param margin how well a point satisfies the relation: positive if it holds by that relative
   *     margin, negative if it is violated by it
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
      ToDoubleFunction<double[]> margin,
      Function<Var[], Constraint[]> build,
      boolean primitive,
      int dep) {}

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
   * found is no worse than any witness by more than the step: a cost bound or a split that loses
   * solutions would end the search with a worse optimum.
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
    double[] seedPoint = seedPoint(t, random);
    if (seedPoint == null) {
      return null;
    }
    buildBox(t, seedPoint, random);
    sampleWitnesses(t, seedPoint, random);
    Constraint[] constraints;
    try {
      constraints = wrapped(t);
    } catch (IllegalArgumentException e) {
      return null;
    }
    String where = describe(t, constraints);
    try {
      for (Constraint constraint : constraints) {
        t.store.impose(constraint);
      }
    } catch (FailException e) {
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
    for (double[] w : t.witnesses) {
      double slack = step + 1e-6 * (1 + Math.abs(w[cost]));
      // a witness on the boundary of the box can be a solution only up to rounding
      if (agrees(t, w, false) && best > w[cost] + slack) {
        return "minimising "
            + vars[cost].id()
            + " ended with "
            + (found ? best : "no solution")
            + ", but "
            + Arrays.toString(w)
            + " is a solution\n    "
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
    final List<double[]> witnesses = new ArrayList<>();
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

    /** Whether a full point (with the 0/1 coordinate under REIFIED) is a model of the wrapping. */
    double margin(double[] x) {
      double m = c.margin().applyAsDouble(Arrays.copyOf(x, c.isFloat().length));
      return switch (wrap) {
        case PLAIN -> m;
        case NOT -> -m;
        case REIFIED -> x[x.length - 1] == 1 ? m : -m;
      };
    }
  }

  private static String trial(Case c, Random random) {
    Wrap wrap = Wrap.PLAIN;
    if (c.primitive()) {
      int w = random.nextInt(4);
      wrap = w == 2 ? Wrap.NOT : w == 3 ? Wrap.REIFIED : Wrap.PLAIN;
    }
    Trial t = new Trial(c, wrap);
    double[] seedPoint = seedPoint(t, random);
    if (seedPoint == null) {
      return null;
    }
    buildBox(t, seedPoint, random);
    sampleWitnesses(t, seedPoint, random);

    Constraint[] constraints;
    try {
      constraints = wrapped(t);
    } catch (IllegalArgumentException e) {
      // a constructor may reject a box, for example a constant out of range
      return null;
    }
    String where = describe(t, constraints);
    try {
      for (Constraint constraint : constraints) {
        t.store.impose(constraint);
      }
    } catch (FailException e) {
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

  /** A point that the wrapping accepts, drawn from the ranges of the case. */
  private static double[] seedPoint(Trial t, Random random) {
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
      boolean wantTrue = t.wrap == Wrap.PLAIN || t.wrap == Wrap.REIFIED && x[n] == 1;
      if (wantTrue && c.fix() != null) {
        double[] fixed = c.fix().apply(Arrays.copyOf(x, n));
        if (fixed == null) {
          continue;
        }
        System.arraycopy(fixed, 0, x, 0, n);
        return x;
      }
      if (t.margin(x) > STRICT_MARGIN) {
        return x;
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

  /** Creates the variables over random intervals around the seed point. */
  private static void buildBox(Trial t, double[] seed, Random random) {
    int n = t.arity();
    t.vars = new Var[n];
    t.lo = new double[n];
    t.hi = new double[n];
    for (int i = 0; i < n; i++) {
      boolean isFloat = i < t.c.isFloat().length && t.c.isFloat()[i];
      double v = seed[i];
      if (!isFloat) {
        int below = random.nextInt(4) == 0 ? 0 : random.nextInt(4);
        int above = random.nextInt(4) == 0 ? 0 : random.nextInt(4);
        if (i == t.c.isFloat().length) {
          // the 0/1 variable of Reified
          below = (int) v - random.nextInt((int) v + 1);
          above = random.nextInt(2 - (int) v);
        }
        IntVar x = new IntVar(t.store, "x" + i, (int) v - below, (int) v + above);
        t.vars[i] = x;
        t.lo[i] = x.min();
        t.hi[i] = x.max();
        continue;
      }
      double lo = v - width(v, random);
      double hi = v + width(v, random);
      FloatIntervalDomain d = new FloatIntervalDomain();
      double holeLo = lo + (hi - lo) * random.nextDouble();
      double holeHi = holeLo + (hi - holeLo) * random.nextDouble() * 0.5;
      if (random.nextInt(6) == 0 && holeLo > lo && holeHi < hi && (v < holeLo || v > holeHi)) {
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

  /** The seed point and the sampled points of the box that the wrapping accepts. */
  private static void sampleWitnesses(Trial t, double[] seed, Random random) {
    t.witnesses.add(seed);
    COUNTS.get()[0]++;
    int n = t.c.isFloat().length;
    for (int s = 0; s < SAMPLES; s++) {
      double[] x = new double[t.arity()];
      for (int i = 0; i < x.length; i++) {
        x[i] = sampleIn(t.vars[i], random);
      }
      boolean wantTrue = t.wrap == Wrap.PLAIN || t.wrap == Wrap.REIFIED && x[n] == 1;
      if (wantTrue && t.c.fix() != null) {
        double[] fixed = t.c.fix().apply(Arrays.copyOf(x, n));
        if (fixed == null) {
          continue;
        }
        System.arraycopy(fixed, 0, x, 0, n);
        if (inDomains(t, x)) {
          t.witnesses.add(x);
        }
      } else if (t.margin(x) > STRICT_MARGIN) {
        t.witnesses.add(x);
      }
    }
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

  /** Whether each coordinate of x is in the domain of its variable, exactly. */
  private static boolean inDomains(Trial t, double[] x) {
    for (int i = 0; i < x.length; i++) {
      Var v = t.vars[i];
      if (v instanceof IntVar iv) {
        if (x[i] != Math.rint(x[i]) || !iv.domain.contains((int) x[i])) {
          return false;
        }
      } else if (!((FloatVar) v).dom().contains(x[i])) {
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
        double[] missed = resample(t, random);
        if (missed != null) {
          return "both branches failed on the solution "
              + Arrays.toString(missed)
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

  /** A point of the current domains that the wrapping accepts, sampled densely, or null. */
  private static double[] resample(Trial t, Random random) {
    int n = t.c.isFloat().length;
    for (int s = 0; s < 50 * SAMPLES; s++) {
      double[] x = new double[t.arity()];
      for (int i = 0; i < x.length; i++) {
        x[i] = sampleIn(t.vars[i], random);
      }
      boolean wantTrue = t.wrap == Wrap.PLAIN || t.wrap == Wrap.REIFIED && x[n] == 1;
      if (wantTrue && t.c.fix() != null) {
        double[] fixed = t.c.fix().apply(Arrays.copyOf(x, n));
        if (fixed == null) {
          continue;
        }
        System.arraycopy(fixed, 0, x, 0, n);
      } else if (t.margin(x) <= STRICT_MARGIN) {
        continue;
      }
      if (inDomains(t, x) && agrees(t, x, false)) {
        return x;
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
    } catch (FailException e) {
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
    } catch (FailException e) {
      consistent = false;
    } catch (RuntimeException | StackOverflowError e) {
      return what + " consistency threw " + e + "\n    " + where;
    }
    if (!consistent) {
      t.failed = true;
      return checkFailure(t, what, where);
    }
    t.failed = false;
    for (double[] w : t.witnesses) {
      if (agrees(t, w, true)) {
        int lost = lostCoordinate(t, w);
        if (lost >= 0) {
          return what
              + " removed the solution "
              + Arrays.toString(w)
              + ": "
              + t.vars[lost]
              + "\n    "
              + where;
        }
      }
    }
    return null;
  }

  /** A failure is right only if no witness agrees with the decisions. */
  private static String checkFailure(Trial t, String what, String where) {
    for (double[] w : t.witnesses) {
      if (agrees(t, w, false)) {
        return what + " failed with the solution " + Arrays.toString(w) + "\n    " + where;
      }
    }
    return null;
  }

  /**
   * Whether a witness lies within the bounds the decisions allow; strictly inside them by the keep
   * tolerance unless loose is set.
   */
  private static boolean agrees(Trial t, double[] w, boolean loose) {
    for (int i = 0; i < w.length; i++) {
      double tol = t.vars[i] instanceof IntVar ? 0 : KEEP_TOLERANCE * (1 + Math.abs(w[i]));
      if (loose) {
        tol = 0;
      }
      if (w[i] < t.lo[i] + tol || w[i] > t.hi[i] - tol) {
        return false;
      }
    }
    return true;
  }

  /** The first coordinate of w that its variable's domain lost, or -1. */
  private static int lostCoordinate(Trial t, double[] w) {
    for (int i = 0; i < w.length; i++) {
      Var v = t.vars[i];
      if (v instanceof IntVar x) {
        if (!x.domain.contains((int) w[i])) {
          return i;
        }
        continue;
      }
      FloatDomain d = ((FloatVar) v).dom();
      double tol = KEEP_TOLERANCE * (1 + Math.abs(w[i])) + FloatDomain.precision();
      boolean kept = false;
      for (int k = 0; k < d.noIntervals() && !kept; k++) {
        kept = w[i] >= d.leftElement(k) - tol && w[i] <= d.rightElement(k) + tol;
      }
      if (!kept) {
        return i;
      }
    }
    return -1;
  }

  /** A node where every variable is singleton must be a solution, up to the ground tolerance. */
  private static String checkGround(Trial t, String where) {
    double[] x = new double[t.vars.length];
    for (int i = 0; i < x.length; i++) {
      if (t.vars[i] instanceof IntVar v) {
        x[i] = v.value();
      } else {
        FloatVar f = (FloatVar) t.vars[i];
        x[i] = (f.min() + f.max()) / 2;
      }
    }
    if (t.margin(x) < -GROUND_TOLERANCE) {
      return "accepted " + Arrays.toString(x) + ", which is not a solution\n    " + where;
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
  // the cases

  private static final boolean F = true;
  private static final boolean I = false;

  private static boolean[] kinds(boolean... k) {
    return k;
  }

  private static double[] r(double... v) {
    return v;
  }

  /** Margin of a = b, scaled by their size. */
  private static double eq(double a, double b) {
    return -Math.abs(a - b) / (1 + Math.abs(a) + Math.abs(b));
  }

  /** Margin of a <= b (and of a < b, which differ only on a set the samples do not hit). */
  private static double le(double a, double b) {
    return (b - a) / (1 + Math.abs(a) + Math.abs(b));
  }

  private static double ne(double a, double b) {
    return a == b ? -1 : Math.abs(a - b) / (1 + Math.abs(a) + Math.abs(b));
  }

  /** A functional case: coordinate {@code dep} is f of the others. */
  private static Case function(
      String name,
      boolean[] kinds,
      double[] lo,
      double[] hi,
      int dep,
      ToDoubleFunction<double[]> f,
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
        x -> {
          double v = f.applyAsDouble(x);
          return Double.isFinite(v) ? eq(x[dep], v) : -1;
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
      ToDoubleFunction<double[]> margin,
      Function<Var[], Constraint> build,
      boolean primitive) {
    return new Case(
        name, kinds, lo, hi, null, margin, v -> new Constraint[] {build.apply(v)}, primitive, -1);
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

  /** Margin of x = g(p) for a step function g: true, false, or 0 within 1e-9 of a step. */
  private static double step(double x, double p, ToDoubleFunction<Double> g) {
    double d = 1e-9 * (1 + Math.abs(p));
    if (x == g.applyAsDouble(p)) {
      return 1;
    }
    return x == g.applyAsDouble(p - d) || x == g.applyAsDouble(p + d) ? 0 : -1;
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
    Function<double[], double[]> partB =
        x -> {
          double[] y = new double[nb];
          for (int j = 0; j < nb; j++) {
            y[j] = x[map[j]];
          }
          return y;
        };
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
          double[] yb = b.fix().apply(partB.apply(z));
          if (yb == null) {
            return null;
          }
          for (int j = 0; j < nb; j++) {
            z[map[j]] = yb[j];
          }
          return z;
        },
        x ->
            Math.min(
                a.margin().applyAsDouble(Arrays.copyOf(x, na)),
                b.margin().applyAsDouble(partB.apply(x))),
        v -> {
          Var[] vb = new Var[nb];
          for (int j = 0; j < nb; j++) {
            vb[j] = v[map[j]];
          }
          Constraint[] ca = a.build().apply(Arrays.copyOf(v, na));
          Constraint[] cb = b.build().apply(vb);
          Constraint[] all = Arrays.copyOf(ca, ca.length + cb.length);
          System.arraycopy(cb, 0, all, ca.length, cb.length);
          return all;
        },
        false,
        -1);
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
      // b's argument that the shared variable becomes: never b's result, same kind
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

  static List<Case> singleCases() {
    List<Case> cases = new ArrayList<>();
    double[] a3 = r(-10, -10, -10);
    double[] b3 = r(10, 10, 10);
    double[] a2 = r(-10, -10);
    double[] b2 = r(10, 10);

    // arithmetic
    cases.add(
        function(
            "PplusQeqR",
            kinds(F, F, F),
            a3,
            b3,
            2,
            x -> x[0] + x[1],
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
            v -> new PdivQeqR(fv(v[0]), fv(v[1]), fv(v[2])),
            false));
    for (double c : new double[] {-2.5, -1, 0.5, 3}) {
      cases.add(
          function(
              "PplusCeqR " + c,
              kinds(F, F),
              a2,
              b2,
              1,
              x -> x[0] + c,
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
              v -> new PdivCeqR(fv(v[0]), c, fv(v[1])),
              false));
    }
    // the same variable twice
    cases.add(
        function(
            "PmulQeqR x*x",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> x[0] * x[0],
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
            v -> new PdivQeqR(fv(v[0]), fv(v[0]), fv(v[1])),
            false));

    // functions
    cases.add(
        function(
            "AbsPeqR",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> Math.abs(x[0]),
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
            v -> new SqrtPeqR(fv(v[0]), fv(v[1])),
            false));
    cases.add(
        function(
            "ExpPeqR",
            kinds(F, F),
            r(-8, -8),
            r(5, 5),
            1,
            x -> Math.exp(x[0]),
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
            v -> new AtanPeqR(fv(v[0]), fv(v[1])),
            false));

    // int and float
    cases.add(
        function(
            "XeqP",
            kinds(I, F),
            r(-6, -6),
            r(6, 6),
            1,
            x -> x[0],
            v -> new XeqP(iv(v[0]), fv(v[1])),
            false));
    cases.add(
        new Case(
            "RoundPeqX",
            kinds(F, I),
            r(-6, -6),
            r(6, 6),
            x -> new double[] {x[0], roundAway(x[0])},
            x -> step(x[1], x[0], FloatPropagationFuzzTest::roundAway),
            v -> new Constraint[] {new RoundPeqX(fv(v[0]), iv(v[1]))},
            false,
            1));
    cases.add(
        new Case(
            "FloorPeqX",
            kinds(F, I),
            r(-6, -6),
            r(6, 6),
            x -> new double[] {x[0], Math.floor(x[0])},
            x -> step(x[1], x[0], Math::floor),
            v -> new Constraint[] {new FloorPeqX(fv(v[0]), iv(v[1]))},
            false,
            1));
    cases.add(
        new Case(
            "CeilPeqX",
            kinds(F, I),
            r(-6, -6),
            r(6, 6),
            x -> new double[] {x[0], Math.ceil(x[0])},
            x -> step(x[1], x[0], Math::ceil),
            v -> new Constraint[] {new CeilPeqX(fv(v[0]), iv(v[1]))},
            false,
            1));

    // comparisons
    cases.add(
        predicate(
            "PeqQ",
            kinds(F, F),
            a2,
            b2,
            x -> eq(x[0], x[1]),
            v -> new PeqQ(fv(v[0]), fv(v[1])),
            true));
    // PeqQ has no witness from sampling, so its solutions come from x = y
    cases.add(
        function(
            "PeqQ functional",
            kinds(F, F),
            a2,
            b2,
            1,
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
            x -> le(x[0], x[1]),
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
            x -> le(x[1], x[0]),
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
      cases.add(
          function(
              "PeqC " + c, kinds(F), r(-10), r(10), 0, x -> c, v -> new PeqC(fv(v[0]), c), true));
      cases.add(
          predicate(
              "PneqC " + c,
              kinds(F),
              r(-10),
              r(10),
              x -> ne(x[0], c),
              v -> new PneqC(fv(v[0]), c),
              true));
      cases.add(
          predicate(
              "PltC " + c,
              kinds(F),
              r(-10),
              r(10),
              x -> le(x[0], c),
              v -> new PltC(fv(v[0]), c),
              true));
      cases.add(
          predicate(
              "PlteqC " + c,
              kinds(F),
              r(-10),
              r(10),
              x -> le(x[0], c),
              v -> new PlteqC(fv(v[0]), c),
              true));
      cases.add(
          predicate(
              "PgtC " + c,
              kinds(F),
              r(-10),
              r(10),
              x -> le(c, x[0]),
              v -> new PgtC(fv(v[0]), c),
              true));
      cases.add(
          predicate(
              "PgteqC " + c,
              kinds(F),
              r(-10),
              r(10),
              x -> le(c, x[0]),
              v -> new PgteqC(fv(v[0]), c),
              true));
    }

    // linear
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
              v -> new LinearFloat(list.apply(v), w, "==", fv(v[n])),
              true));
      cases.add(
          new Case(
              "LinearFloat == const " + ws,
              Arrays.copyOf(k, n),
              Arrays.copyOf(lo, n),
              Arrays.copyOf(hi, n),
              null,
              x -> eq(sum.applyAsDouble(x), 1.5),
              v ->
                  new Constraint[] {
                    new LinearFloat(Arrays.copyOf(v, n, FloatVar[].class), w, "==", 1.5)
                  },
              true,
              -1));
      for (String rel : new String[] {"<", "<=", ">", ">=", "!="}) {
        cases.add(
            predicate(
                "LinearFloat " + rel + " var " + ws,
                k,
                lo,
                hi,
                x -> {
                  double s = sum.applyAsDouble(x);
                  return switch (rel) {
                    case "<", "<=" -> le(s, x[n]);
                    case ">", ">=" -> le(x[n], s);
                    default -> ne(s, x[n]);
                  };
                },
                v -> new LinearFloat(list.apply(v), w, rel, fv(v[n])),
                true));
        cases.add(
            predicate(
                "LinearFloat " + rel + " const " + ws,
                Arrays.copyOf(k, n),
                Arrays.copyOf(lo, n),
                Arrays.copyOf(hi, n),
                x -> {
                  double s = sum.applyAsDouble(x);
                  return switch (rel) {
                    case "<", "<=" -> le(s, 2.5);
                    case ">", ">=" -> le(2.5, s);
                    default -> ne(s, 2.5);
                  };
                },
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
            v -> new SumFloat(new FloatVar[] {fv(v[0]), fv(v[1]), fv(v[2])}, "==", fv(v[3])),
            true));
    // a linear constraint with the same variable twice
    cases.add(
        function(
            "LinearFloat x+x-y",
            kinds(F, F),
            a2,
            b2,
            1,
            x -> 2 * x[0],
            v ->
                new LinearFloat(
                    new FloatVar[] {fv(v[0]), fv(v[0])}, new double[] {1, 1}, "==", fv(v[1])),
            true));

    // min, max
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
              v -> new Min(Arrays.copyOf(v, m, FloatVar[].class), fv(v[m])),
              false));
    }

    // element
    double[] list = {-2.5, 0.75, 4, 0.75, -7, 3.125};
    cases.add(
        function(
            "ElementFloat",
            kinds(I, F),
            r(1, -10),
            r(list.length, 10),
            1,
            x -> x[0] >= 1 && x[0] <= list.length ? list[(int) x[0] - 1] : Double.NaN,
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
            v ->
                new ElementFloatVariable(
                    iv(v[0]), new FloatVar[] {fv(v[1]), fv(v[2]), fv(v[3])}, fv(v[4])),
            false));
    return cases;
  }
}
