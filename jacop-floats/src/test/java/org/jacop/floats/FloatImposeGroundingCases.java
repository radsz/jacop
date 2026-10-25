/*
 * FloatImposeGroundingCases.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.function.BiFunction;
import java.util.function.DoubleUnaryOperator;
import java.util.function.Function;
import java.util.stream.Stream;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.floats.FloatImposeGroundingHarness.Case;
import org.jacop.floats.FloatImposeGroundingHarness.Spec;
import org.jacop.floats.constraints.AbsPeqR;
import org.jacop.floats.constraints.AcosPeqR;
import org.jacop.floats.constraints.AsinPeqR;
import org.jacop.floats.constraints.AtanPeqR;
import org.jacop.floats.constraints.CeilPeqX;
import org.jacop.floats.constraints.CosPeqR;
import org.jacop.floats.constraints.ElementFloat;
import org.jacop.floats.constraints.ElementFloatVariable;
import org.jacop.floats.constraints.EquationSystem;
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
import org.jacop.floats.core.FloatVar;
import org.junit.jupiter.params.provider.Arguments;

/**
 * Instance generators for {@link FloatImposeGroundingTest}. Add a generator per constraint to
 * {@link #cases()} (append only, so that branches adding constraints merge easily).
 */
final class FloatImposeGroundingCases {

  private FloatImposeGroundingCases() {}

  /** The predicate of a comparison of two values. */
  private interface Comparison {
    boolean test(double a, double b);
  }

  /** The constructor of a comparison with a constant. */
  private interface WithConstant {
    PrimitiveConstraint build(FloatVar p, double c);
  }

  /** The constructor of a comparison of two variables. */
  private interface WithVariable {
    PrimitiveConstraint build(FloatVar p, FloatVar q);
  }

  static Stream<Arguments> cases() {
    List<Arguments> cases = new ArrayList<>();
    cases.add(withConstant("PeqC", PeqC::new, (a, b) -> a == b));
    cases.add(withConstant("PneqC", PneqC::new, (a, b) -> a != b));
    cases.add(withConstant("PltC", PltC::new, (a, b) -> a < b));
    cases.add(withConstant("PlteqC", PlteqC::new, (a, b) -> a <= b));
    cases.add(withConstant("PgtC", PgtC::new, (a, b) -> a > b));
    cases.add(withConstant("PgteqC", PgteqC::new, (a, b) -> a >= b));
    cases.add(withVariable("PeqQ", PeqQ::new, (a, b) -> a == b));
    cases.add(withVariable("PneqQ", PneqQ::new, (a, b) -> a != b));
    cases.add(withVariable("PltQ", PltQ::new, (a, b) -> a < b));
    cases.add(withVariable("PlteqQ", PlteqQ::new, (a, b) -> a <= b));
    cases.add(withVariable("PgtQ", PgtQ::new, (a, b) -> a > b));
    cases.add(withVariable("PgteqQ", PgteqQ::new, (a, b) -> a >= b));
    cases.add(
        Arguments.of(
            "XeqP",
            (Function<Random, Case>)
                random ->
                    new Case(
                        new Spec[] {integer(random, -2, 2), floatVar(random, 0.5, -2, 2)},
                        x -> new XeqP((IntVar) x[0], (FloatVar) x[1]),
                        t -> t[0] == t[1],
                        "XeqP(x0, x1)")));
    cases.add(rounding("CeilPeqX", CeilPeqX::new, Math::ceil));
    cases.add(rounding("FloorPeqX", FloorPeqX::new, Math::floor));
    // MiniZinc rounds halves away from zero, like Math.round on the absolute value
    cases.add(
        rounding("RoundPeqX", RoundPeqX::new, v -> Math.signum(v) * Math.floor(Math.abs(v) + 0.5)));
    cases.add(
        Arguments.of(
            "ElementFloat",
            (Function<Random, Case>)
                random -> {
                  // a few repeated values, and sometimes many, which ElementFloat treats apart
                  boolean many = random.nextInt(4) == 0;
                  int n = many ? 12 + random.nextInt(4) : 2 + random.nextInt(4);
                  double[] list = new double[n];
                  for (int i = 0; i < n; i++) {
                    list[i] = many && random.nextBoolean() ? 0.5 : grid(random, 0.5, -1, 1);
                  }
                  int offset = random.nextInt(3) - 1;
                  return new Case(
                      new Spec[] {
                        integer(random, offset, n + offset + 1), floatVar(random, 0.5, -1, 1)
                      },
                      x -> new ElementFloat((IntVar) x[0], list, (FloatVar) x[1], offset),
                      t -> {
                        int i = (int) t[0] - 1 - offset;
                        return i >= 0 && i < n && list[i] == t[1];
                      },
                      "ElementFloat(x0, " + Arrays.toString(list) + ", x1, " + offset + ")");
                }));
    cases.add(
        Arguments.of(
            "ElementFloatVariable",
            (Function<Random, Case>)
                random -> {
                  int n = 2 + random.nextInt(2);
                  int offset = random.nextInt(3) - 1;
                  Spec[] vars = new Spec[n + 2];
                  vars[0] = integer(random, offset, n + offset + 1);
                  for (int i = 1; i < n + 2; i++) {
                    vars[i] = floatVar(random, 0.5, -1, 1);
                  }
                  return new Case(
                      vars,
                      x ->
                          new ElementFloatVariable(
                              (IntVar) x[0],
                              Arrays.copyOfRange(x, 1, n + 1, FloatVar[].class),
                              (FloatVar) x[n + 1],
                              offset),
                      t -> {
                        int i = (int) t[0] - 1 - offset;
                        return i >= 0 && i < n && t[1 + i] == t[n + 1];
                      },
                      "ElementFloatVariable(x0, [x1..x"
                          + n
                          + "], x"
                          + (n + 1)
                          + ", "
                          + offset
                          + ")");
                }));
    cases.add(minMax("Max", true));
    cases.add(minMax("Min", false));
    cases.add(
        arithmetic(
            "PplusQeqR",
            random -> new Spec[] {quarter(random), quarter(random), quarter(random, -3, 3)},
            x -> new PplusQeqR(x[0], x[1], x[2]),
            t -> t[0] + t[1] == t[2]));
    cases.add(
        arithmetic(
            "PminusQeqR",
            random -> new Spec[] {quarter(random), quarter(random), quarter(random, -3, 3)},
            x -> new PminusQeqR(x[0], x[1], x[2]),
            t -> t[0] - t[1] == t[2]));
    cases.add(
        arithmetic(
            "PmulQeqR",
            random ->
                new Spec[] {
                  floatVar(random, 0.5, -2, 2), floatVar(random, 0.5, -2, 2), quarter(random, -3, 3)
                },
            x -> new PmulQeqR(x[0], x[1], x[2]),
            t -> t[0] * t[1] == t[2]));
    cases.add(
        arithmetic(
            "PmulQeqR square",
            random -> new Spec[] {floatVar(random, 0.5, -2, 2), quarter(random, -1, 4)},
            x -> new PmulQeqR(x[0], x[0], x[1]),
            t -> t[0] * t[0] == t[1]));
    cases.add(
        arithmetic(
            "PmulQeqR product is a factor",
            random -> new Spec[] {floatVar(random, 0.5, -1, 1), floatVar(random, 0.5, -1, 2)},
            x -> new PmulQeqR(x[0], x[1], x[0]),
            t -> t[0] * t[1] == t[0]));
    cases.add(
        arithmetic(
            "PdivQeqR",
            random ->
                new Spec[] {
                  floatVar(random, 0.125, -1, 1),
                  pick(random, -2, -1, -0.5, 0, 0.5, 1, 2),
                  quarter(random, -2, 2)
                },
            x -> new PdivQeqR(x[0], x[1], x[2]),
            t -> t[1] != 0 && t[0] / t[1] == t[2]));
    cases.add(
        withArithmeticConstant(
            "PplusCeqR", (p, c, r) -> new PplusCeqR(p, c, r), (p, c) -> p + c, 0.25, -1, 1));
    cases.add(
        withArithmeticConstant(
            "PminusCeqR", (p, c, r) -> new PminusCeqR(p, c, r), (p, c) -> p - c, 0.25, -1, 1));
    cases.add(
        withArithmeticConstant(
            "PmulCeqR", (p, c, r) -> new PmulCeqR(p, c, r), (p, c) -> p * c, 0.5, -2, 2));
    cases.add(
        withArithmeticConstant(
            "PdivCeqR", (p, c, r) -> new PdivCeqR(p, c, r), (p, c) -> p / c, 0.5, -2, 2));
    cases.add(
        arithmetic(
            "AbsPeqR",
            random -> new Spec[] {quarter(random), quarter(random, -1, 2)},
            x -> new AbsPeqR(x[0], x[1]),
            t -> Math.abs(t[0]) == t[1]));
    cases.add(
        arithmetic(
            "SqrtPeqR",
            random ->
                new Spec[] {
                  pick(random, -1, 0, 0.0625, 0.25, 0.5, 0.5625, 1, 1.5625, 2.25, 3, 4),
                  quarter(random, -1, 2)
                },
            x -> new SqrtPeqR(x[0], x[1]),
            t -> t[0] >= 0 && Math.sqrt(t[0]) == t[1]));
    cases.add(
        Arguments.of("LinearFloat", (Function<Random, Case>) random -> linear(random, false)));
    cases.add(Arguments.of("SumFloat", (Function<Random, Case>) random -> linear(random, true)));
    // transcendental functions: on dyadic grids f(x) is transcendental except at the trivial
    // points (sin 0 = 0, exp 0 = 1, ...), so f(x) == y is exact there and everything else must fail
    cases.add(function("SinPeqR", SinPeqR::new, Math::sin, -2, 2, -1.5, 1.5));
    cases.add(function("CosPeqR", CosPeqR::new, Math::cos, -2, 2, -1.5, 1.5));
    cases.add(function("TanPeqR", TanPeqR::new, Math::tan, -2, 2, -1.5, 1.5));
    cases.add(function("AsinPeqR", AsinPeqR::new, Math::asin, -1.5, 1.5, -2, 2));
    cases.add(function("AcosPeqR", AcosPeqR::new, Math::acos, -1.5, 1.5, -1, 2));
    cases.add(function("AtanPeqR", AtanPeqR::new, Math::atan, -2, 2, -2, 2));
    cases.add(function("ExpPeqR", ExpPeqR::new, Math::exp, -1, 2, -0.5, 3));
    cases.add(function("LnPeqR", LnPeqR::new, Math::log, -0.5, 3, -1, 2));
    cases.add(
        Arguments.of(
            "EquationSystem",
            (Function<Random, Case>)
                random ->
                    new Case(
                        new Spec[] {
                          floatVar(random, 0.5, -1, 1),
                          floatVar(random, 0.5, -1, 1),
                          floatVar(random, 0.5, -1, 1),
                          floatVar(random, 0.5, -1, 1)
                        },
                        x -> {
                          // f0 = x0 - x1 and f1 = x0 * x1 are defined in the store, and the
                          // system is solved for f0 = f1 = 0
                          FloatVar[] v = Arrays.copyOf(x, 4, FloatVar[].class);
                          Store store = x[0].getStore();
                          store.impose(
                              new LinearFloat(
                                  new FloatVar[] {v[0], v[1], v[2]},
                                  new double[] {1, -1, -1},
                                  "==",
                                  0));
                          store.impose(new PmulQeqR(v[0], v[1], v[3]));
                          store.impose(new PeqC(v[2], 0));
                          store.impose(new PeqC(v[3], 0));
                          return new EquationSystem(
                              store, new FloatVar[] {v[2], v[3]}, new FloatVar[] {v[0], v[1]});
                        },
                        t -> t[2] == t[0] - t[1] && t[3] == t[0] * t[1] && t[2] == 0 && t[3] == 0,
                        "x0 - x1 = x2, x0 * x1 = x3, EquationSystem([x2, x3], [x0, x1])")));
    return cases.stream();
  }

  /** A constraint on float variables only. */
  private interface OnFloats {
    Constraint build(FloatVar[] x);
  }

  private static Arguments arithmetic(
      String name,
      Function<Random, Spec[]> vars,
      OnFloats build,
      java.util.function.Predicate<double[]> relation) {
    return Arguments.of(
        name,
        (Function<Random, Case>)
            random ->
                new Case(
                    vars.apply(random),
                    x -> build.build(Arrays.copyOf(x, x.length, FloatVar[].class)),
                    relation,
                    name));
  }

  /** The constructor of an arithmetic constraint with a constant. */
  private interface ArithmeticWithConstant {
    Constraint build(FloatVar p, double c, FloatVar r);
  }

  private static Arguments withArithmeticConstant(
      String name,
      ArithmeticWithConstant build,
      java.util.function.DoubleBinaryOperator function,
      double step,
      double lo,
      double hi) {
    return Arguments.of(
        name,
        (Function<Random, Case>)
            random -> {
              // powers of two (and 0 and 1.5 where allowed) keep the results on the grid
              double c =
                  new double[] {-2, -1, -0.5, 0.25, 0.5, 1, 2, name.startsWith("PdivCeqR") ? 4 : 0}
                      [random.nextInt(8)];
              double c2 = name.equals("PmulCeqR") && random.nextInt(4) == 0 ? 1.5 : c;
              return new Case(
                  new Spec[] {floatVar(random, step, lo, hi), floatVar(random, 0.125, -4, 4)},
                  x -> build.build((FloatVar) x[0], c2, (FloatVar) x[1]),
                  t -> function.applyAsDouble(t[0], c2) == t[1],
                  name + "(x0, " + c2 + ", x1)");
            });
  }

  private static final String[] RELATIONS = {"==", "<", "<=", "!=", ">", ">="};

  /**
   * LinearFloat with a constant sum, or SumFloat with a sum variable. Weights are powers of two so
   * that the weighted sums are exact; a variable sometimes appears twice.
   */
  private static Case linear(Random random, boolean sumVariable) {
    int n = 1 + random.nextInt(3);
    String rel = RELATIONS[random.nextInt(RELATIONS.length)];
    double[] weights = new double[n];
    int[] index = new int[n];
    for (int i = 0; i < n; i++) {
      weights[i] = sumVariable ? 1 : new double[] {-2, -1, -0.5, 0.5, 1, 2}[random.nextInt(6)];
      index[i] = i > 0 && random.nextInt(6) == 0 ? 0 : i;
    }
    double sum = grid(random, 0.25, -2, 2);
    Spec[] vars = new Spec[sumVariable ? n + 1 : n];
    for (int i = 0; i < n; i++) {
      vars[i] = quarter(random);
    }
    if (sumVariable) {
      vars[n] = quarter(random, -3, 3);
    }
    return new Case(
        vars,
        x -> {
          FloatVar[] list = new FloatVar[n];
          for (int i = 0; i < n; i++) {
            list[i] = (FloatVar) x[index[i]];
          }
          return sumVariable
              ? new SumFloat(list, rel, (FloatVar) x[n])
              : new LinearFloat(list, weights, rel, sum);
        },
        t -> {
          double total = 0;
          for (int i = 0; i < n; i++) {
            total += weights[i] * t[index[i]];
          }
          double right = sumVariable ? t[n] : sum;
          return switch (rel) {
            case "==" -> total == right;
            case "<" -> total < right;
            case "<=" -> total <= right;
            case "!=" -> total != right;
            case ">" -> total > right;
            default -> total >= right;
          };
        },
        (sumVariable ? "SumFloat(" : "LinearFloat(" + Arrays.toString(weights) + ", ")
            + "x"
            + Arrays.toString(index)
            + ", "
            + rel
            + ", "
            + (sumVariable ? "x" + n : sum)
            + ")");
  }

  /** A float variable on multiples of 0.25 in -1..1. */
  private static Spec quarter(Random random) {
    return floatVar(random, 0.25, -1, 1);
  }

  /** A float variable on multiples of 0.25 in lo..hi. */
  private static Spec quarter(Random random, double lo, double hi) {
    return floatVar(random, 0.25, lo, hi);
  }

  /** A float variable on a random non-empty subset of the given values. */
  private static Spec pick(Random random, double... values) {
    List<Double> chosen = new ArrayList<>();
    for (double v : values) {
      if (random.nextInt(3) != 0) {
        chosen.add(v);
      }
    }
    if (chosen.isEmpty()) {
      chosen.add(values[random.nextInt(values.length)]);
    }
    double[] grid = chosen.stream().mapToDouble(Double::doubleValue).toArray();
    return random.nextInt(3) == 0 ? Spec.points(grid) : Spec.interval(grid);
  }

  private static Arguments withConstant(String name, WithConstant build, Comparison relation) {
    return Arguments.of(
        name,
        (Function<Random, Case>)
            random -> {
              // the constant is a grid point or halfway between two
              double c = grid(random, 0.25, -1.5, 1.5);
              return new Case(
                  new Spec[] {floatVar(random, 0.5, -1, 1)},
                  x -> build.build((FloatVar) x[0], c),
                  t -> relation.test(t[0], c),
                  name + "(x0, " + c + ")");
            });
  }

  private static Arguments withVariable(String name, WithVariable build, Comparison relation) {
    return Arguments.of(
        name,
        (Function<Random, Case>)
            random ->
                new Case(
                    new Spec[] {floatVar(random, 0.5, -1, 1), floatVar(random, 0.5, -1, 1)},
                    x -> build.build((FloatVar) x[0], (FloatVar) x[1]),
                    t -> relation.test(t[0], t[1]),
                    name + "(x0, x1)"));
  }

  /** The constructor of a rounding constraint. */
  private interface Rounding {
    Constraint build(FloatVar p, IntVar x);
  }

  private static Arguments rounding(String name, Rounding build, DoubleUnaryOperator round) {
    return Arguments.of(
        name,
        (Function<Random, Case>)
            random ->
                new Case(
                    new Spec[] {floatVar(random, 0.25, -2, 2), integer(random, -2, 2)},
                    x -> build.build((FloatVar) x[0], (IntVar) x[1]),
                    t -> round.applyAsDouble(t[0]) == t[1],
                    name + "(x0, x1)"));
  }

  private static Arguments minMax(String name, boolean max) {
    return Arguments.of(
        name,
        (Function<Random, Case>)
            random -> {
              int n = 1 + random.nextInt(3);
              Spec[] vars = new Spec[n + 1];
              for (int i = 0; i <= n; i++) {
                vars[i] = floatVar(random, 0.5, -1, 1);
              }
              return new Case(
                  vars,
                  x -> {
                    FloatVar[] list = Arrays.copyOf(x, n, FloatVar[].class);
                    return max ? new Max(list, (FloatVar) x[n]) : new Min(list, (FloatVar) x[n]);
                  },
                  t -> {
                    double m = t[0];
                    for (int i = 1; i < n; i++) {
                      m = max ? Math.max(m, t[i]) : Math.min(m, t[i]);
                    }
                    return m == t[n];
                  },
                  name + "([x0..x" + (n - 1) + "], x" + n + ")");
            });
  }

  /** A random multiple of step in lo..hi. */
  static double grid(Random random, double step, double lo, double hi) {
    int k = (int) Math.round((hi - lo) / step);
    return lo + step * random.nextInt(k + 1);
  }

  /**
   * A float variable with a random non-empty subset of the multiples of step in lo..hi as its grid;
   * its domain is either the interval spanned by the grid or the union of its points.
   */
  static Spec floatVar(Random random, double step, double lo, double hi) {
    List<Double> values = new ArrayList<>();
    int k = (int) Math.round((hi - lo) / step);
    for (int i = 0; i <= k; i++) {
      if (random.nextInt(4) != 0) {
        values.add(lo + step * i);
      }
    }
    if (values.isEmpty()) {
      values.add(grid(random, step, lo, hi));
    }
    double[] grid = values.stream().mapToDouble(Double::doubleValue).toArray();
    return random.nextInt(3) == 0 ? Spec.points(grid) : Spec.interval(grid);
  }

  /** An int variable with a random non-empty subset of lo..hi, so domains may have holes. */
  static Spec integer(Random random, int lo, int hi) {
    List<Integer> values = new ArrayList<>();
    for (int v = lo; v <= hi; v++) {
      if (random.nextInt(4) != 0) {
        values.add(v);
      }
    }
    if (values.isEmpty()) {
      values.add(lo + random.nextInt(hi - lo + 1));
    }
    return Spec.integer(values.stream().mapToInt(Integer::intValue).toArray());
  }

  private static Arguments function(
      String name,
      BiFunction<FloatVar, FloatVar, Constraint> build,
      DoubleUnaryOperator f,
      double pLo,
      double pHi,
      double qLo,
      double qHi) {
    return Arguments.of(
        name,
        (Function<Random, Case>)
            random ->
                new Case(
                    new Spec[] {floatVar(random, 0.25, pLo, pHi), floatVar(random, 0.25, qLo, qHi)},
                    x -> build.apply((FloatVar) x[0], (FloatVar) x[1]),
                    t -> f.applyAsDouble(t[0]) == t[1],
                    name + "(x0, x1)"));
  }
}
