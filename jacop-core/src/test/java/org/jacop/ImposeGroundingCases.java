/*
 * ImposeGroundingCases.java
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

package org.jacop;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.stream.Stream;
import org.jacop.ImposeGroundingHarness.Case;
import org.jacop.constraints.GCC;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusClteqZImplied;
import org.jacop.constraints.XplusCneqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XplusYgtC;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.cumulative.CumulativeUnaryOptional;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.constraints.knapsack.KnapsackDP;
import org.jacop.core.IntVar;
import org.junit.jupiter.params.provider.Arguments;

/**
 * Instance generators for {@link ImposeGroundingTest} for constraints that have none in {@link
 * GlobalConstraintBruteForceTest}. Add a generator per constraint and list it in {@link #cases()}.
 */
final class ImposeGroundingCases {

  private ImposeGroundingCases() {}

  static Stream<Arguments> cases() {
    return Stream.concat(
        Stream.of(
            Arguments.of(
                "XplusYeqZ",
                (Function<Random, Case>)
                    random ->
                        Case.primitive(
                            domains(random, 3, -2, 4),
                            x -> new XplusYeqZ(x[0], x[1], x[2]),
                            t -> t[0] + t[1] == t[2],
                            "")),
            Arguments.of(
                "GCC with first value", (Function<Random, Case>) ImposeGroundingCases::gcc),
            Arguments.of("Knapsack without DP", knapsack("Knapsack")),
            Arguments.of("KnapsackDP", knapsack("KnapsackDP")),
            Arguments.of("CumulativeOld", cumulative("CumulativeOld")),
            Arguments.of("CumulativeBasic flags", cumulative("CumulativeBasic")),
            Arguments.of("CumulativeEF", cumulative("Cumulative")),
            Arguments.of("CumulativeUnary flags", cumulative("CumulativeUnary")),
            Arguments.of("CumulativePrimary", cumulative("CumulativePrimary")),
            Arguments.of("CumulativeOptional", cumulative("CumulativeOptional")),
            Arguments.of("CumulativeUnaryOptional", cumulative("CumulativeUnaryOptional"))),
        additive());
  }

  /** Quantities, then capacity, then profit; weights and profits from 0 (KnapsackDP) or 1. */
  private static Function<Random, Case> knapsack(String kind) {
    return random -> {
      int n = 1 + random.nextInt(3);
      int lowest = kind.equals("KnapsackDP") ? 0 : 1;
      int[] weights = new int[n];
      int[] profits = new int[n];
      for (int i = 0; i < n; i++) {
        weights[i] = lowest + random.nextInt(4 - lowest);
        profits[i] = lowest + random.nextInt(4 - lowest);
      }
      int[][] domains = new int[n + 2][];
      for (int i = 0; i < n; i++) {
        domains[i] = domain(random, 0, 2);
      }
      domains[n] = domain(random, 0, 10);
      domains[n + 1] = domain(random, 0, 10);
      return Case.of(
          domains,
          (store, x) -> {
            IntVar[] quantities = Arrays.copyOfRange(x, 0, n);
            if (kind.equals("KnapsackDP")) {
              store.impose(
                  new KnapsackDP(profits.clone(), weights.clone(), quantities, x[n], x[n + 1]));
            } else {
              store.impose(
                  new Knapsack(profits.clone(), weights.clone(), quantities, x[n], x[n + 1])
                      .dynamicProgramming(false));
            }
          },
          t -> {
            int weight = 0;
            int profit = 0;
            for (int i = 0; i < n; i++) {
              weight += weights[i] * t[i];
              profit += profits[i] * t[i];
            }
            return weight == t[n] && profit == t[n + 1];
          },
          "weights=" + Arrays.toString(weights) + " profits=" + Arrays.toString(profits));
    };
  }

  /** GCC whose counters count 0..m-1 whatever the domains of x are. */
  private static Case gcc(Random random) {
    int n = 1 + random.nextInt(4);
    int m = 1 + random.nextInt(3);
    int[][] domains = new int[n + m][];
    for (int i = 0; i < n; i++) {
      // values up to m, which is not counted, so x must avoid it
      domains[i] = domain(random, 0, m);
    }
    for (int j = 0; j < m; j++) {
      domains[n + j] = domain(random, 0, n);
    }
    return Case.of(
        domains,
        (store, x) ->
            store.impose(new GCC(Arrays.copyOfRange(x, 0, n), Arrays.copyOfRange(x, n, n + m), 0)),
        t -> {
          int[] count = new int[m];
          for (int i = 0; i < n; i++) {
            if (t[i] >= m) {
              return false;
            }
            count[t[i]]++;
          }
          for (int j = 0; j < m; j++) {
            if (count[j] != t[n + j]) {
              return false;
            }
          }
          return true;
        },
        "counted values 0.." + (m - 1));
  }

  /**
   * The cumulative family. Variables are starts, durations, resources (n each), the limit, and for
   * the optional constraints n 0/1 presence variables. "CumulativePrimary" is CumulativeBasic with
   * constant durations and resources, which it delegates to the package-private CumulativePrimary.
   * The unary variants keep two positive resource usages above the limit and run the profile or
   * edge finding (with neither they do not check the constraint). A task with zero duration or zero
   * resource use (or absent) does not occupy the resource. The old org.jacop.constraints.Cumulative
   * also bounds every resource use by the limit; it is checked with profiles on (edge finding alone
   * is not a checker) and without pruning the limit to the maximal profile (setLimit), which is not
   * a relation on assignments.
   */
  private static Function<Random, Case> cumulative(String kind) {
    return random -> {
      boolean unary = kind.startsWith("CumulativeUnary");
      boolean optional = kind.endsWith("Optional");
      boolean primary = kind.equals("CumulativePrimary");
      boolean old = kind.equals("CumulativeOld");
      int n = 1 + random.nextInt(3);
      List<int[]> domains = new ArrayList<>(Arrays.asList(domains(random, n, 0, 3)));
      for (int i = 0; i < 2 * n; i++) {
        domains.add(primary ? new int[] {random.nextInt(3)} : domain(random, 0, 2));
      }
      domains.add(domain(random, 0, unary ? 1 : 3));
      if (optional) {
        domains.addAll(Arrays.asList(domains(random, n, 0, 1)));
      }
      boolean[] flags = new boolean[5];
      for (int i = 0; i < flags.length; i++) {
        flags[i] = random.nextBoolean();
      }
      return Case.of(
          domains.toArray(int[][]::new),
          (store, x) -> {
            IntVar[] s = Arrays.copyOfRange(x, 0, n);
            IntVar[] d = Arrays.copyOfRange(x, n, 2 * n);
            IntVar[] r = Arrays.copyOfRange(x, 2 * n, 3 * n);
            IntVar l = x[3 * n];
            IntVar[] o = optional ? Arrays.copyOfRange(x, 3 * n + 1, 4 * n + 1) : null;
            switch (kind) {
              case "CumulativeOld" ->
                  store.impose(
                      new org.jacop.constraints.Cumulative(s, d, r, l, flags[0], true, false));
              case "CumulativeBasic", "CumulativePrimary" ->
                  store.impose(new CumulativeBasic(s, d, r, l));
              case "Cumulative" -> {
                org.jacop.constraints.cumulative.Cumulative c =
                    new org.jacop.constraints.cumulative.Cumulative(s, d, r, l);
                c.doEdgeFind(flags[0]);
                c.doQuadraticEdgeFind(flags[1]);
                c.doOverload(flags[2]);
                c.doTimeTableEdgeFind(flags[3]);
                c.doTimeTableDisjunctive(flags[4]);
                store.impose(c);
              }
              case "CumulativeUnary" ->
                  store.impose(
                      flags[0] || flags[1]
                          ? new CumulativeUnary(s, d, r, l, flags[0], flags[1])
                          : new CumulativeUnary(s, d, r, l));
              case "CumulativeOptional" -> {
                CumulativeOptional c = new CumulativeOptional(s, d, r, l, o);
                c.doOptionalOverload(flags[0]);
                c.doEdgeFind(flags[1]);
                store.impose(c);
              }
              default -> {
                CumulativeUnaryOptional c =
                    new CumulativeUnaryOptional(s, d, r, l, o, flags[0], flags[1] || !flags[0]);
                c.doOptionalOverload(flags[2]);
                store.impose(c);
              }
            }
          },
          x -> {
            for (int i = 0; old && i < n; i++) {
              if (x[2 * n + i] > x[3 * n]) {
                return false;
              }
            }
            for (int t = 0; t <= 6; t++) {
              int use = 0;
              for (int i = 0; i < n; i++) {
                boolean present = !optional || x[3 * n + 1 + i] == 1;
                if (present && x[i] <= t && t < x[i] + x[n + i]) {
                  use += x[2 * n + i];
                }
              }
              if (use > x[3 * n]) {
                return false;
              }
            }
            return true;
          },
          kind + " flags=" + Arrays.toString(flags));
    };
  }

  static int[][] domains(Random random, int n, int lo, int hi) {
    int[][] domains = new int[n][];
    for (int i = 0; i < n; i++) {
      domains[i] = domain(random, lo, hi);
    }
    return domains;
  }

  /** A random non-empty subset of lo..hi, so domains may have holes. */
  static int[] domain(Random random, int lo, int hi) {
    List<Integer> values = new ArrayList<>();
    for (int v = lo; v <= hi; v++) {
      if (random.nextInt(4) != 0) {
        values.add(v);
      }
    }
    if (values.isEmpty()) {
      values.add(lo + random.nextInt(hi - lo + 1));
    }
    return values.stream().mapToInt(Integer::intValue).toArray();
  }

  /**
   * Batch B3: the additive constraints, including instances whose variables are aliased (the same
   * variable passed twice), where impose() and consistency() take special paths.
   */
  static Stream<Arguments> additive() {
    return Stream.of(
        primitive(
            "XplusYeqZ(x,x,z)",
            r -> domains(r, 2, -3, 4),
            (x, c) -> new XplusYeqZ(x[0], x[0], x[1]),
            (t, c) -> t[0] + t[0] == t[1]),
        primitive(
            "XplusYeqZ(x,y,x)",
            r -> domains(r, 2, -3, 4),
            (x, c) -> new XplusYeqZ(x[0], x[1], x[0]),
            (t, c) -> t[1] == 0),
        primitive(
            "XplusYeqZ(x,y,y)",
            r -> domains(r, 2, -3, 4),
            (x, c) -> new XplusYeqZ(x[0], x[1], x[1]),
            (t, c) -> t[0] == 0),
        primitive(
            "XplusYeqZ(x,x,x)",
            r -> domains(r, 1, -3, 4),
            (x, c) -> new XplusYeqZ(x[0], x[0], x[0]),
            (t, c) -> t[0] == 0),
        primitive(
            "XplusCeqZ",
            r -> domains(r, 2, -3, 4),
            (x, c) -> new XplusCeqZ(x[0], c, x[1]),
            (t, c) -> t[0] + c == t[1]),
        primitive(
            "XplusCeqZ(x,c,x)",
            r -> domains(r, 1, -3, 4),
            (x, c) -> new XplusCeqZ(x[0], c, x[0]),
            (t, c) -> c == 0),
        primitive(
            "XplusClteqZ",
            r -> domains(r, 2, -3, 4),
            (x, c) -> new XplusClteqZ(x[0], c, x[1]),
            (t, c) -> t[0] + c <= t[1]),
        primitive(
            "XplusClteqZ(x,c,x)",
            r -> domains(r, 1, -3, 4),
            (x, c) -> new XplusClteqZ(x[0], c, x[0]),
            (t, c) -> c <= 0),
        primitive(
            "XplusClteqZImplied",
            r -> new int[][] {domain(r, 0, 1), domain(r, -3, 4), domain(r, -3, 4)},
            (x, c) -> new XplusClteqZImplied(x[0], x[1], c, x[2]),
            (t, c) -> t[0] == 0 || t[1] + c <= t[2]),
        primitive(
            "XplusClteqZImplied(b,x,c,x)",
            r -> new int[][] {domain(r, 0, 1), domain(r, -3, 4)},
            (x, c) -> new XplusClteqZImplied(x[0], x[1], c, x[1]),
            (t, c) -> t[0] == 0 || c <= 0),
        primitive(
            "XplusCneqZ",
            r -> domains(r, 2, -3, 4),
            (x, c) -> new XplusCneqZ(x[0], c, x[1]),
            (t, c) -> t[0] + c != t[1]),
        primitive(
            "XplusYeqC",
            r -> domains(r, 2, -3, 4),
            (x, c) -> new XplusYeqC(x[0], x[1], c),
            (t, c) -> t[0] + t[1] == c),
        primitive(
            "XplusYeqC(x,x,c)",
            r -> domains(r, 1, -3, 4),
            (x, c) -> new XplusYeqC(x[0], x[0], c),
            (t, c) -> t[0] + t[0] == c),
        primitive(
            "XplusYgtC",
            r -> domains(r, 2, -3, 4),
            (x, c) -> new XplusYgtC(x[0], x[1], c),
            (t, c) -> t[0] + t[1] > c),
        primitive(
            "XplusYgtC(x,x,c)",
            r -> domains(r, 1, -3, 4),
            (x, c) -> new XplusYgtC(x[0], x[0], c),
            (t, c) -> t[0] + t[0] > c),
        primitive(
            "XplusYlteqZ",
            r -> domains(r, 3, -3, 4),
            (x, c) -> new XplusYlteqZ(x[0], x[1], x[2]),
            (t, c) -> t[0] + t[1] <= t[2]),
        primitive(
            "XplusYlteqZ(x,x,z)",
            r -> domains(r, 2, -3, 4),
            (x, c) -> new XplusYlteqZ(x[0], x[0], x[1]),
            (t, c) -> t[0] + t[0] <= t[1]));
  }

  /** A primitive constraint case with a random constant c in -3..3. */
  static Arguments primitive(
      String name,
      Function<Random, int[][]> domains,
      BiFunction<IntVar[], Integer, PrimitiveConstraint> build,
      BiPredicate<int[], Integer> semantics) {
    return Arguments.of(
        name,
        (Function<Random, Case>)
            random -> {
              int c = random.nextInt(7) - 3;
              return Case.primitive(
                  domains.apply(random),
                  x -> build.apply(x, c),
                  t -> semantics.test(t, c),
                  "c = " + c);
            });
  }
}
