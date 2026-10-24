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
import java.util.function.Function;
import java.util.stream.Stream;
import org.jacop.ImposeGroundingHarness.Case;
import org.jacop.constraints.GCC;
import org.jacop.constraints.XplusYeqZ;
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
    return Stream.of(
        Arguments.of(
            "XplusYeqZ",
            (Function<Random, Case>)
                random ->
                    Case.primitive(
                        domains(random, 3, -2, 4),
                        x -> new XplusYeqZ(x[0], x[1], x[2]),
                        t -> t[0] + t[1] == t[2],
                        "")),
        Arguments.of("GCC with first value", (Function<Random, Case>) ImposeGroundingCases::gcc),
        Arguments.of("Knapsack without DP", knapsack("Knapsack")),
        Arguments.of("KnapsackDP", knapsack("KnapsackDP")));
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
}
