/*
 * GlobalConstraintBruteForceTest.java
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

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.AllEqual;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.AlldifferentExcept;
import org.jacop.constraints.AlldifferentExceptZero;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Among;
import org.jacop.constraints.ArgMax;
import org.jacop.constraints.ArgMin;
import org.jacop.constraints.Assignment;
import org.jacop.constraints.AtLeast;
import org.jacop.constraints.AtMost;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.Count;
import org.jacop.constraints.CountBounds;
import org.jacop.constraints.CountValues;
import org.jacop.constraints.CountVar;
import org.jacop.constraints.Decreasing;
import org.jacop.constraints.Diff2;
import org.jacop.constraints.Distance;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.ElementVariable;
import org.jacop.constraints.ElementVariableFast;
import org.jacop.constraints.ExtensionalConflictVa;
import org.jacop.constraints.ExtensionalSupportMdd;
import org.jacop.constraints.ExtensionalSupportStr;
import org.jacop.constraints.ExtensionalSupportVa;
import org.jacop.constraints.GCC;
import org.jacop.constraints.Increasing;
import org.jacop.constraints.Lex;
import org.jacop.constraints.LexOrder;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.Max;
import org.jacop.constraints.Member;
import org.jacop.constraints.Min;
import org.jacop.constraints.SeqPrecedeChain;
import org.jacop.constraints.Sequence;
import org.jacop.constraints.Stretch;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.ValuePrecede;
import org.jacop.constraints.Values;
import org.jacop.constraints.XdivYeqZ;
import org.jacop.constraints.XexpYeqZ;
import org.jacop.constraints.XmodYeqZ;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.constraints.diffn.Nooverlap;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.constraints.regular.CostRegular;
import org.jacop.constraints.regular.Regular;
import org.jacop.constraints.table.HybridTable;
import org.jacop.constraints.table.SimpleTable;
import org.jacop.constraints.table.Table;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.Indomain;
import org.jacop.search.IndomainMax;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Compares the set of all solutions JaCoP finds for a single global constraint over small random
 * domains (with holes) with a brute-force enumeration of every assignment. Each trial searches with
 * a different value order, so missing solutions, wrong solutions and exceptions all show up.
 */
class GlobalConstraintBruteForceTest {

  private static final int TRIALS = 300;

  private static final String[] RELATIONS = {"==", "!=", "<", "<=", ">", ">="};

  /** One random instance: the variable domains, the constraint and its intended semantics. */
  private record Instance(
      int[][] domains,
      BiConsumer<Store, IntVar[]> impose,
      Predicate<int[]> semantics,
      String description) {}

  static Stream<Arguments> cases() {
    return Stream.of(
        Arguments.of("Alldiff", alldiff("Alldiff")),
        Arguments.of("Alldifferent", alldiff("Alldifferent")),
        Arguments.of("Alldistinct", alldiff("Alldistinct")),
        Arguments.of(
            "AlldifferentExceptZero",
            (Function<Random, Instance>) GlobalConstraintBruteForceTest::alldifferentExceptZero),
        Arguments.of(
            "AlldifferentExcept",
            (Function<Random, Instance>) GlobalConstraintBruteForceTest::alldifferentExcept),
        Arguments.of(
            "AllEqual", (Function<Random, Instance>) GlobalConstraintBruteForceTest::allEqual),
        Arguments.of("GCC", (Function<Random, Instance>) GlobalConstraintBruteForceTest::gcc),
        Arguments.of("Among", (Function<Random, Instance>) GlobalConstraintBruteForceTest::among),
        Arguments.of("Count", (Function<Random, Instance>) GlobalConstraintBruteForceTest::count),
        Arguments.of(
            "CountBounds",
            (Function<Random, Instance>) GlobalConstraintBruteForceTest::countBounds),
        Arguments.of(
            "CountVar", (Function<Random, Instance>) GlobalConstraintBruteForceTest::countVar),
        Arguments.of(
            "CountValues",
            (Function<Random, Instance>) GlobalConstraintBruteForceTest::countValues),
        Arguments.of("AtLeast", atLeastOrMost(true)),
        Arguments.of("AtMost", atLeastOrMost(false)),
        Arguments.of("ElementInteger", elementInteger(false)),
        Arguments.of("ElementIntegerFast", elementInteger(true)),
        Arguments.of("ElementVariable", elementVariable(false)),
        Arguments.of("ElementVariableFast", elementVariable(true)),
        Arguments.of("Circuit", circuit(false)),
        Arguments.of("Subcircuit", circuit(true)),
        Arguments.of(
            "Regular", (Function<Random, Instance>) GlobalConstraintBruteForceTest::regular),
        Arguments.of("CostRegular", costRegular(false)),
        Arguments.of("CostRegularDecomposition", costRegular(true)),
        Arguments.of(
            "Sequence", (Function<Random, Instance>) GlobalConstraintBruteForceTest::sequence),
        Arguments.of(
            "Stretch", (Function<Random, Instance>) GlobalConstraintBruteForceTest::stretch),
        Arguments.of("Lex", (Function<Random, Instance>) GlobalConstraintBruteForceTest::lex),
        Arguments.of(
            "LexOrder", (Function<Random, Instance>) GlobalConstraintBruteForceTest::lexOrder),
        Arguments.of("Values", (Function<Random, Instance>) GlobalConstraintBruteForceTest::values),
        Arguments.of(
            "Assignment", (Function<Random, Instance>) GlobalConstraintBruteForceTest::assignment),
        Arguments.of("Max", maxOrMin(true)),
        Arguments.of("Min", maxOrMin(false)),
        Arguments.of("ArgMax", argMaxOrMin(true)),
        Arguments.of("ArgMin", argMaxOrMin(false)),
        Arguments.of("Increasing", monotonic(true)),
        Arguments.of("Decreasing", monotonic(false)),
        Arguments.of(
            "ValuePrecede",
            (Function<Random, Instance>) GlobalConstraintBruteForceTest::valuePrecede),
        Arguments.of(
            "SeqPrecedeChain",
            (Function<Random, Instance>) GlobalConstraintBruteForceTest::seqPrecedeChain),
        Arguments.of("Member", (Function<Random, Instance>) GlobalConstraintBruteForceTest::member),
        Arguments.of(
            "Distance", (Function<Random, Instance>) GlobalConstraintBruteForceTest::distance),
        Arguments.of("XmulYeqZ", arithmetic("XmulYeqZ")),
        Arguments.of("XdivYeqZ", arithmetic("XdivYeqZ")),
        Arguments.of("XmodYeqZ", arithmetic("XmodYeqZ")),
        Arguments.of("XexpYeqZ", arithmetic("XexpYeqZ")),
        Arguments.of(
            "AbsXeqY", (Function<Random, Instance>) GlobalConstraintBruteForceTest::absXeqY),
        Arguments.of("LinearInt", linear("LinearInt")),
        Arguments.of("LinearIntDom", linear("LinearIntDom")),
        Arguments.of("SumWeight", linear("SumWeight")),
        Arguments.of("SumInt", (Function<Random, Instance>) GlobalConstraintBruteForceTest::sumInt),
        Arguments.of(
            "SumBool", (Function<Random, Instance>) GlobalConstraintBruteForceTest::sumBool),
        Arguments.of("Table", table("Table")),
        Arguments.of("SimpleTable", table("SimpleTable")),
        Arguments.of("HybridTable", table("HybridTable")),
        Arguments.of("ExtensionalSupportVa", table("ExtensionalSupportVa")),
        Arguments.of("ExtensionalSupportStr", table("ExtensionalSupportStr")),
        Arguments.of("ExtensionalSupportMdd", table("ExtensionalSupportMdd")),
        Arguments.of("ExtensionalConflictVa", table("ExtensionalConflictVa")),
        Arguments.of(
            "Binpacking", (Function<Random, Instance>) GlobalConstraintBruteForceTest::binpacking),
        Arguments.of(
            "Knapsack", (Function<Random, Instance>) GlobalConstraintBruteForceTest::knapsack),
        Arguments.of("CumulativeBasic", cumulative(false)),
        Arguments.of("CumulativeUnary", cumulative(true)),
        Arguments.of("Diffn", rectangles("Diffn")),
        Arguments.of("DiffnStrict", rectangles("DiffnStrict")),
        Arguments.of("Nooverlap", rectangles("Nooverlap")),
        Arguments.of("Diff2", rectangles("Diff2")));
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("cases")
  void solutionsMatchBruteForce(String name, Function<Random, Instance> generator) {
    Random random = new Random(name.hashCode());
    for (int trial = 0; trial < TRIALS; trial++) {
      Instance instance = generator.apply(random);
      Set<List<Integer>> expected = new HashSet<>();
      bruteForce(instance, new int[instance.domains().length], 0, expected);

      assertThat(solveAll(instance, trial % 3, random.nextInt()))
          .as(
              "%s trial %d domains=%s %s",
              name, trial, Arrays.deepToString(instance.domains()), instance.description())
          .isEqualTo(expected);
    }
  }

  private static Instance regular(Random random) {
    int n = 1 + random.nextInt(4);
    int states = 1 + random.nextInt(3);
    // random automaton over the alphabet {0, 1, 2}; -1 means no transition
    int[][] delta = new int[states][3];
    for (int[] row : delta) {
      for (int c = 0; c < 3; c++) {
        row[c] = random.nextInt(states + 1) - 1;
      }
    }
    boolean[] accepting = new boolean[states];
    for (int q = 0; q < states; q++) {
      accepting[q] = random.nextBoolean();
    }
    return new Instance(
        domains(random, n, 0, 2),
        (store, x) -> {
          Fsm fsm = new Fsm();
          FsmState[] state = new FsmState[states];
          for (int q = 0; q < states; q++) {
            state[q] = new FsmState();
            fsm.allStates.add(state[q]);
          }
          fsm.initState = state[0];
          for (int q = 0; q < states; q++) {
            if (accepting[q]) {
              fsm.finalStates.add(state[q]);
            }
            for (int c = 0; c < 3; c++) {
              if (delta[q][c] >= 0) {
                state[q].addTransition(
                    new FsmTransition(new IntervalDomain(c, c), state[delta[q][c]]));
              }
            }
          }
          store.impose(new Regular(fsm, x));
        },
        x -> {
          int q = 0;
          for (int c : x) {
            q = delta[q][c];
            if (q < 0) {
              return false;
            }
          }
          return accepting[q];
        },
        "delta=" + Arrays.deepToString(delta) + " accepting=" + Arrays.toString(accepting));
  }

  /** Cost regular over the alphabet {0, 1, 2}; the last variable is the cost. */
  private static Function<Random, Instance> costRegular(boolean decomposition) {
    return random -> {
      int n = random.nextInt(5);
      int states = 1 + random.nextInt(3);
      int[][] delta = new int[states][3];
      for (int[] row : delta) {
        for (int c = 0; c < 3; c++) {
          row[c] = random.nextInt(states + 1) - 1;
        }
      }
      List<Integer> accepting = new ArrayList<>();
      for (int q = 0; q < states; q++) {
        if (random.nextBoolean()) {
          accepting.add(q);
        }
      }
      int[] finals = accepting.stream().mapToInt(Integer::intValue).toArray();
      // costs per position, sometimes the same matrix for every position
      boolean layered = random.nextBoolean();
      int[][][] costs = new int[n][][];
      for (int i = 0; i < n; i++) {
        if (i > 0 && !layered) {
          costs[i] = costs[0];
          continue;
        }
        costs[i] = new int[states][3];
        for (int[] row : costs[i]) {
          for (int c = 0; c < 3; c++) {
            row[c] = random.nextInt(6) - 2;
          }
        }
      }
      return new Instance(
          append(domains(random, n, 0, 2), domain(random, -3, 8)),
          (store, x) -> {
            CostRegular c = new CostRegular(Arrays.copyOf(x, n), delta, 0, 0, finals, costs, x[n]);
            if (decomposition) {
              store.imposeDecomposition(c);
            } else {
              store.impose(c);
            }
          },
          x -> {
            int q = 0;
            int sum = 0;
            for (int i = 0; i < n; i++) {
              sum += costs[i][q][x[i]];
              q = delta[q][x[i]];
              if (q < 0) {
                return false;
              }
            }
            return accepting.contains(q) && sum == x[n];
          },
          "delta="
              + Arrays.deepToString(delta)
              + " accepting="
              + accepting
              + " costs="
              + Arrays.deepToString(costs));
    };
  }

  private static Instance sequence(Random random) {
    int n = 2 + random.nextInt(4);
    int q = 1 + random.nextInt(n);
    int min = random.nextInt(q + 1);
    int max = min + random.nextInt(q + 1 - min);
    int lo = random.nextInt(3);
    int hi = lo + random.nextInt(2);
    return new Instance(
        domains(random, n, 0, 3),
        (store, x) ->
            store.imposeDecomposition(new Sequence(x, new IntervalDomain(lo, hi), q, min, max)),
        x -> {
          for (int i = 0; i + q <= n; i++) {
            int count = 0;
            for (int j = i; j < i + q; j++) {
              if (x[j] >= lo && x[j] <= hi) {
                count++;
              }
            }
            if (count < min || count > max) {
              return false;
            }
          }
          return true;
        },
        "set=" + lo + ".." + hi + " q=" + q + " count=" + min + ".." + max);
  }

  private static Instance lex(Random random) {
    int rows = 2 + random.nextInt(2);
    int n = 1 + random.nextInt(3);
    boolean strict = random.nextBoolean();
    return new Instance(
        domains(random, rows * n, 0, 2),
        (store, x) -> {
          IntVar[][] matrix = new IntVar[rows][];
          for (int i = 0; i < rows; i++) {
            matrix[i] = Arrays.copyOfRange(x, i * n, (i + 1) * n);
          }
          store.imposeDecomposition(new Lex(matrix, strict));
        },
        x -> {
          for (int i = 0; i + 1 < rows; i++) {
            int c =
                Arrays.compare(
                    Arrays.copyOfRange(x, i * n, (i + 1) * n),
                    Arrays.copyOfRange(x, (i + 1) * n, (i + 2) * n));
            if (strict ? c >= 0 : c > 0) {
              return false;
            }
          }
          return true;
        },
        "rows=" + rows + " strict=" + strict);
  }

  private static Instance lexOrder(Random random) {
    int n = 1 + random.nextInt(3);
    int m = 1 + random.nextInt(3);
    boolean strict = random.nextBoolean();
    return new Instance(
        domains(random, n + m, 0, 2),
        (store, x) ->
            store.impose(
                new LexOrder(Arrays.copyOfRange(x, 0, n), Arrays.copyOfRange(x, n, n + m), strict)),
        x -> {
          int c = Arrays.compare(Arrays.copyOfRange(x, 0, n), Arrays.copyOfRange(x, n, n + m));
          return strict ? c < 0 : c <= 0;
        },
        "n=" + n + " strict=" + strict);
  }

  private static Function<Random, Instance> linear(String kind) {
    return random -> {
      int n = 1 + random.nextInt(4);
      int[] weights = new int[n];
      for (int i = 0; i < n; i++) {
        weights[i] = random.nextInt(7) - 3;
      }
      String relation = kind.equals("SumWeight") ? "==" : RELATIONS[random.nextInt(6)];
      int rhs = random.nextInt(9) - 4;
      return new Instance(
          domains(random, n, -2, 2),
          (store, x) ->
              store.impose(
                  switch (kind) {
                    case "LinearInt" -> new LinearInt(x, weights, relation, rhs);
                    case "LinearIntDom" -> new LinearIntDom(x, weights, relation, rhs);
                    default -> new SumWeight(x, weights, rhs);
                  }),
          x -> {
            int sum = 0;
            for (int i = 0; i < n; i++) {
              sum += weights[i] * x[i];
            }
            return holds(sum, relation, rhs);
          },
          "weights=" + Arrays.toString(weights) + " " + relation + " " + rhs);
    };
  }

  private static Function<Random, Instance> table(String kind) {
    return random -> {
      int n = 1 + random.nextInt(4);
      int k = random.nextInt(8);
      int[][] tuples = new int[k][n];
      Set<List<Integer>> tupleSet = new HashSet<>();
      for (int[] tuple : tuples) {
        for (int j = 0; j < n; j++) {
          tuple[j] = random.nextInt(3);
        }
        tupleSet.add(Arrays.stream(tuple).boxed().toList());
      }
      boolean conflict = kind.equals("ExtensionalConflictVa");
      return new Instance(
          domains(random, n, 0, 2),
          (store, x) -> {
            int[][] copy = Arrays.stream(tuples).map(int[]::clone).toArray(int[][]::new);
            store.impose(
                switch (kind) {
                  case "Table" -> new Table(x, copy);
                  case "SimpleTable" -> new SimpleTable(x, copy);
                  case "HybridTable" -> new HybridTable(x, copy, Integer.MIN_VALUE);
                  case "ExtensionalSupportVa" -> new ExtensionalSupportVa(x, copy);
                  case "ExtensionalSupportStr" -> new ExtensionalSupportStr(x, copy);
                  case "ExtensionalSupportMdd" -> new ExtensionalSupportMdd(x, copy);
                  default -> new ExtensionalConflictVa(x, copy);
                });
          },
          x -> tupleSet.contains(Arrays.stream(x).boxed().toList()) != conflict,
          "tuples=" + Arrays.deepToString(tuples));
    };
  }

  private static Function<Random, Instance> cumulative(boolean unary) {
    return random -> {
      int n = 1 + random.nextInt(3);
      List<int[]> domains = new ArrayList<>();
      domains.addAll(Arrays.asList(domains(random, n, 0, 3))); // starts
      domains.addAll(Arrays.asList(domains(random, n, 0, 2))); // durations
      for (int i = 0; i < n; i++) {
        domains.add(unary ? new int[] {1} : domain(random, 0, 2)); // resources
      }
      domains.add(unary ? new int[] {1} : domain(random, 0, 3)); // limit
      return new Instance(
          domains.toArray(int[][]::new),
          (store, x) -> {
            IntVar[] starts = Arrays.copyOfRange(x, 0, n);
            IntVar[] durations = Arrays.copyOfRange(x, n, 2 * n);
            IntVar[] resources = Arrays.copyOfRange(x, 2 * n, 3 * n);
            store.impose(
                unary
                    ? new CumulativeUnary(starts, durations, resources, x[3 * n])
                    : new CumulativeBasic(starts, durations, resources, x[3 * n]));
          },
          x -> {
            // tasks with zero duration or zero resource use do not occupy the resource
            for (int t = 0; t <= 6; t++) {
              int use = 0;
              for (int i = 0; i < n; i++) {
                if (x[i] <= t && t < x[i] + x[n + i]) {
                  use += x[2 * n + i];
                }
              }
              if (use > x[3 * n]) {
                return false;
              }
            }
            return true;
          },
          "");
    };
  }

  private static Function<Random, Instance> alldiff(String kind) {
    return random ->
        new Instance(
            domains(random, 2 + random.nextInt(4), 0, 4),
            (store, x) ->
                store.impose(
                    switch (kind) {
                      case "Alldiff" -> new Alldiff(x);
                      case "Alldifferent" -> new Alldifferent(x);
                      default -> new Alldistinct(x);
                    }),
            GlobalConstraintBruteForceTest::distinct,
            "");
  }

  private static Instance alldifferentExceptZero(Random random) {
    return new Instance(
        domains(random, 2 + random.nextInt(4), 0, 4),
        (store, x) -> store.impose(new AlldifferentExceptZero(x)),
        x -> distinct(Arrays.stream(x).filter(v -> v != 0).toArray()),
        "");
  }

  private static Instance alldifferentExcept(Random random) {
    int[][] domains = domains(random, 2 + random.nextInt(4), 0, 4);
    int except1 = random.nextInt(5);
    int except2 = random.nextInt(5);
    return new Instance(
        domains,
        (store, x) -> {
          IntervalDomain except = new IntervalDomain(except1, except1);
          except.unionAdapt(except2, except2);
          store.impose(new AlldifferentExcept(x, except));
        },
        x -> distinct(Arrays.stream(x).filter(v -> v != except1 && v != except2).toArray()),
        "except={" + except1 + "," + except2 + "}");
  }

  private static Instance allEqual(Random random) {
    return new Instance(
        domains(random, 2 + random.nextInt(3), 0, 3),
        (store, x) -> store.impose(new AllEqual(x)),
        x -> Arrays.stream(x).distinct().count() == 1,
        "");
  }

  private static Instance gcc(Random random) {
    int n = 2 + random.nextInt(3);
    int m = 2 + random.nextInt(2);
    int[][] variables = domains(random, n, 0, m - 1);
    // the union of the variable domains must be exactly the counted values 0..m-1
    variables[0] = IntStream.range(0, m).toArray();
    return new Instance(
        append(variables, domains(random, m, 0, n)),
        (store, x) ->
            store.impose(new GCC(Arrays.copyOfRange(x, 0, n), Arrays.copyOfRange(x, n, n + m))),
        x -> {
          for (int j = 0; j < m; j++) {
            if (occurrences(Arrays.copyOfRange(x, 0, n), j) != x[n + j]) {
              return false;
            }
          }
          return true;
        },
        "");
  }

  private static Instance among(Random random) {
    int n = 1 + random.nextInt(4);
    int[][] domains = append(domains(random, n, 0, 4), domain(random, 0, n));
    int lo = random.nextInt(5);
    int hi = lo + random.nextInt(3);
    return new Instance(
        domains,
        (store, x) ->
            store.impose(new Among(Arrays.copyOfRange(x, 0, n), new IntervalDomain(lo, hi), x[n])),
        x -> IntStream.range(0, n).filter(i -> x[i] >= lo && x[i] <= hi).count() == x[n],
        "set=" + lo + ".." + hi);
  }

  private static Instance count(Random random) {
    int n = 1 + random.nextInt(4);
    int value = random.nextInt(4);
    return new Instance(
        append(domains(random, n, 0, 3), domain(random, 0, n)),
        (store, x) -> store.impose(new Count(Arrays.copyOfRange(x, 0, n), x[n], value)),
        x -> occurrences(Arrays.copyOfRange(x, 0, n), value) == x[n],
        "value=" + value);
  }

  private static Instance countBounds(Random random) {
    int n = 1 + random.nextInt(4);
    int value = random.nextInt(4);
    int lb = random.nextInt(3);
    int ub = lb + random.nextInt(3);
    return new Instance(
        domains(random, n, 0, 3),
        (store, x) -> store.impose(new CountBounds(x, value, lb, ub)),
        x -> {
          int count = occurrences(x, value);
          return count >= lb && count <= ub;
        },
        "value=" + value + " count=" + lb + ".." + ub);
  }

  private static Instance countVar(Random random) {
    int n = 1 + random.nextInt(4);
    return new Instance(
        append(domains(random, n, 0, 3), domain(random, 0, n), domain(random, 0, 3)),
        (store, x) -> store.impose(new CountVar(Arrays.copyOfRange(x, 0, n), x[n], x[n + 1])),
        x -> occurrences(Arrays.copyOfRange(x, 0, n), x[n + 1]) == x[n],
        "");
  }

  private static Instance countValues(Random random) {
    int n = 1 + random.nextInt(4);
    int k = 1 + random.nextInt(3);
    int[] values = new int[k];
    int value = random.nextInt(2);
    for (int j = 0; j < k; j++) {
      value += 1 + random.nextInt(2);
      values[j] = value;
    }
    return new Instance(
        append(domains(random, n, 0, 5), domains(random, k, 0, n)),
        (store, x) ->
            store.impose(
                new CountValues(
                    Arrays.copyOfRange(x, 0, n), Arrays.copyOfRange(x, n, n + k), values)),
        x -> {
          for (int j = 0; j < k; j++) {
            if (occurrences(Arrays.copyOfRange(x, 0, n), values[j]) != x[n + j]) {
              return false;
            }
          }
          return true;
        },
        "values=" + Arrays.toString(values));
  }

  private static Function<Random, Instance> atLeastOrMost(boolean atLeast) {
    return random -> {
      int n = 1 + random.nextInt(4);
      int value = random.nextInt(4);
      int count = random.nextInt(n + 1);
      return new Instance(
          domains(random, n, 0, 3),
          (store, x) ->
              store.impose(atLeast ? new AtLeast(x, count, value) : new AtMost(x, count, value)),
          x -> atLeast ? occurrences(x, value) >= count : occurrences(x, value) <= count,
          "value=" + value + " count=" + count);
    };
  }

  private static Function<Random, Instance> elementInteger(boolean fast) {
    return random -> {
      int n = 1 + random.nextInt(5);
      int offset = random.nextInt(3) - 1;
      int[] list = randomInts(random, n, -2, 3);
      return new Instance(
          new int[][] {domain(random, -1, n + 2), domain(random, -3, 4)},
          (store, x) ->
              store.impose(
                  fast
                      ? new ElementIntegerFast(x[0], list, x[1], offset)
                      : new ElementInteger(x[0], list, x[1], offset)),
          x -> {
            int i = x[0] - offset - 1;
            return i >= 0 && i < n && list[i] == x[1];
          },
          "list=" + Arrays.toString(list) + " offset=" + offset);
    };
  }

  private static Function<Random, Instance> elementVariable(boolean fast) {
    return random -> {
      int n = 1 + random.nextInt(4);
      int offset = random.nextInt(3) - 1;
      int[][] domains =
          append(
              new int[][] {domain(random, -1, n + 2), domain(random, 0, 3)},
              domains(random, n, 0, 3));
      return new Instance(
          domains,
          (store, x) -> {
            IntVar[] list = Arrays.copyOfRange(x, 2, 2 + n);
            store.impose(
                fast
                    ? new ElementVariableFast(x[0], list, x[1], offset)
                    : new ElementVariable(x[0], list, x[1], offset));
          },
          x -> {
            int i = x[0] - offset - 1;
            return i >= 0 && i < n && x[2 + i] == x[1];
          },
          "offset=" + offset);
    };
  }

  private static Function<Random, Instance> circuit(boolean subcircuit) {
    return random -> {
      int n = 1 + random.nextInt(5);
      return new Instance(
          domains(random, n, 0, n + 1),
          (store, x) -> store.impose(subcircuit ? new Subcircuit(x) : new Circuit(x)),
          x -> isCircuit(x, subcircuit),
          "");
    };
  }

  private static Instance stretch(Random random) {
    int n = 2 + random.nextInt(4);
    int[] values = {1, 2};
    int[] min = {1 + random.nextInt(2), 1 + random.nextInt(2)};
    int[] max = {min[0] + random.nextInt(2), min[1] + random.nextInt(2)};
    return new Instance(
        domains(random, n, 1, 2),
        (store, x) -> store.imposeDecomposition(new Stretch(values, min, max, x)),
        x -> {
          int i = 0;
          while (i < n) {
            int j = i;
            while (j < n && x[j] == x[i]) {
              j++;
            }
            int length = j - i;
            if (length < min[x[i] - 1] || length > max[x[i] - 1]) {
              return false;
            }
            i = j;
          }
          return true;
        },
        "min=" + Arrays.toString(min) + " max=" + Arrays.toString(max));
  }

  private static Instance values(Random random) {
    int n = 1 + random.nextInt(4);
    return new Instance(
        append(domains(random, n, 0, 3), domain(random, 0, n + 1)),
        (store, x) -> store.impose(new Values(Arrays.copyOfRange(x, 0, n), x[n])),
        x -> Arrays.stream(x, 0, n).distinct().count() == x[n],
        "");
  }

  private static Instance assignment(Random random) {
    int n = 1 + random.nextInt(4);
    return new Instance(
        domains(random, 2 * n, 0, n + 1),
        (store, x) ->
            store.impose(
                new Assignment(Arrays.copyOfRange(x, 0, n), Arrays.copyOfRange(x, n, 2 * n))),
        x -> {
          // x[0..n) and x[n..2n) are mutually inverse permutations of 0..n-1
          for (int i = 0; i < n; i++) {
            int xi = x[i];
            int di = x[n + i];
            if (xi < 0 || xi >= n || di < 0 || di >= n) {
              return false;
            }
            if (x[n + xi] != i || x[di] != i) {
              return false;
            }
          }
          return true;
        },
        "");
  }

  private static Function<Random, Instance> maxOrMin(boolean max) {
    return random -> {
      int n = 1 + random.nextInt(4);
      return new Instance(
          domains(random, n + 1, 0, 4),
          (store, x) -> {
            IntVar[] list = Arrays.copyOfRange(x, 0, n);
            store.impose(max ? new Max(list, x[n]) : new Min(list, x[n]));
          },
          x -> {
            IntStream list = Arrays.stream(x, 0, n);
            return (max ? list.max() : list.min()).getAsInt() == x[n];
          },
          "");
    };
  }

  private static Function<Random, Instance> argMaxOrMin(boolean max) {
    return random -> {
      int n = 1 + random.nextInt(4);
      return new Instance(
          append(domains(random, n, 0, 3), domain(random, 0, n + 1)),
          (store, x) -> {
            IntVar[] list = Arrays.copyOfRange(x, 0, n);
            store.impose(max ? new ArgMax(list, x[n]) : new ArgMin(list, x[n]));
          },
          x -> {
            // 1-based index of the first maximum (minimum)
            int best = 0;
            for (int i = 1; i < n; i++) {
              if (max ? x[i] > x[best] : x[i] < x[best]) {
                best = i;
              }
            }
            return x[n] == best + 1;
          },
          "");
    };
  }

  private static Function<Random, Instance> monotonic(boolean increasing) {
    return random -> {
      int n = 1 + random.nextInt(4);
      boolean strict = random.nextBoolean();
      return new Instance(
          domains(random, n, 0, 4),
          (store, x) ->
              store.impose(increasing ? new Increasing(x, strict) : new Decreasing(x, strict)),
          x -> {
            for (int i = 0; i + 1 < n; i++) {
              int step = increasing ? x[i + 1] - x[i] : x[i] - x[i + 1];
              if (strict ? step <= 0 : step < 0) {
                return false;
              }
            }
            return true;
          },
          "strict=" + strict);
    };
  }

  private static Instance valuePrecede(Random random) {
    int n = 1 + random.nextInt(5);
    int s = random.nextInt(3);
    int t = random.nextInt(3);
    return new Instance(
        domains(random, n, 0, 2),
        (store, x) -> store.impose(new ValuePrecede(s, t, x)),
        x -> {
          boolean seenS = false;
          for (int v : x) {
            if (v == t && !seenS) {
              return false;
            }
            if (v == s) {
              seenS = true;
            }
          }
          return true;
        },
        "s=" + s + " t=" + t);
  }

  private static Instance seqPrecedeChain(Random random) {
    return new Instance(
        domains(random, 1 + random.nextInt(5), 0, 3),
        (store, x) -> store.impose(new SeqPrecedeChain(x)),
        x -> {
          // each positive value v > 1 is preceded by v - 1
          int maxSeen = 0;
          for (int v : x) {
            if (v > maxSeen + 1) {
              return false;
            }
            maxSeen = Math.max(maxSeen, v);
          }
          return true;
        },
        "");
  }

  private static Instance member(Random random) {
    int n = 1 + random.nextInt(4);
    return new Instance(
        domains(random, n + 1, 0, 4),
        (store, x) -> store.impose(new Member(Arrays.copyOfRange(x, 0, n), x[n])),
        x -> occurrences(Arrays.copyOfRange(x, 0, n), x[n]) > 0,
        "");
  }

  private static Instance distance(Random random) {
    return new Instance(
        new int[][] {domain(random, -3, 3), domain(random, -3, 3), domain(random, -1, 6)},
        (store, x) -> store.impose(new Distance(x[0], x[1], x[2])),
        x -> Math.abs(x[0] - x[1]) == x[2],
        "");
  }

  private static Function<Random, Instance> arithmetic(String kind) {
    // x and y range over bounds[0]..bounds[1], z over bounds[2]..bounds[3]
    int[] bounds =
        switch (kind) {
          case "XmulYeqZ" -> new int[] {-3, 3, -9, 9};
          case "XexpYeqZ" -> new int[] {0, 3, 0, 27};
          default -> new int[] {-6, 6, -6, 6};
        };
    return random ->
        new Instance(
            new int[][] {
              domain(random, bounds[0], bounds[1]),
              domain(random, bounds[0], bounds[1]),
              domain(random, bounds[2], bounds[3])
            },
            (store, x) ->
                store.impose(
                    switch (kind) {
                      case "XmulYeqZ" -> new XmulYeqZ(x[0], x[1], x[2]);
                      case "XdivYeqZ" -> new XdivYeqZ(x[0], x[1], x[2]);
                      case "XmodYeqZ" -> new XmodYeqZ(x[0], x[1], x[2]);
                      default -> new XexpYeqZ(x[0], x[1], x[2]);
                    }),
            x ->
                switch (kind) {
                  case "XmulYeqZ" -> x[0] * x[1] == x[2];
                  case "XdivYeqZ" -> x[1] != 0 && x[0] / x[1] == x[2];
                  case "XmodYeqZ" -> x[1] != 0 && x[0] % x[1] == x[2];
                  default -> Math.pow(x[0], x[1]) == x[2];
                },
            "");
  }

  private static Instance absXeqY(Random random) {
    int[][] domains = {domain(random, -4, 4), domain(random, -2, 4)};
    boolean domainConsistency = random.nextBoolean();
    return new Instance(
        domains,
        (store, x) -> store.impose(new AbsXeqY(x[0], x[1], domainConsistency)),
        x -> Math.abs(x[0]) == x[1],
        "domainConsistency=" + domainConsistency);
  }

  private static Instance sumInt(Random random) {
    int n = 1 + random.nextInt(4);
    String relation = RELATIONS[random.nextInt(6)];
    return new Instance(
        append(domains(random, n, -2, 3), domain(random, -3, 6)),
        (store, x) -> store.impose(new SumInt(Arrays.copyOfRange(x, 0, n), relation, x[n])),
        x -> holds(Arrays.stream(x, 0, n).sum(), relation, x[n]),
        relation);
  }

  private static Instance sumBool(Random random) {
    int n = 1 + random.nextInt(5);
    String relation = RELATIONS[random.nextInt(6)];
    return new Instance(
        append(domains(random, n, 0, 1), domain(random, -1, n + 1)),
        (store, x) -> store.impose(new SumBool(Arrays.copyOfRange(x, 0, n), relation, x[n])),
        x -> holds(Arrays.stream(x, 0, n).sum(), relation, x[n]),
        relation);
  }

  private static Instance binpacking(Random random) {
    int items = 1 + random.nextInt(4);
    int bins = 1 + random.nextInt(3);
    int[] weights = randomInts(random, items, 1, 3);
    return new Instance(
        append(domains(random, items, 0, bins - 1), domains(random, bins, 0, 6)),
        (store, x) ->
            store.impose(
                new Binpacking(
                    Arrays.copyOfRange(x, 0, items),
                    Arrays.copyOfRange(x, items, items + bins),
                    weights.clone(),
                    0)),
        x -> {
          int[] load = new int[bins];
          for (int i = 0; i < items; i++) {
            load[x[i]] += weights[i];
          }
          for (int b = 0; b < bins; b++) {
            if (load[b] != x[items + b]) {
              return false;
            }
          }
          return true;
        },
        "weights=" + Arrays.toString(weights));
  }

  private static Instance knapsack(Random random) {
    int n = 1 + random.nextInt(3);
    int[] weights = randomInts(random, n, 1, 3);
    int[] profits = randomInts(random, n, 1, 3);
    return new Instance(
        append(domains(random, n, 0, 2), domain(random, 0, 10), domain(random, 0, 10)),
        (store, x) -> {
          IntVar[] quantities = Arrays.copyOfRange(x, 0, n);
          store.impose(new Knapsack(profits.clone(), weights.clone(), quantities, x[n], x[n + 1]));
        },
        x -> {
          int weight = 0;
          int profit = 0;
          for (int i = 0; i < n; i++) {
            weight += weights[i] * x[i];
            profit += profits[i] * x[i];
          }
          return weight == x[n] && profit == x[n + 1];
        },
        "weights=" + Arrays.toString(weights) + " profits=" + Arrays.toString(profits));
  }

  private static Function<Random, Instance> rectangles(String kind) {
    return random -> {
      int n = 1 + random.nextInt(3);
      boolean strict = kind.equals("DiffnStrict");
      return new Instance(
          domains(random, 4 * n, 0, 2),
          (store, x) -> {
            IntVar[][] rectangles = new IntVar[n][];
            for (int i = 0; i < n; i++) {
              rectangles[i] = Arrays.copyOfRange(x, 4 * i, 4 * i + 4);
            }
            store.impose(
                switch (kind) {
                  case "Diffn" -> new Diffn(rectangles, false);
                  case "DiffnStrict" -> new Diffn(rectangles, true);
                  case "Nooverlap" -> new Nooverlap(rectangles, false);
                  default -> new Diff2(Arrays.stream(rectangles).map(Arrays::asList).toList());
                });
          },
          x -> {
            // rectangle i is (x[4i], x[4i+1]) with width x[4i+2] and height x[4i+3]; unless
            // strict, a rectangle with zero width or height may overlap anything
            for (int i = 0; i < n; i++) {
              for (int j = i + 1; j < n; j++) {
                int xi = x[4 * i];
                int yi = x[4 * i + 1];
                int wi = x[4 * i + 2];
                int hi = x[4 * i + 3];
                int xj = x[4 * j];
                int yj = x[4 * j + 1];
                int wj = x[4 * j + 2];
                int hj = x[4 * j + 3];
                boolean apart = xi + wi <= xj || xj + wj <= xi || yi + hi <= yj || yj + hj <= yi;
                boolean empty = wi == 0 || hi == 0 || wj == 0 || hj == 0;
                if (!apart && (strict || !empty)) {
                  return false;
                }
              }
            }
            return true;
          },
          "");
    };
  }

  private static boolean holds(int lhs, String relation, int rhs) {
    return switch (relation) {
      case "==" -> lhs == rhs;
      case "!=" -> lhs != rhs;
      case "<" -> lhs < rhs;
      case "<=" -> lhs <= rhs;
      case ">" -> lhs > rhs;
      default -> lhs >= rhs;
    };
  }

  private static boolean distinct(int[] values) {
    return Arrays.stream(values).distinct().count() == values.length;
  }

  private static int occurrences(int[] values, int value) {
    return (int) Arrays.stream(values).filter(v -> v == value).count();
  }

  /** Whether the 1-based successor list x is a single circuit (with self-loops if subcircuit). */
  private static boolean isCircuit(int[] x, boolean subcircuit) {
    int n = x.length;
    int start = -1;
    int inCycle = 0;
    for (int i = 0; i < n; i++) {
      if (x[i] < 1 || x[i] > n) {
        return false;
      }
      if (x[i] != i + 1) {
        inCycle++;
        start = i;
      }
    }
    if (!subcircuit && inCycle != n) {
      return false;
    }
    if (inCycle == 0) {
      return subcircuit;
    }
    int length = 0;
    int current = start;
    boolean[] seen = new boolean[n];
    do {
      if (seen[current]) {
        return false;
      }
      seen[current] = true;
      current = x[current] - 1;
      length++;
    } while (current != start && length <= n);
    return current == start && length == inCycle;
  }

  private static int[] randomInts(Random random, int n, int lo, int hi) {
    int[] values = new int[n];
    for (int i = 0; i < n; i++) {
      values[i] = lo + random.nextInt(hi - lo + 1);
    }
    return values;
  }

  /** The given domains followed by more. */
  private static int[][] append(int[][] domains, int[]... more) {
    int[][] all = Arrays.copyOf(domains, domains.length + more.length);
    System.arraycopy(more, 0, all, domains.length, more.length);
    return all;
  }

  private static int[][] domains(Random random, int n, int lo, int hi) {
    int[][] domains = new int[n][];
    for (int i = 0; i < n; i++) {
      domains[i] = domain(random, lo, hi);
    }
    return domains;
  }

  /** A random non-empty subset of lo..hi, so domains may have holes. */
  private static int[] domain(Random random, int lo, int hi) {
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

  private static void bruteForce(
      Instance instance, int[] values, int index, Set<List<Integer>> solutions) {
    if (index == values.length) {
      if (instance.semantics().test(values)) {
        solutions.add(Arrays.stream(values).boxed().toList());
      }
      return;
    }
    for (int v : instance.domains()[index]) {
      values[index] = v;
      bruteForce(instance, values, index + 1, solutions);
    }
  }

  private static Set<List<Integer>> solveAll(Instance instance, int valueOrder, int seed) {
    Store store = new Store();
    IntVar[] x = new IntVar[instance.domains().length];
    for (int i = 0; i < x.length; i++) {
      IntervalDomain domain = new IntervalDomain();
      for (int v : instance.domains()[i]) {
        domain.unionAdapt(v, v);
      }
      x[i] = new IntVar(store, "x" + i, domain);
    }
    instance.impose().accept(store, x);

    Set<List<Integer>> found = new HashSet<>();
    if (!store.consistency()) {
      return found;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            found.add(Arrays.stream(x).map(IntVar::value).toList());
            return result;
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    Indomain<IntVar> indomain =
        switch (valueOrder) {
          case 0 -> new IndomainMin<>();
          case 1 -> new IndomainMax<>();
          default -> new IndomainRandom<>(seed);
        };
    search.labeling(store, new SimpleSelect<>(x, null, indomain));
    return found;
  }
}
