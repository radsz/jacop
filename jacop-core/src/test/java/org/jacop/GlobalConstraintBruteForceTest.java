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
import java.util.stream.Stream;
import org.jacop.constraints.ExtensionalConflictVa;
import org.jacop.constraints.ExtensionalSupportMdd;
import org.jacop.constraints.ExtensionalSupportStr;
import org.jacop.constraints.ExtensionalSupportVa;
import org.jacop.constraints.Lex;
import org.jacop.constraints.LexOrder;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.Sequence;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.regular.Regular;
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
        Arguments.of(
            "Regular", (Function<Random, Instance>) GlobalConstraintBruteForceTest::regular),
        Arguments.of(
            "Sequence", (Function<Random, Instance>) GlobalConstraintBruteForceTest::sequence),
        Arguments.of("Lex", (Function<Random, Instance>) GlobalConstraintBruteForceTest::lex),
        Arguments.of(
            "LexOrder", (Function<Random, Instance>) GlobalConstraintBruteForceTest::lexOrder),
        Arguments.of("LinearInt", linear("LinearInt")),
        Arguments.of("LinearIntDom", linear("LinearIntDom")),
        Arguments.of("SumWeight", linear("SumWeight")),
        Arguments.of("Table", table("Table")),
        Arguments.of("SimpleTable", table("SimpleTable")),
        Arguments.of("ExtensionalSupportVa", table("ExtensionalSupportVa")),
        Arguments.of("ExtensionalSupportStr", table("ExtensionalSupportStr")),
        Arguments.of("ExtensionalSupportMdd", table("ExtensionalSupportMdd")),
        Arguments.of("ExtensionalConflictVa", table("ExtensionalConflictVa")),
        Arguments.of("CumulativeBasic", cumulative(false)),
        Arguments.of("CumulativeUnary", cumulative(true)));
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
