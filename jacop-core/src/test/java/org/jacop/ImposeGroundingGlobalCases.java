/*
 * ImposeGroundingGlobalCases.java
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

import static org.jacop.ImposeGroundingCases.domain;
import static org.jacop.ImposeGroundingCases.domains;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import org.jacop.ImposeGroundingHarness.Case;
import org.jacop.constraints.AllDifferentLists;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.AmongSeq;
import org.jacop.constraints.CircuitCost;
import org.jacop.constraints.ConditionalSelect;
import org.jacop.constraints.ConjunctionSum;
import org.jacop.constraints.CostAlldifferent;
import org.jacop.constraints.CostGCC;
import org.jacop.constraints.DifferenceCycles;
import org.jacop.constraints.ExactCover;
import org.jacop.constraints.GlobalCardinality;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.MaxCliqueBound;
import org.jacop.constraints.MinOfSums;
import org.jacop.constraints.OrBoolWatched;
import org.jacop.constraints.Routes;
import org.jacop.constraints.Subcircuit;
import org.jacop.constraints.SubcircuitCost;
import org.jacop.constraints.SubcircuitCostPair;
import org.jacop.constraints.SymmetricAlldifferent;
import org.jacop.constraints.TableCover;
import org.jacop.constraints.WeightedSubcircuits;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XorSystem;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.HornFlow;
import org.jacop.constraints.cumulative.MultiCumulative;
import org.jacop.constraints.cumulative.UnaryTransition;
import org.jacop.constraints.regular.MultiCostRegular;
import org.jacop.constraints.table.BinaryBitTable;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.junit.jupiter.params.provider.Arguments;

/**
 * Instance generators for {@link ImposeGroundingTest} for the globals that had no generator in
 * {@link GlobalConstraintBruteForceTest} or {@link ImposeGroundingCases}. A constraint that is
 * documented as redundant or as a relaxation (a bound, a feasibility check) is imposed next to a
 * model of its relation, so the solutions it must keep are those of the model.
 */
final class ImposeGroundingGlobalCases {

  /** Largest number of assignments of an instance; larger ones get random variables fixed. */
  private static final long MAX_ASSIGNMENTS = 20_000;

  private ImposeGroundingGlobalCases() {}

  static Stream<Arguments> cases() {
    return Stream.of(
        Arguments.of("GlobalCardinalityCounters", gen(r -> globalCardinality(r, true))),
        Arguments.of("GlobalCardinalityBounds", gen(r -> globalCardinality(r, false))),
        Arguments.of("CostGCC", gen(ImposeGroundingGlobalCases::costGcc)),
        Arguments.of("CostAlldifferent", gen(ImposeGroundingGlobalCases::costAlldifferent)),
        Arguments.of("AmongSeq", gen(ImposeGroundingGlobalCases::amongSeq)),
        Arguments.of("ExactCover", gen(ImposeGroundingGlobalCases::exactCover)),
        Arguments.of("XorSystem", gen(ImposeGroundingGlobalCases::xorSystem)),
        Arguments.of("ConditionalSelect", gen(ImposeGroundingGlobalCases::conditionalSelect)),
        Arguments.of("ConjunctionSum", gen(ImposeGroundingGlobalCases::conjunctionSum)),
        Arguments.of("MinOfSums", gen(ImposeGroundingGlobalCases::minOfSums)),
        Arguments.of("SymmetricAlldifferentDomain", gen(r -> symmetricAlldifferent(r, true))),
        Arguments.of("SymmetricAlldifferentBounds", gen(r -> symmetricAlldifferent(r, false))),
        Arguments.of("AllDifferentLists", gen(ImposeGroundingGlobalCases::allDifferentLists)),
        Arguments.of("OrBoolWatched", gen(ImposeGroundingGlobalCases::orBoolWatched)),
        Arguments.of("BinaryBitTable", gen(ImposeGroundingGlobalCases::binaryBitTable)),
        Arguments.of("TableCover", gen(ImposeGroundingGlobalCases::tableCover)),
        Arguments.of("MultiCumulative", gen(ImposeGroundingGlobalCases::multiCumulative)),
        Arguments.of("MaxCliqueBound", gen(ImposeGroundingGlobalCases::maxCliqueBound)),
        Arguments.of("CircuitCost", gen(r -> circuitCost(r, false))),
        Arguments.of("SubcircuitCost", gen(r -> circuitCost(r, true))),
        Arguments.of("SubcircuitCostPair", gen(ImposeGroundingGlobalCases::subcircuitCostPair)),
        Arguments.of("WeightedSubcircuits", gen(ImposeGroundingGlobalCases::weightedSubcircuits)),
        Arguments.of("Routes", gen(ImposeGroundingGlobalCases::routes)),
        Arguments.of("DifferenceCycles", gen(ImposeGroundingGlobalCases::differenceCycles)),
        Arguments.of("HornFlow", gen(ImposeGroundingGlobalCases::hornFlow)),
        Arguments.of("UnaryTransition", gen(r -> unaryTransition(r, false))),
        Arguments.of("UnaryTransitionOptional", gen(r -> unaryTransition(r, true))),
        Arguments.of("MultiCostRegular", gen(ImposeGroundingGlobalCases::multiCostRegular)));
  }

  /** The generator with large instances made small by fixing random variables. */
  private static Function<Random, Case> gen(Function<Random, Case> generator) {
    return random -> {
      Case c = generator.apply(random);
      int[][] d = c.domains();
      long size = 1;
      for (int[] values : d) {
        size *= values.length;
      }
      while (size > MAX_ASSIGNMENTS) {
        int v = random.nextInt(d.length);
        if (d[v].length > 1) {
          size /= d[v].length;
          d[v] = new int[] {d[v][random.nextInt(d[v].length)]};
        }
      }
      return c;
    };
  }

  private static int count(int[] t, int from, int to, int value) {
    int k = 0;
    for (int i = from; i < to; i++) {
      if (t[i] == value) {
        k++;
      }
    }
    return k;
  }

  private static boolean distinct(int[] t, int from, int to) {
    Set<Integer> seen = new HashSet<>();
    for (int i = from; i < to; i++) {
      if (!seen.add(t[i])) {
        return false;
      }
    }
    return true;
  }

  private static int[] ints(Random random, int n, int lo, int hi) {
    int[] values = new int[n];
    for (int i = 0; i < n; i++) {
      values[i] = lo + random.nextInt(hi - lo + 1);
    }
    return values;
  }

  private static int[][] matrix(Random random, int n, int m, int lo, int hi) {
    int[][] values = new int[n][];
    for (int i = 0; i < n; i++) {
      values[i] = ints(random, m, lo, hi);
    }
    return values;
  }

  private static int[][] concat(int[][]... parts) {
    return Arrays.stream(parts).flatMap(Arrays::stream).toArray(int[][]::new);
  }

  /** GlobalCardinality over list 0..n-1 with counters n.. (or fixed bounds). */
  private static Case globalCardinality(Random random, boolean counters) {
    int n = 2 + random.nextInt(3);
    int[][] list = domains(random, n, 0, 3);
    List<Integer> pool = new ArrayList<>(List.of(0, 1, 2, 3));
    Collections.shuffle(pool, random);
    int k = 1 + random.nextInt(3);
    int[] values = pool.subList(0, k).stream().mapToInt(Integer::intValue).sorted().toArray();
    if (counters) {
      int[][] d = concat(list, domains(random, k, 0, n));
      return Case.of(
          d,
          (store, x) ->
              store.impose(
                  new GlobalCardinality(
                      Arrays.copyOf(x, n), values, Arrays.copyOfRange(x, n, n + k))),
          t -> {
            for (int j = 0; j < k; j++) {
              if (count(t, 0, n, values[j]) != t[n + j]) {
                return false;
              }
            }
            return true;
          },
          "values=" + Arrays.toString(values));
    }
    int[] low = new int[k];
    int[] up = new int[k];
    for (int j = 0; j < k; j++) {
      low[j] = random.nextInt(2);
      up[j] = low[j] + random.nextInt(n);
    }
    return Case.of(
        list,
        (store, x) -> store.impose(new GlobalCardinality(x, values, low, up)),
        t -> {
          for (int j = 0; j < k; j++) {
            int c = count(t, 0, n, values[j]);
            if (c < low[j] || c > up[j]) {
              return false;
            }
          }
          return true;
        },
        "values="
            + Arrays.toString(values)
            + " low="
            + Arrays.toString(low)
            + " up="
            + Arrays.toString(up));
  }

  /** CostGCC: list 0..n-1, counters n..n+m-1, cost last. */
  private static Case costGcc(Random random) {
    int n = 2 + random.nextInt(2);
    int m = 2 + random.nextInt(2);
    int offset = random.nextInt(3) - 1;
    int[][] costs = matrix(random, n, m, 0, 4);
    int[][] d =
        concat(
            domains(random, n, offset, offset + m - 1),
            domains(random, m, 0, n),
            new int[][] {domain(random, 0, 4 * n)});
    return Case.of(
        d,
        (store, x) ->
            store.impose(
                new CostGCC(
                    Arrays.copyOf(x, n), costs, Arrays.copyOfRange(x, n, n + m), x[n + m], offset)),
        t -> {
          int c = 0;
          for (int i = 0; i < n; i++) {
            c += costs[i][t[i] - offset];
          }
          for (int j = 0; j < m; j++) {
            if (count(t, 0, n, offset + j) != t[n + j]) {
              return false;
            }
          }
          return c == t[n + m];
        },
        "offset=" + offset + " costs=" + Arrays.deepToString(costs));
  }

  /** CostAlldifferent: list 0..n-1, cost last. */
  private static Case costAlldifferent(Random random) {
    int n = 2 + random.nextInt(3);
    int m = n + random.nextInt(2);
    int offset = random.nextInt(3) - 1;
    int[][] costs = matrix(random, n, m, 0, 4);
    int[][] d =
        concat(domains(random, n, offset, offset + m - 1), new int[][] {domain(random, 0, 4 * n)});
    return Case.of(
        d,
        (store, x) -> store.impose(new CostAlldifferent(Arrays.copyOf(x, n), costs, x[n], offset)),
        t -> {
          int c = 0;
          for (int i = 0; i < n; i++) {
            c += costs[i][t[i] - offset];
          }
          return distinct(t, 0, n) && c == t[n];
        },
        "offset=" + offset + " costs=" + Arrays.deepToString(costs));
  }

  private static Case amongSeq(Random random) {
    int n = 3 + random.nextInt(4);
    int q = 1 + random.nextInt(n);
    int min = random.nextInt(q + 1);
    int max = min + random.nextInt(q + 1 - min);
    IntervalDomain values = new IntervalDomain();
    for (int v = 0; v <= 2; v++) {
      if (random.nextBoolean()) {
        values.unionAdapt(v, v);
      }
    }
    if (values.isEmpty()) {
      values.unionAdapt(1, 1);
    }
    return Case.of(
        domains(random, n, 0, 2),
        (store, x) -> store.impose(new AmongSeq(x, values, q, min, max)),
        t -> {
          for (int s = 0; s + q <= n; s++) {
            int c = 0;
            for (int i = s; i < s + q; i++) {
              if (values.contains(t[i])) {
                c++;
              }
            }
            if (c < min || c > max) {
              return false;
            }
          }
          return true;
        },
        "set=" + values + " q=" + q + " min=" + min + " max=" + max);
  }

  private static Case exactCover(Random random) {
    int options = 3 + random.nextInt(5);
    int elements = 2 + random.nextInt(3);
    int[][] sets = new int[options][];
    for (int o = 0; o < options; o++) {
      List<Integer> s = new ArrayList<>();
      for (int e = 0; e < elements; e++) {
        if (random.nextInt(3) == 0) {
          s.add(e);
        }
      }
      if (s.isEmpty()) {
        s.add(random.nextInt(elements));
      }
      sets[o] = s.stream().mapToInt(Integer::intValue).toArray();
    }
    return Case.of(
        domains(random, options, 0, 1),
        (store, x) -> store.impose(new ExactCover(x, sets, elements)),
        t -> {
          int[] covered = new int[elements];
          for (int o = 0; o < options; o++) {
            if (t[o] == 1) {
              for (int e : sets[o]) {
                covered[e]++;
              }
            }
          }
          return Arrays.stream(covered).allMatch(c -> c == 1);
        },
        "n=" + elements + " sets=" + Arrays.deepToString(sets));
  }

  private static Case xorSystem(Random random) {
    int n = 3 + random.nextInt(4);
    int rows = 1 + random.nextInt(3);
    int[][] rowIndex = new int[rows][];
    int[] parities = ints(random, rows, 0, 1);
    for (int r = 0; r < rows; r++) {
      int len = 1 + random.nextInt(n);
      rowIndex[r] = ints(random, len, 0, n - 1);
    }
    return Case.of(
        domains(random, n, 0, 1),
        (store, x) -> {
          IntVar[][] vars = new IntVar[rows][];
          for (int r = 0; r < rows; r++) {
            vars[r] = Arrays.stream(rowIndex[r]).mapToObj(i -> x[i]).toArray(IntVar[]::new);
          }
          store.impose(new XorSystem(vars, parities));
        },
        t -> {
          for (int r = 0; r < rows; r++) {
            int p = 0;
            for (int i : rowIndex[r]) {
              p ^= t[i];
            }
            if (p != parities[r]) {
              return false;
            }
          }
          return true;
        },
        "rows=" + Arrays.deepToString(rowIndex) + " parities=" + Arrays.toString(parities));
  }

  /** ConditionalSelect: b 0..k-1, x k..2k-1, y last. */
  private static Case conditionalSelect(Random random) {
    int k = 1 + random.nextInt(3);
    int[][] d =
        concat(domains(random, k, 0, 1), domains(random, k, 0, 3), domains(random, 1, 0, 3));
    return Case.of(
        d,
        (store, x) ->
            store.impose(
                new ConditionalSelect(
                    Arrays.copyOf(x, k), Arrays.copyOfRange(x, k, 2 * k), x[2 * k])),
        t -> {
          for (int i = 0; i < k; i++) {
            if (t[i] == 1) {
              return t[k + i] == t[2 * k];
            }
          }
          return false;
        },
        "k=" + k);
  }

  /** ConjunctionSum: variables 0..n-1, sum last. */
  private static Case conjunctionSum(Random random) {
    int n = 2 + random.nextInt(2);
    int terms = 1 + random.nextInt(3);
    int[][] termIndex = new int[terms][];
    int[][] termValues = new int[terms][];
    boolean[][] termEq = new boolean[terms][];
    int[] weights = ints(random, terms, 0, 3);
    for (int t = 0; t < terms; t++) {
      int len = 1 + random.nextInt(Math.min(2, n));
      List<Integer> pool = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        pool.add(i);
      }
      Collections.shuffle(pool, random);
      termIndex[t] = pool.subList(0, len).stream().mapToInt(Integer::intValue).toArray();
      termValues[t] = ints(random, len, 0, 2);
      termEq[t] = new boolean[len];
      for (int j = 0; j < len; j++) {
        termEq[t][j] = random.nextInt(3) != 0;
      }
    }
    int[][] d = concat(domains(random, n, 0, 2), new int[][] {domain(random, -1, 7)});
    return Case.of(
        d,
        (store, x) -> {
          IntVar[][] vars = new IntVar[terms][];
          for (int t = 0; t < terms; t++) {
            vars[t] = Arrays.stream(termIndex[t]).mapToObj(i -> x[i]).toArray(IntVar[]::new);
          }
          store.impose(new ConjunctionSum(vars, termValues, termEq, weights, x[n]));
        },
        v -> {
          int s = 0;
          for (int t = 0; t < terms; t++) {
            boolean holds = true;
            for (int j = 0; j < termIndex[t].length; j++) {
              holds &= (v[termIndex[t][j]] == termValues[t][j]) == termEq[t][j];
            }
            if (holds) {
              s += weights[t];
            }
          }
          return v[n] >= s;
        },
        "vars="
            + Arrays.deepToString(termIndex)
            + " values="
            + Arrays.deepToString(termValues)
            + " eq="
            + Arrays.deepToString(termEq)
            + " weights="
            + Arrays.toString(weights));
  }

  /** MinOfSums: x 0..k-1, y k..2k-1 (unused where null), m last. */
  private static Case minOfSums(Random random) {
    int k = 1 + random.nextInt(3);
    boolean[] single = new boolean[k];
    for (int i = 0; i < k; i++) {
      single[i] = random.nextInt(3) == 0;
    }
    int[][] d = concat(domains(random, 2 * k, -2, 3), new int[][] {domain(random, -4, 6)});
    for (int i = 0; i < k; i++) {
      if (single[i]) {
        d[k + i] = new int[] {0};
      }
    }
    return Case.of(
        d,
        (store, x) -> {
          IntVar[] y = new IntVar[k];
          for (int i = 0; i < k; i++) {
            y[i] = single[i] ? null : x[k + i];
          }
          store.impose(new MinOfSums(Arrays.copyOf(x, k), y, x[2 * k]));
        },
        t -> {
          int m = Integer.MAX_VALUE;
          for (int i = 0; i < k; i++) {
            m = Math.min(m, t[i] + (single[i] ? 0 : t[k + i]));
          }
          return m == t[2 * k];
        },
        "single=" + Arrays.toString(single));
  }

  private static Case symmetricAlldifferent(Random random, boolean domainConsistent) {
    int n = 2 + random.nextInt(4);
    int offset = random.nextInt(2);
    return Case.of(
        domains(random, n, offset, offset + n - 1),
        (store, x) -> store.impose(new SymmetricAlldifferent(x, offset, domainConsistent)),
        t -> {
          for (int i = 0; i < n; i++) {
            int j = t[i] - offset;
            if (j < 0 || j >= n || t[j] != i + offset) {
              return false;
            }
          }
          return true;
        },
        "offset=" + offset);
  }

  private static Case allDifferentLists(Random random) {
    int rows = 2 + random.nextInt(2);
    int len = 1 + random.nextInt(2);
    int[][] except = random.nextBoolean() ? new int[0][] : new int[][] {ints(random, len, 0, 2)};
    return Case.of(
        domains(random, rows * len, 0, 2),
        (store, x) -> {
          IntVar[][] lists = new IntVar[rows][];
          for (int r = 0; r < rows; r++) {
            lists[r] = Arrays.copyOfRange(x, r * len, (r + 1) * len);
          }
          store.impose(new AllDifferentLists(lists, except));
        },
        t -> {
          Set<List<Integer>> seen = new HashSet<>();
          for (int r = 0; r < rows; r++) {
            List<Integer> row =
                Arrays.stream(Arrays.copyOfRange(t, r * len, (r + 1) * len)).boxed().toList();
            boolean excepted =
                Arrays.stream(except).anyMatch(e -> Arrays.stream(e).boxed().toList().equals(row));
            if (!excepted && !seen.add(row)) {
              return false;
            }
          }
          return true;
        },
        "rows=" + rows + " except=" + Arrays.deepToString(except));
  }

  private static Case orBoolWatched(Random random) {
    int n = 1 + random.nextInt(4);
    boolean negated = random.nextBoolean();
    return Case.of(
        domains(random, n + 1, 0, 1),
        (store, x) -> store.impose(new OrBoolWatched(Arrays.copyOf(x, n), x[n], negated)),
        t -> {
          boolean or = false;
          for (int i = 0; i < n; i++) {
            or |= t[i] == 1;
          }
          return (t[n] == 1) == (or != negated);
        },
        "negated=" + negated);
  }

  private static Case binaryBitTable(Random random) {
    List<int[]> tuples = new ArrayList<>();
    for (int a = 0; a <= 4; a++) {
      for (int b = 0; b <= 4; b++) {
        if (random.nextInt(3) == 0) {
          tuples.add(new int[] {a, b});
        }
      }
    }
    int[][] table = tuples.toArray(new int[0][]);
    return Case.of(
        domains(random, 2, 0, 4),
        (store, x) -> store.impose(new BinaryBitTable(x[0], x[1], table)),
        t -> tuples.stream().anyMatch(u -> u[0] == t[0] && u[1] == t[1]),
        "tuples=" + Arrays.deepToString(table));
  }

  /**
   * TableCover as the FlatZinc detector posts it: exact only when the union of the domains has as
   * many values as there are variables (the all different then takes all of them), with holes in
   * the range of the values.
   */
  private static Case tableCover(Random random) {
    int groups = 2 + random.nextInt(2);
    int size = 1 + random.nextInt(2);
    int n = groups * size;
    int range = n + 1 + random.nextInt(2);
    boolean exact = random.nextBoolean();
    int[][] d;
    if (exact) {
      List<Integer> pool = new ArrayList<>();
      for (int v = 0; v < range; v++) {
        pool.add(v);
      }
      Collections.shuffle(pool, random);
      List<Integer> union = new ArrayList<>(pool.subList(0, n));
      d = new int[n][];
      List<Set<Integer>> sets = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        Set<Integer> set = new HashSet<>();
        for (int v : union) {
          if (random.nextInt(3) != 0) {
            set.add(v);
          }
        }
        sets.add(set);
      }
      for (int v : union) {
        sets.get(random.nextInt(n)).add(v);
      }
      for (int i = 0; i < n; i++) {
        if (sets.get(i).isEmpty()) {
          sets.get(i).add(union.get(0));
        }
        d[i] = sets.get(i).stream().mapToInt(Integer::intValue).sorted().toArray();
      }
    } else {
      d = domains(random, n, 0, range - 1);
    }
    int[][][] tuples = new int[groups][][];
    for (int g = 0; g < groups; g++) {
      int count = 1 + random.nextInt(4);
      tuples[g] = new int[count][];
      for (int r = 0; r < count; r++) {
        tuples[g][r] = ints(random, size, 0, range - 1);
      }
    }
    return Case.of(
        d,
        (store, x) -> {
          IntVar[][] vars = new IntVar[groups][];
          for (int g = 0; g < groups; g++) {
            vars[g] = Arrays.copyOfRange(x, g * size, (g + 1) * size);
          }
          store.impose(new TableCover(vars, tuples, exact));
        },
        t -> {
          if (!distinct(t, 0, n)) {
            return false;
          }
          for (int g = 0; g < groups; g++) {
            int[] row = Arrays.copyOfRange(t, g * size, (g + 1) * size);
            if (Arrays.stream(tuples[g]).noneMatch(u -> Arrays.equals(u, row))) {
              return false;
            }
          }
          return true;
        },
        "exact=" + exact + " tuples=" + Arrays.deepToString(tuples));
  }

  /** Whether the tasks fit the limit at every time point. */
  private static boolean fits(int[] start, int[] dur, int[] use, int limit) {
    for (int i = 0; i < start.length; i++) {
      if (dur[i] > 0 && use[i] > 0) {
        int load = 0;
        for (int j = 0; j < start.length; j++) {
          if (dur[j] > 0 && start[j] <= start[i] && start[i] < start[j] + dur[j]) {
            load += use[j];
          }
        }
        if (load > limit) {
          return false;
        }
      }
    }
    return true;
  }

  /** MultiCumulative: starts 0..n-1, limits n..n+r-1. */
  private static Case multiCumulative(Random random) {
    int n = 2 + random.nextInt(2);
    int r = 1 + random.nextInt(2);
    int[] durations = ints(random, n, 0, 3);
    int[][] heights = matrix(random, r, n, 0, 2);
    int[][] d = concat(domains(random, n, 0, 4), domains(random, r, 0, 3));
    return Case.of(
        d,
        (store, x) ->
            store.impose(
                new MultiCumulative(
                    Arrays.copyOf(x, n), durations, heights, Arrays.copyOfRange(x, n, n + r))),
        t -> {
          int[] s = Arrays.copyOf(t, n);
          for (int k = 0; k < r; k++) {
            if (!fits(s, durations, heights[k], t[n + k])) {
              return false;
            }
          }
          return true;
        },
        "durations=" + Arrays.toString(durations) + " heights=" + Arrays.deepToString(heights));
  }

  /** MaxCliqueBound: x 0..n-1, sum last. */
  private static Case maxCliqueBound(Random random) {
    int n = 2 + random.nextInt(4);
    boolean[][] conflict = new boolean[n][n];
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        conflict[i][j] = conflict[j][i] = random.nextInt(2) == 0;
      }
    }
    int[][] conflicts = new int[n][];
    for (int i = 0; i < n; i++) {
      List<Integer> c = new ArrayList<>();
      for (int j = 0; j < n; j++) {
        if (conflict[i][j]) {
          c.add(j);
        }
      }
      conflicts[i] = c.stream().mapToInt(Integer::intValue).toArray();
    }
    int[][] d = concat(domains(random, n, 0, 1), new int[][] {domain(random, 0, n)});
    return Case.of(
        d,
        (store, x) -> store.impose(new MaxCliqueBound(Arrays.copyOf(x, n), conflicts, x[n])),
        t -> {
          int ones = 0;
          for (int i = 0; i < n; i++) {
            ones += t[i];
            for (int j : conflicts[i]) {
              if (t[i] == 1 && t[j] == 1) {
                return false;
              }
            }
          }
          return t[n] <= ones;
        },
        "conflicts=" + Arrays.deepToString(conflicts));
  }

  /** Whether successors t[0..n-1] (from offset) are a circuit, or a subcircuit. */
  private static boolean circuit(int[] t, int n, int offset, boolean sub) {
    int inCycle = 0;
    int start = -1;
    for (int i = 0; i < n; i++) {
      int j = t[i] - offset;
      if (j < 0 || j >= n) {
        return false;
      }
      if (j != i) {
        inCycle++;
        start = i;
      }
    }
    if (inCycle == 0) {
      return sub;
    }
    if (!sub && inCycle != n) {
      return false;
    }
    int length = 0;
    int current = start;
    boolean[] seen = new boolean[n];
    do {
      if (seen[current]) {
        return false;
      }
      seen[current] = true;
      current = t[current] - offset;
      length++;
    } while (current != start);
    return length == inCycle;
  }

  private static int arcSum(int[] t, int n, int offset, int[][] costs) {
    int c = 0;
    for (int i = 0; i < n; i++) {
      c += costs[i][t[i] - offset];
    }
    return c;
  }

  /** CircuitCost or SubcircuitCost: list 0..n-1, cost last. */
  private static Case circuitCost(Random random, boolean sub) {
    int n = 2 + random.nextInt(3);
    int offset = random.nextInt(2);
    int[][] costs = matrix(random, n, n, 0, 4);
    if (random.nextBoolean()) {
      for (int i = 0; i < n; i++) {
        for (int j = 0; j < i; j++) {
          costs[i][j] = costs[j][i];
        }
      }
    }
    int[][] d =
        concat(domains(random, n, offset, offset + n - 1), new int[][] {domain(random, 0, 4 * n)});
    return Case.of(
        d,
        (store, x) -> {
          IntVar[] list = Arrays.copyOf(x, n);
          store.impose(
              sub
                  ? new SubcircuitCost(list, costs, x[n], offset)
                  : new CircuitCost(list, costs, x[n], offset));
        },
        t -> circuit(t, n, offset, sub) && arcSum(t, n, offset, costs) == t[n],
        "offset=" + offset + " costs=" + Arrays.deepToString(costs));
  }

  /** SubcircuitCostPair next to Subcircuit: list 0..n-1, cost1, cost2. */
  private static Case subcircuitCostPair(Random random) {
    int n = 2 + random.nextInt(3);
    int[][] costs1 = matrix(random, n, n, 0, 3);
    int[][] costs2 = matrix(random, n, n, 0, 3);
    int[][] d =
        concat(
            domains(random, n, 1, n),
            new int[][] {domain(random, 0, 3 * n), domain(random, 0, 3 * n)});
    return Case.of(
        d,
        (store, x) -> {
          IntVar[] list = Arrays.copyOf(x, n);
          store.impose(new Subcircuit(list));
          store.impose(new SubcircuitCostPair(list, costs1, x[n], costs2, x[n + 1], 1));
          store.impose(new SubcircuitCost(list, costs1, x[n], 1));
          store.impose(new SubcircuitCost(list, costs2, x[n + 1], 1));
        },
        t ->
            circuit(t, n, 1, true)
                && arcSum(t, n, 1, costs1) == t[n]
                && arcSum(t, n, 1, costs2) == t[n + 1],
        "costs1=" + Arrays.deepToString(costs1) + " costs2=" + Arrays.deepToString(costs2));
  }

  /** WeightedSubcircuits next to Alldistinct: list, tour, tourCost, cost. */
  private static Case weightedSubcircuits(Random random) {
    int n = 2 + random.nextInt(2);
    int k = 1 + random.nextInt(2);
    int[][] costs = matrix(random, n, n, 0, 3);
    int[][] d =
        concat(
            domains(random, n, 1, n),
            domains(random, n, 0, k),
            domains(random, k, 0, 3 * n),
            new int[][] {domain(random, 0, 3 * n)});
    return Case.of(
        d,
        (store, x) -> {
          IntVar[] list = Arrays.copyOf(x, n);
          store.impose(new Alldistinct(list));
          store.impose(
              new WeightedSubcircuits(
                  list,
                  Arrays.copyOfRange(x, n, 2 * n),
                  costs,
                  Arrays.copyOfRange(x, 2 * n, 2 * n + k),
                  x[2 * n + k]));
        },
        t -> {
          int[] tourCost = new int[k + 1];
          boolean[] seen = new boolean[n];
          for (int i = 0; i < n; i++) {
            int next = t[i] - 1;
            int tour = t[n + i];
            if ((next == i) != (tour == 0) || t[n + next] != tour) {
              return false;
            }
            tourCost[tour] += costs[i][next];
          }
          // every tour is one circuit
          for (int i = 0; i < n; i++) {
            if (t[n + i] != 0 && !seen[i]) {
              int tour = t[n + i];
              int c = i;
              int len = 0;
              do {
                if (seen[c]) {
                  return false;
                }
                seen[c] = true;
                c = t[c] - 1;
                len++;
              } while (c != i && len <= n);
              for (int j = 0; j < n; j++) {
                if (t[n + j] == tour && !seen[j]) {
                  return false;
                }
              }
            }
          }
          int total = 0;
          for (int tour = 0; tour <= k; tour++) {
            total += tourCost[tour];
            if (tour > 0 && tourCost[tour] != t[2 * n + tour - 1]) {
              return false;
            }
          }
          return distinct(t, 0, n) && total == t[2 * n + k];
        },
        "k=" + k + " costs=" + Arrays.deepToString(costs));
  }

  private static Case routes(Random random) {
    int n = 2 + random.nextInt(3);
    List<int[]> arcs = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (i != j && random.nextInt(3) != 0) {
          arcs.add(new int[] {i, j});
        }
      }
      if (i > 0 && random.nextInt(3) == 0) {
        arcs.add(new int[] {i, i});
      }
    }
    if (arcs.isEmpty()) {
      arcs.add(new int[] {0, 1});
    }
    int m = Math.min(arcs.size(), 12);
    Collections.shuffle(arcs, random);
    List<int[]> used = arcs.subList(0, m);
    int[] tails = used.stream().mapToInt(a -> a[0]).toArray();
    int[] heads = used.stream().mapToInt(a -> a[1]).toArray();
    int nodes =
        1 + Math.max(Arrays.stream(tails).max().orElse(0), Arrays.stream(heads).max().orElse(0));
    boolean capacitated = random.nextBoolean();
    int[] demands = capacitated ? ints(random, nodes, 0, 2) : null;
    int capacity = 1 + random.nextInt(3);
    return Case.of(
        domains(random, m, 0, 1),
        (store, x) ->
            store.impose(
                capacitated
                    ? new Routes(tails, heads, x, demands, capacity)
                    : new Routes(tails, heads, x)),
        t -> {
          int[] next = new int[nodes];
          Arrays.fill(next, -1);
          int[] out = new int[nodes];
          int[] in = new int[nodes];
          boolean[] self = new boolean[nodes];
          List<Integer> depotOut = new ArrayList<>();
          for (int a = 0; a < m; a++) {
            if (t[a] == 1) {
              if (tails[a] == heads[a]) {
                self[tails[a]] = true;
              } else {
                out[tails[a]]++;
                in[heads[a]]++;
                next[tails[a]] = heads[a];
                if (tails[a] == 0) {
                  depotOut.add(heads[a]);
                }
              }
            }
          }
          for (int v = 1; v < nodes; v++) {
            boolean visited = out[v] == 1 && in[v] == 1 && !self[v];
            boolean skipped = out[v] == 0 && in[v] == 0 && self[v];
            if (!visited && !skipped) {
              return false;
            }
          }
          // every visited node lies on a route from the depot
          boolean[] onRoute = new boolean[nodes];
          for (int first : depotOut) {
            int load = 0;
            int v = first;
            int steps = 0;
            while (v != 0 && steps <= nodes) {
              onRoute[v] = true;
              load += capacitated ? demands[v] : 0;
              v = next[v];
              steps++;
            }
            if (v != 0 || capacitated && load > capacity) {
              return false;
            }
          }
          for (int v = 1; v < nodes; v++) {
            if (!self[v] && !onRoute[v]) {
              return false;
            }
          }
          return true;
        },
        "tails="
            + Arrays.toString(tails)
            + " heads="
            + Arrays.toString(heads)
            + (capacitated
                ? " demands=" + Arrays.toString(demands) + " capacity=" + capacity
                : ""));
  }

  /** DifferenceCycles next to its difference constraints: variables, then the 0/1 conditions. */
  private static Case differenceCycles(Random random) {
    int n = 2 + random.nextInt(3);
    int m = 2 + random.nextInt(4);
    int[] xi = ints(random, m, 0, n - 1);
    int[] yi = new int[m];
    for (int a = 0; a < m; a++) {
      yi[a] = (xi[a] + 1 + random.nextInt(n - 1)) % n;
    }
    int[] c = ints(random, m, -2, 2);
    boolean[] conditional = new boolean[m];
    int[] v = ints(random, m, 0, 1);
    int conditions = 0;
    int[] condIndex = new int[m];
    for (int a = 0; a < m; a++) {
      conditional[a] = random.nextBoolean();
      condIndex[a] = conditional[a] ? n + conditions++ : -1;
    }
    int[][] d = concat(domains(random, n, 0, 3), domains(random, conditions, 0, 1));
    return Case.of(
        d,
        (store, x) -> {
          IntVar[] xs = new IntVar[m];
          IntVar[] ys = new IntVar[m];
          IntVar[] bs = new IntVar[m];
          for (int a = 0; a < m; a++) {
            xs[a] = x[xi[a]];
            ys[a] = x[yi[a]];
            // x - y <= c
            XplusClteqZ diff = new XplusClteqZ(xs[a], -c[a], ys[a]);
            if (conditional[a]) {
              bs[a] = x[condIndex[a]];
              store.impose(new IfThen(new XeqC(bs[a], v[a]), diff));
            } else {
              store.impose(diff);
            }
          }
          store.impose(new DifferenceCycles(xs, ys, c, bs, v));
        },
        t -> {
          for (int a = 0; a < m; a++) {
            boolean active = !conditional[a] || t[condIndex[a]] == v[a];
            if (active && t[xi[a]] - t[yi[a]] > c[a]) {
              return false;
            }
          }
          return true;
        },
        "x="
            + Arrays.toString(xi)
            + " y="
            + Arrays.toString(yi)
            + " c="
            + Arrays.toString(c)
            + " conditional="
            + Arrays.toString(conditional)
            + " v="
            + Arrays.toString(v));
  }

  /** HornFlow next to CumulativeBasic: starts, durations, resources, limit. */
  private static Case hornFlow(Random random) {
    int n = 2 + random.nextInt(2);
    int[][] d =
        concat(
            domains(random, n, 0, 3),
            domains(random, n, 0, 2),
            domains(random, n, 0, 2),
            new int[][] {domain(random, 0, 3)});
    return Case.of(
        d,
        (store, x) -> {
          IntVar[] s = Arrays.copyOf(x, n);
          IntVar[] du = Arrays.copyOfRange(x, n, 2 * n);
          IntVar[] r = Arrays.copyOfRange(x, 2 * n, 3 * n);
          store.impose(new CumulativeBasic(s, du, r, x[3 * n]));
          store.impose(new HornFlow(s, du, r, x[3 * n]));
        },
        t ->
            fits(
                Arrays.copyOf(t, n),
                Arrays.copyOfRange(t, n, 2 * n),
                Arrays.copyOfRange(t, 2 * n, 3 * n),
                t[3 * n]),
        "n=" + n);
  }

  /** UnaryTransition: starts, durations, then the presence of each task when optional. */
  private static Case unaryTransition(Random random, boolean optional) {
    int n = 2 + random.nextInt(2);
    int families = 1 + random.nextInt(2);
    int[] family = ints(random, n, 0, families - 1);
    int[][] transitions = matrix(random, families, families, 0, 2);
    int[][] d =
        concat(
            domains(random, n, 0, 5),
            domains(random, n, 0, 2),
            optional ? domains(random, n, 0, 1) : new int[0][]);
    return Case.of(
        d,
        (store, x) ->
            store.impose(
                new UnaryTransition(
                    Arrays.copyOf(x, n),
                    Arrays.copyOfRange(x, n, 2 * n),
                    family,
                    transitions,
                    optional ? Arrays.copyOfRange(x, 2 * n, 3 * n) : null)),
        t -> {
          for (int i = 0; i < n; i++) {
            for (int j = i + 1; j < n; j++) {
              if (optional && (t[2 * n + i] == 0 || t[2 * n + j] == 0)) {
                continue;
              }
              boolean before = t[i] + t[n + i] + transitions[family[i]][family[j]] <= t[j];
              boolean after = t[j] + t[n + j] + transitions[family[j]][family[i]] <= t[i];
              if (!before && !after) {
                return false;
              }
            }
          }
          return true;
        },
        "family=" + Arrays.toString(family) + " transitions=" + Arrays.deepToString(transitions));
  }

  /** MultiCostRegular: word 0..n-1, costs n..n+r-1. */
  private static Case multiCostRegular(Random random) {
    int n = 2 + random.nextInt(3);
    int states = 1 + random.nextInt(3);
    int values = 2 + random.nextInt(2);
    int r = 1 + random.nextInt(2);
    int[][] transition = new int[states][values];
    for (int q = 0; q < states; q++) {
      for (int j = 0; j < values; j++) {
        transition[q][j] = random.nextInt(4) == 0 ? -1 : random.nextInt(states);
      }
    }
    int[] finalStates = IntStream.range(0, states).filter(q -> random.nextInt(3) != 0).toArray();
    if (finalStates.length == 0) {
      finalStates = new int[] {0};
    }
    int[] accepting = finalStates;
    int[][][] costs = new int[r][states][];
    for (int k = 0; k < r; k++) {
      costs[k] = matrix(random, states, values, 0, 2);
    }
    int[][] d = concat(domains(random, n, 0, values - 1), domains(random, r, 0, 2 * n));
    return Case.of(
        d,
        (store, x) ->
            store.impose(
                new MultiCostRegular(
                    Arrays.copyOf(x, n),
                    transition,
                    0,
                    0,
                    accepting,
                    costs,
                    Arrays.copyOfRange(x, n, n + r))),
        t -> {
          int q = 0;
          int[] sum = new int[r];
          for (int i = 0; i < n; i++) {
            for (int k = 0; k < r; k++) {
              sum[k] += costs[k][q][t[i]];
            }
            q = transition[q][t[i]];
            if (q < 0) {
              return false;
            }
          }
          int last = q;
          if (Arrays.stream(accepting).noneMatch(f -> f == last)) {
            return false;
          }
          for (int k = 0; k < r; k++) {
            if (sum[k] != t[n + k]) {
              return false;
            }
          }
          return true;
        },
        "transition="
            + Arrays.deepToString(transition)
            + " final="
            + Arrays.toString(accepting)
            + " costs="
            + Arrays.deepToString(costs));
  }
}
