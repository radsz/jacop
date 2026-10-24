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

import static org.assertj.core.api.Assertions.assertThatThrownBy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Stream;
import org.jacop.ImposeGroundingHarness.Case;
import org.jacop.constraints.ExtensionalConflictVa;
import org.jacop.constraints.ExtensionalSupportMdd;
import org.jacop.constraints.ExtensionalSupportStr;
import org.jacop.constraints.ExtensionalSupportVa;
import org.jacop.constraints.GCC;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.SoftAlldifferent;
import org.jacop.constraints.SoftGCC;
import org.jacop.constraints.ViolationMeasure;
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
import org.jacop.constraints.geost.Dbox;
import org.jacop.constraints.geost.Geost;
import org.jacop.constraints.geost.GeostObject;
import org.jacop.constraints.geost.NonOverlapping;
import org.jacop.constraints.geost.Shape;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.constraints.knapsack.KnapsackDP;
import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.constraints.table.HybridTable;
import org.jacop.constraints.table.NegativeTable;
import org.jacop.constraints.table.Restriction;
import org.jacop.constraints.table.SimpleTable;
import org.jacop.constraints.table.Table;
import org.jacop.constraints.table.TableReified;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
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
            Arguments.of("CumulativeUnaryOptional", cumulative("CumulativeUnaryOptional")),
            Arguments.of("SoftAlldifferentVariable", softAlldifferent(false, false)),
            Arguments.of("SoftAlldifferentDecomposition", softAlldifferent(true, false)),
            Arguments.of("SoftAlldifferentPrimitive", softAlldifferent(true, true)),
            Arguments.of("SoftGCCHardCountersSoftBounds", softGcc(0, false)),
            Arguments.of("SoftGCCHardBoundsSoftCounters", softGcc(1, false)),
            Arguments.of("SoftGCCHardCountersSoftCounters", softGcc(2, false)),
            Arguments.of("SoftGCCAllValuesHardCountersSoftBounds", softGcc(3, false)),
            Arguments.of("SoftGCCAllValuesHardBoundsSoftCounters", softGcc(4, false)),
            Arguments.of("SoftGCCAllValuesHardCountersSoftCounters", softGcc(5, false)),
            Arguments.of("SoftGCCPrimitiveHardCounters", softGcc(0, true)),
            Arguments.of("SoftGCCPrimitiveHardBounds", softGcc(1, true)),
            Arguments.of("SoftGCCPrimitiveSoftCounters", softGcc(2, true)),
            Arguments.of("NetworkFlow", (Function<Random, Case>) ImposeGroundingCases::networkFlow),
            Arguments.of("Geost", geost(false)),
            Arguments.of("GeostTime", geost(true))),
        Stream.concat(additive(), tables()));
  }

  /** The table constraints. */
  private static Stream<Arguments> tables() {
    return Stream.of(
        Arguments.of("TableWide", tableCase("Table")),
        Arguments.of("TableReuse", tableCase("TableReuse")),
        Arguments.of("SimpleTableWide", tableCase("SimpleTable")),
        Arguments.of("SimpleTableReuse", tableCase("SimpleTableReuse")),
        Arguments.of("NegativeTable", tableCase("NegativeTable")),
        Arguments.of("TableReified", tableCase("TableReified")),
        Arguments.of("TableImplied", tableCase("TableImplied")),
        Arguments.of("HybridTableInt", tableCase("HybridTableInt")),
        Arguments.of("HybridTableStar", tableCase("HybridTableStar")),
        Arguments.of("HybridTableRestrictions", hybridRestrictions(true)),
        Arguments.of("HybridTableRestrictionsNoExpand", hybridRestrictions(false)),
        Arguments.of("ExtensionalSupportVaWide", tableCase("ExtensionalSupportVa")),
        Arguments.of("ExtensionalSupportStrTT", tableCase("ExtensionalSupportStrTT")),
        Arguments.of("ExtensionalSupportStrTF", tableCase("ExtensionalSupportStrTF")),
        Arguments.of("ExtensionalSupportStrFT", tableCase("ExtensionalSupportStrFT")),
        Arguments.of("ExtensionalSupportStrFF", tableCase("ExtensionalSupportStrFF")),
        Arguments.of("ExtensionalSupportMddTable", tableCase("ExtensionalSupportMddIncremental")),
        Arguments.of("ExtensionalSupportMddSearch", tableCase("ExtensionalSupportMddSearch")),
        Arguments.of("ExtensionalSupportMddEdges", mddEdges()),
        Arguments.of("ExtensionalConflictVaWide", tableCase("ExtensionalConflictVa")));
  }

  // ---------------------------------------------------------------------------------------------
  // Table constraints.

  /**
   * Random tables of arity 1..4 over values -2..4 on domains within -1..3, so some tuple values are
   * outside the domains; the table may be empty, have duplicates, or contain every combination.
   * Kinds ending in Reified/Implied have a 0/1 control variable last.
   */
  private static Function<Random, Case> tableCase(String kind) {
    return random -> {
      int n = 1 + random.nextInt(4);
      int[][] domains = domains(random, n, -1, 3);
      int[][] table = randomTuples(random, domains, n);
      if (kind.startsWith("SimpleTable") && table.length > 64) {
        // SimpleTable takes at most 64 tuples
        table = Arrays.copyOf(table, 64);
      }
      final int[][] tuples = table;
      Set<List<Integer>> tupleSet = new HashSet<>();
      for (int[] t : tuples) {
        tupleSet.add(Arrays.stream(t).boxed().toList());
      }
      int star = 9;
      boolean starred = kind.equals("HybridTableStar");
      if (starred) {
        for (int[] t : tuples) {
          for (int j = 0; j < n; j++) {
            if (random.nextInt(4) == 0) {
              t[j] = star;
            }
          }
        }
      }
      boolean control = kind.equals("TableReified") || kind.equals("TableImplied");
      int[][] all = domains;
      if (control) {
        all = Arrays.copyOf(domains, n + 1);
        all[n] = new int[] {0, 1};
      }
      Predicate<int[]> inTable =
          t -> {
            if (starred) {
              for (int[] tuple : tuples) {
                boolean match = true;
                for (int j = 0; j < n && match; j++) {
                  match = tuple[j] == star || tuple[j] == t[j];
                }
                if (match) {
                  return true;
                }
              }
              return false;
            }
            return tupleSet.contains(Arrays.stream(t, 0, n).boxed().toList());
          };
      Predicate<int[]> semantics =
          switch (kind) {
            case "NegativeTable", "ExtensionalConflictVa" -> t -> !inTable.test(t);
            case "TableReified" -> t -> (t[n] == 1) == inTable.test(t);
            case "TableImplied" -> t -> t[n] == 0 || inTable.test(t);
            default -> inTable;
          };
      return Case.of(
          all,
          (store, x) -> {
            int[][] copy = Arrays.stream(tuples).map(int[]::clone).toArray(int[][]::new);
            IntVar[] list = Arrays.copyOf(x, n);
            store.impose(
                switch (kind) {
                  case "Table" -> new Table(list, copy);
                  case "TableReuse" -> new Table(list, copy, true);
                  case "SimpleTable" -> new SimpleTable(list, copy);
                  case "SimpleTableReuse" -> new SimpleTable(list, copy, true);
                  case "NegativeTable" -> new NegativeTable(list, copy);
                  case "TableReified" -> new TableReified(list, copy, x[n]);
                  case "TableImplied" -> new TableReified(list, copy, x[n], true);
                  case "HybridTableInt" -> new HybridTable(list, copy);
                  case "HybridTableStar" -> new HybridTable(list, copy, star);
                  case "ExtensionalSupportVa" -> new ExtensionalSupportVa(list, copy);
                  case "ExtensionalSupportStrTT" ->
                      new ExtensionalSupportStr(list, copy, true, true);
                  case "ExtensionalSupportStrTF" ->
                      new ExtensionalSupportStr(list, copy, true, false);
                  case "ExtensionalSupportStrFT" ->
                      new ExtensionalSupportStr(list, copy, false, true);
                  case "ExtensionalSupportStrFF" ->
                      new ExtensionalSupportStr(list, copy, false, false);
                  case "ExtensionalSupportMddIncremental", "ExtensionalSupportMddSearch" -> {
                    ExtensionalSupportMdd mdd = new ExtensionalSupportMdd(list, copy);
                    mdd.setPropagation(
                        kind.endsWith("Search")
                            ? ExtensionalSupportMdd.Propagation.SUPPORT_SEARCH
                            : ExtensionalSupportMdd.Propagation.INCREMENTAL);
                    yield mdd;
                  }
                  default -> new ExtensionalConflictVa(list, copy);
                });
          },
          semantics,
          "tuples=" + Arrays.deepToString(tuples) + (starred ? " star=" + star : ""));
    };
  }

  /**
   * Random tuples: none, a few random ones (values -2..4, with duplicates), the full product of the
   * domains, or the full product minus some.
   */
  private static int[][] randomTuples(Random random, int[][] domains, int n) {
    int mode = random.nextInt(6);
    if (mode == 0) {
      return new int[0][];
    }
    if (mode == 1) {
      List<int[]> product = new ArrayList<>();
      product(domains, new int[n], 0, product);
      Collections.shuffle(product, random);
      int keep = random.nextBoolean() ? product.size() : random.nextInt(product.size() + 1);
      return product.subList(0, keep).toArray(int[][]::new);
    }
    int k = 1 + random.nextInt(10);
    int[][] tuples = new int[k][n];
    for (int[] t : tuples) {
      for (int j = 0; j < n; j++) {
        // mostly domain values, sometimes a value outside the domain
        t[j] =
            random.nextInt(5) == 0
                ? -2 + random.nextInt(7)
                : domains[j][random.nextInt(domains[j].length)];
      }
    }
    if (k > 1 && random.nextBoolean()) {
      tuples[k - 1] = tuples[0].clone();
    }
    return tuples;
  }

  private static void product(int[][] domains, int[] t, int i, List<int[]> out) {
    if (i == t.length) {
      out.add(t.clone());
      return;
    }
    for (int v : domains[i]) {
      t[i] = v;
      product(domains, t, i + 1, out);
    }
  }

  /** A restriction and its meaning for {@link #hybridRestrictions}. */
  private record Cell(Restriction restriction, BiPredicate<Integer, int[]> accepts) {}

  private static Cell randomCell(Random random, int column, int n) {
    int v = -1 + random.nextInt(5);
    int w = -1 + random.nextInt(5);
    switch (random.nextInt(10)) {
      case 0:
        return new Cell(Restriction.any(), (a, t) -> true);
      case 1:
        return new Cell(Restriction.ne(v), (a, t) -> a != v);
      case 2:
        return new Cell(Restriction.le(v), (a, t) -> a <= v);
      case 3:
        return new Cell(Restriction.gt(v), (a, t) -> a > v);
      case 4:
        return new Cell(Restriction.in(v, w), (a, t) -> a == v || a == w);
      case 5:
        return new Cell(Restriction.notIn(v, w), (a, t) -> a != v && a != w);
      case 6:
        if (n > 1) {
          int other = (column + 1 + random.nextInt(n - 1)) % n;
          Restriction.Relation[] relations = Restriction.Relation.values();
          Restriction.Relation relation = relations[random.nextInt(relations.length)];
          int offset = random.nextInt(3) - 1;
          return new Cell(
              Restriction.column(relation, other, offset),
              (a, t) ->
                  switch (relation) {
                    case LT -> a < t[other] + offset;
                    case LE -> a <= t[other] + offset;
                    case EQ -> a == t[other] + offset;
                    case NE -> a != t[other] + offset;
                    case GE -> a >= t[other] + offset;
                    case GT -> a > t[other] + offset;
                  });
        }
        return new Cell(Restriction.eq(v), (a, t) -> a == v);
      default:
        return new Cell(Restriction.eq(v), (a, t) -> a == v);
    }
  }

  /** HybridTable with unary and between-column restrictions. */
  private static Function<Random, Case> hybridRestrictions(boolean expand) {
    return random -> {
      int n = 1 + random.nextInt(4);
      int[][] domains = domains(random, n, -1, 3);
      int k = random.nextInt(6);
      Cell[][] cells = new Cell[k][n];
      for (int r = 0; r < k; r++) {
        for (int j = 0; j < n; j++) {
          cells[r][j] = randomCell(random, j, n);
        }
      }
      Predicate<int[]> semantics =
          t -> {
            for (Cell[] row : cells) {
              boolean match = true;
              for (int j = 0; j < n && match; j++) {
                match = row[j].accepts().test(t[j], t);
              }
              if (match) {
                return true;
              }
            }
            return false;
          };
      Restriction[][] tuples =
          Arrays.stream(cells)
              .map(row -> Arrays.stream(row).map(Cell::restriction).toArray(Restriction[]::new))
              .toArray(Restriction[][]::new);
      return Case.of(
          domains,
          (store, x) -> store.impose(new HybridTable(x, tuples, expand)),
          semantics,
          "tuples=" + Arrays.deepToString(tuples));
    };
  }

  /**
   * ExtensionalSupportMdd given as a random layered graph (node 1 the root, node 0 the terminal),
   * with up to 3 nodes per inner level, labels within -2..4 and nodes without in- or out-edges.
   */
  private static Function<Random, Case> mddEdges() {
    return random -> {
      int n = 1 + random.nextInt(4);
      int[][] domains = domains(random, n, -1, 3);
      List<Integer> level = new ArrayList<>();
      List<List<Integer>> nodesAt = new ArrayList<>();
      level.add(1);
      nodesAt.add(List.of(1));
      for (int l = 2; l <= n; l++) {
        List<Integer> nodes = new ArrayList<>();
        int width = 1 + random.nextInt(3);
        for (int w = 0; w < width; w++) {
          level.add(l);
          nodes.add(level.size());
        }
        nodesAt.add(nodes);
      }
      nodesAt.add(List.of(0));
      List<Integer> from = new ArrayList<>();
      List<Integer> to = new ArrayList<>();
      List<int[]> labels = new ArrayList<>();
      for (int l = 0; l < n; l++) {
        for (int node : nodesAt.get(l)) {
          int edges = random.nextInt(3);
          for (int e = 0; e < edges; e++) {
            List<Integer> next = nodesAt.get(l + 1);
            from.add(node);
            to.add(next.get(random.nextInt(next.size())));
            int a = -2 + random.nextInt(7);
            int b = random.nextBoolean() ? a : -2 + random.nextInt(7);
            labels.add(new int[] {a, b});
          }
        }
      }
      boolean search = random.nextBoolean();
      int[] levelArray = level.stream().mapToInt(Integer::intValue).toArray();
      int[] fromArray = from.stream().mapToInt(Integer::intValue).toArray();
      int[] toArray = to.stream().mapToInt(Integer::intValue).toArray();
      Predicate<int[]> semantics =
          t -> {
            Set<Integer> current = Set.of(1);
            for (int i = 0; i < n; i++) {
              Set<Integer> next = new HashSet<>();
              for (int e = 0; e < fromArray.length; e++) {
                int[] label = labels.get(e);
                if (current.contains(fromArray[e]) && (t[i] == label[0] || t[i] == label[1])) {
                  next.add(toArray[e]);
                }
              }
              current = next;
            }
            return current.contains(0);
          };
      return Case.of(
          domains,
          (store, x) -> {
            IntDomain[] label = new IntDomain[labels.size()];
            for (int e = 0; e < label.length; e++) {
              label[e] = new IntervalDomain();
              label[e].unionAdapt(labels.get(e)[0], labels.get(e)[0]);
              label[e].unionAdapt(labels.get(e)[1], labels.get(e)[1]);
            }
            ExtensionalSupportMdd mdd =
                new ExtensionalSupportMdd(x, levelArray, fromArray, label, toArray);
            mdd.setPropagation(
                search
                    ? ExtensionalSupportMdd.Propagation.SUPPORT_SEARCH
                    : ExtensionalSupportMdd.Propagation.INCREMENTAL);
            store.impose(mdd);
          },
          semantics,
          "level="
              + level
              + " from="
              + from
              + " to="
              + to
              + " labels="
              + labels.stream().map(Arrays::toString).toList()
              + (search ? " SUPPORT_SEARCH" : " INCREMENTAL"));
    };
  }

  /**
   * SoftAlldifferent on x0..x(n-1) with cost last: the number of variables minus the number of
   * distinct values (variable-based) or the number of equal pairs (decomposition-based).
   */
  private static Function<Random, Case> softAlldifferent(boolean pairs, boolean primitive) {
    return random -> {
      int n = 2 + random.nextInt(3);
      int[][] domains = domains(random, n + 1, 0, 3);
      domains[n] = domain(random, 0, pairs ? n * (n - 1) / 2 : n - 1);
      ViolationMeasure measure =
          pairs ? ViolationMeasure.DECOMPOSITION_BASED : ViolationMeasure.VARIABLE_BASED;
      return Case.of(
          domains,
          (store, x) -> {
            SoftAlldifferent c = new SoftAlldifferent(Arrays.copyOf(x, n), x[n], measure);
            if (primitive) {
              c.primitiveDecomposition(store).forEach(store::impose);
            } else {
              store.imposeDecomposition(c);
            }
          },
          t -> {
            int cost = 0;
            if (pairs) {
              for (int i = 0; i < n; i++) {
                for (int j = 0; j < i; j++) {
                  cost += t[i] == t[j] ? 1 : 0;
                }
              }
            } else {
              cost = n - (int) Arrays.stream(t, 0, n).distinct().count();
            }
            return t[n] == cost;
          },
          measure.toString());
    };
  }

  /**
   * SoftGCC (value-based) with x0..x(n-1), then m hard counters and/or m soft counters, then the
   * cost. The constructor variant: 0 hard counters and soft bounds, 1 hard bounds and soft
   * counters, 2 hard and soft counters, 3-5 the same without counted values (all values of x are
   * counted).
   */
  private static Function<Random, Case> softGcc(int variant, boolean primitive) {
    return random -> {
      // all values of x are counted in variants 3-5, so x gets fewer values there
      int nx = variant >= 3 ? 2 : 2 + random.nextInt(2);
      int[][] xs = domains(random, nx, 0, variant >= 3 ? 2 : 3);
      int[] counted;
      if (variant >= 3) {
        counted = Arrays.stream(xs).flatMapToInt(Arrays::stream).distinct().sorted().toArray();
      } else {
        List<Integer> values = new ArrayList<>(List.of(0, 1, 2, 3));
        Collections.shuffle(values, random);
        // sorted, since the network swaps the counters of unsorted values (a separate fix)
        counted =
            values.subList(0, 1 + random.nextInt(2)).stream().mapToInt(i -> i).sorted().toArray();
      }
      int m = counted.length;
      boolean hardCounters = variant % 3 != 1;
      boolean softCounters = variant % 3 != 0;
      int counters = (hardCounters ? m : 0) + (softCounters ? m : 0);
      int[][] domains = new int[nx + counters + 1][];
      System.arraycopy(xs, 0, domains, 0, nx);
      for (int i = nx; i < nx + counters; i++) {
        domains[i] = domain(random, 0, nx);
      }
      domains[nx + counters] = domain(random, 0, 2 * nx);
      int[] lb = new int[m];
      int[] ub = new int[m];
      for (int i = 0; i < m; i++) {
        lb[i] = random.nextInt(nx + 1);
        ub[i] = lb[i] + random.nextInt(nx + 1 - lb[i]);
      }
      int hard0 = nx;
      int soft0 = nx + (hardCounters ? m : 0);
      int cost = nx + counters;
      return Case.of(
          domains,
          (store, x) -> {
            IntVar[] xv = Arrays.copyOf(x, nx);
            IntVar[] hard = hardCounters ? Arrays.copyOfRange(x, hard0, hard0 + m) : null;
            IntVar[] soft = softCounters ? Arrays.copyOfRange(x, soft0, soft0 + m) : null;
            int kind = variant;
            if (variant >= 3) {
              // without counted values, SoftGCC counts the values left in the domains of x, so it
              // must refuse counters that no longer match them and then needs the counted values
              IntDomain left = new IntervalDomain();
              Arrays.stream(xv).forEach(v -> left.unionAdapt(v.domain));
              if (left.getSize() != m) {
                assertThatThrownBy(() -> softGcc(variant, xv, hard, soft, null, lb, ub, x[cost]))
                    .isInstanceOf(IllegalArgumentException.class);
                kind = variant - 3;
              }
            }
            SoftGCC c = softGcc(kind, xv, hard, soft, counted, lb, ub, x[cost]);
            if (primitive) {
              c.primitiveDecomposition(store).forEach(store::impose);
            } else {
              store.imposeDecomposition(c);
            }
          },
          t -> {
            int total = 0;
            for (int i = 0; i < m; i++) {
              int v = counted[i];
              int count = (int) Arrays.stream(t, 0, nx).filter(e -> e == v).count();
              if (hardCounters ? t[hard0 + i] != count : count < lb[i] || count > ub[i]) {
                return false;
              }
              total +=
                  softCounters
                      ? Math.abs(count - t[soft0 + i])
                      : Math.max(0, Math.max(lb[i] - count, count - ub[i]));
            }
            return t[cost] == total;
          },
          "counted="
              + Arrays.toString(counted)
              + " lb="
              + Arrays.toString(lb)
              + " ub="
              + Arrays.toString(ub)
              + " variant="
              + variant);
    };
  }

  private static SoftGCC softGcc(
      int variant,
      IntVar[] x,
      IntVar[] hard,
      IntVar[] soft,
      int[] counted,
      int[] lb,
      int[] ub,
      IntVar cost) {
    ViolationMeasure vm = ViolationMeasure.VALUE_BASED;
    return switch (variant) {
      case 0 -> new SoftGCC(x, hard, counted, lb, ub, cost, vm);
      case 1 -> new SoftGCC(x, lb, ub, counted, soft, cost, vm);
      case 2 -> new SoftGCC(x, hard, counted, soft, cost, vm);
      case 3 -> new SoftGCC(x, hard, lb, ub, cost, vm);
      case 4 -> new SoftGCC(x, lb, ub, soft, cost, vm);
      default -> new SoftGCC(x, hard, soft, cost, vm);
    };
  }

  /**
   * NetworkFlow of a 2x2 transportation problem: sources with supplies, sinks with demands, flow
   * x(i,j) on arc i->j with weight w(i,j), and the cost last. Sometimes one weight is a variable
   * (just before the cost) and sometimes two arcs share one flow variable.
   */
  private static Case networkFlow(Random random) {
    int[] supply = {random.nextInt(3), random.nextInt(3)};
    int[] demand = new int[2];
    demand[0] = random.nextInt(supply[0] + supply[1] + 1);
    demand[1] = supply[0] + supply[1] - demand[0];
    int[] weight = {random.nextInt(3), random.nextInt(3), random.nextInt(3), random.nextInt(3)};
    boolean shared = random.nextInt(4) == 0;
    boolean varWeight = random.nextInt(3) == 0;
    int flows = shared ? 3 : 4;
    // arc k uses flow variable flowOf[k]
    int[] flowOf = shared ? new int[] {0, 1, 2, 0} : new int[] {0, 1, 2, 3};
    int[][] domains = new int[flows + (varWeight ? 1 : 0) + 1][];
    for (int i = 0; i < flows; i++) {
      domains[i] = domain(random, 0, 3);
    }
    if (varWeight) {
      domains[flows] = domain(random, 0, 2);
    }
    int cost = domains.length - 1;
    domains[cost] = domain(random, 0, 14);
    return Case.of(
        domains,
        (store, x) -> {
          NetworkBuilder net = new NetworkBuilder();
          Node[] sources = {net.addNode("s0", supply[0]), net.addNode("s1", supply[1])};
          Node[] sinks = {net.addNode("t0", -demand[0]), net.addNode("t1", -demand[1])};
          for (int k = 0; k < 4; k++) {
            Node from = sources[k / 2];
            Node to = sinks[k % 2];
            if (varWeight && k == 3) {
              net.addArc(from, to, x[flows], x[flowOf[k]]);
            } else {
              net.addArc(from, to, weight[k], x[flowOf[k]]);
            }
          }
          net.setCostVariable(x[cost]);
          store.impose(net.build());
        },
        t -> {
          int[] f = new int[4];
          for (int k = 0; k < 4; k++) {
            f[k] = t[flowOf[k]];
          }
          if (f[0] + f[1] != supply[0] || f[2] + f[3] != supply[1]) {
            return false;
          }
          if (f[0] + f[2] != demand[0] || f[1] + f[3] != demand[1]) {
            return false;
          }
          int total = 0;
          for (int k = 0; k < 4; k++) {
            total += (varWeight && k == 3 ? t[flows] : weight[k]) * f[k];
          }
          return t[cost] == total;
        },
        "supply="
            + Arrays.toString(supply)
            + " demand="
            + Arrays.toString(demand)
            + " weight="
            + Arrays.toString(weight)
            + " shared="
            + shared
            + " varWeight="
            + varWeight);
  }

  /**
   * Geost with 2 or 3 objects in one or two dimensions and NonOverlapping, at coordinates from 0
   * (shapes with holes at negative coordinates lose solutions, a separate fix). Each object has its
   * coordinates and its shape id as variables (in that order); shapes are 0..2, some made of two
   * boxes. With time, each object also has start, duration and end variables and does not overlap
   * the others only while their time intervals intersect; without time, start 0, duration 1 and end
   * 1 are fixed.
   */
  private static Function<Random, Case> geost(boolean time) {
    return random -> {
      int objects = 2 + random.nextInt(time ? 1 : 2);
      int dim = time ? 1 : 1 + random.nextInt(2);
      int shapes = 2 + random.nextInt(2);
      // boxes[s] = list of {origin..., length...}
      List<List<int[]>> boxes = new ArrayList<>();
      for (int s = 0; s < shapes; s++) {
        List<int[]> list = new ArrayList<>();
        int count = 1 + random.nextInt(2);
        for (int b = 0; b < count; b++) {
          int[] box = new int[2 * dim];
          for (int d = 0; d < dim; d++) {
            box[d] = b == 0 ? 0 : random.nextInt(2);
            box[dim + d] = 1 + random.nextInt(2);
          }
          list.add(box);
        }
        boxes.add(list);
      }
      int per = dim + 1 + (time ? 3 : 0);
      int[][] domains = new int[objects * per][];
      for (int o = 0; o < objects; o++) {
        for (int d = 0; d < dim; d++) {
          domains[o * per + d] = domain(random, 0, 3);
        }
        domains[o * per + dim] = domain(random, 0, shapes - 1);
        if (time) {
          domains[o * per + dim + 1] = domain(random, 0, 2);
          domains[o * per + dim + 2] = domain(random, 0, 2);
          domains[o * per + dim + 3] = domain(random, 0, 3);
        }
      }
      return Case.of(
          domains,
          (store, x) -> {
            List<Shape> shapeList = new ArrayList<>();
            for (int s = 0; s < shapes; s++) {
              List<Dbox> dboxes = new ArrayList<>();
              for (int[] box : boxes.get(s)) {
                dboxes.add(
                    new Dbox(
                        Arrays.copyOfRange(box, 0, dim), Arrays.copyOfRange(box, dim, 2 * dim)));
              }
              shapeList.add(new Shape(s, dboxes));
            }
            List<GeostObject> objectList = new ArrayList<>();
            for (int o = 0; o < objects; o++) {
              IntVar[] coords = Arrays.copyOfRange(x, o * per, o * per + dim);
              IntVar shape = x[o * per + dim];
              IntVar start = time ? x[o * per + dim + 1] : new IntVar(store, 0, 0);
              IntVar duration = time ? x[o * per + dim + 2] : new IntVar(store, 1, 1);
              IntVar end = time ? x[o * per + dim + 3] : new IntVar(store, 1, 1);
              objectList.add(new GeostObject(o, coords, shape, start, duration, end));
            }
            // NonOverlapping must select the time dimension (dim) as well; without it the objects
            // are never pruned
            int[] selected = new int[dim + 1];
            for (int d = 0; d < selected.length; d++) {
              selected[d] = d;
            }
            store.impose(
                new Geost(
                    objectList, List.of(new NonOverlapping(objectList, selected)), shapeList));
          },
          t -> {
            if (time) {
              for (int o = 0; o < objects; o++) {
                int start = t[o * per + dim + 1];
                int duration = t[o * per + dim + 2];
                int end = t[o * per + dim + 3];
                if (duration <= 0 || start + duration != end) {
                  return false;
                }
              }
            }
            for (int a = 0; a < objects; a++) {
              for (int b = a + 1; b < objects; b++) {
                if (time
                    && !(t[a * per + dim + 1] < t[b * per + dim + 3]
                        && t[b * per + dim + 1] < t[a * per + dim + 3])) {
                  continue;
                }
                for (int[] boxA : boxes.get(t[a * per + dim])) {
                  for (int[] boxB : boxes.get(t[b * per + dim])) {
                    boolean overlap = true;
                    for (int d = 0; d < dim; d++) {
                      int lowA = t[a * per + d] + boxA[d];
                      int lowB = t[b * per + d] + boxB[d];
                      if (lowA >= lowB + boxB[dim + d] || lowB >= lowA + boxA[dim + d]) {
                        overlap = false;
                      }
                    }
                    if (overlap) {
                      return false;
                    }
                  }
                }
              }
            }
            return true;
          },
          "dim="
              + dim
              + " boxes="
              + boxes.stream().map(l -> l.stream().map(Arrays::toString).toList()).toList());
    };
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
            "XplusCneqZ(x,c,x)",
            r -> domains(r, 1, -3, 4),
            // impose() rejects c = 0 here, the model being trivially inconsistent
            (x, c) -> new XplusCneqZ(x[0], c == 0 ? 1 : c, x[0]),
            (t, c) -> true),
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
            (t, c) -> t[0] + t[0] <= t[1]),
        primitive(
            "XplusYlteqZ(x,y,x)",
            r -> domains(r, 2, -3, 4),
            (x, c) -> new XplusYlteqZ(x[0], x[1], x[0]),
            (t, c) -> t[1] <= 0),
        primitive(
            "XplusYlteqZ(x,y,y)",
            r -> domains(r, 2, -3, 4),
            (x, c) -> new XplusYlteqZ(x[0], x[1], x[1]),
            (t, c) -> t[0] <= 0),
        primitive(
            "XplusYlteqZ(x,x,x)",
            r -> domains(r, 1, -3, 4),
            (x, c) -> new XplusYlteqZ(x[0], x[0], x[0]),
            (t, c) -> t[0] <= 0));
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
