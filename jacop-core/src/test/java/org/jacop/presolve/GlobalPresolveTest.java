/*
 * GlobalPresolveTest.java
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
package org.jacop.presolve;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.stream.Stream;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.ElementBool;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.ElementVariable;
import org.jacop.constraints.ElementVariableFast;
import org.jacop.constraints.Max;
import org.jacop.constraints.MaxSimple;
import org.jacop.constraints.Min;
import org.jacop.constraints.MinSimple;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XltC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.table.HybridTable;
import org.jacop.constraints.table.Restriction;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Global-specific presolve ({@link GlobalPresolve}): every rewriting keeps the solutions, checked
 * on random small instances built so that the rules apply, and the rewritings have the expected
 * form.
 */
class GlobalPresolveTest {

  private static final int TRIALS = 300;

  /** A random instance: variable domains and the constraint over the variables. */
  private record Instance(int[][] domains, BiFunction<Random, IntVar[], Constraint> constraint) {}

  /** Instance generators, each with the domains it draws. */
  private interface Generator {
    Instance next(Random r);
  }

  static Stream<Arguments> cases() {
    return Stream.of(
        Arguments.of("ElementInteger", element((x, l, v) -> new ElementInteger(x, l, v, 0), 6)),
        Arguments.of(
            "ElementIntegerFast", element((x, l, v) -> new ElementIntegerFast(x, l, v, 0), 6)),
        Arguments.of("ElementBool", element((x, l, v) -> new ElementBool(x, l, v, 0), 1)),
        Arguments.of("ElementVariable", elementVariable(false)),
        Arguments.of("ElementVariableFast", elementVariable(true)),
        Arguments.of("HybridTable", (Generator) GlobalPresolveTest::table),
        Arguments.of("XmulYeqZ", (Generator) GlobalPresolveTest::product),
        Arguments.of("Alldistinct", allDifferent(Alldistinct::new)),
        Arguments.of("Alldiff", allDifferent(Alldiff::new)),
        Arguments.of("Alldifferent", allDifferent(Alldifferent::new)),
        Arguments.of("Max", extremum(4, (l, m) -> new Max(l, m))),
        Arguments.of("Min", extremum(4, (l, m) -> new Min(l, m))),
        Arguments.of("MaxSimple", extremum(2, (l, m) -> new MaxSimple(l[0], l[1], m))),
        Arguments.of("MinSimple", extremum(2, (l, m) -> new MinSimple(l[0], l[1], m))),
        Arguments.of("Count", (Generator) GlobalPresolveTest::count),
        Arguments.of("CumulativeBasic", cumulative(0)),
        Arguments.of("Cumulative", cumulative(1)),
        Arguments.of("CumulativeUnary", cumulative(2)));
  }

  /**
   * The solutions through presolve, at level 0 or at level 1 after one variable is fixed, are the
   * solutions of the original store, and the rules rewrite a good share of the instances.
   */
  @ParameterizedTest(name = "{0}")
  @MethodSource("cases")
  void rewritingKeepsTheSolutions(String name, Generator generator) {
    Random random = new Random(name.hashCode());
    int rewritten = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      Instance instance = generator.next(random);
      long seed = random.nextLong();
      int restricted = trial % 3 == 0 ? random.nextInt(instance.domains().length) : -1;
      int[] dom = restricted < 0 ? null : instance.domains()[restricted];
      int kept = restricted < 0 ? 0 : dom[random.nextInt(dom.length)];
      boolean checking = trial % 2 == 0;

      Set<List<Integer>> expected = new HashSet<>();
      IntVar[] x = build(instance, new Random(seed));
      Store store = x[0].getStore();
      if (restrict(store, x, restricted, kept) && store.consistency()) {
        search(store, x, random.nextInt(), () -> expected.add(values(x)));
      }

      Set<List<Integer>> found = new HashSet<>();
      IntVar[] y = build(instance, new Random(seed));
      Store parent = y[0].getStore();
      if (restrict(parent, y, restricted, kept)) {
        Derivation d = Presolver.of(parent).keep(y).checking(checking).presolve();
        if (d.outcome() == Derivation.Outcome.DERIVED) {
          if (d.statistics().simplified() > 0) {
            rewritten++;
          }
          search(
              d.child(),
              d.counterparts(y),
              random.nextInt(),
              () -> {
                if (d.returnSolution()) {
                  found.add(values(y));
                }
              });
          d.discard();
        }
      }
      assertThat(found)
          .as(
              "%s trial %d domains=%s, x%d=%d, checking %b",
              name, trial, Arrays.deepToString(instance.domains()), restricted, kept, checking)
          .isEqualTo(expected);
    }
    assertThat(rewritten)
        .as("%s: instances rewritten (%d)", name, rewritten)
        .isGreaterThan(TRIALS / 20);
  }

  /**
   * Variable aliasing keeps the solutions: random models with equations, among variables that other
   * constraints may share and through elements that rewrite to equations.
   */
  @Test
  void aliasingKeepsTheSolutions() {
    Random random = new Random(17);
    int aliased = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      long seed = random.nextLong();
      boolean checking = trial % 2 == 0;
      int order = random.nextInt();

      Set<List<Integer>> expected = new HashSet<>();
      IntVar[] x = aliasModel(new Random(seed));
      search(x[0].getStore(), x, order, () -> expected.add(values(x)));

      Set<List<Integer>> found = new HashSet<>();
      IntVar[] y = aliasModel(new Random(seed));
      Derivation d = Presolver.of(y[0].getStore()).keep(y).checking(checking).presolve();
      if (d.outcome() == Derivation.Outcome.DERIVED) {
        aliased += d.statistics().aliased() > 0 ? 1 : 0;
        search(
            d.child(),
            d.counterparts(y),
            order,
            () -> {
              if (d.returnSolution()) {
                found.add(values(y));
              }
            });
        d.discard();
      }
      assertThat(found).as("trial %d, checking %b", trial, checking).isEqualTo(expected);
    }
    assertThat(aliased).as("instances aliased (%d)", aliased).isGreaterThan(TRIALS / 4);
  }

  @Test
  void anEquationMergesItsVariablesUnlessAnotherConstraintHasBoth() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 5);
    IntVar b = new IntVar(store, "b", 0, 5);
    IntVar c = new IntVar(store, "c", 0, 5);
    IntVar e = new IntVar(store, "e", 0, 5);
    store.impose(new XeqY(a, b));
    store.impose(new XeqY(b, c));
    store.impose(new XeqY(c, a));
    store.impose(new XeqY(c, e));
    store.impose(new XneqY(a, e));
    store.impose(new XltC(b, 4));
    Derivation d = Presolver.of(store).keep(a, b, c, e).presolve();
    // a, b and c become one variable; e stays apart, since a != e has a and e
    assertThat(d.statistics().aliased()).isEqualTo(2);
    assertThat(d.get(a)).isSameAs(d.get(b)).isSameAs(d.get(c)).isNotSameAs(d.get(e));
    // c = e and a != e are left; b < 4 holds once propagated
    assertThat(d.statistics().childConstraints()).isEqualTo(2);
  }

  /** Five variables over 0..3 with up to three equations and two other constraints. */
  private static IntVar[] aliasModel(Random r) {
    Store store = new Store();
    IntVar[] x = new IntVar[5];
    for (int i = 0; i < x.length; i++) {
      IntervalDomain domain = new IntervalDomain();
      for (int v : subset(r, 0, 3)) {
        domain.unionAdapt(v, v);
      }
      x[i] = new IntVar(store, "x" + i, domain);
    }
    for (int k = 1 + r.nextInt(3); k > 0; k--) {
      int[] p = distinct(r, 2);
      store.impose(new XeqY(x[p[0]], x[p[1]]));
    }
    for (int k = 0; k < 2; k++) {
      int[] p = distinct(r, 3);
      store.impose(
          switch (r.nextInt(5)) {
            case 0 -> new XneqY(x[p[0]], x[p[1]]);
            case 1 -> new XplusYeqZ(x[p[0]], x[p[1]], x[p[2]]);
            case 2 -> new Alldistinct(new IntVar[] {x[p[0]], x[p[1]], x[p[2]]});
            case 3 -> new XltY(x[p[0]], x[p[1]]);
            default -> new ElementInteger(x[p[0]], new int[] {0, 1, 2, 3, 4}, x[p[1]], -1);
          });
    }
    return x;
  }

  /** Distinct random indices of the five variables of {@link #aliasModel}. */
  private static int[] distinct(Random r, int n) {
    List<Integer> all = new ArrayList<>(List.of(0, 1, 2, 3, 4));
    Collections.shuffle(all, r);
    return all.subList(0, n).stream().mapToInt(Integer::intValue).toArray();
  }

  @Test
  void anElementOnConsecutiveValuesBecomesAnEquation() {
    Store store = new Store();
    IntVar index = new IntVar(store, "i", 1, 3);
    index.addDom(5, 5);
    IntVar value = new IntVar(store, "v", -10, 10);
    // positions 1, 2, 3 and 5 hold index + 4; position 4 cannot be reached
    assertThat(rewrite(store, new ElementInteger(index, new int[] {5, 6, 7, 0, 9}, value, 0)))
        .singleElement()
        .isInstanceOf(XplusCeqZ.class);
    IntVar value2 = new IntVar(store, "w", -10, 10);
    assertThat(rewrite(store, new ElementIntegerFast(index, new int[] {9, 8, 7, 0, 5}, value2, 0)))
        .singleElement()
        .isInstanceOf(XplusYeqC.class);
    IntVar value3 = new IntVar(store, "u", -10, 10);
    assertThat(rewrite(store, new ElementInteger(index, new int[] {1, 2, 3, 4, 5}, value3, 0)))
        .singleElement()
        .isInstanceOf(XeqY.class);
  }

  @Test
  void anElementOnOneValueHoldsAndOtherwiseItsListIsCut() {
    Store store = new Store();
    IntVar index = new IntVar(store, "i", 2, 4);
    IntVar value = new IntVar(store, "v", -10, 10);
    assertThat(rewrite(store, new ElementInteger(index, new int[] {1, 7, 7, 7, 2}, value, 0)))
        .isEmpty();
    IntVar value2 = new IntVar(store, "w", -10, 10);
    List<Constraint> cut =
        rewrite(store, new ElementInteger(index, new int[] {1, 7, 3, 9, 2}, value2, 0));
    assertThat(cut).singleElement().isInstanceOf(ElementInteger.class);
    assertThat(cut.get(0).toString()).contains("[7, 3, 9]");
  }

  @Test
  void anElementOverFixedVariablesBecomesAnElementOverIntegers() {
    Store store = new Store();
    IntVar index = new IntVar(store, "i", 1, 3);
    IntVar[] list = {
      new IntVar(store, "a", 4, 4), new IntVar(store, "b", 1, 1), new IntVar(store, "c", 6, 6)
    };
    IntVar value = new IntVar(store, "v", 0, 10);
    assertThat(rewrite(store, new ElementVariableFast(index, list, value, 0)))
        .singleElement()
        .isInstanceOf(ElementIntegerFast.class);
  }

  @Test
  void aTableLosesFixedColumnsAndTuplesTheDomainsRuleOut() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 2);
    IntVar b = new IntVar(store, "b", 1, 1);
    IntVar c = new IntVar(store, "c", 0, 2);
    HybridTable t =
        new HybridTable(new IntVar[] {a, b, c}, new int[][] {{0, 1, 2}, {1, 0, 1}, {2, 1, 0}});
    List<Constraint> r = rewrite(store, t);
    assertThat(r).singleElement().isInstanceOf(HybridTable.class);
    assertThat(r.get(0).arguments()).containsExactlyInAnyOrder(a, c);
    assertThat(a.domain.contains(1)).isFalse();
  }

  @Test
  void aProductWithAFixedFactorBecomesAScaling() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 3, 3);
    IntVar y = new IntVar(store, "y", -5, 5);
    IntVar z = new IntVar(store, "z", -20, 20);
    assertThat(rewrite(store, new XmulYeqZ(y, x, z))).singleElement().isInstanceOf(XmulCeqZ.class);
  }

  @Test
  void cumulativeLosesTasksThatUseNothingAndHoldsWhenEverythingFits() {
    Store store = new Store();
    IntVar[] s = {
      new IntVar(store, "s0", 0, 5), new IntVar(store, "s1", 0, 5), new IntVar(store, "s2", 0, 5)
    };
    IntVar[] d = {
      new IntVar(store, "d0", 2, 2), new IntVar(store, "d1", 0, 0), new IntVar(store, "d2", 3, 3)
    };
    IntVar[] res = {
      new IntVar(store, "r0", 2, 2), new IntVar(store, "r1", 1, 1), new IntVar(store, "r2", 0, 0)
    };
    IntVar limit = new IntVar(store, "limit", 1, 3);
    List<Constraint> r = rewrite(store, new Cumulative(s, d, res, limit));
    assertThat(r).singleElement().isInstanceOf(Cumulative.class);
    assertThat(r.get(0).arguments()).contains(s[0]).doesNotContain(s[1], s[2]);

    IntVar wide = new IntVar(store, "wide", 4, 9);
    assertThat(rewrite(store, new CumulativeBasic(s, d, res, wide))).isEmpty();
  }

  @Test
  void allDifferentLosesFixedVariablesNoOtherCanTake() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 1, 1);
    IntVar b = new IntVar(store, "b", 2, 4);
    IntVar c = new IntVar(store, "c", 2, 4);
    List<Constraint> r = rewrite(store, new Alldistinct(new IntVar[] {a, b, c}));
    assertThat(r).singleElement().isInstanceOf(Alldistinct.class);
    assertThat(r.get(0).arguments()).containsExactlyInAnyOrder(b, c);
  }

  @Test
  void aMaximumLosesVariablesThatCannotReachIt() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 3);
    IntVar b = new IntVar(store, "b", 3, 6);
    IntVar c = new IntVar(store, "c", 1, 2);
    IntVar m = new IntVar(store, "m", 0, 10);
    assertThat(rewrite(store, new Max(new IntVar[] {a, b, c}, m)))
        .singleElement()
        .isInstanceOf(XeqY.class);
  }

  /** Imposes a constraint, propagates and rewrites it. */
  private static List<Constraint> rewrite(Store store, Constraint c) {
    store.impose(c);
    assertThat(store.consistency()).isTrue();
    return GlobalPresolve.rewrite(c).orElseThrow();
  }

  // ----- generators -----

  @FunctionalInterface
  private interface ElementFactory {
    Constraint element(IntVar index, int[] list, IntVar value);
  }

  private static Generator element(ElementFactory factory, int maxValue) {
    return r -> {
      int n = 3 + r.nextInt(4);
      int[] list = new int[n];
      int c = r.nextInt(3);
      int shape = r.nextInt(4);
      for (int i = 0; i < n; i++) {
        list[i] =
            switch (shape) {
              case 0 -> Math.min(maxValue, i + c);
              case 1 -> Math.max(0, Math.min(maxValue, n - i - c));
              case 2 -> maxValue == 1 ? 1 : c;
              default -> r.nextInt(maxValue + 1);
            };
      }
      // a noisy entry the index may or may not reach
      if (r.nextBoolean()) {
        list[r.nextInt(n)] = r.nextInt(maxValue + 1);
      }
      int[][] domains = {subset(r, 0, n + 1), subset(r, -1, maxValue + 1)};
      return new Instance(domains, (rr, x) -> factory.element(x[0], list, x[1]));
    };
  }

  private static Generator elementVariable(boolean fast) {
    return r -> {
      int n = 2 + r.nextInt(4);
      int[][] domains = new int[n + 2][];
      domains[0] = subset(r, 0, n + 1);
      domains[1] = subset(r, 0, 4);
      for (int i = 0; i < n; i++) {
        domains[i + 2] = r.nextInt(3) == 0 ? subset(r, 0, 4) : new int[] {r.nextInt(5)};
      }
      return new Instance(
          domains,
          (rr, x) -> {
            IntVar[] list = Arrays.copyOfRange(x, 2, x.length);
            return fast
                ? new ElementVariableFast(x[0], list, x[1], 0)
                : new ElementVariable(x[0], list, x[1], 0);
          });
    };
  }

  private static Instance table(Random r) {
    int arity = 2 + r.nextInt(3);
    int[][] domains = new int[arity][];
    for (int i = 0; i < arity; i++) {
      domains[i] = r.nextInt(3) == 0 ? new int[] {r.nextInt(3)} : subset(r, 0, 3);
    }
    int count = 1 + r.nextInt(8);
    boolean binary = r.nextInt(4) == 0;
    return new Instance(
        domains,
        (rr, x) -> {
          Restriction[][] tuples = new Restriction[count][arity];
          for (Restriction[] tuple : tuples) {
            for (int i = 0; i < arity; i++) {
              tuple[i] = rr.nextInt(5) == 0 ? Restriction.any() : Restriction.eq(rr.nextInt(4));
            }
            if (binary) {
              tuple[0] = Restriction.column(Restriction.Relation.LE, 1);
            }
          }
          return new HybridTable(x, tuples);
        });
  }

  private static Instance product(Random r) {
    int[][] domains = {
      r.nextBoolean() ? new int[] {r.nextInt(5) - 2} : subset(r, -2, 3),
      subset(r, -3, 3),
      subset(r, -6, 6)
    };
    return new Instance(
        domains,
        (rr, x) ->
            rr.nextBoolean() ? new XmulYeqZ(x[0], x[1], x[2]) : new XmulYeqZ(x[1], x[0], x[2]));
  }

  private static Generator allDifferent(java.util.function.Function<IntVar[], Constraint> factory) {
    return r -> {
      int n = 2 + r.nextInt(4);
      int[][] domains = new int[n][];
      for (int i = 0; i < n; i++) {
        domains[i] = r.nextInt(3) == 0 ? new int[] {r.nextInt(6)} : subset(r, 0, 5);
      }
      return new Instance(domains, (rr, x) -> factory.apply(x));
    };
  }

  private static Generator extremum(int n, BiFunction<IntVar[], IntVar, Constraint> factory) {
    return r -> {
      int[][] domains = new int[n + 1][];
      for (int i = 0; i < n; i++) {
        int lo = r.nextInt(6);
        domains[i] = r.nextBoolean() ? new int[] {lo} : subset(r, lo, lo + 1 + r.nextInt(3));
      }
      domains[n] = subset(r, 0, 9);
      return new Instance(domains, (rr, x) -> factory.apply(Arrays.copyOf(x, n), x[n]));
    };
  }

  private static Instance count(Random r) {
    int n = 2 + r.nextInt(4);
    int[][] domains = new int[n + 1][];
    for (int i = 0; i < n; i++) {
      domains[i] = r.nextInt(3) == 0 ? new int[] {r.nextInt(3)} : subset(r, 0, 3);
    }
    domains[n] = subset(r, 0, n);
    int value = r.nextInt(3);
    return new Instance(domains, (rr, x) -> new Count(Arrays.copyOf(x, n), x[n], value));
  }

  /** Tasks with starts, durations and resource uses, then the limit; kind 2 is unary. */
  private static Generator cumulative(int kind) {
    return r -> {
      int n = 1 + r.nextInt(3);
      int[][] domains = new int[3 * n + 1][];
      for (int i = 0; i < n; i++) {
        domains[i] = subset(r, 0, 3);
        domains[n + i] = r.nextInt(3) == 0 ? new int[] {0} : subset(r, 0, 2);
        domains[2 * n + i] =
            r.nextInt(3) == 0 ? new int[] {0} : kind == 2 ? subset(r, 0, 1) : subset(r, 0, 3);
      }
      domains[3 * n] = kind == 2 ? new int[] {1} : subset(r, 1, 4);
      return new Instance(
          domains,
          (rr, x) -> {
            IntVar[] s = Arrays.copyOfRange(x, 0, n);
            IntVar[] d = Arrays.copyOfRange(x, n, 2 * n);
            IntVar[] res = Arrays.copyOfRange(x, 2 * n, 3 * n);
            return switch (kind) {
              case 0 -> new CumulativeBasic(s, d, res, x[3 * n]);
              case 1 -> new Cumulative(s, d, res, x[3 * n]);
              default -> new CumulativeUnary(s, d, res, x[3 * n]);
            };
          });
    };
  }

  /** A random non-empty subset of {@code lo..hi}. */
  private static int[] subset(Random r, int lo, int hi) {
    List<Integer> values = new ArrayList<>();
    for (int v = lo; v <= hi; v++) {
      if (r.nextInt(4) != 0) {
        values.add(v);
      }
    }
    if (values.isEmpty()) {
      values.add(lo + r.nextInt(hi - lo + 1));
    }
    return values.stream().mapToInt(Integer::intValue).toArray();
  }

  // ----- solving -----

  private static IntVar[] build(Instance instance, Random r) {
    Store store = new Store();
    IntVar[] x = new IntVar[instance.domains().length];
    for (int i = 0; i < x.length; i++) {
      IntervalDomain domain = new IntervalDomain();
      for (int v : instance.domains()[i]) {
        domain.unionAdapt(v, v);
      }
      x[i] = new IntVar(store, "x" + i, domain);
    }
    store.impose(instance.constraint().apply(r, x));
    return x;
  }

  private static boolean restrict(Store store, IntVar[] x, int restricted, int kept) {
    if (restricted < 0) {
      return true;
    }
    store.setLevel(1);
    try {
      x[restricted].domain.in(store.level, x[restricted], kept, kept);
      return true;
    } catch (FailException e) {
      return false;
    }
  }

  private static List<Integer> values(IntVar[] vars) {
    return Arrays.stream(vars).map(IntVar::value).toList();
  }

  private static void search(Store store, IntVar[] vars, int seed, Runnable onSolution) {
    if (vars.length == 0) {
      onSolution.run();
      return;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            onSolution.run();
            return result;
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, new SimpleSelect<>(vars, null, new IndomainRandom<>(seed)));
  }
}
