/*
 * CumulativeBruteForceTest.java
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
import java.util.function.Function;
import java.util.stream.Stream;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.constraints.cumulative.CumulativeUnaryOptional;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMax;
import org.jacop.search.IndomainMin;
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
 * Compares all solutions of the cumulative propagators, with each combination of filtering rules,
 * against brute-force enumeration on random small instances with holes in the start domains and
 * variable durations, resources and limits. It also checks that every added rule only removes
 * values that the weaker configuration keeps and that each rule prunes on some instances.
 */
class CumulativeBruteForceTest {

  private static final int TRIALS = 400;

  private static final int MAX_TUPLES = 60_000;

  /** One random instance; absent optional tasks have presence 0. */
  private record Instance(
      int n, int[][] starts, int[][] durations, int[][] resources, int[] limit, int[][] opt) {

    int[][] domains() {
      List<int[]> all = new ArrayList<>();
      all.addAll(Arrays.asList(starts));
      all.addAll(Arrays.asList(durations));
      all.addAll(Arrays.asList(resources));
      all.add(limit);
      if (opt != null) {
        all.addAll(Arrays.asList(opt));
      }
      return all.toArray(int[][]::new);
    }

    boolean satisfied(int[] x) {
      int horizon = 0;
      for (int i = 0; i < n; i++) {
        horizon = Math.max(horizon, x[i] + x[n + i]);
      }
      for (int t = 0; t < horizon; t++) {
        int use = 0;
        for (int i = 0; i < n; i++) {
          boolean present = opt == null || x[3 * n + 1 + i] == 1;
          if (present && x[i] <= t && t < x[i] + x[n + i]) {
            use += x[2 * n + i];
          }
        }
        if (use > x[3 * n]) {
          return false;
        }
      }
      return true;
    }

    @Override
    public String toString() {
      return "starts="
          + Arrays.deepToString(starts)
          + " durations="
          + Arrays.deepToString(durations)
          + " resources="
          + Arrays.deepToString(resources)
          + " limit="
          + Arrays.toString(limit)
          + (opt == null ? "" : " opt=" + Arrays.deepToString(opt));
    }
  }

  /** A propagator configuration: which class and which rules. */
  private record Config(
      String name, boolean optional, boolean unary, Function<Vars, Constraint> make) {}

  private record Vars(IntVar[] s, IntVar[] d, IntVar[] r, IntVar limit, IntVar[] opt) {}

  private static Constraint cumulative(
      Vars v, boolean ef, boolean overload, boolean ttef, boolean ttdr, boolean quad) {
    Cumulative c = new Cumulative(v.s(), v.d(), v.r(), v.limit());
    c.doEdgeFind(ef);
    c.doOverload(overload);
    c.doTimeTableEdgeFind(ttef);
    c.doTimeTableDisjunctive(ttdr);
    c.doQuadraticEdgeFind(quad);
    return c;
  }

  static Stream<Arguments> configs() {
    return Stream.of(
            new Config("TT", false, false, v -> cumulative(v, false, false, false, false, false)),
            new Config(
                "TT+overload", false, false, v -> cumulative(v, false, true, false, false, false)),
            new Config("TT+EF", false, false, v -> cumulative(v, true, false, false, false, false)),
            new Config(
                "TT+quadEF", false, false, v -> cumulative(v, true, false, false, false, true)),
            new Config(
                "TT+TTEF", false, false, v -> cumulative(v, false, false, true, false, false)),
            new Config(
                "TT+TTDR", false, false, v -> cumulative(v, false, false, false, true, false)),
            new Config("all", false, false, v -> cumulative(v, true, true, true, true, false)),
            new Config(
                "optional",
                true,
                false,
                v -> {
                  CumulativeOptional c =
                      new CumulativeOptional(v.s(), v.d(), v.r(), v.limit(), v.opt());
                  c.doTimeTableEdgeFind(true);
                  c.doTimeTableDisjunctive(true);
                  return c;
                }),
            new Config(
                "optionalNoEF",
                true,
                false,
                v -> {
                  CumulativeOptional c =
                      new CumulativeOptional(v.s(), v.d(), v.r(), v.limit(), v.opt());
                  c.doEdgeFind(false);
                  return c;
                }),
            new Config(
                "unaryOptional",
                true,
                true,
                v ->
                    new CumulativeUnaryOptional(
                        v.s(), v.d(), v.r(), v.limit(), v.opt(), true, true)),
            new Config(
                "unaryOptionalNoProfile",
                true,
                true,
                v ->
                    new CumulativeUnaryOptional(
                        v.s(), v.d(), v.r(), v.limit(), v.opt(), false, true)))
        .map(c -> Arguments.of(c.name(), c));
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("configs")
  void solutionsMatchBruteForce(String name, Config config) {
    Random random = new Random(name.hashCode());
    for (int trial = 0; trial < TRIALS; trial++) {
      Instance instance = instance(random, config.optional(), config.unary());
      Set<List<Integer>> expected = new HashSet<>();
      int[][] domains = instance.domains();
      bruteForce(instance, domains, new int[domains.length], 0, expected);

      Set<List<Integer>> found = solveAll(instance, config, trial % 3, random.nextInt());
      Set<List<Integer>> missing = new HashSet<>(expected);
      missing.removeAll(found);
      Set<List<Integer>> wrong = new HashSet<>(found);
      wrong.removeAll(expected);
      assertThat(missing)
          .as("%s trial %d %s, missing solutions (wrong ones: %s)", name, trial, instance, wrong)
          .isEmpty();
      assertThat(wrong).as("%s trial %d %s, wrong solutions", name, trial, instance).isEmpty();
    }
  }

  /**
   * Every rule keeps a subset of the values the plain time-table keeps, at the root of random
   * instances, and every rule removes more than the time-table on some of them.
   */
  @Test
  void rulesAreStrongerThanTimeTable() {
    record Rule(String name, boolean ef, boolean overload, boolean ttef, boolean ttdr) {}
    List<Rule> rules =
        List.of(
            new Rule("EF", true, false, false, false),
            new Rule("TTEF", false, false, true, false),
            new Rule("TTDR", false, false, false, true));
    Random random = new Random(42);
    int[] stronger = new int[rules.size()];
    for (int trial = 0; trial < 3000; trial++) {
      Instance instance = instance(random, false, false, 7, 12, Long.MAX_VALUE);
      String base = rootDomains(instance, v -> cumulative(v, false, false, false, false, false));
      for (int k = 0; k < rules.size(); k++) {
        Rule rule = rules.get(k);
        String withRule =
            rootDomains(
                instance,
                v -> cumulative(v, rule.ef(), rule.overload(), rule.ttef(), rule.ttdr(), false));
        if (base == null) {
          assertThat(withRule).as("%s %s", rule.name(), instance).isNull();
        } else if (withRule == null || !withRule.equals(base)) {
          assertThat(withRule == null || subset(withRule, base, instance))
              .as("%s %s", rule.name(), instance)
              .isTrue();
          stronger[k]++;
        }
      }
    }
    for (int k = 0; k < rules.size(); k++) {
      assertThat(stronger[k])
          .as("%s %s", rules.get(k).name(), Arrays.toString(stronger))
          .isPositive();
    }
  }

  /** Three tasks of energy 4 each cannot fit in [0, 4) with capacity 2; no compulsory parts. */
  @Test
  void overloadCheckFailsWithoutCompulsoryParts() {
    for (boolean overload : new boolean[] {false, true}) {
      Store store = new Store();
      IntVar[] s = new IntVar[3];
      IntVar[] d = new IntVar[3];
      IntVar[] r = new IntVar[3];
      for (int i = 0; i < 3; i++) {
        s[i] = new IntVar(store, 0, 2);
        d[i] = new IntVar(store, 2, 2);
        r[i] = new IntVar(store, 2, 2);
      }
      Cumulative c = new Cumulative(s, d, r, new IntVar(store, 2, 2));
      c.doEdgeFind(false);
      c.doTimeTableEdgeFind(false);
      c.doTimeTableDisjunctive(false);
      c.doOverload(overload);
      store.impose(c);
      assertThat(store.consistency()).as("overload %s", overload).isEqualTo(!overload);
    }
  }

  /** The optional task that would overload the two present ones is made absent. */
  @Test
  void optionalOverloadMakesTaskAbsent() {
    for (boolean unary : new boolean[] {false, true}) {
      Store store = new Store();
      IntVar[] s = new IntVar[3];
      IntVar[] d = new IntVar[3];
      IntVar[] r = new IntVar[3];
      IntVar[] o = new IntVar[3];
      int height = unary ? 1 : 2;
      for (int i = 0; i < 3; i++) {
        s[i] = new IntVar(store, 0, unary ? 4 : 2);
        d[i] = new IntVar(store, 2, 2);
        r[i] = new IntVar(store, height, height);
        o[i] = new IntVar(store, i < 2 ? 1 : 0, 1);
      }
      IntVar limit = new IntVar(store, height, height);
      Constraint c;
      if (unary) {
        // three tasks of length 2 in [0, 6) fit; restrict the optional one to [0, 4)
        s[2].domain.in(store.level, s[2], 0, 2);
        s[0].domain.in(store.level, s[0], 0, 2);
        s[1].domain.in(store.level, s[1], 0, 2);
        c = new CumulativeUnaryOptional(s, d, r, limit, o, false, true);
      } else {
        CumulativeOptional co = new CumulativeOptional(s, d, r, limit, o);
        co.doEdgeFind(false);
        c = co;
      }
      store.impose(c);
      assertThat(store.consistency()).isTrue();
      assertThat(o[2].max()).as("unary %s", unary).isZero();
    }
  }

  /**
   * On a unary resource, two present tasks fill [0, 4); an optional task that can start at most at
   * 3 has to go after both, so it is absent. Its long maximal duration hides this from the overload
   * check.
   */
  @Test
  void optionalEdgeFindMakesTaskAbsent() {
    for (boolean edgeFind : new boolean[] {false, true}) {
      Store store = new Store();
      IntVar[] s = {new IntVar(store, 0, 2), new IntVar(store, 0, 2), new IntVar(store, 0, 3)};
      IntVar[] d = {new IntVar(store, 2, 2), new IntVar(store, 2, 2), new IntVar(store, 1, 5)};
      IntVar one = new IntVar(store, 1, 1);
      IntVar[] r = {one, one, one};
      IntVar[] o = {one, one, new IntVar(store, 0, 1)};
      store.impose(new CumulativeUnaryOptional(s, d, r, one, o, false, edgeFind));
      assertThat(store.consistency()).isTrue();
      assertThat(o[2].max()).as("edge finding %s", edgeFind).isEqualTo(edgeFind ? 0 : 1);
    }
  }

  private static boolean subset(String a, String b, Instance instance) {
    // compares the rendered domains variable by variable
    String[] da = a.split(";");
    String[] db = b.split(";");
    for (int i = 0; i < da.length; i++) {
      Set<String> va = new HashSet<>(Arrays.asList(da[i].split(",")));
      Set<String> vb = new HashSet<>(Arrays.asList(db[i].split(",")));
      if (!vb.containsAll(va)) {
        return false;
      }
    }
    return true;
  }

  /** The domains after root propagation, values separated by commas and variables by ';'. */
  private static String rootDomains(Instance instance, Function<Vars, Constraint> make) {
    Store store = new Store();
    IntVar[] x = variables(store, instance.domains());
    store.impose(make.apply(vars(instance, x)));
    if (!store.consistency()) {
      return null;
    }
    StringBuilder result = new StringBuilder();
    for (IntVar v : x) {
      for (var e = v.dom().valueEnumeration(); e.hasMoreElements(); ) {
        result.append(e.nextElement()).append(',');
      }
      result.append(';');
    }
    return result.toString();
  }

  private static Instance instance(Random random, boolean optional, boolean unary) {
    return instance(random, optional, unary, 5, 6, MAX_TUPLES);
  }

  private static Instance instance(
      Random random, boolean optional, boolean unary, int maxTasks, int horizon, long maxTuples) {
    while (true) {
      int n = 2 + random.nextInt(maxTasks - 1);
      int[][] starts = new int[n][];
      int[][] durations = new int[n][];
      int[][] resources = new int[n][];
      int[][] opt = optional ? new int[n][] : null;
      for (int i = 0; i < n; i++) {
        int lo = random.nextInt(horizon / 2 + 1);
        starts[i] = values(random, lo, lo + random.nextInt(horizon - lo + 1));
        int d = 1 + random.nextInt(3);
        durations[i] = random.nextInt(4) == 0 ? values(random, d - 1, d + 1) : new int[] {d};
        if (unary) {
          resources[i] = new int[] {1};
        } else {
          int r = 1 + random.nextInt(3);
          resources[i] = random.nextInt(4) == 0 ? values(random, r - 1, r) : new int[] {r};
        }
        if (optional) {
          int p = random.nextInt(4);
          opt[i] = p == 0 ? new int[] {0} : p == 1 ? new int[] {1} : new int[] {0, 1};
        }
      }
      int[] limit;
      if (unary) {
        limit = new int[] {1};
      } else {
        int c = 1 + random.nextInt(4);
        limit = random.nextInt(4) == 0 ? values(random, c, c + 1) : new int[] {c};
      }
      Instance instance = new Instance(n, starts, durations, resources, limit, opt);
      long tuples = 1;
      for (int[] dom : instance.domains()) {
        tuples *= dom.length;
      }
      if (tuples <= maxTuples) {
        return instance;
      }
    }
  }

  private static int[] values(Random random, int lo, int hi) {
    List<Integer> values = new ArrayList<>();
    for (int v = Math.max(0, lo); v <= hi; v++) {
      if (random.nextInt(4) != 0) {
        values.add(v);
      }
    }
    if (values.isEmpty()) {
      values.add(Math.max(0, lo));
    }
    return values.stream().mapToInt(Integer::intValue).toArray();
  }

  private static void bruteForce(
      Instance instance, int[][] domains, int[] values, int index, Set<List<Integer>> solutions) {
    if (index == values.length) {
      if (instance.satisfied(values)) {
        solutions.add(Arrays.stream(values).boxed().toList());
      }
      return;
    }
    for (int v : domains[index]) {
      values[index] = v;
      bruteForce(instance, domains, values, index + 1, solutions);
    }
  }

  private static IntVar[] variables(Store store, int[][] domains) {
    IntVar[] x = new IntVar[domains.length];
    for (int i = 0; i < x.length; i++) {
      IntervalDomain domain = new IntervalDomain();
      for (int v : domains[i]) {
        domain.unionAdapt(v, v);
      }
      x[i] = new IntVar(store, "x" + i, domain);
    }
    return x;
  }

  private static Vars vars(Instance instance, IntVar[] x) {
    int n = instance.n();
    return new Vars(
        Arrays.copyOfRange(x, 0, n),
        Arrays.copyOfRange(x, n, 2 * n),
        Arrays.copyOfRange(x, 2 * n, 3 * n),
        x[3 * n],
        instance.opt() == null ? null : Arrays.copyOfRange(x, 3 * n + 1, 4 * n + 1));
  }

  private static Set<List<Integer>> solveAll(
      Instance instance, Config config, int valueOrder, int seed) {
    Store store = new Store();
    IntVar[] x = variables(store, instance.domains());
    store.impose(config.make().apply(vars(instance, x)));

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
    search.labeling(
        store,
        new SimpleSelect<>(
            x,
            null,
            switch (valueOrder) {
              case 0 -> new IndomainMin<>();
              case 1 -> new IndomainMax<>();
              default -> new IndomainRandom<>(seed);
            }));
    return found;
  }
}
