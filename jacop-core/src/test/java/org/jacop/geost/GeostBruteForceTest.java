/*
 * GeostBruteForceTest.java
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

package org.jacop.geost;

import static org.assertj.core.api.Assertions.assertThat;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.BiFunction;
import java.util.stream.Stream;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.geost.GeostInstance.Posted;
import org.jacop.geost.GeostInstance.Rect;
import org.jacop.geost.GeostInstance.Solutions;
import org.jacop.geost.GeostInstanceGenerator.Family;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMax;
import org.jacop.search.IndomainMiddle;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.SmallestDomain;
import org.jacop.search.SplitSelect;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Checks Geost against brute force on many small instances, searching for all solutions.
 *
 * <p>{@link #corpus} runs the instances of {@code geost/corpus.txt} (written by {@link
 * GeostInstanceGenerator}), whose solution counts and solution hashes come from brute force. Each
 * one is solved with Geost under four search strategies (input order, random order and values,
 * smallest domain with max values, and domain splitting), and also with Diffn, Nooverlap and Diff2
 * when it is a plain packing in one or two dimensions, and with a pairwise decomposition.
 *
 * <p>{@link #fuzz} generates new random instances and compares the solution sets. It runs a few
 * instances per family in the build; for a campaign raise the count:
 *
 * <pre>
 * mvn -Pmin -pl jacop-core test -Dtest=GeostBruteForceTest#fuzz -Dsurefire.rerunFailingTestsCount=0 \
 *     -Dgeost.fuzz.trials=2000 -Dgeost.fuzz.seed=7 -Dgeost.fuzz.families=TIME,SUBDIMS
 * </pre>
 */
class GeostBruteForceTest {

  /** Gives up an instance whose brute force has more solutions than this. */
  static final long MAX_SOLUTIONS = 3000;

  static final int FUZZ_TRIALS = Integer.getInteger("geost.fuzz.trials", 10);

  static final long FUZZ_SEED = Long.getLong("geost.fuzz.seed", 1);

  /** Solves all solutions of a posted model with one of the search strategies. */
  static Solutions solveAll(
      GeostInstance g,
      BiFunction<GeostInstance, Store, Posted> post,
      int strategy,
      long seed,
      boolean keep,
      List<String> wrong) {
    Store store = new Store();
    Posted p = post.apply(g, store);
    Solutions found = new Solutions(keep);
    if (!store.consistency()) {
      return found;
    }
    IntVar[] model = p.vars();
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            int[] v = Arrays.stream(model).mapToInt(IntVar::value).toArray();
            if (!g.check(v)) {
              wrong.add(Arrays.toString(v));
            }
            found.add(v);
            return result;
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    IntVar[] order = model.clone();
    SelectChoicePoint<IntVar> select =
        switch (strategy) {
          case 0 -> new SimpleSelect<>(order, null, new IndomainMin<>());
          case 1 -> {
            List<IntVar> l = new ArrayList<>(Arrays.asList(order));
            Collections.shuffle(l, new Random(seed));
            yield new SimpleSelect<>(
                l.toArray(new IntVar[0]), null, new IndomainRandom<>((int) seed));
          }
          case 2 -> new SimpleSelect<>(order, new SmallestDomain<>(), new IndomainMax<>());
          default -> new SplitSelect<>(order, null, new IndomainMiddle<>());
        };
    search.labeling(store, select);
    return found;
  }

  static final int STRATEGIES = 4;

  /** The models compared on an instance: Geost always, the others when they apply. */
  static List<Map.Entry<String, BiFunction<GeostInstance, Store, Posted>>> models(
      GeostInstance g, boolean decomposition) {
    List<Map.Entry<String, BiFunction<GeostInstance, Store, Posted>>> m = new ArrayList<>();
    m.add(Map.entry("geost", (i, s) -> i.postGeost(s, false)));
    m.add(Map.entry("geost-shared", (i, s) -> i.postGeost(s, true)));
    if (g.nonOverlaps.size() > 1 || g.area != null) {
      m.add(Map.entry("geost-split", (i, s) -> i.postGeostSplit(s)));
    }
    if (g.diffnExpressible()) {
      m.add(Map.entry("diffn-nonstrict", (i, s) -> i.postRectangles(s, Rect.DIFFN_NONSTRICT)));
      m.add(Map.entry("diff2", (i, s) -> i.postRectangles(s, Rect.DIFF2)));
      if (g.sameBoxCounts()) {
        m.add(Map.entry("diffn", (i, s) -> i.postRectangles(s, Rect.DIFFN_STRICT)));
        m.add(Map.entry("nooverlap", (i, s) -> i.postRectangles(s, Rect.NOOVERLAP_STRICT)));
      }
    }
    if (decomposition) {
      m.add(Map.entry("decomposition", (i, s) -> i.postDecomposition(s)));
    }
    return m;
  }

  static List<GeostInstance> corpusInstances() throws IOException {
    try (InputStream in = GeostBruteForceTest.class.getResourceAsStream("/geost/corpus.txt")) {
      return GeostInstance.parseAll(new String(in.readAllBytes(), StandardCharsets.UTF_8));
    }
  }

  static Stream<Arguments> corpusFamilies() throws IOException {
    Map<String, List<GeostInstance>> byFamily = new TreeMap<>();
    for (GeostInstance g : corpusInstances()) {
      byFamily.computeIfAbsent(g.name.replaceAll("-\\d+$", ""), f -> new ArrayList<>()).add(g);
    }
    return byFamily.entrySet().stream().map(e -> Arguments.of(e.getKey(), e.getValue()));
  }

  /**
   * Every model and search finds exactly the brute-force solutions of every corpus instance (same
   * count, same order-independent hash, and every solution checked).
   */
  @ParameterizedTest(name = "{0}")
  @MethodSource("corpusFamilies")
  void corpus(String family, List<GeostInstance> instances) {
    List<String> failures = new ArrayList<>();
    for (GeostInstance g : instances) {
      for (var model : models(g, true)) {
        int strategies = model.getKey().equals("geost") ? STRATEGIES : 1;
        for (int st = 0; st < strategies; st++) {
          List<String> wrong = new ArrayList<>();
          Solutions s = solveAll(g, model.getValue(), st, g.name.hashCode(), false, wrong);
          if (s.count != g.expectedCount || !s.hash().equals(g.expectedHash) || !wrong.isEmpty()) {
            failures.add(
                String.format(
                    "%s %s strategy %d: %d solutions (expected %d)%s",
                    g.name,
                    model.getKey(),
                    st,
                    s.count,
                    g.expectedCount,
                    wrong.isEmpty()
                        ? ""
                        : ", wrong " + wrong.subList(0, Math.min(3, wrong.size()))));
          }
        }
      }
    }
    assertThat(failures).as(family).isEmpty();
  }

  /**
   * After a backtrack, Geost's own pruning grounds object 8 of mixed-70 during consistency; the
   * object was swept as grounded in the branch before, and was not swept again in its new place, so
   * a solution with two overlapping objects was accepted.
   */
  @Test
  void objectGroundedByItsOwnPruningAfterABacktrackIsSweptAgain() throws IOException {
    GeostInstance g =
        corpusInstances().stream().filter(i -> i.name.equals("mixed-70")).findFirst().orElseThrow();
    long seed = g.name.hashCode();
    Store store = new Store();
    IntVar[] model = g.postGeost(store, false).vars();
    List<String> wrong = new ArrayList<>();
    Solutions found = new Solutions(false);
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            int[] v = Arrays.stream(model).mapToInt(IntVar::value).toArray();
            if (!g.check(v)) {
              wrong.add(Arrays.toString(v));
            }
            found.add(v);
            return result;
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    List<IntVar> order = new ArrayList<>(Arrays.asList(model));
    Collections.shuffle(order, new Random(seed + 200_038L));
    assertThat(store.consistency()).isTrue();
    search.labeling(
        store,
        new SimpleSelect<>(order.toArray(new IntVar[0]), null, new IndomainRandom<>((int) seed)));
    assertThat(wrong).isEmpty();
    assertThat(found.count).isEqualTo(g.expectedCount);
  }

  /** The corpus has instances of every family, and its counts still match the brute force. */
  @Test
  void corpusMatchesBruteForce() throws IOException {
    List<GeostInstance> all = corpusInstances();
    Set<String> families = new HashSet<>();
    for (GeostInstance g : all) {
      families.add(g.name.replaceAll("-\\d+$", ""));
      Solutions s = g.bruteForce(false, Long.MAX_VALUE);
      assertThat(s.count).as(g.name).isEqualTo(g.expectedCount);
      assertThat(s.hash()).as(g.name).isEqualTo(g.expectedHash);
    }
    assertThat(families).hasSize(Family.values().length);
  }

  static Stream<Arguments> families() {
    String only = System.getProperty("geost.fuzz.families");
    return Arrays.stream(Family.values())
        .filter(f -> only == null || Arrays.asList(only.split(",")).contains(f.name()))
        .map(Arguments::of);
  }

  /** New random instances: the solution sets of every model and search equal the brute force. */
  @ParameterizedTest(name = "{0}")
  @MethodSource("families")
  void fuzz(Family family) {
    GeostInstanceGenerator gen = new GeostInstanceGenerator(FUZZ_SEED * 31 + family.ordinal());
    List<String> failures = new ArrayList<>();
    int checked = 0;
    for (int trial = 0; trial < FUZZ_TRIALS && failures.size() < 5; trial++) {
      GeostInstance g = gen.generate(family, family.name().toLowerCase() + "-fuzz-" + trial);
      Solutions expected = g.bruteForce(true, MAX_SOLUTIONS);
      if (expected == null) {
        continue;
      }
      checked++;
      for (var model : models(g, trial % 4 == 0)) {
        int strategies = model.getKey().equals("geost") ? STRATEGIES : 1;
        for (int st = 0; st < strategies; st++) {
          List<String> wrong = new ArrayList<>();
          Solutions s = solveAll(g, model.getValue(), st, trial, true, wrong);
          Set<List<Integer>> missing = new HashSet<>(expected.all);
          missing.removeAll(s.all);
          if (!missing.isEmpty() || !wrong.isEmpty() || s.count != expected.count) {
            failures.add(
                String.format(
                    "%s strategy %d: %d solutions, expected %d; missing %s; wrong %s%n%s",
                    model.getKey(),
                    st,
                    s.count,
                    expected.count,
                    missing.stream().limit(3).toList(),
                    wrong.stream().limit(3).toList(),
                    g.format()));
            break;
          }
        }
      }
    }
    assertThat(failures).as("%s, %d instances checked", family, checked).isEmpty();
  }
}
