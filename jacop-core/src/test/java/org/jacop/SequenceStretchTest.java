/*
 * SequenceStretchTest.java
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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import org.jacop.constraints.AmongSeq;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Sequence;
import org.jacop.constraints.Stretch;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/**
 * Tests Sequence and Stretch. For the domain consistent Sequence propagator AmongSeq: all solutions
 * against brute force, also through Sequence and with repeated variables, the domain consistency at
 * random dive nodes, and identical search trees with the Regular decomposition of Sequence, which
 * is also domain consistent. For Stretch: all solutions against brute force with repeated variables
 * and with maximal lengths far above the list length.
 */
class SequenceStretchTest {

  /** One random instance; list[j] is the index of the variable at position j of the sequence. */
  record Instance(int[][] domains, int[] list, int[] set, int q, int min, int max) {

    boolean holds(int[] values) {
      int n = list.length;
      for (int i = 0; i + q <= n; i++) {
        int count = 0;
        for (int j = i; j < i + q; j++) {
          if (inSet(values[list[j]])) {
            count++;
          }
        }
        if (count < min || count > max) {
          return false;
        }
      }
      return true;
    }

    boolean inSet(int v) {
      return Arrays.stream(set).anyMatch(s -> s == v);
    }

    IntervalDomain setDomain() {
      IntervalDomain d = new IntervalDomain();
      for (int v : set) {
        d.unionAdapt(v, v);
      }
      return d;
    }

    @Override
    public String toString() {
      return "domains="
          + Arrays.deepToString(domains)
          + " list="
          + Arrays.toString(list)
          + " set="
          + Arrays.toString(set)
          + " q="
          + q
          + " min="
          + min
          + " max="
          + max;
    }
  }

  private static Instance random(Random random, int maxLength, boolean repeated) {
    int n = 1 + random.nextInt(maxLength);
    int vars = repeated ? 1 + random.nextInt(n) : n;
    int[][] domains = new int[vars][];
    for (int i = 0; i < vars; i++) {
      domains[i] = domain(random, 0, 4);
    }
    int[] list = new int[n];
    for (int j = 0; j < n; j++) {
      list[j] = repeated ? random.nextInt(vars) : j;
    }
    // sets with holes, empty sets and sets beyond the domains
    List<Integer> set = new ArrayList<>();
    for (int v = -1; v <= 6; v++) {
      if (random.nextInt(3) == 0) {
        set.add(v);
      }
    }
    int q = 1 + random.nextInt(n + 1);
    // mostly sensible bounds, sometimes min > max, min < 0 or max > q
    int min = random.nextInt(q + 3) - 1;
    int max = random.nextInt(5) == 0 ? random.nextInt(q + 3) - 1 : min + random.nextInt(q + 1);
    return new Instance(
        domains, list, set.stream().mapToInt(Integer::intValue).toArray(), q, min, max);
  }

  private static int[] domain(Random random, int lo, int hi) {
    List<Integer> values = new ArrayList<>();
    for (int v = lo; v <= hi; v++) {
      if (random.nextInt(3) != 0) {
        values.add(v);
      }
    }
    if (values.isEmpty()) {
      values.add(lo + random.nextInt(hi - lo + 1));
    }
    return values.stream().mapToInt(Integer::intValue).toArray();
  }

  private static IntVar[] variables(Store store, int[][] domains) {
    IntVar[] x = new IntVar[domains.length];
    for (int i = 0; i < x.length; i++) {
      IntervalDomain d = new IntervalDomain();
      for (int v : domains[i]) {
        d.unionAdapt(v, v);
      }
      x[i] = new IntVar(store, "x" + i, d);
    }
    return x;
  }

  private static IntVar[] sequence(IntVar[] x, int[] list) {
    return Arrays.stream(list).mapToObj(j -> x[j]).toArray(IntVar[]::new);
  }

  private static void bruteForce(
      Instance instance, int[][] domains, int[] values, int index, Set<List<Integer>> solutions) {
    if (index == values.length) {
      if (instance.holds(values)) {
        solutions.add(Arrays.stream(values).boxed().toList());
      }
      return;
    }
    for (int v : domains[index]) {
      values[index] = v;
      bruteForce(instance, domains, values, index + 1, solutions);
    }
  }

  private static Set<List<Integer>> allSolutions(Instance instance, int seed, boolean decomposed) {
    Store store = new Store();
    IntVar[] x = variables(store, instance.domains());
    IntVar[] list = sequence(x, instance.list());
    if (decomposed) {
      store.imposeDecomposition(
          new Sequence(list, instance.setDomain(), instance.q(), instance.min(), instance.max()));
    } else {
      store.impose(
          new AmongSeq(list, instance.setDomain(), instance.q(), instance.min(), instance.max()));
    }
    return allSolutions(store, x, seed);
  }

  private static Set<List<Integer>> allSolutions(Store store, IntVar[] x, int seed) {
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
    search.labeling(store, new SimpleSelect<>(x, null, new IndomainRandom<>(seed)));
    return found;
  }

  @Test
  void allSolutionsMatchBruteForce() {
    Random random = new Random(26);
    for (int trial = 0; trial < 3000; trial++) {
      Instance instance = random(random, 8, trial % 3 == 0);
      Set<List<Integer>> expected = new HashSet<>();
      bruteForce(instance, instance.domains(), new int[instance.domains().length], 0, expected);
      assertThat(allSolutions(instance, random.nextInt(), trial % 2 == 0))
          .as("trial %d %s", trial, instance)
          .isEqualTo(expected);
    }
  }

  private static int[][] currentDomains(IntVar[] x) {
    int[][] domains = new int[x.length][];
    for (int i = 0; i < x.length; i++) {
      domains[i] = new int[x[i].getSize()];
      ValueEnumeration e = x[i].dom().valueEnumeration();
      int k = 0;
      while (e.hasMoreElements()) {
        domains[i][k++] = e.nextElement();
      }
    }
    return domains;
  }

  /** It checks that after propagation every value has a support and that no solution is lost. */
  @Test
  void domainConsistentAtDiveNodes() {
    Random random = new Random(27);
    int nodes = 0;
    for (int trial = 0; trial < 1000; trial++) {
      Instance instance = random(random, 8, false);
      Store store = new Store();
      IntVar[] x = variables(store, instance.domains());
      store.impose(
          new AmongSeq(
              sequence(x, instance.list()),
              instance.setDomain(),
              instance.q(),
              instance.min(),
              instance.max()));

      while (true) {
        Set<List<Integer>> solutions = new HashSet<>();
        int[][] before = currentDomains(x);
        bruteForce(instance, before, new int[x.length], 0, solutions);
        boolean consistent = store.consistency();
        nodes++;
        assertThat(consistent)
            .as("trial %d %s at %s", trial, instance, Arrays.deepToString(before))
            .isEqualTo(!solutions.isEmpty());
        if (!consistent) {
          break;
        }
        // every remaining value appears in a solution
        int[][] after = currentDomains(x);
        for (int i = 0; i < x.length; i++) {
          int position = i;
          Set<Integer> supported = new HashSet<>();
          solutions.forEach(s -> supported.add(s.get(position)));
          for (int v : after[i]) {
            assertThat(supported)
                .as(
                    "trial %d %s at %s: x%d = %d",
                    trial, instance, Arrays.deepToString(after), i, v)
                .contains(v);
          }
        }
        List<Integer> open = new ArrayList<>();
        for (int i = 0; i < x.length; i++) {
          if (!x[i].singleton()) {
            open.add(i);
          }
        }
        if (open.isEmpty()) {
          break;
        }
        IntVar v = x[open.get(random.nextInt(open.size()))];
        int value = after[Arrays.asList(x).indexOf(v)][random.nextInt(v.getSize())];
        store.setLevel(store.level + 1);
        switch (random.nextInt(4)) {
          case 0:
            v.domain.in(store.level, v, value, value);
            break;
          case 1:
            v.domain.inComplement(store.level, v, value);
            break;
          case 2:
            v.domain.in(store.level, v, v.min(), Math.max(v.min(), value));
            break;
          default:
            v.domain.in(store.level, v, Math.min(v.max(), value), v.max());
            break;
        }
      }
    }
    assertThat(nodes).isGreaterThan(1500);
  }

  private static long[] tree(
      IntVar[] x, Function<IntVar[], List<Constraint>> constraints, int[] order) {
    Store store = x[0].getStore();
    for (Constraint c : constraints.apply(x)) {
      store.impose(c);
    }
    if (!store.consistency()) {
      return new long[] {0, 0};
    }
    IntVar[] vars = Arrays.stream(order).mapToObj(i -> x[i]).toArray(IntVar[]::new);
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, new SimpleSelect<>(vars, null, new IndomainMin<>()));
    return new long[] {search.getNodes(), search.getSolutionListener().solutionsNo()};
  }

  /**
   * Both AmongSeq and the Regular decomposition are domain consistent, so the same search must
   * visit the same nodes. The variable order is random, so windows are not filled left to right.
   */
  @Test
  void sameTreeAsRegularDecomposition() {
    Random random = new Random(28);
    for (int trial = 0; trial < 150; trial++) {
      int n = 8 + random.nextInt(5);
      int[][] domains = new int[n][];
      for (int i = 0; i < n; i++) {
        domains[i] = domain(random, 0, 3);
      }
      int q = 2 + random.nextInt(n - 1);
      int min = random.nextInt(q);
      int max = min + random.nextInt(q - min + 1);
      IntervalDomain set = random.nextBoolean() ? new IntervalDomain(0, 1) : new IntervalDomain();
      if (set.isEmpty()) {
        set.unionAdapt(0, 0);
        set.unionAdapt(2, 2);
      }
      List<Integer> shuffled = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        shuffled.add(i);
      }
      Collections.shuffle(shuffled, random);
      int[] order = shuffled.stream().mapToInt(Integer::intValue).toArray();

      long[] regular =
          tree(
              variables(new Store(), domains),
              x -> Sequence.decomposeByRegular(new Sequence(x, set, q, min, max)),
              order);
      long[] amongSeq =
          tree(
              variables(new Store(), domains),
              x -> List.of(new AmongSeq(x, set, q, min, max)),
              order);
      assertThat(amongSeq)
          .as(
              "trial %d domains=%s set=%s q=%d min=%d max=%d",
              trial, Arrays.deepToString(domains), set, q, min, max)
          .isEqualTo(regular);
    }
  }

  @Test
  void repeatedVariableIsChecked() {
    // x, x, y with windows of 2 holding exactly one value from {1}: the window x, x holds 0 or 2
    // such values, so there is no solution although the root propagation does not see it
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 1);
    IntVar y = new IntVar(store, "y", 0, 1);
    store.impose(new AmongSeq(new IntVar[] {x, x, y}, new IntervalDomain(1, 1), 2, 1, 1));
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    boolean found =
        store.consistency()
            && search.labeling(
                store, new SimpleSelect<>(new IntVar[] {x, y}, null, new IndomainMin<>()));
    assertThat(found).isFalse();
  }

  private static boolean stretchHolds(int[] word, int[] values, int[] min, int[] max) {
    int i = 0;
    while (i < word.length) {
      int j = i;
      while (j < word.length && word[j] == word[i]) {
        j++;
      }
      int k = 0;
      while (k < values.length && values[k] != word[i]) {
        k++;
      }
      if (k == values.length || j - i < min[k] || j - i > max[k]) {
        return false;
      }
      i = j;
    }
    return true;
  }

  @Test
  void stretchMatchesBruteForceWithRepeatedVariablesAndLongMaxima() {
    Random random = new Random(29);
    for (int trial = 0; trial < 2000; trial++) {
      int n = 1 + random.nextInt(7);
      int vars = trial % 2 == 0 ? n : 1 + random.nextInt(n);
      int[][] domains = new int[vars][];
      for (int i = 0; i < vars; i++) {
        domains[i] = domain(random, 1, 4);
      }
      int[] list = new int[n];
      for (int j = 0; j < n; j++) {
        list[j] = trial % 2 == 0 ? j : random.nextInt(vars);
      }
      int[] values = random.nextBoolean() ? new int[] {1, 2, 3} : new int[] {1, 3};
      int[] min = new int[values.length];
      int[] max = new int[values.length];
      for (int k = 0; k < values.length; k++) {
        min[k] = random.nextInt(4);
        max[k] = random.nextInt(5) == 0 ? 1_000_000_000 : min[k] + random.nextInt(4) - 1;
      }

      Set<List<Integer>> expected = new HashSet<>();
      enumerate(
          domains,
          new int[vars],
          0,
          values1 -> {
            int[] word = Arrays.stream(list).map(j -> values1[j]).toArray();
            if (stretchHolds(word, values, min, max)) {
              expected.add(Arrays.stream(values1).boxed().toList());
            }
          });

      Store store = new Store();
      IntVar[] x = variables(store, domains);
      store.imposeDecomposition(new Stretch(values, min, max, sequence(x, list)));
      assertThat(allSolutions(store, x, random.nextInt()))
          .as(
              "trial %d domains=%s list=%s values=%s min=%s max=%s",
              trial,
              Arrays.deepToString(domains),
              Arrays.toString(list),
              Arrays.toString(values),
              Arrays.toString(min),
              Arrays.toString(max))
          .isEqualTo(expected);
    }
  }

  private static void enumerate(int[][] domains, int[] values, int index, Consumer<int[]> action) {
    if (index == values.length) {
      action.accept(values);
      return;
    }
    for (int v : domains[index]) {
      values[index] = v;
      enumerate(domains, values, index + 1, action);
    }
  }
}
