/*
 * MddTest.java
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
import static org.assertj.core.api.Assertions.assertThatThrownBy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.IntStream;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ExtensionalSupportMdd;
import org.jacop.constraints.ExtensionalSupportStr;
import org.jacop.constraints.XeqC;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.jacop.util.Mdd;
import org.junit.jupiter.api.Test;

/**
 * Tests of the MDD constraint {@link ExtensionalSupportMdd}, given as an {@link Mdd} built from a
 * table or as a layered graph in the MiniZinc form, against brute force enumeration and against a
 * domain consistent decomposition.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class MddTest {

  /** A diagram in the MiniZinc form: node 1 is the root and node 0 the terminal node. */
  private record Diagram(int levels, int[] level, int[] from, IntDomain[] label, int[] to) {

    /** It follows all paths labelled with the word, as the diagram may be non-deterministic. */
    boolean accepts(int[] word) {
      Set<Integer> current = Set.of(1);
      for (int i = 0; i < levels; i++) {
        Set<Integer> next = new HashSet<>();
        for (int e = 0; e < from.length; e++) {
          if (current.contains(from[e]) && label[e].contains(word[i])) {
            next.add(to[e]);
          }
        }
        current = next;
      }
      return current.contains(0);
    }

    ExtensionalSupportMdd constraint(IntVar[] x) {
      return new ExtensionalSupportMdd(x, level, from, label, to);
    }
  }

  /**
   * A random layered diagram with width nodes on each inner level. Edges are labelled with one or
   * more values of 0..3, sometimes with a value outside the domains, and several edges leaving a
   * node may share values. Some nodes have no outgoing or no incoming edges.
   */
  private static Diagram randomDiagram(Random random, int levels, int width, int edgesPerNode) {
    List<Integer> level = new ArrayList<>();
    level.add(1);
    int[][] nodesOfLevel = new int[levels + 1][];
    nodesOfLevel[0] = new int[] {1};
    nodesOfLevel[levels] = new int[] {0};
    for (int l = 1; l < levels; l++) {
      int count = 1 + random.nextInt(width);
      nodesOfLevel[l] = new int[count];
      for (int k = 0; k < count; k++) {
        level.add(l + 1);
        nodesOfLevel[l][k] = level.size();
      }
    }
    List<Integer> from = new ArrayList<>();
    List<IntDomain> label = new ArrayList<>();
    List<Integer> to = new ArrayList<>();
    for (int l = 0; l < levels; l++) {
      for (int node : nodesOfLevel[l]) {
        for (int k = random.nextInt(edgesPerNode + 1); k > 0; k--) {
          IntervalDomain values = new IntervalDomain();
          for (int v = 0; v < 4; v++) {
            if (random.nextInt(3) == 0) {
              values.unionAdapt(v, v);
            }
          }
          if (random.nextInt(10) == 0) {
            values.unionAdapt(7, 7);
          }
          if (values.isEmpty()) {
            int low = random.nextInt(4);
            values.unionAdapt(low, low + random.nextInt(2));
          }
          int[] targets = nodesOfLevel[l + 1];
          from.add(node);
          label.add(values);
          to.add(targets[random.nextInt(targets.length)]);
        }
      }
    }
    return new Diagram(
        levels,
        level.stream().mapToInt(Integer::intValue).toArray(),
        from.stream().mapToInt(Integer::intValue).toArray(),
        label.toArray(new IntDomain[0]),
        to.stream().mapToInt(Integer::intValue).toArray());
  }

  private static int[][] randomTable(Random random, int arity, int size, int values) {
    Set<List<Integer>> tuples = new HashSet<>();
    for (int k = 0; k < size; k++) {
      List<Integer> tuple = new ArrayList<>();
      for (int i = 0; i < arity; i++) {
        tuple.add(random.nextInt(values));
      }
      tuples.add(tuple);
    }
    return tuples.stream()
        .map(t -> t.stream().mapToInt(Integer::intValue).toArray())
        .toArray(int[][]::new);
  }

  // The constraint on random diagrams and tables must keep every domain equal to the values that
  // appear in some allowed tuple, after each pruning step of a dive and after backtracking out of
  // it, must fail exactly when no allowed tuple remains, and must be satisfied when ground.
  @Test
  void mddIsDomainConsistentAcrossBacktracking() {

    Random random = new Random(5);
    for (int trial = 0; trial < 600; trial++) {
      int n = 1 + random.nextInt(6);
      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 3);
        if (random.nextInt(4) == 0) {
          x[i].domain.inComplement(0, x[i], random.nextInt(4));
        }
      }
      Predicate<int[]> allowed;
      ExtensionalSupportMdd mdd;
      String instance;
      if (trial % 2 == 0) {
        Diagram diagram = randomDiagram(random, n, 4, 3);
        allowed = diagram::accepts;
        mdd = diagram.constraint(x);
        instance =
            "trial "
                + trial
                + " level "
                + Arrays.toString(diagram.level())
                + " from "
                + Arrays.toString(diagram.from())
                + " label "
                + Arrays.toString(diagram.label())
                + " to "
                + Arrays.toString(diagram.to());
      } else {
        int[][] table = randomTable(random, n, random.nextInt(20), 4);
        Set<List<Integer>> tuples = new HashSet<>();
        for (int[] t : table) {
          tuples.add(Arrays.stream(t).boxed().toList());
        }
        allowed = w -> tuples.contains(Arrays.stream(w).boxed().toList());
        mdd = new ExtensionalSupportMdd(x, table);
        instance = "trial " + trial + " table " + Arrays.deepToString(table);
      }
      mdd.setPropagation(propagation(trial / 2));
      instance += " " + propagation(trial / 2);
      store.impose(mdd);

      List<String> domainsAtLevel = new ArrayList<>();
      boolean consistent = store.consistency();
      assertDomainConsistent(x, allowed, consistent, instance);
      while (consistent) {
        domainsAtLevel.add(Arrays.toString(x));
        List<IntVar> free = Arrays.stream(x).filter(v -> !v.singleton()).toList();
        if (free.isEmpty()) {
          assertThat(mdd.satisfied()).as(instance).isTrue();
          break;
        }
        assertThat(mdd.satisfied()).as(instance).isFalse();
        IntVar v = free.get(random.nextInt(free.size()));
        int[] values = valuesOf(v);
        store.setLevel(store.level + 1);
        v.domain.inComplement(store.level, v, values[random.nextInt(values.length)]);
        consistent = store.consistency();
        assertDomainConsistent(x, allowed, consistent, instance);
      }
      // Backtrack level by level; domains must come back and propagation must still be correct.
      while (store.level > 0) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
        if (store.level < domainsAtLevel.size()) {
          assertThat(Arrays.toString(x)).as(instance).isEqualTo(domainsAtLevel.get(store.level));
        }
        List<IntVar> free = Arrays.stream(x).filter(v -> !v.singleton()).toList();
        if (!free.isEmpty() && random.nextBoolean()) {
          IntVar v = free.get(random.nextInt(free.size()));
          store.setLevel(store.level + 1);
          v.domain.in(store.level, v, v.min(), v.min());
          assertDomainConsistent(x, allowed, store.consistency(), instance);
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
          if (store.level < domainsAtLevel.size()) {
            assertThat(Arrays.toString(x)).as(instance).isEqualTo(domainsAtLevel.get(store.level));
          }
        }
      }
    }
  }

  // On diagrams large enough for the propagator to remove nodes a level at a time and to compact
  // its adjacency arrays, the domains must equal those of a domain consistent reference: for a
  // diagram, its decomposition into a chain of ternary tables over node variables (Berge-acyclic),
  // for a table, the STR propagator on the same table. Both stores take the same random dives and
  // backtrack out of them again and again.
  @Test
  void mddMatchesReferenceOnLargeDiagrams() {

    Random random = new Random(13);
    for (int trial = 0; trial < 12; trial++) {
      Store mddStore = new Store();
      Store referenceStore = new Store();
      int n;
      IntVar[] x;
      IntVar[] y;
      if (trial % 2 == 0) {
        n = 30 + random.nextInt(20);
        Diagram diagram = randomDiagram(random, n, 300, 4);
        x = variables(mddStore, n, 3);
        y = variables(referenceStore, n, 3);
        ExtensionalSupportMdd mdd = diagram.constraint(x);
        mdd.setPropagation(propagation(trial / 2));
        mddStore.impose(mdd);
        imposeChainDecomposition(referenceStore, diagram, y);
      } else {
        n = 12 + random.nextInt(3);
        int[][] table = randomTable(random, n, 12000 + random.nextInt(8000), 5);
        x = variables(mddStore, n, 4);
        y = variables(referenceStore, n, 4);
        ExtensionalSupportMdd mdd = new ExtensionalSupportMdd(x, table);
        mdd.setPropagation(propagation(trial / 2));
        mddStore.impose(mdd);
        referenceStore.impose(new ExtensionalSupportStr(y, table));
      }
      String instance = "trial " + trial + " " + propagation(trial / 2);
      boolean rootConsistent = mddStore.consistency();
      assertThat(rootConsistent).as(instance).isEqualTo(referenceStore.consistency());
      if (!rootConsistent) {
        continue;
      }
      assertThat(Arrays.toString(x)).as(instance).isEqualTo(Arrays.toString(y));

      // Level 1 fixes some of the variables, so many edges are removed below it.
      mddStore.setLevel(1);
      referenceStore.setLevel(1);
      for (int i = 0; i < n / 4; i++) {
        int[] values = valuesOf(x[i]);
        int value = values[random.nextInt(values.length)];
        x[i].domain.in(1, x[i], value, value);
        y[i].domain.in(1, y[i], value, value);
        assertThat(mddStore.consistency()).as(instance).isTrue();
        assertThat(referenceStore.consistency()).as(instance).isTrue();
      }
      assertThat(Arrays.toString(x)).as(instance).isEqualTo(Arrays.toString(y));

      for (int dive = 0; dive < 200; dive++) {
        int base = mddStore.level;
        String atBase = Arrays.toString(x);
        boolean consistent = true;
        while (consistent) {
          List<Integer> free =
              IntStream.range(0, n).filter(i -> !x[i].singleton()).boxed().toList();
          if (free.isEmpty()) {
            break;
          }
          int i = free.get(random.nextInt(free.size()));
          int[] values = valuesOf(x[i]);
          int value = values[random.nextInt(values.length)];
          mddStore.setLevel(mddStore.level + 1);
          referenceStore.setLevel(referenceStore.level + 1);
          if (random.nextInt(5) == 0) {
            x[i].domain.in(mddStore.level, x[i], value, value);
            y[i].domain.in(referenceStore.level, y[i], value, value);
          } else {
            x[i].domain.inComplement(mddStore.level, x[i], value);
            y[i].domain.inComplement(referenceStore.level, y[i], value);
          }
          consistent = mddStore.consistency();
          assertThat(consistent).as(instance).isEqualTo(referenceStore.consistency());
          if (consistent) {
            assertThat(Arrays.toString(x)).as(instance).isEqualTo(Arrays.toString(y));
          }
        }
        // Backtrack to a random level below level 2, so that many dives share the subtree of
        // level 2, and sometimes to level 1, which removes that subtree.
        int deepest = mddStore.level;
        int target =
            deepest < 2 || random.nextInt(40) == 0
                ? Math.min(1, deepest)
                : 2 + random.nextInt(deepest - 1);
        while (mddStore.level > target) {
          mddStore.removeLevel(mddStore.level);
          mddStore.setLevel(mddStore.level - 1);
          referenceStore.removeLevel(referenceStore.level);
          referenceStore.setLevel(referenceStore.level - 1);
        }
        assertThat(Arrays.toString(x)).as(instance).isEqualTo(Arrays.toString(y));
        if (target == base) {
          assertThat(Arrays.toString(x)).as(instance).isEqualTo(atBase);
        }
      }
    }
  }

  // The same diagram array reused for other variables (the constructor copied the variables onto
  // themselves, so the constraint had no variables), and constraints sharing variables in a
  // search, must find exactly the solutions of brute force enumeration.
  @Test
  void mddFromDiagramArrayFindsAllSolutions() {

    Random random = new Random(3);
    for (int trial = 0; trial < 30; trial++) {
      int n = 7;
      int[][] first = randomTable(random, 4, 40, 3);
      int[][] second = randomTable(random, 4, 40, 3);
      Store store = new Store();
      IntVar[] x = variables(store, n, 2);
      Mdd built = new Mdd(new IntVar[] {x[0], x[1], x[2], x[3]}, first);
      ExtensionalSupportMdd firstMdd = new ExtensionalSupportMdd(built);
      firstMdd.setPropagation(propagation(trial));
      store.impose(firstMdd);
      IntVar[] scope = {x[3], x[4], x[5], x[6]};
      Mdd reused = new Mdd(scope, new Mdd(scope, second).diagram, new int[] {3, 3, 3, 3});
      ExtensionalSupportMdd secondMdd = new ExtensionalSupportMdd(reused);
      secondMdd.setPropagation(propagation(trial + 1));
      store.impose(secondMdd);
      Set<List<Integer>> a = new HashSet<>();
      Set<List<Integer>> b = new HashSet<>();
      Arrays.stream(first).forEach(t -> a.add(Arrays.stream(t).boxed().toList()));
      Arrays.stream(second).forEach(t -> b.add(Arrays.stream(t).boxed().toList()));

      long expected =
          bruteForce(
                  x,
                  w ->
                      a.contains(List.of(w[0], w[1], w[2], w[3]))
                          && b.contains(List.of(w[3], w[4], w[5], w[6])))
              .size();
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      search.labeling(store, new InputOrderSelect<>(store, x, new IndomainMin<>()));
      assertThat((long) search.getSolutionListener().solutionsNo())
          .as("trial " + trial)
          .isEqualTo(expected);
    }
  }

  @Test
  void mddRejectsEdgesThatSkipALevel() {
    Store store = new Store();
    IntVar[] x = variables(store, 3, 1);
    IntDomain one = new IntervalDomain(1, 1);
    assertThatThrownBy(
            () ->
                new ExtensionalSupportMdd(
                    x,
                    new int[] {1, 2},
                    new int[] {1, 2},
                    new IntDomain[] {one, one},
                    new int[] {2, 0}))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(
            () ->
                new ExtensionalSupportMdd(
                    x, new int[] {1}, new int[] {1}, new IntDomain[] {one}, new int[] {2}))
        .isInstanceOf(IllegalArgumentException.class);
  }

  /** It alternates between the two propagation algorithms. */
  private static ExtensionalSupportMdd.Propagation propagation(int i) {
    return i % 2 == 0
        ? ExtensionalSupportMdd.Propagation.INCREMENTAL
        : ExtensionalSupportMdd.Propagation.SUPPORT_SEARCH;
  }

  /**
   * It imposes the diagram as node variables q0..qn, with q0 the root and qn the terminal node, and
   * one ternary table (q_i, x_i, q_i+1) per level.
   */
  private static void imposeChainDecomposition(Store store, Diagram diagram, IntVar[] x) {
    int n = x.length;
    int nodes = diagram.level().length;
    List<List<int[]>> tuples = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      tuples.add(new ArrayList<>());
    }
    for (int e = 0; e < diagram.from().length; e++) {
      int level = diagram.level()[diagram.from()[e] - 1] - 1;
      for (ValueEnumeration v = diagram.label()[e].valueEnumeration(); v.hasMoreElements(); ) {
        tuples.get(level).add(new int[] {diagram.from()[e], v.nextElement(), diagram.to()[e]});
      }
    }
    IntVar[] q = new IntVar[n + 1];
    for (int i = 0; i <= n; i++) {
      q[i] = new IntVar(store, "q" + i, 0, nodes);
    }
    List<Constraint> constraints = new ArrayList<>();
    constraints.add(new XeqC(q[0], 1));
    constraints.add(new XeqC(q[n], 0));
    for (int i = 0; i < n; i++) {
      constraints.add(
          new ExtensionalSupportStr(
              new IntVar[] {q[i], x[i], q[i + 1]}, tuples.get(i).toArray(new int[0][])));
    }
    constraints.forEach(store::impose);
  }

  private static IntVar[] variables(Store store, int n, int max) {
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, max);
    }
    return x;
  }

  private static void assertDomainConsistent(
      IntVar[] x, Predicate<int[]> allowed, boolean consistent, String instance) {
    List<int[]> solutions = bruteForce(x, allowed);
    if (!consistent) {
      assertThat(solutions).as(instance + " failed with solutions").isEmpty();
      return;
    }
    assertThat(solutions).as(instance + " no solution " + Arrays.toString(x)).isNotEmpty();
    for (int i = 0; i < x.length; i++) {
      int position = i;
      int[] supported = solutions.stream().mapToInt(w -> w[position]).distinct().sorted().toArray();
      assertThat(valuesOf(x[i])).as(instance + " " + Arrays.toString(x)).containsExactly(supported);
    }
  }

  private static List<int[]> bruteForce(IntVar[] vars, Predicate<int[]> allowed) {
    List<int[]> solutions = new ArrayList<>();
    int[][] domains = Arrays.stream(vars).map(MddTest::valuesOf).toArray(int[][]::new);
    int[] index = new int[vars.length];
    while (true) {
      int[] assignment = new int[vars.length];
      for (int i = 0; i < vars.length; i++) {
        assignment[i] = domains[i][index[i]];
      }
      if (allowed.test(assignment)) {
        solutions.add(assignment);
      }
      int k = 0;
      while (k < vars.length && ++index[k] == domains[k].length) {
        index[k] = 0;
        k++;
      }
      if (k == vars.length) {
        return solutions;
      }
    }
  }

  private static int[] valuesOf(IntVar v) {
    int[] values = new int[v.getSize()];
    int k = 0;
    for (ValueEnumeration e = v.domain.valueEnumeration(); e.hasMoreElements(); ) {
      values[k++] = e.nextElement();
    }
    return values;
  }
}
