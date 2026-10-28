/*
 * RandomAutomata.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2026 Radoslaw Szymanek
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

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.BooleanSupplier;
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

/** Random automata, costs and domains, and the search shared by the cost regular tests. */
final class RandomAutomata {

  private RandomAutomata() {}

  /** A random transition table; transitions are more likely than dead ends. */
  static int[][] transitions(Random random, int states, int symbols) {
    int[][] delta = new int[states][symbols];
    for (int[] row : delta) {
      for (int j = 0; j < symbols; j++) {
        row[j] = random.nextInt(4) == 0 ? -1 : random.nextInt(states);
      }
    }
    return delta;
  }

  /** A random set of accepting states, each with probability 2/3. */
  static int[] finals(Random random, int states) {
    List<Integer> finalList = new ArrayList<>();
    for (int q = 0; q < states; q++) {
      if (random.nextInt(3) != 0) {
        finalList.add(q);
      }
    }
    return finalList.stream().mapToInt(Integer::intValue).toArray();
  }

  /** Random costs in -2..spread-3 per state and symbol. */
  static int[][] costs(Random random, int states, int symbols, int spread) {
    int[][] c = new int[states][symbols];
    for (int[] row : c) {
      for (int j = 0; j < symbols; j++) {
        row[j] = random.nextInt(spread) - 2;
      }
    }
    return c;
  }

  static int[] range(int lo, int hi) {
    int[] values = new int[hi - lo + 1];
    for (int i = 0; i < values.length; i++) {
      values[i] = lo + i;
    }
    return values;
  }

  /** A random non-empty subset of lo..hi, so domains may have holes. */
  static int[] subset(Random random, int lo, int hi) {
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

  static IntVar[] variables(Store store, int[][] domains) {
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

  /**
   * All solutions of the store over x, labelling the variables in the given order with indomain min
   * (0), max (1) or random (2); satisfied must hold at every solution.
   */
  static Set<List<Integer>> solveAll(
      Store store,
      IntVar[] x,
      IntVar[] order,
      BooleanSupplier satisfied,
      int valueOrder,
      int seed) {
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
            assertTrue(satisfied.getAsBoolean(), "satisfied() at a solution");
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
    search.labeling(store, new SimpleSelect<>(order, null, indomain));
    return found;
  }

  /** It posts x = v, x != v, x <= v or x >= v for a random v within the bounds of x. */
  static void randomDecision(Store store, IntVar x, Random random) {
    int value = x.min() + random.nextInt(x.max() - x.min() + 1);
    switch (random.nextInt(4)) {
      case 0 -> x.domain.in(store.level, x, value, value);
      case 1 -> x.domain.inComplement(store.level, x, value);
      case 2 -> x.domain.inMax(store.level, x, value);
      default -> x.domain.inMin(store.level, x, value);
    }
  }

  /** With probability 1/4, it backtracks a random number of levels. */
  static void randomBacktrack(Store store, Random random) {
    if (store.level > 0 && random.nextInt(4) == 0) {
      int back = 1 + random.nextInt(store.level);
      for (int k = 0; k < back; k++) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }
    }
  }
}
