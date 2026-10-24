/*
 * SatWrapperTest.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.satwrapper;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XneqY;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.InputOrderSelect;
import org.jacop.search.SelectChoicePoint;
import org.junit.jupiter.api.Test;

/**
 * Tests of {@link SatWrapper}: random clauses over boolean and small integer variables, mixed with
 * CP constraints, solved by CP search with all solutions counted and compared with brute force.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class SatWrapperTest {

  private static final int INT_MAX = 3;

  /** A clause literal: variable index, kind (0 is x=1 for booleans, 1 is y=v, 2 is y<=v), sign. */
  private record Lit(int var, int kind, int value, boolean positive) {

    boolean holds(int[] assignment) {
      int x = assignment[var];
      boolean atom =
          switch (kind) {
            case 0 -> x == 1;
            case 1 -> x == value;
            default -> x <= value;
          };
      return atom == positive;
    }
  }

  /** A CP constraint between two variables: 0 is x != y, 1 is x < y. */
  private record Pair(int x, int y, int kind) {

    boolean holds(int[] assignment) {
      return kind == 0 ? assignment[x] != assignment[y] : assignment[x] < assignment[y];
    }
  }

  private static long bruteForce(int[] max, List<Lit[]> clauses, List<Pair> pairs) {
    int[] a = new int[max.length];
    long count = 0;
    while (true) {
      if (clauses.stream().allMatch(c -> anyHolds(c, a))
          && pairs.stream().allMatch(p -> p.holds(a))) {
        count++;
      }
      int i = 0;
      while (i < a.length && a[i] == max[i]) {
        a[i++] = 0;
      }
      if (i == a.length) {
        return count;
      }
      a[i]++;
    }
  }

  private static boolean anyHolds(Lit[] clause, int[] assignment) {
    for (Lit l : clause) {
      if (l.holds(assignment)) {
        return true;
      }
    }
    return false;
  }

  private static long countWithWrapper(
      int[] max, List<Lit[]> clauses, List<Pair> pairs, boolean random, long seed) {
    Store store = new Store();
    IntVar[] vars = new IntVar[max.length];
    SatWrapper wrapper = new SatWrapper();
    store.impose(wrapper);
    for (int i = 0; i < max.length; i++) {
      vars[i] =
          max[i] == 1 ? new BooleanVar(store, "b" + i) : new IntVar(store, "y" + i, 0, max[i]);
      wrapper.register(vars[i]);
    }
    for (Lit[] clause : clauses) {
      int[] c = new int[clause.length];
      for (int k = 0; k < clause.length; k++) {
        Lit l = clause[k];
        int boolVar =
            wrapper.cpVarToBoolVar(vars[l.var()], l.kind() == 0 ? 1 : l.value(), l.kind() != 2);
        c[k] = l.positive() ? boolVar : -boolVar;
      }
      wrapper.addModelClause(c);
    }
    for (Pair p : pairs) {
      if (p.kind() == 0) {
        store.impose(new XneqY(vars[p.x()], vars[p.y()]));
      } else {
        store.impose(new XltY(vars[p.x()], vars[p.y()]));
      }
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> select =
        new InputOrderSelect<>(
            store, vars, random ? new IndomainRandom<>((int) seed) : new IndomainMin<>());
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.setPrintInfo(false);
    search.labeling(store, select);
    return search.getSolutionListener().solutionsNo();
  }

  @Test
  void solutionCountsAgreeWithBruteForce() {
    Random rnd = new Random(3);
    for (int run = 0; run < 1500; run++) {
      int numBools = 1 + rnd.nextInt(6);
      int numInts = rnd.nextInt(4);
      int[] max = new int[numBools + numInts];
      for (int i = 0; i < max.length; i++) {
        max[i] = i < numBools ? 1 : INT_MAX;
      }
      List<Lit[]> clauses = new ArrayList<>();
      int numClauses = 1 + rnd.nextInt(4 * max.length);
      for (int c = 0; c < numClauses; c++) {
        Lit[] clause = new Lit[1 + rnd.nextInt(3)];
        for (int k = 0; k < clause.length; k++) {
          int v = rnd.nextInt(max.length);
          int kind = max[v] == 1 ? 0 : 1 + rnd.nextInt(2);
          clause[k] = new Lit(v, kind, rnd.nextInt(INT_MAX + 1), rnd.nextBoolean());
        }
        clauses.add(clause);
      }
      List<Pair> pairs = new ArrayList<>();
      for (int p = rnd.nextInt(3); p > 0 && max.length > 1; p--) {
        int x = rnd.nextInt(max.length);
        int y = rnd.nextInt(max.length);
        if (x != y) {
          pairs.add(new Pair(x, y, rnd.nextInt(2)));
        }
      }
      long expected = bruteForce(max, clauses, pairs);
      assertEquals(expected, countWithWrapper(max, clauses, pairs, false, 0), "run " + run);
      assertEquals(expected, countWithWrapper(max, clauses, pairs, true, run), "random run " + run);
    }
  }
}
