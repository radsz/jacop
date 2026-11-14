/*
 * TableCoverTest.java
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

package org.jacop.constraints;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.table.Table;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Tests of {@link TableCover}: random tilings of groups with tables and an all different have the
 * solutions of the same model without the cover, which is redundant.
 */
class TableCoverTest {

  // cells 0..cells-1, groups of size 1..3 whose tuples are random sets of cells in random order
  private static final class Tiling {
    final int cells;
    final int[][][] tuples;

    Tiling(int cells, int[][][] tuples) {
      this.cells = cells;
      this.tuples = tuples;
    }
  }

  private static Tiling random(Random rnd) {
    int cells = 3 + rnd.nextInt(6);
    List<int[][]> groups = new ArrayList<>();
    int used = 0;
    while (used < cells) {
      int k = Math.min(cells - used, 1 + rnd.nextInt(3));
      int m = 1 + rnd.nextInt(6);
      int[][] t = new int[m][k];
      for (int r = 0; r < m; r++) {
        for (int j = 0; j < k; j++) {
          // a repeated value sometimes, which the all different rejects
          t[r][j] = rnd.nextInt(cells + (rnd.nextInt(8) == 0 ? 1 : 0));
        }
      }
      groups.add(t);
      used += k;
    }
    return new Tiling(cells, groups.toArray(new int[0][][]));
  }

  private static int solutions(Tiling t, boolean cover, boolean exact, Random rnd) {
    Store store = new Store();
    IntVar[][] groups = new IntVar[t.tuples.length][];
    List<IntVar> all = new ArrayList<>();
    for (int i = 0; i < groups.length; i++) {
      groups[i] = new IntVar[t.tuples[i][0].length];
      for (int j = 0; j < groups[i].length; j++) {
        groups[i][j] = new IntVar(store, "x" + i + "_" + j, 0, exact ? t.cells - 1 : t.cells);
        all.add(groups[i][j]);
      }
      store.impose(new Table(groups[i], t.tuples[i]));
    }
    IntVar[] x = all.toArray(new IntVar[0]);
    store.impose(new Alldistinct(x));
    if (cover) {
      store.impose(new TableCover(groups, t.tuples, exact));
    }
    if (!store.consistency()) {
      return 0;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, new SimpleSelect<>(x, null, new IndomainRandom<>(rnd.nextInt())));
    return search.getSolutionListener().solutionsNo();
  }

  @Test
  void randomTilingsKeepTheirSolutions() {
    Random rnd = new Random(20261108L);
    int nonZero = 0;
    for (int trial = 0; trial < 1500; trial++) {
      Tiling t = random(rnd);
      // exact: as many variables as cells, domains 0..cells-1; otherwise one cell more
      for (boolean exact : new boolean[] {true, false}) {
        int expected = solutions(t, false, exact, rnd);
        int found = solutions(t, true, exact, rnd);
        assertThat(found).as("trial %d exact %s", trial, exact).isEqualTo(expected);
        if (expected > 0) {
          nonZero++;
        }
      }
    }
    assertThat(nonZero).isGreaterThan(50);
  }
}
