/*
 * MinOfSumsTest.java
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

package org.jacop.constraints;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.jacop.search.Search;
import org.junit.jupiter.api.Test;

/** MinOfSums against its decomposition z = x + y, m = min(z). */
class MinOfSumsTest {

  // a random instance: the domains of the pool variables and of m, and the terms over the pool
  private record Instance(int[][] domains, int[] tx, int[] ty) {}

  private static Instance instance(Random rnd, boolean holes) {
    int pool = 2 + rnd.nextInt(4);
    int[][] domains = new int[pool + 1][];
    for (int i = 0; i <= pool; i++) {
      int lo = rnd.nextInt(7) - 3;
      int hi = lo + rnd.nextInt(6);
      int hole = holes && hi - lo >= 2 && rnd.nextBoolean() ? lo + 1 + rnd.nextInt(hi - lo - 1) : 0;
      domains[i] = holes && hole != 0 ? new int[] {lo, hi, hole} : new int[] {lo, hi};
    }
    int n = 1 + rnd.nextInt(4);
    int[] tx = new int[n];
    int[] ty = new int[n];
    for (int i = 0; i < n; i++) {
      tx[i] = rnd.nextInt(pool);
      ty[i] = rnd.nextInt(3) == 0 ? -1 : rnd.nextInt(pool);
      if (ty[i] == tx[i]) {
        ty[i] = -1;
      }
    }
    return new Instance(domains, tx, ty);
  }

  // the store over the instance's variables, the pool first and m last
  private static IntVar[] variables(Store store, Instance in) {
    IntVar[] v = new IntVar[in.domains.length];
    for (int i = 0; i < v.length; i++) {
      int[] d = in.domains[i];
      IntervalDomain dom = new IntervalDomain(d[0], d[1]);
      if (d.length == 3) {
        dom.subtractAdapt(d[2]);
      }
      v[i] = new IntVar(store, "v" + i, dom);
    }
    return v;
  }

  private static void impose(Store store, IntVar[] v, Instance in, boolean decomposed) {
    IntVar m = v[v.length - 1];
    int n = in.tx.length;
    if (decomposed) {
      IntVar[] z = new IntVar[n];
      for (int i = 0; i < n; i++) {
        IntVar a = v[in.tx[i]];
        if (in.ty[i] < 0) {
          z[i] = a;
          continue;
        }
        IntVar b = v[in.ty[i]];
        z[i] = new IntVar(store, "z" + i, a.min() + b.min(), a.max() + b.max());
        store.impose(new XplusYeqZ(a, b, z[i]));
      }
      store.impose(new Min(z, m));
      return;
    }
    IntVar[] x = new IntVar[n];
    IntVar[] y = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = v[in.tx[i]];
      y[i] = in.ty[i] < 0 ? null : v[in.ty[i]];
    }
    store.impose(new MinOfSums(x, y, m));
  }

  private static int solutions(Instance in, boolean decomposed) {
    Store store = new Store();
    IntVar[] v = variables(store, in);
    impose(store, v, in, decomposed);
    if (!store.consistency()) {
      return 0;
    }
    Search<IntVar> search = new DepthFirstSearch<>();
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.setPrintInfo(false);
    if (!search.labeling(store, new InputOrderSelect<>(store, v, new IndomainMin<>()))) {
      return 0;
    }
    return search.getSolutionListener().solutionsNo();
  }

  @Test
  void hasTheSolutionsOfTheDecomposition() {
    Random rnd = new Random(7);
    for (int run = 0; run < 3000; run++) {
      Instance in = instance(rnd, true);
      assertThat(solutions(in, false)).as("run %d", run).isEqualTo(solutions(in, true));
    }
  }

  // the bounds of every variable after propagation at each step of a random descent, "fail" once
  // the store fails
  private static List<String> descent(Instance in, boolean decomposed, long seed) {
    Store store = new Store();
    IntVar[] v = variables(store, in);
    impose(store, v, in, decomposed);
    Random rnd = new Random(seed);
    List<String> trace = new ArrayList<>();
    for (int step = 0; step < 4; step++) {
      if (!store.consistency()) {
        trace.add("fail");
        return trace;
      }
      StringBuilder s = new StringBuilder();
      for (IntVar x : v) {
        s.append(x.min()).append("..").append(x.max()).append(' ');
      }
      trace.add(s.toString());
      IntVar x = v[rnd.nextInt(v.length)];
      int cut = x.min() + rnd.nextInt(x.max() - x.min() + 1);
      store.setLevel(store.level + 1);
      try {
        if (rnd.nextBoolean()) {
          x.domain.in(store.level, x, cut, IntDomain.MAX_INT);
        } else {
          x.domain.in(store.level, x, IntDomain.MIN_INT, cut);
        }
      } catch (org.jacop.core.FailException e) {
        trace.add("fail");
        return trace;
      }
    }
    return trace;
  }

  @Test
  void prunesTheBoundsOfTheDecomposition() {
    Random rnd = new Random(11);
    for (int run = 0; run < 3000; run++) {
      Instance in = instance(rnd, false);
      assertThat(descent(in, false, run)).as("run %d", run).isEqualTo(descent(in, true, run));
    }
  }

  @Test
  void rejectsTheMinimumInATerm() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 5);
    IntVar m = new IntVar(store, "m", 0, 5);
    org.assertj.core.api.Assertions.assertThatThrownBy(
            () -> new MinOfSums(new IntVar[] {a}, new IntVar[] {m}, m))
        .isInstanceOf(IllegalArgumentException.class);
  }
}
