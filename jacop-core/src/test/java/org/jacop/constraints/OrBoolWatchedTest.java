/*
 * OrBoolWatchedTest.java
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

import java.util.Random;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Checks {@link OrBoolWatched} against {@link OrBoolVector} and {@code Not(OrBoolVector)}: both
 * propagate the disjunction fully, so the same search over the same side constraints must visit the
 * same tree and find the same solutions.
 */
class OrBoolWatchedTest {

  /** Counts of one full search: solutions, nodes and failures. */
  private record Run(int solutions, long nodes, long failures) {}

  private static Run search(long seed, boolean watched) {
    Random rnd = new Random(seed);
    int n = 1 + rnd.nextInt(9);
    boolean negated = rnd.nextBoolean();
    Store store = new Store();
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
    }
    IntVar r = new IntVar(store, "r", 0, 1);
    IntVar[] all = new IntVar[n + 1];
    System.arraycopy(x, 0, all, 0, n);
    all[n] = r;

    // a list with a repeated variable, as the FlatZinc front end may hand over
    IntVar[] list = new IntVar[n + (n > 1 ? 1 : 0)];
    System.arraycopy(x, 0, list, 0, n);
    if (n > 1) {
      list[n] = x[rnd.nextInt(n)];
    }
    if (watched) {
      store.impose(new OrBoolWatched(list, r, negated));
    } else if (negated) {
      store.impose(new Not(new OrBoolVector(list, r)));
    } else {
      store.impose(new OrBoolVector(list, r));
    }

    // random side constraints, so that variables get fixed by propagation and not only by search
    int sides = rnd.nextInt(4);
    for (int k = 0; k < sides; k++) {
      IntVar a = all[rnd.nextInt(n + 1)];
      IntVar b = all[rnd.nextInt(n + 1)];
      if (a == b) {
        continue;
      }
      switch (rnd.nextInt(3)) {
        case 0 -> store.impose(new XneqY(a, b));
        case 1 -> store.impose(new XlteqY(a, b));
        default -> store.impose(new OrBoolSimple(a, b, new IntVar(store, 1, 1)));
      }
    }

    // shuffle the search order, the same for both runs
    IntVar[] order = all.clone();
    for (int i = order.length - 1; i > 0; i--) {
      int j = rnd.nextInt(i + 1);
      IntVar t = order[i];
      order[i] = order[j];
      order[j] = t;
    }
    long valueSeed = rnd.nextLong();

    if (!store.consistency()) {
      return new Run(0, 0, 0);
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(true);
    SimpleSelect<IntVar> select =
        new SimpleSelect<>(
            order,
            null,
            rnd.nextBoolean() ? new IndomainMin<>() : new IndomainRandom<>((int) valueSeed));
    search.labeling(store, select);
    int solutions = search.getSolutionListener().solutionsNo();
    for (int s = 1; s <= solutions; s++) {
      int[] value = new int[order.length];
      for (int i = 0; i < order.length; i++) {
        value[i] = ((org.jacop.core.IntDomain) search.getSolution(s)[i]).value();
      }
      boolean any = false;
      int rv = 0;
      for (int i = 0; i < order.length; i++) {
        if (order[i] == r) {
          rv = value[i];
        } else if (value[i] == 1) {
          any = true;
        }
      }
      assertThat(rv == 1).as("seed %d solution %d", seed, s).isEqualTo(any != negated);
    }
    return new Run(solutions, search.getNodes(), search.getWrongDecisions());
  }

  @Test
  void sameTreeAsOrBoolVector() {
    for (long seed = 0; seed < 3000; seed++) {
      Run reference = search(seed, false);
      Run watched = search(seed, true);
      assertThat(watched).as("seed %d", seed).isEqualTo(reference);
    }
  }

  @Test
  void lastNonZeroVariableIsSetWhenTheDisjunctionMustHold() {
    Store store = new Store();
    IntVar[] x = new IntVar[5];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
    }
    IntVar r = new IntVar(store, "r", 0, 1);
    store.impose(new OrBoolWatched(x, r, true));
    assertThat(store.consistency()).isTrue();

    store.setLevel(1);
    r.domain.inValue(store.level, r, 0);
    for (int i = 0; i < 4; i++) {
      x[i].domain.inValue(store.level, x[i], 0);
    }
    assertThat(store.consistency()).isTrue();
    assertThat(x[4].min()).isEqualTo(1);
    store.removeLevel(1);
    store.setLevel(0);

    // after backtracking the watches must still see every variable
    store.setLevel(1);
    for (int i = 1; i < 5; i++) {
      x[i].domain.inValue(store.level, x[i], 0);
    }
    assertThat(store.consistency()).isTrue();
    assertThat(r.singleton()).isFalse();
    x[0].domain.inValue(store.level, x[0], 0);
    assertThat(store.consistency()).isTrue();
    assertThat(r.value()).isEqualTo(1);
  }

  @Test
  void variableSelectionsSeeTheConstraintAsAttached() {
    Store reference = new Store();
    IntVar[] y = new IntVar[4];
    for (int i = 0; i < y.length; i++) {
      y[i] = new IntVar(reference, "y" + i, 0, 1);
    }
    reference.impose(new Not(new OrBoolVector(y, new IntVar(reference, "s", 0, 1))));

    Store store = new Store();
    IntVar[] x = new IntVar[4];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 1);
    }
    OrBoolWatched c = new OrBoolWatched(x, new IntVar(store, "r", 0, 1), true);
    store.impose(c);
    assertThat(store.consistency()).isTrue();

    for (int i = 0; i < x.length; i++) {
      assertThat(x[i].sizeConstraintsOriginal()).isEqualTo(y[i].sizeConstraintsOriginal());
      assertThat(x[i].constraintsWithWatches()).containsExactly(c);
    }
    // a value watch of 0 does not count the constraint twice
    store.setLevel(1);
    x[0].domain.inValue(store.level, x[0], 0);
    assertThat(store.consistency()).isTrue();
    for (IntVar v : x) {
      assertThat(v.constraintsWithWatches()).containsExactly(c);
    }
  }
}
