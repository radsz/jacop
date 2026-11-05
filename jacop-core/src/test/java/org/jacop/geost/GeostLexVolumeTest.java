/*
 * GeostLexVolumeTest.java
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
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.BiFunction;
import org.jacop.constraints.geost.ExternalConstraint;
import org.jacop.constraints.geost.Geost;
import org.jacop.constraints.geost.GeostObject;
import org.jacop.constraints.geost.LexChain;
import org.jacop.constraints.geost.NonOverlapping;
import org.jacop.constraints.geost.Shape;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.geost.GeostInstance.Posted;
import org.jacop.geost.GeostInstance.Solutions;
import org.junit.jupiter.api.Test;

/** Checks Geost's volume reasoning and its lexicographic chain of objects. */
class GeostLexVolumeTest {

  /** A 1 x 1 object at x in xs and y in ys, in no time in particular. */
  static GeostObject object(Store store, int no, int shape, int[] xs, int[] ys) {
    IntVar[] coords = {
      new IntVar(store, "x" + no, xs[0], xs[1]), new IntVar(store, "y" + no, ys[0], ys[1])
    };
    return new GeostObject(
        no,
        coords,
        new IntVar(store, "s" + no, shape, shape),
        new IntVar(store, "t" + no, 0, 0),
        new IntVar(store, "d" + no, 1, 1),
        new IntVar(store, "e" + no, 1, 1));
  }

  static Geost geost(GeostObject[] objects, List<ExternalConstraint> more, Shape... shapes) {
    List<ExternalConstraint> ecs = new ArrayList<>();
    ecs.add(new NonOverlapping(objects, new int[] {0, 1}));
    ecs.addAll(more);
    return new Geost(objects, ecs.toArray(new ExternalConstraint[0]), shapes);
  }

  /**
   * Three 2 x 1 bars with x in 0..2 on one row: no bar has a compulsory part, so the sweep keeps
   * every place, but six cells do not fit in the four of the row.
   */
  @Test
  void volumeFailsWhenTheObjectsDoNotFitInTheirWindow() {
    for (boolean volume : new boolean[] {true, false}) {
      Store store = new Store();
      GeostObject[] bars = new GeostObject[3];
      for (int i = 0; i < 3; i++) {
        bars[i] = object(store, i, 0, new int[] {0, 2}, new int[] {0, 0});
      }
      Geost g = geost(bars, List.of(), new Shape(0, new int[] {0, 0}, new int[] {2, 1}));
      g.setVolumeReasoning(volume);
      store.impose(g);
      assertThat(store.consistency()).as("volume " + volume).isEqualTo(!volume);
    }
  }

  /**
   * The predecessor is fixed at (1, 1). At x = 1 the follower is either below it in y, which is
   * lexicographically smaller, or on it, so the sweep moves the follower's x to 2 (a separate lex
   * constraint on the bounds would keep x = 1).
   */
  @Test
  void lexChainRemovesValuesInsideTheSweep() {
    Store store = new Store();
    GeostObject first = object(store, 0, 0, new int[] {1, 1}, new int[] {1, 1});
    GeostObject second = object(store, 1, 0, new int[] {0, 2}, new int[] {0, 1});
    GeostObject[] objects = {first, second};
    Geost g =
        geost(
            objects,
            List.of(new LexChain(objects)),
            new Shape(0, new int[] {0, 0}, new int[] {1, 1}));
    store.impose(g);
    assertThat(store.consistency()).isTrue();
    assertThat(((IntVar) second.getVariables().get(0)).min()).isEqualTo(2);
    assertThat(g.canCopy()).isTrue();
  }

  /**
   * On corpus instances, Geost with a lex chain over all objects finds exactly the brute-force
   * solutions whose origins are in lexicographic order.
   */
  @Test
  void lexChainKeepsExactlyTheOrderedSolutions() throws IOException {
    BiFunction<GeostInstance, Store, Posted> withChain =
        (g, store) -> {
          IntVar[] vars = g.variables(store, false);
          List<GeostObject> objs = g.geostObjects(vars, GeostInstance.range(g.objects.size()));
          List<ExternalConstraint> ecs = new ArrayList<>(g.externalConstraints(objs));
          ecs.add(new LexChain(objs.toArray(new GeostObject[0])));
          Geost geost = new Geost(objs, ecs, g.geostShapes());
          store.impose(geost);
          return new Posted(vars, geost);
        };
    List<String> failures = new ArrayList<>();
    int checked = 0;
    for (GeostInstance g : GeostBruteForceTest.corpusInstances()) {
      if (g.objects.size() < 2 || checked >= 60) {
        continue;
      }
      Solutions all = g.bruteForce(true, GeostBruteForceTest.MAX_SOLUTIONS);
      if (all == null) {
        continue;
      }
      checked++;
      Set<List<Integer>> expected = new HashSet<>();
      for (List<Integer> s : all.all) {
        if (ordered(g, s)) {
          expected.add(s);
        }
      }
      for (int st = 0; st < GeostBruteForceTest.STRATEGIES; st++) {
        List<String> wrong = new ArrayList<>();
        Solutions found = GeostBruteForceTest.solveAll(g, withChain, st, checked, true, wrong);
        if (!found.all.equals(expected) || found.count != expected.size() || !wrong.isEmpty()) {
          failures.add(
              g.name + " strategy " + st + ": " + found.count + " expected " + expected.size());
        }
      }
    }
    assertThat(checked).isGreaterThan(20);
    assertThat(failures).isEmpty();
  }

  static boolean ordered(GeostInstance g, List<Integer> s) {
    int w = g.varsPerObject();
    for (int o = 0; o + 1 < g.objects.size(); o++) {
      int[] a = new int[g.k];
      int[] b = new int[g.k];
      for (int i = 0; i < g.k; i++) {
        a[i] = s.get(o * w + i);
        b[i] = s.get((o + 1) * w + i);
      }
      if (Arrays.compare(a, b) > 0) {
        return false;
      }
    }
    return true;
  }
}
