/*
 * ConstraintQueueTest.java
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
package org.jacop.core;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XneqY;
import org.jacop.util.VarIntMap;
import org.junit.jupiter.api.Test;

/**
 * Tests for {@link ConstraintQueue}, the array-based propagation queue of {@link Store}.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
class ConstraintQueueTest {

  /** Random adds, polls and clears on two queues give the order of a LinkedHashSet per queue. */
  @Test
  void keepsInsertionOrderWithoutDuplicatesLikeLinkedHashSet() {
    Store store = new Store();
    List<Constraint> constraints = new ArrayList<>();
    for (int i = 0; i < 40; i++) {
      IntVar x = new IntVar(store, "x" + i, 0, 5);
      IntVar y = new IntVar(store, "y" + i, 0, 5);
      constraints.add(new XneqY(x, y));
    }
    ConstraintQueue[] queues = {new ConstraintQueue(store, 0), new ConstraintQueue(store, 3)};
    List<LinkedHashSet<Constraint>> references =
        List.of(new LinkedHashSet<>(), new LinkedHashSet<>());

    Random random = new Random(1);
    for (int step = 0; step < 20_000; step++) {
      int q = random.nextInt(2);
      ConstraintQueue queue = queues[q];
      LinkedHashSet<Constraint> reference = references.get(q);
      int action = random.nextInt(100);
      if (action < 55) {
        Constraint c = constraints.get(random.nextInt(constraints.size()));
        assertThat(queue.add(c)).isEqualTo(reference.add(c));
      } else if (action < 98) {
        if (!reference.isEmpty()) {
          Iterator<Constraint> it = reference.iterator();
          Constraint expected = it.next();
          it.remove();
          assertThat(queue.poll()).isSameAs(expected);
        }
      } else {
        queue.clear();
        reference.clear();
      }
      assertThat(queue.size()).isEqualTo(reference.size());
      assertThat(queue.isEmpty()).isEqualTo(reference.isEmpty());
      for (Constraint c : constraints) {
        assertThat(queue.contains(c)).isEqualTo(reference.contains(c));
      }
    }
  }

  /** A constraint left in the queue of an abandoned store is still scheduled in a new store. */
  @Test
  void membershipBelongsToOneStore() {
    Store first = new Store();
    IntVar x = new IntVar(first, "x", 1, 2);
    IntVar y = new IntVar(first, "y", 1, 2);
    XneqY c = new XneqY(x, y);
    first.impose(c);
    assertThat(first.changed[c.getQueueIndex()].contains(c)).isTrue();

    Store second = new Store();
    assertThat(second.changed[c.getQueueIndex()].contains(c)).isFalse();
    assertThat(second.changed[c.getQueueIndex()].add(c)).isTrue();
    assertThat(second.changed[c.getQueueIndex()].poll()).isSameAs(c);
  }

  /** Queued constraints are dropped on failure and scheduled again after backtracking. */
  @Test
  void queueIsEmptiedOnFailureAndUsableAfterBacktrack() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 3);
    IntVar y = new IntVar(store, "y", 1, 3);
    IntVar z = new IntVar(store, "z", 1, 3);
    XneqY xy = new XneqY(x, y);
    XneqY yz = new XneqY(y, z);
    store.impose(xy);
    store.impose(yz);
    assertThat(store.consistency()).isTrue();

    store.setLevel(1);
    x.domain.in(store.level, x, 2, 2);
    z.domain.in(store.level, z, 2, 2);
    y.domain.in(store.level, y, 2, 2);
    assertThat(store.consistency()).isFalse();
    store.removeLevel(1);
    store.setLevel(0);
    for (ConstraintQueue queue : store.changed) {
      assertThat(queue.isEmpty()).isTrue();
    }

    store.setLevel(1);
    x.domain.in(store.level, x, 1, 1);
    assertThat(store.changed[xy.getQueueIndex()].contains(xy)).isTrue();
    assertThat(store.consistency()).isTrue();
    assertThat(y.dom().contains(1)).isFalse();
  }

  /**
   * With returnAfterPruning, consistency() stops after each pruning constraint with the rest still
   * queued, and repeated calls reach the same fixpoint as one full call.
   */
  @Test
  void returnAfterPruningReachesTheSameFixpointInSteps() {
    int[][] full = chainDomains(false);
    int[][] stepped = chainDomains(true);
    assertThat(stepped).isDeepEqualTo(full);
  }

  private static int[][] chainDomains(boolean returnAfterPruning) {
    Store store = new Store();
    IntVar[] x = new IntVar[6];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 10);
    }
    for (int i = 0; i + 1 < x.length; i++) {
      store.impose(new XltY(x[i], x[i + 1]));
    }
    assertThat(store.consistency()).isTrue();
    store.setReturnAfterPruning(returnAfterPruning);
    store.setLevel(1);
    x[0].domain.in(store.level, x[0], 3, 10);
    int calls = 0;
    do {
      assertThat(store.consistency()).isTrue();
      calls++;
    } while (store.hasPendingConstraints());
    assertThat(calls > 1).isEqualTo(returnAfterPruning);
    int[][] domains = new int[x.length][];
    for (int i = 0; i < x.length; i++) {
      domains[i] = new int[] {x[i].min(), x[i].max()};
    }
    return domains;
  }

  /**
   * Random watches and unwatches of watched-literal constraints keep, per variable, the order and
   * the set of a LinkedHashSet, which the store used before.
   */
  @Test
  void watchedLiteralConstraintsKeepLinkedHashSetOrder() {
    Store store = new Store();
    List<IntVar> vars = new ArrayList<>();
    List<Constraint> constraints = new ArrayList<>();
    for (int i = 0; i < 12; i++) {
      vars.add(new IntVar(store, "w" + i, 0, 5));
    }
    for (int i = 0; i < 30; i++) {
      constraints.add(new XneqY(vars.get(i % 12), vars.get((i + 1) % 12)));
    }
    Map<Var, LinkedHashSet<Constraint>> reference = new IdentityHashMap<>();
    Random random = new Random(2);
    for (int step = 0; step < 20_000; step++) {
      IntVar v = vars.get(random.nextInt(vars.size()));
      Constraint c = constraints.get(random.nextInt(constraints.size()));
      if (random.nextInt(100) < 60) {
        store.registerWatchedLiteralConstraint(v, c);
        reference.computeIfAbsent(v, k -> new LinkedHashSet<>()).add(c);
      } else if (reference.containsKey(v)) {
        store.deregisterWatchedLiteralConstraint(v, c);
        reference.get(v).remove(c);
      }
      assertThat(store.watchedLiteralConstraints(v))
          .containsExactlyElementsOf(reference.getOrDefault(v, new LinkedHashSet<>()));
    }
    assertThat(store.countWatches())
        .isEqualTo(reference.values().stream().mapToInt(LinkedHashSet::size).sum());
    store.clearWatchedConstraint();
    assertThat(store.countWatches()).isZero();
    assertThat(store.watchedLiteralConstraints(vars.get(0))).isEmpty();
  }

  /** A VarIntMap answers like an IdentityHashMap, also for variables sharing a store index. */
  @Test
  void varIntMapAnswersLikeIdentityHashMap() {
    Store store = new Store();
    List<Var> vars = new ArrayList<>();
    for (int i = 0; i < 300; i++) {
      IntVar v = new IntVar(store, "m" + i, 0, 1);
      if (i % 7 == 0) {
        v.storeIndex = -1;
      }
      vars.add(v);
    }
    VarIntMap map = new VarIntMap(2);
    Map<Var, Integer> reference = new IdentityHashMap<>();
    Random random = new Random(3);
    for (int step = 0; step < 5_000; step++) {
      Var v = vars.get(random.nextInt(vars.size()));
      if (random.nextBoolean()) {
        int value = random.nextInt(1000);
        map.put(v, value);
        reference.put(v, value);
      }
      assertThat(map.get(v)).isEqualTo(reference.getOrDefault(v, VarIntMap.ABSENT));
      assertThat(map.size()).isEqualTo(reference.size());
    }
  }
}
