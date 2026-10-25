/*
 * StoreTrailTest.java
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.Test;

/**
 * Tests that removing a level restores the variables and timestamps changed at it, with the store
 * trail ({@link TrailBacktrackableManager}, the timestamp trail and the Boolean change trail).
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
class StoreTrailTest {

  /**
   * Random dives with changes to integer and Boolean variables and timestamps, backtracks and
   * re-entries of a level after it was removed (as a right branch does). After each removed level
   * the state must equal the state saved when the level was entered.
   */
  @Test
  void removeLevelRestoresStateOfRandomDives() {
    Random random = new Random();
    for (int seed = 0; seed < 200; seed++) {
      random.setSeed(seed);
      runRandomDives(random);
    }
  }

  private static void runRandomDives(Random random) {
    // A small initial size makes the store grow its variable array while variables are created.
    Store store = new Store(2);
    List<IntVar> vars = new ArrayList<>();
    for (int i = 0; i < 2 + random.nextInt(60); i++) {
      int max = random.nextBoolean() ? 1 + random.nextInt(20) : 1 + random.nextInt(300);
      vars.add(
          random.nextInt(4) == 0
              ? new BooleanVar(store, "b" + i)
              : new IntVar(store, "x" + i, 0, max));
    }
    List<TimeStamp<Integer>> stamps = new ArrayList<>();
    for (int i = 0; i < 1 + random.nextInt(20); i++) {
      stamps.add(new TimeStamp<>(store, -1));
    }

    Deque<String> saved = new ArrayDeque<>();
    for (int step = 0; step < 3000; step++) {
      int action = random.nextInt(100);
      if (action < 15 && store.level < 60) {
        saved.push(state(vars, stamps));
        store.setLevel(store.level + 1);
      } else if (action < 30 && !saved.isEmpty()) {
        store.removeLevel(store.level);
        assertThat(state(vars, stamps)).isEqualTo(saved.peek());
        if (random.nextBoolean()) {
          // Back to the parent level.
          saved.pop();
          store.setLevel(store.level - 1);
        } else {
          // The same level again, as a right branch after its left branch.
          store.setLevel(store.level);
        }
      } else if (action < 45) {
        stamps.get(random.nextInt(stamps.size())).update(random.nextInt(1000));
      } else {
        IntVar v = vars.get(random.nextInt(vars.size()));
        if (v.getSize() > 1) {
          if (random.nextBoolean() || v instanceof BooleanVar) {
            v.domain.inComplement(store.level, v, v.min() + random.nextInt(v.max() - v.min() + 1));
          } else {
            int min = v.min() + random.nextInt(v.max() - v.min());
            int max = Math.max(min, v.max() - random.nextInt(3));
            if (v.domain.isIntersecting(min, max)) {
              v.domain.in(store.level, v, min, max);
            }
          }
        }
      }
    }

    while (!saved.isEmpty()) {
      store.removeLevel(store.level);
      assertThat(state(vars, stamps)).isEqualTo(saved.pop());
      store.setLevel(store.level - 1);
    }
  }

  private static String state(List<IntVar> vars, List<TimeStamp<Integer>> stamps) {
    StringBuilder result = new StringBuilder();
    for (IntVar v : vars) {
      result.append(v.domain).append(' ');
    }
    for (TimeStamp<Integer> t : stamps) {
      result.append(t.value()).append(' ');
    }
    return result.toString();
  }

  /** A timestamp created during the search loses its value when the level of its creation goes. */
  @Test
  void timeStampCreatedDuringSearchIsRemovedWithItsLevel() {
    Store store = new Store();
    TimeStamp<Integer> root = new TimeStamp<>(store, 1);
    store.setLevel(1);
    store.setLevel(2);
    TimeStamp<Integer> inner = new TimeStamp<>(store, 5);
    inner.update(6);
    root.update(2);
    store.setLevel(3);
    inner.update(7);

    store.removeLevel(3);
    store.setLevel(2);
    assertThat(inner.value()).isEqualTo(6);
    store.removeLevel(2);
    store.setLevel(1);
    assertThat(inner.pointer4Last).isEqualTo(-1);
    assertThat(root.value()).isEqualTo(1);
  }

  /** The listener array follows every way of changing the set. */
  @Test
  void listenerSetElementsFollowChanges() {
    ListenerSet<Integer> set = new ListenerSet<>();
    Random random = new Random(3);
    for (int step = 0; step < 2000; step++) {
      int action = random.nextInt(10);
      Integer value = random.nextInt(20);
      if (action < 4) {
        set.add(value);
      } else if (action < 6) {
        set.remove(value);
      } else if (action < 7) {
        set.removeIf(x -> x % 3 == value % 3);
      } else if (action < 8) {
        set.removeAll(List.of(value, value + 1));
      } else if (action < 9) {
        set.addAll(List.of(value, value + 2));
      } else if (random.nextInt(10) == 0) {
        set.clear();
      }
      assertThat(set.elements()).containsExactly(set.toArray());
    }
  }
}
