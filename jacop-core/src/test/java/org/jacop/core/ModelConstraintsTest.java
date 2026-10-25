/*
 * ModelConstraintsTest.java
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
import java.util.Arrays;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Supplier;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XneqC;
import org.junit.jupiter.api.Test;

/**
 * Tests the lists of model constraints attached to the domains of integer variables, which grow in
 * place when the domain object owns them and are shared with the domains of earlier levels.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
class ModelConstraintsTest {

  private static final int EVENTS = 5;

  /** The removal order of {@link IntDomain#removeModelConstraint}. */
  private static final int[] REMOVAL_ORDER = {
    IntDomain.GROUND, IntDomain.BOUND, IntDomain.ANY, IntDomain.MIN_EVENT, IntDomain.MAX_EVENT
  };

  private static final List<Supplier<IntDomain>> DOMAINS =
      List.of(
          () -> new IntervalDomain(0, 1000),
          () -> new SmallDenseDomain(0, 20),
          () -> new BoundDomain(0, 1000),
          () -> new LazyBitSetDomain(0, 200));

  /**
   * Random sequences of imposing and removing constraints, entering levels and removing them. After
   * each step the attached constraints of every variable and event must equal a model kept with
   * sets, and none may be attached twice.
   */
  @Test
  void attachedConstraintsFollowImposeRemoveAndBacktrack() {
    Random random = new Random();
    for (int seed = 0; seed < 300; seed++) {
      random.setSeed(seed);
      Store store = new Store();
      IntVar[] vars = new IntVar[DOMAINS.size()];
      for (int i = 0; i < vars.length; i++) {
        vars[i] = new IntVar(store, "x" + i, DOMAINS.get(i).get());
      }
      // up to 80 constraints, so lists grow past the hash table threshold
      Constraint[] constraints = new Constraint[5 + random.nextInt(76)];
      for (int i = 0; i < constraints.length; i++) {
        constraints[i] = new XneqC(vars[0], -1 - i);
      }

      List<List<Set<Constraint>>> model = new ArrayList<>();
      for (int i = 0; i < vars.length; i++) {
        List<Set<Constraint>> events = new ArrayList<>();
        for (int e = 0; e < EVENTS; e++) {
          events.add(new HashSet<>());
        }
        model.add(events);
      }
      Deque<List<List<Set<Constraint>>>> saved = new ArrayDeque<>();

      for (int step = 0; step < 400; step++) {
        int op = random.nextInt(20);
        String context = "seed " + seed + " step " + step;
        if (op < 2 && store.level < 30) {
          saved.push(copy(model));
          store.setLevel(store.level + 1);
        } else if (op < 4 && !saved.isEmpty()) {
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
          model = saved.pop();
        } else {
          int v = random.nextInt(vars.length);
          Constraint c = constraints[random.nextInt(constraints.length)];
          if (op < 14) {
            int event = random.nextInt(EVENTS);
            vars[v].putModelConstraint(c, event);
            model.get(v).get(event).add(c);
          } else {
            vars[v].removeConstraint(c);
            for (int event : REMOVAL_ORDER) {
              if (model.get(v).get(event).remove(c)) {
                break;
              }
            }
          }
        }
        for (int v = 0; v < vars.length; v++) {
          check(vars[v].dom(), model.get(v), context + " var " + v);
        }
      }
    }
  }

  /**
   * A constraint removed at a level and imposed again at the same level is attached again, also
   * when the list it was removed from is shared with the domain of an earlier level.
   */
  @Test
  void constraintRemovedAndImposedAgainIsAttached() {
    for (Supplier<IntDomain> domain : DOMAINS) {
      Store store = new Store();
      IntVar x = new IntVar(store, "x", domain.get());
      Constraint[] constraints = new Constraint[40];
      for (int i = 0; i < constraints.length; i++) {
        constraints[i] = new XneqC(x, -1 - i);
        x.putModelConstraint(constraints[i], IntDomain.ANY);
      }
      store.setLevel(1);
      x.removeConstraint(constraints[3]);
      assertThat(x.dom().constraints()).doesNotContain(constraints[3]).hasSize(39);
      x.putModelConstraint(constraints[3], IntDomain.ANY);
      assertThat(x.dom().constraints()).contains(constraints[3]).hasSize(40);

      store.removeLevel(1);
      store.setLevel(0);
      assertThat(new HashSet<>(x.dom().constraints()))
          .isEqualTo(new HashSet<>(Arrays.asList(constraints)));
    }
  }

  private static void check(IntDomain dom, List<Set<Constraint>> expected, String context) {
    for (int e = 0; e < EVENTS; e++) {
      int count = dom.modelConstraintsToEvaluate[e];
      List<Constraint> attached =
          count == 0 ? List.of() : Arrays.asList(dom.modelConstraints[e]).subList(0, count);
      assertThat(attached).as(context + " event " + e).doesNotHaveDuplicates();
      assertThat(new HashSet<>(attached)).as(context + " event " + e).isEqualTo(expected.get(e));
    }
  }

  private static List<List<Set<Constraint>>> copy(List<List<Set<Constraint>>> model) {
    List<List<Set<Constraint>>> result = new ArrayList<>();
    for (List<Set<Constraint>> events : model) {
      List<Set<Constraint>> copied = new ArrayList<>();
      for (Set<Constraint> s : events) {
        copied.add(new HashSet<>(s));
      }
      result.add(copied);
    }
    return result;
  }
}
