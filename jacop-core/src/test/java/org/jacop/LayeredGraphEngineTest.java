/*
 * LayeredGraphEngineTest.java
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

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.function.BiFunction;
import org.jacop.constraints.ExtensionalSupportMdd;
import org.jacop.constraints.regular.LayeredGraphConstraint;
import org.jacop.constraints.regular.LayeredGraphConstraint.Engine;
import org.jacop.constraints.regular.Regular;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;
import org.junit.jupiter.api.Test;

/**
 * The propagation algorithms of {@link LayeredGraphConstraint} on models of several {@link Regular}
 * or {@link ExtensionalSupportMdd} constraints over shared variables. All algorithms are domain
 * consistent, so a complete search must visit the same number of nodes and find the same solutions
 * with each of them, including when the automatic choice switches from the counters to support
 * search in the middle of the search.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class LayeredGraphEngineTest {

  private static final int TRIALS = Integer.getInteger("layeredgraph.trials", 20);

  /** Constraints that switched to support search in the middle of a search. */
  private static int switched;

  /** The automatic choice, forced to switch to support search or to keep the counters. */
  private enum Variant {
    COUNTERS,
    SUPPORT_SEARCH,
    AUTO,
    AUTO_SWITCH,
    AUTO_STAY
  }

  @Test
  void regularEnginesExploreTheSameTree() {
    switched = 0;
    Random random = new Random(3);
    for (int trial = 0; trial < TRIALS; trial++) {
      int n = 12 + random.nextInt(4);
      int values = 2 + random.nextInt(3);
      int length = 4 + random.nextInt(9);
      int constraints = 3 + random.nextInt(4);
      long seed = random.nextLong();
      compareVariants(
          "regular trial " + trial,
          n,
          values,
          (store, x) -> {
            Random r = new Random(seed);
            List<LayeredGraphConstraint> list = new ArrayList<>();
            for (int c = 0; c < constraints; c++) {
              list.add(
                  new SwitchingRegular(
                      randomDfa(r, 3 + r.nextInt(8), values), scope(r, x, length)));
            }
            return list;
          });
    }
    assertThat(switched).as("constraints that switched").isPositive();
  }

  @Test
  void mddEnginesExploreTheSameTree() {
    switched = 0;
    Random random = new Random(11);
    for (int trial = 0; trial < TRIALS; trial++) {
      int n = 9 + random.nextInt(4);
      int values = 2 + random.nextInt(3);
      int length = 4 + random.nextInt(9);
      int constraints = 3 + random.nextInt(4);
      long seed = random.nextLong();
      compareVariants(
          "mdd trial " + trial,
          n,
          values,
          (store, x) -> {
            Random r = new Random(seed);
            List<LayeredGraphConstraint> list = new ArrayList<>();
            for (int c = 0; c < constraints; c++) {
              list.add(randomMdd(r, scope(r, x, length), 2 + r.nextInt(10), values));
            }
            return list;
          });
    }
    assertThat(switched).as("constraints that switched").isPositive();
  }

  private static void compareVariants(
      String instance,
      int n,
      int values,
      BiFunction<Store, IntVar[], List<LayeredGraphConstraint>> model) {
    long[] reference = null;
    for (Variant variant : Variant.values()) {
      Store store = new Store();
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, values - 1);
      }
      List<LayeredGraphConstraint> constraints = model.apply(store, x);
      for (LayeredGraphConstraint c : constraints) {
        switch (variant) {
          case COUNTERS -> c.setEngine(Engine.COUNTERS);
          case SUPPORT_SEARCH -> c.setEngine(Engine.SUPPORT_SEARCH);
          case AUTO -> c.setEngine(Engine.AUTO);
          case AUTO_SWITCH -> setSwitch(c, Boolean.TRUE);
          case AUTO_STAY -> setSwitch(c, Boolean.FALSE);
        }
        store.impose(c);
      }
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      long solutions = 0;
      long nodes = 0;
      if (store.consistency()) {
        search.labeling(store, new InputOrderSelect<>(store, x, new IndomainMin<>()));
        solutions = search.getSolutionListener().solutionsNo();
        nodes = search.getNodes();
      }
      long[] result = {solutions, nodes};
      if (reference == null) {
        reference = result;
      } else {
        assertThat(result).as(instance + " " + variant).containsExactly(reference);
      }
      for (LayeredGraphConstraint c : constraints) {
        if (variant == Variant.AUTO_STAY) {
          assertThat(c.engine()).as(instance).isEqualTo(Engine.COUNTERS);
        } else if (variant == Variant.AUTO_SWITCH && c.engine() == Engine.SUPPORT_SEARCH) {
          switched++;
        }
      }
    }
  }

  private static void setSwitch(LayeredGraphConstraint c, Boolean decision) {
    c.setEngine(Engine.AUTO);
    if (c instanceof SwitchingRegular r) {
      r.decision = decision;
    } else if (c instanceof SwitchingMdd m) {
      m.decision = decision;
    }
  }

  /** A Regular whose automatic choice can be forced. */
  private static final class SwitchingRegular extends Regular {
    Boolean decision;

    SwitchingRegular(Fsm fsm, IntVar[] list) {
      super(fsm, list);
    }

    @Override
    protected boolean preferSupportSearch(long countersNanos, long searchNanos) {
      return decision == null ? super.preferSupportSearch(countersNanos, searchNanos) : decision;
    }
  }

  /** An MDD whose automatic choice can be forced. */
  private static final class SwitchingMdd extends ExtensionalSupportMdd {
    Boolean decision;

    SwitchingMdd(IntVar[] vars, int[] level, int[] from, IntDomain[] label, int[] to) {
      super(vars, level, from, label, to);
    }

    @Override
    protected boolean preferSupportSearch(long countersNanos, long searchNanos) {
      return decision == null ? super.preferSupportSearch(countersNanos, searchNanos) : decision;
    }
  }

  private static IntVar[] scope(Random random, IntVar[] x, int length) {
    List<IntVar> pool = new ArrayList<>(List.of(x));
    IntVar[] scope = new IntVar[Math.min(length, x.length)];
    for (int i = 0; i < scope.length; i++) {
      scope[i] = pool.remove(random.nextInt(pool.size()));
    }
    return scope;
  }

  private static Fsm randomDfa(Random random, int states, int values) {
    Fsm fsm = new Fsm();
    FsmState[] state = new FsmState[states];
    for (int q = 0; q < states; q++) {
      state[q] = new FsmState();
      fsm.allStates.add(state[q]);
    }
    fsm.initState = state[0];
    for (int q = 0; q < states; q++) {
      if (random.nextInt(3) > 0) {
        fsm.finalStates.add(state[q]);
      }
      for (int v = 0; v < values; v++) {
        if (random.nextInt(10) < 8) {
          state[q].addTransition(
              new FsmTransition(new IntervalDomain(v, v), state[random.nextInt(states)]));
        }
      }
    }
    return fsm;
  }

  /** A random diagram in the MiniZinc form, with node 1 the root and node 0 the terminal. */
  private static SwitchingMdd randomMdd(Random random, IntVar[] scope, int width, int values) {
    int levels = scope.length;
    List<Integer> level = new ArrayList<>();
    int[][] nodesOfLevel = new int[levels + 1][];
    level.add(1);
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
        for (int v = 0; v < values; v++) {
          if (random.nextInt(10) < 8) {
            int[] targets = nodesOfLevel[l + 1];
            from.add(node);
            label.add(new IntervalDomain(v, v));
            to.add(targets[random.nextInt(targets.length)]);
          }
        }
      }
    }
    return new SwitchingMdd(
        scope,
        level.stream().mapToInt(Integer::intValue).toArray(),
        from.stream().mapToInt(Integer::intValue).toArray(),
        label.toArray(new IntDomain[0]),
        to.stream().mapToInt(Integer::intValue).toArray());
  }
}
