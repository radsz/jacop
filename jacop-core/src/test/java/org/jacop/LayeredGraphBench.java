/*
 * LayeredGraphBench.java
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

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Random;
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
 * Speed of the layered graph engines on models made only of {@link Regular} or {@link
 * ExtensionalSupportMdd} constraints of a given shape. All engines are domain consistent, so they
 * explore the same tree and nodes per second compare them. Not part of any build profile; run it on
 * demand:
 *
 * <pre>
 * mvn -Pmin -pl jacop-core test -Dtest=LayeredGraphBench -Dsurefire.rerunFailingTestsCount=0 \
 *     -Dbench.shapes=dfa:10:16:4,mdd:12:60:5,window:50:5:8 -Dbench.seconds=3
 * </pre>
 *
 * <p>A shape is kind:levels:width:values. dfa is a random automaton with width states, mdd a random
 * diagram with up to width nodes per level, window a sliding window automaton allowing at most half
 * of any width consecutive variables to take a value of the lower half.
 */
class LayeredGraphBench {

  private static final Engine[] ENGINES = {Engine.COUNTERS, Engine.SUPPORT_SEARCH, Engine.AUTO};

  @Test
  void bench() {
    String shapes =
        System.getProperty(
            "bench.shapes",
            "dfa:8:8:4,dfa:12:30:4,dfa:30:30:4,dfa:60:12:3,mdd:8:20:4,mdd:12:60:5,mdd:14:200:5,"
                + "mdd:30:8:4,window:30:4:6,window:60:6:8,window:100:8:10");
    int seconds = Integer.getInteger("bench.seconds", 3);
    int seeds = Integer.getInteger("bench.seeds", 2);
    String engines = System.getProperty("bench.engines", "");
    for (String shape : shapes.split(",")) {
      String[] p = shape.split(":");
      for (int seed = 1; seed <= seeds; seed++) {
        StringBuilder line =
            new StringBuilder(String.format(Locale.ROOT, "%-18s s%d", shape, seed));
        long reference = -1;
        for (Engine engine : ENGINES) {
          if (!engines.isEmpty() && !engines.contains(engine.name())) {
            continue;
          }
          // Warm up once, then measure.
          run(p, seed, engine, 1);
          long[] r = run(p, seed, engine, seconds);
          double rate = r[0] / (r[1] / 1e9);
          if (reference < 0) {
            reference = (long) rate;
          }
          line.append(
              String.format(
                  Locale.ROOT,
                  "  %s %8.0f n/s (%5.2f) %s",
                  engine.name().toLowerCase(Locale.ROOT),
                  rate,
                  rate / Math.max(1, reference),
                  r[2] > 0 ? "done" : ""));
        }
        System.out.println(line);
      }
    }
  }

  /** It returns the nodes, the nanoseconds and 1 when the search completed. */
  private static long[] run(String[] p, int seed, Engine engine, int seconds) {
    String kind = p[0];
    int levels = Integer.parseInt(p[1]);
    int width = Integer.parseInt(p[2]);
    int values = Integer.parseInt(p[3]);
    Random random = new Random(seed * 1000003L + levels * 31L + width);
    int n = Math.max(2 * levels, 24);
    int constraints = Math.max(4, 3 * n / levels + 2);
    Store store = new Store();
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      x[i] = new IntVar(store, "x" + i, 0, values - 1);
    }
    List<LayeredGraphConstraint> posted = new ArrayList<>();
    for (int c = 0; c < constraints; c++) {
      IntVar[] scope = scope(random, x, levels);
      LayeredGraphConstraint constraint =
          switch (kind) {
            case "dfa" -> new Regular(randomDfa(random, width, values), scope);
            case "window" -> new Regular(window(random, width, values), scope);
            case "mdd" -> randomMdd(random, scope, width, values);
            default -> throw new IllegalArgumentException(kind);
          };
      constraint.setEngine(engine);
      posted.add(constraint);
      store.impose(constraint);
    }
    long start = System.nanoTime();
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.setTimeOut(seconds);
    boolean done;
    if (!store.consistency()) {
      done = true;
    } else {
      search.labeling(store, new InputOrderSelect<>(store, x, new IndomainMin<>()));
      done = !search.timeOutOccured;
    }
    long time = System.nanoTime() - start;
    return new long[] {search.getNodes(), time, done ? 1 : 0};
  }

  private static IntVar[] scope(Random random, IntVar[] x, int levels) {
    List<IntVar> pool = new ArrayList<>(List.of(x));
    IntVar[] scope = new IntVar[levels];
    for (int i = 0; i < levels; i++) {
      scope[i] = pool.remove(random.nextInt(pool.size()));
    }
    return scope;
  }

  /** A random automaton: each state has a transition for most values, half of the states accept. */
  private static Fsm randomDfa(Random random, int states, int values) {
    Fsm fsm = new Fsm();
    FsmState[] state = new FsmState[states];
    for (int q = 0; q < states; q++) {
      state[q] = new FsmState();
      fsm.allStates.add(state[q]);
    }
    fsm.initState = state[0];
    for (int q = 0; q < states; q++) {
      if (random.nextInt(2) == 0 || q == states - 1) {
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

  /**
   * At most half of any q consecutive values lie in a random half of the values: one state per
   * window of the last q - 1 bits.
   */
  private static Fsm window(Random random, int q, int values) {
    boolean[] marked = new boolean[values];
    for (int v = 0; v < values; v++) {
      marked[v] = random.nextBoolean();
    }
    int limit = Math.max(1, q / 2);
    int windows = 1 << (q - 1);
    Fsm fsm = new Fsm();
    // States: (number of values seen, capped at q - 1, last q - 1 bits).
    FsmState[][] state = new FsmState[q][windows];
    for (int seen = 0; seen < q; seen++) {
      for (int w = 0; w < windows; w++) {
        state[seen][w] = new FsmState();
      }
    }
    for (int seen = 0; seen < q; seen++) {
      for (int w = 0; w < windows; w++) {
        if (seen < q - 1 && w >= 1 << seen) {
          continue;
        }
        FsmState s = state[seen][w];
        fsm.allStates.add(s);
        fsm.finalStates.add(s);
        for (int v = 0; v < values; v++) {
          int bit = marked[v] ? 1 : 0;
          int all = (w << 1) | bit;
          int count = Integer.bitCount(seen < q - 1 ? all : all & ((1 << q) - 1));
          if (count > limit) {
            continue;
          }
          int next = all & (windows - 1);
          s.addTransition(
              new FsmTransition(new IntervalDomain(v, v), state[Math.min(seen + 1, q - 1)][next]));
        }
      }
    }
    fsm.initState = state[0][0];
    return fsm;
  }

  /** A random diagram in the MiniZinc form: node 1 is the root and 0 the terminal. */
  private static ExtensionalSupportMdd randomMdd(
      Random random, IntVar[] scope, int width, int values) {
    int levels = scope.length;
    List<Integer> level = new ArrayList<>();
    int[][] nodesOfLevel = new int[levels + 1][];
    level.add(1);
    nodesOfLevel[0] = new int[] {1};
    nodesOfLevel[levels] = new int[] {0};
    for (int l = 1; l < levels; l++) {
      int count = Math.max(1, width / 2 + random.nextInt(width / 2 + 1));
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
          if (random.nextInt(10) < 7) {
            int[] targets = nodesOfLevel[l + 1];
            from.add(node);
            label.add(new IntervalDomain(v, v));
            to.add(targets[random.nextInt(targets.length)]);
          }
        }
      }
    }
    return new ExtensionalSupportMdd(
        scope,
        level.stream().mapToInt(Integer::intValue).toArray(),
        from.stream().mapToInt(Integer::intValue).toArray(),
        label.toArray(new IntDomain[0]),
        to.stream().mapToInt(Integer::intValue).toArray());
  }
}
