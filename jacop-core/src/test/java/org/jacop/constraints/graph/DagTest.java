/*
 * DagTest.java
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

package org.jacop.constraints.graph;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.ExplanationChecker;
import org.junit.jupiter.api.Test;

/** Tests of {@link Dag}: its propagation and its explanations for lazy clause generation. */
class DagTest {

  @Test
  void removesTheEdgeThatClosesACycleAndExplainsItByThePath() {
    Store store = new Store();
    IntVar[] ns = nodes(store, 3);
    IntVar[] es = edges(store, 3);
    AtomicTrail trail = new AtomicTrail(store);
    // 0 -> 1 -> 2 -> 0
    Dag dag = new Dag(new int[] {0, 1, 2}, new int[] {1, 2, 0}, ns, es);
    store.impose(dag);
    assertTrue(store.consistency());
    store.setLevel(1);
    es[0].domain.in(1, es[0], 1, 1);
    es[1].domain.in(1, es[1], 1, 1);
    assertTrue(store.consistency());
    assertEquals(0, es[2].max());
    assertEquals(1, ns[0].min());
    int entry = lastEntry(trail, es[2]);
    EntryList out = new EntryList();
    assertTrue(dag.explain(trail, entry, out));
    assertEquals(List.of("e0", "e1"), ids(trail, out));
    assertNull(new ExplanationChecker(trail).checkReason(entry, out));
    trail.detach();
  }

  @Test
  void failsOnASelectedCycleAndExplainsItByItsEdges() {
    Store store = new Store();
    IntVar[] ns = nodes(store, 4);
    IntVar[] es = edges(store, 4);
    AtomicTrail trail = new AtomicTrail(store);
    // a cycle 1 -> 2 -> 3 -> 1 and an edge 0 -> 1 outside it
    Dag dag = new Dag(new int[] {0, 1, 2, 3}, new int[] {1, 2, 3, 1}, ns, es);
    store.impose(dag);
    assertTrue(store.consistency());
    store.setLevel(1);
    for (IntVar e : es) {
      e.domain.in(1, e, 1, 1);
    }
    assertFalse(store.consistency());
    EntryList out = new EntryList();
    assertTrue(dag.explainFailure(trail, out));
    assertEquals(List.of("e1", "e2", "e3"), ids(trail, out));
    assertNull(new ExplanationChecker(trail).checkFailure(dag, out));
    trail.detach();
  }

  @Test
  void removesSelfLoopsAndTheEdgesOfLeftOutNodes() {
    Store store = new Store();
    IntVar[] ns = nodes(store, 2);
    IntVar[] es = edges(store, 2);
    store.impose(new Dag(new int[] {1, 1}, new int[] {1, 2}, ns, es, 1));
    assertTrue(store.consistency());
    assertEquals(0, es[0].max());
    store.setLevel(1);
    ns[1].domain.in(1, ns[1], 0, 0);
    assertTrue(store.consistency());
    assertEquals(0, es[1].max());
  }

  @Test
  void randomGraphsHaveSoundExplanations() {
    Random random = new Random(7);
    ExplanationChecker[] checker = new ExplanationChecker[1];
    int explained = 0;
    for (int trial = 0; trial < 300; trial++) {
      Store store = new Store();
      int n = 2 + random.nextInt(5);
      int m = random.nextInt(10);
      int[] from = new int[m];
      int[] to = new int[m];
      for (int e = 0; e < m; e++) {
        from[e] = random.nextInt(n);
        to[e] = random.nextInt(n);
      }
      IntVar[] ns = nodes(store, n);
      IntVar[] es = edges(store, m);
      AtomicTrail trail = new AtomicTrail(store);
      checker[0] = new ExplanationChecker(trail);
      Dag dag = new Dag(from, to, ns, es);
      store.impose(dag);
      boolean ok = store.consistency();
      int level = 0;
      while (ok) {
        List<IntVar> open = new ArrayList<>();
        for (IntVar v : es) {
          if (!v.singleton()) {
            open.add(v);
          }
        }
        for (IntVar v : ns) {
          if (!v.singleton()) {
            open.add(v);
          }
        }
        if (open.isEmpty()) {
          assertTrue(dag.satisfied());
          break;
        }
        store.setLevel(++level);
        IntVar v = open.get(random.nextInt(open.size()));
        int value = random.nextInt(4) == 0 ? 0 : 1;
        int before = trail.size();
        v.domain.in(level, v, value, value);
        ok = store.consistency();
        for (int entry = before + 1; entry < trail.size(); entry++) {
          if (trail.reason(entry) == dag) {
            EntryList out = new EntryList();
            assertTrue(dag.explain(trail, entry, out), "no reason for entry " + entry);
            assertNull(checker[0].checkReason(entry, out));
            explained++;
          }
        }
        if (!ok) {
          EntryList out = new EntryList();
          if (dag.explainFailure(trail, out)) {
            assertNull(checker[0].checkFailure(dag, out));
            explained++;
          }
        }
      }
      trail.detach();
    }
    assertTrue(explained > 100, "explained " + explained);
  }

  private static IntVar[] nodes(Store store, int n) {
    IntVar[] ns = new IntVar[n];
    for (int i = 0; i < n; i++) {
      ns[i] = new IntVar(store, "n" + i, 0, 1);
    }
    return ns;
  }

  private static IntVar[] edges(Store store, int m) {
    IntVar[] es = new IntVar[m];
    for (int e = 0; e < m; e++) {
      es[e] = new IntVar(store, "e" + e, 0, 1);
    }
    return es;
  }

  private static int lastEntry(AtomicTrail trail, IntVar x) {
    for (int entry = trail.size() - 1; entry >= 0; entry--) {
      if (trail.variable(entry) == x) {
        return entry;
      }
    }
    return -1;
  }

  private static List<String> ids(AtomicTrail trail, EntryList out) {
    List<String> ids = new ArrayList<>();
    for (int i = 0; i < out.size(); i++) {
      ids.add(trail.variable(out.get(i)).id());
    }
    ids.sort(String::compareTo);
    return ids;
  }
}
