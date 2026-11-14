/*
 * DisjunctiveCliquesTest.java
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
package org.jacop.presolve;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Tests the search for disjunctive cliques.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
class DisjunctiveCliquesTest {

  private final Store store = new Store();

  private IntVar[] starts(int n) {
    IntVar[] s = new IntVar[n];
    for (int i = 0; i < n; i++) {
      s[i] = new IntVar(store, "s" + i, 0, 100);
    }
    return s;
  }

  @Test
  void precedenceChainJoinsAClique() {
    IntVar[] s = starts(3);
    DisjunctiveCliques dc = new DisjunctiveCliques();
    int a = dc.task(s[0], 2);
    int b = dc.task(s[1], 3);
    int c = dc.task(s[2], 1);
    // a and b in either order, b and c on one resource, a before c through an intermediate start
    IntVar m = new IntVar(store, "m", 0, 100);
    dc.disjunction(s[0], 2, s[1], 3);
    dc.conflict(b, c);
    dc.precedence(s[0], m, 1);
    dc.precedence(m, s[2], 1);
    List<int[]> cliques = dc.cliques();
    assertEquals(1, cliques.size());
    assertArrayEquals(new int[] {a, b, c}, cliques.get(0));
  }

  @Test
  void orderedTasksNeedNoClique() {
    IntVar[] s = starts(4);
    DisjunctiveCliques dc = new DisjunctiveCliques();
    for (int i = 0; i < 4; i++) {
      dc.task(s[i], 2);
    }
    for (int i = 0; i < 3; i++) {
      dc.precedence(s[i], s[i + 1], 2);
    }
    assertTrue(dc.cliques().isEmpty());
  }

  @Test
  void unaryOfTheModelIsNotRepeated() {
    IntVar[] s = starts(4);
    DisjunctiveCliques dc = new DisjunctiveCliques();
    int[] t = new int[4];
    for (int i = 0; i < 4; i++) {
      t[i] = dc.task(s[i], 2);
    }
    for (int i = 0; i < 4; i++) {
      for (int j = i + 1; j < 4; j++) {
        dc.conflict(t[i], t[j]);
      }
    }
    dc.unary(t[0], t[1], t[2]);
    // the fourth task makes a larger clique than the model's unary resource
    assertArrayEquals(t, dc.cliques().get(0));

    DisjunctiveCliques same = new DisjunctiveCliques();
    for (int i = 0; i < 4; i++) {
      same.task(s[i], 2);
    }
    for (int i = 0; i < 4; i++) {
      for (int j = i + 1; j < 4; j++) {
        same.conflict(t[i], t[j]);
      }
    }
    same.unary(t);
    assertTrue(same.cliques().isEmpty());
  }

  @Test
  void disjunctionShorterThanTheDurationsIsNoEdge() {
    IntVar[] s = starts(3);
    DisjunctiveCliques dc = new DisjunctiveCliques();
    int[] t = {dc.task(s[0], 3), dc.task(s[1], 3), dc.task(s[2], 3)};
    // s1 >= s0 + 2 or s0 >= s1 + 3 lets a task of duration 3 on s0 overlap s1
    dc.disjunction(s[0], 2, s[1], 3);
    dc.disjunction(s[1], 3, s[2], 3);
    dc.disjunction(s[0], 3, s[2], 3);
    assertTrue(dc.cliques().isEmpty());
    // the same start and duration is the same task, a zero duration is no task
    assertEquals(t[0], dc.task(s[0], 3));
    assertEquals(-1, dc.task(s[0], 0));
  }

  @Test
  void variableDurationsUseTheirBounds() {
    IntVar[] s = starts(3);
    IntVar d = new IntVar(store, "d", 1, 4);
    DisjunctiveCliques dc = new DisjunctiveCliques();
    int a = dc.task(s[0], d);
    int b = dc.task(s[1], 2);
    int c = dc.task(s[2], 2);
    dc.conflict(b, c);
    dc.disjunction(s[1], 2, s[2], 2);
    // a may last 4 but s0 is only 3 before the others
    dc.disjunction(s[0], 3, s[1], 2);
    dc.disjunction(s[0], 3, s[2], 2);
    assertTrue(dc.cliques().isEmpty());
    dc.disjunction(s[0], 4, s[1], 2);
    dc.disjunction(s[0], 4, s[2], 2);
    assertArrayEquals(new int[] {a, b, c}, dc.cliques().get(0));
  }

  @Test
  void positiveCycleIsIgnored() {
    IntVar[] s = starts(3);
    DisjunctiveCliques dc = new DisjunctiveCliques();
    int[] t = {dc.task(s[0], 1), dc.task(s[1], 1), dc.task(s[2], 1)};
    dc.precedence(s[0], s[1], 1);
    dc.precedence(s[1], s[0], 1);
    dc.conflict(t[0], t[2]);
    dc.conflict(t[1], t[2]);
    dc.conflict(t[0], t[1]);
    assertArrayEquals(t, dc.cliques().get(0));
  }
}
