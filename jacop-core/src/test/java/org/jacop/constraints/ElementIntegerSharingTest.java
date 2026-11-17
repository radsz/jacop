/*
 * ElementIntegerSharingTest.java
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Random;
import org.jacop.api.VarMap;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.junit.jupiter.api.Test;

/**
 * Elements over one list share it and what is derived from it: each element over a list of 20,000
 * values held its own copy of the list, of the ranks of its values and of the groups of duplicates.
 */
class ElementIntegerSharingTest {

  @Test
  void elementsOverOneListShareItAndPropagateAsSeparateOnes() {
    Random r = new Random(5);
    int n = 300;
    int[] list = new int[n];
    for (int i = 0; i < n; i++) {
      list[i] = r.nextInt(20); // many duplicates, so the groups of duplicates are used
    }
    Store store = new Store();
    IntVar i1 = new IntVar(store, "i1", 1, n);
    IntVar v1 = new IntVar(store, "v1", -5, 30);
    IntVar i2 = new IntVar(store, "i2", 1, n);
    IntVar v2 = new IntVar(store, "v2", -5, 30);
    IntVar i3 = new IntVar(store, "i3", 1, n);
    IntVar v3 = new IntVar(store, "v3", -5, 30);
    ElementInteger first = new ElementInteger(i1, list, v1, 0);
    ElementInteger shared = new ElementInteger(i2, v2, first);
    ElementInteger separate = new ElementInteger(i3, list, v3, 0);
    store.impose(first);
    store.impose(shared);
    store.impose(separate);
    assertTrue(store.consistency());
    assertSame(first.list, shared.list);
    assertSame(first.duplicates, shared.duplicates);
    assertTrue(!first.duplicates.isEmpty());

    for (int trial = 0; trial < 300; trial++) {
      store.setLevel(store.level + 1);
      int lo = 1 + r.nextInt(n);
      int hi = lo + r.nextInt(n - lo + 1);
      int hole = 1 + r.nextInt(n);
      int a = r.nextInt(20);
      boolean ok = true;
      try {
        i2.domain.in(store.level, i2, lo, hi);
        i3.domain.in(store.level, i3, lo, hi);
        i2.domain.inComplement(store.level, i2, hole);
        i3.domain.inComplement(store.level, i3, hole);
        if (r.nextBoolean()) {
          v2.domain.inComplement(store.level, v2, a);
          v3.domain.inComplement(store.level, v3, a);
        }
        ok = store.consistency();
      } catch (FailException e) {
        ok = false;
      }
      if (ok) {
        assertTrue(v2.dom().eq(v3.dom()), v2 + " " + v3);
        assertTrue(i2.dom().eq(i3.dom()), i2 + " " + i3);
      }
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
    }

    // a copy shares the list too
    Store other = new Store();
    java.util.Map<Var, Var> copies = new java.util.HashMap<>();
    VarMap map =
        new VarMap() {
          @Override
          public Store target() {
            return other;
          }

          @Override
          @SuppressWarnings("unchecked")
          public <V extends Var> V get(V v) {
            return (V)
                copies.computeIfAbsent(
                    v, k -> new IntVar(other, k.id(), ((IntVar) k).min(), ((IntVar) k).max()));
          }
        };
    ElementInteger copy = shared.copy(map);
    assertSame(first.list, copy.list);
    assertEquals(n, copy.values().length);
  }
}
