/*
 * VarIntMapTest.java
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

package org.jacop.util;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.HashSet;
import java.util.Set;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.junit.jupiter.api.Test;

/**
 * Tests VarIntMap with integer variables, which are hashed by their store index, and boolean
 * variables, which all have index -1 and are hashed by their name.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class VarIntMapTest {

  @Test
  void mixedVariablesKeepTheirValues() {
    Store store = new Store();
    VarIntMap map = new VarIntMap();
    Var[] vars = new Var[600];
    for (int i = 0; i < vars.length; i++) {
      vars[i] = i % 3 == 0 ? new IntVar(store, "x" + i, 0, 5) : new BooleanVar(store, "b" + i);
      map.put(vars[i], i);
    }
    // a variable put again keeps one entry with the new value
    map.put(vars[7], 7000);
    assertThat(map.size()).isEqualTo(vars.length);
    for (int i = 0; i < vars.length; i++) {
      assertThat(map.get(vars[i])).isEqualTo(i == 7 ? 7000 : i);
    }
    assertThat(map.get(new BooleanVar(store, "other"))).isEqualTo(VarIntMap.ABSENT);
    assertThat(map.get(new BooleanVar(new Store(), "b1")))
        .as("same name in another store")
        .isEqualTo(VarIntMap.ABSENT);
  }

  /**
   * Boolean variables all have store index -1. Hashed by it, they all start probing from one slot,
   * and a lookup scans every boolean of the map: a symmetry breaking lex over 1,369 booleans spent
   * 15-20 % of the search in this scan (still-life-wastage 13).
   */
  @Test
  void booleanVariablesSpreadOverTheSlots() {
    Store store = new Store();
    int mask = 4095;
    Set<Integer> slots = new HashSet<>();
    for (int i = 0; i < 1000; i++) {
      BooleanVar b = new BooleanVar(store, "X_INTRODUCED_" + i + "_");
      assertThat(b.index()).isEqualTo(-1);
      slots.add(VarIntMap.slot(b, mask));
    }
    assertThat(slots.size()).isGreaterThan(800);
  }
}
