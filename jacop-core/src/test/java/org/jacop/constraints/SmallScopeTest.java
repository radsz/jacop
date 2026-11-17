/*
 * SmallScopeTest.java
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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import org.junit.jupiter.api.Test;

/**
 * Scopes of more than {@link SmallScope#MAX_SIZE} elements were a {@code LinkedHashSet}, about 45
 * bytes an element in every constraint; they are an array with a hash index, and behave as the set
 * did.
 */
class SmallScopeTest {

  // equal by id, with few distinct hash codes, so the hash index meets collisions
  private record Key(int id) {
    @Override
    public int hashCode() {
      return id % 3;
    }
  }

  @Test
  void largeScopesBehaveAsLinkedHashSets() {
    Random r = new Random(11);
    for (int trial = 0; trial < 200; trial++) {
      int n = SmallScope.MAX_SIZE + 1 + r.nextInt(60);
      Key[] keys = new Key[n];
      for (int i = 0; i < n; i++) {
        keys[i] = new Key(r.nextInt(2 * n));
      }
      Set<Key> scope = SmallScope.of(keys);
      Set<Key> expected = new LinkedHashSet<>(List.of(keys));
      assertEquals(new ArrayList<>(expected), new ArrayList<>(scope));
      assertEquals(expected.size(), scope.size());
      assertEquals(expected, scope);
      assertEquals(expected.hashCode(), scope.hashCode());
      for (int id = -1; id <= 2 * n; id++) {
        assertEquals(expected.contains(new Key(id)), scope.contains(new Key(id)));
      }
      assertFalse(scope.contains(null));
      assertTrue(scope.containsAll(expected));
      Key extra = new Key(-5);
      assertThrows(UnsupportedOperationException.class, () -> scope.add(extra));
    }
  }
}
