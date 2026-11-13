/*
 * SmallScope.java
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

import java.util.AbstractSet;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Set;

/**
 * The scope of a constraint with few elements: an unmodifiable set in the order of first
 * occurrence, kept in an array. A {@code LinkedHashSet} with a 16-slot table costs about 300 bytes
 * for three variables, and every constraint has one: 20 % of the heap of ma-path-finding
 * ins_g32_p20_a10 while its 2 million constraints were posted.
 *
 * @param <E> the type of the elements
 */
final class SmallScope<E> extends AbstractSet<E> {

  /** The largest scope kept in an array; a larger one is a {@code LinkedHashSet}. */
  static final int MAX_SIZE = 8;

  private final Object[] elements;

  private SmallScope(Object[] elements) {
    this.elements = elements;
  }

  /**
   * Returns an unmodifiable set of the distinct elements, in the order of their first occurrence,
   * as {@code Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(elements)))} does.
   *
   * @param <E> the type of the elements
   * @param elements the elements, possibly repeated
   * @return the set of the elements
   */
  @SafeVarargs
  static <E> Set<E> of(E... elements) {
    if (elements.length > MAX_SIZE) {
      return Collections.unmodifiableSet(new LinkedHashSet<>(Arrays.asList(elements)));
    }
    Object[] distinct = new Object[elements.length];
    int n = 0;
    for (E e : elements) {
      if (indexOf(distinct, n, e) < 0) {
        distinct[n++] = e;
      }
    }
    return new SmallScope<>(n == distinct.length ? distinct : Arrays.copyOf(distinct, n));
  }

  private static int indexOf(Object[] elements, int n, Object o) {
    for (int i = 0; i < n; i++) {
      if (Objects.equals(elements[i], o)) {
        return i;
      }
    }
    return -1;
  }

  @Override
  public boolean contains(Object o) {
    return indexOf(elements, elements.length, o) >= 0;
  }

  @Override
  public int size() {
    return elements.length;
  }

  @Override
  public Object[] toArray() {
    return elements.clone();
  }

  @Override
  public Iterator<E> iterator() {
    return new Iterator<>() {
      private int next;

      @Override
      public boolean hasNext() {
        return next < elements.length;
      }

      @Override
      @SuppressWarnings("unchecked")
      public E next() {
        if (next >= elements.length) {
          throw new NoSuchElementException();
        }
        return (E) elements[next++];
      }
    };
  }
}
