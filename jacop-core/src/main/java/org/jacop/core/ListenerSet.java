/*
 * ListenerSet.java
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

import java.io.Serial;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedHashSet;

/**
 * A set of listeners the store informs at every removed level. It keeps the insertion order of a
 * {@code LinkedHashSet} and an array copy of its elements, rebuilt after a change, so informing the
 * listeners neither allocates an iterator nor walks the linked entries.
 *
 * @param <T> the type of the listeners.
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class ListenerSet<T> extends LinkedHashSet<T> {

  @Serial private static final long serialVersionUID = 8683452581100000008L;

  private static final Object[] EMPTY = new Object[0];

  private transient Object[] elements = EMPTY;

  private transient boolean changed;

  ListenerSet() {
    super(10);
  }

  /**
   * Returns the listeners in insertion order. The array must not be modified.
   *
   * @return the listeners.
   */
  Object[] elements() {
    if (changed) {
      elements = isEmpty() ? EMPTY : toArray();
      changed = false;
    }
    return elements;
  }

  @Override
  public boolean add(T element) {
    boolean added = super.add(element);
    changed |= added;
    return added;
  }

  @Override
  public boolean remove(Object element) {
    boolean removed = super.remove(element);
    changed |= removed;
    return removed;
  }

  @Override
  public void clear() {
    super.clear();
    changed = true;
  }

  @Override
  public Iterator<T> iterator() {
    Iterator<T> iterator = super.iterator();
    return new Iterator<>() {
      @Override
      public boolean hasNext() {
        return iterator.hasNext();
      }

      @Override
      public T next() {
        return iterator.next();
      }

      @Override
      public void remove() {
        iterator.remove();
        changed = true;
      }
    };
  }

  @Override
  public boolean equals(Object other) {
    return super.equals(other);
  }

  @Override
  public int hashCode() {
    return super.hashCode();
  }

  @Override
  public String toString() {
    return Arrays.toString(toArray());
  }
}
