/*
 * ConstraintQueue.java
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

import java.util.NoSuchElementException;
import org.jacop.constraints.Constraint;

/**
 * One propagation queue of a store: constraints waiting for their consistency function, in first in
 * first out order and without duplicates.
 *
 * <p>The constraints are kept in a ring buffer. Whether a constraint is already waiting is a bit
 * kept in the constraint itself (one bit per queue of the store), so adding and polling never
 * allocate or hash. The order is the same as that of the {@code LinkedHashSet} used before.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class ConstraintQueue {

  private static final int INITIAL_CAPACITY = 16;

  private final Store store;

  private final int bit;

  private Constraint[] elements = new Constraint[INITIAL_CAPACITY];

  private int head;

  private int size;

  /**
   * Creates an empty queue of a store.
   *
   * @param store the store whose constraints the queue holds.
   * @param index the index of the queue within the store, below 32.
   */
  ConstraintQueue(Store store, int index) {
    if (index < 0 || index >= Integer.SIZE) {
      throw new IllegalArgumentException(
          "Queue index " + index + " outside 0.." + (Integer.SIZE - 1));
    }
    this.store = store;
    this.bit = 1 << index;
  }

  /**
   * Adds a constraint at the end of the queue unless it is already waiting in it.
   *
   * @param c the constraint to add.
   * @return true if the constraint was added, false if it was already in the queue.
   */
  public boolean add(Constraint c) {
    int membership = c.queueMembership(store);
    if ((membership & bit) != 0) {
      return false;
    }
    c.setQueueMembership(store, membership | bit);
    if (size == elements.length) {
      grow();
    }
    elements[(head + size) & (elements.length - 1)] = c;
    size++;
    return true;
  }

  /**
   * Removes and returns the first constraint of the queue.
   *
   * @return the first constraint.
   * @throws java.util.NoSuchElementException if the queue is empty.
   */
  public Constraint poll() {
    if (size == 0) {
      throw new NoSuchElementException("Empty constraint queue");
    }
    Constraint c = elements[head];
    elements[head] = null;
    head = (head + 1) & (elements.length - 1);
    size--;
    c.setQueueMembership(store, c.queueMembership(store) & ~bit);
    return c;
  }

  /**
   * Checks whether the queue is empty.
   *
   * @return true if no constraint is waiting in the queue.
   */
  public boolean isEmpty() {
    return size == 0;
  }

  /**
   * Returns the number of constraints waiting in the queue.
   *
   * @return the number of constraints in the queue.
   */
  public int size() {
    return size;
  }

  /**
   * Checks whether a constraint is waiting in the queue.
   *
   * @param c the constraint to look for.
   * @return true if the constraint is in the queue.
   */
  public boolean contains(Constraint c) {
    return (c.queueMembership(store) & bit) != 0;
  }

  /** Removes all constraints from the queue. */
  public void clear() {
    while (size > 0) {
      poll();
    }
    head = 0;
  }

  private void grow() {
    Constraint[] larger = new Constraint[elements.length * 2];
    for (int i = 0; i < size; i++) {
      larger[i] = elements[(head + i) & (elements.length - 1)];
    }
    elements = larger;
    head = 0;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder("[");
    for (int i = 0; i < size; i++) {
      if (i > 0) {
        result.append(", ");
      }
      result.append(elements[(head + i) & (elements.length - 1)]);
    }
    return result.append("]").toString();
  }
}
