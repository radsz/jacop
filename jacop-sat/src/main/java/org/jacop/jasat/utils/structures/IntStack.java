/*
 * IntStack.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.utils.structures;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import org.jacop.jasat.utils.MemoryPool;

/**
 * Special class for unboxed int stack.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class IntStack {

  // pool of int[]
  public final MemoryPool pool;
  // inner array of integers
  public int[] array = new int[40];
  // pointer to the first free slot
  public int currentIndex;

  /**
   * Creates a new integer stack using the given memory pool.
   *
   * @param pool the memory pool for allocating arrays
   */
  public IntStack(MemoryPool pool) {
    this.pool = pool;
  }

  /** Clears all elements from the stack. */
  public void clear() {
    currentIndex = 0;
  }

  /**
   * Checks if the stack is empty.
   *
   * @return true if the stack is empty
   */
  public boolean isEmpty() {
    return currentIndex == 0;
  }

  /**
   * Returns the number of elements of the stack.
   *
   * @return the number of elements of the stack
   */
  public int size() {
    return currentIndex;
  }

  /**
   * Pushes the int on the stack.
   *
   * @param n the element to push
   */
  public void push(int n) {

    if (currentIndex >= array.length) {
      ensureCapacity(currentIndex);
    }

    array[currentIndex++] = n;
  }

  /**
   * Returns the top of the stack and removes it from the stack.
   *
   * @return the top element
   */
  public int pop() {

    if (ASSERTS_ENABLED && currentIndex == 0) {
      throw new IllegalStateException("Assertion failed");
    }

    return array[--currentIndex];
  }

  /**
   * Returns, without removing, the top element.
   *
   * @return the top element
   */
  public int peek() {

    if (ASSERTS_ENABLED && currentIndex == 0) {
      throw new IllegalStateException("Assertion failed");
    }

    return array[currentIndex - 1];
  }

  /**
   * Ensure the stack can contains at least n elements.
   *
   * @param n the number of elements
   */
  private void ensureCapacity(int n) {
    if (n < array.length) {
      return;
    }

    int[] newArray = pool.getNew(2 * n);
    System.arraycopy(array, 0, newArray, 0, currentIndex);

    pool.storeOld(array);
    this.array = newArray;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder("IntStack [");
    for (int i = 0; i < currentIndex; i++) {
      sb.append(array[i]).append(' ');
    }
    return sb.append(']').toString();
  }
}
