/*
 * IntVec.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import org.jacop.jasat.utils.MemoryPool;
import org.jacop.jasat.utils.Utils;

/**
 * Low level, efficient int vector.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class IntVec implements Iterable<Integer> {

  // memory pool
  public final MemoryPool pool;
  // real array
  public int[] array;
  // number of elements
  public int numElem;

  /**
   * Initializes the array with a memory pool.
   *
   * @param pool the pool to use for memory allocation
   */
  public IntVec(MemoryPool pool) {
    this.pool = pool;
    this.array = pool.getNew(5);
  }

  /**
   * Initialize from pool and some integers.
   *
   * @param pool the pool to use
   * @param clause the elements to add
   */
  public IntVec(MemoryPool pool, Iterable<Integer> clause) {
    this(pool);

    for (int i : clause) {
      add(i);
    }
  }

  /**
   * Add an element at the end of the array.
   *
   * @param i the element to add
   */
  public void add(int i) {
    if (numElem >= array.length) {
      array = Utils.resize(array, 2 * array.length, pool);
    }

    array[numElem++] = i;
  }

  /** Clears all elements in the array. */
  public void clear() {
    numElem = 0;
  }

  /**
   * Checks if the array contains elements.
   *
   * @return true if the array is empty
   */
  public boolean isEmpty() {
    return numElem == 0;
  }

  /**
   * Gets the element at the specified index.
   *
   * @param index the index
   * @return the element at the index
   */
  public int get(int index) {
    if (ASSERTS_ENABLED && !(index >= 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(index < numElem)) {
      throw new IllegalStateException("Assertion failed");
    }

    return array[index];
  }

  /**
   * Set the element at index index to i.
   *
   * @param index the index to modify
   * @param i the new value
   */
  public void set(int index, int i) {
    if (ASSERTS_ENABLED && !(index >= 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(index < numElem)) {
      throw new IllegalStateException("Assertion failed");
    }

    array[index] = i;
  }

  /**
   * Number of elements.
   *
   * @return number of elements in the vector
   */
  public int size() {
    return numElem;
  }

  /**
   * Remove the element at index index.
   *
   * @param index the index of the element to remove
   */
  public void remove(int index) {
    if (ASSERTS_ENABLED && !(index >= 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(index < numElem)) {
      throw new IllegalStateException("Assertion failed");
    }

    // how many elements to move
    int numToCopy = numElem - index - 1;
    if (numToCopy > 0) {
      System.arraycopy(array, index + 1, array, index, numToCopy);
    }
  }

  /**
   * This removes the element at given index. This operation does *NOT* keep the order in the array
   * (the last element may change of position)
   *
   * @param index the index to remove
   */
  public void removeFast(int index) {
    if (ASSERTS_ENABLED && !(index >= 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(index < numElem)) {
      throw new IllegalStateException("Assertion failed");
    }

    numElem--;
    // the last element ? easy !
    if (index == numElem) {
    } else {
      array[index] = array[numElem];
    }

    // note: we just move the last element in place of the one we remove
  }

  /**
   * Get a new array from the clause.
   *
   * @return a new array
   */
  public int[] toArray() {
    int[] answer = pool.getNew(numElem);
    System.arraycopy(array, 0, answer, 0, numElem);
    return answer;
  }

  @Override
  public String toString() {
    return "IntVec " + Arrays.toString(Arrays.copyOf(array, numElem));
  }

  /**
   * Returns an iterator over the elements in the vector.
   *
   * @return an iterator over the elements
   */
  public Iterator<Integer> iterator() {
    List<Integer> list = new ArrayList<>();
    for (int i = 0; i < numElem; i++) {
      list.add(array[i]);
    }
    return list.iterator();
  }
}
