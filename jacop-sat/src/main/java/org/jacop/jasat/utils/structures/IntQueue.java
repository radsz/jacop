/*
 * IntQueue.java
 * <p>
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

import java.util.Iterator;
import org.jacop.jasat.utils.MemoryPool;

/**
 * Special class for unboxed int FIFO.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.10
 */
public final class IntQueue implements Iterable<Integer> {

  // inner array of integers
  public int[] array = new int[40];

  // pointer to the first element slot
  public int start;

  // pointer to the first empty slot at the right of the FIFO
  public int stop;

  // pool of int[]
  public MemoryPool pool;

  /**
   * Creates a new integer queue using the given memory pool.
   *
   * @param pool the memory pool for allocating arrays
   */
  public IntQueue(MemoryPool pool) {
    assert pool != null;
    this.pool = pool;
  }

  /** Clears all elements from the queue. */
  public void clear() {
    start = stop = 0;
  }

  /**
   * Checks if the queue is empty.
   *
   * @return true if the queue is empty
   */
  public boolean isEmpty() {
    return start == stop;
  }

  /**
   * Adds an int at the end of the FIFO.
   *
   * @param element the element to add
   */
  public void add(int element) {

    // add the element at the free position
    array[stop++] = element;
    if (stop == array.length) {
      stop = 0;
    }

    // resize if needed
    if (start == stop) {
      resize();
    }
  }

  /**
   * Inspection of the first element, without removal.
   *
   * @return the first element of the array
   */
  public int peek() {
    assert !isEmpty();

    return array[start];
  }

  /**
   * Takes the first element, removes it from the FIFO and returns it.
   *
   * @return the first element from the FIFO queue
   */
  public int pop() {
    assert start != stop;

    int answer = array[start];
    // increase start
    start++;
    if (start == array.length) {
      start = 0;
    }

    return answer;
  }

  /**
   * Returns the number of elements in the queue.
   *
   * @return the size of the queue
   */
  public int size() {
    if (start <= stop) {
      return stop - start;
    } else {
      return array.length - start + stop;
    }
  }

  /** Increase the size of the queue. */
  private void resize() {
    assert start == stop;

    int newSize = 4 * array.length;
    int[] newArray = pool.getNew(newSize);

    /*
     * copy the elements currently in the array
     */

    // copy in [0, stop) and [start, length) to the new array
    int numRight = array.length - start; // number of elements after start

    // copy elements from start to start+numRight
    System.arraycopy(array, start, newArray, 0, numRight);
    // then, copy elements from 0 to stop-1
    if (stop > 0) {
      System.arraycopy(array, 0, newArray, numRight, stop);
    }

    // update indexes
    start = 0;
    stop = numRight + stop;

    // manipulate arrays
    pool.storeOld(array);
    this.array = newArray;
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder("IntQueue [");
    for (int i : this) {
      sb.append(i).append(' ');
    }
    return sb.append(']').toString();
  }

  /**
   * Returns an iterator over the elements in this queue.
   *
   * @return an iterator over the elements in this queue
   */
  public Iterator<Integer> iterator() {
    return new QueueIterator();
  }

  private final class QueueIterator implements Iterator<Integer> {
    private int index;
    private boolean hasNext;

    {
      index = start;
      hasNext = start != stop; // only if not empty
    }

    public boolean hasNext() {
      return hasNext;
    }

    public Integer next() {
      int answer = array[index];
      findNext();
      return answer;
    }

    public void remove() {
      throw new AssertionError("not implemented");
    }

    /** Find the next index. */
    private void findNext() {
      index++;
      if (index == array.length) {
        index = 0;
      }
      if (index == stop) {
        hasNext = false;
      }
    }
  }
}
