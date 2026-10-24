/*
 * IntHashMap.java
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

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

/**
 * An efficient map with ints as keys. This is a hashtable with arrays.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class IntHashMap<E> {

  // prime number used to hash
  private static final int HASH_PRIME = 431;

  // default size of the tables
  private static final int INITIAL_SIZE = 40;

  // maximum size of a bucket
  private static final int MAX_BUCKET_SIZE = 10;

  // key table (the first index of every int[] contains its real length)
  private int[][] tableKey;

  // value table
  private E[][] tableValue;

  // number of elements
  private int cardinal;

  /**
   * Builds a new map with given size.
   *
   * @param size the size
   */
  @SuppressWarnings("unchecked")
  private IntHashMap(int size) {
    tableKey = new int[size][];
    tableValue = (E[][]) new Object[size][];

    for (int i = 0; i < size; i++) {
      tableKey[i] = new int[MAX_BUCKET_SIZE + 2];
      tableKey[i][0] = 0;
      tableValue[i] = (E[]) new Object[MAX_BUCKET_SIZE + 2];
    }
  }

  /** Creates a new hash map with default initial size. */
  public IntHashMap() {
    this(INITIAL_SIZE);
  }

  /** Clear the table, removing all elements. */
  public void clear() {
    cardinal = 0;

    for (int i = 0; i < tableKey.length; i++) {
      tableKey[i][0] = 0;
    }
  }

  /**
   * Check if the key is in the table.
   *
   * @param key the key
   * @return true if the key is in the table
   */
  public boolean containsKey(int key) {
    int index = hash(key, tableKey.length);
    int i = find(key, index);
    return i != -1;
  }

  /**
   * Checks if the map contains the specified key.
   *
   * @param arg0 the key to check
   * @return true if the map contains the key, false otherwise
   */
  public boolean containsKey(Object arg0) {
    if (arg0 instanceof Integer) {
      return containsKey(((Integer) arg0).intValue());
    }
    return false;
  }

  /**
   * Get the value associated with key, or null otherwise.
   *
   * @param key the key
   * @return the value associated with key, or null otherwise
   */
  public E get(int key) {

    int index = hash(key, tableKey.length);
    int i = find(key, index);

    if (i == -1) {
      return null;
    } else {
      return tableValue[index][i];
    }
  }

  /**
   * Checks if the table is empty.
   *
   * @return true if the table is empty
   */
  public boolean isEmpty() {
    return cardinal == 0;
  }

  /**
   * Put the value associated with the key.
   *
   * @param key the key
   * @param value the value
   * @return the old value, or null
   */
  public E put(int key, E value) {
    // index in the table
    int index = hash(key, tableKey.length);

    int[] bucketKey = tableKey[index];
    E[] bucketValue = tableValue[index];

    if (bucketKey[0] > MAX_BUCKET_SIZE) {
      // bucket is too long
      doubleSize();
      return put(key, value);
    } else {

      // find the occurrence of key in the bucket, if it is present
      int i = find(key, index);
      // did we find the key ?
      if (i != -1) {
        E old = bucketValue[i];
        bucketValue[i] = value;
        return old;
      } else {
        int pos = bucketKey[0] + 1;
        bucketKey[pos] = key;
        bucketValue[pos] = value;
        bucketKey[0]++;
        cardinal++;
        return null;
      }
    }
  }

  /**
   * Remove the key from the table.
   *
   * @param key the key to remove
   * @return true if the key was in the table
   */
  public boolean remove(int key) {
    // index in the table
    int index = hash(key, tableKey.length);

    int[] bucketKey = tableKey[index];
    // find the first free place, or occurrence of key in the bucket
    int i = find(key, index);
    // did we find the key ?
    boolean answer = false;
    if (i != -1) {
      E[] bucketValue = tableValue[index];
      if (bucketKey[0] == 1) {
        // only one element, which we are about to remove
        bucketKey[0] = 0;
      } else if (i != bucketKey[0]) {
        // put the last element in place of this one
        bucketKey[i] = bucketKey[bucketKey[0]];
        bucketValue[i] = bucketValue[bucketKey[0]];
        bucketKey[0]--; // one less element
      } else {
        // this is the last element, we can remove it
        bucketKey[0]--;
      }

      // one less element in the table
      cardinal--;
      answer = true;
    }
    return answer;
  }

  /**
   * Returns the number of elements in the map.
   *
   * @return the size of the map
   */
  public int size() {
    return cardinal;
  }

  /** Double the size of the table. */
  private void doubleSize() {
    if (ASSERTS_ENABLED && tableValue.length != tableKey.length) {
      throw new IllegalStateException("Assertion failed");
    }

    // new map for temporary use
    IntHashMap<E> temp = new IntHashMap<>(tableKey.length * 2);

    // insert all data in the new map
    for (int index = 0; index < tableKey.length; index++) {
      for (int i = 1; i <= tableKey[index][0]; i++) {

        int key = tableKey[index][i];
        E value = tableValue[index][i];

        // insert both key and value in the new table
        temp.put(key, value);
      }
    }

    // take fields from the temp map
    if (ASSERTS_ENABLED && cardinal != temp.cardinal) {
      throw new IllegalStateException("Assertion failed");
    }
    tableKey = temp.tableKey;
    tableValue = temp.tableValue;
  }

  /**
   * Try to find the key in the table. On success, will return the index of the key in its bucket;
   * otherwise, will return -1
   *
   * @param key the key to search
   * @param index the hash of the key
   * @return the index of the key in the tableKey[hash(key)], or -1 if the key is not present
   */
  private int find(int key, int index) {

    int[] bucketKey = tableKey[index];

    for (int i = 1; i <= bucketKey[0]; i++) {
      // we found the key
      if (bucketKey[i] == key) {
        return i;
      }
    }

    // the key is not in the table
    return -1;
  }

  /**
   * Hash an integer and returns the result modulo length.
   *
   * @param key the int to hash
   * @param length the length (space of keys)
   * @return an int between 0 and length-1 inclusive
   */
  private int hash(int key, int length) {
    int hashed = Math.abs(key) * HASH_PRIME;
    return hashed % length;
  }

  /**
   * Returns the set of keys of the map.
   *
   * @return the set of keys of the map
   */
  public Set<Integer> keySet() {
    return new Set<>() {

      @Override
      public Iterator<Integer> iterator() {
        return new KeysIterator();
      }

      @Override
      public boolean add(Integer arg0) {
        if (containsKey(arg0)) {
          return true;
        }
        put(arg0, null);
        return false;
      }

      @Override
      public boolean addAll(Collection<? extends Integer> arg0) {
        boolean and = true;
        for (int i : arg0) {
          and = and && add(i);
        }
        return and;
      }

      @Override
      public void clear() {
        IntHashMap.this.clear();
      }

      @Override
      public boolean contains(Object arg0) {
        return containsKey(arg0);
      }

      @Override
      public boolean containsAll(Collection<?> arg0) {
        for (Object o : arg0) {
          if (!containsKey(o)) {
            return false;
          }
        }
        return true;
      }

      @Override
      public boolean isEmpty() {
        return IntHashMap.this.isEmpty();
      }

      @Override
      public boolean remove(Object arg0) {
        if (arg0 instanceof Integer) {
          int i = (Integer) arg0;
          return IntHashMap.this.remove(i);
        }
        return false;
      }

      @Override
      public boolean removeAll(Collection<?> arg0) {
        boolean or = false;
        for (Object o : arg0) {
          or = or || remove(o);
        }
        return or;
      }

      @Override
      public boolean retainAll(Collection<?> arg0) {
        throw new AssertionError("not implemented");
      }

      @Override
      public int size() {
        return IntHashMap.this.size();
      }

      @Override
      public Object[] toArray() {
        throw new AssertionError("not implemented");
      }

      @Override
      public <T> T[] toArray(T[] arg0) {
        throw new AssertionError("not implemented");
      }
    };
  }

  /**
   * Iterates over all entries in the map.
   *
   * @return iterator for enumeration of elements in this map
   */
  public Iterable<Map.Entry<Integer, E>> entrySet() {
    return EntryIterator::new;
  }

  /**
   * Class used to iterate on the keys of the map.
   *
   * @author simon
   */
  private final class KeysIterator implements Iterator<Integer> {
    private int index;
    private int bucketIndex;
    private int current;
    private boolean hasNext = true;

    {
      findNext();
    }

    @Override
    public boolean hasNext() {
      return hasNext;
    }

    @Override
    public Integer next() {
      if (!hasNext) {
        throw new NoSuchElementException();
      }
      // the next int
      int answer = current;
      findNext();
      return answer;
    }

    @Override
    public void remove() {
      IntHashMap.this.remove(current);
    }

    /** Find the next key. */
    private void findNext() {
      BucketInfo info = findNextBucket(index, bucketIndex);
      index = info.index;
      bucketIndex = info.bucketIndex;
      hasNext = info.hasNext;
      if (hasNext) {
        current = tableKey[index][bucketIndex];
      }
    }
  }

  /**
   * Iterator over values.
   *
   * @author simon
   */
  private final class EntryIterator implements Iterator<Map.Entry<Integer, E>> {
    private int index;
    private int bucketIndex;
    private int current;
    private E currentValue;
    private boolean hasNext = true;

    {
      findNext();
    }

    @Override
    public boolean hasNext() {
      return hasNext;
    }

    @Override
    public Map.Entry<Integer, E> next() {
      if (!hasNext) {
        throw new NoSuchElementException();
      }
      // the next int
      Map.Entry<Integer, E> answer =
          new Map.Entry<>() {
            final int key = current;
            final E value = currentValue;

            @Override
            public Integer getKey() {
              return key;
            }

            @Override
            public E getValue() {
              return value;
            }

            @Override
            public E setValue(E arg0) {
              throw new AssertionError("not implemented");
            }
          };
      findNext();
      return answer;
    }

    @Override
    public void remove() {
      IntHashMap.this.remove(current);
    }

    /** Find the next key. */
    private void findNext() {
      BucketInfo info = findNextBucket(index, bucketIndex);
      index = info.index;
      bucketIndex = info.bucketIndex;
      hasNext = info.hasNext;
      if (hasNext) {
        current = tableKey[index][bucketIndex];
        currentValue = tableValue[index][bucketIndex];
      }
    }
  }

  /**
   * Result of finding the next bucket in iteration.
   *
   * @param index the table index
   * @param bucketIndex the bucket index
   * @param hasNext whether there are more elements
   */
  private record BucketInfo(int index, int bucketIndex, boolean hasNext) {}

  /**
   * Common logic for finding the next bucket across iterators.
   *
   * @param startIndex the starting table index
   * @param startBucketIndex the starting bucket index
   * @return information about the next bucket
   */
  private BucketInfo findNextBucket(int startIndex, int startBucketIndex) {
    int idx = startIndex;
    int bucketIdx = startBucketIndex;

    while (true) {
      int[] bucket = tableKey[idx];
      bucketIdx++;
      if (bucketIdx > bucket[0]) {
        // finished this bucket, go to the next
        bucketIdx = 0;
        idx++;
        if (idx >= tableKey.length) {
          // no more keys at all
          return new BucketInfo(idx, bucketIdx, false);
        }
      } else {
        return new BucketInfo(idx, bucketIdx, true);
      }
    }
  }
}
