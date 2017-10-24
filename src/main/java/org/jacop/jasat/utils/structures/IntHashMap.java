/*
 * IntHashMap.java
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

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * an efficient map with ints as keys. This is a hashtable with arrays.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
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
    private int cardinal = 0;

    /**
     * clear the table, removing all elements
     */
    public void clear() {
        cardinal = 0;

        for (int i = 0; i < tableKey.length; ++i)
            tableKey[i][0] = 0;
    }

    /**
     * check if the key is in the table
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
     * get the value associated with key, or null otherwise
     *
     * @param key the key
     * @return the value associated with key, or null otherwise
     */
    public E get(int key) {

        int index = hash(key, tableKey.length);
        int i = find(key, index);

        if (i == -1)
            return null;
        else
            return tableValue[index][i];
    }

    /**
     * @return true if the table is empty
     */
    public boolean isEmpty() {
        return cardinal == 0;
    }

    /**
     * put the value associated with the key
     *
     * @param key   the key
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
     * remove the key from the table
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

    public int size() {
        return cardinal;
    }

    public boolean containsKey(Object arg0) {
        if (Integer.class.isInstance(arg0))
            return containsKey((Integer) arg0);
        return false;
    }

    /**
     * double the size of the table
     */
    private void doubleSize() {
        assert tableValue.length == tableKey.length;

        // new map for temporary use
        IntHashMap<E> temp = new IntHashMap<E>(tableKey.length * 2);

        // insert all data in the new map
        for (int index = 0; index < tableKey.length; ++index) {
            for (int i = 1; i <= tableKey[index][0]; ++i) {

                int key = tableKey[index][i];
                E value = tableValue[index][i];

                // insert both key and value in the new table
                temp.put(key, value);
            }
        }

        // take fields from the temp map
        assert cardinal == temp.cardinal;
        tableKey = temp.tableKey;
        tableValue = temp.tableValue;
    }

    /**
     * try to find the key in the table. On success, will return the index of
     * the key in its bucket; otherwise, will return -1
     *
     * @param key   the key to search
     * @param index the hash of the key
     * @return the index of the key in the tableKey[hash(key)],
     * or -1 if the key is not present
     */
    private int find(int key, int index) {

        int[] bucketKey = tableKey[index];

        for (int i = 1; i <= bucketKey[0]; ++i) {
            // we found the key
            if (bucketKey[i] == key)
                return i;
        }

        // the key is not in the table
        return -1;
    }


    /**
     * hash an integer and returns the result modulo length
     *
     * @param key    the int to hash
     * @param length the length (space of keys)
     * @return an int between 0 and length-1 inclusive
     */
    private int hash(int key, int length) {
        int hashed = Math.abs(key) * HASH_PRIME;
        return hashed % length;
    }


    /**
     * builds a new map with given size
     *
     * @param size the size
     */
    @SuppressWarnings("unchecked") private IntHashMap(int size) {
        tableKey = new int[size][];
        tableValue = (E[][]) new Object[size][];

        for (int i = 0; i < size; ++i) {
            tableKey[i] = new int[MAX_BUCKET_SIZE + 2];
            tableKey[i][0] = 0;
            tableValue[i] = (E[]) new Object[MAX_BUCKET_SIZE + 2];
        }
    }

    /**
     * public constructor
     */
    public IntHashMap() {
        this(INITIAL_SIZE);
    }

    /**
     * @return the set of keys of the map
     */
    public Set<Integer> keySet() {
        return new Set<Integer>() {

            public Iterator<Integer> iterator() {
                return new KeysIterator();
            }

            public boolean add(Integer arg0) {
                if (containsKey(arg0))
                    return true;
                put(arg0, null);
                return false;
            }


            public boolean addAll(Collection<? extends Integer> arg0) {
                boolean and = true;
                for (int i : arg0)
                    and = and && add(i);
                return and;
            }


            public void clear() {
                IntHashMap.this.clear();
            }


            public boolean contains(Object arg0) {
                return containsKey(arg0);
            }


            public boolean containsAll(Collection<?> arg0) {
                for (Object o : arg0) {
                    if (!containsKey(o))
                        return false;
                }
                return true;
            }


            public boolean isEmpty() {
                return IntHashMap.this.isEmpty();
            }


            public boolean remove(Object arg0) {
                if (Integer.class.isInstance(arg0)) {
                    int i = (Integer) arg0;
                    return IntHashMap.this.remove(i);
                }
                return false;
            }


            public boolean removeAll(Collection<?> arg0) {
                boolean or = false;
                for (Object o : arg0)
                    or = or || remove(o);
                return or;
            }


            public boolean retainAll(Collection<?> arg0) {
                throw new AssertionError("not implemented");
            }


            public int size() {
                return IntHashMap.this.size();
            }


            public Object[] toArray() {
                throw new AssertionError("not implemented");
            }


            public <T> T[] toArray(T[] arg0) {
                throw new AssertionError("not implemented");
            }
        };
    }

    /**
     * iterates over all entries in the map
     *
     * @return iterator for enumeration of elements in this map
     */
    public Iterable<Map.Entry<Integer, E>> entrySet() {
        return new Iterable<Map.Entry<Integer, E>>() {

            public Iterator<Map.Entry<Integer, E>> iterator() {
                return new EntryIterator();
            }
        };
    }

    /**
     * class used to iterate on the keys of the map
     *
     * @author simon
     */
    private final class KeysIterator implements Iterator<Integer> {
        private int index = 0;
        private int bucketIndex = 0;
        private int current;
        private boolean hasNext = true;

        {
            findNext();
        }


        public boolean hasNext() {
            return hasNext;
        }


        public Integer next() {
            if (!hasNext)
                return null;
            // the next int
            int answer = current;
            findNext();
            return answer;
        }


        public void remove() {
            // TODO: verify this more precisely
            IntHashMap.this.remove(current);
        }

        /**
         * find the next key
         */
        private void findNext() {
            while (true) {
                int[] bucket = tableKey[index];
                bucketIndex++;
                if (bucketIndex > bucket[0]) {
                    // finished this bucket, go to the next
                    bucketIndex = 0;
                    index++;
                    if (index >= tableKey.length) {
                        // no more keys at all
                        hasNext = false;
                        return;
                    }
                } else {
                    current = bucket[bucketIndex];
                    return;
                }
            }
        }
    }


    /**
     * iterator over values
     *
     * @author simon
     */
    private final class EntryIterator implements Iterator<Map.Entry<Integer, E>> {
        private int index = 0;
        private int bucketIndex = 0;
        private int current;
        private E currentValue;
        private boolean hasNext = true;

        {
            findNext();
        }


        public boolean hasNext() {
            return hasNext;
        }


        public Map.Entry<Integer, E> next() {
            if (!hasNext)
                return null;
            // the next int
            Map.Entry<Integer, E> answer = new Map.Entry<Integer, E>() {
                int key = current;
                E value = currentValue;

                public Integer getKey() {
                    return key;
                }

                public E getValue() {
                    return value;
                }

                public E setValue(E arg0) {
                    throw new AssertionError("not implemented");
                }

            };
            findNext();
            return answer;
        }


        public void remove() {
            IntHashMap.this.remove(current);
        }

        /**
         * find the next key
         */
        private void findNext() {
            while (true) {
                int[] bucket = tableKey[index];
                bucketIndex++;
                if (bucketIndex > bucket[0]) {
                    // finished this bucket, go to the next
                    bucketIndex = 0;
                    index++;
                    if (index >= tableKey.length) {
                        // no more keys at all
                        hasNext = false;
                        return;
                    }
                } else {
                    current = bucket[bucketIndex];
                    currentValue = tableValue[index][bucketIndex];
                    return;
                }
            }
        }
    }
}
