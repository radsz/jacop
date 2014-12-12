/**
 *  SimpleHashSet.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.jacop.util;

import java.util.Arrays;

/**
 * This class provides very simple HashSet functionality. Designed specially for
 * maintaining pending constraints for evaluation. It's implementation was
 * partially based on standard hash set implementation as implemented in java
 * util class.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 * @param <E> Class being stored in SimpleHashSet.
 */

public class SimpleHashSet<E> {

	@SuppressWarnings("hiding")
	class Entry<E> {

		@SuppressWarnings("unchecked")
		public Entry chain;

		public final E element;

		@SuppressWarnings("unchecked")
		public Entry next;

		/**
		 * Create new entry.
		 */
		Entry(E el) {
			element = el;
			next = null;
		}

		/**
		 * Create new entry.
		 */
		Entry(E el, Entry<E> n) {
			element = el;
			next = n;
		}

		@SuppressWarnings("unchecked")
		public boolean add(E addedElement) {
			if (element == addedElement)
				return false;
			if (next != null)
				return next.add(addedElement);
			else {
				next = new Entry(addedElement);
				lastEntry.chain = next;
				lastEntry = next;
				return true;
			}
		}

		@SuppressWarnings("unchecked")
		public boolean contains(E checkedElement) {
			if (element == checkedElement)
				return true;
			if (next != null)
				return next.contains(checkedElement);
			else {
				return false;
			}
		}

	}

	/**
	 * The default initial capacity - MUST be a power of two.
	 */
	static final int DEFAULT_INITIAL_CAPACITY = 16;

	/**
	 * The load factor used when none specified in constructor.
	 */
	static final float DEFAULT_LOAD_FACTOR = 0.75f;

	/**
	 * The maximum capacity, used if a higher value is implicitly specified by
	 * either of the constructors with arguments. MUST be a power of two <= 1<<30.
	 */
	static final int MAXIMUM_CAPACITY = 1 << 30;

	/**
	 * Returns a hash value for the specified object. In addition to the
	 * object's own hashCode, this method applies a "supplemental hash
	 * function," which defends against poor quality hash functions. This is
	 * critical because SimpleHashSet uses power-of two length hash tables.
	 * <p>
	 * 
	 * The shift distances in this function were chosen as the result of an
	 * automated search over the entire four-dimensional search space.
	 * 
	 * This hash code function implementation is original Sun function proposed
	 * in util package.
	 */

	static int hash(Object x) {
		int h = x.hashCode();

		h += ~(h << 9);
		h ^= (h >>> 14);
		h += (h << 4);
		h ^= (h >>> 10);
		return h;
	}

	/**
	 * Returns index for hash code h.
	 */
	static int indexFor(int h, int length) {
		return h & (length - 1);
	}

	/**
	 * It points to the first Entry to be removed.
	 */
	transient Entry<E> firstEntry = null;

	/**
	 * The initial capacity for the hash set.
	 */
	int initialCapacity;

	/**
	 * It points to the last Entry being add.
	 */
	transient Entry<E> lastEntry = null;

	/**
	 * The load factor for the hash set.
	 */
	final float loadFactor;

	/**
	 * The number of elements contained in this set.
	 */
	transient int size;

	/**
	 * The set, resized as necessary. Length MUST Always be a power of two.
	 */
	@SuppressWarnings("unchecked")
	private transient Entry[] table;

	/**
	 * The next size value at which to resize (capacity * load factor).
	 */
	int threshold;

	/**
	 * Constructs an empty <tt>HashSet</tt> with the default initial capacity
	 * (16) and the default load factor (0.75).
	 */
	public SimpleHashSet() {
		this.loadFactor = DEFAULT_LOAD_FACTOR;
		threshold = (int) (DEFAULT_INITIAL_CAPACITY * DEFAULT_LOAD_FACTOR);
		table = new Entry[DEFAULT_INITIAL_CAPACITY];
		initialCapacity = table.length;
	}

	/**
	 * Constructs an empty <tt>HashSet</tt> with the specified initial
	 * capacity and the default load factor (0.75).
	 * 
	 * @param initialCapacity
	 *            the initial capacity.
	 * @throws IllegalArgumentException
	 *             if the initial capacity is negative.
	 */
	public SimpleHashSet(int initialCapacity) {
		this(initialCapacity, DEFAULT_LOAD_FACTOR);
	}

	/**
	 * Constructs an empty <tt>HashSet</tt> with the specified initial
	 * capacity and load factor.
	 * 
	 * @param initialCapacity
	 *            The initial capacity.
	 * @param loadFactor
	 *            The load factor.
	 * @throws IllegalArgumentException
	 *             if the initial capacity is negative or the load factor is
	 *             nonpositive.
	 */
	public SimpleHashSet(int initialCapacity, float loadFactor) {
		if (initialCapacity < 0)
			throw new IllegalArgumentException("Illegal initial capacity: "
					+ initialCapacity);
		if (initialCapacity > MAXIMUM_CAPACITY)
			initialCapacity = MAXIMUM_CAPACITY;
		if (loadFactor <= 0 || Float.isNaN(loadFactor))
			throw new IllegalArgumentException("Illegal load factor: "
					+ loadFactor);

		// Find a power of 2 >= initialCapacity
		int capacity = 1;
		while (capacity < initialCapacity)
			capacity <<= 1;

		this.loadFactor = loadFactor;
		threshold = (int) (capacity * loadFactor);
		table = new Entry[capacity];
		initialCapacity = table.length;
	}

	/**
	 * Adds the specified element to this set.
	 * 
	 * @param element
	 *            element with which the specified value is to be associated.
	 * @return <tt>true</tt> if object is inserted and <tt>false</tt> if
	 *         object was already in the set.
	 */
	@SuppressWarnings("unchecked")
	public boolean add(E element) {
		int hash = hash(element);
		int i = indexFor(hash, table.length);

		Entry<E> e = table[i];

		if (e != null) {
			boolean result = e.add(element);

			if (result) {
				// checks threshold and increases size
				if (size++ >= threshold)
					resize(2 * table.length);
			}
			return result;
		} else {
			e = table[i] = new Entry<E>(element);

			if (firstEntry == null) {
				firstEntry = e;
				lastEntry = firstEntry;
			} else {
				lastEntry.chain = e;
				lastEntry = e;
			}

			// checks threshold and increases size
			if (size++ >= threshold)
				resize(2 * table.length);
		}

		return true;
	}

	/**
	 * Removes all elements from this set.
	 */
	public void clear() {

	//	Entry<E>[] tab = table;
	//	for (int i = tab.length - 1; i >= 0; i--)
	//		tab[i] = null;

		Arrays.fill(table, null);
		
		firstEntry = null;
		lastEntry = null;

		size = 0;
	}

	/**
	 * Clones this set.
	 */

	@Override
	@SuppressWarnings("unchecked")
	public Object clone() {
		SimpleHashSet<E> result = new SimpleHashSet<E>();

		result.table = new Entry[table.length];
		result.size = size;
		result.initialCapacity = result.table.length;

		for (int i = table.length - 1; i >= 0; i--) {
			Entry<E> e = table[i];
			if (e != null) {
				result.table[i] = new Entry<E>(e.element);
				e = e.next;
			}

			while (e != null) {
				result.table[i].add(e.element);
				e = e.next;
			}
		}

		return result;
	}

	/**
	 * Returns the boolean value which specifies if given element is already in
	 * this identity hash set.
	 * 
	 * @param element
	 *            the element whose existence in the hash set is to be checked.
	 * @return the boolean value which specifies if given element exists in a
	 *         hash set.
	 */
	@SuppressWarnings( { "unchecked" })
	public boolean contains(E element) {
		int hash = hash(element);
		int i = indexFor(hash, table.length);
		Entry<E> e = table[i];
		if (e != null)
			return e.contains(element);
		else
			return false;
	}

	/**
	 * Returns <tt>true</tt> if this set contains no elements.
	 * 
	 * @return <tt>true</tt> if this set contains no elements.
	 */
	public boolean isEmpty() {
		return size == 0;
	}

	/**
	 * Removes and returns an entry removed from the HashSet. Returns null if
	 * the HashSet contains no entry.
	 * @return the first entry which has been removed. 
	 */

	@SuppressWarnings("unchecked")
	public E removeFirst() {

		if (size == 0)
			return null;

		Entry<E> removed = firstEntry;

		firstEntry = firstEntry.chain;

		size--;

		int hash = hash(removed.element);
		int i = indexFor(hash, table.length);

		if (removed.next == null)
			table[i] = null;
		else
			table[i] = removed.next;

		return removed.element;

	}

	/**
	 * Rehashes the contents of this set into a new array with a larger
	 * capacity. This method is called automatically when the number of elements
	 * in this set reaches its threshold.
	 * 
	 * If current capacity is MAXIMUM_CAPACITY, this method does not resize the
	 * set, but sets threshold to Integer.MAX_VALUE. This has the effect of
	 * preventing future calls.
	 * 
	 * @param newCapacity
	 *            the new capacity, MUST be a power of two; must be greater than
	 *            current capacity unless current capacity is MAXIMUM_CAPACITY
	 *            (in which case value is irrelevant).
	 */
	@SuppressWarnings("unchecked")
	void resize(int newCapacity) {

		Entry[] oldTable = table;
		int oldCapacity = oldTable.length;
		if (oldCapacity == MAXIMUM_CAPACITY) {
			threshold = Integer.MAX_VALUE;
			return;
		}

		table = new Entry[newCapacity];
		threshold = (int) (newCapacity * loadFactor);
		transfer(oldTable);

	}

	/**
	 * Returns the number of elements in this set.
	 * 
	 * @return the number of elements in this set.
	 */
	public int size() {
		return size;
	}

	/**
	 * Returns string representation of the hash set.
	 */

	@Override
	@SuppressWarnings("unchecked")
	public String toString() {
		StringBuffer S = new StringBuffer();

		S.append("SimpleHashSet[");

		Entry[] tab = table;

		for (int i = 0; i < tab.length; i++) {

			Entry<E> e = tab[i];

			while (e != null) {
				S.append(e.element);
				e = e.next;
				if (e != null)
					S.append(",");
			}

		}

		S.append("]");

		return S.toString();
	}

	/**
	 * Transfer all entries from current table to newTable.
	 */
	@SuppressWarnings("unchecked")
	void transfer(Entry[] oldTable) {

		size = 0;

		Entry<E> temp = firstEntry;
		firstEntry = null;

		while (temp != null) {
			add(temp.element);
			temp = temp.chain;
		}

	}

}
