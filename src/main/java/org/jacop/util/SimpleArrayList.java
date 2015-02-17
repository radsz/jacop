/**
 *  SimpleArrayList.java 
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

import java.util.AbstractList;
import java.util.Arrays;
import java.util.Collection;

/**
 * Different implementation of an ArrayList data structures. This version is
 * tailored for JaCoP. Use with care, check when it uses == instead of equals().
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 * @param <V> the type which is being stored by this class.
 */

public class SimpleArrayList<V> extends AbstractList<V>{

	/**
	 * The array buffer into which the elements of the ArrayList are stored. The
	 * capacity of the ArrayList is the length of this array buffer.
	 */
	private V[] elementData;

	/**
	 * The size of the ArrayList (the number of elements it contains).
	 * 
	 */
	private int size;

	/**
	 * Constructs an empty list with an initial capacity of ten.
	 */
	public SimpleArrayList() {
		this(10);
	}

	/**
	 * Constructs a list containing the elements of the specified collection, in
	 * the order they are returned by the collection's iterator. The
	 * <tt>ArrayList</tt> instance has an initial capacity of 110% the size of
	 * the specified collection.
	 * 
	 * @param c
	 *            the collection whose elements are to be placed into this list.
	 * @throws NullPointerException
	 *             if the specified collection is null.
	 */
	@SuppressWarnings("unchecked")
	public SimpleArrayList(Collection<? extends V> c) {
		size = c.size();
		// Allow 10% room for growth
		elementData = (V[]) new Object[(int) Math.min((size * 110L) / 100,
				Integer.MAX_VALUE)];
		c.toArray(elementData);
	}

	/**
	 * Constructs an empty list with the specified initial capacity.
	 * 
	 * @param initialCapacity the initial capacity of the list.
	 */
	@SuppressWarnings("unchecked")
	public SimpleArrayList(int initialCapacity) {
		this.elementData = (V[]) new Object[initialCapacity];
	}
	
	
	
	/**
	 * AbstractList defines hashCode so that it depends on the objects included.
	 * This makes it costly (linear in the number of elements).
	 * 
	 * Taking the hash of elementData will make it faster
	 * TODO make sure this is what we want
	 */
	@Override
	public int hashCode(){
		return elementData.hashCode();
	}
	
	/**
	 * AbstractList defines equals so that it depends on the objects included.
	 * This makes it costly (linear in the number of elements).
	 * 
	 * Equality of references makes it faster
	 * TODO make sure this is what we want
	 */
	public boolean equals(Object o){
		if(o==this) {
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Appends the specified element to the end of this list.
	 * 
	 * @param o element to be appended to this list.
	 */
	public boolean add(V o) {
		ensureCapacity(size + 1);
		elementData[size++] = o;
		return true;
	}

	/**
	 * Inserts the specified element at the specified position in this list.
	 * Shifts the element currently at that position (if any) and any subsequent
	 * elements to the right (adds one to their indices).
	 * 
	 * @param index index at which the specified element is to be inserted.
	 * @param element element to be inserted.
	 */
	public void add(int index, V element) {
		ensureCapacity(size + 1); // Increments modCount!!
		System.arraycopy(elementData, index, elementData, index + 1, size
				- index);
		elementData[index] = element;
		size++;
	}

	/**
	 * Appends all of the elements in the specified Collection to the end of
	 * this list, in the order that they are returned by the specified
	 * Collection's Iterator. The behavior of this operation is undefined if the
	 * specified Collection is modified while the operation is in progress.
	 * (This implies that the behavior of this call is undefined if the
	 * specified Collection is this list, and this list is nonempty.)
	 * 
	 * @param c the elements to be inserted into this list.
	 * @return true if some elements has been added.
	 */
	public boolean addAll(Collection<? extends V> c) {
		Object[] a = c.toArray();
		int numNew = a.length;
		ensureCapacity(size + numNew); // Increments modCount
		System.arraycopy(a, 0, elementData, size, numNew);
		size += numNew;
		return numNew != 0;
	}

	/**
	 * Removes all of the elements from this list. The list will be empty after
	 * this call returns.
	 */
	public void clear() {

		Arrays.fill(elementData, 0, size, null);
		size = 0;

	}
	
	/**
	 * same as clear(), but references to objects are kept internally. This
	 * allows the operation to be constant time, but implies that objects will 
	 * not be garbage collected until their references are overwritten to
	 * store other objects.
	 */
	public void clearNoGC(){
		size = 0;
	}

	/**
	 * Returns <tt>true</tt> if this list contains the specified element.
	 * 
	 * @param elem
	 *            element whose presence in this list is to be tested.
	 * @return <code>true</code> if the specified element is present;
	 *         <code>false</code> otherwise.
	 */
	public boolean contains(Object elem) {
		return indexOf(elem) >= 0;
	}

	/**
	 * Increases the capacity of this <tt>ArrayList</tt> instance, if
	 * necessary, to ensure that it can hold at least the number of elements
	 * specified by the minimum capacity argument.
	 * 
	 * @param minCapacity
	 *            the desired minimum capacity.
	 */
	@SuppressWarnings("unchecked")
	public void ensureCapacity(int minCapacity) {
		int oldCapacity = elementData.length;
		if (minCapacity > oldCapacity) {
			Object oldData[] = elementData;
			int newCapacity = (oldCapacity * 3) / 2 + 1;
			if (newCapacity < minCapacity)
				newCapacity = minCapacity;
			elementData = (V[]) new Object[newCapacity];
			System.arraycopy(oldData, 0, elementData, 0, size);
		}
	}

	/**
	 * Private remove method that skips bounds checking and does not return the
	 * value removed.
	 */
	private void fastRemove(int index) {
		int numMoved = size - index - 1;
		if (numMoved > 0)
			System.arraycopy(elementData, index + 1, elementData, index,
					numMoved);
		elementData[--size] = null;
	}

	/**
	 * Returns the element at the specified position in this list.
	 * 
	 * @param index index of element to return.
	 * @return the element at the specified position in this list.
	 */
	public V get(int index) {

		return elementData[index];
	}
	
	/**
	 * It removes and returns the last element in the list.
	 * 
	 * @return the last element in the list.
	 */
	public V pop(){
		size--;
		return elementData[size];
	}
	
	/**
	 * It inserts the element at the end of the list
	 * @param element the added element.
	 */
	public void push(V element){
		add(element);
	}

	/**
	 * Searches for the first occurrence of the given argument, testing for
	 * equality using the <tt>equals</tt> method.
	 * 
	 * @param elem an object.
	 * @return the index of the first occurrence of the argument in this list;
	 *         returns value -1 if the object is not found.
	 */
	public int indexOf(Object elem) {
		if (elem == null) {
			for (int i = 0; i < size; i++)
				if (elementData[i] == null)
					return i;
		} else {
			for (int i = 0; i < size; i++)
				if (elem.equals(elementData[i]))
					return i;
		}
		return -1;
	}

	/**
	 * Searches for the first occurrence of the given argument, testing for
	 * equality using the == method.
	 * 
	 * @param elem an object.
	 * @param lastPosition last index to which it should check.
	 * @return the index of the first occurrence of the argument in this list;
	 *         returns value -1 if the object is not found.
	 */
	public int indexOf(Object elem, int lastPosition) {

		for (int i = 0; i <= lastPosition; i++)
			if (elem == elementData[i])
				return i;

		return -1;
	}

	/**
	 * Tests if this list has no elements.
	 * 
	 * @return true if this list has no elements; false otherwise.
	 */
	public boolean isEmpty() {
		return size == 0;
	}

	/**
	 * Returns the index of the last occurrence of the specified object in this
	 * list.
	 * 
	 * @param elem
	 *            the desired element.
	 * @return the index of the last occurrence of the specified object in this
	 *         list; returns -1 if the object is not found.
	 */
	public int lastIndexOf(Object elem) {
		if (elem == null) {
			for (int i = size - 1; i >= 0; i--)
				if (elementData[i] == null)
					return i;
		} else {
			for (int i = size - 1; i >= 0; i--)
				if (elem.equals(elementData[i]))
					return i;
		}
		return -1;
	}

	/**
	 * Removes the element at the specified position in this list. Shifts any
	 * subsequent elements to the left (subtracts one from their indices).
	 * 
	 * @param index the index of the element to removed.
	 * @return the element that was removed from the list.
	 */
	public V remove(int index) {

		V oldValue = elementData[index];

		int numMoved = size - index - 1;
		if (numMoved > 0)
			System.arraycopy(elementData, index + 1, elementData, index,
					numMoved);
		elementData[--size] = null; 
		return oldValue;
	}

	/**
	 * Removes a single instance of the specified element from this list, if it
	 * is present (optional operation). More formally, removes an element
	 * <tt>e</tt> such that <tt>(o==null ? e==null :
	 * o.equals(e))</tt>, if
	 * the list contains one or more such elements. Returns <tt>true</tt> if
	 * the list contained the specified element (or equivalently, if the list
	 * changed as a result of the call).
	 * <p>
	 * 
	 * @param o element to be removed from this list, if present.
	 * @return true if the list contained the specified element.
	 */
	public boolean remove(Object o) {
		if (o == null) {
			for (int index = 0; index < size; index++)
				if (elementData[index] == null) {
					fastRemove(index);
					return true;
				}
		} else {
			for (int index = 0; index < size; index++)
				if (o.equals(elementData[index])) {
					fastRemove(index);
					return true;
				}
		}
		return false;
	}

	/**
	 * Replaces the element at the specified position in this list with the
	 * specified element.
	 * 
	 * @param index
	 *            index of element to replace.
	 * @param element
	 *            element to be stored at the specified position.
	 * @return the element previously at the specified position.
	 */
	public V set(int index, V element) {

		V oldValue = elementData[index];
		elementData[index] = element;
		return oldValue;
	}

	/**
	 * Replaces the element at the specified position in this list with the
	 * specified element.
	 * 
	 * @param index
	 *            index of element to replace.
	 * @param element
	 *            element to be stored at the specified position.
	 */
	public void setElementAt(V element, int index) {
		elementData[index] = element;
	}

	/**
	 * Returns the number of elements in this list.
	 * 
	 * @return the number of elements in this list.
	 */
	public int size() {
		return size;
	}

	/**
	 * Returns an array containing all of the elements in this list in the
	 * correct order.
	 * 
	 * @return an array containing all of the elements in this list in the
	 *         correct order.
	 */
	public Object[] toArray() {
		Object[] result = new Object[size];
		System.arraycopy(elementData, 0, result, 0, size);
		return result;
	}

	/**
	 * Returns an array containing all of the elements in this list in the
	 * correct order; the runtime type of the returned array is that of the
	 * specified array. If the list fits in the specified array, it is returned
	 * therein. Otherwise, a new array is allocated with the runtime type of the
	 * specified array and the size of this list.
	 * <p>
	 * 
	 * If the list fits in the specified array with room to spare (i.e., the
	 * array has more elements than the list), the element in the array
	 * immediately following the end of the collection is set to <tt>null</tt>.
	 * This is useful in determining the length of the list <i>only</i> if the
	 * caller knows that the list does not contain any <tt>null</tt> elements.
	 * @param <T> the type which is being stored by a SimpleArrayList.
	 * 
	 * @param a
	 *            the array into which the elements of the list are to be
	 *            stored, if it is big enough; otherwise, a new array of the
	 *            same runtime type is allocated for this purpose.
	 * @return an array containing the elements of the list.
	 * @throws ArrayStoreException
	 *             if the runtime type of a is not a supertype of the runtime
	 *             type of every element in this list.
	 */
	@SuppressWarnings("unchecked")
	public <T> T[] toArray(T[] a) {
		if (a.length < size)
			a = (T[]) java.lang.reflect.Array.newInstance(a.getClass()
					.getComponentType(), size);
		System.arraycopy(elementData, 0, a, 0, size);
		if (a.length > size)
			a[size] = null;
		return a;
	}

	/**
	 * Check if the given index is in range. If not, throw an appropriate
	 * runtime exception. This method does *not* check if the index is negative:
	 * It is always used immediately prior to an array access, which throws an
	 * ArrayIndexOutOfBoundsException if index is negative.
	 */
	@Override
	public String toString() {
		StringBuffer buf = new StringBuffer();
		buf.append("[");

		for (int i = 0; i < elementData.length; i++) {
			buf.append(elementData[i]);
			if (i + 1 < elementData.length)
				buf.append(", ");
		}

		buf.append("]");
		return buf.toString();
	}

	/**
	 * Trims the capacity of this <tt>ArrayList</tt> instance to be the list's
	 * current size. An application can use this operation to minimize the
	 * storage of an <tt>ArrayList</tt> instance.
	 */
	@SuppressWarnings("unchecked")
	public void trimToSize() {
		int oldCapacity = elementData.length;
		if (size < oldCapacity) {
			Object oldData[] = elementData;
			elementData = (V[]) new Object[size];
			System.arraycopy(oldData, 0, elementData, 0, size);
		}
	}

}
