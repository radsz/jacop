package org.jacop.jasat.utils;

import java.util.ArrayDeque;


/**
 * MemoryPool for arbitrary types. Less efficient than MemoryPool, but
 * maybe more efficient than allocating. To be used if some data structure
 * is often allocated/deallocated.
 * @author simon
 *
 */
@Deprecated
public final class GenericMemoryPool<E> {

	// pool of <E> objects
	private ArrayDeque<E> set = new ArrayDeque<E>();
	
	// factory used to create new instances if none is available
	private Factory<E> factory;

	/**
	 * get an instance of E
	 * @return	an instance of type E stored here, or a fresh
	 * instance from the factory
	 */
	public E getNew() {
		if (set.isEmpty())
			return factory.newInstance();
		else
			return set.poll();
	}

	/**
	 * stores an instance of E for future uses
	 * @param old	the E to store
	 */
	public void storeOld(E old) {
		set.addLast(old);
	}
	
	
	public GenericMemoryPool(Factory<E> factory) {
		this.factory = factory;
	}

}
