package org.jacop.jasat.utils.structures;

import java.util.Iterator;

import org.jacop.jasat.utils.MemoryPool;

/**
 * Special class for unboxed int FIFO
 * @author simon
 *
 */
public final class IntQueue implements Iterable<Integer> {

	// inner array of integers
	public int[] array = new int[40];

	// pointer to the first element slot
	public int start = 0;
	
	// pointer to the first empty slot at the right of the FIFO
	public int stop = 0;

	// pool of int[]
	public MemoryPool pool;
	
	public void clear() {
		start = stop = 0;
	}


	public boolean isEmpty() {
		return start == stop;
	}

	/**
	 * adds an int at the end of the FIFO
	 * @param element	the element to add
	 */
	public void add(int element) {
		
		// add the element at the free position
		array[stop++] = element;
		if (stop == array.length)
			stop = 0;
		
		// resize if needed
		if (start == stop)
			resize();
	}


	/**
	 * inspection of the first element, without removal
	 * @return the first element of the array
	 */
	public int peek() {
		assert ! isEmpty();
		
		return array[start];
	}

	/**
	 * takes the first element, removes it from the FIFO and returns it
	 *
	 * @return the first element from the FIFO queue
	 */
	public int pop() {
		assert start != stop;
		
		int answer = array[start];
		// increase start
		start++;
		if (start == array.length)
			start = 0;
		
		return answer;
	}

	public int size() {
		if (start <= stop)
			return stop - start;
		else
			return array.length - start + stop;
	}
	
	/**
	 * increase the size of the queue
	 */
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
		if (stop > 0)
			System.arraycopy(array, 0, newArray, numRight, stop);
		
		// update indexes
		start = 0;
		stop = numRight + stop;
		
		// manipulate arrays
		pool.storeOld(array);
		this.array = newArray;
	}
	
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer("IntQueue [");
		for (int i : this)
			sb.append(i).append(' ');
		return sb.append(']').toString();
	}
	
	public Iterator<Integer> iterator() {
		return new QueueIterator();
	}


	public IntQueue(MemoryPool pool) {
		assert pool != null;
		this.pool = pool;
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
		
		/**
		 * find the next index
		 */
		private final void findNext() {
			index++;
			if (index == array.length)
				index = 0;
			if (index == stop)
				hasNext = false;
		}
		
	}

}
