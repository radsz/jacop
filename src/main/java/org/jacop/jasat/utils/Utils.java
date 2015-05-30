package org.jacop.jasat.utils;

import java.util.HashSet;


/**
 * Contains utils for arrays manipulation
 * @author simon
 *
 */
public final class Utils {
	
	/**
	 * Resize the array to newSize, using the given memory pool
	 * @param array the array to resize
	 * @param newSize the size of the new array
	 * @param size the number of elements to copy from @param array
	 * @param pool the MemoryPool from which to find an int[]
	 * @return a new int[] with required size, and elements from @param array
	 */
	public final static int[]
	resize(int[] array, int newSize, int size, MemoryPool pool) {
		assert newSize > array.length : "resize to bigger size";
		assert size <= array.length;
		
		// "allocate" from the pool
		int[] answer = pool.getNew(newSize);

		// copy data
		if (size > 4) {
			System.arraycopy(array, 0, answer, 0, size);
		} else {
			for (int i = 0; i < size; ++i)
				answer[i] = array[i];
		}

		// store the old array (if not too large)
		pool.storeOld(array);

		return answer;
	}
	
	public final static int[]
    resize(int[] array, int newSize, MemoryPool pool) {
		return resize(array, newSize, array.length, pool);
	}
	                        

	/**
	 * resize for int[][]
	 * @param array		the array to resize
	 * @param newSize	the size of the array we want
	 * @return			a new array which first elements are the same
	 * as the ones in array
	 */
	public final static int[][] resize(int[][] array, int newSize) {
		int[][] answer = new int[newSize][];
		System.arraycopy(array, 0, answer, 0, array.length);
		return answer;
	}
	
	/**
	 * the same, but with the number of elements to copy from old list
	 * @param size 	the number of elements to copy from the old
	 */
	public final static int[][] resize(int[][] array, int newSize, int size) {
		assert size < newSize;
		int[][] answer = new int[newSize][];
		System.arraycopy(array, 0, answer, 0, size);
		return answer;
	}
	
	public final static Integer[] ensure(Integer[] array, int size) {
		if (array.length <= size) {
			Integer[] answer = new Integer[2 * size];
			System.arraycopy(array, 0, answer, 0, array.length);
			return answer;
		} else
			return array;
	}

	public final static <E> HashSet<E>[] ensure(HashSet<E>[] array, int size) {
		if (array.length <= size) {
			@SuppressWarnings("unchecked")
			HashSet<E>[] answer = (HashSet<E>[]) new HashSet[2 * size];
			System.arraycopy(array, 0, answer, 0, array.length);
			return answer;
		} else
			return array;
	}

	/**
	 * facility to print a clause to a string
	 * @param clause	the clause to print
	 * @return			a nice representation of the clause
	 */
	public static String showClause(int[] clause) {
		StringBuilder sb = new StringBuilder();

		for (int i = 0; i < clause.length-1; ++i) {
			int literal = clause[i];
			sb.append(literal + " ");
		}
		sb.append(clause[clause.length-1]);
		return sb.toString();
	}
	
	
	/*
	 * TODO: try to replace arithmetic negation by this var(), not() methods
	 * (which should be faster) about representation of signed literals
	 */
	
	// mask for the leftmost bit
	private final static int MASK = ~ Integer.MIN_VALUE;
	
	/**
	 * get the "absolute value" of the int (the variable that corresponds to
	 * the literal)
	 * literal -> variable
	 * @param i	the literal
	 * @return	the variable
	 */
	public static int var(int i) {
		return i & MASK; 
	}

	/**
	 * given a positive var, returns the literal that represents the negation
	 * of the variable
	 * variable -> literal
	 * @param i	the variable
	 * @return	the negated variable
	 */
	public static int not(int i) {
		return i | Integer.MIN_VALUE;
	}
	
}
