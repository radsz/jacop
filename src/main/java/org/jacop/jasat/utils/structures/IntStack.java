package org.jacop.jasat.utils.structures;

import org.jacop.jasat.utils.MemoryPool;

/**
 * Special class for unboxed int stack
 *
 * @author simon
 */
public final class IntStack {

    // inner array of integers
    public int[] array = new int[40];

    // pointer to the first free slot
    public int currentIndex = 0;

    // pool of int[]
    public MemoryPool pool;

    public void clear() {
        currentIndex = 0;
    }

    /**
     * @return true if the stack is empty
     */
    public boolean isEmpty() {
        return currentIndex == 0;
    }

    /**
     * @return the number of elements of the stack
     */
    public int size() {
        return currentIndex;
    }

    /**
     * pushes the int on the stack
     *
     * @param n the element to push
     */
    public void push(int n) {

        if (currentIndex >= array.length)
            ensureCapacity(currentIndex);

        array[currentIndex++] = n;
    }

    /**
     * returns the top of the stack and removes it from the stack
     *
     * @return the top element
     */
    public int pop() {

        assert currentIndex != 0;
        //if (currentIndex == 0)
        //	throw new EmptyStackException();

        return array[--currentIndex];
    }

    /**
     * returns, without removing, the top element
     *
     * @return the top element
     */
    public int peek() {

        assert currentIndex != 0;
        //if (currentIndex == 0)
        //	throw new EmptyStackException();

        return array[currentIndex - 1];

    }

    /**
     * ensure the stack can contains at least n elements
     *
     * @param n the number of elements
     */
    private void ensureCapacity(int n) {
        if (n < array.length)
            return;

        int[] newArray = pool.getNew(2 * n);
        System.arraycopy(array, 0, newArray, 0, currentIndex);

        pool.storeOld(array);
        this.array = newArray;
    }

    @Override public String toString() {
        StringBuilder sb = new StringBuilder("IntStack [");
        for (int i = 0; i < currentIndex; ++i)
            sb.append(array[i]).append(' ');
        return sb.append(']').toString();
    }

    public IntStack(MemoryPool pool) {
        this.pool = pool;
    }

}
