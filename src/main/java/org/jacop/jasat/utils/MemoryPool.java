/*
 * MemoryPool.java
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


package org.jacop.jasat.utils;

import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.SolverComponent;

/**
 * Class containing int[] of different lengths, to avoid allocating/deallocating too much.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */

public final class MemoryPool implements SolverComponent {

    // the pool of arrays
    public int[][][] pool;

    // for each size, the next free slot
    public int[] indexes;

    // number of int[] stored for each length
    private int stockSize;

    /**
     * returns an array, from the pool if one is available, allocating it
     * otherwise
     * @param size  the size of the array we need
     * @return an int[size] array
     */
    public int[] getNew(int size) {

        assert size > 0 : "size must be > 0";

        int[] answer;

        // aww, too long
        if (size >= pool.length) {
            answer = new int[size];
        } else if (indexes[size] == 0) {
            // no available arrays
            answer = new int[size];
        } else {
            assert indexes[size] > 0;
            assert indexes[size] <= stockSize;

            // decrement and get this element (which slot is going to be free)
            int index = --indexes[size];
            answer = pool[size][index];

        }

        assert answer != null : "returning a null array";
        assert answer.length == size : "not the good length";

        return answer;
    }

    /**
     * save this array for a future usage, when not needed anymore
     * @param array  the array to store
     */
    public void storeOld(int[] array) {

        int size = array.length;

        if (size >= pool.length)
            return; // ignore this array, it is too long

        assert indexes[array.length] <= stockSize;

        if (indexes[size] == stockSize)
            return; // there are already enough arrays of this size

        int newIndex = indexes[size];
        indexes[size]++; // the free place is next now
        pool[size][newIndex] = array;

    }

    private void setupPool(int maxSize, int stockSize) {

        this.stockSize = stockSize;

        pool = new int[maxSize][stockSize + 1][];

        indexes = new int[maxSize];

        for (int i = 0; i < maxSize; ++i)
            indexes[i] = 0;

    }

    @Override public String toString() {
        return "MemoryPool";
    }

    public void initialize(Core core) {
        core.pool = this;
        // create the pool matrix
        setupPool(core.config.MEMORY_POOL_MAX_SIZE, core.config.MEMORY_POOL_STOCK_SIZE);
    }

}
