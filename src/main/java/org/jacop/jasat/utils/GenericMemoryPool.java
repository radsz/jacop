/*
 * GenericMemoryPool.java
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

import java.util.ArrayDeque;


/**
 * MemoryPool for arbitrary types. Less efficient than MemoryPool, but
 * maybe more efficient than allocating. To be used if some data structure
 * is often allocated/deallocated.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */
@Deprecated public final class GenericMemoryPool<E> {

    // pool of <E> objects
    private ArrayDeque<E> set = new ArrayDeque<E>();

    // factory used to create new instances if none is available
    private Factory<E> factory;

    /**
     * get an instance of E
     *
     * @return an instance of type E stored here, or a fresh
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
     *
     * @param old the E to store
     */
    public void storeOld(E old) {
        set.addLast(old);
    }


    public GenericMemoryPool(Factory<E> factory) {
        this.factory = factory;
    }

}
