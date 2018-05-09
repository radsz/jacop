/*
 * IndomainList.java
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

package org.jacop.search;

import org.jacop.core.IntVar;

/**
 * IndomainList - implements enumeration method based on the selection
 * of the preferred values for each variable. The preferred values are
 * specified as an ordered list of values. The values will be selected
 * in the order specified by this list. If the non of the values from
 * the list is present in the current domain a default indomain method
 * will be used.
 *
 * @author Radoslaw Szymanek
 * @version 4.5
 */

public class IndomainList<T extends IntVar> implements Indomain<T> {

    private Indomain<T> defIndomain;

    private int[] order;

    /**
     * It creates an IndomainList heuristic for choosing the values.
     * @param order the order of values used to decide which values goes first.
     * @param defIndomain the default indomain used if some values are not specified by the order array.
     */
    public IndomainList(int[] order, Indomain<T> defIndomain) {

        this.order = new int[order.length];

        for (int i = 0; i < order.length; i++)
            this.order[i] = order[i];

        this.defIndomain = defIndomain;
    }

    /*
     * @throws JaCoPException if no value can be returned since list does not
     * contain a value which belongs to the domain and default indomain was not
     * supplied.
     */
    public int indomain(T var) throws RuntimeException {

        // FIXME, there is no better way than just creating a BoundDomain object?
        for (int next : order)
            if (var.dom().contains(next))
                return next;

        if (defIndomain == null)
            throw new RuntimeException();

        return defIndomain.indomain(var);
    }

}
