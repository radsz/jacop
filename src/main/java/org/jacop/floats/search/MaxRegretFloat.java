/*
 * MaxRegretFloat.java
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

package org.jacop.floats.search;

import org.jacop.search.ComparatorVariable;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatIntervalDomain;
//import org.jacop.core.ValueEnumeration;


/**
 * Defines a MaxRegretFloat comparator for Variables.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 * @param <T> variable of type FloatVar.
 */

public class MaxRegretFloat<T extends FloatVar> implements ComparatorVariable<T> {

    /**
     * It constructs MaxRegretFloat comparator.
     */
    public MaxRegretFloat() {
    }

    public int compare(float ldiff, T var) {

        // ValueEnumeration rEnum = var.domain.valueEnumeration();

        // int rmin = rEnum.nextElement();
        // int rminNext = 0;
        // if (rEnum.hasMoreElements())
        // 	rminNext = rEnum.nextElement();
        // else
        // 	rminNext = IntDomain.MaxInt;
        double rmin = var.min();
        double rminNext = ((FloatIntervalDomain) var.domain).nextValue(rmin);

        double rdiff = rminNext - rmin;

        if (ldiff > rdiff)
            return 1;
        if (ldiff < rdiff)
            return -1;
        return 0;

    }

    public int compare(T left, T right) {

        // ValueEnumeration lEnum = left.domain.valueEnumeration();

        // int lmin = lEnum.nextElement();
        // int lminNext = 0;
        // if (lEnum.hasMoreElements())
        //   lminNext = lEnum.nextElement();
        // else
        //   lminNext = IntDomain.MaxInt;
        double lmin = left.min();
        double lminNext = ((FloatIntervalDomain) left.domain).nextValue(lmin);

        double ldiff = lminNext - lmin;

        // ValueEnumeration rEnum = right.domain.valueEnumeration();

        // int rmin = rEnum.nextElement();
        // int rminNext = 0;
        // if (rEnum.hasMoreElements())
        //   rminNext = rEnum.nextElement();
        // else
        //   rminNext = IntDomain.MaxInt;
        double rmin = right.min();
        double rminNext = ((FloatIntervalDomain) right.domain).nextValue(rmin);

        double rdiff = rminNext - rmin;

        if (ldiff > rdiff)
            return 1;
        if (ldiff < rdiff)
            return -1;
        return 0;

    }

    public float metric(T o) {

        // ValueEnumeration oEnum = o.domain.valueEnumeration();

        // int omin = oEnum.nextElement();
        // int ominNext = 0;
        // if (oEnum.hasMoreElements())
        //   ominNext = oEnum.nextElement();
        // else
        //   ominNext = IntDomain.MaxInt;
        double omin = o.min();
        double ominNext = ((FloatIntervalDomain) o.domain).nextValue(omin);

        return (float) (ominNext - omin);

    }

}
