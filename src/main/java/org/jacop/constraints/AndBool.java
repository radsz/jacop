/*
 * AndBool.java
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

package org.jacop.constraints;

import java.util.Collections;
import java.util.List;
import java.util.ArrayList;

import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * AndBool constraint implements logic and operation on its arguments
 * and returns result.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class AndBool extends DecomposedConstraint<PrimitiveConstraint> {

    PrimitiveConstraint c = null;

    /**
     * It constructs and constraint on variables.
     *
     * @param a      parameters variable.
     * @param result variable.
     */
    public AndBool(IntVar[] a, IntVar result) {

	IntVar[] r = filter(a);

	if (r == null)
	    c = new XeqC(result, 0);
	else if (r.length == 1)
	    c = new XeqY(r[0], result);
        else if (r.length == 2) {
	    c = new AndBoolSimple(r[0], r[1], result);
	}
        else
            c = new AndBoolVector(r, result);
    }

    /**
     * It constructs and constraint on variables.
     *
     * @param a      parameters variable.
     * @param result variable.
     */
    public AndBool(List<IntVar> a, IntVar result) {
        this(a.toArray(new IntVar[a.size()]), result);
    }

    /**
     * It constructs and constraint on variables.
     *
     * @param a      parameter variable.
     * @param b      parameter variable.
     * @param result variable.
     */
    public AndBool(IntVar a, IntVar b, IntVar result) {
	this(new IntVar[] {a, b}, result);
    }

    @Override public void imposeDecomposition(Store store) {
        store.impose(c);
    }

    @Override public List<PrimitiveConstraint> decompose(Store store) {
        return Collections.singletonList(c);
    }

    public String toString() {
        return c.toString();
    }

    IntVar[] filter(IntVar[] xs) {
	List<IntVar> result = new ArrayList<>();
	for (IntVar x : xs)
	    if (x.max() == 0)
		return null;
	    else if (x.min() == 1)
		continue;
	    else
		result.add(x);

	return result.toArray(new IntVar[result.size()]);
    }
}
