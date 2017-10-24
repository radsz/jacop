/*
 * CosPeqR_decomposed.java
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

package org.jacop.floats.constraints;

import java.util.ArrayList;
import java.util.List;

import org.jacop.constraints.DecomposedConstraint;
import org.jacop.core.Store;
import org.jacop.constraints.Constraint;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;


/**
 * Constraints cos(P) = R
 *
 * Bounds consistency can be used; third parameter of constructor controls this.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class CosPeqR_decomposed extends DecomposedConstraint<Constraint> {

    /**
     * It contains variable p.
     */
    public FloatVar p;

    /**
     * It contains variable q.
     */
    public FloatVar q;

    /**
     * It contains constraints of the CosPeqR_decomposed constraint decomposition. 
     */
    List<Constraint> constraints;

    /**
     * It constructs cos(P) = Q constraints.
     * @param p variable P
     * @param q variable Q
     */
    public CosPeqR_decomposed(FloatVar p, FloatVar q) {

        checkInputForNullness(new String[]{"p", "q"}, new Object[][]{{p}, {q}});
        this.p = p;
        this.q = q;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer("Decomposition of CosPeqR(" + p + ", " + q + "): { ");

        for (Constraint c : constraints)
            result.append(c).append(System.getProperty("line.separator"));
        result.append("}");

        return result.toString();

    }

    @Override public void imposeDecomposition(Store store) {

        if (constraints == null  || constraints.size() == 0)
            constraints = decompose(store);

        for (Constraint c : constraints)
            store.impose(c);
    }

    @Override public List<Constraint> decompose(Store store) {

        constraints = new ArrayList<Constraint>();

        FloatVar pPlus = new FloatVar(store, FloatDomain.MinFloat, FloatDomain.MaxFloat);
        Constraint c1 = new PplusCeqR(p, FloatDomain.PI / 2, pPlus);
        Constraint c2 = new SinPeqR(pPlus, q);

        constraints.add(c1);
        constraints.add(c2);

        return constraints;

    }
}
