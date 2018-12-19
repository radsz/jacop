/*
 * AFCMinDeg.java
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

import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.constraints.Constraint;

/**
 * Defines a AccumulatedFailureCount comparator (afc) for variables. Every time
 * a constraint failure is encountered the constraint afc_weight is increased by
 * one. All other constraints afc weight value is recalculated as afc_weight *
 * decay.  The comparator will choose the variable with the lowest afc_weight
 * divided by variable's domain size.
 *
 * @param <T> type of variable being compared.
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.6
 */

public class AFCMinDeg<T extends Var> implements ComparatorVariable<T> {

    private AFCMinDeg() {}

    public AFCMinDeg(Store store) {
	this(store, store.getDecay());
    }
    
    public AFCMinDeg(Store store, float decay) {
	store.setAllConstraints();
	store.afcManagement(true);
	store.setDecay(decay);
    }
    
    public int compare(float left, T var) {

        float right = afcValue(var) / ((float)var.getSize());

        if (left < right)

            return 1;

        if (left > right)

            return -1;

        return 0;

    }

    public int compare(T leftVar, T rightVar) {

        float left = afcValue(leftVar) / ((float)leftVar.getSize());

        float right = afcValue(rightVar) / ((float)rightVar.getSize());

        if (left < right)

            return 1;

        if (left > right)

            return -1;

        return 0;

    }

    public float metric(T var) {

        return afcValue(var) / ((float)var.getSize());

    }

    float afcValue(Var v) {
	float value = 0.0f;
	for (Constraint c : v.dom().constraints())
	    value += c.afc();
	return value;
    }
}
