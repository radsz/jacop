/**
 *  SqrtPeqR.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


package org.jacop.floats.constraints;

import org.jacop.core.Store;
import org.jacop.floats.core.FloatVar;

/**
 * Constraint sqrt(P) = R for floats
 * 
 * Boundary consistency is used.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class SqrtPeqR extends PmulQeqR {

    /**
     * It constructs a constraint sqrt(P) = R.
     * @param p variable p.
     * @param r variable r.
     */
    public SqrtPeqR(FloatVar p, FloatVar r) {
	super(r, r, p);
    }

    @Override
    public void consistency (Store store) {
	// definition of SQRT requires that both p & r qre non-negative
	// r will be bound to non negative in super class
	p.domain.inMin(store.level, p, 0.0);

	super.consistency(store);
    }


    @Override
    public String toString() {

	return id() + " : SqrtPeqR(" + p + ", " + r + " )";
    }

    public FloatVar derivative(Store store, FloatVar f, java.util.Set<FloatVar> vars, FloatVar x) {

	if (f.equals(r)) {
	    // f = sqrt(p)
	    // f' = d(p)*(1/sqrt(p)
	    FloatVar v1 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v2 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    Derivative.poseDerivativeConstraint(new SqrtPeqR(p, v1));
	    Derivative.poseDerivativeConstraint(new PdivQeqR(new FloatVar(store, 1.0, 1.0), v1, v2));
	    Derivative.poseDerivativeConstraint(new PmulQeqR(Derivative.getDerivative(store, p, vars, x), v2, v));
	    return v;
		
	}
	else if (f.equals(p)) {
	    // f = r^2
	    // f' = d(r)*2*r
	    FloatVar v1 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v2 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v3 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    Derivative.poseDerivativeConstraint(new PmulCeqR(r, 2.0, v1));
	    Derivative.poseDerivativeConstraint(new PmulQeqR(Derivative.getDerivative(store, r, vars, x), v1, v));
	    return v;
	}

	return null;

    }
}
