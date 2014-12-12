/**
 *  LinearFloat.java 
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


import org.jacop.core.Var;
import org.jacop.floats.constraints.linear.Linear;
import org.jacop.floats.core.FloatVar;
import org.jacop.core.Store;

import java.util.ArrayList;

/**
 * LinearFloat constraint implements the weighted summation over several
 * Variable's . It provides the weighted sum from all Variable's on the list.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class LinearFloat extends Linear {

    /**
     * @param list
     * @param weights
     * @param sum
     */
    public LinearFloat(Store store, FloatVar[] list, double[] weights, String rel, double sum) {

	super(store, list, weights, rel, sum);
    }

    /**
     * It constructs the constraint LinearFloat. 
     * @param variables variables which are being multiplied by weights.
     * @param weights weight for each variable.
     * @param sum variable containing the sum of weighted variables.
     */
    public LinearFloat(Store store, ArrayList<? extends FloatVar> variables,
		       ArrayList<Double> weights, String rel, double sum) {

	super(store, variables, weights, rel, sum);
    }

    @Override
    public void queueVariable(int level, Var var) {
	super.queueVariable(level, var);
    }

    public FloatVar derivative(Store store, FloatVar f, java.util.Set<FloatVar> vars, FloatVar x) {

	// System.out.println ("FloatLinear of " + f + " on " + x);

	int fIndex = 0;
	while (list[fIndex] != f)
	    fIndex++;

	if (fIndex == list.length) {
	    System.out.println ("Wrong variable in derivative of " + this);
	    System.exit(0);
	}

	double w = weights[fIndex];
	FloatVar[] df = new FloatVar[list.length];
	double[] ww = new double[list.length];
	FloatVar v = null;

	for (int i = 0; i < list.length; i++) {
	    if ( i != fIndex) {
		df[i] = Derivative.getDerivative(store, list[i], vars, x);

		// System.out.println ("derivate of " + list[i] + " = " + df[i]);

		ww[i] = weights[i]/(-weights[fIndex]);
	    }
	    else {
		v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
		df[i] = v;
		ww[i] = -1.0;
	    }
	}

	org.jacop.constraints.Constraint c = new LinearFloat(store, df, ww, "==", 0.0);
	Derivative.poseDerivativeConstraint(c);

	// System.out.println ("Derivative of " + f + " over " + x + " is " + c);

	return v;
   }
}
