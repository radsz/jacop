/**
 *  IntervalGaussSeidel.java 
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

import java.util.Arrays;

import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatInterval;

/**
 * IntervalGaussSeidel implements Gauss-Seidel method for solving a
 * system of linear equations Ax = b with interval matrix A of
 * coefficients.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.0
 */

public class IntervalGaussSeidel {

    final static boolean debug = false;

    int MaxIterations = 100;
    double epsilon = FloatDomain.precision();

    FloatInterval[][] A;
    double[] b;
    FloatInterval[] x;

    public IntervalGaussSeidel(FloatInterval[][] A, double[] b) {
	this.A = A;
	this.b = b;
	x = new FloatInterval[b.length];

	if (debug)
	    System.out.println ("Interval Gauss-Seidel iterations:");

    }

    public FloatInterval[]  solve() {
	int N = 0;
	FloatInterval[] previousX = new FloatInterval[x.length];
	for (int i = 0; i < x.length; i++) 
	    x[i] = new FloatInterval(0.0, 0.0);

	while (true) {

	    for (int i = 0; i < b.length; i++) {
		FloatIntervalDomain sum = new FloatIntervalDomain(b[i], b[i]);

		for (int j = 0; j < A[i].length; j++)
		    if (j != i) {
			FloatIntervalDomain v1 = FloatDomain.mulBounds(A[i][j].min(), A[i][j].max(), x[j].min(), x[j].max());
			sum = FloatDomain.subBounds(sum.min(), sum.max(), v1.min(), v1.max());
		    }


		FloatIntervalDomain w = FloatDomain.divBounds(sum.min(), sum.max(), A[i][i].min(), A[i][i].max());
		x[i] = new FloatInterval(w.min(), w.max());
	    }

	    if (debug) {
		System.out.print("iteration " + N + ": {");
		for (int i = 0; i < x.length; i++) {
		    if (i == x.length - 1)
			System.out.print(x[i]);
		    else
			System.out.print(x[i] + ", ");
		}
		System.out.println("}");
	    }

	    if (N == 0) {
		N++;
		for (int i = 0; i < x.length; i++) 
		    previousX[i] = (FloatInterval)x[i].clone();

		continue;
	    }
	    else {
		N++;
		if (N == MaxIterations)
		    break;
	    }

	    boolean converged = true;
	    for (int i = 0; i < x.length; i++)
		if ( ! x[i].eq(previousX[i]))
		    converged = false;

	    if (converged) 
		break;

	    for (int i = 0; i < x.length; i++) 
		previousX[i] = (FloatInterval)x[i].clone();


	}

	return x;
    }


    public String toString() {

	String s = "";

	for (int i = 0; i < A.length; i++) {
	    for (int j = 0; j < A[i].length; j++)
		s += "" + A[i][j] + " ";
	    s += " = " + b[i] + "\n";
	}

	return s;
    }
    
}
