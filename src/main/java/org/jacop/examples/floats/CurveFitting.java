/**
 *  CurveFitting.java 
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

package org.jacop.examples.floats;

/**
 * 
 * It models curve fitting flow for floating solver.
 *
 * Curve fitting problem by Least Squares based on
 * minizinc model curve_fitting3.mzn by Håkan Kjellerstrand
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * 
 */

import java.util.ArrayList;

import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrintOutListener;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.floats.search.SmallestDomainFloat;

public class CurveFitting {

    double MIN_FLOAT = -1e+150;
    double MAX_FLOAT =  1e+150;

    void curve_fitting3() {

	System.out.println ("========= curve_fitting3 =========");

	Store store = new Store();

	FloatDomain.setPrecision(1e-14);

	int n = 19;

	double[] Sx = {0.0, 0.5,1.0,1.5,1.9,2.5,3.0,3.5,4.0,4.5,5.0,5.5,6.0,6.6,7.0,7.6,8.5,9.0,10.0};

	double[] Sy = {1.0,0.9,0.7,1.5,2.0,2.4,3.2,2.0,2.7,3.5,1.0,4.0,3.6,2.7,5.7,4.6,6.0,6.8,7.3};

	FloatVar X = new FloatVar(store, "X", MIN_FLOAT, MAX_FLOAT); //-10, 10);
	FloatVar Y = new FloatVar(store, "Y", MIN_FLOAT, MAX_FLOAT); //-10, 10);

	FloatVar[] Ex = new FloatVar[n];
	FloatVar[] Ey = new FloatVar[n];
	for (int i = 0; i < n; i++) {
	    Ex[i] = new FloatVar(store, "Ex["+i+"]", MIN_FLOAT, MAX_FLOAT);
	    Ey[i] = new FloatVar(store, "Ey["+i+"]", MIN_FLOAT, MAX_FLOAT);
	}

	FloatVar b1 = new FloatVar(store, "b1", MIN_FLOAT, MAX_FLOAT);

	FloatVar sumExEx = new FloatVar(store, "sumExEx", MIN_FLOAT, MAX_FLOAT);
	FloatVar sumExEy = new FloatVar(store, "sumExEy", MIN_FLOAT, MAX_FLOAT);

	FloatVar[] ExEx = new FloatVar[n+1];
	FloatVar[] ExEy = new FloatVar[n+1];
	double[] w = new double[n+1];
	for (int i = 0; i < n; i++) {
	    ExEx[i] = new FloatVar(store, "ExEx["+i+"]", MIN_FLOAT, MAX_FLOAT);
	    store.impose(new PmulQeqR(Ex[i], Ex[i], ExEx[i]));

	    ExEy[i] = new FloatVar(store, "ExEy["+i+"]", MIN_FLOAT, MAX_FLOAT);
	    store.impose(new PmulQeqR(Ex[i], Ey[i], ExEy[i]));

	    w[i] = 1.0;
	}
	w[n] = -1.0;
	ExEx[n] = sumExEx;

	store.impose( new LinearFloat(store, ExEx, w, "==", 0.0));

	FloatVar[] div = new FloatVar[n+1];
	for (int i = 0; i < n; i++) {
	    div[i] = new FloatVar(store, "div["+i+"]", MIN_FLOAT, MAX_FLOAT);
	    store.impose(new PmulQeqR(sumExEx, div[i], ExEy[i]));
	}
	div[n] = b1;

	double[] ones1 = new double[n+1];
	for (int i = 0; i < n; i++) 
	    ones1[i] = 1.0;
	ones1[n] = -1.0;
	store.impose(new LinearFloat(store, div, ones1, "==", 0.0));

	double[] ones = new double[n];
	for (int i = 0; i < n; i++) 
	    ones[i] = 1.0;
	store.impose(new LinearFloat(store, Ex, ones, "==", 0.0));
	store.impose(new LinearFloat(store, Ey, ones, "==", 0.0));

	for (int i = 0; i < n; i++) {
	    store.impose(new PplusQeqR(X, Ex[i], new FloatVar(store, Sx[i], Sx[i])));
	    store.impose(new PplusQeqR(Y, Ey[i], new FloatVar(store, Sy[i], Sy[i])));
	    // store.impose(new LinearFloat(store, new FloatVar[] {X, Ex[i]}, new double[] {1.0, 1.0}, "==", Sx[i]));
	    // store.impose(new LinearFloat(store, new FloatVar[] {Y, Ey[i]}, new double[] {1.0, 1.0}, "==", Sy[i]));
	}

	FloatVar[] vars = new FloatVar[2*n+1];
	for (int i = 0; i < n; i++) 
	    vars[i] = Ex[i];
	for (int i = n; i < 2*n; i++) 
	    vars[i] = Ey[i-n];
	vars[2*n] = b1;

	System.out.println( "\bFloatVar store size: "+ store.size()+
  			    "\nNumber of constraints: " + store.numberConstraints()
			    );

	// solve minimize cost;
	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, vars, null); //new SmallestDomainFloat<FloatVar>());
	label.setAssignSolution(true);
	// s.leftFirst = false;

	label.setSolutionListener(new PrintOutListener<FloatVar>());

	label.labeling(store, s);

	System.out.println (X+"\n"+Y+"\n"+b1);

	System.out.println ("\nPrecision = " + FloatDomain.precision());

    }

    /**
     * It executes the program. 
     * 
     * @param args no arguments
     */
    public static void main(String args[]) {
		
	CurveFitting example = new CurveFitting();
		
	example.curve_fitting3();

    }			
}
