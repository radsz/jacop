/**
 *  SixHumpCamelFunction.java 
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
 *
 * SixHumpCamelFunction function (a nonlinear standard problem).
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * 
 */

import java.util.ArrayList;
import java.util.Set;
import java.util.HashSet;

import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.constraints.Constraint;
import org.jacop.search.Search;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrintOutListener;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.SelectChoicePoint;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.PeqC;
import org.jacop.floats.constraints.Derivative;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.floats.search.SmallestDomainFloat;
import org.jacop.floats.search.Optimize;

public class SixHumpCamelFunction {

    double MIN_FLOAT = -1e+20;
    double MAX_FLOAT =  1e+20;

    void six_hump_camel_function() {

       long T1, T2, T;
	T1 = System.currentTimeMillis();

	System.out.println ("========= Six Hump Camel Function =========");

	Store store = new Store();

	FloatDomain.setPrecision(1.0e-5);
	FloatDomain.intervalPrint(false);

	FloatVar x1 = new FloatVar(store, "x1", -2.5, 2.5);
	FloatVar x2 = new FloatVar(store, "x2", -2.5, 2.5);

	// f = 4.0*(x1*x1) - 2.1*(x1*x1*x1*x1) + (1.0/3.0)*(x1*x1*x1*x1*x1*x1) + x1*x2 - 
	//     4.0*(x2*x2) + 4.0*(x2*x2*x2*x2);

	FloatVar x1x1 = new FloatVar(store, "x1x1", MIN_FLOAT, MAX_FLOAT);
	Constraint c0 = new PmulQeqR(x1, x1, x1x1);
	store.impose(c0);

	FloatVar x2x2 = new FloatVar(store, "x2x2", MIN_FLOAT, MAX_FLOAT);
	Constraint c1 = new PmulQeqR(x2, x2, x2x2); 
	store.impose(c1);

	FloatVar x1x2 = new FloatVar(store, "x1x2", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(x1, x2, x1x2));

	FloatVar x1x1x1x1 = new FloatVar(store, "x1x1x1x1", MIN_FLOAT, MAX_FLOAT);
	Constraint c2 = new PmulQeqR(x1x1, x1x1, x1x1x1x1);
	store.impose(c2);

	FloatVar x2x2x2x2 = new FloatVar(store, "x2x2x2x2", MIN_FLOAT, MAX_FLOAT);
	Constraint c3 = new PmulQeqR(x2x2, x2x2, x2x2x2x2);
	store.impose(c3);

	FloatVar x1x1x1x1x1x1 = new FloatVar(store, "x1x1x1x1x1x1", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(x1x1, x1x1x1x1, x1x1x1x1x1x1));

	FloatVar f = new FloatVar(store, "f", MIN_FLOAT, MAX_FLOAT);
	store.impose(new LinearFloat(store,
				     new FloatVar[] {f, x1x1, x1x1x1x1, x1x1x1x1x1x1, x1x2, x2x2, x2x2x2x2},
				     new double[] {-1.0, 4.0, -2.1, (1.0/3.0), 1.0, -4.0, 4.0}, "==", 0.0));

	// with first derivative it computes minimum value
	// in 2.735s instead of 382s :)
	Set<FloatVar> vars = new HashSet<FloatVar>();
	vars.add(x1);
	vars.add(x2);
	Derivative.init(store);
	// Derivative.defineConstraint(x1x1, c0);
	// Derivative.defineConstraint(x2x2, c1);
	// Derivative.defineConstraint(x1x1x1x1, c2);
	// Derivative.defineConstraint(x2x2x2x2, c3);

	System.out.println ("================== fx1 =================");
	FloatVar fx1 = Derivative.getDerivative(store, f, vars, x1);

	System.out.println ("================== fx2 =================");
	FloatVar fx2 = Derivative.getDerivative(store, f, vars, x2);
	store.impose (new PeqC(fx1, 0.0));
	store.impose (new PeqC(fx2, 0.0));

	System.out.println( "Var store size: "+ store.size()+
  			    "\nNumber of constraints: " + store.numberConstraints()
			    );

	boolean result1 = store.consistency();

	/*
	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, new FloatVar[] {x1, x2}, null); //new SmallestDomainFloat<FloatVar>());
	label.setAssignSolution(true);
	label.setSolutionListener(new PrintOutListener<FloatVar>());
	// label.getSolutionListener().recordSolutions(true); 
	// label.getSolutionListener().searchAll(true); 
	//s.leftFirst = false;

	boolean result = label.labeling(store, s, f);
	*/

	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, new FloatVar[] {x1, x2}, null); //new LargestDomainFloat<FloatVar>());

	Optimize min = new Optimize(store, label, s, f);
	boolean result = min.minimize();

	if (!result)
	    System.out.println ("NO SOLUTION");

	System.out.println ("\nPrecision = " + FloatDomain.precision());

	T2 = System.currentTimeMillis();
	T = T2 - T1;

	System.out.println("\n\t*** Execution time = "+ T + " ms");

    }

    /**
     * It executes the program. 
     * 
     * @param args no arguments
     */
    public static void main(String args[]) {
		
	SixHumpCamelFunction example = new SixHumpCamelFunction();
		
	example.six_hump_camel_function();

    }			

}
