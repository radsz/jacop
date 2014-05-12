/**
 *  SinCosExample.java 
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
 * It models tan(x) = -x for floating solver.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * 
 */

import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.SinPeqR;
import org.jacop.floats.constraints.CosPeqR;
import org.jacop.floats.search.SplitSelectFloat;

public class SinCosExample {

    void model() {

       long T1, T2, T;
	T1 = System.currentTimeMillis();

	System.out.println("\nProgram to solve sin(x) = cos(x) problem in interval -4*pi..4*pi");

	Store store = new Store();

	FloatDomain.setPrecision(1.0e-13);
	FloatDomain.intervalPrint(false);

	FloatVar p = new FloatVar(store, "p", -4*FloatDomain.PI, 4*FloatDomain.PI);
	FloatVar q = new FloatVar(store, "q", -1.0, 1.0);

	store.impose(new SinPeqR(p, q));
	store.impose(new CosPeqR(p, q));

	System.out.println( "\bVar store size: "+ store.size()+
  			    "\nNumber of constraints: " + store.numberConstraints()
			    );


	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, new FloatVar[] {p, q}, null); //new SmallestDomainFloat<FloatVar>());
	s.roundRobin=false;
	label.setAssignSolution(true);
	// label.setSolutionListener(new PrintOutListener<FloatVar>());
	label.getSolutionListener().recordSolutions(true); 
	label.getSolutionListener().searchAll(true); 
	//s.leftFirst = false;

	boolean result = label.labeling(store, s);


	if (result)
	    label.printAllSolutions();
	else
	    System.out.println ("NO SOLUTION");

	System.out.println ("\nPrecision = " + FloatDomain.precision());

	T2 = System.currentTimeMillis();
	T = T2 - T1;

	System.out.println("\n\t*** Execution time = "+ T + " ms");

    }
	
    /**
     * It executes the program which computes values for sin(x) = cos(x). 
     * 
     * @param args no arguments
     */
    public static void main(String args[]) {
		
	SinCosExample example = new SinCosExample();
		
	example.model();

    }			


}
