/**
 *  CircleIntersection.java 
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
 * It models circle intersection for floating solver.
 *
 * The following equations are solved
 *
 *       4 = X^2 + Y^2,
 *       4 = (X-1)^2 + (Y-1)^2,
 *
 * Based on minizinc model circle_intersection.mzn by Håkan Kjellerstrand
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
import org.jacop.floats.constraints.PplusCeqR;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.floats.search.SmallestDomainFloat;

public class CircleIntersection {

    double MIN_FLOAT = -1e+150;
    double MAX_FLOAT =  1e+150;

    void circle_intersection() {

       long T1, T2, T;
	T1 = System.currentTimeMillis();

	System.out.println ("========= circle_intersection =========");

	Store store = new Store();

	FloatDomain.setPrecision(1e-13);
	FloatDomain.intervalPrint(false);

	// x*x + y*y = 4.0 /\ (x-1.0)*(x-1.0) + (y-1.0)(y-1.0) = 4.0
	FloatVar x = new FloatVar(store, "x", MIN_FLOAT, MAX_FLOAT);
	FloatVar y = new FloatVar(store, "y", MIN_FLOAT, MAX_FLOAT);

	FloatVar t1 = new FloatVar(store, "t1", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(x, x, t1));
	FloatVar t2 = new FloatVar(store, "t2", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(y, y, t2));
	store.impose(new PplusQeqR(t1, t2, new FloatVar(store, 4.0, 4.0)));

	FloatVar s1 = new FloatVar(store, "s1", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PplusCeqR(x, -1.0, s1));
	FloatVar s2 = new FloatVar(store, "s2", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PplusCeqR(y, -1.0, s2));
	FloatVar r1 = new FloatVar(store, "r1", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(s1, s1, r1));
	FloatVar r2 = new FloatVar(store, "r2", MIN_FLOAT, MAX_FLOAT);
	store.impose(new PmulQeqR(s2, s2, r2));
	store.impose(new PplusQeqR(r1, r2,  new FloatVar(store, 4.0, 4.0)));

	System.out.println( "\bVar store size: "+ store.size()+
  			    "\nNumber of constraints: " + store.numberConstraints()
			    );

	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, new FloatVar[] {x, y}, new SmallestDomainFloat<FloatVar>());
	label.setSolutionListener(new PrintOutListener<FloatVar>());
	label.getSolutionListener().recordSolutions(true); 
	label.getSolutionListener().searchAll(true); 
	label.setAssignSolution(true);
	// s.leftFirst = false;


	label.labeling(store, s);

	label.printAllSolutions();

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
		
	CircleIntersection example = new CircleIntersection();
		
	example.circle_intersection();

    }			
}
