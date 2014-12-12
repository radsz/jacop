/**
 *  Rosenbrock.java 
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
 * It models rosenbrock for floating solver based on minizinc model 
 * by Håkan Kjellerstrand
 *
 * Rosenbrock function (a nonlinear standard problem).
 * 
 * This is problem 3.1 from
 * http://www.cs.cas.cz/ics/reports/v798-00.ps
 *
 * Also see:
 * http://mathworld.wolfram.com/RosenbrockFunction.html
 * http://en.wikipedia.org/wiki/Rosenbrock_function
 * """
 * It is also known as Rosenbrock's valley or Rosenbrock's banana function.
 * It has a global minimum at (x,y) = (1,1) where f(x,y) = 0.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * 
 */

import java.util.ArrayList;

import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.Search;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrintOutListener;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.SelectChoicePoint;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.floats.search.SmallestDomainFloat;
import org.jacop.floats.search.Optimize;

public class Rosenbrock {

    double MIN_FLOAT = -1e+150;
    double MAX_FLOAT =  1e+150;

    void rosenbrock() {

       long T1, T2, T;
	T1 = System.currentTimeMillis();

	System.out.println ("========= rosenbrock =========");

	Store store = new Store();

	FloatDomain.setPrecision(1e-14);
	FloatDomain.intervalPrint(false);

	FloatVar x1 = new FloatVar(store, "x1", -1.0, 8.0);
	FloatVar x2 = new FloatVar(store, "x2", -1.0, 8.0);
	FloatVar z = new FloatVar(store, "z", MIN_FLOAT, MAX_FLOAT);

	FloatVar x1x1 = new FloatVar(store, "x1x1", MIN_FLOAT, MAX_FLOAT);
	FloatVar one = new FloatVar(store, "1", 1.0, 1.0);
	FloatVar t1 = new FloatVar(store, "t1", MIN_FLOAT, MAX_FLOAT);
	FloatVar t2 = new FloatVar(store, "t2", MIN_FLOAT, MAX_FLOAT);
	FloatVar t3 = new FloatVar(store, "t3", MIN_FLOAT, MAX_FLOAT);
	FloatVar t4 = new FloatVar(store, "t4", MIN_FLOAT, MAX_FLOAT);

	//var float: z =   100.0*(x2-x1*x1)*(x2-x1*x1)+(1.0-x1)*(1.0-x1);
	store.impose(new PmulQeqR(x1, x1, x1x1));   // x1*x1
	store.impose(new PplusQeqR(x1x1, t1, x2));  // x2 - x1*x1
	store.impose(new PplusQeqR(x1, t2, one));   // 1 - x1
	store.impose(new PmulQeqR(t1, t1, t3));     // (x2 - x1*x1)*(x2 - x1*x1)
	store.impose(new PmulQeqR(t2, t2, t4));     // (1 - x1)*(1 -x1)
	store.impose(new LinearFloat(store, new FloatVar[] {z, t3, t4}, new double[] {-1.0, 100.0, 1.0}, "==", 0.0));

	System.out.println( "\bFloatVar store size: "+ store.size()+
  			    "\nNumber of constraints: " + store.numberConstraints()
			    );
	/*
	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, new FloatVar[] {x1, x2, z}, new SmallestDomainFloat<FloatVar>());
	label.setAssignSolution(true);
	// s.leftFirst = false;

	// label.setSolutionListener(new PrintOutListener<FloatVar>());

	label.labeling(store, s, z);
	*/

	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, new FloatVar[] {x1, x2}, null);

	Optimize min = new Optimize(store, label, s, z);
	boolean result = min.minimize();

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
		
	Rosenbrock example = new Rosenbrock();
		
	example.rosenbrock();

    }			
}
