/**
 *  Markov.java 
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
 * From Hamdy Taha "Operations Research" (8th edition), page 649ff.
 * Fertilizer example.
 *
 * Based on minizinc model by Håkan Kjellerstrand.
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

public class Markov {

    double MIN_FLOAT = -1e+150;
    double MAX_FLOAT =  1e+150;

    void markov_chains_taha() {

       long T1, T2, T;
	T1 = System.currentTimeMillis();

	System.out.println ("========= markov_chains_taha =========");

	Store store = new Store();

	FloatDomain.setPrecision(1.0e-13);
	FloatDomain.intervalPrint(false);

	double [] cost = {100.0, 125.0, 160.0};

	FloatVar[] mean_first_return_time = new FloatVar[3];
	for (int i = 0; i < 3; i++) 
	    mean_first_return_time[i] = new FloatVar(store, "mean_first_return_time["+i+"]", 0.0, 1.0);

	FloatVar[] p = new FloatVar[3];
	for (int i = 0; i < 3; i++) 
	    p[i] = new FloatVar(store, "p["+i+"]", 0.0, 1.0);

	FloatVar tot_cost = new FloatVar(store, "tot_cost", 0.0, 385.0);

	store.impose(new LinearFloat(store, new FloatVar[] {p[2], p[0], p[1], p[2]}, new double[] {-1.0, 0.1, 0.3, 0.55}, "==", 0.0));
	store.impose(new LinearFloat(store, new FloatVar[] {p[0], p[0], p[1], p[2]}, new double[] {-1.0, 0.3, 0.1, 0.05}, "==", 0.0));
	store.impose(new LinearFloat(store, new FloatVar[] {p[1], p[0], p[1], p[2]}, new double[] {-1.0, 0.6, 0.6, 0.4}, "==", 0.0));
	FloatVar one = new FloatVar(store, "1", 1.0, 1.0);
	store.impose(new LinearFloat(store, new FloatVar[] {one, p[0], p[1], p[2]}, new double[] {-1.0, 1.0, 1.0, 1.0}, "==", 0.0));
	store.impose(new LinearFloat(store, new FloatVar[] {tot_cost, p[0], p[1], p[2]}, new double[] {-1.0, 100.0, 125.0, 160.0}, "==", 0.0));


	FloatVar[] vars = new FloatVar[7];
	for (int i = 0; i < 3; i++) 
	    vars[i] = p[i];
	for (int i = 0; i < 3; i++) 
	    vars[i+3] = mean_first_return_time[i];
	vars[6] = tot_cost;

	System.out.println( "\bVar store size: "+ store.size()+
  			    "\nNumber of constraints: " + store.numberConstraints()
			    );

	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, vars, null); //new SmallestDomainFloat<FloatVar>());
	label.setAssignSolution(true);
	// label.setSolutionListener(new PrintOutListener<FloatVar>());
	label.getSolutionListener().recordSolutions(true); 
	// label.getSolutionListener().searchAll(true); 
	//s.leftFirst = false;

	boolean result = label.labeling(store, s, tot_cost);


	if (result)
	    System.out.println (tot_cost);
	else
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
		
	Markov example = new Markov();
		
	example.markov_chains_taha();

    }			
}
