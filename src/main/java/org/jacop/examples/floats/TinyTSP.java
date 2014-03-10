/**
 *  TinyTSP.java 
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
 * It models traveling slaesperson problem for floating solver.
 *
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * 
 */

import java.util.ArrayList;

import org.jacop.core.Store;
import org.jacop.core.IntVar;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.jacop.search.IndomainMin;
import org.jacop.search.PrintOutListener;
import org.jacop.constraints.Circuit;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.ElementFloat;
// import org.jacop.floats.search.SplitSelectFloat;

public class TinyTSP {

    double MIN_FLOAT = -1e+150;
    double MAX_FLOAT =  1e+150;

    void tiny_tsp() {

       long T1, T2, T;
	T1 = System.currentTimeMillis();

	System.out.println ("========= tiny_tsp =========");

	Store store = new Store();

	FloatDomain.setPrecision(1e-6);
	FloatDomain.intervalPrint(false);

	int N = 4;
	double[][] d = {{0.0, 2.23606797749979, 2.23606797749979, 3.605551275463989}, 
	                {2.23606797749979, 0.0, 1.4142135623730951, 1.4142135623730951}, 
			{2.23606797749979, 1.4142135623730951, 0.0, 2.0}, 
			{3.605551275463989, 1.4142135623730951, 2.0, 0.0}};

	IntVar[] visit = new IntVar[N];
	for (int i = 0; i < N; i++) 
	    visit[i] = new IntVar(store, "visit["+i+"]", 1, N);

	store.impose(new Circuit(visit));

	FloatVar[] dist = new FloatVar[N];
	for (int i = 0; i < N; i++) {
	    dist[i] = new FloatVar(store, "dist["+i+"]", 0.0, 10.0);
	    store.impose(new ElementFloat(visit[i], d[i], dist[i]));
	}
	
	FloatVar route = new FloatVar(store, "route", 0.0, MAX_FLOAT);
	FloatVar[] var = new FloatVar[N+1];
	for (int i = 0; i < N; i++) 
	    var[i] = dist[i];
	var[N] = route;

	store.impose(new LinearFloat(store, var, new double[] {1.0, 1.0, 1.0, 1.0, -1.0}, "==", 0.0));

	System.out.println( "\bVar store size: "+ store.size()+
  			    "\nNumber of constraints: " + store.numberConstraints()
			    );

	// DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	// SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(var, new SmallestDomainFloat<FloatVar>());
	DepthFirstSearch<IntVar> label = new DepthFirstSearch<IntVar>();
	SelectChoicePoint<IntVar> s = new SimpleSelect<IntVar>(visit, 
						  new SmallestDomain<IntVar>(), 
						  new IndomainMin<IntVar>()); 
	label.setAssignSolution(true);
	// s.leftFirst = false;

	label.setSolutionListener(new PrintOutListener<IntVar>());

	label.labeling(store, s, route);

	System.out.println (route);
	System.out.println (java.util.Arrays.asList(dist));
	System.out.println (java.util.Arrays.asList(visit));

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
		
	TinyTSP example = new TinyTSP();
		
	example.tiny_tsp();

    }			
}
