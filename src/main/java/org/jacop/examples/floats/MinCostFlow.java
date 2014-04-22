/**
 *  MinCostFlow.java 
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
 * It models min-cost flow for floating solver.
 *
 * Minimum Cost Flow problem.
 * One of the most classic OR problems known: Find the minimum cost
 * flow in a network, while satisfying the demands in the nodes,
 * and not violating the capacities of the arcs.
 *
 * Testdata available at:
 * http://elib.zib.de/pub/Packages/mp-testdata/mincost/ 
 *
 * Based on minizinc model
 * min_cost_flow.mzn
 * Jakob Puchinger <jakobp@cs.mu.oz.au>
 * Wed Jun 14
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
import org.jacop.floats.constraints.PplusCeqR;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.floats.search.SmallestDomainFloat;
import org.jacop.floats.search.LargestDomainFloat;
import org.jacop.floats.search.LargestMaxFloat;
import org.jacop.floats.search.Optimize; 

public class MinCostFlow {

    double MIN_FLOAT = -1e+150;
    double MAX_FLOAT =  1e+150;

    void min_cost_flow() {

	System.out.println ("========= min_cost_flow =========");

	Store store = new Store();

	FloatDomain.setPrecision(1e-3);
	FloatDomain.intervalPrint(true);

	int n = 5;
	int m = 10;

	double[] demand = {-10.0, 0.0, 0.0, 0.0, 10.0};

	double[] costs = {10.0, 6.0, 10.0, 20.0, 2.0,  4.0, 10.0, 2.0, 10.0, 2.0};
	double[] capacity = {6.0, 4.0, 4.0, 4.0, 3.0, 3.0, 3.0, 3.0, 3.0, 4.0};
	double[] capacity_lb = {0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0};

	int[][] arcs ={  {1, 2},
			 {1, 3},
			 {1, 4},
			 {1, 5},
			 {2, 3},
			 {2, 4},
			 {2, 5},
			 {3, 4},
			 {3, 5},
			 {4, 5}
	};

	FloatVar cost = new FloatVar(store, "cost", 0.0, MAX_FLOAT);

	FloatVar[] X = new FloatVar[m];

	for (int i = 0; i < m; i++) 
	    X[i] = new FloatVar(store, "X["+i+"]", capacity_lb[i], capacity[i]);

	for (int i = 0; i < n; i++) {

	    ArrayList<FloatVar> outFlow = new ArrayList<FloatVar>();
	    ArrayList<Double> outFlowWeights = new ArrayList<Double>();
	    for (int j = 0; j < m; j++) 
		if (arcs[j][1] == i+1) {
		    outFlow.add(X[j]);
		    outFlowWeights.add(1.0);
		}

	    ArrayList<FloatVar> inFlow = new ArrayList<FloatVar>();
	    ArrayList<Double> inFlowWeights = new ArrayList<Double>();
	    for (int j = 0; j < m; j++) 
		if (arcs[j][0] == i+1) {
		    inFlow.add(X[j]);
		    inFlowWeights.add(1.0);
		}

		FloatVar outResult = new FloatVar(store, "outResult_"+ i, MIN_FLOAT, MAX_FLOAT);
		outFlow.add(outResult);
		outFlowWeights.add(-1.0);
		store.impose(new LinearFloat(store, outFlow, outFlowWeights, "==", 0.0));

		FloatVar inResult = new FloatVar(store, "inResult_"+ i, MIN_FLOAT, MAX_FLOAT);
		inFlow.add(inResult);
		inFlowWeights.add(-1.0);
		store.impose(new LinearFloat(store, inFlow, inFlowWeights, "==", 0.0));

		store.impose(new PplusCeqR(inResult, demand[i], outResult));
	}

	FloatVar[] vars = new FloatVar[X.length+1];
	double[] nCosts = new double[costs.length+1];
	for (int i = 0; i < vars.length-1; i++) {
	    vars[i] = X[i];
	    nCosts[i] = costs[i];
	}
	vars[X.length] = cost;
	nCosts[costs.length] = -1.0;

	store.impose(new LinearFloat(store, vars, nCosts, "==", 0.0));

	// solve minimize cost;
	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, X, new SmallestDomainFloat<FloatVar>());
	label.setAssignSolution(true);
	// s.leftFirst = false;
	label.setTimeOut(1);
	// label.setSolutionListener(new PrintOutListener<FloatVar>());

	label.labeling(store, s, cost); 

	/*
	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, X, new SmallestDomainFloat<FloatVar>());
	// s.roundRobin = false;
	// s.leftFirst = false;

	Optimize opt = new Optimize(store, label, s, cost);
	opt.minimize();
	*/

	System.out.println (cost);
	// System.out.printf ("cost = %.2f\n", cost.value());

	for (int i = 0; i < X.length; i++) 
	    System.out.printf ("%.2f, ", X[i].value());
	System.out.println ();
	// for (int i = 0; i < X.length; i++) {
	//     // System.out.printf ("%.0f, ", (double)(X[i].min() * costs[i]));
	//     System.out.println ("X["+i+"] = "+ X[i].min()+".."+X[i].max() + " * " + costs[i] + " result =" +
	// 			(double)(X[i].min() * costs[i]) + ".."+(double)(X[i].max() * costs[i]));
	// }

	System.out.println ("\nPrecision = " + FloatDomain.precision());

    }
    /**
     * It executes the program. 
     * 
     * @param args no arguments
     */
    public static void main(String args[]) {
		
	MinCostFlow example = new MinCostFlow();
		
	example.min_cost_flow();

    }
}
