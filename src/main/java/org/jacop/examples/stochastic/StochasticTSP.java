package org.jacop.examples.stochastic;

import java.util.ArrayList;
import java.util.Arrays;

import org.jacop.constraints.Circuit;
import org.jacop.constraints.Sum;
import org.jacop.constraints.XplusYeqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.PrintOutListener;
import org.jacop.stochastic.constraints.Element;
import org.jacop.stochastic.constraints.Expectation;
import org.jacop.stochastic.constraints.PrOfElement;
import org.jacop.stochastic.core.StochasticVar;

/**
 * Implements a Stochastic Travelling Salesman Problem where
 * the weights (travelling times) between the cities (nodes)
 * are stochastic variables.
 */
public class StochasticTSP extends ExampleFD{
	
	/**
	 * Generates a StochasticTSP instance.
	 */
	public void model() {
		
		store = new Store();
		vars = new ArrayList<IntVar>();
		
		int noCities = 5;
		int res = 1000;
		StochasticVar[][] distance = new StochasticVar[noCities][noCities];
		
		for (int i = 0; i < noCities; i++) {
			for (int j = 0; j < noCities; j++){
				if (i == j) 
					distance[i][j] = new StochasticVar(store, "distance["+ i + "][" + j + "]", true, 1, 1000, 1000);
				else
					distance[i][j] = new StochasticVar(store, "distance["+ i + "][" + j + "]", true, 3, 10, 150);
				//System.out.println(distance[i][j]);
			}
		}
		
		IntVar[] cities = new IntVar[noCities];
		IntVar[] Ecosts = new IntVar[noCities];
		
		for (int i = 0; i < cities.length; i++) {
			cities[i] = new IntVar(store, "cities" + i, 1, cities.length);
			Ecosts[i] = new IntVar(store, "Ecosts" + i, 0 , 1000000);
			vars.add(cities[i]);
			//vars.add(Ecosts[i]);
		}

		IntVar[][] Ps = new IntVar[cities.length][];
		
		StochasticVar[] costs = new StochasticVar[noCities];
		for (int i = 0; i < cities.length; i++){
			costs[i] = new StochasticVar(store, "costs"+i, distance);
			Ps[i] = new IntVar[costs[i].getSize()];
			for (int j=0; j < costs[i].getSize(); j++){
				Ps[i][j] = new IntVar(store, "PEl"+ i + "_" + costs[i].dom().values[j], 0, res);
				//vars.add(Ps[i][j]);
			}
			store.impose(new PrOfElement(costs[i], costs[i].dom().values, Ps[i], res));
		}
		
		store.impose(new Circuit(cities));

		for (int i = 0; i < cities.length; i++) {
            //System.out.println("Element)"+cities[i]+", "+ Arrays.asList(distance[i]) + ", "+ costs[i]+")");
			store.impose(new Element(cities[i], distance[i], costs[i], 1));
			store.imposeDecomposition(new Expectation(Ps[i], costs[i].dom().values, Ecosts[i]));
		}
		
		IntVar goal = new IntVar(store, "goal", 0, 1000000);
		vars.add(goal);
		store.impose(new Sum(Ecosts, goal));
		
		IntVar goalNegation= new IntVar(store, "goalNegation", -1000000, 0);
		store.impose(new XplusYeqC(goal, goalNegation, 0));
		
		cost = goalNegation;
	}

	/**
	 * It executes the program to solve this Travelling Salesman Problem. 
	 * @param args no argument is used.
	 */
	public static void main(String args[]) {

		StochasticTSP example = new StochasticTSP();
		
		example.model();

		if (example.searchAllAtOnce()) {
			System.out.println("Solution(s) found");			
		}
		
		//example.search.printAllSolutions();

	}
	
	/**
	 * It specifies simple search method based on most constrained static and lexigraphical 
	 * ordering of values. It searches for all solutions.
	 * 
	 * @return true if there is a solution, false otherwise.
	 */
	@Override
	public boolean searchAllAtOnce() {
		
		long T1, T2;
		T1 = System.currentTimeMillis();		
		
		SelectChoicePoint<IntVar> select = new SimpleSelect<IntVar>(vars.toArray(new IntVar[1]),
				null, new IndomainMin<IntVar>());

		search = new DepthFirstSearch<IntVar>();
		
        search.setSolutionListener(new PrintOutListener<IntVar>());
		search.getSolutionListener().searchAll(true);
		search.getSolutionListener().recordSolutions(true);
		search.setAssignSolution(true);
		
		boolean result = search.labeling(store, select);

		T2 = System.currentTimeMillis();

		if (result) {
			System.out.println("Number of solutions " + search.getSolutionListener().solutionsNo());
			//search.printAllSolutions();
		} 
		else
			System.out.println("Failed to find any solution");

		System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");

		return result;
	}		
}
