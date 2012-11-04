package org.jacop.examples.stochastic;

import java.util.ArrayList;

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.MostConstrainedStatic;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.stochastic.constraints.PrOfElement;
import org.jacop.stochastic.constraints.SopSeqS;
import org.jacop.stochastic.core.Operator;
import org.jacop.stochastic.core.StochasticVar;

public class TestSplusReqT extends ExampleFD {

		int[] valS, valR, valT;
		double[] minPrS, maxPrS, minPrR, maxPrR, minPrT, maxPrT;
		int resolution;
		StochasticVar S,R,T;
				
		@Override
		public void model() {

			store = new Store();
			vars = new ArrayList<IntVar>();
				
			S = new StochasticVar(store, "S", valS, minPrS, maxPrS);
			R = new StochasticVar(store, "R", valR, minPrR, maxPrR);
			T = new StochasticVar(store, "T", valT, minPrT, maxPrT);
			
			IntVar[] prS = new IntVar[valS.length];
			for (int i=0; i< valS.length; i++)
				prS[i] = new IntVar(store, "prS_" + valS[i], 0, resolution);
			store.impose(new PrOfElement(S, valS, prS, resolution));
			for (IntVar pr : prS)
				vars.add(pr);
			
			IntVar[] prR = new IntVar[valR.length];
			for (int i=0; i< valR.length; i++)
				prR[i] = new IntVar(store, "prR_" + valR[i], 0, resolution);
			store.impose(new PrOfElement(R, valR, prR, resolution));
			for (IntVar pr : prR)
				vars.add(pr);
			
			IntVar[] prT = new IntVar[valT.length];
			for (int i=0; i< valT.length; i++)
				prT[i] = new IntVar(store, "prT_" + valT[i], 0, resolution);
			store.impose(new PrOfElement(T, valT, prT, resolution));
			for (IntVar pr : prT)
				vars.add(pr);
			
			store.impose(new SopSeqS(S, new Operator("+"), R, T));

			System.out.println(store);
			
		}
			
		public static void main(String args[]) {

			TestSplusReqT example = new TestSplusReqT();
			
			int[] vS = {1, 2};
			double[] minPS = {0.3, 0.2, 0.5};
			double[] maxPS = {0.4, 0.3, 0.6};
			
			int[] vR = {2, 3};
			double[] minPR = {0.1, 0.1};
			double[] maxPR = {0.2, 0.3};
			
			int[] vT = {3,4,5};
			double[] minPT = {0, 0, 0};
			double[] maxPT = {1, 1, 1};
			
			example.valS = vS;
			example.minPrS = minPS;
			example.maxPrS = maxPS;
			example.valR = vR;
			example.minPrR = minPR;
			example.maxPrR = maxPR;
			example.valT = vT;
			example.minPrT = minPT;
			example.maxPrT = maxPT;
			example.resolution = 100;
			
			example.model();

			if (example.searchAllAtOnce()) {
				System.out.println("Solution(s) found");			
			}		
			
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
					new MostConstrainedStatic<IntVar>(), new IndomainMin<IntVar>());

			search = new DepthFirstSearch<IntVar>();
			
			search.getSolutionListener().searchAll(true);
			search.getSolutionListener().recordSolutions(false);
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
