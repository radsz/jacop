package org.jacop.examples.stochastic;

import java.util.ArrayList;

import org.jacop.constraints.Sum;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.search.*;
import org.jacop.stochastic.constraints.Expectation;
import org.jacop.stochastic.constraints.PrOfElement;
import org.jacop.stochastic.constraints.SopSeqS;
import org.jacop.stochastic.constraints.SopXeqS;
import org.jacop.stochastic.core.Operator;
import org.jacop.stochastic.core.StochasticVar;

/**
 * Implements a Static Stochastic Knapsack Problem (SSKP). 
 */
public class SSKP extends ExampleFD{

	/*
	 * SSKP example given in the paper:
	 * Roberto Rossi, S. Armagan Tarim, Brahim Hnich, and Steven Prestwich. 
	 * Cost-based domain Filtering for stochastic constraint programming. 
	 * In Proceedings of the 14th International Conference on the Principles 
	 * and Practice of Constraint Programming, page 235.
	 */
	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		int res = 10;
		
		int noItems = 5;		
		int volume = 30;
		int fine = 2;
		
		/*
		 * Decision variables : quantity[i] of the ith item.
		 */
		IntVar quantity[] = new IntVar[noItems];
		for (int i = 0; i < quantity.length; i++) {
			quantity[i] = new IntVar(store, "Quantity_" + i, 0, 1);
			vars.add(quantity[i]);
		}	
		
		StochasticVar[] weights = new StochasticVar[noItems];
		StochasticVar[] effectiveWeights = new StochasticVar[noItems];
		IntVar[][] prEffWts = new IntVar[noItems][];
		
		int[][] itemWeights = {{10,8},
							  {10,12},
							  {9,13},
							  {4,6},
							  {12,15}};
							  
		double[][] minPs = {{0.5,0.5},
							{0.5,0.5},
							{0.5,0.5},
							{0.5,0.5},
							{0.5,0.5},};
		
		double[][] maxPs = {{0.5,0.5},
							{0.5,0.5},
							{0.5,0.5},
							{0.5,0.5},
							{0.5,0.5},};
		
		/*
		 * Stochastic Variables : weights[i] of the ith object.
		 */
		for (int i=0; i<noItems; i++)
			weights[i] = new StochasticVar(store, "Wt_" + i, itemWeights[i], minPs[i], maxPs[i]);
		
		int[] profits = {10, 15, 20, 5, 25};
			
		for (int i=0; i < profits.length; i++)
			profits[i] *= res;
		
		IntVar profit = new IntVar(store, "Profit", 0, 1000000);
		vars.add(profit);
		store.impose(new SumWeight(quantity, profits, profit));
		
		/*
		 * Imposing efectiveWeights[i] = weights[i]*quantity[i].
		 */
		for (int i=0; i < noItems; i++){
			
			effectiveWeights[i] = new StochasticVar(store, "EffWt_"+i, weights[i], quantity[i], new Operator("*"));
			prEffWts[i] = new IntVar[effectiveWeights[i].getSize()];
			
			for (int j = 0; j<effectiveWeights[i].getSize(); j++){
				prEffWts[i][j] = new IntVar(store, "effWt_" + i + "_val" + effectiveWeights[i].dom().values[j], 0, res);
				//vars.add(prEffWts[i][j]);
			}
			
			store.impose(new Sum(prEffWts[i], new IntVar(store, "Res", res,res)));

			store.impose(new PrOfElement(effectiveWeights[i], effectiveWeights[i].dom().values, prEffWts[i], res));
			
			store.impose(new SopXeqS(weights[i],new Operator("*"), quantity[i], effectiveWeights[i]));
		}
		
		/*
		 * Imposing Sum[i = 1 : noItems] {effectiveWeights[i] = tmp[noItems-2]}
		 */
		StochasticVar[] tmp = new StochasticVar[noItems-1];
		IntVar[][] prTmp = new IntVar[noItems][];
		
		tmp[0] = new StochasticVar(store, "tmp" + 0, effectiveWeights[0], effectiveWeights[1], new Operator("+"));
		prTmp[0] = new IntVar[tmp[0].getSize()];
		
		for (int j = 0; j < tmp[0].getSize(); j++){
			prTmp[0][j] = new IntVar(store, "tmp_" + 0 + "_val" + tmp[0].dom().values[j], 0, res);
			//vars.add(prTmp[0][j]);
		}
		store.impose(new PrOfElement(tmp[0], tmp[0].dom().values, prTmp[0], res));
		
		store.impose(new SopSeqS(effectiveWeights[0], new Operator("+"), effectiveWeights[1], tmp[0]));
		
		for (int i = 1; i < noItems-1; i++){
			
			tmp[i] = new StochasticVar(store, "tmp"+i, tmp[i-1], effectiveWeights[i+1], new Operator("+"));
			prTmp[i] = new IntVar[tmp[i].getSize()];
			
			for (int j = 0; j < tmp[i].getSize(); j++){
				prTmp[i][j] = new IntVar(store, "tmp_" + i + "_val" + tmp[i].dom().values[j], 0, res);
				//vars.add(prTmp[i][j]);
			}
			
			store.impose(new PrOfElement(tmp[i],tmp[i].dom().values, prTmp[i],res));
			store.impose(new SopSeqS(tmp[i-1], new Operator("+"), effectiveWeights[i+1], tmp[i]));
		}		
		
		/*
		 * Imposing Expectation[tmp[noItems-2] - volume > 0] 
		 */
		int[] excessWt = new int[tmp[noItems-2].getSize()];
		
		for (int i = 0; i < excessWt.length; i++){
			excessWt[i] = (tmp[noItems-2].dom().values[i] - volume > 0) ? (tmp[noItems-2].dom().values[i] - volume) : 0;
		}
		
		IntVar E = new IntVar(store, "Expectation", 0, tmp[noItems-2].dom().values[tmp[noItems-2].getSize()-1]*res);
		//vars.add(E);
		store.imposeDecomposition(new Expectation(prTmp[noItems-2], excessWt, E));
		
		IntVar penalty = new IntVar(store, "Penalty", -1000000, 0);
		//vars.add(penalty);
		store.impose(new XmulCeqZ(E, -1*fine, penalty));
				
		IntVar goal = new IntVar(store, "goal", 0, 1000000);
		vars.add(goal);
		store.impose(new XplusYeqZ(profit, penalty, goal));
		
		IntVar goalNegation= new IntVar(store, "goalNegation", -1000000, 0);
		store.impose(new XplusYeqC(goal, goalNegation, 0));
		
		cost = goalNegation;
	}
	
	/**
	 * Generates a random SSKP instance.
	 */
	public void modelRandom() {
		
		store = new Store();
		vars = new ArrayList<IntVar>();
		int res = 1000;
		
		int noItems = 7;		
		int volume = 30;
		int fine = 2;
		int profits[] = new int[noItems];
		
		/*
		 * Decision variables : quantity[i] of the ith item.
		 */
		IntVar quantity[] = new IntVar[noItems];
		for (int i = 0; i < quantity.length; i++) {
			quantity[i] = new IntVar(store, "Quantity_" + i, 0, 1);
			vars.add(quantity[i]);
		}	
		
		StochasticVar[] weights = new StochasticVar[noItems];
		StochasticVar[] effectiveWeights = new StochasticVar[noItems];
		IntVar[][] prEffWts = new IntVar[noItems][];
		
		/*
		 * Stochastic Variables : weights[i] of the ith object, 
		 * Genrated randomly along with profits[i]
		 */
		for (int i = 0; i<noItems; i++){
			weights[i] = new StochasticVar(store, "Wt_" + i, true, 2, 5, 20);
			profits[i] = (int)Math.random()*(25-5) + 5;
		}
			
		for (int i=0; i < profits.length; i++)
			profits[i] *= res;
		
		IntVar profit = new IntVar(store, "Profit", 0, 1000000);
		vars.add(profit);
		store.impose(new SumWeight(quantity, profits, profit));
		
		/*
		 * Imposing efectiveWeights[i] = weights[i]*quantity[i].
		 */
		for (int i=0; i < noItems; i++){
			
			effectiveWeights[i] = new StochasticVar(store, "EffWt_"+i, weights[i], quantity[i], new Operator("*"));
			prEffWts[i] = new IntVar[effectiveWeights[i].getSize()];
			
			for (int j = 0; j<effectiveWeights[i].getSize(); j++){
				prEffWts[i][j] = new IntVar(store, "effWt_" + i + "_val" + effectiveWeights[i].dom().values[j], 0, res);
				//vars.add(prEffWts[i][j]);
			}
			
			store.impose(new Sum(prEffWts[i], new IntVar(store, "Res", res,res)));

			store.impose(new PrOfElement(effectiveWeights[i], effectiveWeights[i].dom().values, prEffWts[i], res));
			
			store.impose(new SopXeqS(weights[i], new Operator("*"), quantity[i], effectiveWeights[i]));
		}
		
		/*
		 * Imposing Sum[i = 1 : noItems] {effectiveWeights[i] = tmp[noItems-2]}
		 */
		StochasticVar[] tmp = new StochasticVar[noItems-1];
		IntVar[][] prTmp = new IntVar[noItems][];
		
		tmp[0] = new StochasticVar(store, "tmp" + 0, effectiveWeights[0], effectiveWeights[1], new Operator("+"));
		prTmp[0] = new IntVar[tmp[0].getSize()];
		for (int j = 0; j < tmp[0].getSize(); j++){
			prTmp[0][j] = new IntVar(store, "tmp_" + 0 + "_val" + tmp[0].dom().values[j], 0, res);
			//vars.add(prTmp[0][j]);
		}
		store.impose(new PrOfElement(tmp[0], tmp[0].dom().values, prTmp[0], res));
		
		store.impose(new SopSeqS(effectiveWeights[0], new Operator("+"), effectiveWeights[1], tmp[0]));
		
		for (int i = 1; i < noItems-1; i++){
			
			tmp[i] = new StochasticVar(store, "tmp"+i, tmp[i-1], effectiveWeights[i+1], new Operator("+"));
			prTmp[i] = new IntVar[tmp[i].getSize()];
			
			for (int j = 0; j < tmp[i].getSize(); j++){
				prTmp[i][j] = new IntVar(store, "tmp_" + i + "_val" + tmp[i].dom().values[j], 0, res);
				//vars.add(prTmp[i][j]);
			}
			
			store.impose(new PrOfElement(tmp[i],tmp[i].dom().values, prTmp[i],res));
			store.impose(new SopSeqS(tmp[i-1], new Operator("+"), effectiveWeights[i+1], tmp[i]));
		}		
		
		/*
		 * Imposing Expectation[tmp[noItems-2] - volume > 0] 
		 */
		int[] excessWt = new int[tmp[noItems-2].getSize()];
		
		for (int i = 0; i < excessWt.length; i++){
			excessWt[i] = (tmp[noItems-2].dom().values[i] - volume > 0) ? (tmp[noItems-2].dom().values[i] - volume) : 0;
		}
		
		IntVar E = new IntVar(store, "Expectation", 0, tmp[noItems-2].dom().values[tmp[noItems-2].getSize()-1]*res);
		//vars.add(E);
		store.imposeDecomposition(new Expectation(prTmp[noItems-2], excessWt, E));
		
		IntVar penalty = new IntVar(store, "Penalty", -1000000, 0);
		//vars.add(penalty);
		store.impose(new XmulCeqZ(E, -1*fine, penalty));
				
		IntVar goal = new IntVar(store, "goal", 0, 1000000);
		vars.add(goal);
		store.impose(new XplusYeqZ(profit, penalty, goal));
		
		IntVar goalNegation= new IntVar(store, "goalNegation", -1000000, 0);
		store.impose(new XplusYeqC(goal, goalNegation, 0));
		
		cost = goalNegation;
	}
	
	public static void main(String[] args){
		
		SSKP example = new SSKP();
		
		//example.model();
		example.modelRandom();
		
		if (example.searchOptimal()) {
			System.out.println("Solution(s) found");			
		}
        example.search.printAllSolutions();
		
	}

	/* It specifies simple search method based on most constrained static and lexigraphical 
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