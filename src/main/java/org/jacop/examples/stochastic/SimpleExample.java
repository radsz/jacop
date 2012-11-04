package org.jacop.examples.stochastic;

import java.util.ArrayList;

import org.jacop.constraints.Sum;
import org.jacop.constraints.SumWeight;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.MostConstrainedStatic;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.stochastic.constraints.*;
import org.jacop.stochastic.constraints.SopCeqS;
import org.jacop.stochastic.core.Operator;
import org.jacop.stochastic.core.ProbabilityRange;
import org.jacop.stochastic.core.StochasticVar;

public class SimpleExample extends ExampleFD {

		private void modelPrOfElement() {
			
			store = new Store();
			vars = new ArrayList<IntVar>();
			
			int[] valS = {1, 2, 4};
			double[] minPS = {0.3, 0.2, 0.1};
			double[] maxPS = {0.7, 0.3, 0.5};
			IntVar[] PsS = new IntVar[valS.length];
			int res = 10;
			
			StochasticVar S = new StochasticVar(store, "S", valS, minPS, maxPS);
			for (int i=0; i < valS.length; i++)
				PsS[i] = new IntVar(store, "PEl" + valS[i], 0, res);
			
			store.impose(new PrOfElement(S, valS, PsS, res));
			
			for (IntVar V : PsS)
				vars.add(V);
			
			store.impose(new Sum(PsS, new IntVar(store, "Res", res,res)));
			
			IntVar E = new IntVar(store, "Expectation", 0, S.dom().values[S.getSize()-1]*res);
			vars.add(E);
			store.impose(new SumWeight(PsS, valS, E)); 
			 
			System.out.println(store);
		}
		
		private void modelSopC() {
			
			store = new Store();
			vars = new ArrayList<IntVar>();
			
			int[] valS = {3, 5};
			double[] minPS = {0.1, 0};
			double[] maxPS = {0.3, 0.1};
			IntVar[] PsS = new IntVar[valS.length];
			int res = 10;
			int C = 7;
			
			StochasticVar S = new StochasticVar(store, "S", valS, minPS, maxPS);
			for (int i=0; i < valS.length; i++)
				PsS[i] = new IntVar(store, "PEl" + valS[i], 0, res);
			
			store.impose(new PrOfElement(S, valS, PsS, res));
			
			for (IntVar V : PsS)
				vars.add(V);
			
			IntVar pr = new IntVar(store, "pr", 5, 8);
			store.impose(new SopC(S, C, pr, res, new Operator("<=")));

			vars.add(pr);			 
		}
		
		private void modelSopX() {

			store = new Store();
			vars = new ArrayList<IntVar>();
			
			int[] valS = {1, 2, 4};
			double[] minPS = {0.3, 0.2, 0.5};
			double[] maxPS = {0.3, 0.2, 0.5};
			IntVar[] PsS = new IntVar[valS.length];
			int res = 10;

			StochasticVar S = new StochasticVar(store, "S", valS, minPS, maxPS);
			for (int i=0; i < valS.length; i++)
				PsS[i] = new IntVar(store, "PEl" + valS[i], 0, res);
			
			store.impose(new PrOfElement(S, valS, PsS, res));
			
			for (IntVar V : PsS)
				vars.add(V);
			
			store.impose(new Sum(PsS, new IntVar(store, "Res", res,res)));
			
			IntVar X = new IntVar(store, "X", 0, 1);
			
			int[] valP = {0};
			ProbabilityRange[] ranP = {new ProbabilityRange(0,1)};
			IntVar[] PsP = new IntVar[valP.length];

			StochasticVar P = new StochasticVar(store, "P", valP, ranP);
			IntVar pr = new IntVar(store, "pr", 0, res);
			PsP[0] = pr;
			
			store.impose(new PrOfElement(P, valP, PsP, res));

			store.impose(new SopX(S, X, P, new Operator(">")));

			vars.add(X);
			vars.add(pr);			 
		}
		
		private void modelSopCeqS() {
			
			store = new Store();
			vars = new ArrayList<IntVar>();
			int res = 10;
			int C = 1;
			Operator op = new Operator("+");
			
			int[] valSlhs = {1, 2, 3};
			double[] minPSlhs = {0, 0, 0};
			double[] maxPSlhs = {0.1, 1, 1};
			IntVar[] PsSlhs = new IntVar[valSlhs.length];

			StochasticVar Slhs = new StochasticVar(store, "Slhs", valSlhs, minPSlhs, maxPSlhs);
			for (int i=0; i < valSlhs.length; i++)
				PsSlhs[i] = new IntVar(store, "PEl" + valSlhs[i], 0, res);
			
			store.impose(new PrOfElement(Slhs, valSlhs, PsSlhs, res));
			
			for (IntVar V : PsSlhs)
				vars.add(V);
			
			int[] valSrhs = {5, 6, 7};
			double[] minPSrhs = {0, 0, 0};
			double[] maxPSrhs = {0.7, 0.7, 0.1};
			IntVar[] PsSrhs = new IntVar[valSrhs.length];

			StochasticVar Srhs = new StochasticVar(store, "Srhs", valSrhs, minPSrhs, maxPSrhs);
			for (int i=0; i < valSrhs.length; i++)
				PsSrhs[i] = new IntVar(store, "PEl" + valSrhs[i], 0, res);
			
			store.impose(new PrOfElement(Srhs, valSrhs, PsSrhs, res));
			
			for (IntVar V : PsSrhs)
				vars.add(V);
			
			store.impose(new SopCeqS(Slhs, op, C, Srhs));
			
		}
		
		private void modelSopXeqS() {
			
			store = new Store();
			vars = new ArrayList<IntVar>();
			int res = 100;
			Operator op = new Operator("*");
			
			int[] valSlhs = {2, 5};
			double[] minPSlhs = {0.2, 0.8};
			double[] maxPSlhs = {0.2, 0.8};
			IntVar[] PsSlhs = new IntVar[valSlhs.length];

			StochasticVar Slhs = new StochasticVar(store, "Slhs", valSlhs, minPSlhs, maxPSlhs);
			for (int i=0; i < valSlhs.length; i++)
				PsSlhs[i] = new IntVar(store, "PEl" + valSlhs[i], 0, res);
			
			store.impose(new PrOfElement(Slhs, valSlhs, PsSlhs, res));
			
			for (IntVar V : PsSlhs)
				vars.add(V);
			
			store.impose(new Sum(PsSlhs, new IntVar(store, "Res", res,res)));

			
			int[] valSrhs = {0, 2, 5};
			double[] minPSrhs = {0, 0, 0};
			double[] maxPSrhs = {1, 1, 1};
			IntVar[] PsSrhs = new IntVar[valSrhs.length];

			StochasticVar Srhs = new StochasticVar(store, "Srhs", valSrhs, minPSrhs, maxPSrhs);
			for (int i=0; i < valSrhs.length; i++)
				PsSrhs[i] = new IntVar(store, "PEl" + valSrhs[i], 0, res);
			
			store.impose(new PrOfElement(Srhs, valSrhs, PsSrhs, res));
			
			for (IntVar V : PsSrhs)
				vars.add(V);
			
			store.impose(new Sum(PsSrhs, new IntVar(store, "Res", res,res)));

			IntVar X = new IntVar(store, "X", 0, 1);
			vars.add(X);
			
			store.impose(new SopXeqS(Slhs, op, X, Srhs));
		}
		
		private void modelSopSeqS() {
			
			store = new Store();
			vars = new ArrayList<IntVar>();
			int res = 100;
			Operator op = new Operator("+");
			
			int[] valSlhs1 = {1, 2};
			double[] minPSlhs1 = {0.4, 0.4};
			double[] maxPSlhs1 = {0.6, 0.6};
			IntVar[] PsSlhs1 = new IntVar[valSlhs1.length];

			StochasticVar Slhs1 = new StochasticVar(store, "Slhs1", valSlhs1, minPSlhs1, maxPSlhs1);
			for (int i=0; i < valSlhs1.length; i++)
				PsSlhs1[i] = new IntVar(store, "PEl" + valSlhs1[i], 0, res);
			
			store.impose(new PrOfElement(Slhs1, valSlhs1, PsSlhs1, res));
			
			for (IntVar V : PsSlhs1)
				vars.add(V);
			
			store.impose(new Sum(PsSlhs1, new IntVar(store, "Res", res,res)));
			
			int[] valSlhs2 = {2, 3};
			double[] minPSlhs2 = {0.4, 0.4};
			double[] maxPSlhs2 = {0.6, 0.6};
			IntVar[] PsSlhs2 = new IntVar[valSlhs2.length];

			StochasticVar Slhs2 = new StochasticVar(store, "Slhs2", valSlhs2, minPSlhs2, maxPSlhs2);
			for (int i=0; i < valSlhs2.length; i++)
				PsSlhs2[i] = new IntVar(store, "PEl" + valSlhs2[i], 0, res);
			
			store.impose(new PrOfElement(Slhs2, valSlhs2, PsSlhs2, res));
			
			for (IntVar V : PsSlhs2)
				vars.add(V);
			
			store.impose(new Sum(PsSlhs2, new IntVar(store, "Res", res,res)));

			
			int[] valSrhs = {3, 4, 5};
			double[] minPSrhs = {0, 0, 0};
			double[] maxPSrhs = {1, 1, 1};
			IntVar[] PsSrhs = new IntVar[valSrhs.length];

			StochasticVar Srhs = new StochasticVar(store, "Srhs", valSrhs, minPSrhs, maxPSrhs);
			for (int i=0; i < valSrhs.length; i++)
				PsSrhs[i] = new IntVar(store, "PEl" + valSrhs[i], 0, res);
			
			store.impose(new PrOfElement(Srhs, valSrhs, PsSrhs, res));
			
			for (IntVar V : PsSrhs)
				vars.add(V);
			
			store.impose(new Sum(PsSrhs, new IntVar(store, "Res", res,res)));

			store.impose(new SopSeqS(Slhs1, op, Slhs2, Srhs));
		}
		
		private void modelElement() {
			
			store = new Store();
			vars = new ArrayList<IntVar>();
			int res = 10;
			
			int[] valS0 = {1, 2};
			double[] minPS0 = {0.5, 0.5};
			double[] maxPS0 = {0.5, 0.5};
			IntVar[] PsS0 = new IntVar[valS0.length];

			StochasticVar S0 = new StochasticVar(store, "S0", valS0, minPS0, maxPS0);
			for (int i=0; i < valS0.length; i++)
				PsS0[i] = new IntVar(store, "PEl" + valS0[i], 0, res);
			
			store.impose(new PrOfElement(S0, valS0, PsS0, res));
			
			for (IntVar V : PsS0)
				vars.add(V);
			
			store.impose(new Sum(PsS0, new IntVar(store, "Res", res,res)));
			
			int[] valS1 = {2, 3};
			double[] minPS1 = {0.4, 0.6};
			double[] maxPS1 = {0.4, 0.6};
			IntVar[] PsS1 = new IntVar[valS1.length];

			StochasticVar S1 = new StochasticVar(store, "S1", valS1, minPS1, maxPS1);
			for (int i=0; i < valS1.length; i++)
				PsS1[i] = new IntVar(store, "PEl" + valS1[i], 0, res);
			
			store.impose(new PrOfElement(S1, valS1, PsS1, res));
			
			for (IntVar V : PsS1)
				vars.add(V);
			
			store.impose(new Sum(PsS1, new IntVar(store, "Res", res,res)));

			StochasticVar[] list = {S0, S1};
			
			StochasticVar S = new StochasticVar(store, "S", list);
			int[] valS = S.dom().values;
			IntVar[] PsS = new IntVar[valS.length];

			for (int i=0; i < valS.length; i++)
				PsS[i] = new IntVar(store, "PEl" + valS[i], 0, res);
			
			store.impose(new PrOfElement(S, valS, PsS, res));
			
			for (IntVar V : PsS)
				vars.add(V);
			
			store.impose(new Sum(PsS, new IntVar(store, "Res", res,res)));
			
			IntVar index = new IntVar(store, "index", 0, 1);
			vars.add(index);

			store.impose(new Element(index, list, S));
		}
		
		@Override
		public void model() {

		}
			
		public static void main(String args[]) {

			SimpleExample example = new SimpleExample();
			
			example.modelPrOfElement();
			example.modelSopC();
			example.modelSopX();
			example.modelSopCeqS();
			example.modelSopXeqS();
			example.modelSopSeqS();
			example.modelElement();

			if (example.searchAllAtOnce()) {
				System.out.println("Solution(s) found");			
			}		
			example.search.printAllSolutions();
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
