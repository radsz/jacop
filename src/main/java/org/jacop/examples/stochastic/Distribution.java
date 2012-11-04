package org.jacop.examples.stochastic;

import java.util.ArrayList;

import org.jacop.constraints.Distance;
import org.jacop.constraints.IfThenElse;
import org.jacop.constraints.Sum;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.MostConstrainedStatic;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.stochastic.constraints.PrOfElement;
import org.jacop.stochastic.constraints.SopX;
import org.jacop.stochastic.core.Operator;
import org.jacop.stochastic.core.StochasticVar;

/**
 * Implements a stochastic distribution problem between a set of Suppliers and 
 * a set of Customers using 5 different models. 
 * 
 * The first 4 models deal with the situation where the supply of each supplier
 * is stochastic in nature with increasing complexity as described in the paper:
 * 
 * S. Tarim, Brahim Hnich, Steven Prestwich, and Roberto Rossi. Finding reliable
 * solutions: event-driven probabilistic constraint programming. Annals of 
 * Operations Research, 171(1):77{99{99, October 2009.
 * 
 * The 5th model which is an extension of model 1, deals with the situation 
 * where both the supply of the suppliers and the demand of the customers are 
 * stochastic in nature. 
 */
public class Distribution extends ExampleFD {

	public void model_I() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		int numSuppliers = 3;
		int numCustomers = 3;
		StochasticVar[] S = new StochasticVar[numSuppliers];
		int res = 10;
		
		int[] valS1 = {3, 7, 12};
		double[] minPS1 = {0.3, 0.5, 0.2};
		double[] maxPS1 = {0.3, 0.5, 0.2};
		S[0] = new StochasticVar(store, "S0", valS1, minPS1, maxPS1);
		
		int[] valS2 = {6, 7, 10};
		double[] minPS2 = {0.4, 0.2, 0.4};
		double[] maxPS2 = {0.4, 0.2, 0.4};
		S[1] = new StochasticVar(store, "S1", valS2, minPS2, maxPS2);
		
		
		int[] valS3 = {3, 8};
		double[] minPS3 = {0.3, 0.7};
		double[] maxPS3 = {0.3, 0.7};		
		S[2] = new StochasticVar(store, "S2", valS3, minPS3, maxPS3);
		
		IntVar[] C = new IntVar[numCustomers];
		C[0] = new IntVar(store, "C0", 8, 8);
		C[1] = new IntVar(store, "C1", 7, 7);
		C[2] = new IntVar(store, "C2", 4, 4);
		
		IntVar[][] x = new IntVar[numSuppliers][numCustomers];
		
		for (int i = 0; i < numSuppliers; i++)
			for (int j = 0; j < numCustomers; j++){
				
				if ((i==0 & j == 2) || (i==2 && j==0))
					x[i][j] = new IntVar(store, "x"+i+"_"+j, 0, 0);
				else
					x[i][j] = new IntVar(store, "x"+i+"_"+j, 0, 15);
				
				vars.add(x[i][j]);
			}
		
		IntVar[][] scopeS = {{x[0][0], x[0][1]},
							{x[1][0], x[1][1], x[1][2]},
							{x[2][1], x[2][2]}};
		
		IntVar[][] scopeC = {{x[0][0], x[1][0]},
							{x[0][1], x[1][1], x[2][1]},
							{x[1][2], x[2][2]}};
			

		for (int i = 0; i < numCustomers; i++)
			store.impose(new Sum(scopeC[i], C[i]));
		
		IntVar[] Sout = new IntVar[numSuppliers];
		IntVar[] Spr = new IntVar[numSuppliers];
		StochasticVar[] SP = new StochasticVar[numSuppliers];
		
		for (int i = 0; i < numSuppliers; i++){
			
			Sout[i] = new IntVar(store, "Sout"+i, 0, 15);
			Spr[i] = new IntVar(store, "Spr"+i, 0, res);
			SP[i] = new StochasticVar(store, "SP"+i);
			
			IntVar[] tmp = {Spr[i]};
			
			store.impose(new PrOfElement(SP[i], SP[i].dom().values, tmp, res));
			store.impose(new Sum(scopeS[i], Sout[i]));
			store.impose(new SopX(S[i], Sout[i], SP[i], new Operator(">=")));
			
		}
		
		IntVar goal = new IntVar(store, "goal", 0, 10000);
		IntVar[] tmp = {Spr[0], Spr[1], Spr[2]};
		store.impose(new Sum(tmp, goal));
		vars.add(goal);
		
		IntVar goalNegation= new IntVar(store, "goalNegation", -1000000, 0);
		store.impose(new XplusYeqC(goal, goalNegation, 0));
		
		cost = goalNegation;
		
	}

	public void model_II() {
		
		store = new Store();
		vars = new ArrayList<IntVar>();
		int numSuppliers = 3;
		int numCustomers = 3;
		StochasticVar[] S = new StochasticVar[numSuppliers];
		int res = 10;
		
		int[] valS1 = {3, 7, 12};
		double[] minPS1 = {0.3, 0.5, 0.2};
		double[] maxPS1 = {0.3, 0.5, 0.2};
		S[0] = new StochasticVar(store, "S0", valS1, minPS1, maxPS1);
		
		int[] valS2 = {6, 7, 10};
		double[] minPS2 = {0.4, 0.2, 0.4};
		double[] maxPS2 = {0.4, 0.2, 0.4};
		S[1] = new StochasticVar(store, "S1", valS2, minPS2, maxPS2);
		
		
		int[] valS3 = {3, 8};
		double[] minPS3 = {0.3, 0.7};
		double[] maxPS3 = {0.3, 0.7};		
		S[2] = new StochasticVar(store, "S2", valS3, minPS3, maxPS3);
		
		IntVar[] C = new IntVar[numCustomers];
		C[0] = new IntVar(store, "C0", 8, 8);
		C[1] = new IntVar(store, "C1", 7, 7);
		C[2] = new IntVar(store, "C2", 4, 4);
		
		IntVar[][] x = new IntVar[numSuppliers][numCustomers];
		
		for (int i = 0; i < numSuppliers; i++)
			for (int j = 0; j < numCustomers; j++){
				
				if ((i==0 & j == 2) || (i==2 && j==0))
					x[i][j] = new IntVar(store, "x"+i+"_"+j, 0, 0);
				else
					x[i][j] = new IntVar(store, "x"+i+"_"+j, 0, 15);
				
				vars.add(x[i][j]);
			}
		
		IntVar[][] scopeS = {{x[0][0], x[0][1]},
							{x[1][0], x[1][1], x[1][2]},
							{x[2][1], x[2][2]}};
		
		IntVar[][] scopeC = {{x[0][0], x[1][0]},
							{x[0][1], x[1][1], x[2][1]},
							{x[1][2], x[2][2]}};
			

		for (int i = 0; i < numCustomers; i++)
			store.impose(new Sum(scopeC[i], C[i]));
		
		IntVar[] Sout = new IntVar[numSuppliers];
		IntVar[] Spr = new IntVar[numSuppliers];
		StochasticVar[] SP = new StochasticVar[numSuppliers];
		
		for (int i = 0; i < numSuppliers; i++){
			
			Sout[i] = new IntVar(store, "Sout"+i, 0, 15);
			Spr[i] = new IntVar(store, "Spr"+i, 0, res);
			SP[i] = new StochasticVar(store, "SP"+i);
			
			IntVar[] tmp = {Spr[i]};
			
			store.impose(new PrOfElement(SP[i], SP[i].dom().values, tmp, res));
			store.impose(new Sum(scopeS[i], Sout[i]));
			store.impose(new SopX(S[i], Sout[i], SP[i], new Operator(">=")));
		}
		
		IntVar[] Cpr = new IntVar[numCustomers];
		for (int i = 0; i < numCustomers; i++)
			Cpr[i] = new IntVar(store, "Cpr"+i, 0, 10000);
		
		IntVar tmp0 = new IntVar(store, "tmp1", 0, 10000);
		IntVar tmp1 = new IntVar(store, "tmp2", 0, 10000);
		IntVar tmp2 = new IntVar(store, "tmp2", 0, 10000);
		
		store.impose(new XmulYeqZ(Spr[0], Spr[1], tmp0));
		store.impose(new XmulYeqZ(Spr[0], Spr[1], tmp1));
		store.impose(new XmulYeqZ(Spr[1], Spr[2], tmp2));
		
		store.impose(new XmulCeqZ(tmp0, res, Cpr[0]));
		store.impose(new XmulYeqZ(tmp1, Spr[2], Cpr[1]));
		store.impose(new XmulCeqZ(tmp2, res, Cpr[2]));

		IntVar goal = new IntVar(store, "goal", 0, 1000000);
		IntVar[] tmp = {Cpr[0], Cpr[1], Cpr[2]};
		store.impose(new Sum(tmp, goal));
		vars.add(goal);
		
		IntVar goalNegation= new IntVar(store, "goalNegation", -1000000, 0);
		store.impose(new XplusYeqC(goal, goalNegation, 0));
		
		cost = goalNegation;
	}

	public void model_III() {
		
		store = new Store();
		vars = new ArrayList<IntVar>();
		int numSuppliers = 3;
		int numCustomers = 3;
		StochasticVar[] S = new StochasticVar[numSuppliers];
		int res = 10;
		
		int[] valS1 = {3, 7, 12};
		double[] minPS1 = {0.3, 0.5, 0.2};
		double[] maxPS1 = {0.3, 0.5, 0.2};
		S[0] = new StochasticVar(store, "S0", valS1, minPS1, maxPS1);
		
		int[] valS2 = {6, 7, 10};
		double[] minPS2 = {0.4, 0.2, 0.4};
		double[] maxPS2 = {0.4, 0.2, 0.4};
		S[1] = new StochasticVar(store, "S1", valS2, minPS2, maxPS2);
		
		
		int[] valS3 = {3, 8};
		double[] minPS3 = {0.3, 0.7};
		double[] maxPS3 = {0.3, 0.7};		
		S[2] = new StochasticVar(store, "S2", valS3, minPS3, maxPS3);
		
		IntVar[] C = new IntVar[numCustomers];
		C[0] = new IntVar(store, "C0", 8, 8);
		C[1] = new IntVar(store, "C1", 7, 7);
		C[2] = new IntVar(store, "C2", 4, 4);
		
		IntVar[][] x = new IntVar[numSuppliers][numCustomers];
		
		for (int i = 0; i < numSuppliers; i++)
			for (int j = 0; j < numCustomers; j++){
				
				if ((i==0 & j == 2) || (i==2 && j==0))
					x[i][j] = new IntVar(store, "x"+i+"_"+j, 0, 0);
				else
					x[i][j] = new IntVar(store, "x"+i+"_"+j, 0, 15);
				
				vars.add(x[i][j]);
			}
		
		IntVar[][] scopeS = {{x[0][0], x[0][1]},
							{x[1][0], x[1][1], x[1][2]},
							{x[2][1], x[2][2]}};
		
		IntVar[][] scopeC = {{x[0][0], x[1][0]},
							{x[0][1], x[1][1], x[2][1]},
							{x[1][2], x[2][2]}};
			

		for (int i = 0; i < numCustomers; i++)
			store.impose(new Sum(scopeC[i], C[i]));
		
		IntVar[] Sout = new IntVar[numSuppliers];
		IntVar[] Spr = new IntVar[numSuppliers];
		StochasticVar[] SP = new StochasticVar[numSuppliers];
		
		for (int i = 0; i < numSuppliers; i++){
			
			Sout[i] = new IntVar(store, "Sout"+i, 0, 15);
			Spr[i] = new IntVar(store, "Spr"+i, 0, res);
			SP[i] = new StochasticVar(store, "SP"+i);
			
			IntVar[] tmp = {Spr[i]};
			
			store.impose(new PrOfElement(SP[i], SP[i].dom().values, tmp, res));
			store.impose(new Sum(scopeS[i], Sout[i]));
			store.impose(new SopX(S[i], Sout[i], SP[i], new Operator(">=")));
		}
		
		IntVar[] Cpr = new IntVar[numCustomers];
		for (int i = 0; i < numCustomers; i++)
			Cpr[i] = new IntVar(store, "Cpr"+i, 0, 10000);
		
		IntVar tmp0 = new IntVar(store, "tmp0", 0, 10000);
		IntVar tmp1 = new IntVar(store, "tmp1", 0, 10000);
		IntVar tmp2 = new IntVar(store, "tmp2", 0, 10000);
		
		IntVar t00 = new IntVar(store, "t00", 0, res);
		IntVar t10 = new IntVar(store, "t01", 0, res);
		IntVar t01 = new IntVar(store, "t10", 0, res);
		IntVar t11 = new IntVar(store, "t11", 0, res);
		IntVar t21 = new IntVar(store, "t12", 0, res);
		IntVar t12 = new IntVar(store, "t21", 0, res);
		IntVar t22 = new IntVar(store, "t22", 0, res);
		
		store.impose(new IfThenElse( new XeqC(x[0][0],0), new XeqC(t00, res), new XeqY(t00, Spr[0])));
		store.impose(new IfThenElse( new XeqC(x[1][0],0), new XeqC(t10, res), new XeqY(t10, Spr[1])));
		
		store.impose(new IfThenElse( new XeqC(x[0][1],0), new XeqC(t01, res), new XeqY(t01, Spr[0])));
		store.impose(new IfThenElse( new XeqC(x[1][1],0), new XeqC(t11, res), new XeqY(t11, Spr[1])));
		store.impose(new IfThenElse( new XeqC(x[2][1],0), new XeqC(t21, res), new XeqY(t21, Spr[2])));
		
		store.impose(new IfThenElse( new XeqC(x[1][2],0), new XeqC(t12, res), new XeqY(t12, Spr[1])));
		store.impose(new IfThenElse( new XeqC(x[2][2],0), new XeqC(t22, res), new XeqY(t22, Spr[2])));

		store.impose(new XmulYeqZ(t00, t10, tmp0));
		store.impose(new XmulYeqZ(t01, t11, tmp1));
		store.impose(new XmulYeqZ(t12, t22, tmp2));
		
		store.impose(new XmulCeqZ(tmp0, res, Cpr[0]));
		store.impose(new XmulYeqZ(tmp1, t21, Cpr[1]));
		store.impose(new XmulCeqZ(tmp2, res, Cpr[2]));

		IntVar goal = new IntVar(store, "goal", 0, 1000000);
		IntVar[] tmp = {Cpr[0], Cpr[1], Cpr[2]};
		store.impose(new Sum(tmp, goal));
		vars.add(goal);
		
		IntVar goalNegation= new IntVar(store, "goalNegation", -1000000, 0);
		store.impose(new XplusYeqC(goal, goalNegation, 0));
		
		cost = goalNegation;
	}
	
	/*
	 * Alternative implementation of model IV.
	 */
	public void model_IV_b() {
		
		store = new Store();
		vars = new ArrayList<IntVar>();
		int numSuppliers = 3;
		int numCustomers = 3;
		StochasticVar[] S = new StochasticVar[numSuppliers];
		int res = 10;
		
		int[] valS1 = {3, 7, 12};
		double[] minPS1 = {0.3, 0.5, 0.2};
		double[] maxPS1 = {0.3, 0.5, 0.2};
		S[0] = new StochasticVar(store, "S0", valS1, minPS1, maxPS1);
		
		int[] valS2 = {6, 7, 10};
		double[] minPS2 = {0.4, 0.2, 0.4};
		double[] maxPS2 = {0.4, 0.2, 0.4};
		S[1] = new StochasticVar(store, "S1", valS2, minPS2, maxPS2);
		
		
		int[] valS3 = {3, 8};
		double[] minPS3 = {0.3, 0.7};
		double[] maxPS3 = {0.3, 0.7};		
		S[2] = new StochasticVar(store, "S2", valS3, minPS3, maxPS3);
		
		StochasticVar[] C = new StochasticVar[numCustomers];
		int[] valC1 = {8};
		double[] minPC1 = {1};
		double[] maxPC1 = {1};
		C[0] = new StochasticVar(store, "C0", valC1, minPC1, maxPC1);
		
		int[] valC2 = {7};
		double[] minPC2 = {1};
		double[] maxPC2 = {1};
		C[1] = new StochasticVar(store, "C1", valC2, minPC2, maxPC2);
		
		
		int[] valC3 = {4};
		double[] minPC3 = {1};
		double[] maxPC3 = {1};
		C[2] = new StochasticVar(store, "C2", valC3, minPC3, maxPC3);
		
		IntVar[][] x = new IntVar[numSuppliers][numCustomers];
		
		for (int i = 0; i < numSuppliers; i++)
			for (int j = 0; j < numCustomers; j++){
				
				if ((i==0 & j == 2) || (i==2 && j==0))
					x[i][j] = new IntVar(store, "x"+i+"_"+j, 0, 0);
				else
					x[i][j] = new IntVar(store, "x"+i+"_"+j, 0, 15);
				
				vars.add(x[i][j]);
			}
		
		IntVar[][] scopeS = {{x[0][0], x[0][1]},
							{x[1][0], x[1][1], x[1][2]},
							{x[2][1], x[2][2]}};
		
		IntVar[][] scopeC = {{x[0][0], x[1][0]},
							{x[0][1], x[1][1], x[2][1]},
							{x[1][2], x[2][2]}};
			

		IntVar[] Cout = new IntVar[numCustomers];
		IntVar[] Cpr = new IntVar[numCustomers];
		StochasticVar[] CP = new StochasticVar[numCustomers];
		
		for (int i = 0; i < numCustomers; i++){
			
			Cout[i] = new IntVar(store, "Cout"+i, 0, 15);
			vars.add(Cout[i]);
			Cpr[i] = new IntVar(store, "Cpr"+i, 0, res);
			vars.add(Cpr[i]);
			CP[i] = new StochasticVar(store, "CP"+i);
			
			IntVar[] tmp = {Cpr[i]};
			
			store.impose(new PrOfElement(CP[i], CP[i].dom().values, tmp, res));
			store.impose(new Sum(scopeC[i], Cout[i]));
			store.impose(new SopX(C[i], Cout[i], CP[i], new Operator("==")));
			
		}
		
		IntVar[] Sout = new IntVar[numSuppliers];
		IntVar[] Spr = new IntVar[numSuppliers];
		StochasticVar[] SP = new StochasticVar[numSuppliers];
		
		for (int i = 0; i < numSuppliers; i++){
			
			Sout[i] = new IntVar(store, "Sout"+i, 0, 15);
			Spr[i] = new IntVar(store, "Spr"+i, 0, res);
			SP[i] = new StochasticVar(store, "SP"+i);
			
			IntVar[] tmp = {Spr[i]};
			
			store.impose(new PrOfElement(SP[i], SP[i].dom().values, tmp, res));
			store.impose(new Sum(scopeS[i], Sout[i]));
			store.impose(new SopX(S[i], Sout[i], SP[i], new Operator(">=")));
		}
		
		IntVar[] prC = new IntVar[numCustomers];
		IntVar[] prCfinal = new IntVar[numCustomers];
		for (int i = 0; i < numCustomers; i++){
			prC[i] = new IntVar(store, "prC"+i, 0, 10000);
			prCfinal[i] = new IntVar(store, "prCfinal"+i, 0, 100000);
		}
		
		IntVar tmp0 = new IntVar(store, "tmp0", 0, 10000);
		IntVar tmp1 = new IntVar(store, "tmp1", 0, 10000);
		IntVar tmp2 = new IntVar(store, "tmp2", 0, 10000);
		
		IntVar t00 = new IntVar(store, "t00", 0, res);
		IntVar t10 = new IntVar(store, "t01", 0, res);
		IntVar t01 = new IntVar(store, "t10", 0, res);
		IntVar t11 = new IntVar(store, "t11", 0, res);
		IntVar t21 = new IntVar(store, "t12", 0, res);
		IntVar t12 = new IntVar(store, "t21", 0, res);
		IntVar t22 = new IntVar(store, "t22", 0, res);
		
		store.impose(new IfThenElse( new XeqC(x[0][0],0), new XeqC(t00, res), new XeqY(t00, Spr[0])));
		store.impose(new IfThenElse( new XeqC(x[1][0],0), new XeqC(t10, res), new XeqY(t10, Spr[1])));
		
		store.impose(new IfThenElse( new XeqC(x[0][1],0), new XeqC(t01, res), new XeqY(t01, Spr[0])));
		store.impose(new IfThenElse( new XeqC(x[1][1],0), new XeqC(t11, res), new XeqY(t11, Spr[1])));
		store.impose(new IfThenElse( new XeqC(x[2][1],0), new XeqC(t21, res), new XeqY(t21, Spr[2])));
		
		store.impose(new IfThenElse( new XeqC(x[1][2],0), new XeqC(t12, res), new XeqY(t12, Spr[1])));
		store.impose(new IfThenElse( new XeqC(x[2][2],0), new XeqC(t22, res), new XeqY(t22, Spr[2])));

		store.impose(new XmulYeqZ(t00, t10, tmp0));
		store.impose(new XmulYeqZ(t01, t11, tmp1));
		store.impose(new XmulYeqZ(t12, t22, tmp2));
		
		store.impose(new XmulCeqZ(tmp0, res, prC[0]));
		store.impose(new XmulYeqZ(tmp1, t21, prC[1]));
		store.impose(new XmulCeqZ(tmp2, res, prC[2]));
		
		store.impose(new XmulYeqZ(prC[0], Cpr[0], prCfinal[0]));
		store.impose(new XmulYeqZ(prC[1], Cpr[1], prCfinal[1]));
		store.impose(new XmulYeqZ(prC[2], Cpr[2], prCfinal[2]));

		IntVar goal = new IntVar(store, "goal", 0, 1000000);
		IntVar[] tmp = {prCfinal[0], prCfinal[1], prCfinal[2]};
		store.impose(new Sum(tmp, goal));
		vars.add(goal);
		
		IntVar goalNegation= new IntVar(store, "goalNegation", -1000000, 0);
		store.impose(new XplusYeqC(goal, goalNegation, 0));
		
		cost = goalNegation;
	}
	
	public void model_IV_a() {
		
		store = new Store();
		vars = new ArrayList<IntVar>();
		int numSuppliers = 3;
		int numCustomers = 3;
		StochasticVar[] S = new StochasticVar[numSuppliers];
		int res = 10;
		
		int[] valS1 = {3, 7, 12};
		double[] minPS1 = {0.3, 0.5, 0.2};
		double[] maxPS1 = {0.3, 0.5, 0.2};
		S[0] = new StochasticVar(store, "S0", valS1, minPS1, maxPS1);
		
		int[] valS2 = {6, 7, 10};
		double[] minPS2 = {0.4, 0.2, 0.4};
		double[] maxPS2 = {0.4, 0.2, 0.4};
		S[1] = new StochasticVar(store, "S1", valS2, minPS2, maxPS2);
		
		
		int[] valS3 = {3, 8};
		double[] minPS3 = {0.3, 0.7};
		double[] maxPS3 = {0.3, 0.7};		
		S[2] = new StochasticVar(store, "S2", valS3, minPS3, maxPS3);
		
		IntVar[] C = new IntVar[numCustomers];
		C[0] = new IntVar(store, "C0", 8, 8);
		C[1] = new IntVar(store, "C1", 7, 7);
		C[2] = new IntVar(store, "C2", 4, 4);
		
		IntVar[][] x = new IntVar[numSuppliers][numCustomers];
		
		for (int i = 0; i < numSuppliers; i++)
			for (int j = 0; j < numCustomers; j++){
				
				if ((i==0 & j == 2) || (i==2 && j==0))
					x[i][j] = new IntVar(store, "x"+i+"_"+j, 0, 0);
				else
					x[i][j] = new IntVar(store, "x"+i+"_"+j, 0, 15);
				
				vars.add(x[i][j]);
			}
		
		IntVar[][] scopeS = {{x[0][0], x[0][1]},
							{x[1][0], x[1][1], x[1][2]},
							{x[2][1], x[2][2]}};
		
		IntVar[][] scopeC = {{x[0][0], x[1][0]},
							{x[0][1], x[1][1], x[2][1]},
							{x[1][2], x[2][2]}};
			
		IntVar[] actualC = new IntVar[numCustomers];
		IntVar[] Cpr = new IntVar[numCustomers];
		IntVar zero = new IntVar(store, "zero", 0, 0);
		
		for (int i = 0; i < numCustomers; i++){
			actualC[i] = new IntVar(store, "actualC"+i, 0, 50);
			Cpr[i] = new IntVar(store, "Cpr"+i, 0, res);
			store.impose(new Sum(scopeC[i], actualC[i]));
			store.impose(new IfThenElse( new Distance(C[i],actualC[i],zero), new XeqC(Cpr[i], res), new XeqY(Cpr[i], zero)));
		}
		
		IntVar[] Sout = new IntVar[numSuppliers];
		IntVar[] Spr = new IntVar[numSuppliers];
		StochasticVar[] SP = new StochasticVar[numSuppliers];
		
		for (int i = 0; i < numSuppliers; i++){
			
			Sout[i] = new IntVar(store, "Sout"+i, 0, 15);
			Spr[i] = new IntVar(store, "Spr"+i, 0, res);
			SP[i] = new StochasticVar(store, "SP"+i);
			
			IntVar[] tmp = {Spr[i]};
			
			store.impose(new PrOfElement(SP[i], SP[i].dom().values, tmp, res));
			store.impose(new Sum(scopeS[i], Sout[i]));
			store.impose(new SopX(S[i], Sout[i], SP[i], new Operator(">=")));
		}
		
		IntVar[] prC = new IntVar[numCustomers];
		IntVar[] prCfinal = new IntVar[numCustomers];
		for (int i = 0; i < numCustomers; i++){
			prC[i] = new IntVar(store, "prC"+i, 0, 10000);
			prCfinal[i] = new IntVar(store, "prCfinal"+i, 0, 100000);
		}
		
		IntVar tmp0 = new IntVar(store, "tmp0", 0, 10000);
		IntVar tmp1 = new IntVar(store, "tmp1", 0, 10000);
		IntVar tmp2 = new IntVar(store, "tmp2", 0, 10000);
		
		IntVar t00 = new IntVar(store, "t00", 0, res);
		IntVar t10 = new IntVar(store, "t01", 0, res);
		IntVar t01 = new IntVar(store, "t10", 0, res);
		IntVar t11 = new IntVar(store, "t11", 0, res);
		IntVar t21 = new IntVar(store, "t12", 0, res);
		IntVar t12 = new IntVar(store, "t21", 0, res);
		IntVar t22 = new IntVar(store, "t22", 0, res);
		
		store.impose(new IfThenElse( new XeqC(x[0][0],0), new XeqC(t00, res), new XeqY(t00, Spr[0])));
		store.impose(new IfThenElse( new XeqC(x[1][0],0), new XeqC(t10, res), new XeqY(t10, Spr[1])));
		
		store.impose(new IfThenElse( new XeqC(x[0][1],0), new XeqC(t01, res), new XeqY(t01, Spr[0])));
		store.impose(new IfThenElse( new XeqC(x[1][1],0), new XeqC(t11, res), new XeqY(t11, Spr[1])));
		store.impose(new IfThenElse( new XeqC(x[2][1],0), new XeqC(t21, res), new XeqY(t21, Spr[2])));
		
		store.impose(new IfThenElse( new XeqC(x[1][2],0), new XeqC(t12, res), new XeqY(t12, Spr[1])));
		store.impose(new IfThenElse( new XeqC(x[2][2],0), new XeqC(t22, res), new XeqY(t22, Spr[2])));

		store.impose(new XmulYeqZ(t00, t10, tmp0));
		store.impose(new XmulYeqZ(t01, t11, tmp1));
		store.impose(new XmulYeqZ(t12, t22, tmp2));
		
		store.impose(new XmulCeqZ(tmp0, res, prC[0]));
		store.impose(new XmulYeqZ(tmp1, t21, prC[1]));
		store.impose(new XmulCeqZ(tmp2, res, prC[2]));
		
		store.impose(new XmulYeqZ(prC[0], Cpr[0], prCfinal[0]));
		store.impose(new XmulYeqZ(prC[1], Cpr[1], prCfinal[1]));
		store.impose(new XmulYeqZ(prC[2], Cpr[2], prCfinal[2]));

		IntVar goal = new IntVar(store, "goal", 0, 1000000);
		IntVar[] tmp = {prCfinal[0], prCfinal[1], prCfinal[2]};
		store.impose(new Sum(tmp, goal));
		vars.add(goal);
		
		IntVar goalNegation= new IntVar(store, "goalNegation", -1000000, 0);
		store.impose(new XplusYeqC(goal, goalNegation, 0));
		
		cost = goalNegation;
	}

	public void model_V() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		int numSuppliers = 3;
		int numCustomers = 3;
		StochasticVar[] S = new StochasticVar[numSuppliers];
		int res = 10;
		
		int[] valS1 = {3, 7, 12};
		double[] minPS1 = {0.3, 0.5, 0.2};
		double[] maxPS1 = {0.3, 0.5, 0.2};
		S[0] = new StochasticVar(store, "S0", valS1, minPS1, maxPS1);
		
		int[] valS2 = {6, 7, 10};
		double[] minPS2 = {0.4, 0.2, 0.4};
		double[] maxPS2 = {0.4, 0.2, 0.4};
		S[1] = new StochasticVar(store, "S1", valS2, minPS2, maxPS2);
		
		
		int[] valS3 = {3, 8};
		double[] minPS3 = {0.3, 0.7};
		double[] maxPS3 = {0.3, 0.7};		
		S[2] = new StochasticVar(store, "S2", valS3, minPS3, maxPS3);
		
		StochasticVar[] C = new StochasticVar[numCustomers];
		int[] valC1 = {7, 8, 9};
		double[] minPC1 = {0.3, 0.5, 0.2};
		double[] maxPC1 = {0.3, 0.5, 0.2};
		C[0] = new StochasticVar(store, "C0", valC1, minPC1, maxPC1);
		
		int[] valC2 = {6, 7, 8};
		double[] minPC2 = {0.2, 0.6, 0.2};
		double[] maxPC2 = {0.2, 0.6, 0.2};
		C[1] = new StochasticVar(store, "C1", valC2, minPC2, maxPC2);
		
		
		int[] valC3 = {4, 5};
		double[] minPC3 = {0.7, 0.3};
		double[] maxPC3 = {0.7, 0.3};		
		C[2] = new StochasticVar(store, "C2", valC3, minPC3, maxPC3);
		
		IntVar[][] x = new IntVar[numSuppliers][numCustomers];
		
		for (int i = 0; i < numSuppliers; i++)
			for (int j = 0; j < numCustomers; j++){
				
				if ((i==0 & j == 2) || (i==2 && j==0))
					x[i][j] = new IntVar(store, "x"+i+"_"+j, 0, 0);
				else
					x[i][j] = new IntVar(store, "x"+i+"_"+j, 0, 15);
				
				vars.add(x[i][j]);
			}
		
		IntVar[][] scopeS = {{x[0][0], x[0][1]},
							{x[1][0], x[1][1], x[1][2]},
							{x[2][1], x[2][2]}};
		
		IntVar[][] scopeC = {{x[0][0], x[1][0]},
							{x[0][1], x[1][1], x[2][1]},
							{x[1][2], x[2][2]}};
			

		IntVar[] Cout = new IntVar[numCustomers];
		IntVar[] Cpr = new IntVar[numCustomers];
		StochasticVar[] CP = new StochasticVar[numCustomers];
		
		for (int i = 0; i < numCustomers; i++){
			
			Cout[i] = new IntVar(store, "Cout"+i, 0, 15);
			vars.add(Cout[i]);
			Cpr[i] = new IntVar(store, "Cpr"+i, 0, res);
			vars.add(Cpr[i]);
			CP[i] = new StochasticVar(store, "CP"+i);
			
			IntVar[] tmp = {Cpr[i]};
			
			store.impose(new PrOfElement(CP[i], CP[i].dom().values, tmp, res));
			store.impose(new Sum(scopeC[i], Cout[i]));
			store.impose(new SopX(C[i], Cout[i], CP[i], new Operator("<")));
			
		}
		
		IntVar[] Sout = new IntVar[numSuppliers];
		IntVar[] Spr = new IntVar[numSuppliers];
		StochasticVar[] SP = new StochasticVar[numSuppliers];
		
		for (int i = 0; i < numSuppliers; i++){
			
			Sout[i] = new IntVar(store, "Sout"+i, 0, 15);
			vars.add(Sout[i]);
			Spr[i] = new IntVar(store, "Spr"+i, 0, res);
			vars.add(Spr[i]);
			SP[i] = new StochasticVar(store, "SP"+i);
			
			IntVar[] tmp = {Spr[i]};
			
			store.impose(new PrOfElement(SP[i], SP[i].dom().values, tmp, res));
			store.impose(new Sum(scopeS[i], Sout[i]));
			store.impose(new SopX(S[i], Sout[i], SP[i], new Operator(">=")));
			
		}
		
		IntVar goal = new IntVar(store, "goal", 0, 10000);
		IntVar[] tmp = {Spr[0], Spr[1], Spr[2], Cpr[0], Cpr[1], Cpr[2]};
		store.impose(new Sum(tmp, goal));
		vars.add(goal);
		
		IntVar goalNegation= new IntVar(store, "goalNegation", -1000000, 0);
		store.impose(new XplusYeqC(goal, goalNegation, 0));
		
		cost = goalNegation;
		
	}
	
	public static void main(String[] args){
		
		Distribution example = new Distribution();
		int model = 1;
		
		switch(model){
		
		case 1:
			example.model_I();
			break;
			
		case 2:
			example.model_II();
			break;
			
		case 3:
			example.model_III();
			break;
			
		case 4:
			//example.model_IV_a();
			example.model_IV_b();
			break;
			
		case 5:
			example.model_V();
			break;
			
		}
		
		/*if (example.searchAllAtOnce()) {
			System.out.println("Solution(s) found");			
		}
		example.search.printAllSolutions();*/
		
		if (example.searchAllOptimal()) {
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
	
	/**
	 * It searches for all solutions with the optimal value.
	 * @return true if any optimal solution has been found.
	 */
	public boolean searchAllOptimal() {
		
		long T1, T2, T;
		T1 = System.currentTimeMillis();

		SelectChoicePoint<IntVar> select = new SimpleSelect<IntVar>(vars.toArray(new IntVar[1]), null,
													new IndomainMin<IntVar>());

		search = new DepthFirstSearch<IntVar>();
		search.getSolutionListener().searchAll(true);
		search.getSolutionListener().recordSolutions(true);

		boolean result = search.labeling(store, select, cost);

		T2 = System.currentTimeMillis();
		T = T2 - T1;
		System.out.println("\n\t*** Execution time = " + T + " ms");

		return result;
		
	}
	@Override
	public void model() {
		
	}

}
