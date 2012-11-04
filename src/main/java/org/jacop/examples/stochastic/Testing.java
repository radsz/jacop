package org.jacop.examples.stochastic;

import java.util.ArrayList;

import org.jacop.constraints.Sum;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.stochastic.constraints.PrOfElement;
import org.jacop.stochastic.constraints.SopC;
import org.jacop.stochastic.constraints.SopSeqS;
import org.jacop.stochastic.constraints.SopX;
import org.jacop.stochastic.constraints.SopXeqS;
import org.jacop.stochastic.core.Operator;
import org.jacop.stochastic.core.StochasticVar;

public class Testing extends ExampleFD {

	/*
	 * This model tests the PrOfElement Constraint.
	 */
	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		int res = 100;
		int seed = 1989;

		StochasticVar S = new StochasticVar(store, "S", seed, false, 3, 0, 10);
		System.out.println(S);
		IntVar[] PsS = new IntVar[S.getSize()];

		for (int i=0; i < S.getSize(); i++)
			PsS[i] = new IntVar(store, "PEl" + S.dom().values[i], 0, res);

		for (IntVar V : PsS)
			vars.add(V);

		store.impose(new PrOfElement(S, S.dom().values, PsS, res));
		store.impose(new Sum(PsS, new IntVar(store, "Res", res,res)));
	}

	/*
	 * Scenario 1.
	 */
	public void modelTest1(int seed, boolean SopX) {

		store = new Store();
		vars = new ArrayList<IntVar>();
		int res = 10;

		StochasticVar S = new StochasticVar(store, "S", seed, false, 3, 0, 10);
		System.out.println(S);
		IntVar[] PsS = new IntVar[S.getSize()];

		for (int i=0; i < S.getSize(); i++)
			PsS[i] = new IntVar(store, "PEl" + S.dom().values[i], 0, res);

		for (IntVar V : PsS)
			vars.add(V);

		store.impose(new PrOfElement(S, S.dom().values, PsS, res));
		store.impose(new Sum(PsS, new IntVar(store, "Res", res,res)));

		if (SopX) {

			StochasticVar PX = new StochasticVar(store, "PX");
			IntVar pX = new IntVar(store, "pX", 0 , res);
			store.impose(new PrOfElement(PX, pX, res));
			vars.add(pX);

			IntVar X = new IntVar(store, "X", 5, 5);

			store.impose(new SopX(S, X, PX, new Operator("<")));
		}

		else {

			IntVar PC = new IntVar(store, "PC", 0, res);
			vars.add(PC);

			store.impose(new SopC(S, 5, PC, res, new Operator("<")));
		}

	}

	/*
	 * Scenario 2.
	 */
	public void modelTest2(int seed, boolean plus) {

		store = new Store();
		vars = new ArrayList<IntVar>();
		int res = 10;

		StochasticVar S1 = new StochasticVar(store, "S1", seed, false, 3, 0, 10);
		System.out.println(S1);
		IntVar[] PsS1 = new IntVar[S1.getSize()];

		for (int i=0; i < S1.getSize(); i++)
			PsS1[i] = new IntVar(store, "PEl" + S1.dom().values[i], 0, res);

		for (IntVar V : PsS1)
			vars.add(V);

		store.impose(new PrOfElement(S1, S1.dom().values, PsS1, res));
		store.impose(new Sum(PsS1, new IntVar(store, "Res", res,res)));

		IntVar X = new IntVar(store, "X", 2, 3);

		StochasticVar S2 = new StochasticVar(store, "S2", S1, X, new Operator("+"));
		System.out.println(S2);
		IntVar[] PsS2 = new IntVar[S2.getSize()];

		for (int i=0; i < S2.getSize(); i++)
			PsS2[i] = new IntVar(store, "PEl" + S2.dom().values[i], 0, res);

		for (IntVar V : PsS2)
			vars.add(V);

		store.impose(new PrOfElement(S2, S2.dom().values, PsS2, res));
		store.impose(new Sum(PsS2, new IntVar(store, "Res", res,res)));

		if (plus)
			store.impose(new SopXeqS(S1, new Operator("+"), X, S2));
		else
			store.impose(new SopXeqS(S2, new Operator("-"), X, S1));
	}

	/*
	 * Scenario 3.
	 */
	public void modelTest3(int seed, boolean l2r) {

		store = new Store();
		vars = new ArrayList<IntVar>();
		int res = 10;

		// S1
		StochasticVar S1 = new StochasticVar(store, "S1", seed, false, 2, 0, 10);
		//System.out.println(S1);
		IntVar[] PsS1 = new IntVar[S1.getSize()];

		for (int i=0; i < S1.getSize(); i++)
			PsS1[i] = new IntVar(store, "PElS1" + S1.dom().values[i], 0, res);

		store.impose(new PrOfElement(S1, S1.dom().values, PsS1, res));
		store.impose(new Sum(PsS1, new IntVar(store, "Res", res,res)));

		// S2
		StochasticVar S2 = new StochasticVar(store, "S2", seed/3, false, 2, 0, 10);
		//System.out.println(S2);
		IntVar[] PsS2 = new IntVar[S2.getSize()];

		for (int i=0; i < S2.getSize(); i++)
			PsS2[i] = new IntVar(store, "PElS2" + S2.dom().values[i], 0, res);

		store.impose(new PrOfElement(S2, S2.dom().values, PsS2, res));
		store.impose(new Sum(PsS2, new IntVar(store, "Res", res,res)));

		// S3
		StochasticVar S3 = new StochasticVar(store, "S3", seed/5, false, 2, 0, 10);
		//System.out.println(S3);
		IntVar[] PsS3 = new IntVar[S3.getSize()];

		for (int i=0; i < S3.getSize(); i++)
			PsS3[i] = new IntVar(store, "PElS3" + S3.dom().values[i], 0, res);

		store.impose(new PrOfElement(S3, S3.dom().values, PsS3, res));
		store.impose(new Sum(PsS3, new IntVar(store, "Res", res,res)));

		// S4
		StochasticVar S4 = new StochasticVar(store, "S4", seed/7, false, 2, 0, 10);
		//System.out.println(S4);
		IntVar[] PsS4 = new IntVar[S4.getSize()];

		for (int i=0; i < S4.getSize(); i++)
			PsS4[i] = new IntVar(store, "PElS4" + S4.dom().values[i], 0, res);

		store.impose(new PrOfElement(S4, S4.dom().values, PsS4, res));
		store.impose(new Sum(PsS4, new IntVar(store, "Res", res,res)));

		if (l2r) {

			// Stmp1
			StochasticVar Stmp1 = new StochasticVar(store, S1, S2, new Operator("+"));
			//System.out.println(Stmp1);
			IntVar[] Pstmp1 = new IntVar[Stmp1.getSize()];

			for (int i=0; i < Stmp1.getSize(); i++)
				Pstmp1[i] = new IntVar(store, "PElStmp1" + Stmp1.dom().values[i], 0, res);

			store.impose(new PrOfElement(Stmp1, Stmp1.dom().values, Pstmp1, res));
			store.impose(new Sum(Pstmp1, new IntVar(store, "Res", res,res)));
			store.impose(new SopSeqS(S1, new Operator("+"), S2, Stmp1));

			// Stmp2
			StochasticVar Stmp2 = new StochasticVar(store, Stmp1, S3, new Operator("+"));
			//System.out.println(Stmp2);
			IntVar[] Pstmp2 = new IntVar[Stmp2.getSize()];

			for (int i=0; i < Stmp2.getSize(); i++)
				Pstmp2[i] = new IntVar(store, "PElStmp2" + Stmp2.dom().values[i], 0, res);

			store.impose(new PrOfElement(Stmp2, Stmp2.dom().values, Pstmp2, res));
			store.impose(new Sum(Pstmp2, new IntVar(store, "Res", res,res)));
			store.impose(new SopSeqS(Stmp1, new Operator("+"), S3, Stmp2));

			// Stmp3
			StochasticVar Stmp3 = new StochasticVar(store, Stmp2, S4, new Operator("+"));
			//System.out.println(Stmp3);
			IntVar[] Pstmp3 = new IntVar[Stmp3.getSize()];

			for (int i=0; i < Stmp3.getSize(); i++)
				Pstmp3[i] = new IntVar(store, "PElStmp3" + Stmp3.dom().values[i], 0, res);

			for (IntVar V : Pstmp3)
				vars.add(V);

			store.impose(new PrOfElement(Stmp3, Stmp3.dom().values, Pstmp3, res));
			store.impose(new Sum(Pstmp3, new IntVar(store, "Res", res,res)));
			store.impose(new SopSeqS(Stmp2, new Operator("+"), S4, Stmp3));

		}

		else {

			// Stmp1
			StochasticVar Stmp1 = new StochasticVar(store, S4, S3, new Operator("+"));
			//System.out.println(Stmp1);
			IntVar[] Pstmp1 = new IntVar[Stmp1.getSize()];

			for (int i=0; i < Stmp1.getSize(); i++)
				Pstmp1[i] = new IntVar(store, "PElStmp1" + Stmp1.dom().values[i], 0, res);

			store.impose(new PrOfElement(Stmp1, Stmp1.dom().values, Pstmp1, res));
			store.impose(new Sum(Pstmp1, new IntVar(store, "Res", res,res)));
			store.impose(new SopSeqS(S4, new Operator("+"), S3, Stmp1));

			// Stmp2
			StochasticVar Stmp2 = new StochasticVar(store, Stmp1, S2, new Operator("+"));
			//System.out.println(Stmp2);
			IntVar[] Pstmp2 = new IntVar[Stmp2.getSize()];

			for (int i=0; i < Stmp2.getSize(); i++)
				Pstmp2[i] = new IntVar(store, "PElStmp2" + Stmp2.dom().values[i], 0, res);

			store.impose(new PrOfElement(Stmp2, Stmp2.dom().values, Pstmp2, res));
			store.impose(new Sum(Pstmp2, new IntVar(store, "Res", res,res)));
			store.impose(new SopSeqS(Stmp1, new Operator("+"), S2, Stmp2));

			// Stmp3
			StochasticVar Stmp3 = new StochasticVar(store, Stmp2, S1, new Operator("+"));
			//System.out.println(Stmp3);
			IntVar[] Pstmp3 = new IntVar[Stmp3.getSize()];

			for (int i=0; i < Stmp3.getSize(); i++)
				Pstmp3[i] = new IntVar(store, "PElStmp3" + Stmp3.dom().values[i], 0, res);

			for (IntVar V : Pstmp3)
				vars.add(V);

			store.impose(new PrOfElement(Stmp3, Stmp3.dom().values, Pstmp3, res));
			store.impose(new Sum(Pstmp3, new IntVar(store, "Res", res,res)));
			store.impose(new SopSeqS(Stmp2, new Operator("+"), S1, Stmp3));

		}
	}

	void test1() {

		int seed = 12353155;

		for (int i = 0; i < 100; i++) {

			System.out.println("Modeling using S < C");

			Testing testSopC = new Testing();
			testSopC.modelTest1(seed+i, false);

			if (testSopC.searchAllAtOnce()) 
				System.out.println("Solution(s) found");	

			int noOfSol1 = testSopC.search.getSolutionListener().solutionsNo();

			System.out.println("Modeling using S < X");
			Testing testSopX = new Testing();
			testSopX.modelTest1(seed+i, true);

			if (testSopX.searchAllAtOnce()) 
				System.out.println("Solution(s) found");

			int noOfSol2 = testSopX.search.getSolutionListener().solutionsNo();

			if (noOfSol1 != noOfSol2)
				System.err.println("For seed no " + (seed+i) + " the number of solutions does not match in test1");
			else 
				System.out.println("Test no. " + (seed+i) + " succesfull");

		}

	}

	void test2() {

		int seed = 91150437;

		for (int i = 0; i < 100; i++) {

		System.out.println("Modeling using S1 + X = S2");
		Testing testSopXeqSPlus = new Testing();
		testSopXeqSPlus.modelTest2(seed+i, true);

		if (testSopXeqSPlus.searchAllAtOnce()) 
			System.out.println("Solution(s) found");	

		int noOfSol1 = testSopXeqSPlus.search.getSolutionListener().solutionsNo();

		System.out.println("Modeling using S2 - X = S1");
		Testing testSopXeqSMinus = new Testing();
		testSopXeqSMinus.modelTest2(seed+i, false);

		if (testSopXeqSMinus.searchAllAtOnce()) 
			System.out.println("Solution(s) found");	

		int noOfSol2 = testSopXeqSMinus.search.getSolutionListener().solutionsNo();

		if (noOfSol1 != noOfSol2)
			System.err.println("For seed no " + (seed+i) + " the number of solutions does not match in test1");
		else 
			System.out.println("Test no. " + (seed+i) + " succesfull");

		}
		
	}

	void test3() {

		int seed = 14071989;

		for (int i = 0; i < 100; i++) {

		System.out.println("Modeling using S1 + S2 + S3 + S4");
		Testing l2r = new Testing();
		l2r.modelTest3(seed+i, true);

		if (l2r.searchAllAtOnce()) 
			System.out.println("Solution(s) found");

		int noOfSol1 = l2r.search.getSolutionListener().solutionsNo();

		System.out.println("Modeling using S4 + S3 + S2 + S1");
		Testing r2l = new Testing();
		r2l.modelTest3(seed+i, false);

		if (r2l.searchAllAtOnce()) 
			System.out.println("Solution(s) found");

		int noOfSol2 = r2l.search.getSolutionListener().solutionsNo();

		if (noOfSol1 != noOfSol2)
			System.err.println("For seed no " + (seed+i) + " the number of solutions does not match in test1");
		else 
			System.out.println("Test no. " + (seed+i) + " succesfull");
		
		}
		
	}

	public static void main(String args[]) {

		int scenario = 2;
		Testing test = new Testing();

		switch (scenario){

		/*
		 * Testing SopX and SopC by setting X ~ C. Same number of soltions
		 * are obtained in both cases.
		 */
		case 1:
			test.test1();
			break;

			/*
			 * Testing S1 + X = S2 and S2 - X = S1. Same number of solutions are
			 * obtained in both cases. 	
			 */
		case 2:
			test.test2();
			break;

			/*
			 * Testing S1 + S2 + S3 +S4 = S and S4 + S3 + S2 + S1 = S. Same number of 
			 * solutions are obtained in both cases.	
			 */
		case 3:
			test.test3();
			break;
		}	
	}
}
