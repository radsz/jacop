package org.jacop.examples.cpviz;


// The import below is required since some utilities are used
import java.util.ArrayList;

import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.Sum;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.IntVar;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;

import org.jacop.search.TraceGenerator;
import org.jacop.search.ConsistencyListener;
import org.jacop.search.ExitChildListener;
import org.jacop.search.ExitListener;

public class CPvizSendMoreMoney {

    Store store = new Store();
    ArrayList<IntVar> vars;
    Search<IntVar> search;

	// Find for the equation on the left
	// what digits are represented by the letters
	// different letters represent different digits

	// SEND 9567
	// +MORE =======> +1085
	// MONEY 10652
	
	/*
	 * This creates a standard model using simple basic constraints. 
	 */
	
	public void model() {
		
		vars = new ArrayList<IntVar>();
		store = new Store();

		// Creating an array for IntVars
		IntVar letters[] = new IntVar[8];
		
		// Creating IntVar (finite domain variables)
		// with indexes for accessing
		int iS = 0, iE = 1, iN = 2, iD = 3;
		int iM = 4, iO = 5, iR = 6, iY = 7;
		letters[iS] = new IntVar(store, "S", 0, 9);
		letters[iE] = new IntVar(store, "E", 0, 9);
		letters[iN] = new IntVar(store, "N", 0, 9);
		letters[iD] = new IntVar(store, "D", 0, 9);
		letters[iM] = new IntVar(store, "M", 0, 9);
		letters[iO] = new IntVar(store, "O", 0, 9);
		letters[iR] = new IntVar(store, "R", 0, 9);
		letters[iY] = new IntVar(store, "Y", 0, 9);

		for (IntVar x : letters)
			vars.add(x);
		
		// Imposing inequalities constraints between letters
		// This nested loop imposes inequality constraint
		// for all pairs of letters
		// Since there are 8 different letters this will create
		// 0+1+2+3+4+5+6+7 = 28 inequality constraints

		for (int i = 0; i < letters.length; i++)
			for (int j = i - 1; j >= 0; j--)
				store.impose(new XneqY(letters[j], letters[i]));


// 		// Main equation of the problem SEND + MORE = MONEY
// 		store.impose(new XplusYeqZ(valueSEND, valueMORE, valueMONEY));

		// Since S is the first digit of SEND
		// and M is the first digit of MORE or MONEY
		// both letters can not be equal to zero
		store.impose(new XneqC(letters[iS], 0));
		store.impose(new XneqC(letters[iM], 0));
					

		// 1000*S + 91*E - 90*N + D - 9000*M - 900*O + 10*R = Y
		IntVar s1 = new IntVar(store, 0, 9000);
		store.impose(new XmulCeqZ(letters[iS], 1000, s1));
		IntVar s2 = new IntVar(store, 0, 1000);
		store.impose(new XmulCeqZ(letters[iE], 91, s2));
		IntVar s3 = new IntVar(store, -1000, 0);
		store.impose(new XmulCeqZ(letters[iN], -90, s3));
		IntVar s4 = new IntVar(store, -100000, 0);
		store.impose(new XmulCeqZ(letters[iM], -9000, s4));
		IntVar s5 = new IntVar(store, -100000, 0);
		store.impose(new XmulCeqZ(letters[iO], -900, s5));
		IntVar s6 = new IntVar(store, 0, 100);
		store.impose(new XmulCeqZ(letters[iR], 10, s6));

		IntVar t1 = new IntVar(store, -100000, 100000);
		store.impose(new XplusYeqZ(s1, s2, t1));
		IntVar t2 = new IntVar(store, -100000, 100000);
		store.impose(new XplusYeqZ(t1, s3, t2));
		IntVar t3 = new IntVar(store, -100000, 100000);
		store.impose(new XplusYeqZ(t2, s4, t3));
		IntVar t4 = new IntVar(store, -100000, 100000);
		store.impose(new XplusYeqZ(t3, s5, t4));
		IntVar t5 = new IntVar(store, -100000, 100000);
		store.impose(new XplusYeqZ(t4, s6, t5));
		store.impose(new XplusYeqZ(t5, letters[iD], letters[iY]));

  		store.consistency();
//   		System.out.println(vars);
// 	}
	
// 	/**
// 	 * This creates a standard search, which looks for a single solution.
// 	 */
	
// 	public boolean search() {
		
		SelectChoicePoint<IntVar> varSelect = new SimpleSelect<IntVar>(vars.toArray(new IntVar[1]), null,
				new IndomainMin<IntVar>());
		
		search = new DepthFirstSearch<IntVar>();

		// Trace --->
	
 		TraceGenerator<IntVar> select = new TraceGenerator<IntVar>(search, varSelect);

// 		TraceGenerator<IntVar> select = new TraceGenerator<IntVar>(varSelect, true);
		select.addTracedVar( letters[iE] );

 // 		search.setConsistencyListener((ConsistencyListener)select);
 // 		search.setExitChildListener((ExitChildListener<IntVar>)select);
//		search.setExitListener((ExitListener)select);
		// <---

		boolean result = search.labeling(store, select);		
		
// 		return result;
		
	}
	
	public static void main(String args[]) {

// 		SendMoreMoney exampleBasic = new SendMoreMoney();
		
// 		exampleBasic.model();

// 		if (exampleBasic.search())
// 			System.out.println("Solution found");

		CPvizSendMoreMoney exampleGlobal = new CPvizSendMoreMoney();
		
		exampleGlobal.modelGlobal();
		
// 		if (exampleGlobal.search())
// 			System.out.println();
		
	}
	
	/*
	 * This creates a model which uses global constraints to provide consize modeling.
	 */
	
	public void modelGlobal() {
		
		vars = new ArrayList<IntVar>();
		store = new Store();

		// Creating IntVar (finite domain variables)
		IntVar s = new IntVar(store, "S", 0, 9);
		IntVar e = new IntVar(store, "E", 0, 9);
		IntVar n = new IntVar(store, "N", 0, 9);
		IntVar d = new IntVar(store, "D", 0, 9);
		IntVar m = new IntVar(store, "M", 0, 9);
		IntVar o = new IntVar(store, "O", 0, 9);
		IntVar r = new IntVar(store, "R", 0, 9);
		IntVar y = new IntVar(store, "Y", 0, 9);

		// Creating arrays for IntVars
		IntVar digits[] = { s, e, n, d, m, o, r, y };
		IntVar send[] = { s, e, n, d };
		IntVar more[] = { m, o, r, e };
		IntVar money[] = { m, o, n, e, y };

		for (IntVar v : digits)
			vars.add(v);
		
		// Imposing inequalities constraints between letters
		// Only one global constraint
		store.impose(new Alldifferent(digits));

		int[] weights5 = { 10000, 1000, 100, 10, 1 };
		int[] weights4 = { 1000, 100, 10, 1 };

		IntVar valueSEND = new IntVar(store, "v(SEND)", 0, 9999);
		IntVar valueMORE = new IntVar(store, "v(MORE)", 0, 9999);
		IntVar valueMONEY = new IntVar(store, "v(MONEY)", 0, 99999);

		// Constraints for getting value for words
		// SEND = 1000 * S + 100 * E + N * 10 + D * 1
		// MORE = 1000 * M + 100 * O + R * 10 + E * 1
		// MONEY = 10000 * M + 1000 * O + 100 * N + E * 10 + Y * 1
 		store.impose(new SumWeight(send, weights4, valueSEND));
 		store.impose(new SumWeight(more, weights4, valueMORE));
 		store.impose(new SumWeight(money, weights5, valueMONEY));

		// Main equation of the problem SEND + MORE = MONEY
     		store.impose(new XplusYeqZ(valueSEND, valueMORE, valueMONEY));

// 		// 1000*S + 91*E - 90*N + D - 9000*M - 900*O + 10*R = Y
// 		int[] w = {1000, 91, -90, 1, -9000, -900, 10};
// 		IntVar[] vs = {s, e, n, d, m, o, r};
// 		store.impose(new SumWeight(vs, w, y));

		// Since S is the first digit of SEND
		// and M is the first digit of MORE or MONEY
		// both letters can not be equal to zero
		store.impose(new XneqC(s, 0));
		store.impose(new XneqC(m, 0));		
		
     		store.consistency();

		SelectChoicePoint<IntVar> varSelect = new SimpleSelect<IntVar>(vars.toArray(new IntVar[1]), null,
				new IndomainMin<IntVar>());
		
		search = new DepthFirstSearch<IntVar>();

		// Trace --->
 		TraceGenerator<IntVar> select = new TraceGenerator<IntVar>(search, varSelect, new IntVar[] {s, e, n, d, m, o, r, y});

// 		TraceGenerator<IntVar> select = new TraceGenerator<IntVar>(varSelect, true, new IntVar[] {s, e, n, d, m, o, r, y});

 // 		search.setConsistencyListener((ConsistencyListener)select);
 //  		search.setExitChildListener((ExitChildListener<IntVar>)select);
//		search.setExitListener((ExitListener)select);
		// <---

		boolean result = search.labeling(store, select);		
		
// 		return result;
		
	}
}
