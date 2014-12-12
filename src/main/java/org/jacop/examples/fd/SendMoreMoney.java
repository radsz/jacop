/**
 *  SendMoreMoney.java 
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

package org.jacop.examples.fd;

import java.util.ArrayList;

import org.jacop.constraints.Alldiff;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;

/**
 * 
 * It is a simple arithmetic logic puzzle, where SEND+MORE=MONEY.
 * 
 *  Find for the equation on the left
 *   what digits are represented by the letters
 *    different letters represent different digits

 *  SEND           9567
 * +MORE =======> +1085
 * MONEY          10652
 * 
 * @author Radoslaw Szymanek
 * @version 4.2
 *
 */
public class SendMoreMoney extends ExampleFD {

	/*
	 * This creates a standard model using simple basic constraints. 
	 */
	
	/**
	 * 1. Every CP program consists of two parts. The first one is a model and
	 * the second one is the specification of the search. 
	 * 
	 * The model consists of variables and constraints. 
	 */
	public void modelBasic() {
		
		vars = new ArrayList<IntVar>();
		
		/**
		 * A constraint store can be considered as a manager of constraints 
		 * and variables. It is always required to have a constraint store 
		 * in order to create a CP model of the problem. 
		 */
		store = new Store();

		// Creating an array for FDVs
		/**
		 * First, we need to specify the variables. In this problem we 
		 * will for certain have variables representing the value of different
		 * letters.
		 */
		IntVar letters[] = new IntVar[8];
		
		// Creating FDV (finite domain variables)
		// with indexes for accessing
		int iS = 0, iE = 1, iN = 2, iD = 3;
		int iM = 4, iO = 5, iR = 6, iY = 7;
		
		/**
		 * We create variables. Each variable is created in a given 
		 * constraint store. We provide information about variable name. 
		 * However, the most part part of the specification is about the initial
		 * domain. The initial domain is specified to be in between 0 and 9. 
		 * 
		 * One important feature of CP is that a variable must take a value from
		 * the initial domain. The actual value of the variable can not be outside
		 * the initial domain. In some sense, the initial domain is also like a
		 * constraint.
		 * 
		 *  A variable is an integer variable, so eventually it will have an integer
		 *  value.
		 *  
		 *  FDV - Finite Domain Variable.
		 */
		
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

		/**
		 * After specifying the variables we need to specify the 
		 * constraints. 
		 * 
		 * All the constraints which are specified have to be satisfied
		 * by the solution. 
		 * 
		 */
		
		// Imposing inequalities constraints between letters
		// This nested loop imposes inequality constraint
		// for all pairs of letters
		// Since there are 8 different letters this will create
		// 0+1+2+3+4+5+6+7 = 28 inequality constraints

		/**
		 * XneqyY is one of the available constraint in the solver. The problem
		 * has to be modeled using the available constraints. 
		 * 
		 * Sometimes, if a relation specified by a problem does not have a direct
		 * constraint available within a constraint solver, it must be replaced by
		 * a set of constraints.
		 * 
		 * Finding proper constraints which can in combination provide the constraint
		 * present in the problem is not always trivial. The bad match of the problem
		 * constraint to the constraints used within a solver can cause problems with 
		 * efficiency of reasoning and solving. In the worst case, the constraints may
		 * not cooperate well (lack of propagation in between constraints) and the
		 * search will take a long time.
		 * 
		 * What is a propagation? For example, if variable S becomes 9 then all other
		 * variables can not be equal to 9. As soon as variables S is equal to 9 the 
		 * constraints (XneqY) can propagate and remove value 9 from the domains of other
		 * constraints. 
		 * 
		 * One decision can lead to another decisions. Assigning value 9 to variable S 
		 * makes it possible for constraints to remove value 9 from remaining variables.
		 * 
		 * If the constraint is not satisfied then the current problem with all constraints
		 * does not have a solution. 
		 */
		for (int i = 0; i < letters.length; i++)
			for (int j = i - 1; j >= 0; j--)
				store.impose(new XneqY(letters[j], letters[i]));

	
		
		// Each letter is SEND number has a different value
		// which depends on the position of this letter
		// SEND = 1000 * S + 100 * E + N * 10 + D * 1
		IntVar numbersSEND[] = new IntVar[4];
		IntVar valueSEND = new IntVar(store, "SEND", 0, 9999);

		// Creates FDV for each position in SEND with
		// appropriate domain, they all start with zero
		// since a letter could be zero and the position
		// value is also zero
		numbersSEND[0] = new IntVar(store, "v(S)", 0, 9000);
		numbersSEND[1] = new IntVar(store, "v(E)", 0, 900);
		numbersSEND[2] = new IntVar(store, "v(N)", 0, 90);
		numbersSEND[3] = new IntVar(store, "v(D)", 0, 9);

		// Creates and imposes constraints which enforce
		// relationship between letter and value of its position
		// in the number SEND
		store.impose(new XmulCeqZ(letters[iS], 1000, numbersSEND[0]));
		store.impose(new XmulCeqZ(letters[iE], 100, numbersSEND[1]));
		store.impose(new XmulCeqZ(letters[iN], 10, numbersSEND[2]));
		store.impose(new XmulCeqZ(letters[iD], 1, numbersSEND[3]));

		// Succesively adds position to get value of the number SEND
		IntVar valueSEinSEND = new IntVar(store, "v(SEinSEND)", 0, 9900);
		IntVar valueNDinSEND = new IntVar(store, "v(NDinSEND)", 0, 99);

		store.impose(new XplusYeqZ(numbersSEND[0], numbersSEND[1],
				valueSEinSEND));
		store.impose(new XplusYeqZ(numbersSEND[2], numbersSEND[3],
				valueNDinSEND));
		store.impose(new XplusYeqZ(valueSEinSEND, valueNDinSEND, valueSEND));

		// Each letter in MORE number has a different value
		// which depends on the position of this letter
		// MORE = 1000 * M + 100 * O + R * 10 + E * 1
		IntVar numbersMORE[] = new IntVar[4];
		IntVar valueMORE = new IntVar(store, "MORE", 0, 9999);

		// Creates FDV for each position in MORE with
		// appropriate domain, they all start with zero
		// since a letter could be zero and the position
		// value is also zero
		numbersMORE[0] = new IntVar(store, "v(M)", 0, 9000);
		numbersMORE[1] = new IntVar(store, "v(O)", 0, 900);
		numbersMORE[2] = new IntVar(store, "v(R)", 0, 90);
		numbersMORE[3] = new IntVar(store, "v(E)", 0, 9);

		// Creates and imposes constraints which enforce
		// relationship between letter and value of its position
		// in the number MORE
		store.impose(new XmulCeqZ(letters[iM], 1000, numbersMORE[0]));
		store.impose(new XmulCeqZ(letters[iO], 100, numbersMORE[1]));
		store.impose(new XmulCeqZ(letters[iR], 10, numbersMORE[2]));
		store.impose(new XmulCeqZ(letters[iE], 1, numbersMORE[3]));

		// Successively adds position to get value of the number MORE
		IntVar valueMOinMORE = new IntVar(store, "v(MOinMORE)", 0, 9900);
		IntVar valueREinMORE = new IntVar(store, "v(REinMORE)", 0, 99);

		store.impose(new XplusYeqZ(numbersMORE[0], numbersMORE[1],
				valueMOinMORE));
		store.impose(new XplusYeqZ(numbersMORE[2], numbersMORE[3],
				valueREinMORE));
		store.impose(new XplusYeqZ(valueMOinMORE, valueREinMORE, valueMORE));

		// Each letter in MONEY number has a different value
		// which depends on the position of this letter
		// MONEY = 10000 * M + 1000 * O + N * 100 + E * 10 + Y * 1
		IntVar numbersMONEY[] = new IntVar[5];
		IntVar valueMONEY = new IntVar(store, "MONEY", 0, 99999);
		;

		// Creates FDV for each position in MONEY with
		// appropriate domain, they all start with zero
		// since a letter could be zero and the position
		// value is also zero
		numbersMONEY[0] = new IntVar(store, "v(M)", 0, 90000);
		numbersMONEY[1] = new IntVar(store, "v(O)", 0, 9000);
		numbersMONEY[2] = new IntVar(store, "v(N)", 0, 900);
		numbersMONEY[3] = new IntVar(store, "v(E)", 0, 90);
		numbersMONEY[4] = new IntVar(store, "v(Y)", 0, 9);

		store.impose(new XmulCeqZ(letters[iM], 10000, numbersMONEY[0]));
		store.impose(new XmulCeqZ(letters[iO], 1000, numbersMONEY[1]));
		store.impose(new XmulCeqZ(letters[iN], 100, numbersMONEY[2]));
		store.impose(new XmulCeqZ(letters[iE], 10, numbersMONEY[3]));
		store.impose(new XmulCeqZ(letters[iY], 1, numbersMONEY[4]));

		// Successively adds position to get value of the number MONEY
		IntVar valueMOinMONEY = new IntVar(store, "v(MOinMONEY)", 0, 99000);
		IntVar valueNEinMONEY = new IntVar(store, "v(NEinMONEY)", 0, 990);
		IntVar valueMONEinMONEY = new IntVar(store, "v(MONEinMONEY)", 0, 99990);

		store.impose(new XplusYeqZ(numbersMONEY[0], numbersMONEY[1],
				valueMOinMONEY));
		store.impose(new XplusYeqZ(numbersMONEY[2], numbersMONEY[3],
				valueNEinMONEY));
		store.impose(new XplusYeqZ(valueMOinMONEY, valueNEinMONEY,
				valueMONEinMONEY));
		store.impose(new XplusYeqZ(valueMONEinMONEY, numbersMONEY[4],
				valueMONEY));

		// Main equation of the problem SEND + MORE = MONEY
		store.impose(new XplusYeqZ(valueSEND, valueMORE, valueMONEY));

		// Since S is the first digit of SEND
		// and M is the first digit of MORE or MONEY
		// both letters can not be equal to zero
		store.impose(new XneqC(letters[iS], 0));
		store.impose(new XneqC(letters[iM], 0));
					
	}
	
	/**
	 * This creates a standard search, which looks for a single solution.
	 */
	
	@Override
	public boolean search() {
		
		/**
		 * The search procedure is required for majority of the problems. At some
		 * point the constraints are no longer able to prune the domains of the 
		 * variables. In this case, we have to speculatively take decisions about
		 * what values should be assigned to what variables.
		 * 
		 * Feel free to insert store.consistency() method and store.print() just 
		 * before executing any code in this function to see at what point the 
		 * constraints were not able to reason more.
		 */
		
		/*
			store.consistency();
			store.print();
		*/
		
		 /** In the context of the SEND+MORE=MONEY problem, the search could decide 
		   * to assign first value 2 to variable E, followed by another trial 
		   * by assinging value 3 to variable E. Again, failure after trying to assign 
		   * value 4 to variable E. Finally, after assigning value 5 to variable E the 
		   * constraint are not violated an the search continues with assigning other 
		   * variables. Eventually, after making E equal to value 5 all other variables
		   * get proper values.
		   * 
		   *  Assigning only one variable (E) to proper value 5 makes all other variables
		   *  assigned their proper value. This shows a power of constraints because 
		   *  one decision was enough to trigger cascade of decisions (one as logical 
		   *  consequence of the previous decisions) which made all variables fixed to 
		   *  their proper value. Constraint alldiff may have reduced some domains of
		   *  variables, which was followed by reduction caused by SumWeight constraint. 
		   *  Again, the change by SumWeight may have caused Alldiff constraint to 
		   *  figure out another reduction of the variables domain. The constraint can 
		   *  cause re-execution of the consistency function multiple times. 
		   *  
		   *  In general, if the variable within a constraint scope changes then a constraint
		   *  may be able to reduce the domain of other variables in the constraint scope.
		   *  It is like a domino effect. If a domino stops (no more pruning can be inferred
		   *  through constraints) a search has to make another speculative decision to continue
		   *  finding a solution.  
		   */
		
		/**
		 * Most of the search specification contains information what variables have to have 
		 * a value, what is the ordering of variables, and finally what is the order of values 
		 * tried. 
		 * 
		 * In the context of our example, we may have tried with different variable (e.g. not E,
		 * but N), or with different value (instead of trying value 2, 3, 4, and 5, we could start
		 * with value 5. 
		 *
		 * It is example of the simplest possible search, which most likely can work 
		 * only on the simple problems, toy examples.
		 */
		SelectChoicePoint<IntVar> select = new SimpleSelect<IntVar>(vars.toArray(new IntVar[1]),
													new SmallestDomain<IntVar>(),
													new IndomainMin<IntVar>());
		
		search = new DepthFirstSearch<IntVar>();

		boolean result = search.labeling(store, select);		
		
		return result;
		
	}
	
	/**
	 * It executes the program to solve this simple logic puzzle.
	 * @param args no arguments used.
	 */
	public static void main(String args[]) {

		SendMoreMoney exampleBasic = new SendMoreMoney();
		
		exampleBasic.modelBasic();

		if (exampleBasic.search())
			System.out.println("Solution found.");

		SendMoreMoney exampleGlobal = new SendMoreMoney();
		
		exampleGlobal.model();
		
		if (exampleGlobal.search())
			System.out.println("Solution found.");
		
	}
	
	/**
	 * 1. Every CP program consists of two parts. The first one is a model and
	 * the second one is the specification of the search. 
	 * This creates a model which uses global constraints to provide consize modeling. 
	 * The model consists of variables and constraints. 
	 */
	@Override
	public void model() {
		
		vars = new ArrayList<IntVar>();

		/**
		 * A constraint store can be considered as a manager of constraints 
		 * and variables. It is always required to have a constraint store 
		 * in order to create a CP model of the problem. 
		 */
		store = new Store();

		/**
		 * First, we need to specify the variables. In this problem we 
		 * will for certain have variables representing the value of different
		 * letters.
		 */

		/**
		 * We create variables. Each variable is created in a given 
		 * constraint store. We provide information about variable name. 
		 * However, the most part part of the specification is about the initial
		 * domain. The initial domain is specified to be in between 0 and 9. 
		 * 
		 * One important feature of CP is that a variable must take a value from
		 * the initial domain. The actual value of the variable can not be outside
		 * the initial domain. In some sense, the initial domain is also like a
		 * constraint.
		 * 
		 *  A variable is an integer variable, so eventually it will have an integer
		 *  value.
		 *  
		 *  FDV - Finite Domain Variable.
		 */

		IntVar s = new IntVar(store, "S", 0, 9);
		IntVar e = new IntVar(store, "E", 0, 9);
		IntVar n = new IntVar(store, "N", 0, 9);
		IntVar d = new IntVar(store, "D", 0, 9);
		IntVar m = new IntVar(store, "M", 0, 9);
		IntVar o = new IntVar(store, "O", 0, 9);
		IntVar r = new IntVar(store, "R", 0, 9);
		IntVar y = new IntVar(store, "Y", 0, 9);

		// Creating arrays for FDVs
		IntVar digits[] = { s, e, n, d, m, o, r, y };
		IntVar send[] = { s, e, n, d };
		IntVar more[] = { m, o, r, e };
		IntVar money[] = { m, o, n, e, y };

		for (IntVar v : digits)
			vars.add(v);
		
		/**
		 * After specifying the variables we need to specify the 
		 * constraints. 
		 * 
		 * All the constraints which are specified have to be satisfied
		 * by the solution. 
		 * 
		 * Constraints are added to the model through executing the impose function 
		 * of the constraint store.
		 *
		 * Instead of using 28 primitive constraints of the form XneqY
		 * we can use only one global constraint. 
		 * 
		 * A global constraint may have number of advantages when compared
		 * to primitive (basic) constraints : 
		 * 
		 * a). It give more concise model. A relatively minor improvement. 
		 * 
		 * b) the global constraint is aware of the relation not only between
		 * two variables, but actually between all pairs within a set of variables.
		 * A global has a potential of reducing an exponential size of the search tree
		 * to a constant small size search tree. 
		 * 
		 *  Example. If three variables had a domain 1..2, then primitive constraints
		 *  will not notice any problem, because any pair of variables can be assigned
		 *  to value 1 or 2 and the variables will be different. However, the global
		 *  constraint can notice that there are only two different values in the domains
		 *  but three variables, so the constraint is not possible to satisfy.
		 *  
		 *  A (primitive) constraint can not assign a value to a variable, unless it has
		 *  to be equal to that value. In our example above the primitive constraint can
		 *  not make the first variable equal to one.
		 */
		store.impose(new Alldiff(digits));

		/**
		 * We would like to express the relation that SEND + MORE = MONEY. We have value
		 * for particular letters but not for the whole words. Now, the task is to figure 
		 * out the value of the word given values of the letters.
		 * 
		 * This can be easily achieved using SumWeight constraint. A SumWeight constraint
		 * will take a list of variable and a list of weights and multiple each variable by
		 * a corresponding weight and make the result equal to the last (third parameter) of
		 * the constraint.
		 */
		
		int[] weights5 = { 10000, 1000, 100, 10, 1 };
		int[] weights4 = { 1000, 100, 10, 1 };

		/**
		 * We create auxilary variables in order to make it easier to express some of the
		 * constraints. Each auxilary variable holds a value for a given word.
		 */
		IntVar valueSEND = new IntVar(store, "v(SEND)", 0, 9999);
		IntVar valueMORE = new IntVar(store, "v(MORE)", 0, 9999);
		IntVar valueMONEY = new IntVar(store, "v(MONEY)", 0, 99999);

		/**
		 * Constraints for getting value for words
		 * SEND = 1000 * S + 100 * E + N * 10 + D * 1
		 * MORE = 1000 * M + 100 * O + R * 10 + E * 1
		 * MONEY = 10000 * M + 1000 * O + 100 * N + E * 10 + Y * 1
		 */
		store.impose(new SumWeight(send, weights4, valueSEND));
		store.impose(new SumWeight(more, weights4, valueMORE));
		store.impose(new SumWeight(money, weights5, valueMONEY));

		/**
		 * The auxilary variables allow us to express the main constraint
		 * of the problem in very simple manner. We just use XplusYeqZ constraint.
		 */
		store.impose(new XplusYeqZ(valueSEND, valueMORE, valueMONEY));

		/**
		 * Implied constraint after transformation of SEND+MORE=MONEY.
		 * 1000 * S + 91 * E + 10 * R + D -9000 * M - 900 * O -90 * N = Y.
		 * It removes 2 wrong decisions.
		 */
		
		int [] weightsImplied = {1000, 91, 10, 1, -9000, -900, -90}; 
		IntVar [] varsImplied = {s, e, r, d, m, o, n};
		store.impose(new SumWeight(varsImplied, weightsImplied, y));
		
		/**
		 * The two constraints below were not explicit in the problem description. However, 
		 * they are still valid constraints. The programmer task is to find and make the 
		 * constraint explicit in the constraint model.
		 *
		 * Since S is the first digit of SEND and M is the first digit of MORE or MONEY
		 * both letters can not be equal to zero
		 */
		store.impose(new XneqC(s, 0));
		store.impose(new XneqC(m, 0));		
		
		/**
		 * We have very concise model of the problem. It contains only 28 lines of code. 
		 * It is thanks to the constraints which incorporate reasoning mechanisms which 
		 * are used as soon as some decisions about variables domains are taken. 
		 * 
		 * In addition, the constraints can specify quite complex relationships between variables, 
		 * like an alldiff constraint. 
		 */
		
	}

}
