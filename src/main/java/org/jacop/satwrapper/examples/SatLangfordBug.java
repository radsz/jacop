/**
 *  Langford.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *  Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.satwrapper.examples;

import java.util.ArrayList;

import org.jacop.constraints.*;
import org.jacop.core.BoundDomain;
import org.jacop.core.Domain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.jasat.modules.StatModule;
import org.jacop.satwrapper.SatWrapper;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;

/**
 * 
 * It solves Langford problem. 
 * 
 * @author Radoslaw Szymanek
 * @version 3.0
 * 
 * 
x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 
1 4 8 9 5 6 2 3 7 12 14 11 13 10 
1 4 9 6 8 5 2 3 7 13 11 14 12 10 
1 5 10 6 7 2 4 3 8 14 11 13 9 12 
1 6 10 7 2 4 5 3 9 14 12 8 11 13 
1 8 9 2 4 5 6 3 11 13 7 10 12 14 
1 9 6 2 8 4 5 3 12 10 7 14 11 13 
1 10 4 7 5 2 6 3 13 8 12 11 9 14 
1 10 5 6 2 7 4 3 13 9 11 8 14 12 
1 10 5 7 2 4 6 3 13 9 12 8 11 14 
1 10 7 4 2 5 6 3 13 11 9 8 12 14 
2 6 10 8 1 5 3 4 9 14 13 7 12 11 
2 7 9 1 8 5 3 4 10 13 6 14 12 11 
2 9 7 1 8 3 5 4 12 11 6 14 10 13 
2 10 3 6 8 5 1 4 13 7 11 14 12 9 
2 11 6 3 7 5 1 4 14 10 8 13 12 9 
2 11 6 7 3 1 5 4 14 10 12 9 8 13 
3 8 10 1 7 2 4 5 11 14 6 13 9 12 
 * x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
 *  3 10  2  7  8  4 1  5  13 6  12  14  11  9 - missing solution. #18
 * 1. level: 15, Variable: x3 = 7<--7
3 10 7 1 8 2 4 5 13 11 6 14 9 12 
 * 3 11 6 8 1 2 4 5 14 10 13 7 9 12 - missing solution.
3 11 8 2 4 6 1 5 14 12 7 10 13 9 
3 11 8 4 1 6 2 5 14 12 9 7 13 10 
4 10 1 7 8 2 3 6 13 5 12 14 9 11 
 * 4 11 9 3 1 5 2 6 14 13 8 7 12 10 - missing solution.
5 1 10 8 6 2 3 7 4 14 13 12 9 11 
5 11 9 1 2 3 4 7 14 13 6 8 10 12 
8 1 2 9 7 5 3 10 4 6 14 13 12 11 
8 11 1 2 3 6 4 10 14 5 7 9 13 12 
9 1 2 7 8 3 5 11 4 6 12 14 10 13 
 * 9 2 10 3 1 6 4 11 5 14 8 7 13 12 - missing solution.
10 1 3 6 8 2 5 12 4 7 11 14 9 13 
10 1 3 8 5 2 6 12 4 7 13 11 9 14 
10 1 5 2 8 6 3 12 4 9 7 14 13 11 
10 2 4 9 1 6 3 12 5 8 14 7 13 11 
10 2 9 3 1 4 6 12 5 13 8 7 11 14 
10 4 1 9 2 6 3 12 7 5 14 8 13 11 
11 1 5 3 6 7 2 13 4 9 8 12 14 10 
11 1 5 7 2 3 6 13 4 9 12 8 10 14 
 * 11 2 8 4 1 3 6 13 5 12 9 7 10 14 - missing solution.
11 3 4 9 1 5 2 13 6 8 14 7 12 10 
11 5 2 9 1 3 4 13 8 6 14 7 10 12 
11 6 1 2 8 3 4 13 9 5 7 14 10 12 
12 2 4 6 7 3 1 14 5 8 11 13 10 9 
12 2 6 3 7 4 1 14 5 10 8 13 11 9 
12 2 6 4 7 1 3 14 5 10 9 13 8 11 
12 2 7 3 4 6 1 14 5 11 8 10 13 9 
12 3 5 8 1 4 2 14 6 9 13 7 11 10 
12 4 2 8 5 3 1 14 7 6 13 11 10 9 
12 6 1 3 7 4 2 14 9 5 8 13 11 10 
12 7 1 4 2 6 3 14 10 5 9 8 13 11 
12 8 2 4 1 3 5 14 11 6 9 7 10 13 
12 8 3 1 4 2 5 14 11 7 6 10 9 13 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
 * 
Number of Solutions: 53
x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 
1 4 8 9 5 6 2 3 7 12 14 11 13 10 
1 4 9 6 8 5 2 3 7 13 11 14 12 10 
1 5 10 6 7 2 4 3 8 14 11 13 9 12 
1 6 10 7 2 4 5 3 9 14 12 8 11 13 
1 8 9 2 4 5 6 3 11 13 7 10 12 14 
1 9 6 2 8 4 5 3 12 10 7 14 11 13 
1 10 4 7 5 2 6 3 13 8 12 11 9 14 
1 10 5 6 2 7 4 3 13 9 11 8 14 12 
1 10 5 7 2 4 6 3 13 9 12 8 11 14 
1 10 7 4 2 5 6 3 13 11 9 8 12 14 
2 6 10 8 1 5 3 4 9 14 13 7 12 11 
2 7 9 1 8 5 3 4 10 13 6 14 12 11 
2 9 7 1 8 3 5 4 12 11 6 14 10 13 
2 10 3 6 8 5 1 4 13 7 11 14 12 9 
2 11 6 3 7 5 1 4 14 10 8 13 12 9 
2 11 6 7 3 1 5 4 14 10 12 9 8 13 
3 8 10 1 7 2 4 5 11 14 6 13 9 12 
3 10 2 7 8 4 1 5 13 6 12 14 11 9 - missing solution
3 10 7 1 8 2 4 5 13 11 6 14 9 12 
3 11 6 8 1 2 4 5 14 10 13 7 9 12 
3 11 8 2 4 6 1 5 14 12 7 10 13 9 
3 11 8 4 1 6 2 5 14 12 9 7 13 10 
4 10 1 7 8 2 3 6 13 5 12 14 9 11 
4 11 9 3 1 5 2 6 14 13 8 7 12 10 
5 1 10 8 6 2 3 7 4 14 13 12 9 11 
5 11 9 1 2 3 4 7 14 13 6 8 10 12 
8 1 2 9 7 5 3 10 4 6 14 13 12 11 
8 11 1 2 3 6 4 10 14 5 7 9 13 12 
9 1 2 7 8 3 5 11 4 6 12 14 10 13 
9 1 6 3 2 7 5 11 4 10 8 12 14 13 - additional solution, clause not respected [-31, -23], sol. #29

1. level: 15, Variable: x2 = 6<--6
Variable being traced has changed into x11::{2..3, 5, 7..8, 10, 12..14}
Variable being traced has changed into x4::{2..3, 5, 7..8, 10, 12..14}
Variable being traced has changed into x11::{2..3, 5, 7..8, 12..14}
Variable being traced has changed into x4::{2..3, 5, 7..8, 12..14}
Variable being traced has changed into x11::{2..3, 7..8, 12..14}
Variable being traced has changed into x4::{2..3, 7..8, 12..14}
Variable being traced has changed into x11::{2..3, 8, 12..14}
Variable being traced has changed into x4::{2..3, 8, 12..14}
Variable being traced has changed into x11::{2..3, 8, 12, 14}
Variable being traced has changed into x4::{2..3, 8, 12, 14}
Variable being traced has changed into x11::{2..3, 8, 12}
Variable being traced has changed into x4::{2..3, 8, 12}
Variable being traced has changed into x11::{2..3, 12}
Variable being traced has changed into x4::{2..3, 12}
Variable being traced has changed into x11::{2, 12}
Variable being traced has changed into x4::{2, 12}
Variable being traced has changed into x4 = 2
Variable being traced has changed into x11 = 12
Variable index 2	15
Store level changes from 15 to 16
Solution # 29

9 4 1 8 2 3 6 11 7 5 13 12 10 14 - additional solution
9 2 10 3 1 6 4 11 5 14 8 7 13 12 - missing solution
10 1 3 6 8 2 5 12 4 7 11 14 9 13 
10 1 3 8 5 2 6 12 4 7 13 11 9 14 
10 1 5 2 8 6 3 12 4 9 7 14 13 11 
10 2 4 6 3 7 1 12 5 8 11 13 14 9 - additional solution
10 2 4 9 1 6 3 12 5 8 14 7 13 11 
10 2 9 3 1 4 6 12 5 13 8 7 11 14 
10 4 1 9 2 6 3 12 7 5 14 8 13 11 
11 1 5 3 6 7 2 13 4 9 8 12 14 10 
11 1 5 7 2 3 6 13 4 9 12 8 10 14 
11 2 8 4 1 3 6 13 5 12 9 7 10 14 - missing solution
11 3 4 9 1 5 2 13 6 8 14 7 12 10 
11 5 2 9 1 3 4 13 8 6 14 7 10 12 
11 6 1 2 8 3 4 13 9 5 7 14 10 12 
12 2 4 6 7 3 1 14 5 8 11 13 10 9 
12 2 6 3 7 4 1 14 5 10 8 13 11 9 
12 2 6 4 7 1 3 14 5 10 9 13 8 11 
12 2 7 3 4 6 1 14 5 11 8 10 13 9 
12 3 5 8 1 4 2 14 6 9 13 7 11 10 
12 3 7 4 2 1 5 14 6 11 9 10 8 13 - additional solution
12 4 2 8 5 3 1 14 7 6 13 11 10 9 
12 6 1 3 7 4 2 14 9 5 8 13 11 10 
12 7 1 4 2 6 3 14 10 5 9 8 13 11 
12 8 2 4 1 3 5 14 11 6 9 7 10 13 
12 8 3 1 4 2 5 14 11 7 6 10 9 13 
 */

public class SatLangfordBug extends ExampleFD {

	static int n = 2;
	static int m = 8;

	//public static StatModule stats = new StatModule(true);
	public static SatWrapper wrapper;
	public static StatModule stats = new StatModule(false);

	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();

		// create a SAT solver wrapper
		wrapper = new SatWrapper();
		store.impose(wrapper);
		wrapper.addSolverComponent(stats);

		// Get problem size n from second program argument.
		IntVar[] x = new IntVar[n * m];

		for (int i = 0; i < n * m; i++) {
			x[i] = new IntVar(store, "x" + i, 1, m * n);
			//wrapper.register(x[i]);
			vars.add(x[i]);
		}

		//     Store.variablesToTrace.add(x[4]);
		//     Store.variablesToTrace.add(x[11]);

		Constraint cx = new Alldistinct(x);
		store.impose(cx);
		store.consistency();

        //store.imposeToSat(new Alldifferent(x));

		for (int i = 0; i + 1 < n; i++) {
			for (int j = 0; j < m; j++) {

				// if (i % 2 == 0) {
				store.imposeToSat(new XplusCeqZ(x[i * m + j], (j + 2), x[(i + 1) * m + j]));
				//     System.out.println(new XplusCeqZ(x[i * m + j], (j + 2), x[(i + 1) * m + j]));
				// }
				// else
				store.imposeToSat(new XplusCeqZ(x[i * m + j], (j + 2), x[(i + 1) * m + j]));

				// System.out.println(new XplusCeqZ(x[i * m + j], (j + 2), x[(i + 1) * m
				//		+ j]));
			}
		}

		store.consistency();



	}

	/**
	 * It uses BoundDomain for all variables.
	 */
	public void modelBound() {

		store = new Store();
		vars = new ArrayList<IntVar>();

		// Get problem size n from second program argument.
		IntVar[] x = new IntVar[n * m];

		for (int i = 0; i < n * m; i++) {
			x[i] = new IntVar(store, "x" + i, new BoundDomain(1, m * n) );
			vars.add(x[i]);
		}

		for (int i = 0; i + 1 < n; i++) {
			for (int j = 0; j < m; j++) {
				store.impose(new XplusCeqZ(x[i * m + j], (j + 2), x[(i + 1) * m	+ j]));
			}
		}

		Constraint cx = new Alldiff(x);
		store.impose(cx);

	}


	/**
	 * It uses the dual model.
	 */
	public void modelDual() {

		store = new Store();
		vars = new ArrayList<IntVar>();

		IntVar[] x = new IntVar[n * m];

		for (int i = 0; i < n * m; i++) {
			x[i] = new IntVar(store, "x" + i, 0, m * n - 1);
			vars.add(x[i]);
		}

		for (int i = 0; i + 1 < n; i++) {
			for (int j = 0; j < m; j++) {

				store.impose(new XplusCeqZ(x[i * m + j], (j + 2), x[(i + 1) * m + j]));

			}
		}

		Constraint cx = new Alldistinct(x);
		store.impose(cx);

		IntVar[] d = new IntVar[n * m];

		for (int i = 0; i < n * m; i++) {
			d[i] = new IntVar(store, "d" + i, 0, m * n - 1);
			vars.add(d[i]);
		}

		store.impose(new Assignment(x, d));

	}

	/**
	 * It executes the program to solve the Langford problem.
	 * It is possible to specify two parameters. If no 
	 * parameter is used then default values for n and m are used.
	 * 
	 * @param args the first parameter denotes n, the second parameter denotes m.
	 */
	public static void test(String args[]) {

		SatLangfordBug example = new SatLangfordBug();
		if (args.length > 1) {
			SatLangfordBug.n = new Integer(args[0]);
			SatLangfordBug.m = new Integer(args[1]);
		}	

		example.model();

		if (example.search())
			System.out.println("Solution(s) found");

		SatLangfordBug exampleBound = new SatLangfordBug();
		if (args.length > 1) {
			SatLangfordBug.n = new Integer(args[0]);
			SatLangfordBug.m = new Integer(args[1]);
		}

		exampleBound.modelBound();

		if (exampleBound.search())
			System.out.println("Solution(s) found");		


		SatLangfordBug exampleDual = new SatLangfordBug();
		if (args.length > 1) {
			SatLangfordBug.n = new Integer(args[0]);
			SatLangfordBug.m = new Integer(args[1]);
		}
		exampleDual.modelDual();

		if (exampleDual.search())
			System.out.println("Solution(s) found");

	}	


	/**
	 * It executes the program to solve the Langford problem.
	 * It is possible to specify two parameters. If no 
	 * parameter is used then default values for n and m are used.
	 * 
	 * @param args the first parameter denotes n, the second parameter denotes m.
	 */
	public static void main(String args[]) {

		SatLangfordBug example = new SatLangfordBug();
		if (args.length > 1) {
			SatLangfordBug.n = new Integer(args[0]);
			SatLangfordBug.m = new Integer(args[1]);
		}	

		example.model();

		/*        
        // add debug and stat modules
		StatModule mod = new StatModule(false);
		example.wrapper.addSolverComponent(mod);
		example.wrapper.core.verbosity = 3;

		// debug module
		WrapperDebugModule debug = new WrapperDebugModule();
		example.wrapper.addWrapperComponent(debug);
		 */      

		if (example.searchAllAtOnce())
			System.out.println("Solution(s) found");

		//   example.search.printAllSolutions();
	}	


	public boolean searchAllAtOnce() {

		long T1, T2;
		T1 = System.currentTimeMillis();		

		SelectChoicePoint select = new SimpleSelect(vars.toArray(new Var[1]),
				null, new IndomainMin());

		search = new DepthFirstSearch();
		//search.setSolutionListener(new PrintListener());

		search.getSolutionListener().searchAll(true);
		search.getSolutionListener().recordSolutions(false);
		search.setPrintInfo(true);

		search.setAssignSolution(true);

		boolean result = search.labeling(store, select);

		T2 = System.currentTimeMillis();

		if (result) {
			System.out.println("Number of solutions " + search.getSolutionListener().solutionsNo());
			//	search.printAllSolutions();
		} 
		else
			System.out.println("Failed to find any solution");

		System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");

		return result;
	}


	/**
	 * It is a simple print listener to print every tenth solution encountered.
	 */
	public class PrintListener extends SimpleSolutionListener {

		@Override
		public boolean executeAfterSolution(Search search, SelectChoicePoint select) {

			boolean returnCode = super.executeAfterSolution(search, select);


			System.out.println("Solution # " + noSolutions);
			for (Domain dom : search.getSolution())
				System.out.print(dom + " ");
					System.out.println();


					return returnCode;
		}


	}      

}
