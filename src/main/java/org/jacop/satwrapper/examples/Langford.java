/**
 *  Langford.java 
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

package org.jacop.satwrapper.examples;

import java.util.ArrayList;

import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Assignment;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.BoundDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;

/**
 * 
 * It solves Langford problem. 
 * 
 * @author Radoslaw Szymanek
 * @version 3.0
 */

public class Langford extends ExampleFD {

	static int n = 2;
	static int m = 8;

	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		
		// Get problem size n from second program argument.
		IntVar[] x = new IntVar[n * m];

		for (int i = 0; i < n * m; i++) {
			x[i] = new IntVar(store, "x" + i, 1, m * n);
			vars.add(x[i]);
		}

		for (int i = 0; i + 1 < n; i++) {
			for (int j = 0; j < m; j++) {

				store.impose(new XplusCeqZ(x[i * m + j], (j + 2), x[(i + 1) * m
						+ j]));

			}
		}

		Constraint cx = new Alldistinct(x);
		store.impose(cx);
		
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

		Langford example = new Langford();
		if (args.length > 1) {
			Langford.n = new Integer(args[0]);
			Langford.m = new Integer(args[1]);
		}	
		
		example.model();

		if (example.search())
			System.out.println("Solution(s) found");
		
		Langford exampleBound = new Langford();
		if (args.length > 1) {
			Langford.n = new Integer(args[0]);
			Langford.m = new Integer(args[1]);
		}
		
		exampleBound.modelBound();

		if (exampleBound.search())
			System.out.println("Solution(s) found");		
		
		
		Langford exampleDual = new Langford();
		if (args.length > 1) {
			Langford.n = new Integer(args[0]);
			Langford.m = new Integer(args[1]);
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

		Langford example = new Langford();
		if (args.length > 1) {
			Langford.n = new Integer(args[0]);
			Langford.m = new Integer(args[1]);
		}	
		
		example.model();

		if (example.searchAllAtOnce())
			System.out.println("Solution(s) found");
                
              //  example.search.printAllSolutions();
		
	}	

        public boolean searchAllAtOnce() {
		
		long T1, T2;
		T1 = System.currentTimeMillis();		
		
		SelectChoicePoint select = new SimpleSelect(vars.toArray(new Var[1]),
				null, new IndomainMin());

		search = new DepthFirstSearch();
		
		search.getSolutionListener().searchAll(true);
		search.getSolutionListener().recordSolutions(false);
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
	
}
