/**
 *  Golomb.java 
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
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.jacop.search.PrintOutListener;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;

/**
 * 
 * It models a Golomb ruler problem.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 *
 * 
 * Golomb ruler is a special sequence of natural numbers
 * an example is 0 1 4 6
 *
 * a sequence is a Golomb ruler if all differences are different
 * (1-0), (4-0), (6-0), (4-1), (6-1), (6-4)
 * 1 4 6 3 5 2
 * All differences above have different values
 * A Golomb ruler is optimal if the length of it (the last mark)
 * has the smallest possible value
 * The presented ruler with 4 marks of length 6 is optimal
 */

public class Golomb extends ExampleFD {

	/**
	 * It specifies the number of marks (number of natural numbers in 
	 * the sequence).
	 */
	public int noMarks = 10;

	/**
	 * It specifies the upper bound of the optimal solution.
	 */
	public int bound = -1;

	
	/**
	 * It contains all differences between all possible pairs of marks.
	 */
	public ArrayList<IntVar> subs = new ArrayList<IntVar>();
	
	@Override
	public void model() {

		System.out.println("Program to solve Golomb mark problem - length "
				           + noMarks);

		store = new Store();
		vars = new ArrayList<IntVar>();
		
		IntVar numbers[] = new IntVar[noMarks];

		for (int i = 0; i < numbers.length; i++) {
			// Create FDV for each natural number
			numbers[i] = new IntVar(store, "n" + new Integer(i), (i + 1) * i / 2,
					noMarks * noMarks);

			// Impose constraints that each consequtive number
			// is larger than the previous one
			// Golomb ruler is an ordered sequence of numbers
			if (i > 0)
				store.impose(new XltY(numbers[i - 1], numbers[i]));
			else
				store.impose(new XeqC(numbers[0], 0));
		}

		for (IntVar v : numbers)
			vars.add(v);
		
		if (bound > -1)
			store.impose(new XlteqC(numbers[noMarks - 1], bound));

		// ArrayList contains all differences
		subs = new ArrayList<IntVar>();

		for (int i = 1; i < numbers.length; i++) {

			// for (int j = i - 1; j >= 0; j--) {
			for (int j = 0; j < i; j++) {
				// Create FDV for a difference between ith and jth number
				IntVar sub = new IntVar(store, "c" + i + "_" + j, (i - j)
						* (i - j + 1) / 2, noMarks * noMarks);

				subs.add(sub);

				// sub + jth = ith since sub = ith - jth
				// Add constraint so the above relationship holds
	//			store.imposePropagators(new XplusYeqZ(sub, numbers[j], numbers[i]));
				store.impose(new XplusYeqZ(sub, numbers[j], numbers[i]));

			}
		}

		int index = 0;
		for (int i = 1; i < noMarks; i++)
			for (int j = 0; j < i; j++)
//				store.imposePropagators(new XplusClteqZ(subs.get(index++), (noMarks - 1 - i + j)
//						* (noMarks - i + j) / 2, numbers[noMarks - 1]));
				store.impose(new XplusClteqZ(subs.get(index++), (noMarks - 1 - i + j)
						* (noMarks - i + j) / 2, numbers[noMarks - 1]));

		// symmetry breaking constraint
		// important constraint to reduce search space since
		// interested in proving the optimality
		store.impose(new XltY(subs.get(0), subs.get(subs.size() - 1)));

		// All differences have to have unique values
		store.impose(new Alldiff(subs), 1);

		cost = numbers[numbers.length - 1];
		
	}
	
	/**
	 * It specifies specific search for the optimal solution search procedure, which 
	 * printouts intermediate search results and shows how the search is progressing.
	 * 
	 * @return true if the (optimal) solution is found, false if no solution found.
	 */
	public boolean searchOptimalInfo() {
		
		long T1, T2;
		T1 = System.currentTimeMillis();
		
		SelectChoicePoint<IntVar> select = new InputOrderSelect<IntVar>(store, 
														vars.toArray(new IntVar[1]),
														new IndomainMin<IntVar>());

		Search<IntVar> search = new DepthFirstSearch<IntVar>();
		
		PrintOutListener<IntVar> solutionListener = new PrintOutListener<IntVar>();
		search.setSolutionListener(solutionListener);
		
		boolean result = search.labeling(store, select, cost);

		if (result)
			store.print();

		T2 = System.currentTimeMillis();

		System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");
		
		return result;
		
	}	
	
	/**
	 * It executes the program which computes the optimal Golomb ruler. 
	 * 
	 * @param args the first argument specifies the number of marks, the second argument specifies the upper bound of the optimal solution.
	 */
	public static void main(String args[]) {
		
		Golomb example = new Golomb();
		
		if (args.length != 0)
			example.noMarks = new Integer(args[0]);
		
		if (args.length > 1)
			example.bound = new Integer(args[1]);
		
		example.model();

		if (example.searchOptimalInfo())
			System.out.println("Solution(s) found");
	
		
	}			


	/**
	 * It executes the program which first computes the optimal Golomb ruler. 
	 * Afterwards, it computes all the optimal solutions but it does not use
	 * previously established cost of the optimal solution.
	 * 
	 * @param args the first argument specifies the number of marks, the second argument specifies the upper bound of the optimal solution.
	 */
	public static void test(String args[]) {
		
		Golomb example = new Golomb();
		
		if (args.length != 0)
			example.noMarks = new Integer(args[0]);
		
		if (args.length > 1)
			example.bound = new Integer(args[1]);
		
		example.model();

		if (example.searchOptimalInfo())
			System.out.println("Solution(s) found");
	
	
		Golomb exampleAll = new Golomb();
		
		if (args.length != 0)
			exampleAll.noMarks = new Integer(args[0]);
		
		if (args.length > 1)
			exampleAll.bound = new Integer(args[1]);
		
		exampleAll.model();

		if (exampleAll.searchAllOptimal())
			System.out.println("Solution(s) found");
		
	}			

	
}
