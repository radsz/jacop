/**
 *  LatinSquare.java 
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

import org.jacop.constraints.Alldifferent;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * It solves a Latin Square problem.
 * 
 * LatinSquare problem consists of filling the square
 * of size n by n with numbers 1..n in such a way that
 * every row and column does not contain two numbers 
 * of the same value.
 * 
 * QuasiGroupCompletion example provides possibility to
 * impose initial conditions on the values of pre-assigned
 * cells.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 */

public class LatinSquare extends ExampleFD {

	/**
	 * The size of the latin square.
	 */
	public int n = 20;

	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		
		System.out.println("Quasigroup (Latin-square) problem size = " + n
				+ "x" + n);

		// Get problem size n from second program argument.
		IntVar[][] x = new IntVar[n][n];

		for (int i = 0; i < n; i++)
			for (int j = 0; j < n; j++) {
				x[i][j] = new IntVar(store, "x" + i + "_" + j, 1, n);
				vars.add(x[i][j]);
			}

		// Create variables and state constraints.
		for (int i = 0; i < n; i++) {
			store.impose(new Alldifferent(x[i]));

			IntVar[] y = new IntVar[n];
			for (int j = 0; j < n; j++)
				y[j] = x[j][i];
			store.impose(new Alldifferent(y));
		}

	}

	/**
	 * It executes the program to solve the LatinSquare problem.
	 * @param args
	 */
	public static void main(String args[]) {

		LatinSquare example = new LatinSquare();

		if (args.length > 0)
			example.n = Integer.parseInt(args[0]);
		
		example.model();

		if (example.searchSmallestDomain(false))
			System.out.println("Solution(s) found");
		
	}		
	
}
