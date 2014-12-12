/**
 *  Laplace.java 
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

package org.jacop.examples.floats;

/**
 * 
 * 
 * From the CLP(R) laplace example:
 * 
 * Solves the Dirichlet problem for Laplace's equation using
 * Leibman's five-point finite-difference approximation. 
 * 
 * Based on minizinc program written by Håkan Kjellerstrand
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * 
 */

import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrintOutListener;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.search.SplitSelectFloat;

public class Laplace {

    void laplace() {

	System.out.println ("========= laplace =========");
	System.out.println ("Solves the Dirichlet problem for Laplace's equation using\nLeibman's five-point finite-difference approximation");

	Store store = new Store();

	FloatDomain.setPrecision(1e-3);

	int r = 10;
	int c = 10;

	
	double Z = 0.0; 
	double M = 100.0; 

	FloatVar[][] x = new FloatVar[r+1][c+1];

	for (int i = 0; i < r+1; i++) 
	    for (int j = 0; j < c+1; j++)
		if (i == 0)
		    x[i][j] = new FloatVar(store, "r["+i+"]["+j+"]", Z, Z);
		else if (i == r || j == 0 || j == c)
		    x[i][j] = new FloatVar(store, "r["+i+"]["+j+"]", M, M);
		else
		    x[i][j] = new FloatVar(store, "r["+i+"]["+j+"]", Z, M);

	for (int i = 1; i < r; i++) 
	    for (int j = 1; j < c; j++)
		store.impose(new LinearFloat(store, new FloatVar[] {x[i][j], x[i-1][j], x[i][j-1], x[i+1][j], x[i][j+1]},
					     new double[] {-4.0, 1.0, 1.0, 1.0, 1.0}, "==", 0.0));


	FloatVar[] xs = new FloatVar[(r+1)*(c+1)];
	int n = 0;
	for (int i = 0; i < r+1; i++) 
	    for (int j = 0; j < c+1; j++)
		xs[n++] = x[i][j];

	// solve minimize cost;
	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, xs, null);
	label.setAssignSolution(true);
	s.leftFirst = false;

	// label.setSolutionListener(new PrintOutListener<FloatVar>());

	label.labeling(store, s);

	for (int i = 0; i < r+1; i++) {
	    for (int j = 0; j < c+1; j++)
		System.out.printf ("%.2f\t", x[i][j].value());
	    System.out.println ();
	}

	System.out.println ();
	System.out.println ("Precision = " + FloatDomain.precision());

    }
	
    /**
     * It executes the program which computes warm distribution. 
     * 
     * @param args no arguments
     */
    public static void main(String args[]) {
		
	Laplace example = new Laplace();

	example.laplace();

    }			


}
