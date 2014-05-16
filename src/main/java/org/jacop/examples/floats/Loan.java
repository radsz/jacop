/**
 *  Loan.java 
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
 * It models tan(x) = -x for floating solver.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * 
 */

import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrintOutListener;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.search.SplitSelectFloat;

public class Loan {

    public void loan(double i, double p, double r, double b4) {

// ￼￼￼LOAN1 I = 0.04;
//            P = 1000.0;
//            R = 260.0;
//            result B4 = 65.78
//       LOAN2 I = 0.04;
//             P = 1000.0;
//             B4 = 0.0;
//             result R=275.49 (precision 1e-11)
//       LOAN3 I = 0.04;
//             R = 250.0;
//             B4 = 0.0;
//	       result P = 907.47 (precision 1e-4)

	System.out.println ("\nProgram to solve loan payments under four quaeter\nI- interest rate, P- principal initially borrowed\nR- quarterly repayment and B4- balance owing at end\nParameters:");

	Store store = new Store();

	FloatDomain.setPrecision(1e-13);

	FloatVar one = new FloatVar(store, "1.0", 1.0, 1.0); 
	FloatVar zero = new FloatVar(store, "0.0", 0.0, 0.0); 

	FloatVar R;  // quarterly repayment
	if (r != 0.0) {
	    R = new FloatVar(store, "R", r, r);
	    System.out.println ("R = " + r);
	}
	else {
	    R = new FloatVar(store, "R", FloatDomain.MinFloat, FloatDomain.MaxFloat);
	    System.out.println ("R = ?");
	}


	FloatVar P;   // principal initially borrowed
	if (p != 0.0) {
	    P = new FloatVar(store, "P", p, p);
	    System.out.println ("P = " + p);
	}
	else {
	    P = new FloatVar(store, "P", FloatDomain.MinFloat, FloatDomain.MaxFloat);
	    System.out.println ("P = ?");
	}


	FloatVar I = new FloatVar(store, "I", i, i);  // interest rate

	FloatVar B1 = new FloatVar(store, "B1", FloatDomain.MinFloat, FloatDomain.MaxFloat); // balance after one quarter
	FloatVar B2 = new FloatVar(store, "B2", FloatDomain.MinFloat, FloatDomain.MaxFloat); // balance after two quarters
	FloatVar B3 = new FloatVar(store, "B3", FloatDomain.MinFloat, FloatDomain.MaxFloat); // balance after three quarters

	FloatVar B4; //  balance owing at end
	if (b4 >= 0.0) {
	    B4 = new FloatVar(store, "B4", b4, b4);
	    System.out.println ("B4 = " + b4);
	}
	else {
	    B4 = new FloatVar(store, "B4", FloatDomain.MinFloat, FloatDomain.MaxFloat);
	    System.out.println ("B4 = ?");
	}

	FloatVar t1 = new FloatVar(store, "t1", 1.0, 2.0);
	store.impose(new PplusQeqR(one, I, t1));
	FloatVar t2 = new FloatVar(store, "t2", FloatDomain.MinFloat, FloatDomain.MaxFloat);
	store.impose(new PmulQeqR(P, t1, t2));
	FloatVar negR = new FloatVar(store, "negR", FloatDomain.MinFloat, FloatDomain.MaxFloat);
	store.impose(new PplusQeqR(R, negR, zero));
	store.impose(new PplusQeqR(t2, negR, B1));

	FloatVar t3 = new FloatVar(store, "t3", FloatDomain.MinFloat, FloatDomain.MaxFloat);
	store.impose(new PmulQeqR(B1, t1, t3));
	store.impose(new PplusQeqR(t3, negR, B2));

	FloatVar t4 = new FloatVar(store, "t4", FloatDomain.MinFloat, FloatDomain.MaxFloat);
	store.impose(new PmulQeqR(B2, t1, t4));
	store.impose(new PplusQeqR(t4, negR, B3));

	FloatVar t5 = new FloatVar(store, "t5", FloatDomain.MinFloat, FloatDomain.MaxFloat);
	store.impose(new PmulQeqR(B3, t1, t5));
	store.impose(new PplusQeqR(t5, negR, B4));

	// solve minimize cost;
	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, new FloatVar[] {B1, B2, B3, B4, P, R}, null);
	// s.leftFirst = false;

	label.setSolutionListener(new PrintOutListener<FloatVar>());

	label.labeling(store, s);

	System.out.println (B4+"\n"+P+"\n"+R);

	System.out.println ("Precision = " + FloatDomain.precision());
    }
	
    /**
     * It executes the program which computes values for tan(x) = -x. 
     * 
     * @param args no arguments
     */
    public static void main(String args[]) {
		
	Loan example = new Loan();

	if (args.length != 4)
	    System.out.println ("Wring number of parameters");
	else {
	    double i = Double.parseDouble(args[0]);
	    double p = Double.parseDouble(args[1]);
	    double r = Double.parseDouble(args[2]);
	    double b4 = Double.parseDouble(args[3]);

	    example.loan(i, p, r, b4);
	}
    }			


}
