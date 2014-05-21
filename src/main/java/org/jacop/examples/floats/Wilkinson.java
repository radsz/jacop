/**
 *  Wilkinson.java 
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
 * It models wilkinson problem for floating solver based  
 * on minizinc model by Håkan Kjellerstrand
 *
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * 
 */

import java.util.ArrayList;

import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrintOutListener;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.floats.search.SmallestDomainFloat;

public class Wilkinson {

    double MIN_FLOAT = -1e+150;
    double MAX_FLOAT =  1e+150;

    void wilkinson() {

       long T1, T2, T;
	T1 = System.currentTimeMillis();

	System.out.println ("========= wilkinson =========");

	Store store = new Store();

	FloatDomain.setPrecision(1e-13);
	FloatDomain.intervalPrint(false);

	FloatVar x = new FloatVar(store, "x", -100.0, 10.0);

	//0.0 =
	// (x+1.0)*(x+2.0)*(x+3.0)*(x+4.0)*(x+5.0)*(x+6.0)*(x+7.0)*(x+8.0)*(x+9.0)*(x+10.0)*(x+11.0)*(x+12.0)*(x+13.0)*(x+14.0)*(x+15.0)*(x+16.0)*(x+17.0)*(x+18.0)*(x+19.0)*(x+20.0)
	// +
	// 0.00000011920928955078*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x*x

	FloatVar[] temp = new FloatVar[20];
	for (int i = 0; i < 20; i++) {
	    temp[i] = new FloatVar(store, "temp["+i+"]", MIN_FLOAT, MAX_FLOAT);
	    FloatVar c = new FloatVar(store, (double)(i+1), (double)(i+1));
	    store.impose(new PplusQeqR(x, c, temp[i]));
	}

	FloatVar t1 = x; 
	for (int i = 0; i < 18; i++) {
	    FloatVar t2 = new FloatVar(store, MIN_FLOAT, MAX_FLOAT);
	    store.impose(new PmulQeqR(x, t1, t2));
	    t1 = t2;
	}

	FloatVar s1 = temp[0];
	for (int i = 1; i < 20; i++) {
	    FloatVar s2 = new FloatVar(store, MIN_FLOAT, MAX_FLOAT);
	    store.impose(new PmulQeqR(s1, temp[i], s2));
	    s1 = s2;
	}

	store.impose(new LinearFloat(store, new FloatVar[] {s1, t1}, new double[] {1.0, 0.00000011920928955078}, "==", 0.0)); 

	System.out.println( "\bFloatVar store size: "+ store.size()+
  			    "\nNumber of constraints: " + store.numberConstraints()
			    );

	DepthFirstSearch<FloatVar> label = new DepthFirstSearch<FloatVar>();
	SplitSelectFloat<FloatVar> s = new SplitSelectFloat<FloatVar>(store, new FloatVar[] {x}, new SmallestDomainFloat<FloatVar>());
	label.setAssignSolution(true);
	// s.leftFirst = false;

	label.setSolutionListener(new PrintOutListener<FloatVar>());

	label.labeling(store, s, x);

	System.out.println (x);

	System.out.println ("\nPrecision = " + FloatDomain.precision());

	T2 = System.currentTimeMillis();
	T = T2 - T1;

	System.out.println("\n\t*** Execution time = "+ T + " ms");
    }

    /**
     * It executes the program. 
     * 
     * @param args no arguments
     */
    public static void main(String args[]) {
		
	Wilkinson example = new Wilkinson();
		
	example.wilkinson();

    }			
}
