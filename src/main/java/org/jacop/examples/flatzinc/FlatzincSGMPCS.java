/**
 *  FlatzincSGMPCS.java 
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

package org.jacop.examples.flatzinc;

import java.util.*;

import org.jacop.core.*;
import org.jacop.constraints.*;
import org.jacop.constraints.netflow.*;
import org.jacop.constraints.netflow.simplex.*;
import org.jacop.search.*;
import org.jacop.search.sgmpcs.*;
import org.jacop.fz.*;


/**
 * The class Run is used to run test programs for JaCoP package.
 * It is used for test purpose only.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.2
 */
public class FlatzincSGMPCS {
    Store store;

    public static void main (String args[]) {

      FlatzincSGMPCS run = new FlatzincSGMPCS();

      run.ex(args);

    }

    FlatzincSGMPCS() {}

    void ex(String[] args) {

	long T1, T2, T;
	T1 = System.currentTimeMillis();

	if (args.length == 0) {
	    args = new String[2];
	    args[0] = "-s"; args[1] = "jobshop.fzn";
    }
	FlatzincLoader fl = new FlatzincLoader(args); 
	fl.load();

	Store store = fl.getStore();

	// System.out.println (store);

	// System.out.println("============================================");
	// System.out.println(fl.getTables());
	// System.out.println("============================================");

	System.out.println( "\nIntVar store size: "+ store.size()+
			    "\nNumber of constraints: " + store.numberConstraints()
			    );

	if ( fl.getSearch().type() == null || (! fl.getSearch().type().equals("int_search")) ) {
	    System.out.println("The problem is not of type int_search and cannot be handled by this method");

	    System.exit(0);	    
	}

	if (fl.getSolve().getSolveKind() != 1) {
	    System.out.println("The problem is not minimization problem and cannot be handled by this method");

	    System.exit(0);
	}

	int timeOut = fl.getOptions().getTimeOut();
	if (timeOut == 0)
	    timeOut = 900;     // default time-out 900s=15min

	IntVar[] vars = (IntVar[])fl.getSearch().vars();
	IntVar cost = (IntVar)fl.getCost();

 	SGMPCSearch label = new SGMPCSearch(store, vars, cost);
	label.setFailStrategy(label.luby);  // luby or poly
	label.setProbability(0.25);         // limit for probability of selecting search from empty 
	label.setEliteSize(4);              // size of the set of reference solutions
	label.setTimeOut(timeOut);          // time-out in seconds
	label.setInitialSolutionsSize(10);  // size of the random initial solutions

	label.setPrintInfo(true);

  	boolean Result = label.search();

	if (Result) {
	    int[] sol = label.lastSolution();
	    if (sol != null) {
		System.out.println("\n%%% Last found solution with cost " + label.lastCost());
		for (int i = 0; i < sol.length; i++) {
		    System.out.print(sol[i] + " ");	    
		}
	    }
	    else
		System.out.println("\n%%% No solution found with this method");
	}

	T2 = System.currentTimeMillis();
	T = T2 - T1;
	System.out.println("\n\t*** Execution time = "+ T + " ms");

    }

}
