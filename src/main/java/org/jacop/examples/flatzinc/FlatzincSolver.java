/**
 *  FlatzincSolver.java 
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
import org.jacop.fz.*;


/**
 * The class Run is used to run test programs for JaCoP package.
 * It is used for test purpose only.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.2
 */
public class FlatzincSolver {
    Store store;

    public static void main (String args[]) {

      FlatzincSolver run = new FlatzincSolver();

      run.ex(args);

    }

    FlatzincSolver() {}

    void ex(String[] args) {

	long T1, T2, T;
	T1 = System.currentTimeMillis();

	if (args.length == 0) {
	    args = new String[2];
	    args[0] = "-s"; args[1] = "wilkinson.fzn";
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

	DepthFirstSearch<Var> label = fl.getDFS();
	SelectChoicePoint<Var> select = fl.getSelectChoicePoint();
	Var cost = fl.getCost();

	boolean result = false;
	if (cost != null)
	    result = label.labeling(fl.getStore(), select, cost);
	else
	    result = label.labeling(fl.getStore(), select);

	fl.getSolve().statistics(result);

	// System.out.println(fl.getTables());

	// System.out.println(fl.getSearch());

	// System.out.println("cost: " + fl.getCost());

  	if ( result )
  	    System.out.println("*** Yes");
	else 
	    System.out.println("*** No");

	T2 = System.currentTimeMillis();
	T = T2 - T1;
	System.out.println("\n\t*** Execution time = "+ T + " ms");

    }

}
