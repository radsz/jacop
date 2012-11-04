/**
 *  BIBD.java
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

import org.jacop.constraints.AndBool;
import org.jacop.constraints.Sum;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.jasat.modules.StatModule;

/**
 *
 * It models and solves Balanced Incomplete Block Design (BIBD) problem (CSPLIB-P28).
 *
 * @author Radoslaw Szymanek
 * @version 3.0
 */

/*
Depth First Search DFS0
        [x0_0=1, x0_1=1, x0_2=1, x0_3=0, x0_4=0, x0_5=0, x0_6=0, x1_0=1, x1_1=0, x1_2=0, x1_3=1, x1_4=1, x1_5=0, x1_6=0, x2_0=1, x2_1=0, x2_2=0, x2_3=0, x2_4=0, x2_5=1, x2_6=1, x3_0=0, x3_1=1, x3_2=0, x3_3=1, x3_4=0, x3_5=1, x3_6=0, x4_0=0, x6_0=0, x5_0=0, x4_1=1, x4_2=0, x4_3=0, x4_5=0, x4_6=1, x4_4=1, x5_1=0, x6_2=1, x6_1=0, x5_2=1, x5_3=1, x6_3=0, x6_6=0, x5_4=0, x6_5=1, x6_4=1, x5_5=0, x5_6=1]

        No of solutions : 151200
        Last Solution : [x0_0=1, x0_1=1, x0_2=1, x0_3=0, x0_4=0, x0_5=0, x0_6=0, x1_0=1, x1_1=0, x1_2=0, x1_3=1, x1_4=1, x1_5=0, x1_6=0, x2_0=1, x2_1=0, x2_2=0, x2_3=0, x2_4=0, x2_5=1, x2_6=1, x3_0=0, x3_1=1, x3_2=0, x3_3=1, x3_4=0, x3_5=1, x3_6=0, x4_0=0, x4_1=1, x4_2=0, x4_3=0, x4_4=1, x4_5=0, x4_6=1, x5_0=0, x5_1=0, x5_2=1, x5_3=1, x5_4=0, x5_5=0, x5_6=1, x6_0=0, x6_1=0, x6_2=1, x6_3=0, x6_4=1, x6_5=1, x6_6=0]
        Nodes : 180033
        Decisions : 165616
        Wrong Decisions : 14417
        Backtracks : 165616
        Max Depth : 28

        Number of solutions 151200

        *** Execution time = 65099 ms



        Solution(s) found
        1 1 1 0 0 0 0
        1 0 0 1 1 0 0
        1 0 0 0 0 1 1
        0 1 0 1 0 1 0
        0 1 0 0 1 0 1
        0 0 1 1 0 0 1
        0 0 1 0 1 1 0
*/

/*
Last Solution : [x0_0=1, x0_1=1, x0_2=1, x0_3=0, x0_4=0, x0_5=0, x0_6=0, x1_0=1, x1_1=0, x1_2=0, x1_3=1, x1_4=1, x1_5=0, x1_6=0, x2_0=1, x2_1=0, x2_2=0, x2_3=0, x2_4=0, x2_5=1, x2_6=1, x3_0=0, x3_1=1, x3_2=0, x3_3=1, x3_4=0, x3_5=1, x3_6=0, x4_0=0, x4_1=1, x4_2=0, x4_3=0, x4_4=1, x4_5=0, x4_6=1, x5_0=0, x5_1=0, x5_2=1, x5_3=1, x5_4=0, x5_5=0, x5_6=1, x6_0=0, x6_1=0, x6_2=1, x6_3=0, x6_4=1, x6_5=1, x6_6=0]
                 Nodes : 179921
                 Decisions : 165560
                 Wrong Decisions : 14361
                 Backtracks : 165560
                 Max Depth : 28

                 Number of solutions 151200

                     *** Execution time = 11323873 ms
  c /==================================
c restarts            : 0          (0/s)
c conflicts           : 14331      (1/s)
c assertions          : 321845     (28/s)
c backjumps           : 321833     (28/s)
c forget              : 0          (0/s)
c added clauses       : 14331      (1/s)
c learn clauses       : 14331      (1/s)
c removed clauses     : 0          (0/s)
c propagations        : 26945130   (2379/s)
c
c trail state: 594/790
c database store state: 20336
c wrapper.translation.DomainClausesDatabase in state 0
c satInsideCp.core.clauses.BinaryClausesDatabase in state 1372
c satInsideCp.core.clauses.TernaryClausesDatabase in state 147
c satInsideCp.core.clauses.DefaultClausesDatabase in state 18811
c satInsideCp.core.clauses.UnaryClausesDatabase in state 6
c \==================================
                     *
                     *
  Depth First Search DFS0
[x0_0=1, x0_1=1, x0_2=1, x0_3=0, x0_4=0, x0_5=0, x0_6=0, x1_0=1, x1_1=0, x1_2=0, x1_3=1, x1_4=1, x1_5=0, x1_6=0, x2_0=1, x2_1=0, x2_2=0, x2_3=0, x2_4=0, x2_5=1, x2_6=1, x3_0=0, x3_1=1, x3_2=0, x3_3=1, x3_4=0, x3_5=1, x3_6=0, x4_0=0, x6_0=0, x5_0=0, x4_1=1, x4_2=0, x4_3=0, x4_5=0, x4_6=1, x4_4=1, x5_1=0, x6_2=1, x6_1=0, x5_2=1, x5_3=1, x6_3=0, x6_6=0, x6_4=1, x6_5=1, x5_4=0, x5_5=0, x5_6=1]No of solutions : 151200
Last Solution : [x0_0=1, x0_1=1, x0_2=1, x0_3=0, x0_4=0, x0_5=0, x0_6=0, x1_0=1, x1_1=0, x1_2=0, x1_3=1, x1_4=1, x1_5=0, x1_6=0, x2_0=1, x2_1=0, x2_2=0, x2_3=0, x2_4=0, x2_5=1, x2_6=1, x3_0=0, x3_1=1, x3_2=0, x3_3=1, x3_4=0, x3_5=1, x3_6=0, x4_0=0, x4_1=1, x4_2=0, x4_3=0, x4_4=1, x4_5=0, x4_6=1, x5_0=0, x5_1=0, x5_2=1, x5_3=1, x5_4=0, x5_5=0, x5_6=1, x6_0=0, x6_1=0, x6_2=1, x6_3=0, x6_4=1, x6_5=1, x6_6=0]
Nodes : 179921
Decisions : 165560
Wrong Decisions : 14361
Backtracks : 165560
Max Depth : 28

Number of solutions 151200

    *** Execution time = 75350 ms



Solution(s) found
1 1 1 0 0 0 0 
1 0 0 1 1 0 0 
1 0 0 0 0 1 1 
0 1 0 1 0 1 0 
0 1 0 0 1 0 1 
0 0 1 1 0 0 1 
0 0 1 0 1 1 0                	*
*/

public class FullSatBIBD extends ExampleFD {

	/**
	 * It specifies number of rows in the incidence matrix.
	 */
	public int v = 7;
	/**
	 * It specifies number of columns in the incidence matrix.
	 */
	public int b = 7;
	/**
	 * It specifies number of ones in each row.
	 */
	public int r = 3;
	/**
	 * It specifies number of ones in each column.
	 */
	public int k = 3;
	/**
	 * It specifies the value of the scalar product of any two distinct rows.
	 */
	public int lambda = 1;

	IntVar[][] x;

	//public static StatModule stats = new StatModule(true);
	
	public static StatModule stats = new StatModule(false);

	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();

		//wrapper.addSolverComponent(new WrapperDebugModule());
		//wrapper.core.verbosity = 3;

		// Get problem size n from second program argument.
		x = new IntVar[v][b];

		for (int i = 0; i < v; i++)
			for (int j = 0; j < b; j++) {
			x[i][j] = new BooleanVar(store, "x" + i + "_" + j);
			vars.add(x[i][j]);
		}

		IntVar rVar = new IntVar(store, "r", r, r);
		IntVar kVar = new IntVar(store, "k", k, k);
		IntVar lambdaVar = new IntVar(store, "lambda", lambda, lambda);
		
		for (int i = 0; i < v; i++) {
			//store.impose(new Sum(x[i], rVar));
			store.imposeToSat(new Sum(x[i], rVar));
		}

		for (int j = 0; j < b; j++) {
			IntVar[] column = new IntVar[v];
			for (int i = 0; i < v; i++)
				column[i] = x[i][j];
			//store.impose(new Sum(column, kVar), 1);
			store.imposeToSat(new Sum(column, kVar));
		}

		for (int i = 0; i - 1 < v; i++)
			for (int j = i + 1; j < v; j++) {

				ArrayList<IntVar> result = new ArrayList<IntVar>();

				for (int m = 0; m < b; m++) {
                                    
					IntVar product = new BooleanVar(store, "p" + i + "_" + j + "_" + m);
					IntVar[] array = {(IntVar)x[i][m], (IntVar)x[j][m]};

					// use SAT solver here
					//store.impose(new AndBool(array, product));
					store.imposeToSat(new AndBool(array, product));

					result.add(product);
				}

				store.imposeToSat(new Sum(result, lambdaVar));
			}

            // debug: restrict space
//		store.impose(new XeqC(x[0][0], 0));
//		store.impose(new XeqC(x[0][5], 1));
//		store.impose(new XeqC(x[0][4], 1));
//		store.impose(new XeqC(x[0][2], 1));
        
        /*
        store.consistency();
        
        try {
            BufferedWriter output = new BufferedWriter(new FileWriter("current.cnf"));
            wrapper.toCNF(output);
            output.close();
        } catch (IOException ex) {
            System.out.println(ex);
        }
        */
                
	}


	/**
	 * It executes the program to solve the Langford problem.
	 * It is possible to specify two parameters. If no
	 * parameter is used then default values for n and m are used.
	 *
	 * @param args the first parameter denotes n, the second parameter denotes m.
	 */
	public static void main(String args[]) {

		FullSatBIBD example = new FullSatBIBD();

		if (args.length > 1) {
			try {
				example.v = new Integer(args[0]);
				example.b = new Integer(args[1]);
				example.r = new Integer(args[2]);
				example.k = new Integer(args[3]);
				example.lambda = new Integer(args[4]);
			}
			catch(Exception ex) {
				System.out.println("Program parameters if provided must specify v, b, r, k, and lambda");
			}
		}

		example.model();
		
		//wrapper.verbosity = 0;
		//wrapper.consistency(wrapper.store);
		
		/*
		stats = new StatModule(true);
		wrapper.addSolverComponent(stats);
		stats.logStats();
		wrapper.core.verbosity = 0;
		wrapper.addWrapperComponent(new WrapperDebugModule());
	*/
		
		// debug : add clauses and print state of dbStore
		//wrapper.consistency(wrapper.store);
		//System.out.println(wrapper.solver.dbStore);

		if (example.searchAllAtOnce()) {
			
			System.out.println("\n\n");

			System.out.println("Solution(s) found");

			ExampleFD.printMatrix(example.x, example.v, example.b);

		}
		
		//wrapper.core.verbosity = 2;
		//stats.logStats();
	}
}
