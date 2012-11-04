/**
 *  WhoKilledAgatha.java 
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

import org.jacop.constraints.Eq;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.Sum;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XlteqC;
import org.jacop.core.Domain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;

/**
*
*   Who killed agatha? (The Dreadsbury Mansion Murder Mystery).

*   This is a standard benchmark for theorem proving.  
*   http://www.lsv.ens-cachan.fr/~goubault/H1.dist/H1.1/Doc/h1003.html
*   """ 
*   Someone in Dreadsbury Mansion killed Aunt Agatha. 
*   Agatha, the butler, and Charles live in Dreadsbury Mansion, and 
*   are the only ones to live there. A killer always hates, and is no 
*   richer than his victim. Charles hates noone that Agatha hates. Agatha 
*   hates everybody except the butler. The butler hates everyone not richer 
*   than Aunt Agatha. The butler hates everyone whom Agatha hates. 
*   Noone hates everyone. Who killed Agatha? 
*   """

*   Originally from 
*   F. J. Pelletier: Seventy-five problems for testing automatic theorem provers. Journal of Automated Reasoning, 2: 191â€“216, 1986.

*   Compare with the following models:
*   - MiniZinc: http://www.hakank.org/minizinc/who_killed_agatha.mzn
*   - Comet: http://www.hakank.org/comet/who_killed_agatha.mzn
*   - Gecode: http://www.hakank.org/gecode/who_killed_agatha.cpp

* 
* This Choco model was created by Hakan Kjellerstrand (hakank@bonetmail.com)
* Also, see my Choco page: http://www.hakank.org/choco/ 

*
* This JaCoP model was created by Hakan Kjellerstrand (hakank@bonetmail.com)
* http://www.hakank.org/JaCoP/ .
*
*	@author Hakan Kjellerstrand and Radoslaw Szymanek
*/

public class WhoKilledAgatha extends ExampleFD {

    public void model() {

        int n = 3;
        store = new Store();

        IntVar the_killer = new IntVar(store, "the_killer", 0, n-1);

        int agatha  = 0;
        int butler  = 1;
        int charles = 2;

        IntVar[][] hates = new IntVar[n][n];
        IntVar[][] richer = new IntVar[n][n];
        for(int i = 0; i < n; i++) {
            for(int j = 0; j < n; j++) {
                hates[i][j]  = new IntVar(store, "hates:" + i + "->" + j, 0, 1);
                richer[i][j] = new IntVar(store, "richer:" + i + "->" + j, 0, 1);
            }
        }


        vars = new ArrayList<IntVar>();

        // """
        // Agatha, the butler, and Charles live in Dreadsbury Mansion, and 
        // are the only ones to live there. 
        // """

        // "A killer always hates, and is no richer than his victim."
        for(int i = 0; i < n; i++) {
            store.impose(
                         new IfThen(
                                    new XeqC(the_killer, i),
                                    new XeqC(hates[i][agatha], 1)
                                    )
                         );

            store.impose(
                         new IfThen(
                                    new XeqC(the_killer, i),
                                    new XeqC(richer[i][agatha], 0)
                                    )
                         );
        }
        
        
        // define the concept of richer: 
        //   a) no one is richer than him-/herself
        for(int i = 0; i < n; i++) {
            store.impose(new XeqC(richer[i][i], 0));
        }
        
        // (contd...) 
        //   b) if i is richer than j then j is not richer than i
        for(int i = 0; i < n; i++) {
            for(int j = 0; j < n; j++) {
                if (i != j) {
                    // MiniZinc: richer[i,j] == 1 <-> richer[j,i] == 0
                     store.impose(
                                  new Eq(
                                         new XeqC(richer[i][j], 1),
                                         new XeqC(richer[j][i], 0)
                                         )
                                  );

                }
            }
        }

       
        // "Agatha hates everybody except the butler. "
        store.impose(new XeqC(hates[agatha][charles], 1));
        store.impose(new XeqC(hates[agatha][agatha], 1));
        store.impose(new XeqC(hates[agatha][butler], 0));


  
        // "Charles hates no one that Agatha hates." 
        for(int i = 0; i < n; i++) {
            // MiniZinc: hates[agatha, i] = 1 -> hates[charles, i] = 0
            store.impose(new IfThen(
                                    new XeqC(hates[agatha][i], 1),
                                    new XeqC(hates[charles][i], 0)
                                    )
                         );
        }

        
        // "The butler hates everyone not richer than Aunt Agatha. "
        for(int i = 0; i < n; i++) {
            // MiniZinc: richer[i, agatha] = 0 -> hates[butler, i] = 1
             store.impose(new IfThen(
                                     new XeqC(richer[i][agatha], 0),
                                     new XeqC(hates[butler][i], 1)
                                     )
                          );
        }
        
        // "The butler hates everyone whom Agatha hates." 
        for(int i = 0; i < n; i++) {
            // MiniZinc: hates[agatha, i] = 1 -> hates[butler, i] = 1
             store.impose(new IfThen(
                                     new XeqC(hates[agatha][i], 1),
                                     new XeqC(hates[butler][i], 1)
                                     )
                             );

        }

        vars.add(the_killer);

        for(int i = 0; i < n; i++) {
            for(int j = 0; j < n; j++) {
                vars.add(hates[i][j]);
            }
        }

        for(int i = 0; i < n; i++) {
            for(int j = 0; j < n; j++) {
                vars.add(richer[i][j]);
            }
        }


        // "No one hates everyone. "
        for(int i = 0; i < n; i++) {
            // MiniZinc: sum(j in r) (hates[i,j]) <= 2
            IntVar a[] = new IntVar[n];
            for (int j = 0; j < n; j++) {
                a[j] = new IntVar(store, "a"+ i + "-" + j, 0, 1);
                a[j] = hates[i][j];
            }
            IntVar a_sum = new IntVar(store, "a_sum"+i, 0, n);
            store.impose(new Sum(a, a_sum));
            store.impose(new XlteqC(a_sum, 2));
            vars.add(a_sum);

        }
        

    }
    
    @Override
    public boolean search() {
    	
        SelectChoicePoint<IntVar> select = 
            new SimpleSelect<IntVar> (vars.toArray(new IntVar[1]),
                              new SmallestDomain<IntVar>(),
                              new IndomainMin<IntVar> ()
                              );

        Search<IntVar> label = new DepthFirstSearch<IntVar> ();
        label.getSolutionListener().searchAll(true);
        label.getSolutionListener().recordSolutions(true);
        boolean result = label.labeling(store, select);

        //
        // output
        //
        if (result) {

            int numSolutions = label.getSolutionListener().solutionsNo();

            System.out.println("Number of Solutions: " + numSolutions);

            for(int s = 1; s <= numSolutions; s++) {
                Domain [] res = label.getSolutionListener().getSolution(s);
                int len = res.length;

                System.out.println("the_killer: " + res[0]);

                // print the result
                for(int i = 0; i < len; i++) {
                    System.out.print(res[i] + " ");
                }
                System.out.println();

            }


        }  else {

            System.out.println("No solution.");
            
        } 

        return result;
    } 

    /**
     * It runs the program which solves the logic puzzle "Who killed Agatha". 
     * @param args
     */
    public static void main(String args[]) {

    	WhoKilledAgatha example = new WhoKilledAgatha();
        example.model();

		if (example.search())
			System.out.println("Solution(s) found");

    } // end main

} // end class
 
