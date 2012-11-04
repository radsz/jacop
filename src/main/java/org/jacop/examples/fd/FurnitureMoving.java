/**
 *  FurnitureMoving.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Hakan Kjellerstrand and Radoslaw Szymanek
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

import org.jacop.constraints.Cumulative;
import org.jacop.constraints.Sum;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;

/**
  * It is a simple logic puzzle about furniture moving. 
  *
  * @author Hakan Kjellerstrand (hakank@bonetmail.com) and Radoslaw Szymanek
  *
  * Problem from Marriott & Stuckey: 'Programming with constraints', page 112f
  *
  * Feature: testing cumulative.
  *
  * Also see http://www.hakank.org/JaCoP/
  * 
  */

public class FurnitureMoving extends ExampleFD {
	
	private static final boolean generateAll = true;

    IntVar [] starts;
    IntVar [] endTimes;
    
	@Override
	public void model() {
		
		store = new Store();

		IntVar numPersons = new IntVar(store, "numPersons", 2, 5); // will be minimized
		IntVar maxTime    = new IntVar(store, "maxTime", 60,60);

		// Start times
		IntVar Sp = new IntVar(store, "Sp", 0, 60); // Piano
		IntVar Sc = new IntVar(store, "Sc", 0, 60); // Chair 
		IntVar Sb = new IntVar(store, "Sb", 0, 60); // Bed
		IntVar St = new IntVar(store, "St", 0, 60); // Table
		IntVar sumStartTimes = new IntVar(store, "SumStartTimes", 0, 1000);

		starts = new IntVar[4];
		starts[0] = Sp;		starts[1] = Sc;		starts[2] = Sb;		starts[3] = St;
		
		store.impose(new Sum(starts, sumStartTimes));

		IntVar[] durations     = new IntVar[4];
		IntVar[] resources     = new IntVar[4];
		endTimes      		= new IntVar[4];
		
		int durationsInts[] = {30,10,15,15}; // duration of task
		int resourcesInts[] = {3,1,3,2};     // resources: num persons required for each task
		for (int i = 0; i < durationsInts.length; i++) {
			// converts to FDV
			durations[i] = new IntVar(store, "dur_"+i, durationsInts[i], durationsInts[i]);
			// converts to FDV
			resources[i] = new IntVar(store, "res_"+i, resourcesInts[i], resourcesInts[i]);

			// all tasks must be finished in 60 minutes
			endTimes[i]  = new IntVar(store, "end_"+i, 0, 120);
			store.impose(new XplusYeqZ(starts[i], durations[i], endTimes[i]));
			store.impose(new XlteqY(endTimes[i], maxTime));
			
	    }	

	    store.impose(new Cumulative(starts, durations, resources, numPersons));

	    
	    if (generateAll) {
	    	// generate all optimal solutions
	    	store.impose(new XeqC(numPersons, 3));
	    }
	    
	    vars = new ArrayList<IntVar>();
	    
	    for(IntVar s: starts) 
	    	vars.add(s);

	    for(IntVar e: endTimes) 
	        vars.add(e);

	    vars.add(numPersons);     
	    
	    cost = numPersons;
	        
	}


	/**
	 * It executes the program which solves this logic puzzle.
	 * @param args
	 */
	public static void main(String args[]) {

		long T1, T2, T;
		T1 = System.currentTimeMillis();

		FurnitureMoving example = new FurnitureMoving();
		example.model();
		
		example.searchSpecific();
		
		T2 = System.currentTimeMillis();
		T = T2 - T1;
		System.out.println("\n\t*** Execution time = " + T + " ms");
	}
	
	
    /**
     * It specifies search for that logic puzzle. 
     */
    public boolean searchSpecific() {

        SelectChoicePoint<IntVar> select = new SimpleSelect<IntVar> (vars.toArray(new IntVar[1]),
                                                     new SmallestDomain<IntVar>(),
                                                     new IndomainMin<IntVar> ());
        
        search = new DepthFirstSearch<IntVar> ();
        search.getSolutionListener().searchAll(true);
        search.getSolutionListener().recordSolutions(true);

        boolean result;
        if (generateAll) {
            // Generate all optimal solutions. 
            // Note: Gives null pointer exception when searchAll(true)
            result = search.labeling(store, select); 
        } else {
            // minimize over numPersons
            result = search.labeling(store, select, cost); 
        }

        Var[] variables = search.getSolutionListener().getVariables();
        for(int i = 0; i < variables.length; i++) {
            System.out.println("Variable " + i + " " + variables[i]);
        }

        if(result) {
            
        	search.printAllSolutions();

            System.out.println("\nNumber of persons needed: " + cost.value());
            System.out.println("Piano: " + starts[0].value() + " .. " + endTimes[0].value() + "\n" +
                               "Chair: " + starts[1].value() + " .. " + endTimes[1].value() + "\n" +
                               "Bed  : " + starts[2].value() + " .. " + endTimes[2].value() + "\n" + 
                               "Table: " + starts[3].value() + " .. " + endTimes[3].value());

                               
            
        } // end if result
        
        return result;

    } // end main
	
	
} // end class FurnitureMoving
