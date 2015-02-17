/**
 *  Examples.java 
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

package org.jacop.examples.set;

import java.util.ArrayList;

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.MostConstrainedStatic;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.jacop.search.WeightedDegree;
import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMin;

/**
 * It is an abstract class to describe all necessary functions of any store.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public abstract class ExampleSet {

	/**
	 * It contains all variables used within a specific example.
	 */
	public ArrayList<SetVar> vars;
	
	/**
	 * It specifies the cost function, null if no cost function is used.
	 */
	public IntVar cost;
	
	/**
	 * It specifies the constraint store responsible for holding information 
	 * about constraints and variables.
	 */
	public Store store;
	
	/**
	 * It specifies the search procedure used by a given example.
	 */
	public Search<SetVar> search;	
	
	/**
	 * It specifies a standard way of modeling the problem.
	 */
	public abstract void model();
	
	/**
	 * It specifies simple search method based on input order and lexigraphical 
	 * ordering of values. 
	 * 
	 * @return true if there is a solution, false otherwise.
	 */
	public boolean search() {
		
		long T1, T2;
		T1 = System.currentTimeMillis();
		
		SelectChoicePoint<SetVar> select = new SimpleSelect<SetVar>(vars.toArray(new SetVar[1]), null,
				new IndomainSetMin<SetVar>());

		search = new DepthFirstSearch<SetVar>();

		boolean result = search.labeling(store, select);

		if (result)
			store.print();

		T2 = System.currentTimeMillis();

		System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");
		
		System.out.println();
		System.out.print(search.getNodes() + "\t");
		System.out.print(search.getDecisions() + "\t");
		System.out.print(search.getWrongDecisions() + "\t");
		System.out.print(search.getBacktracks() + "\t");
		System.out.print(search.getMaximumDepth() + "\t");
		
		return result;
		
	}	

	/**
	 * It specifies simple search method based on input order and lexigraphical 
	 * ordering of values. It optimizes the solution by minimizing the cost function.
	 * 
	 * @return true if there is a solution, false otherwise.
	 */
	public boolean searchOptimal() {
		
		long T1, T2;
		T1 = System.currentTimeMillis();
		
		SelectChoicePoint<SetVar> select = new SimpleSelect<SetVar>(vars.toArray(new SetVar[1]), null,
				new IndomainSetMin<SetVar>());

		search = new DepthFirstSearch<SetVar>();
		
		boolean result = search.labeling(store, select, cost);

		if (result)
			store.print();

		T2 = System.currentTimeMillis();

		System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");
		
		return result;
		
	}	
	
	
	/**
	 * It searches for all solutions with the optimal value.
	 * @return true if any optimal solution has been found.
	 */
	public boolean searchAllOptimal() {
		
		long T1, T2, T;
		T1 = System.currentTimeMillis();

		SelectChoicePoint<SetVar> select = new SimpleSelect<SetVar>(vars.toArray(new SetVar[1]), null,
													new IndomainSetMin<SetVar>());

		search = new DepthFirstSearch<SetVar>();
		search.getSolutionListener().searchAll(true);
		search.getSolutionListener().recordSolutions(true);

		boolean result = search.labeling(store, select, cost);

		T2 = System.currentTimeMillis();
		T = T2 - T1;
		System.out.println("\n\t*** Execution time = " + T + " ms");

		return result;
		
	}
	
	/**
	 * It specifies simple search method based on smallest domain variable order 
	 * and lexigraphical ordering of values. 
	 * @param optimal it specifies if the search the optimal solution takes place.
	 * 
	 * @return true if there is a solution, false otherwise.
	 */

	public boolean searchSmallestDomain(boolean optimal) {
		
		long T1, T2;
		T1 = System.currentTimeMillis();
		
		SelectChoicePoint<SetVar> select = new SimpleSelect<SetVar>(vars.toArray(new SetVar[1]), new SmallestDomain<SetVar>(),
				new IndomainSetMin<SetVar>());

		search = new DepthFirstSearch<SetVar>();

		boolean result = false;
		
		if (optimal) 
			search.labeling(store, select, cost);
		else
			search.labeling(store, select);

		System.out.println();
		System.out.print(search.getNodes() + "\t");
		System.out.print(search.getDecisions() + "\t");
		System.out.print(search.getWrongDecisions() + "\t");
		System.out.print(search.getBacktracks() + "\t");
		System.out.print(search.getMaximumDepth() + "\t");
		
		if (result)
			store.print();

		T2 = System.currentTimeMillis();

		System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");
		
		return result;
		
	}	
	
	/**
	 * It specifies simple search method based on weighted degree variable order 
	 * and lexigraphical ordering of values. This search method is rather general
	 * any problem good fit. It can be a good first trial to see if the model is 
	 * correct.
	 * 
	 * @return true if there is a solution, false otherwise.
	 */

	public boolean searchWeightedDegree() {
		
		long T1, T2;
		T1 = System.currentTimeMillis();
		
		SelectChoicePoint<SetVar> select = new SimpleSelect<SetVar>(vars.toArray(new SetVar[1]), 
							    new WeightedDegree<SetVar>(),
							    new SmallestDomain<SetVar>(),
							    new IndomainSetMin<SetVar>());

		search = new DepthFirstSearch<SetVar>();

		boolean result = search.labeling(store, select);

		System.out.println();
		System.out.print(search.getNodes() + "\t");
		System.out.print(search.getDecisions() + "\t");
		System.out.print(search.getWrongDecisions() + "\t");
		System.out.print(search.getBacktracks() + "\t");
		System.out.print(search.getMaximumDepth() + "\t");
		
		if (result)
			store.print();

		T2 = System.currentTimeMillis();

		System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");
		
		return result;
		
	}	

	/**
	 * It specifies simple search method based variable order which 
	 * takes into account the number of constraints attached to a variable 
	 * and lexigraphical ordering of values. 
	 * 
	 * @return true if there is a solution, false otherwise.
	 */

	public boolean searchMostConstrainedStatic() {
		
		search = new DepthFirstSearch<SetVar>();

		SelectChoicePoint<SetVar> select = new SimpleSelect<SetVar>(vars.toArray(new SetVar[1]),
				new MostConstrainedStatic<SetVar>(), new IndomainSetMin<SetVar>());

		boolean result = search.labeling(store, select);

		System.out.println();
		System.out.print(search.getNodes() + "\t");
		System.out.print(search.getDecisions() + "\t");
		System.out.print(search.getWrongDecisions() + "\t");
		System.out.print(search.getBacktracks() + "\t");
		System.out.print(search.getMaximumDepth() + "\t");
		
		if (!result)
			System.out.println("**** No Solution ****");

		return result;
	}
	
	/**
	 * It specifies simple search method based on most constrained static and lexigraphical 
	 * ordering of values. It searches for all solutions.
	 * 
	 * @return true if there is a solution, false otherwise.
	 */

	public boolean searchAllAtOnce() {
		
		long T1, T2;
		T1 = System.currentTimeMillis();		
		
		SelectChoicePoint<SetVar> select = new SimpleSelect<SetVar>(vars.toArray(new SetVar[1]),
				new MostConstrainedStatic<SetVar>(), new IndomainSetMin<SetVar>());

		search = new DepthFirstSearch<SetVar>();
		
		search.getSolutionListener().searchAll(true);
		search.getSolutionListener().recordSolutions(true);
		search.setAssignSolution(true);
		
		boolean result = search.labeling(store, select);

		T2 = System.currentTimeMillis();

		if (result) {
			System.out.println("Number of solutions " + search.getSolutionListener().solutionsNo());
		//	search.printAllSolutions();
		} 
		else
			System.out.println("Failed to find any solution");

		System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");

		return result;
	}	
	
	

	/**
	 * It conducts master-slave search. Both of them use input order variable ordering. 
	 * 
	 * @param masterVars it specifies the search variables used in master search.
	 * @param slaveVars it specifies the search variables used in slave search.
	 * 
	 * @return true if the solution exists, false otherwise.
	 */
	public boolean searchMasterSlave(ArrayList<Var> masterVars, 
									 ArrayList<Var> slaveVars) {

		long T1 = System.currentTimeMillis();

		boolean result = false;

		Search<SetVar> labelSlave = new DepthFirstSearch<SetVar>();
		SelectChoicePoint<SetVar> selectSlave = new SimpleSelect<SetVar>(slaveVars.toArray(new SetVar[0]), null,
				new IndomainSetMin<SetVar>());
		labelSlave.setSelectChoicePoint(selectSlave);

		Search<SetVar> labelMaster = new DepthFirstSearch<SetVar>();
		SelectChoicePoint<SetVar> selectMaster = new SimpleSelect<SetVar>(masterVars.toArray(new SetVar[0]), null,
				new IndomainSetMin<SetVar>());
		
		labelMaster.addChildSearch(labelSlave);

		search = labelMaster;
		
		result = labelMaster.labeling(store, selectMaster);

		if (result)
			System.out.println("Solution found");

		if (result)
			store.print();

		long T2 = System.currentTimeMillis();
		
		System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");

		return result;
	}

	
	/**
	 * It returns the search used within an example.
	 * @return the search used within an example.
	 */
	public Search<SetVar> getSearch() {
		return search;
	}

	/**
	 * It specifies the constraint store used within an example.
	 * @return constraint store used within an example.
	 */
	public Store getStore() {
		return store;
	}

	/**
	 * It returns an array list of variables used to model the example.
	 * @return the array list of variables used to model the example.
	 */
	public ArrayList<SetVar> getSearchVariables() {
		return vars;
	}	
		
    /**
     * It prints a matrix of variables. All variables must be grounded.
     * @param matrix matrix containing the grounded variables.
     * @param rows number of elements in the first dimension.
     * @param cols number of elements in the second dimension.
     */
    public static void printMatrix(IntVar[][] matrix, int rows, int cols) {

        for(int i = 0; i < rows; i++) {
            for(int j = 0; j < cols; j++) {
                System.out.print(matrix[i][j].value() + " ");
            }
            System.out.println();
        }

    }

}
