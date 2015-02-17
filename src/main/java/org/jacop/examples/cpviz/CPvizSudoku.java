package org.jacop.examples.cpviz;

/**
 *  Sudoku.java 
 *  This file is part of org.jacop.
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

/**
 *
 * A simple model to solve Sudoku problem. 
 *
 */

import java.util.ArrayList;

import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.*;

/**
 *  @author Radoslaw Szymanek
 *  @version 4.2
 */

public class CPvizSudoku {

	IntVar[][] elements;
	
	public void model() {

		// >0 - known element
		// 0 - unknown element
		int[][] description = { { 0, 0, 0, 0, 0, 0, 0, 0, 0 },
					{ 0, 6, 8, 4, 0, 1, 0, 7, 0 }, 
					{ 0, 0, 0, 0, 8, 5, 3, 0, 0 },
					{ 0, 2, 6, 8, 0, 9, 0, 4, 7 }, 
					{ 0, 0, 7, 0, 0, 0, 9, 0, 0 },
					{ 0, 5, 0, 1, 0, 6, 2, 0, 3 }, 
					{ 0, 4, 0, 6, 1, 0, 0, 0, 0 },
					{ 0, 3, 0, 2, 0, 7, 6, 9, 0 }, 
					{ 0, 0, 0, 0, 0, 0, 0, 0, 0 } };

		// No of rows and columns in a box.
		int noRows = 3;
		int noColumns = 3;

		Store store = new Store();
		ArrayList<Var> vars = new ArrayList<Var>();
		
		elements = new IntVar[noRows * noColumns][noRows * noColumns];

		// Creating variables.
		for (int i = 0; i < noRows * noColumns; i++)
			for (int j = 0; j < noRows * noColumns; j++)
				if (description[i][j] == 0) {
					elements[i][j] = new IntVar(store, "f" + i + j, 1, noRows * noColumns);
					vars.add(elements[i][j]);
				}
				else
					elements[i][j] = new IntVar(store, "f" + i + j,
							description[i][j], description[i][j]);

		// Creating constraints for rows.
		for (int i = 0; i < noRows * noColumns; i++)
			store.impose(new Alldistinct(elements[i]));

		// Creating constraints for columns.
		for (int j = 0; j < noRows * noColumns; j++) {
			IntVar[] column = new IntVar[noRows * noColumns];
			for (int i = 0; i < noRows * noColumns; i++)
				column[i] = elements[i][j];

			store.impose(new Alldistinct(column));
		}

		// Creating constraints for blocks.
		for (int i = 0; i < noRows; i++)
			for (int j = 0; j < noColumns; j++) {

				ArrayList<IntVar> block = new ArrayList<IntVar>();
				for (int k = 0; k < noColumns; k++)
					for (int m = 0; m < noRows; m++)
						block.add(elements[i * noColumns + k][j * noRows + m]);

				store.impose(new Alldistinct(block));

			}

		SelectChoicePoint<IntVar> varSelect = new SimpleSelect<IntVar>(vars.toArray(new IntVar[1]), 
									       null, //new SmallestMax<IntVar>(),
									       new IndomainMin<IntVar>());
		
		DepthFirstSearch<IntVar> search = new DepthFirstSearch<IntVar>();

		// Trace --->
		IntVar[] el = new IntVar[elements.length*elements[0].length];
		int k=0;
		for (int i = 0; i < elements.length; i++)
		    for (int j = 0; j < elements[0].length; j++)
			el[k++] = elements[i][j];

 		TraceGenerator<IntVar> select = new TraceGenerator<IntVar>(search, varSelect, el);

// 		TraceGenerator<IntVar> select = new TraceGenerator<IntVar>(varSelect, false, el);
 // 		search.setConsistencyListener((ConsistencyListener)select);
  // 		search.setExitChildListener((ExitChildListener<IntVar>)select);
//		search.setExitListener((ExitListener)select);
		// <---

		boolean result = search.labeling(store, select);		
	}

	/**
	 * It specifies the model using mostly primitive constraints. 
	 */
	public void modelBasic() {

		// >0 - known element
		// 0 - unknown element
		int[][] description = { { 0, 0, 0, 0, 0, 0, 0, 0, 0 },
					{ 0, 6, 8, 4, 0, 1, 0, 7, 0 }, 
					{ 0, 0, 0, 0, 8, 5, 3, 0, 0 },
					{ 0, 2, 6, 8, 0, 9, 0, 4, 7 }, 
					{ 0, 0, 7, 0, 0, 0, 9, 0, 0 },
					{ 0, 5, 0, 1, 0, 6, 2, 0, 3 }, 
					{ 0, 4, 0, 6, 1, 0, 0, 0, 0 },
					{ 0, 3, 0, 2, 0, 7, 6, 9, 0 }, 
					{ 0, 0, 0, 0, 0, 0, 0, 0, 0 } };

		// No of rows and columns in a box.
		int noRows = 3;
		int noColumns = 3;

		Store store = new Store();
		ArrayList<Var> vars = new ArrayList<Var>();
		
		elements = new IntVar[noRows * noColumns][noRows * noColumns];

		// Creating variables.
		for (int i = 0; i < noRows * noColumns; i++)
			for (int j = 0; j < noRows * noColumns; j++)
				if (description[i][j] == 0) {
				    elements[i][j] = new IntVar(store, "f" + (int)(i+1)+"," + (int)(j+1), 1, noRows * noColumns);
					vars.add(elements[i][j]);
				}
				else
					elements[i][j] = new IntVar(store, "f" + i + j,
							description[i][j], description[i][j]);

		// Creating constraints for rows.
		for (int i = 0; i < noRows * noColumns; i++)
			for (int k = 0; k < noRows * noColumns; k++)
				for (int j = k + 1; j < noRows * noColumns; j++)
					store.impose(new XneqY(elements[i][k], elements[i][j]));

		// Creating constraints for columns.
		for (int i = 0; i < noRows * noColumns; i++)
			for (int k = 0; k < noRows * noColumns; k++)
				for (int j = k + 1; j < noRows * noColumns; j++)
					store.impose(new XneqY(elements[k][i], elements[j][i]));

		// Creating constraints for blocks.
		for (int i = 0; i < noRows; i++)
			for (int j = 0; j < noColumns; j++) {

				ArrayList<IntVar> block = new ArrayList<IntVar>();
				for (int k = 0; k < noColumns; k++)
					for (int m = 0; m < noRows; m++)
						block.add(elements[i * noColumns + k][j * noRows + m]);

				for (int k = 0; k < noColumns*noRows; k++)
					for (int m = k + 1; m < noColumns*noRows; m++)
						store.impose(new XneqY(block.get(k), block.get(m)));

			}
		
		store.consistency();

		IntVar[] el = new IntVar[elements.length*elements[0].length];
		int k=0;
		for (int i = 0; i < elements.length; i++)
		    for (int j = 0; j < elements[0].length; j++)
			el[k++] = elements[i][j];

		SelectChoicePoint<IntVar> varSelect = new SimpleSelect<IntVar>(el, // vars.toArray(new IntVar[1]), 
									       null, //new SmallestDomain<IntVar>(),
									       new IndomainMin<IntVar>());
		
		DepthFirstSearch<IntVar> search = new DepthFirstSearch<IntVar>();

		// Trace --->
 		TraceGenerator<IntVar> select = new TraceGenerator<IntVar>(search, varSelect, el);

// 		TraceGenerator<IntVar> select = new TraceGenerator<IntVar>(varSelect, false, el);
 // 		search.setConsistencyListener((ConsistencyListener)select);
 //  		search.setExitChildListener((ExitChildListener<IntVar>)select);
//		search.setExitListener((ExitListener)select);
		// <---

		boolean result = search.labeling(store, select);		

	}
	
	
    
	/**
	 * It specifies the main executable function creating a model for 
	 * a particular Sudoku. 
	 * 
	 * @param args not used. 
	 */
	public static void main(String args[]) {

		CPvizSudoku example = new CPvizSudoku();
		
		example.modelBasic();		
	}	

}
