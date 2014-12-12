/**
 *  Sudoku.java 
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

/**
 *  @author Radoslaw Szymanek
 *  @version 4.2
 */

public class Sudoku extends ExampleFD {

	IntVar[][] elements;
	
	@Override
	public void model() {

		// >0 - known element
		// 0 - unknown element
		int[][] description = { { 0, 1, 0, 4, 2, 0, 0, 0, 5 },
							    { 0, 0, 2, 0, 7, 1, 0, 3, 9 }, 
							    { 0, 0, 0, 0, 0, 0, 0, 4, 0 },
							    { 2, 0, 7, 1, 0, 0, 0, 0, 6 }, 
							    { 0, 0, 0, 0, 4, 0, 0, 0, 0 },
							    { 6, 0, 0, 0, 0, 7, 4, 0, 3 }, 
							    { 0, 7, 0, 0, 0, 0, 0, 0, 0 },
							    { 1, 2, 0, 7, 3, 0, 5, 0, 0 }, 
							    { 3, 0, 0, 0, 8, 2, 0, 7, 0 } };

		// No of rows and columns in a box.
		int noRows = 3;
		int noColumns = 3;

		store = new Store();
		vars = new ArrayList<IntVar>();
		
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

	}

	/**
	 * It specifies the model using mostly primitive constraints. 
	 */
	public void modelBasic() {

		// >0 - known element
		// 0 - unknown element
		int[][] description = { { 0, 1, 0, 4, 2, 0, 0, 0, 5 },
							    { 0, 0, 2, 0, 7, 1, 0, 3, 9 }, 
							    { 0, 0, 0, 0, 0, 0, 0, 4, 0 },
							    { 2, 0, 7, 1, 0, 0, 0, 0, 6 }, 
							    { 0, 0, 0, 0, 4, 0, 0, 0, 0 },
							    { 6, 0, 0, 0, 0, 7, 4, 0, 3 }, 
							    { 0, 7, 0, 0, 0, 0, 0, 0, 0 },
							    { 1, 2, 0, 7, 3, 0, 5, 0, 0 }, 
							    { 3, 0, 0, 0, 8, 2, 0, 7, 0 } };

		// No of rows and columns in a box.
		int noRows = 3;
		int noColumns = 3;

		store = new Store();
		vars = new ArrayList<IntVar>();
		
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
		
	}
	
	
    
	/**
	 * It specifies the main executable function creating a model for 
	 * a particular Sudoku. 
	 * 
	 * @param args not used. 
	 */
	public static void main(String args[]) {

		Sudoku example = new Sudoku();
		
		example.model();

		if (example.searchSmallestDomain(false))
			System.out.println("Solution(s) found");
		
		ExampleFD.printMatrix(example.elements, example.elements.length, example.elements[0].length);
		
		example = new Sudoku();
		
	}		

	
	/**
	 * It specifies the testing function creating a model for a particular Sudoku. 
	 * 
	 * @param args not used. 
	 */
	public static void test(String args[]) {

		Sudoku example = new Sudoku();
		
		example.model();

		if (example.searchSmallestDomain(false))
			System.out.println("Solution(s) found");
		
		ExampleFD.printMatrix(example.elements, example.elements.length, example.elements[0].length);
		
		example = new Sudoku();
		
		example.modelBasic();

		if (example.searchSmallestDomain(false))
			System.out.println("Solution(s) found");

		ExampleFD.printMatrix(example.elements, example.elements.length, example.elements[0].length);

	}		

}
