/**
 *  PigeonHole.java 
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

import org.jacop.constraints.Alldiff;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * It solves the PigeonHole problem. 
 * 
 * 
 * The problem is how to assign n pigeons into n-1 holes in 
 * such a way that each hole holds only one pigeons.
 * Clearly this problem is not satisfiable.
 * 
 * @author Radoslaw Szymanek
 * 
 */

public class PigeonHole extends ExampleFD {

	/**
	 * 
	 */
	public int noPigeons = 5;

	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();

		IntVar[] numbers = new IntVar[noPigeons];

		for (int i = 0; i < noPigeons; i++)
			numbers[i] = new IntVar(store, "h" + (i + 1), 1, noPigeons - 1);

		store.impose(new Alldiff(numbers));
		
		for (IntVar v : numbers)
			vars.add(v);
		
	}

	/**
	 * It specifies inefficient model which uses only 
	 * primitive constraints.
	 */
	public void modelBasic() {

		store = new Store();
		vars = new ArrayList<IntVar>();

		IntVar[] numbers = new IntVar[noPigeons];

		for (int i = 0; i < noPigeons; i++)
			numbers[i] = new IntVar(store, "h" + (i + 1), 1, noPigeons - 1);

		for (int i = 0; i < noPigeons; i++)
			for (int j = i + 1; j < noPigeons; j++)
				store.impose(new XneqY(numbers[i], numbers[j]));

		for (IntVar v : numbers)
			vars.add(v);
		
	}
	
	/**
	 * It executes the program to solve PigeonHole problem in two 
	 * different ways. The first approach uses global constraint, 
	 * the second approach uses only primitive constraints.
	 * 
	 * @param args the number of pigeons.
	 */
	public static void main(String args[]) {

		PigeonHole example = new PigeonHole();

		if (args.length > 1)
			example.noPigeons = Integer.parseInt(args[1]);
	
		example.model();

		if (example.search())
			System.out.println("Solution(s) found");

		example = new PigeonHole();
			
		if (args.length > 1)
			example.noPigeons = Integer.parseInt(args[1]);
		
		example.modelBasic();

		if (example.search())
			System.out.println("Solution(s) found");

	}	



}
