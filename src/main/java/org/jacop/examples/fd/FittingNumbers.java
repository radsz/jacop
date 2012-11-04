/**
 *  FittingNumbers.java 
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

import org.jacop.constraints.SumWeight;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * 
 * It is program to solve problem of fitting numbers to made them equal to zero. 
 * 
 * @author Radoslaw Szymanek
 * 
 * Find how many copies of each numbers to take that its sum is equal to one of the specified domain. 
 * 520, 247, 2626, 2119, 520, 2054, 1976, 1209, 1118, 1287, 1040, 741, 390, 2691, 2717, -1000
 * 
 */

public class FittingNumbers extends ExampleFD {

	int[] elements =   {520, 247, 2626, 2119, 2054, 1976, 1209, 1118, 1287, 741, 2691, 2717};

	int [] sum = {13000};
	
	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		
		IntVar[] counters = new IntVar[elements.length];

		IntervalDomain sumDomain = new IntervalDomain();
		for (int i = 0; i < sum.length; i++)
			sumDomain.unionAdapt(sum[i]);
		IntVar sum = new IntVar(store, "sum", sumDomain);

		vars.add(sum);

		// Creating variables.
		for (int i = 0; i < elements.length; i++) {
			counters[i] = new IntVar(store, "counter" + i, 0, sum.max() / elements[i] );
			vars.add(counters[i]);
		}
		
		store.impose(new SumWeight(counters, elements, sum));
		
		System.out.println(store);
	}
		

	/**
	 * It executes the program to solve simple Kakro puzzle.
	 * @param args
	 */
	public static void main(String args[]) {

		FittingNumbers example = new FittingNumbers();
		
		example.model();

		if (example.searchAllAtOnce()) {
			System.out.println("Solution(s) found");			
		}
		
	}	
	
	
}
