/**
 *  IndomainRandom.java 
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

package org.jacop.search;

import java.util.Random;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;

/**
 * IndomainRandom - implements enumeration method based on the selection of the
 * random value in the domain of FD variable. Can split domains into multiple
 * intervals
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 * @param <T> type of variable being used in the search.
 */

public class IndomainRandom<T extends IntVar> implements Indomain<T> {

	private final Random generator;
	
	/**
	 * It specifies Indomain function, which assigns values randomly.
	 */
	public IndomainRandom() {
		generator = new Random();
	}

	/**
	 * It specifies Indomain function, which assigns values randomly.
	 * @param seed it specifies the seed of the random generator.
	 */
	public IndomainRandom(int seed) {
		generator = new Random(seed);
	}

	public int indomain(IntVar var) {

		assert (!var.singleton()) : "Indomain should not be called with singleton domain";
		
		IntDomain dom = var.domain;

		int min = dom.min();
		int size = dom.getSize();

		if (size == 0)
			return min;

		int value = generator.nextInt(size);

		int domainSize = dom.noIntervals();
		if (domainSize == 1)
			return value + min ;

		for (int i = 0; i < domainSize; i++) {

			int currentMin = dom.leftElement(i);
			int currentMax = dom.rightElement(i);

			// System.out.println( dom +", "+value);
			if (currentMax - currentMin + 1 > value)
				return currentMin + value;
			else
				value -= currentMax - currentMin + 1;

		}

		// Only to satisfy the compiler.
		assert false : "Error. This code should not be reached.";
		return Integer.MAX_VALUE;

	}

}
