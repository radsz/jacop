/**
 *  IndomainSimpleRandom.java 
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

public class IndomainSimpleRandom<T extends IntVar> implements Indomain<T> {

	/**
	 * It does not achieve uniform probability but it does work faster than
	 * IndomainRandom.
	 */
	public IndomainSimpleRandom() {
	}

	public int indomain(IntVar var) {

		IntDomain dom = var.domain;

		return dom.getRandomValue();
				
	}

}
