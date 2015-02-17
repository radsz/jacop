/**
 *  MaxLubCard.java 
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

package org.jacop.set.search;

import org.jacop.search.ComparatorVariable;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * Defines a maximum cardinality, of the least upper bound, variable comparator. The variable with the maximum
 * cardinality for the least upper bound has the priority.
 * 
 * @author Krzysztof Kuchcinski and Robert Åkemalm 
 * @version 4.2
 * @param <T> 
 */

public class MaxLubCard<T extends SetVar> implements ComparatorVariable<T> {

	/**
	 * It constructs a maximum cardinality, of the least upper bound, variable comparator.
	 */
	public MaxLubCard() {
	}

	/**
	 * Compares the cardinality of the variables lub to the float value.
	 */
	public int compare(float left, T var) {

		SetDomain SD = (SetDomain) var.dom();

		int right = SD.lub().getSize();

		if (left > right)
			return 1;
		if (left < right)
			return -1;
		return 0;
	}

	/**
	 * Compares the cardinality of the variables lubs.
	 */
	public int compare(T leftVar, T rightVar) {

		SetDomain leftSD = (SetDomain) leftVar.dom();
		SetDomain rightSD = (SetDomain) rightVar.dom();

		int left = leftSD.lub().getSize();
		int right = rightSD.lub().getSize();

		if (left > right)
			return 1;
		if (left < right)
			return -1;
		return 0;
	}

	/**
	 * Returns the cardinality of the lub.
	 */
	public float metric(T var) {

		SetDomain SD = (SetDomain) var.dom();
		return SD.lub().getSize();
	}

}
