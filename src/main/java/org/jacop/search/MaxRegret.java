/**
 *  MaxRegret.java 
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
import org.jacop.core.ValueEnumeration;

/**
 * Defines a MaxRegret comparator for Variables.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 * @param <T> variable of type IntVar.
 */

public class MaxRegret<T extends IntVar> implements ComparatorVariable<T> {

	/**
	 * It constructs MaxRegret comparator.
	 */
	public MaxRegret() {
	}

	public int compare(float ldiff, T var) {

		ValueEnumeration rEnum = var.domain.valueEnumeration();

		int rmin = rEnum.nextElement();
		int rminNext = 0;
		if (rEnum.hasMoreElements())
			rminNext = rEnum.nextElement();
		else
			rminNext = IntDomain.MaxInt;

		int rdiff = rminNext - rmin;

		if (ldiff > rdiff)
			return 1;
		if (ldiff < rdiff)
			return -1;
		return 0;

	}

	public int compare(T left, T right) {

		ValueEnumeration lEnum = left.domain.valueEnumeration();

		int lmin = lEnum.nextElement();
		int lminNext = 0;
		if (lEnum.hasMoreElements())
			lminNext = lEnum.nextElement();
		else
			lminNext = IntDomain.MaxInt;

		int ldiff = lminNext - lmin;

		ValueEnumeration rEnum = right.domain.valueEnumeration();

		int rmin = rEnum.nextElement();
		int rminNext = 0;
		if (rEnum.hasMoreElements())
			rminNext = rEnum.nextElement();
		else
			rminNext = IntDomain.MaxInt;

		int rdiff = rminNext - rmin;

		if (ldiff > rdiff)
			return 1;
		if (ldiff < rdiff)
			return -1;
		return 0;

	}

	public float metric(T o) {

		ValueEnumeration oEnum = o.domain.valueEnumeration();

		int omin = oEnum.nextElement();
		int ominNext = 0;
		if (oEnum.hasMoreElements())
			ominNext = oEnum.nextElement();
		else
			ominNext = IntDomain.MaxInt;

		return (ominNext - omin);

	}

}
