/**
 *  IndomainMedian.java 
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
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.ValueEnumeration;

/**
 * IndomainMedian - implements enumeration method based on the selection of the
 * median value in the domain of FD variable and then right and left values.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 * @param <T> type of variable being used in search.
 */

public class IndomainMedian<T extends IntVar> implements Indomain<T> {

	/**
	 * It creates Indomain heuristic which chooses the middle value.
	 */
	public IndomainMedian() {
	}

	/**
	 * It requires IntVar variable.
	 */

	public int indomain(IntVar var) {

		assert (! var.singleton()) : "indomain does not work with singleton variables.";

		assert ( var.dom().domainID() != IntDomain.BoundDomainID) : "It is not possible to use BoundDomain";

		int position = var.getSize();
		
		if (position % 2 == 0)
			position = ( position >> 1 ) - 1;
		else
			position = position >> 1;

		if (var.domain.domainID() == IntDomain.IntervalDomainID) {

			IntervalDomain domain = (IntervalDomain) var.domain;

			for (int i = 0; i < domain.size; i++) {
				
				int intervalSize = domain.intervals[i].max - domain.intervals[i].min + 1;
				if (intervalSize <= position) {
					position -= intervalSize;
				}
				else 
					return domain.intervals[i].min + position;
			}

			assert false : "Indomain Median does not work properly.";
			
		}

		IntDomain dom = var.dom();
		
		if (dom.isSparseRepresentation()) {
			
			ValueEnumeration enumer = dom.valueEnumeration();
			
			while (enumer.hasMoreElements() && position > 0) {
				enumer.nextElement();
				position--;
			}

			return enumer.nextElement();

		}
		else {
			
			IntervalEnumeration enumer = dom.intervalEnumeration();
			
			while (enumer.hasMoreElements()) {
				
				Interval next = enumer.nextElement();
				
				int intervalSize = next.max - next.min + 1;
				
				if (intervalSize <= position) {
					position -= intervalSize;
				}
				else 
					return next.min + position;

			}

		}

		assert false : "Indomain Median does not work properly.";

		return 0;		

	}

}
