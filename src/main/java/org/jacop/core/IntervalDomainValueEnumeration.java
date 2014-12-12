/**
 *  IntervalDomainValueEnumeration.java 
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

package org.jacop.core;

/**
 * Defines a methods for enumerating values contain in the domain.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class IntervalDomainValueEnumeration extends ValueEnumeration {

	int current;

	IntervalDomain domain;

	Interval i = null;

	int intervalNo = 0;

	int maxIntervalNo = 0;

	/**
	 * It create an enumeration for a given domain.
	 * @param dom domain for which value enumeration is created.
	 */
	public IntervalDomainValueEnumeration(IntervalDomain dom) {
		domain = dom;
		maxIntervalNo = domain.size - 1;
		if (maxIntervalNo >= 0) {
			i = domain.intervals[intervalNo];
			current = i.min;
		}

	}

	@Override
	public boolean hasMoreElements() {
		return (i != null);
	}

	@Override
	public int nextElement() {

		int v;

		if (current < i.max) {
			v = current;
			current++;
			return v;
		} else {

			if (intervalNo < maxIntervalNo) {
				intervalNo++;
				v = current;
				i = domain.intervals[intervalNo];
				current = i.min;
				return v;
			} else {
				i = null;
				return current;
			}
		}
	}

	@Override
	public void domainHasChanged() {
		intervalNo = domain.intervalNo(current);
		maxIntervalNo = domain.size - 1;
		if (intervalNo == -1) {
			
			for (int j = 0; j < maxIntervalNo; j++)
				if (domain.intervals[j].min > current) {
					current = domain.intervals[j].min;
					intervalNo = j;
					i = domain.intervals[j];
					return;
				}
			
			i = null;
			return;
		}
		
		if (i != null)
			i = domain.intervals[intervalNo];
	}
	
}
