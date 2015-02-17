/**
 *  SmallDenseDomainValueEnumeration.java 
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

public class SmallDenseDomainValueEnumeration extends ValueEnumeration {

	int current;

	SmallDenseDomain domain;

	long bits;
	/**
	 * It create an enumeration for a given domain.
	 * @param dom domain for which value enumeration is created.
	 */
	public SmallDenseDomainValueEnumeration(SmallDenseDomain dom) {
		
		domain = dom;
		current = dom.min;
		bits = dom.bits;
		
	}

	@Override
	public boolean hasMoreElements() {
		return (bits != 0);
	}

	@Override
	public int nextElement() {

		if (bits == 0)
			throw new IllegalStateException("No more elements");
		
		while (bits > 0) {
			current++;
			bits = bits << 1;
		}

		int next = current;
		
		current++;
		bits = bits << 1;
		
		return next;
	}

	@Override
	public void domainHasChanged() {

		// current, denotes the last element which has been returned.
		if (domain.min + 63 < current) {
			bits = 0;
			// no more elements.
			return;
		}
		
		bits = domain.bits << (current - domain.min);
	}
	
}
