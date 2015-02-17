/**
 *  ValueEnumeration.java 
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
 * Defines a methods for enumerating values contained in the domain.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public abstract class ValueEnumeration {

	/**
	 * It checks if the value enumeration has more elements.
	 * @return true if more elements can be enumerated, false otherwise.
	 */
	public abstract boolean hasMoreElements();

	/**
	 * It returns the next element in the enumeration. 
	 * @return the next element.
	 */
	public abstract int nextElement();

	/**
	 * This function is called to inform enumeration of the change of the domain
	 * it enumerates over. The enumeration will update its private data structure
	 * and if possible adapt next element to the closest (on the right) which is 
	 * still in the domain.
	 */
	public abstract void domainHasChanged();

}
