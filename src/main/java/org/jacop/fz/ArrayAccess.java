/**
 *  ArrayAccess.java
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
package org.jacop.fz;


/**
 *
 * It stores information about a single array access encountered during parsing flatzinc file.
 *
 * @author Krzysztof Kuchcinski
 *
 */

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ArrayAccess  { private static Logger logger = LoggerFactory.getLogger(ArrayAccess.class);

	String id;

	int index;

	/**
	 * It creates an array access storage object.
	 *
	 * @param id the string describing identity of the array being accessed.
	 * @param index the index of the element being accessed.
	 */
	public ArrayAccess(String id, int index) {

		this.id = id;
		this.index = index;

	}

	String getIdent() {
		return id;
	}

	int getIndex() {
		return index;
	}

	public String toString() {
		return id + "[" + index + "]";
	}

}

