/**
 *  IndomainHierarchical.java 
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

import java.util.HashMap;

import org.jacop.core.Var;

/**
 * IndomainHierarchical - implements enumeration method based on the selection
 * of the preferred indomain for each variable. The initial idea of having such
 * functionality was proposed by Ben Weiner.
 * 
 * @author Radoslaw Szymanek 
 * 
 * @version 4.2
 * @param <T> type of variable being used in the search.
 */

public class IndomainHierarchical<T extends Var> implements Indomain<T> {

	/**
	 * It defines the default indomain if there is no mapping provided.
	 */
	private Indomain<T> defIndomain;

	/**
	 * It defines for each variable and indomain method which should be used.
	 */
	private HashMap<T, Indomain<T>> hashmap;

	/**
	 * Constructor which specifies the mapping and default indomain to be used
	 * if mapping does not give specific indomain for some variables.
	 * @param hashmap a mapping from variable to indomain heuristic used.
	 * @param defIndomain default indomain used if hashmap does not contain an entry.
	 */

	public IndomainHierarchical(HashMap<T, Indomain<T>> hashmap,
			Indomain<T> defIndomain) {

		this.hashmap = new HashMap<T, Indomain<T>>(hashmap);
		this.defIndomain = defIndomain;

	}

	/*
	 * @throws JaCoPException if no value can be returned since no selection
	 * mechanism is provided.
	 */
	public int indomain(T v) throws RuntimeException {
		if (hashmap.containsKey(v))
			return hashmap.get(v).indomain(v);
		else {
			if (defIndomain == null)
				throw new RuntimeException("Variable " + v
						+ " does not have any indomain"
						+ " associated and default indomain is not defined");
			return defIndomain.indomain(v);
		}
	}

}
