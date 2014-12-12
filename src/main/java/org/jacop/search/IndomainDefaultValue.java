/**
 *  IndomainDefaultValue.java 
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
import java.lang.Number;

import org.jacop.core.Var;
import org.jacop.core.IntVar;

/**
 * IndomainDefaultValue - implements enumeration method based on the
 * selection of the default value for each variable first. If
 * selection of this value will not succeed it will try to assign
 * values with the default indomain method.
 *
 *
 * This method works only for IntVar.
 *
 * @author Krzysztof Kuchcinski 
 * 
 * @version 4.2
 * @param <T> type of variable being used in the search.
 */

public class IndomainDefaultValue<T extends Var> implements Indomain<T> {

	/**
	 * It defines the default indomain if there is no mapping provided.
	 */
	private Indomain<T> defIndomain;

	/**
	 * It defines for each variable and a value which should be used.
	 */
	private HashMap<T, Integer> defValue;

	/**
	 * Constructor which specifies default values to be used
	 * if values are not in the domain a defualt indomain is used.
	 * @param defaultIndomain default indomain heuristic used.
	 * @param defeaultValue default value used for each variable.
	 */

	public IndomainDefaultValue(HashMap<T, Integer> defaultValue,
				    Indomain<T> defaultIndomain) {

		this.defIndomain = defaultIndomain;
		this.defValue = defaultValue;

	}

	/*
	 * indomain method
	 */
	public int indomain(T v) {
	    if (defValue.containsKey(v)) {
		int value = defValue.get(v);
		
		if (((IntVar)v).dom().contains(value)) 
		    return value;
	    }

	    return defIndomain.indomain(v);

	}

}
