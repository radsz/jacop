/**
 *  InputOrderSelect.java 
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

import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Map;

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;

/**
 * It is simple input order selector of variables.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 * @param <T> type of variable being used in the search. 
 */

public class InputOrderSelect<T extends Var> implements SelectChoicePoint<T> {

	static final boolean debugAll = false;

	T[] searchVariables;

	Indomain<T> valueOrdering;

	TimeStamp<Integer> currentIndex;
	
	/**
	 * It stores the original positions of variables to be used for input order
	 * tie-breaking.
	 */

	public IdentityHashMap<T, Integer> position;

	/**
	 * It constructs an input order selection procedure.
	 * @param store a constraint store in which variables resides.
	 * @param variables a list of variables which must be assigned a value by search.
	 * @param indomain the indomain heuristic for assigning values to variables.
	 */
	public InputOrderSelect(Store store, 
							T[] variables,
							Indomain<T> indomain) {

		position = new IdentityHashMap<T, Integer>();

		int unique = 0;
		for (int i = 0; i < variables.length; i++) {
			if (variables[i] != null && !position.containsKey(variables[i])) {
				position.put(variables[i], unique);
				unique++;
			}
		}

		this.searchVariables = (T[]) new Var[unique];
		
		for (Iterator<Map.Entry<T, Integer>> itr = position.entrySet()
				.iterator(); itr.hasNext();) {
			Map.Entry<T, Integer> e = itr.next();
			searchVariables[e.getValue()] = e.getKey();
		}

		valueOrdering = indomain;

		currentIndex = new TimeStamp<Integer>(store, 0);
	}


	/**
	 * It returns the variable which is the base on the next choice point. Only
	 * if choice is of an X = C type. This function returns null if all
	 * variables have a value assigned or a choice point based on other type of
	 * constraint is being selected. The parameter index is the last variable which
	 * have been return by this SelectChoicePoint object which has not been
	 * backtracked upon yet.
	 */

	public T getChoiceVariable(int index) {

		assert (index < searchVariables.length);

		int finalIndex = searchVariables.length;
		
		for (int i = currentIndex.value(); i < finalIndex; i++)
			if (!searchVariables[i].singleton()) {
				currentIndex.update(i);
				return searchVariables[i];
			}
		
		return null;

	}

	/**
	 * It returns a value which is the base of the next choice point. Only if
	 * choice is of an X = C type.
	 */

	public int getChoiceValue() {

		assert (currentIndex.value() >= 0);
		assert (currentIndex.value() < searchVariables.length);
		assert (searchVariables[currentIndex.value()].dom() != null);
		
		return valueOrdering.indomain(searchVariables[currentIndex.value()]);

	}

	/**
	 * It always returns null as choice point is obtained by getChoiceVariable
	 * and getChoiceValue.
	 */

	public PrimitiveConstraint getChoiceConstraint(int index) {

		return null;

	}

	/**
	 * It returns the variables for which assignment in the solution is given.
	 */

	public IdentityHashMap<T, Integer> getVariablesMapping() {

		return position;

	}

	/**
	 * It returns the current index. Supplying this value in the next invocation
	 * of select will make search for next variable faster without comprimising
	 * efficiency.
	 */

	public int getIndex() {
		return currentIndex.value();
	}

}
