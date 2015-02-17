/**
 *  SelectChoicePoint.java 
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

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Var;

/**
 * Defines an interface for defining different methods for selecting next search
 * decision to be taken. The search decision called choice point will be first
 * enforced and later upon backtrack a negation of that search decision will be
 * enforced.
 * 
 * @author Radoslaw Szymanek and Radoslaw Szymanek
 * @version 4.2
 * @param <T> type of the variable for which choice point is being created.
 */

public interface SelectChoicePoint<T extends Var> {

	/**
	 * It returns the variable which is the base on the next choice point. Only
	 * if choice is of an X = C type. This function returns null if all
	 * variables have a value assigned or a choice point based on other type of
	 * constraint is being selected. The parameter index is the last variable which
	 * have been return by this SelectChoicePoint object which has not been
	 * backtracked upon yet.
	 * @param index the position of the last variable in selection choice point heuristic.
	 * @return variable based on which the choice needs to be created.
	 */

	public T getChoiceVariable(int index);

	/**
	 * It returns a value which is the base of the next choice point. Only if
	 * choice is of an getChoiceVariable() = getChoiceValue() type.
	 * @return value used in the choice point (value).
	 */

	public int getChoiceValue();

	/**
	 * It returns the constraint which is the base of the choice point. If the
	 * return value is equal to null and choice point is also not based on X = C
	 * type of constraint then all variables have been assigned a value.
	 * @param index the position of the last variable returned by selection choice point heuristic.
	 * @return primitive constraint which is a base of a choice point.
	 */

	public PrimitiveConstraint getChoiceConstraint(int index);

	/**
	 * It specifies the position of variables as given when variables of this
	 * select object were supplied.
	 * @return mapping of variables to the positions in the variables array.
	 */

	public IdentityHashMap<T, Integer> getVariablesMapping();

	/**
	 * It returns the current index. Supplying this value in the next invocation
	 * of select will make search for next variable faster without compromising
	 * efficiency.
	 * @return internal position of the last variable chosen to be the base of the choice point. 
	 */

	public int getIndex();

}
