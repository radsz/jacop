/**
 *  Variable.java 
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

import org.jacop.constraints.Constraint;

/**
 * Defines a variable and related operations on it.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public abstract class Var implements Backtrackable {

	
	public boolean trace = SwitchesPruningLogging.traceVar;

	/**
	 * It is a counter to indicate number of created variables.
	 */
	public static int idNumber = 0;

	/**
	 * Id string of the variable.
	 */
	public String id;

	/**
	 * It specifies the index at which it is stored in Store. 
	 */
	
	public int index = -1;

	/**
	 * It specifies the current weight of the variable.
	 */
	
	public int weight = 1;
	
	/**
	 * Each variable is created in a store. This attribute represents the store
	 * in which this variable was created.
	 */
	public Store store;

	/**
	 * This function returns current domain of the variable.
	 * @return the domain of the variable.
	 */

	public abstract Domain dom();


	/**
	 * It returns the size of the current domain.
	 * @return the size of the variables domain.
	 */

	public abstract int getSize();


	/**
	 * It checks if the domain is empty.
	 * @return true if variable domain is empty.
	 */

	public abstract boolean isEmpty();


	/**
	 * It registers constraint with current variable, so anytime this variable
	 * is changed the constraint is reevaluated. Pruning events constants from 0
	 * to n, where n is the strongest pruning event.
	 * @param c the constraint which is being attached to the variable.
	 * @param pruningEvent type of the event which must occur to trigger the execution of the consistency function.
	 */

	public abstract void putModelConstraint(Constraint c, int pruningEvent);
	
	/**
	 * It registers constraint with current variable, so always when this variable
	 * is changed the constraint is reevaluated.
	 * @param c the constraint which is added as a search constraint. 
	 */

	public abstract void putSearchConstraint(Constraint c);
		
	/**
	 * It detaches constraint from the current variable, so change in variable
	 * will not cause constraint reevaluation. It is only removed from the 
	 * current level onwards. Removing current level at later stage will 
	 * automatically re-attached the constraint to the variable. 
	 * 
	 * @param c the constraint being detached from the variable.
	 */

	public abstract void removeConstraint(Constraint c);
	
	/**
	 * It checks if the domain contains only one value.
	 * @return true if the variable domain is a singleton, false otherwise.
	 */

	public abstract boolean singleton();


	/**
	 * It returns current number of constraints which are associated with
	 * variable and are not yet satisfied.
	 * @return number of constraints attached to the variable.
	 */
	public abstract int sizeConstraints();

	/**
	 * It returns all constraints which are associated with variable, even the
	 * ones which are already satisfied.
	 * @return number of constraints attached at the earliest level of the variable.
	 */
	public abstract int sizeConstraintsOriginal();

	/**
	 * It returns current number of constraints which are associated with
	 * variable and are not yet satisfied.
	 * @return number of attached search constraints.
	 */
	public abstract int sizeSearchConstraints();

	/**
	 * This function returns stamp of the current domain of variable. It is
	 * equal or smaller to the stamp of store. Larger difference indicates that
	 * variable has been changed for a longer time.
	 * @return level for which the most recent changes have been applied to.
	 */

	public abstract int level();
	
	/**
	 * It returns the string representation of the variable using the full representation
	 * of the domain. 
	 * @return string representation.
	 */
	public abstract String toStringFull();

	/**
	 * It informs the variable that its variable has changed according to the specified event.
	 * @param event the type of the change (GROUND, BOUND, ANY).
	 */
	public abstract void domainHasChanged(int event);

	/**
	 * It registers constraint with current variable, so anytime this variable
	 * is changed the constraint is reevaluated.
	 * @param c the constraint being attached to this variable.
	 */

	public abstract void putConstraint(Constraint c);

	/**
	 * This function returns variable id.
	 * @return the id of the variable.
	 */
	public String id() {
		return id;
	}

	/**
	 * This function returns the index of variable in store array.
	 * @return the index of the variable. 
	 */
	public int index() {
		return index;
	}

}
