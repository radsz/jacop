/**
 *  Domain.java 
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

import java.util.ArrayList;

import org.jacop.constraints.Constraint;

/**
 * Defines a Domain and related operations on it.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public abstract class Domain {

	/**
	 * It specifies the constant responsible of conveying a message that
	 * no information is provided by the domain when describing the change
	 * which has occurred within the domain.
	 */
	public final static int NOINFO = Integer.MIN_VALUE;
	
	/**
	 * It specifies the constant for NONE event, if event is NONE then
	 * the constraint is not attached to a variable. Useful for constraints
	 * which are always satisfied or not satisfied after the first 
	 * consistency function execution.
	 */
	public final static int NONE = -1;
	
	/**
	 * An exception used if failure encountered in functions in();
	 */

	public static final FailException failException = new FailException();

	/**
	 * It specifies constraints which are attached to current domain, each array
	 * has different pruning event.
	 */

	public Constraint modelConstraints[][];

	/**
	 * It specifies the first position of a constraint which is satisfied. All
	 * constraints at earlier positions are not satisfied yet.
	 */

	public int[] modelConstraintsToEvaluate;
		
	/**
	 * It specifies constraints which are attached to current domain.
	 */

	public ArrayList<Constraint> searchConstraints;

	/**
	 * It specifies if the vector of constraints were cloned (if it was not
	 * cloned then the same vector is reused across domains with different
	 * stamps. Only reading actions are allowed on not cloned vector of
	 * constraints.
	 */

	public boolean searchConstraintsCloned;

	/**
	 * It specifies the position of the last constraint which is still not yet
	 * satisfied.
	 */

	public int searchConstraintsToEvaluate;

	/**
	 * It specifies the level of this domain, which specifies at which store
	 * level it was created and used. The domain is only valid (used) at a store
	 * level equal domain stamp.
	 */
	// TODO: change stamp name to level in ALL places, e.g. setStamp(int) too.
	public int stamp;

	/**
	 * It removes all elements.
	 */

	public abstract void clear();

	/**
	 * It clones the domain object, only data responsible for encoding domain
	 * values is cloned. All other fields must be set separately.
	 * @return return a clone of the domain. It aims at getting domain of the proper class type. 
	 */

	public abstract Domain cloneLight();

	/**
	 * It clones the domain object.
	 */
	
	public abstract Domain clone();
	
	/**
	 * It returns value enumeration of the domain values.
	 * @return valueEnumeration which can be used to enumerate one by one value from this domain.
	 */

	public abstract ValueEnumeration valueEnumeration();

	/**
	 * It returns the size of the domain.
	 * @return number of elements in this domain.
	 */

	public abstract int getSize();

	/**
	 * It returns true if given domain is empty.
	 * @return true if the given domain is empty.
	 */

	public abstract boolean isEmpty();

	/**
	 * It removes a constraint from a domain, it should only be called by
	 * removeConstraint function of Variable object. It is called for example in a
	 * situation when a constraint is satisfied. 
	 * @param storeLevel specifies the current level of the store, from which it should be removed.
	 * @param var specifies variable for which the constraint is being removed.
	 * @param c the constraint which is being removed.
	 */

	public abstract void removeModelConstraint(int storeLevel, Var var, Constraint c);

	/**
	 * It removes a constraint from a domain, it should only be called by
	 * removeConstraint function of Variable object.
	 * @param storeLevel specifies the current level of the store, from which it should be removed.
	 * @param var specifies variable for which the constraint is being removed.
	 * @param position specifies the position of the removed constraint.
	 * @param c the constraint which is being removed.
	 */
	public abstract void removeSearchConstraint(int storeLevel, Var var, int position, Constraint c);

	/**
	 * @return it returns the array containing search constraints (the ones imposed after setting up the model).
	 */
	public ArrayList<Constraint> searchConstraints() {
		return searchConstraints;
	}

	/**
	 * It sets the stamp of the domain.
	 * 
	 * @param stamp defines the time stamp of the domain.
	 */

	public void setStamp(int stamp) {
		this.stamp = stamp;
	}

	/**
	 * It returns true if given domain has only one element.
	 * @return true if the domain contains only one element.
	 */
	public abstract boolean singleton();

	
	/**
	 * It returns true if given domain has only one element.
	 * @param value value represented as domain object to which the domain must be equal to.
	 * @return true if the domain contains only one element.
	 */
	public abstract boolean singleton(Domain value);

	/**
	 * It returns the number of constraints
	 * @return the number of constraints attached to this domain.
	 */

	public abstract int noConstraints();

	/**
	 * It returns number of search constraints.
	 * @return the number of search constraints.
	 */

	public int noSearchConstraints() {
		return searchConstraintsToEvaluate;
	}

	/**
	 * It returns the stamp of the domain.
	 * @return the level of the domain.
	 */
	public int stamp() {
		return stamp;
	}

	/**
	 * It returns string description of the domain (only values in the domain).
	 */

	public abstract String toString();

	/**
	 * It returns string description of the constraints attached to the domain.
	 * @return the string description.
	 */

	public abstract String toStringConstraints();

	/**
	 * It returns complete string description containing all relevant
	 * information about the domain.
	 * @return complete description of the domain.
	 */

	public abstract String toStringFull();


	/**
	 * It removes the specified level. This function may re-instantiate
	 * the old copy of the domain (previous value) or recover from changes done at stamp
	 * level to get the previous value at level lower at provided level.
	 * @param level the level which is being removed.
	 * @param var the variable to which this domain belonged to.
	 */

	public abstract void removeLevel(int level, Var var);

	/**
	 * It returns an unique identifier of the domain.
	 * @return it returns an integer id of the domain.
	 */

	public abstract int domainID();

	/**
	 * It specifies if the domain type is more suited to representing sparse
	 * domain.
	 * @return true if sparse, false otherwise.
	 */

	public abstract boolean isSparseRepresentation();

	/**
	 * It specifies if domain is a finite domain of numeric values (integers).
	 * @return true if domains contains numeric values.
	 */

	public abstract boolean isNumeric();

	/**
	 * It adds a constraint to a domain, it should only be called by
	 * putConstraint function of Variable object. putConstraint function from
	 * Variable must make a copy of a list of model constraints if vector was not
	 * cloned.
	 * @param storeLevel the level at which the model constraint is to be added.
	 * @param var variable to which the constraint is attached to.
	 * @param C the constraint which is being attached to a variable.
	 * @param pruningEvent the type of the prunning event required to check the consistency of the attached constraint.
	 */

	public abstract void putModelConstraint(int storeLevel, Var var,
			Constraint C, int pruningEvent);

	/**
	 * It adds a constraint to a domain, it should only be called by
	 * putConstraint function of Variable object. putConstraint function from
	 * Variable must make a copy of a list of search constraints if vector was not
	 * cloned.
	 * @param storeLevel the level at which the search constraint is to be added.
	 * @param var variable to which the constraint is attached to.
	 * @param C the constraint which is being attached to a variable.
		 */

	public abstract void putSearchConstraint(int storeLevel, Var var,
			Constraint C);

	/**
	 * It returns the values which have been removed at current store level.
	 * @param currentStoreLevel the current store level.
	 * @return emptyDomain if domain did not change at current level, or the set of values which have been removed at current level.
	 */

	// public abstract Domain recentDomainPruning(int currentStoreLevel);

	/**
	 * It returns all constraints which are associated with variable, even the
	 * ones which are already satisfied.
	 * @return the number of constraint attached to this domain. 
	 */

	public int sizeConstraints() {
		return (modelConstraintsToEvaluate[0] + 
				modelConstraintsToEvaluate[1] + 
				modelConstraintsToEvaluate[2]);
	}

	/**
	 * It returns all constraints which are associated with variable, even the
	 * ones which are already satisfied.
	 * @return the number of constraints attached to the original domain of the variable associated with this domain.
	 */
	public abstract int sizeConstraintsOriginal();	
	
	/**
	 * It returns all the constraints attached currently to the domain.
	 * It should not be used extensively.
	 * 
	 * @return an array of constraints currently attached to the domain.
	 */
	public ArrayList<Constraint> constraints() {

		ArrayList<Constraint> result = new ArrayList<Constraint>();

		result.addAll(searchConstraints);

		if (modelConstraints != null)
			for (int i = 0; i < modelConstraints.length; i++) {
				for (int j = modelConstraintsToEvaluate[i]; j >= 0; j--)
					if (modelConstraints[i] != null)
						if (j < modelConstraints[i].length)
							result.add(modelConstraints[i][j]);
			}

		return result;
		
	}

	
	/**
	 * It enforces that this domain is included within the specified domain. 
	 * 
	 * @param level store level at which this inclusion is enforced.
	 * @param var variable which is informed of the change if any occurs.
	 * @param domain the domain which restricts this domain. 
	 */
	public abstract void in(int level, Var var, Domain domain);

	
	/**
	 * It assigns a variable to a value represented by a domain. 
	 * 
	 * @param level store level at which this assignment occurs.
	 * @param var variable which is being assigned.
	 * @param singleton the value being used in the assignment. 
	 */
	// public abstract void inValue(int level, Var var, Domain singleton);

	/**
	 * It checks if the domain is equal to the supplied domain.
	 * @param domain against which the equivalence test is performed.
	 * @return true if suppled domain has the same elements as this domain. 
	 */

	// public abstract boolean eq(Domain domain);


	/**
	 * It adds values as specified by the parameter to the domain.
	 * @param domain Domain which needs to be added to the domain.
	 */

	// public abstract void addDom(Domain domain);


	/**
	 * It checks if the domain has correct state. 
	 * @return null if everything is ok, otherwise a string describing the problem. 
	 * 
	 */
	public abstract String checkInvariants();

	/**
	 * It specifies what events should be executed if a given event occurs.
	 * @param pruningEvent the pruning event for which we want to know what events it encompasses.
	 * @return an array specifying what events should be included given this event.
	 */
	public abstract int[] getEventsInclusion(int pruningEvent);

}
