/**
 *  Constraint.java
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

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Hashtable;

import org.jacop.core.Store;
import org.jacop.core.SwitchesPruningLogging;
import org.jacop.core.Var;

/**
 * Standard unified interface/abstract class for all constraints.
 *
 * Defines how to construct a constraint, impose, check satisfiability,
 * notSatisfiability, enforce consistency.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 3.1
 */

public abstract class Constraint extends DecomposedConstraint {

	public boolean trace = SwitchesPruningLogging.traceConstraint;
	
	/**
	 * It specifies the number id for a given constraint. All constraints
	 * within the same type have unique number ids.
	 */
	public int numberId;

	/**
	 * It specifies the string id of the constraint. If it is null then 
	 * the string id is created from string associated for the constraint
	 * type and the numberId of the constraint.
	 */
	public String id;

	/**
	 * It returns the variables in a scope of the constraint.
	 * @return variables in a scope of the constraint.
	 */
	public abstract ArrayList<Var> arguments();

	/**
	 * This function is called in case of the backtrack, so a constraint can
	 * clear the queue of changed variables which is no longer valid. This
	 * function is called *before* all timestamps, variables, mutablevariables
	 * have reverted to their previous value.
	 * @param level the level which is being removed.
	 */
	public void removeLevel(int level) {
	}

	/**
	 * This function is called in case of the backtrack. It is called
	 * after all timestamps, variables, mutablevariables have reverted
	 * to their values *after* removing the level.
	 * @param level the level which is being removed.
	 */
	public void removeLevelLate(int level) {
	}


	/**
	 * It is a (most probably incomplete) consistency function which removes the
	 * values from variables domains. Only values which do not have any support
	 * in a solution space are removed.
	 * @param store constraint store within which the constraint consistency is being checked.
	 */
	public abstract void consistency(Store store);

	/**
	 * It retrieves the pruning event which causes reevaluation of the
	 * constraint.
	 * 
	 * @param var variable for which pruning event is retrieved
	 * @return it returns the int code of the pruning event (GROUND, BOUND, ANY, NONE)
	 */

	public abstract int getConsistencyPruningEvent(Var var);

	/**
	 * It gives the id string of a constraint.
	 * @return string id of the constraint.
	 */
	public String id() {
		if (id != null)
			return id;
		else
			return this.getClass().getSimpleName() + numberId;
	}

	/**
	 * It imposes the constraint in a given store.
	 * @param store the constraint store to which the constraint is imposed to.
	 */
	public abstract void impose(Store store);

	/**
	 * It imposes the constraint and adjusts the queue index.
	 * @param store the constraint store to which the constraint is imposed to.
	 * @param queueIndex the index of the queue in the store it is assigned to.
	 */
	public void impose(Store store, int queueIndex) {

		assert ( queueIndex < store.queueNo ) : "Constraint queue number larger than permitted by store.";

		this.queueIndex = queueIndex;

		impose(store);

	}

	/**
	 * This is a function called to indicate which variable in a scope of
	 * constraint has changed. It also indicates a store level at which the
	 * change has occurred.
	 * @param level the level of the store at which the change has occurred.
	 * @param var variable which has changed.
	 */
	public void queueVariable(final int level, final Var var) {
	}

	/**
	 * It removes the constraint by removing this constraint from all variables.
	 */
	public abstract void removeConstraint();

	/**
	 * It checks if the constraint is satisfied. If this function is incorrectly
	 * implemented a constraint may not be satisfied in a solution.
	 * @return true if the constraint is for certain satisfied, false otherwise.
	 */
	public abstract boolean satisfied();

	/**
	 * It produces a string representation of a constraint state.
	 */
	@Override
	public abstract String toString();

	/**
	 * It specifies a constraint which if imposed by search will enhance
	 * propagation of this constraint.
	 * @return Constraint enhancing propagation of this constraint.
	 */
	public Constraint getGuideConstraint() {
		return null;
	}

	/**
	 * This function provides a variable which assigned a value returned
	 * by will enhance propagation of this constraint.
	 * @return Variable which is a base of enhancing constraint.
	 */
	public Var getGuideVariable() {
		return null;
	}

	/**
	 * This function provides a value which if assigned to a variable returned
	 * by getGuideVariable() will enhance propagation of this constraint.
	 * @return Value which is a base of enhancing constraint.
	 */
	public int getGuideValue() {
		return Integer.MAX_VALUE;
	}

	/**
	 * This function allows to provide a guide feedback. If constraint does
	 * not propose sufficiently good enhancing constraints it will be informed
	 * so it has a chance to reexamine its efforts.
	 * @param feedback true if the guide was useful, false otherwise.
	 */
	public void supplyGuideFeedback(boolean feedback) {
	}

	/**
	 * It increases the weight of the variables in the constraint scope.
	 *
	 */

	public abstract void increaseWeight();


	/**
	 * It allows to customize the event for a given variable which 
	 * causes the re-execution of the consistency method for a constraint.
	 * 
	 * @param var variable for which the events are customized.
	 * @param pruningEvent the event which must occur to trigger execution of the consistency method.
	 */
	public void setConsistencyPruningEvent(final Var var, final int pruningEvent) {

		if (consistencyPruningEvents == null)
			consistencyPruningEvents = new Hashtable<Var, Integer>();
		consistencyPruningEvents.put(var, pruningEvent);

	}


	/**
	 * It returns the number of variables within a constraint scope.
	 * @return number of variables in the constraint scope.
	 */
	public int numberArgs() {
		return numberArgs;
	}

	/**
	 * It specifies if the constraint allows domains of variables 
	 * in its scope only to shrink its domain with the progress
	 * of search downwards.
	 * 
	 * @return true, by default by all constraints. 
	 */
	public boolean requiresMonotonicity() {
		return true;
	}

	/**
	 * It specifies if upon the failure of the constraint, all variables
	 * in the constraint scope should have their weight increased.
	 */
	public boolean increaseWeight = true;

	/**
	 * It specifies the number of variables in the constraint scope.
	 */
	public int numberArgs;

	/**
	 * It specifies the event which must occur in order for the consistency function to 
	 * be called.
	 */
	public Hashtable<Var, Integer> consistencyPruningEvents;

	/**
	 * It specifies if the constraint consistency function can be prematurely terminated
	 * through other than FailureException exception.
	 */
	public boolean earlyTerminationOK = false;

	/**
	 * It specifies if the constraint consistency function requires consistency function 
	 * executed in one atomic step. A constraint can specify that if any other pruning
	 * events are initiated by outside entity then the constraint may not work correctly
	 * if the execution is continued, but it will work well if consistency() function is 
	 * restarted.
	 */
	public boolean atomicExecution = true;

	/**
	 * It imposes the decomposition of the given constraint in a given store.
	 * @param store the constraint store to which the constraint is imposed to.
	 */
	@Override
	public void imposeDecomposition(Store store) {
		throw new UnsupportedOperationException();
	};

	/**
	 * It returns an array list of constraint which are used to decompose this 
	 * constraint. It actually creates a decomposition (possibly also creating
	 * variables), but it does not impose the constraint.
	 * @param store the constraint store in which context the decomposition takes place.
	 * @return an array list of constraints used to decompose this constraint.
	 */
	@Override
	public ArrayList<Constraint> decompose(final Store store) {
		throw new UnsupportedOperationException();
	}

	/**
	 * It is executed after the constraint has failed. It allows to clean some 
	 * data structures. 
	 */
	public void cleanAfterFailure() {
	};	


    /**
     * Methods that check for overflow/underflow 
     */

    int add(int a, int b) {  
		
	long cc = (long)a + (long)b;

	if ( cc < Integer.MIN_VALUE || cc > Integer.MAX_VALUE)
	    throw new ArithmeticException("Overflow occurred from int " + a + " + " + b);  
		
	return a + b;  
		
    } 
	

    int subtract(int a, int b) {  
		
	long cc = (long)a - (long)b;
		
	if ( cc < Integer.MIN_VALUE || cc > Integer.MAX_VALUE)
	    throw new ArithmeticException("Overflow occurred from int " + a + " - " + b);  
		
	return a - b;  
		
    } 

	int toInt(final float f) {
		
		if (f >= (float) Integer.MIN_VALUE && f <= (float) Integer.MAX_VALUE) {
			return (int) f;
		} else {
			throw new ArithmeticException("Overflow occurred " + f);
		}
		
	}

}
