/**
 *  BooleanVariable.java 
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
 * Defines a variable and related operations on it.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class BooleanVar extends IntVar {

	/**
	 * No parameter, explicit, empty constructor for subclasses.
	 */
	public BooleanVar() {
	}

	/**
	 * This constructor creates a variable with empty domain (standard FD
	 * domain), automatically generated name, and empty attached constraint
	 * list.
	 * @param store It specifies the store in which boolean variable should be created.
	 */
	public BooleanVar(final Store store) {
		this(store, store.getVariableIdPrefix() + idNumber++,
				new BoundDomain(0, 1));
	}

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */		
	public static String[] xmlAttributes = {"store", "id", "min", "max"};

	/**
	 * Boolean variable constructor. 
	 * @param store It specifies the store in which boolean variable should be created.
	 * @param name It specifies the id of the variable.
	 */
	public BooleanVar(Store store, String name) {
		this(store, name, new BoundDomain(0, 1));

	}

	/**
	 * Boolean variable constructor. 
	 * @param store It specifies the store in which boolean variable should be created.
	 * @param name It specifies the id of the variable.
	 * @param min it specifies the minimum value, which must be greater or equal 0.  
	 * @param max it specifies the maximum value, which must be smaller or equal 1.
	 */
	public BooleanVar(Store store, String name, int min, int max) {
		this(store, name, new BoundDomain(min, max));
	}

	/**
	 * It creates a Boolean variable. 
	 * 
	 * @param store It specifies the store in which boolean variable should be created.
	 * @param dom It specifies the domain of the boolean variable.
	 */
	public BooleanVar(Store store, BoundDomain dom) {
		this(store, store.getVariableIdPrefix() + idNumber++, dom);
	}

	/**
	 * It creates a Boolean variable. 
	 * 
	 * @param store the store in which the variable is being created.
	 * @param name the name of the created variable.
	 * @param dom the domain specifying the domain of the variable.
	 */
	// @FIXME, constructor uses an argument without copying, (dom)
	// it will cause problems if dom is reused.
 	public BooleanVar(Store store, String name, BoundDomain dom) {

		assert (dom.min >= 0 && dom.min <= dom.max && dom.max <= 1) : "Boolean variable can only get value between 0..1";

		dom.searchConstraints = new ArrayList<Constraint>();
		dom.modelConstraints = new Constraint[3][];
		dom.modelConstraintsToEvaluate = new int[3];
		dom.modelConstraintsToEvaluate[0] = 0;
		dom.modelConstraintsToEvaluate[1] = 0;
		dom.modelConstraintsToEvaluate[2] = 0;
		id = name;
		domain = dom;
		domain.stamp = 0;
		this.store = store;
		// the return code is ignored as the variable is not stored within store.vars; 
		store.putVariable(this);

		if (store.pointer4GroundedBooleanVariables == null) {
			store.pointer4GroundedBooleanVariables = new TimeStamp<Integer>(store, 0);
			// Boolean Time stamp will be updated manually by store.
			store.timeStamps.remove(store.pointer4GroundedBooleanVariables);
			store.changeHistory4BooleanVariables = new BooleanVar[100];
		}

	}

	/**
	 * It registers constraint with current variable, so anytime this variable
	 * is changed the constraint is reevaluated. Pruning event is ignored as all
	 * are evaluated with GROUND event, since any change to Boolean Variable
	 * makes it ground.
	 * @param constraint - constraint being attached to a variable.
	 * @param pruningEvent - Only NONE and GROUND events are considered. By default GROUND event is used.
	 * 
	 */
	@Override
	public void putModelConstraint(Constraint constraint, int pruningEvent) {

		if (singleton())
			return;

		if (pruningEvent == Domain.NONE) {
			return;
		}

		domain.putModelConstraint(store.level, this, constraint, IntDomain.GROUND);

		store.recordBooleanChange(this);

	}

	/**
	 * It registers constraint with current variable, so anytime this variable
	 * is changed the constraint is reevaluated.
	 * @param constraint It specifies the constraint which is being added. 
	 */
	@Override
	public void putSearchConstraint(Constraint constraint) {

		if (singleton())
			return;

		domain.putSearchConstraint(store.level, this, constraint);
		store.recordBooleanChange(this);

	}

	/**
	 * It unregisters constraint with current variable, so change in variable
	 * will not cause constraint reevaluation.
	 * @param constraint it specifies the constraint which is no longer attached to a variable.
	 */
	@Override
	public void removeConstraint(Constraint constraint) {

		if (singleton())
			return;

		int i = domain.searchConstraintsToEvaluate - 1;
		for (; i >= 0; i--)
			if (domain.searchConstraints.get(i) == constraint)
				domain.removeSearchConstraint(store.level, this, i, constraint);

		if (i == -1)
			domain.removeModelConstraint(store.level, this, constraint);

		store.recordBooleanChange(this);

	}

	/**
	 * It returns current number of constraints which are associated with
	 * variable and are not yet satisfied.
	 * @return the number of constraints currently attached to this variable.
	 */
	@Override
	public int sizeConstraints() {
		return domain.sizeConstraints();
	}

	/**
	 * It returns all constraints which are associated with variable, even the
	 * ones which are already satisfied.
	 * @return the number of constraints originally attached to this variable.
	 */
	@Override
	public int sizeConstraintsOriginal() {
		return domain.sizeConstraintsOriginal();
	}

	/**
	 * It returns current number of constraints which are associated with
	 * a boolean variable and are not yet satisfied.
	 * @return the number of constraints.
	 */
	@Override
	public int sizeSearchConstraints() {
		return domain.searchConstraintsToEvaluate;
	}

	/**
	 * @return it returns the string description of the boolean variable.
	 * 
	 */
	@Override
	public String toString() {
		if (domain.singleton())
			return id + "=" + domain;
		else
			return id + "::" + domain;		
	}

	/**
	 * @return It returns elaborate string description of the boolean variable and all the components of its domain. 
	 * 
	 */
	@Override
	public String toStringFull() {
		return id + domain.toStringFull();
	}

    /**
	 * It is possible to add the domain of variable. It should be used with
	 * care, only right after variable was created and before it is used in
	 * constraints or search.
	 * @param dom the added domain. 
	 */

	public void addDom(Domain dom) {
		
		domain.addDom((IntDomain)dom);
		
	}

	/**
	 * This function returns current domain of the variable.
	 * @return the domain of the variable.
	 */

	public BoundDomain dom() {
		return (BoundDomain)domain;
	}

	/**
	 * It checks if the domains of variables are equal.
	 * @param var the variable to which current variable is compared to.
	 * @return true if both variables have the same domain.
	 */
	public boolean eq(BooleanVar var) {
		return domain.eq(var.dom());
	}

	/**
	 * It returns the size of the current domain.
	 * @return the size of the variables domain.
	 */

	public int getSize() {
		return domain.getSize();
	}


	/**
	 * It checks if the domain is empty.
	 * @return true if variable domain is empty.
	 */

	public boolean isEmpty() {
		return domain.isEmpty();
	}



	/**
	 * It returns the values which have been removed at current store level. It does
	 * _not_ return the recent pruning in between the calls to that function.
	 * @return difference between the current level and the one before it.
	 */
	public BoundDomain recentDomainPruning() {

		return (BoundDomain)domain.recentDomainPruning(store.level);

	}


	/**
	 * It checks if the domain contains only one value.
	 * @return true if the variable domain is a singleton, false otherwise.
	 */

	public boolean singleton() {
		return domain.singleton();
	}



	/**
	 * This function returns stamp of the current domain of variable. It is
	 * equal or smaller to the stamp of store. Larger difference indicates that
	 * variable has been changed for a longer time.
	 * @return level for which the most recent changes have been applied to.
	 */

	public int level() {
		return domain.stamp;
	}

	public void remove(int removedLevel) {
		domain.removeLevel(removedLevel, this);
	}

	/**
	 * It informs the variable that its variable has changed according to the specified event.
	 * @param event the type of the change (GROUND, BOUND, ANY).
	 */
	public void domainHasChanged(int event) {
				
		assert ((event == IntDomain.ANY && !singleton()) || 
				(event == IntDomain.BOUND && !singleton()) ||
				(event == IntDomain.GROUND && singleton())) : "Wrong event generated";
		
		store.addChanged(this, event, Integer.MIN_VALUE);

	}

	public void putConstraint(Constraint c) {
		putModelConstraint(c, IntDomain.ANY);
	}
	
}
