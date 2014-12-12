/**
 *  IntVar.java 
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
 * Defines a Finite Domain Variable (FDV) and related operations on it.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class IntVar extends Var {

	/**
	 * It stores pointer to a current domain, which has stamp equal to store
	 * stamp.
	 */
	public IntDomain domain;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */		
	public static String[] xmlAttributes = {"store", "id", "domain"};
	
	/**
	 * It creates a variable in a given store, with a given name and 
	 * a given domain.
	 * @param store store in which the variable is created.
	 * @param name the name for the variable being created.
	 * @param dom the domain of the variable being created.
	 */
	public IntVar(Store store, String name, IntDomain dom) {

		commonInitialization(store, name, dom);
		
	}

	private void commonInitialization(Store store, String name, IntDomain dom) {

		dom.searchConstraints = new ArrayList<Constraint>();
		dom.modelConstraints = new Constraint[IntDomain.eventsInclusion.length][];
		dom.modelConstraintsToEvaluate = new int[IntDomain.eventsInclusion.length];

		assert (name.lastIndexOf(" ") == -1) : "Name can not contain space character";
		
		id = name;
		domain = dom;
		domain.stamp = 0;
		index = store.putVariable(this);
		this.store = store;

	}

	/**
	 * It creates a variable in a given store, with a given name and 
	 * a given domain.
	 * @param store store in which the variable is created.
	 * @param dom the domain of the variable being created.
	 */
	public IntVar(Store store, IntDomain dom) {
		this(store, store.getVariableIdPrefix() + idNumber++, dom);
	}

	/**
	 * No parameter, explicit, empty constructor for subclasses.
	 */
	public IntVar() {
	}

	/**
	 * This constructor creates a variable with empty domain (standard
	 * IntervalDomain domain), automatically generated name, and empty attached
	 * constraint list.
	 * @param store store in which the variable is created.
	 */
	public IntVar(Store store) {
		this(store, store.getVariableIdPrefix() + idNumber++,
				new IntervalDomain(5));
	}

	/**
	 * This constructor creates a variable with a domain between min..max, 
	 * automatically generated name, and empty attached constraint list.
	 * @param store store in which the variable is created.
	 * @param min the minimum value of the domain.
	 * @param max the maximum value of the domain.
	 */
	public IntVar(Store store, int min, int max) {
		this(store, store.getVariableIdPrefix() + idNumber++, min, max);
	}

	/**
	 * This constructor creates a variable with an empty domain (standard
	 * IntervalDomain domain), the specified name, and an empty attached
	 * constraint list. 
	 * 
	 * @param store store in which the variable is created.
	 * @param name the name for the variable being created.
	 */
	public IntVar(Store store, String name) {
		this(store, name, new IntervalDomain(5));
	}
	
	/**
	 * This constructor creates a variable in a given store, with 
	 * the domain specified by min..max and with the given name.
	 * @param store the store in which the variable is created.
	 * @param name the name of the variable being created.
	 * @param min the minimum value of the variables domain.
	 * @param max the maximum value of the variables domain.
	 */
	public IntVar(Store store, String name, int min, int max) {
		
		if (max - min > 63)
			commonInitialization(store, name, new IntervalDomain(min, max));
		else
			commonInitialization(store, name, new SmallDenseDomain(min, max));

	}


	/**
	 * It is possible to add the domain of variable. It should be used with
	 * care, only right after variable was created and before it is used in
	 * constraints or search. Current implementation requires domains being
	 * added in the increasing order (e.g. 1..5 before 9..10).
	 * @param min the left bound of the interval being added.
	 * @param max the right bound of the interval being added.
	 */

	public void addDom(int min, int max) {
		domain.unionAdapt(min, max);
	}

	/**
	 * It is possible to set the domain of variable. It should be used with
	 * care, only right after variable was created and before it is used in
	 * constraints or search.
	 * @param min the left bound of the interval used to set this variable domain to.
	 * @param max the right bound of the interval used to set this variable domain to.
	 */

	public void setDomain(int min, int max) {
		domain.setDomain(min, max);
	}

	/**
	 * This function returns current value in the domain of the variable. If
	 * current domain of variable is not singleton then warning is printed and
	 * minimal value is returned.
	 * @return the value to which the variable has been grounded to.
	 */

	public int value() {
				
		assert singleton() : "Request for a value of not grounded variable " + this;

		// if (!singleton())
		//	Thread.dumpStack();
				
		return domain.min();
	}
	
	/**
	 * It checks if the domain contains only one value equal to c.
	 * @param val value to which we compare the singleton of the variable.
	 * @return true if a variable domain is singleton and it is equal to the specified value.
	 */

	public boolean singleton(int val) {
		return domain.singleton(val);
	}

	/**
	 * This function returns current maximal value in the domain of the
	 * variable.
	 * @return the maximum value belonging to the domain.
	 */

	public int max() {
		return domain.max();
	}

	/**
	 * This function returns current minimal value in the domain of the
	 * variable.
	 * @return the minimum value beloning to the domain. 
	 */
	public int min() {
		return domain.min();
	}


	/**
	 * It is possible to set the domain of variable. It should be used with
	 * care, only right after variable was created and before it is used in
	 * constraints or search.
	 * @param dom domain to which the current variable domain is set to. 
	 */

	public void setDomain(IntDomain dom) {
		domain.setDomain(dom);
	}

    /**
	 * It is possible to add the domain of variable. It should be used with
	 * care, only right after variable was created and before it is used in
	 * constraints or search.
	 * @param dom the added domain. 
	 */

	public void addDom(IntDomain dom) {
		domain.addDom(dom);
	}

	/**
	 * This function returns current domain of the variable.
	 * @return the domain of the variable.
	 */

	public IntDomain dom() {
		return domain;
	}

	/**
	 * It checks if the domains of variables are equal.
	 * @param var the variable to which current variable is compared to.
	 * @return true if both variables have the same domain.
	 */
	public boolean eq(IntVar var) {
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
	 * It registers constraint with current variable, so anytime this variable
	 * is changed the constraint is reevaluated. Pruning events constants from 0
	 * to n, where n is the strongest pruning event.
	 * @param c the constraint which is being attached to the variable.
	 * @param pruningEvent type of the event which must occur to trigger the execution of the consistency function.
	 */

	public void putModelConstraint(Constraint c, int pruningEvent) {

		// If variable is a singleton then it will not be put in the model.
		// It will be put in the queue and evaluated only once in the queue. 
		// If constraint is consistent for a singleton then it will remain 
		// consistent from the point of view of this variable.
		if (singleton())
			return;

		// if Event is NONE then constraint is not being attached, it will 
		// be only evaluated once, as after imposition it is being put in the constraint 
		// queue.
		
		if (pruningEvent == Domain.NONE) {
			return;
		}

		domain.putModelConstraint(store.level, this, c, pruningEvent);

		store.recordChange(this);

	}

	/**
	 * It registers constraint with current variable, so always when this variable
	 * is changed the constraint is reevaluated.
	 * @param c the constraint which is added as a search constraint. 
	 */

	public void putSearchConstraint(Constraint c) {

		if (singleton())
			return;

		domain.putSearchConstraint(store.level, this, c);

		store.recordChange(this);

	}

	/**
	 * It returns the values which have been removed at current store level. It does
	 * _not_ return the recent pruning in between the calls to that function.
	 * @return difference between the current level and the one before it.
	 */
	public IntDomain recentDomainPruning() {

		return domain.recentDomainPruning(store.level);

	}

	/**
	 * It detaches constraint from the current variable, so change in variable
	 * will not cause constraint reevaluation. It is only removed from the 
	 * current level onwards. Removing current level at later stage will 
	 * automatically re-attached the constraint to the variable. 
	 * 
	 * @param c the constraint being detached from the variable.
	 */

	public void removeConstraint(Constraint c) {

		if (singleton())
			return;

		int i = domain.searchConstraintsToEvaluate - 1;
		for (; i >= 0; i--)
			if (domain.searchConstraints.get(i) == c)
				domain.removeSearchConstraint(store.level, this, i, c);

		if (i == -1)
			domain.removeModelConstraint(store.level, this, c);

		store.recordChange(this);

	}

	/**
	 * It checks if the domain contains only one value.
	 * @return true if the variable domain is a singleton, false otherwise.
	 */

	public boolean singleton() {
		return domain.singleton();
	}


	/**
	 * It returns current number of constraints which are associated with
	 * variable and are not yet satisfied.
	 * @return number of constraints attached to the variable.
	 */
	public int sizeConstraints() {
		return domain.sizeConstraints();
	}

	/**
	 * It returns all constraints which are associated with variable, even the
	 * ones which are already satisfied.
	 * @return number of constraints attached at the earliest level of the variable.
	 */
	public int sizeConstraintsOriginal() {
		return domain.sizeConstraintsOriginal();
	}

	/**
	 * It returns current number of constraints which are associated with
	 * variable and are not yet satisfied.
	 * @return number of attached search constraints.
	 */
	public int sizeSearchConstraints() {
		return domain.searchConstraintsToEvaluate;
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

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer(id);
		
		if (domain.singleton())
			result.append(" = ");
		else
			result.append("::");
			
		result.append(domain);
		return result.toString();
		
	}

	/**
	 * It returns the string representation of the variable using the full representation
	 * of the domain. 
	 * @return string representation.
	 */
	public String toStringFull() {
		
		StringBuffer result = new StringBuffer(id);
		result.append(domain.toStringFull());
		return result.toString();
		
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
