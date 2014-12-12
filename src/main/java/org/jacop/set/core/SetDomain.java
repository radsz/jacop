/**
 *  SetDomain.java 
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

package org.jacop.set.core;

import java.util.ArrayList;
import java.util.Iterator;

import org.jacop.constraints.Constraint;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.Interval;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Defines a set interval determined by a least upper bound(lub) and a 
 * greatest lower bound(glb). The domain consist of zero, one or several sets.
 * 
 * 
 * @author Radoslaw Szymanek, Krzysztof Kuchcinski and Robert Åkemalm 
 * @version 4.2
 */

public abstract class SetDomain extends Domain {

	/**
	 * It specifies an unique ID for the domain. 
	 */
	public static final int SetDomainID = 3;

	/**
	 * It specifies event that Set variable became singleton. 
	 */
	public static final int GROUND = 0;

	/**
	 * It specifies event that GLB has grown.
	 */
	public static final int GLB = 1;

	/**
	 * It specifies event that LUB has shrank. 
	 */
	public static final int LUB = 2;

	/**
	 * Bound event. Both bounds have changed.
	 */
	public static final int BOUND = 3;
	
	/**
	 * Any event. 
	 */
	public static final int ANY = 4;

	/**
	 * It specifies event that has changed the cardinality of the set.
	 */
	public static final int CARDINALITY = 5;

	/**
	 * It specifies for each event what other events are subsumed by this
	 * event. Possibly implement this by bit flags in int. 
	 */
	public final static int[][] eventsInclusion = { {GROUND, GLB, LUB, BOUND, ANY, CARDINALITY}, // GROUND event 
											 		{GLB, BOUND, ANY, CARDINALITY}, // GLB event 
											 		{LUB, BOUND, ANY, CARDINALITY}, // LUB event
											 		{BOUND, ANY, CARDINALITY}, // BOUND event
											 		{ANY, CARDINALITY}, // ANY event
											 		{CARDINALITY}}; // CARDINALITY event

	/**
	 * It helps to specify what events should be executed if a given event occurs.
	 * @param pruningEvent the pruning event for which we want to know what events it encompasses.
	 * @return an array specifying what events should be included given this event.
	 */
	public int[] getEventsInclusion(int pruningEvent) {
		return eventsInclusion[pruningEvent];
	}

	/**
	 * It specifies the previous domain which was used by this domain. The old
	 * domain is stored here and can be easily restored if necessary.
	 */

	public SetDomain previousDomain;	


	/**
	 * It predefines empty domain so there is no need to constantly create it when
	 * needed.
	 */
	static public SetDomain emptyDomain = new BoundSetDomain();

	/**
	 * Adds an interval to the lub.
	 * @param i  The interval to be added to the lub.
	 */
	public abstract void addDom(Interval i);

	/**
	 * Adds a set of values to the set of possible values used within this set domain. It changes the cardinality 
	 * too to avoid cardinality constraining the domain. 
	 * 
	 * @param set a set of values which can be taken by a set domain.
	 * 
	 */
	public abstract void addDom(IntDomain set);

	/**
	 * Adds a set domain to this set domain. This operation may
	 * add more sets than intended if for example used in the 
	 * context of BoundSetDomain which can not represent arbitrary 
	 * union of two sets.
	 * 
	 * @param domain a set domain containing information what sets are being added.
	 * 
	 */
	public abstract void addDom(SetDomain domain);
	
	/**
	 * Adds an interval [min..max] to the domain.
	 * @param min min value in the set
	 * @param max max value in the set
	 */
	public abstract void addDom(int min, int max);

	/**
	 * Returns the cardinality of the setDomain as [glb.card(), lub.card()] 
	 * @return The cardinality of the setDomain given as a boundDomain.
	 */
	public abstract IntDomain card();
	
	/**
	 * Sets the domain to an empty SetDomain.
	 */
	@Override
	public abstract void clear();

	/**
	 * It checks if the supplied set or setDomain is still potentially a subset of this domain.
	 * @param set the set for which we check the inclusion relation.
	 * @return true, if this domain contains provided set, false otherwise.
	 */
	public abstract boolean contains(IntDomain set);
	

	/**
	 * It checks if the supplied set domain is a subset of this domain. 
	 * 
	 * @param domain the domain for which we check the inclusion relation.
	 * @return true, if this domain contains provided domain, false otherwise.
	 */

	public abstract boolean contains(SetDomain domain);

	/**
	 * It checks if value belongs to the domain of the set. 
	 * 
	 * @param value value which is checked.
	 *  
	 * @return true if the value being checked can still be included in the set, false otherwise.
	 */
	public abstract boolean contains(int value);
	
	/**
	 * It returns an unique identifier of the domain.
	 * @return it returns an integer id of the domain.
	 */
	@Override
	public abstract int domainID();

	/**
	 * It checks if the domain is equal to the supplied domain.
	 * @param domain against which the equivalence test is performed.
	 * @return true if suppled domain has the same elements as this domain. 
	 */
	public abstract boolean eq(SetDomain domain);
	
	/**
	 * This function is equivalent to in(int storeLevel, Variable var, int min, int max).
	 *
	 * @param storeLevel the level of the store at which the change occurrs.
	 * @param var the set variable for which the domain may change.
	 * @param glb the greatest lower bound of the domain. 
	 * @param lub the least upper bound of the domain.
	 */
	public abstract void in(int storeLevel, SetVar var, IntDomain glb, IntDomain lub);
	
	/**
	 * It updates the domain to have values only within the domain. The type of
	 * update is decided by the value of stamp. It informs the variable of a
	 * change if it occurred.
	 * @param storeLevel level of the store at which the update occurs.
	 * @param var variable for which this domain is used.
	 * @param domain the domain according to which the domain is updated.
	 */
	public abstract void in(int storeLevel, SetVar var, SetDomain domain);
	
	/**
	 * It intersects current domain with the one given as a parameter.
	 * @param domain domain with which the intersection needs to be computed.
	 * @return the intersection between supplied domain and this domain.
	 */
	public abstract SetDomain intersect(SetDomain domain);
	
	/**
	 * It intersects current domain with the set of allowed values to be taken
	 * by the set domain. 
	 * 
	 * @param set set of values which are allowed to be used within a set. 
	 * 
	 * @return the intersection of this domain with the set of allowed values. 
	 */
	public abstract SetDomain intersect(IntDomain set);
	
	/**
	 * It returns true if given domain is empty.
	 * @return true if the given domain is empty.
	 */
	@Override
	public abstract boolean isEmpty();

	/**
	 * It returns true if this domain intersects with the supplied domain.
	 * @param domain the domain against which the intersection is being checked.
	 * 
	 * @return true if the given domain intersects this domain.
	 */
	public abstract boolean isIntersecting(SetDomain domain);

	/**
	 * In intersects current domain with the interval min..max.
	 * @param min the left bound of the interval (inclusive)
	 * @param max the right bound of the interval (inclusive)
	 * @return the intersection between the specified interval and this domain.
	 */
	public abstract boolean isIntersecting(int min, int max);

	/**
	 * A set is never numeric
	 * @return false
	 */
	@Override
	public abstract boolean isNumeric();

	/**
	 * A set is not sparse
	 * @return false
	 */
	@Override
	public abstract boolean isSparseRepresentation();

	/**
	 * It returns the least upper bound of the domain.
	 * @return the least upper bound of the domain.
	 */
	public abstract IntDomain lub();
	
	/**
	 * It returns the least upper bound of the domain.
	 * @return the least upper bound of the domain.
	 */
	public abstract IntDomain glb();

	/**
	 * It clones the domain object, only data responsible for encoding domain
	 * values is cloned. All other fields must be set separately.
	 * @return return a clone of the domain. It aims at getting domain of the proper class type. 
	 */
	public abstract SetDomain cloneLight();

	/**
	 * It adds a constraint to a domain, it should only be called by
	 * putConstraint function of Variable object. putConstraint function from
	 * Variable must make a copy of a vector of constraints if vector was not
	 * cloned.
	 */
	@Override
	public void putModelConstraint(int storeLevel, Var var, Constraint C,
			int pruningEvent) {

		if (stamp < storeLevel) {

			SetDomain result = this.cloneLight();

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			((SetVar)var).domain = result;

			result.putModelConstraint(storeLevel, var, C, pruningEvent);
			return;
		}

		Constraint[] pruningEventConstraints = modelConstraints[pruningEvent];

		// FIXME, do not create a new array every time a new constraint is attached.
		if (pruningEventConstraints != null) {

			boolean alreadyImposed = false;

			if (modelConstraintsToEvaluate[pruningEvent] > 0)
				for (int i = pruningEventConstraints.length - 1; i >= 0 && !alreadyImposed; i--)
					if (pruningEventConstraints[i] == C)
						alreadyImposed = true;

			int pruningConstraintsToEvaluate = modelConstraintsToEvaluate[pruningEvent];

			if (!alreadyImposed) {
				
				Constraint[] newPruningEventConstraints = new Constraint[pruningConstraintsToEvaluate + 1];

				System.arraycopy(pruningEventConstraints, 0,
						newPruningEventConstraints, 0,
						pruningConstraintsToEvaluate);
				
				newPruningEventConstraints[pruningConstraintsToEvaluate] = C;

				Constraint[][] newModelConstraints = new Constraint[modelConstraints.length][];
				int[] newModelConstraintsToEvaluate = new int[modelConstraintsToEvaluate.length];

				for (int i = 0; i < modelConstraints.length; i++) {
					newModelConstraints[i] = modelConstraints[i];
					newModelConstraintsToEvaluate[i] = modelConstraintsToEvaluate[i];
				}

				newModelConstraints[pruningEvent] = newPruningEventConstraints;
				newModelConstraintsToEvaluate[pruningEvent]++;

				modelConstraints = newModelConstraints;
				modelConstraintsToEvaluate = newModelConstraintsToEvaluate;

			}

		} else {

			Constraint[] newPruningEventConstraints = new Constraint[1];
			newPruningEventConstraints[0] = C;

			Constraint[][] newModelConstraints = new Constraint[modelConstraints.length][];
			int[] newModelConstraintsToEvaluate = new int[modelConstraintsToEvaluate.length];

			for (int i = 0; i < modelConstraints.length; i++) {
				newModelConstraints[i] = modelConstraints[i];
				newModelConstraintsToEvaluate[i] = modelConstraintsToEvaluate[i];
			}

			newModelConstraints[pruningEvent] = newPruningEventConstraints;
			newModelConstraintsToEvaluate[pruningEvent] = 1;

			modelConstraints = newModelConstraints;
			modelConstraintsToEvaluate = newModelConstraintsToEvaluate;			

		}

	}

	/**
	 * It adds a constraint to a domain, it should only be called by
	 * putConstraint function of Variable object. putConstraint function from
	 * Variable must make a copy of a vector of constraints if vector was not
	 * cloned.
	 */
	@Override
	public void putSearchConstraint(int storeLevel, Var var, Constraint C) {

		if (!searchConstraints.contains(C)) {

			if (stamp < storeLevel) {

				SetDomain result = this.cloneLight();

				result.modelConstraints = modelConstraints;

				result.searchConstraints = new ArrayList<Constraint>(
						searchConstraints.subList(0,
								searchConstraintsToEvaluate));
				result.searchConstraintsCloned = true;
				result.stamp = storeLevel;
				result.previousDomain = this;
				result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
				result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
				((SetVar)var).domain = result;

				result.putSearchConstraint(storeLevel, var, C);
				return;
			}

			if (searchConstraints.size() == searchConstraintsToEvaluate) {
				searchConstraints.add(C);
				searchConstraintsToEvaluate++;
			} else {
				// Exchange the first satisfied constraint with just added
				// constraint
				// Order of satisfied constraints is not preserved

				if (searchConstraintsCloned) {
					Constraint firstSatisfied = searchConstraints
					.get(searchConstraintsToEvaluate);
					searchConstraints.set(searchConstraintsToEvaluate, C);
					searchConstraints.add(firstSatisfied);
					searchConstraintsToEvaluate++;
				} else {
					searchConstraints = new ArrayList<Constraint>(
							searchConstraints.subList(0,
									searchConstraintsToEvaluate));
					searchConstraintsCloned = true;
					searchConstraints.add(C);
					searchConstraintsToEvaluate++;
				}
			}
		}

	}


	/**
	 * It returns the values which have been removed at current store level.
	 * @param storeLevel the current store level.
	 * @return emptyDomain if domain did not change at current level, or the set of values which have been removed at current level.
	 */
	public SetDomain recentDomainPruning(int storeLevel) {
		if (previousDomain == null)
			return emptyDomain;

		if (stamp < storeLevel)
			return emptyDomain;

		return previousDomain.subtract(this);		
	}

	/**
	 * It removes the specified level. This function may re-instantiate
	 * the old copy of the domain (previous value) or recover from changes done at stamp
	 * level to get the previous value at level lower at provided level.
	 * @param level the level which is being removed.
	 * @param var the variable to which this domain belonged to.
	 */
	@Override
	public void removeLevel(int level, Var var) {

		assert (this.stamp <= level);

		if (this.stamp == level) {

			((SetVar)var).domain = this.previousDomain;
		}

		assert (var.level() < level);		
	}


	/**
	 * It removes a constraint from a domain, it should only be called by
	 * removeConstraint function of Variable object.
	 */
	@Override
	public void removeSearchConstraint(int storeLevel, Var var,
			int position, Constraint C) {

		if (stamp < storeLevel) {

			SetDomain result = this.cloneLight();

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			((SetVar)var).domain = result;

			result.removeSearchConstraint(storeLevel, var, position, C);
			return;
		}

		assert (stamp == storeLevel);

		if (position < searchConstraintsToEvaluate) {

			searchConstraints.set(position, searchConstraints
					.get(searchConstraintsToEvaluate - 1));
			searchConstraints.set(searchConstraintsToEvaluate - 1, C);
			searchConstraintsToEvaluate--;

		}

	}

	/**
	 * It removes a constraint from a domain, it should only be called by
	 * removeConstraint function of Variable object.
	 */
	@Override
	public void removeModelConstraint(int storeLevel, Var var, Constraint C) {

		if (stamp < storeLevel) {

			SetDomain result = this.cloneLight();

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			((SetVar)var).domain = result;

			result.removeModelConstraint(storeLevel, var, C);
			return;
		}

		int pruningEvent = IntDomain.GROUND;

		Constraint[] pruningEventConstraints = modelConstraints[pruningEvent];

		if (pruningEventConstraints != null) {

			boolean isImposed = false;

			int i;

			for (i = modelConstraintsToEvaluate[pruningEvent] - 1; i >= 0; i--)
				if (pruningEventConstraints[i] == C) {
					isImposed = true;
					break;
				}

			// int pruningConstraintsToEvaluate =
			// modelConstraintsToEvaluate[pruningEvent];

			if (isImposed) {

				if (i != modelConstraintsToEvaluate[pruningEvent] - 1) {

					modelConstraints[pruningEvent][i] = modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1];

					modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1] = C;
				}

				int[] newModelConstraintsToEvaluate = new int[3];

				newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
				newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
				newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];

				newModelConstraintsToEvaluate[pruningEvent]--;

				modelConstraintsToEvaluate = newModelConstraintsToEvaluate;

				return;

			}

		}

		pruningEvent = IntDomain.BOUND;

		pruningEventConstraints = modelConstraints[pruningEvent];

		if (pruningEventConstraints != null) {

			boolean isImposed = false;

			int i;

			for (i = modelConstraintsToEvaluate[pruningEvent] - 1; i >= 0; i--)
				if (pruningEventConstraints[i] == C) {
					isImposed = true;
					break;
				}

			if (isImposed) {

				if (i != modelConstraintsToEvaluate[pruningEvent] - 1) {

					modelConstraints[pruningEvent][i] = modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1];

					modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1] = C;
				}

				int[] newModelConstraintsToEvaluate = new int[3];

				newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
				newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
				newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];

				newModelConstraintsToEvaluate[pruningEvent]--;

				modelConstraintsToEvaluate = newModelConstraintsToEvaluate;

				return;

			}

		}

		pruningEvent = IntDomain.ANY;

		pruningEventConstraints = modelConstraints[pruningEvent];

		if (pruningEventConstraints != null) {

			boolean isImposed = false;

			int i;

			for (i = modelConstraintsToEvaluate[pruningEvent] - 1; i >= 0; i--)
				if (pruningEventConstraints[i] == C) {
					isImposed = true;
					break;
				}

			// int pruningConstraintsToEvaluate =
			// modelConstraintsToEvaluate[pruningEvent];

			if (isImposed) {

				if (i != modelConstraintsToEvaluate[pruningEvent] - 1) {

					modelConstraints[pruningEvent][i] = modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1];

					modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1] = C;
				}

				int[] newModelConstraintsToEvaluate = new int[3];

				newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
				newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
				newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];

				newModelConstraintsToEvaluate[pruningEvent]--;

				modelConstraintsToEvaluate = newModelConstraintsToEvaluate;

			}

		}

	}

	/**
	 * It sets the domain to the specified domain.
	 * @param domain the domain from which this domain takes all elements.
	 */
	public abstract void setDomain(SetDomain domain);
	
	/**
	 * It sets the domain to contain any values in between min and max.
	 * 
	 * @param min the minimum value allowed to be taken within the set. 
	 * @param max the maximal value allowed to be taken within the set.
	 */
	public abstract void setDomain(int min, int max);

	/**
	 * It returns true if given domain has only one set-element.
	 * @return true if the domain contains only one set-element.
	 */
	public abstract boolean singleton();

	/**
	 * It check whether the set domain is singleton and its value is 
	 * equal to the specified set. 
	 * 
	 * @param set the set for which we check if it is equal to a value taken by this set domain. 
	 *  
	 * @return true, if this set domain is equal to supplied set, false otherwise.
	 */	
	public abstract boolean singleton(IntDomain set);

	/**
	 * It returns all constraints which are associated with variable, even the
	 * ones which are already satisfied.
	 * @return the number of constraints attached to the original domain of the variable associated with this domain.
	 */
	@Override
	public int sizeConstraintsOriginal() {

		SetDomain domain = this;

		while (domain.domainID() == SetDomainID) {

			if (domain.previousDomain != null)
				domain = domain.previousDomain;
			else
				break;
		}

			return (domain.modelConstraintsToEvaluate[0]
			        + domain.modelConstraintsToEvaluate[1] 
			        + domain.modelConstraintsToEvaluate[2]);

	}

	/**
	 * It subtracts domain from current domain and returns the result.
	 * @param domain the domain which is subtracted from this domain.
	 * @return the result of the subtraction.
	 */
	public abstract SetDomain subtract(SetDomain domain);

	/**
	 * It subtracts the set {min..max}.
	 * @param min the left bound of the set.
	 * @param max the right bound of the set.
	 * @return the result of the subtraction.
	 */
	public abstract SetDomain subtract(int min, int max);

	/**
	 * It removes the value from any set allowed to be taken 
	 * by this set domain.
	 *  
	 * @param value value which can not be used within any set value assigned to this set domain.
	 * 
	 * @return the domain which does not allow specified value to be used. 
	 * 
	 */
	public abstract SetDomain subtract(int value);

	/**
	 * It returns string description of the constraints attached to the domain.
	 * @return the string description.
	 */
	@Override
	public String toStringConstraints() {

		StringBuffer S = new StringBuffer("");

		for (Iterator<Constraint> e = searchConstraints.iterator(); e.hasNext();) {
			S.append(e.next().id());
			if (e.hasNext())
				S.append(", ");
		}

		return S.toString();		

	}

	/**
	 * not implemented.
	 */
	@Override
	public String toStringFull() {
		throw new RuntimeException("This function is not used for setDomain.");
		/*
		StringBuffer S = new StringBuffer("");

		Domain domain = this;

		do {
			if (!domain.singleton()) {
				S.append(toString()).append("(").append(domain.stamp()).append(") ");
			} else
				S.append(min).append("(").append(
						String.valueOf(domain.stamp())).append(") ");

			S.append("constraints: ");

			for (Iterator<Constraint> e = domain.searchConstraints.iterator(); e
					.hasNext();)
				S.append(e.next());

			if (domain.domainID() == IntervalDomainID) {

				IntervalDomain dom = (IntervalDomain) domain;
				domain = dom.previousDomain;

			} 
			else if (domain.domainID() == BoundDomainID) {

				BoundDomain dom = (BoundDomain) domain;
				domain = dom.previousDomain;

				}
			else {

				// Other type.
			}

		} while (domain != null);

		return S.toString();
		 */
	}

	/**
	 * It computes union of the supplied domain with this domain.
	 * @param domain the domain for which the union is computed.
	 * @return the union of this domain with the supplied one.
	 */
	public abstract SetDomain union(SetDomain domain);
	
	/**
	 * It computes union of this domain and the interval.
	 * @param min the left bound of the interval (inclusive).
	 * @param max the right bound of the interval (inclusive).
	 * @return the union of this domain and the interval.
	 */

	public abstract SetDomain union(int min, int max);

	/**
	 * It computes union of this domain and value. 
	 * 
	 * @param value it specifies the value which is being added.
	 * @return domain which is a union of this one and the value.
	 */
	public abstract SetDomain union(int value);

	/**
	 * It returns value enumeration of the domain values.
	 * @return valueEnumeration which can be used to enumerate the sets of this domain one by one.
	 */
	@Override
	public abstract ValueEnumeration valueEnumeration();

	/**
	 * @return It returns the information about the first invariant which does not hold or null otherwise. 
	 */
	public abstract String checkInvariants();
	
	@Override
	public void in(int level, Var var, Domain domain) {
		
		in(level, (SetVar)var, (SetDomain)domain);
		
	}

	/**
	 * It specifies what elements can be in LUB. It will not add 
	 * any new elements only removed the elements currently in LUB
	 * but not permitted by the argument domain.  
	 * 
	 * @param level level of the store at which this restriction takes place.
	 * @param var variable which domain is being restricted. 
	 * @param domain the domain specifying the allowed values the domain of the set variable.
	 */
	public abstract void inLUB(int level, SetVar var, IntDomain domain);

	/**
	 * It specifies the element which can *NOT* be used as an element within a set assign
	 * to a set variable. 
	 * 
	 * @param level level of the store at which this restriction takes place.
	 * @param var variable which domain is being restricted. 
	 * @param element the value being removed from the domain of the set variable.
	 */
	public abstract void inLUBComplement(int level, SetVar var, int element);

	/**
	 * It specifies what elements must be in GLB. It will add 
	 * new elements if they are not already in GLB. 
	 * 
	 * @param level level of the store at which this addition takes place.
	 * @param var variable which domain is being restricted. 
	 * @param domain the domain specifying the required values of the set variable.
	 */
	
	public abstract void inGLB(int level, SetVar var, IntDomain domain);

	/**
	 * It adds if necessary an element to glb.
	 * @param level level at which the change is recorded.
	 * @param var set variable to which the change applies to.
	 * @param element the element which must be in glb.
	 */
	public abstract void inGLB(int level, SetVar var, int element);

	/**
	 * It assigns a set variable to the specified value. 
	 * 
	 * @param level level at which the change is recorded.
	 * @param var set variable to which the change applies to.
	 * @param set the value assigned to a set variable.
	 */
	public abstract void inValue(int level, SetVar var, IntDomain set);

	/**
	 * It returns the number of constraints
	 * @return the number of constraints attached to this domain.
	 */
	// FIXME, how to deal with repeated constraints without penalty hit.
	public int noConstraints() {
		return searchConstraintsToEvaluate 
				+ modelConstraintsToEvaluate[GROUND]
				+ modelConstraintsToEvaluate[LUB]
				+ modelConstraintsToEvaluate[GLB]
				+ modelConstraintsToEvaluate[ANY];
	}


	/**
	 * It restricts the possible cardinality of the set domain. 
	 * 
	 * @param level level of the store at which the restriction takes place.
	 * @param a the variable which domain is being restricted.
	 * @param i the minimal allowed cardinality
	 * @param j the maximal allowed cardinality
	 */
	public abstract void inCardinality(int level, SetVar a, int i, int j);


}

