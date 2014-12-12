/**
 *  Eq.java 
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

import org.jacop.core.Domain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.util.SimpleHashSet;

/**
 * Constraint "constraint1" #<=> "constraint2"
 * 
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Eq extends PrimitiveConstraint {

	static int counter = 1;

	/**
	 * It specifies the first constraint which status must be equivalent to the status of the second constraint. 
	 */
	public PrimitiveConstraint c1;

	/**
	 * It specifies the second constraint which status must be equivalent to the status of the first constraint.
	 */
	public PrimitiveConstraint c2;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"c1", "c2"};

	/**
	 * It constructs equality constraint between two constraints.
	 * @param c1 the first constraint 
	 * @param c2 the second constraint
	 */
	public Eq(PrimitiveConstraint c1, PrimitiveConstraint c2) {

		assert (c1 != null) : "Constraint c1 is null";
		assert (c2 != null) : "Constraint c1 is null";
		
		numberId = counter++;
		numberArgs = (short) ( c1.numberArgs + c2.numberArgs );
		
		this.c1 = c1;
		this.c2 = c2;
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(1);

		variables.addAll(c1.arguments());
		variables.addAll(c2.arguments());
		
		return variables;
	}

	@Override
	public void consistency(Store store) {

		// Does not need to loop due to propagation occuring.		
		if (c2.satisfied())
			c1.consistency(store);
		else if (c2.notSatisfied())
			c1.notConsistency(store);

		if (c1.satisfied())
			c2.consistency(store);
		else if (c1.notSatisfied())
			c2.notConsistency(store);
		
	}

	@Override
	public int getNestedPruningEvent(Var var, boolean mode) {

		return getConsistencyPruningEvent(var);

	}


	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
			if (consistencyPruningEvents != null) {
				Integer possibleEvent = consistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}

			int eventAcross = -1;

			if (c1.arguments().contains(var)) {
				int event = c1.getNestedPruningEvent(var, true);
				if (event > eventAcross)
					eventAcross = event;
			}

			if (c1.arguments().contains(var)) {
				int event = c1.getNestedPruningEvent(var, false);
				if (event > eventAcross)
					eventAcross = event;
			}

			if (c2.arguments().contains(var)) {
				int event = c2.getNestedPruningEvent(var, true);
				if (event > eventAcross)
					eventAcross = event;
			}

			if (c2.arguments().contains(var)) {
				int event = c2.getNestedPruningEvent(var, false);
				if (event > eventAcross)
					eventAcross = event;
			}

			if (eventAcross == -1)
				return Domain.NONE;
			else
				return eventAcross;
			
		}

	@Override
	public int getNotConsistencyPruningEvent(Var var) {
		
		// If notConsistency function mode
			if (notConsistencyPruningEvents != null) {
				Integer possibleEvent = notConsistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}

		int eventAcross = -1;

		if (c1.arguments().contains(var)) {
			int event = c1.getNestedPruningEvent(var, true);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (c1.arguments().contains(var)) {
			int event = c1.getNestedPruningEvent(var, false);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (c2.arguments().contains(var)) {
			int event = c2.getNestedPruningEvent(var, true);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (c2.arguments().contains(var)) {
			int event = c2.getNestedPruningEvent(var, false);
			if (event > eventAcross)
				eventAcross = event;
		}

		if (eventAcross == -1)
			return Domain.NONE;
		else
			return eventAcross;

	}

	@Override
	public void impose(Store store) {

		SimpleHashSet<Var> variables = new SimpleHashSet<Var>();

		for (Var var : c1.arguments())
			variables.add(var);

		for (Var var : c2.arguments())
			variables.add(var);

		while (!variables.isEmpty()) {
			Var V = variables.removeFirst();
			V.putModelConstraint(this, getConsistencyPruningEvent(V));
		}

		c1.include(store);
		c2.include(store);

		store.addChanged(this);
		store.countConstraint(2);
	}

    @Override
    public void include(Store store) {

	c1.include(store);
	c2.include(store);

    }

	@Override
	public void notConsistency(Store store) {

		// No need for fixpoint loop in this context. Fixpoint always achieved after one execution.
		if (c2.satisfied())
			c1.notConsistency(store);
		else if (c2.notSatisfied())
			c1.consistency(store);
		
		if (c1.satisfied())
			c2.notConsistency(store);
		else if (c1.notSatisfied())
			c2.consistency(store);
		

	}

	@Override
	public boolean notSatisfied() {
		return (c1.satisfied() && c2.notSatisfied())
				|| (c1.notSatisfied() && c2.satisfied());
	}

	@Override
	public void removeConstraint() {

		for (Var var : c1.arguments())
			var.removeConstraint(this);

		for (Var var : c2.arguments())
			var.removeConstraint(this);

	}

	@Override
	public boolean satisfied() {
		return (c1.satisfied() && c2.satisfied())
				|| (c1.notSatisfied() && c2.notSatisfied());
	}

	@Override
	public String toString() {

		return id() + " : Eq(" + c1 + ", " + c2 + " )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			c1.increaseWeight();
			c2.increaseWeight();
		}
	}
	
}
