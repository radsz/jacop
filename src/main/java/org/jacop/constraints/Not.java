/**
 *  Not.java 
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

import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.util.SimpleHashSet;

/**
 * Constraint "not costraint"
 * 
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Not extends PrimitiveConstraint {

	static int IdNumber = 1;

	/**
	 * It specifies the constraint which negation is being created.
	 */
	public PrimitiveConstraint c;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"c"};

	/**
	 * It constructs not constraint.
	 * @param c primitive constraint which is being negated.
	 */
	public Not(PrimitiveConstraint c) {
		numberId = IdNumber++;
		this.c = c;
		numberArgs += c.numberArgs();
	}

	@Override
	public ArrayList<Var> arguments() {

		return c.arguments();

	}

	@Override
	public void consistency(Store store) {
		c.notConsistency(store);
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
			return c.getNestedPruningEvent(var, false);
	}

		
	@Override
	public int getNotConsistencyPruningEvent(Var var) {
		
		// If notConsistency function mode
			if (notConsistencyPruningEvents != null) {
				Integer possibleEvent = notConsistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return c.getNestedPruningEvent(var, true);
	}

	@Override
	public void impose(Store store) {

		SimpleHashSet<Var> variables = new SimpleHashSet<Var>();

		for (Var V : c.arguments())
			variables.add(V);

		while (!variables.isEmpty()) {
			Var V = variables.removeFirst();
			V.putModelConstraint(this, getConsistencyPruningEvent(V));
		}

		c.include(store);

		store.addChanged(this);
		store.countConstraint();
	}

        @Override
        public void include(Store store) {
	    c.include(store);
	}

	@Override
	public void notConsistency(Store store) {
		c.consistency(store);
	}

	@Override
	public boolean notSatisfied() {
		return c.satisfied();
	}

	@Override
	public void removeConstraint() {

		for (Var V : c.arguments())
			V.removeConstraint(this);

	}

	@Override
	public boolean satisfied() {
		return c.notSatisfied();
	}

	@Override
	public String toString() {
		return id() + " : Not( " + c + ")";
	}
	
	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			c.increaseWeight();
		}
	}

}
