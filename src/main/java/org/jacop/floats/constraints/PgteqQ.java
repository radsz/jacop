/**
 *  PgteqQ.java 
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

package org.jacop.floats.constraints;

import java.util.ArrayList;

import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

import org.jacop.constraints.PrimitiveConstraint;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;

/**
 * Constraints P >= Q for floats
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class PgteqQ extends PrimitiveConstraint {

	static int idNumber = 1;

	/**
	 * It specifies variables p which must be greater or equal to a given varibale.
	 */
	public FloatVar p;

	/**
	 * It specifies variablw q from which a given variable must be greater or equal.
	 */
	public FloatVar q;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"p", "q"};

	/**
	 * It constructs constraint P >= Q.
	 * @param p variable p.
	 * @param q variable q.
	 */
	public PgteqQ(FloatVar p, FloatVar q) {
		
		assert (p != null) : "Variable p is null";
		assert (q != null) : "Variable q is null";

		numberId = idNumber++;
		numberArgs = 1;
		
		this.p = p;
		this.q = q;
	
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(1);

		variables.add(p);
		variables.add(q);
		return variables;
	}

	@Override
	public void consistency(Store store) {

	    p.domain.inMin(store.level, p, q.min());
	    q.domain.inMax(store.level, q, p.max());
	
	}

	@Override
	public void notConsistency(Store store) {
	    p.domain.inMax(store.level, p, FloatDomain.previous(q.max()));
	    q.domain.inMin(store.level, q, FloatDomain.next(p.min()));
	}

	@Override
	public boolean satisfied() {
	    return p.min() >= q.max();
	}

	@Override
	public boolean notSatisfied() {
	    return p.max() < q.min();
	}

	@Override
	public int getNestedPruningEvent(Var var, boolean mode) {

		// If consistency function mode
		if (mode) {
			if (consistencyPruningEvents != null) {
				Integer possibleEvent = consistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return IntDomain.BOUND;
		}
		// If notConsistency function mode
		else {
			if (notConsistencyPruningEvents != null) {
				Integer possibleEvent = notConsistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return IntDomain.BOUND;
		}
	}

	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
			if (consistencyPruningEvents != null) {
				Integer possibleEvent = consistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return Domain.NONE;
		}

	
	@Override
	public int getNotConsistencyPruningEvent(Var var) {

	// If notConsistency function mode
			if (notConsistencyPruningEvents != null) {
				Integer possibleEvent = notConsistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return Domain.NONE;
	}

	@Override
	public void impose(Store store) {
		p.putModelConstraint(this, getConsistencyPruningEvent(p));
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void removeConstraint() {
		p.removeConstraint(this);
	}

	@Override
	public String toString() {
		return id() + " : PgteqQ(" + p + ", " + q + " )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			p.weight++;
			q.weight++;
		}
	}
	
}
