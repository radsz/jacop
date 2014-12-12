/**
 *  PeqC.java 
 *  This file is part of org.jacop.
 *
 *  org.jacop is a Java Constraint Programming solver. 
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
 * Constraints P #= C
 * 
 * Domain consistency is used.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class PeqC extends PrimitiveConstraint {

	static int idNumber = 1;

	/**
	 * It specifies the constant to which a specified variable should be equal to. 
	 */
	public double c;

	/**
	 * It specifies the variable which is constrained to be equal to the specified value.
	 */
	public FloatVar p;

	/**
	 * It specifies the arguments required to be saved by an PML format as well as 
	 * the constructor being called to recreate an object from an PML format.
	 */
	public static String[] pmlAttributes = {"x", "c"};

	/**
	 * It constructs the constraint P = C.
	 * @param p variable p.
	 * @param c constant c.
	 */
	public PeqC(FloatVar p, double c) {

		assert (p != null) : "Variable p is null";
		assert (c >= IntDomain.MinInt && c <= IntDomain.MaxInt) : "Constant c " + c + " is not in the allowed range ";

		numberId = idNumber++;
		numberArgs = 1;
		this.p = p;
		this.c = c;

	}
	
	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(1);
		variables.add(p);

		return variables;
	}

	@Override
	public void consistency(Store store) {

		p.domain.in(store.level, p, c, c);

	}

	@Override
	public void notConsistency(Store store) {

		p.domain.inComplement(store.level, p, c);

	}

	@Override
	public boolean satisfied() {
		return p.singleton(c);
	}

	@Override
	public boolean notSatisfied() {
		return ! p.domain.contains(c);
	}

	@Override
	public int getNestedPruningEvent(Var var, boolean mode) {

		// If satisfied function mode
		if (mode) {
			if (consistencyPruningEvents != null) {
				Integer possibleEvent = consistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}

			return IntDomain.ANY;

		}
		// If notSatisfied function mode
		else {
			if (notConsistencyPruningEvents != null) {
				Integer possibleEvent = notConsistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return IntDomain.ANY;

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
		return id() + " : PeqC(" + p + ", " + c + " )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			p.weight++;
		}
	}

	/**
	 * It returns the constant to which a given variable should be equal to.
	 * @return the constant to which the variable should be equal to.
	 */
	public double getC() {
		return c;
	} 

}
