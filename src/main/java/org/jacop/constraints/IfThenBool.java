/**
 *  IfThenBool.java
 *   
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Constraint ( X => Y ) <=> Z.
 * 
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class IfThenBool extends PrimitiveConstraint {

	/*
	 * X | Y | Z
	 * 0   0   1
	 * 0   1   1
	 * 1   0   0
	 * 1   1   1
	 */
	
	static int counter = 1;

	/**
	 * It specifies variable x in constraint ( X => Y ) <=> Z.
	 */
	public IntVar x;

	/**
	 * It specifies variable y in constraint ( X => Y ) <=> Z.
	 */
	public IntVar y;

	/**
	 * It specifies variable z in constraint ( X => Y ) <=> Z.
	 */
	public IntVar z;

	
	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"x", "y", "z"};

	/** It constructs constraint ( X => Y ) <=> Z.
	 * @param x variable x.
	 * @param y variable y.
	 * @param z variable z.
	 */
	public IfThenBool(IntVar x, IntVar y, IntVar z) {

		assert (x != null) : "Variable x is null";
		assert (y != null) : "Variable y is null";
		assert (z != null) : "Variable z is null";

		numberId = counter++;
		numberArgs = 3;

		this.x = x;
		this.y = y;
		this.z = z;
		
		assert ( checkInvariants() == null) : checkInvariants();

	}

	/**
	 * It checks invariants required by the constraint. Namely that
	 * boolean variables have boolean domain. 
	 * 
	 * @return the string describing the violation of the invariant, null otherwise.
	 */
	public String checkInvariants() {

		if (x.min() < 0 || x.max() > 1)
			return "Variable " + x + " does not have boolean domain";

		if (y.min() < 0 || y.max() > 1)
			return "Variable " + y + " does not have boolean domain";

		if (z.min() < 0 || z.max() > 1)
			return "Variable " + z + " does not have boolean domain";

		return null;
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(3);

		variables.add(x);
		variables.add(y);
		variables.add(z);
		return variables;
	}

	@Override
	public void consistency(Store store) {

		if (z.max() == 0) {
			x.domain.in(store.level, x, 1, 1);
			y.domain.in(store.level, y, 0, 0);
		}

		if (x.max() == 0) {
			z.domain.in(store.level, z, 1, 1);				
		} else if (x.min() == 1) {
			z.domain.in(store.level, z, y.domain);
			y.domain.in(store.level, y, z.domain);				
		}

		if (y.max() == 0) {
			if (x.singleton())
				z.domain.inComplement(store.level, z, x.value() );
			if (z.singleton())
				x.domain.inComplement(store.level, x, z.value() );
		} else if (y.min() == 1) {
			z.domain.in(store.level, z, 1, 1);								
		}			

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
			return IntDomain.GROUND;
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
		return IntDomain.BOUND;
	}

	@Override
	public int getNotConsistencyPruningEvent(Var var) {

		// If notConsistency function mode
		if (notConsistencyPruningEvents != null) {
			Integer possibleEvent = notConsistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return IntDomain.GROUND;
	}

	@Override
	public void impose(Store store) {

		x.putModelConstraint(this, getConsistencyPruningEvent(x));
		y.putModelConstraint(this, getConsistencyPruningEvent(y));
		z.putModelConstraint(this, getConsistencyPruningEvent(z));
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void notConsistency(Store store) {

		do {

			store.propagationHasOccurred = false;
			
			if (x.singleton()) {

				if (x.max() == 0) {
					z.domain.in(store.level, z, 0, 0);				
				}

				if (x.min() == 1) {
					if (y.singleton())
						z.domain.inComplement(store.level, z, y.value() );
					if (z.singleton())
						y.domain.inComplement(store.level, y, z.value() );
				}
			}

			if (y.singleton()) {

				if (y.max() == 0) {
					z.domain.in(store.level, z, x.domain);
					x.domain.in(store.level, x, z.domain);				
				}

				if (y.min() == 1) {
					z.domain.in(store.level, z, 0, 0);								
				}
			}

			if (z.min() == 1) {
				x.domain.in(store.level, x, 1, 1);
				y.domain.in(store.level, y, 0, 0);
			}

		} while (store.propagationHasOccurred);

	}

	@Override
	public boolean notSatisfied() {

		if (!x.singleton())
			return false;
		if (!z.singleton())
			return false;

		if (x.singleton(0) && z.singleton(0))
			return true;

		if (!y.singleton())
			return false;

		if (x.singleton(1) && y.singleton(1) && z.singleton(0))
			return true;

		// 1 0 1
		return false;
	}

	@Override
	public void removeConstraint() {
		x.removeConstraint(this);
		y.removeConstraint(this);
		z.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {

		if (!x.singleton())
			return false;
		if (!z.singleton())
			return false;

		if (x.singleton(0) && z.singleton(1))
			return true;

		if (!y.singleton())
			return false;

		if (x.singleton(1) && y.singleton(1) && z.singleton(1))
			return true;

		// 1 0 0
		return false;

	}

	@Override
	public String toString() {

		return id() + " : IfThenBool( (" + x + "=> " + y + ") <=> " + z + " )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			x.weight++;
			y.weight++;
			z.weight++;
		}
	}

}
