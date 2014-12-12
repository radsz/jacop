/**
 *  XplusYeqZ.java 
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
 * Constraint X + Y #= Z
 * 
 * Bound consistency is used.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class XplusYeqZ extends PrimitiveConstraint {

	static int idNumber = 1;

	/**
	 * It specifies variable x in constraint x+y=z. 
	 */
	public IntVar x;

	/**
	 * It specifies variable x in constraint x+y=z. 
	 */
	public IntVar y;

	/**
	 * It specifies variable x in constraint x+y=z. 
	 */
	public IntVar z;

	
	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"x", "y", "z"};

	/** It constructs constraint X+Y=Z.
	 * @param x variable x.
	 * @param y variable y.
	 * @param z variable z.
	 */
	public XplusYeqZ(IntVar x, IntVar y, IntVar z) {
		
		assert (x != null) : "Variable x is null";
		assert (y != null) : "Variable y is null";
		assert (z != null) : "Variable z is null";

		numberId = idNumber++;
		numberArgs = 3;

		this.x = x;
		this.y = y;
		this.z =  z;

		checkForOverflow();
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
		
		do {
			
			store.propagationHasOccurred = false;

			if (x.singleton()) {

				y.domain.inShift(store.level, y, z.domain, -x.value());
				z.domain.inShift(store.level, z, y.domain, x.value());

			} else if (y.singleton()) {

				x.domain.inShift(store.level, x, z.domain, -y.value());
				z.domain.inShift(store.level, z, x.dom(), y.value());

			} else {

				x.domain.in(store.level, x, z.min() - y.max(), z.max()
						- y.min());
				y.domain.in(store.level, y, z.min() - x.max(), z.max()
						- x.min());
				z.domain.in(store.level, z, x.min() + y.min(), x.max()
						+ y.max());
			}

		} while (store.propagationHasOccurred);
		
	}

    void checkForOverflow() {

	int sumMin=0, sumMax=0;

	sumMin = add(sumMin, x.min());
	sumMax = add(sumMax, x.max());

	sumMin = add(sumMin, y.min());
	sumMax = add(sumMax, y.max());

	sumMin = subtract(sumMin, z.max());
	sumMax = subtract(sumMax, z.min());
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

			if (z.singleton() && y.singleton())
				x.domain.inComplement(store.level, x, z.min() - y.min());

			if (z.singleton() && x.singleton())
				y.domain.inComplement(store.level, y, z.min() - x.min());

			if (x.singleton() && y.singleton())
				z.domain.inComplement(store.level, z, x.min() + y.min());
			
		} while (store.propagationHasOccurred);
		
	}

	@Override
	public boolean notSatisfied() {
		IntDomain xDom = x.dom(), yDom = y.dom(), zDom = z.dom();
		return (xDom.max() + yDom.max() < zDom.min() || 
				xDom.min() + yDom.min() > zDom.max());
	}

	@Override
	public void removeConstraint() {
		x.removeConstraint(this);
		y.removeConstraint(this);
		z.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {

		return (x.singleton() && y.singleton() && z.singleton() 
				&& x.value() + y.value() == z.value());
		
	}

	@Override
	public String toString() {

		return id() + " : XplusYeqZ(" + x + ", " + y + ", " + z + " )";
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
