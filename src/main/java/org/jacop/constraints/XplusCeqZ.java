/**
 *  XplusCeqZ.java
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

import java.util.*;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Constraint X + C #= Z.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class XplusCeqZ extends PrimitiveConstraint { private static Logger logger = LoggerFactory.getLogger(XplusCeqZ.class);

	static int idNumber = 1;

	/**
	 * It specifies variable x in constraint x+c=z.
	 */
	public IntVar x;

	/**
	 * It specifies constant c in constraint x+c=z.
	 */
	public int c;

	/**
	 * It specifies variable z in constraint x+c=z.
	 */
	public IntVar z;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"x", "c", "z"};

	/**
	 * It constructs a constraint x+c=z.
	 * @param x variable x.
	 * @param c constant c.
	 * @param z variable z.
	 */
	public XplusCeqZ(IntVar x, int c, IntVar z) {

		assert (x != null) : "Variable x is null";
		assert (z != null) : "Variable z is null";

		numberId = idNumber++;
		numberArgs = 2;

		this.x = x;
		this.c = c;
		this.z = z;

	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(2);

		variables.add(x);
		variables.add(z);
		return variables;
	}

	@Override
	public void consistency(Store store) {

		do {

			store.propagationHasOccurred = false;

			x.domain.inShift(store.level, x, z.domain, -c);

			z.domain.inShift(store.level, z, x.domain, c);

		} while (store.propagationHasOccurred);

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
			return IntDomain.ANY;
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
		z.putModelConstraint(this, getConsistencyPruningEvent(z));
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void notConsistency(Store store) {

		do {

			store.propagationHasOccurred = false;

			if (x.singleton())
				z.domain.inComplement(store.level, z, x.min() + c);

			if (z.singleton())
				x.domain.inComplement(store.level, x, z.min() - c);

		} while (store.propagationHasOccurred);

	}

	@Override
	public boolean notSatisfied() {
		return (x.max() + c < z.min() || x.min() + c > z.max());

	}

	@Override
	public void removeConstraint() {
		x.removeConstraint(this);
		z.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
		return x.singleton() && z.singleton() && x.min() + c == z.min();
	}

	@Override
	public String toString() {

		return id() + " : XplusCeqZ(" + x + ", " + c + ", " + z + " )";
	}


	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			x.weight++;
			z.weight++;
		}
	}

}
