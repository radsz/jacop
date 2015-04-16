/**
 *  XmodYeqZ.java
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
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Constraint X mod Y = Z
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 3.1
 */

public class XmodYeqZ extends Constraint { private static Logger logger = LoggerFactory.getLogger(XmodYeqZ.class);

	static int counter = 1;

	/**
	 * It specifies variable x in constraint x mod y = z.
	 */
	public IntVar x;

	/**
	 * It specifies variable y in constraint x mod y = z.
	 */
	public IntVar y;

	/**
	 * It specifies variable z in constraint x mod y = z.
	 */
	public IntVar z;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"x", "y", "z"};

	/**
	 * It constructs a constraint X mod Y = Z.
	 * @param x variable x.
	 * @param y variable y.
	 * @param z variable z.
	 */
	public XmodYeqZ(IntVar x, IntVar y, IntVar z) {

		assert (x != null) : "Variable x is null";
		assert (y != null) : "Variable y is null";
		assert (z != null) : "Variable z is null";

		numberId = counter++;
		numberArgs = 3;

		this.x = x;
		this.y = y;
		this.z = z;
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(3);

		variables.add(z);
		variables.add(y);
		variables.add(x);
		return variables;
	}

	@Override
	public void consistency (Store store) {

		int resultMin=IntDomain.MinInt;
		int resultMax=IntDomain.MaxInt;

		do {

			store.propagationHasOccurred = false;

			y.domain.inComplement(store.level, y, 0);

			// Compute bounds for reminder

			int reminderMin, reminderMax;

			if (x.min() >= 0) {
				reminderMin = 0;
				reminderMax = Math.max(Math.abs(y.min()), Math.abs(y.max()))  - 1;
			}
			else if (x.max() < 0) {
				reminderMax = 0;
				reminderMin = - Math.max(Math.abs(y.min()), Math.abs(y.max())) + 1;
			}
			else {
				reminderMin = Math.min(Math.min(y.min(),-y.min()), Math.min(y.max(),-y.max())) + 1;
				reminderMax = Math.max(Math.max(y.min(),-y.min()), Math.max(y.max(),-y.max())) - 1;
			}

			z.domain.in(store.level, z, reminderMin, reminderMax);

			// Bounds for result
			int oldResultMin = resultMin, oldResultMax = resultMax;

			IntervalDomain result = IntDomain.divBounds(x.min(), x.max(), y.min(), y.max());

			resultMin = result.min();
			resultMax = result.max();

			if (oldResultMin != resultMin || oldResultMax != resultMax)
			    store.propagationHasOccurred = true;

			// Bounds for Y
			IntervalDomain yBounds = IntDomain.divBounds(x.min()-reminderMax, x.max()-reminderMin, resultMin, resultMax);

 			y.domain.in(store.level, y, yBounds);

			// Bounds for Z and reminder
			IntervalDomain reminder = IntDomain.mulBounds(resultMin, resultMax, y.min(), y.max());
 			int zMin = reminder.min(), zMax = reminder.max();

 			reminderMin = x.min() - zMax;
 			reminderMax = x.max() - zMin;

 			z.domain.in(store.level, z, reminderMin, reminderMax);

			x.domain.in(store.level, x, zMin + z.min(), zMax + z.max());

			assert checkSolution(resultMin, resultMax) == null : checkSolution(resultMin, resultMax) ;

		} while (store.propagationHasOccurred);

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
	public void impose(Store store) {
		z.putModelConstraint(this, getConsistencyPruningEvent(z));
		y.putModelConstraint(this, getConsistencyPruningEvent(y));
		x.putModelConstraint(this, getConsistencyPruningEvent(x));
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void removeConstraint() {
		z.removeConstraint(this);
		y.removeConstraint(this);
		x.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
		IntDomain Xdom = z.dom(), Ydom = y.dom(), Zdom = x.dom();

		return Xdom.singleton() && Ydom.singleton() && Zdom.singleton() &&
		    Zdom.min() == mod(Xdom.min(), Ydom.min());
	}

	@Override
	public String toString() {

		return id() + " : XmodYeqZ(" + x + ", " + y + ", " + z + " )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			z.weight++;
			y.weight++;
			x.weight++;
		}
	}

	String checkSolution(int resultMin, int resultMax) {
		String result = null;

		if (z.singleton() && y.singleton() && x.singleton()) {
			result = "Operation mod does not hold " + x + " mod " + y + " = " + z + "(result "+resultMin+".."+resultMax;
			for (int i=resultMin; i<=resultMax; i++) {
				if ( i*y.value() + z.value() == x.value() )
					result = null;
			}
		}
		else
			result = null;
		return result;
	}

    int div(int a, int b) {
	return (int)Math.floor((float)a / (float)b);
    }

    int mod(int a, int b) {
	return a - div(a, b) * b;
    }
}
