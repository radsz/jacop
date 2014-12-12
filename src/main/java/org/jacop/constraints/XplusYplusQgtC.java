/**
 *  XplusYplusQgtC.java 
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
 * Constraint X + Y + Q > C
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class XplusYplusQgtC extends PrimitiveConstraint {

	static int counter = 1;

	/**
	 * It specifies variable x in constraint x+y+q > c.
	 */
	public IntVar x;

	/**
	 * It specifies variable y in constraint x+y+q > c.
	 */
	public IntVar y;

	/**
	 * It specifies variable q in constraint x+y+q > c.
	 */
	public IntVar q;

	/**
	 * It specifies constant c in constraint x+y+q > c.
	 */
	int c;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"x", "y", "q", "c"};

	/**
	 * It creates X+Y+Q>=C constraint.
	 * @param x variable x.
	 * @param y variable y.
	 * @param q variable q.
	 * @param c constant c.
	 */
	public XplusYplusQgtC(IntVar x, IntVar y, IntVar q, int c) {
		
		assert (x != null) : "Variable x is null";
		assert (y != null) : "Variable y is null";
		assert (q != null) : "Variable q is null";

		numberId = counter++;
		numberArgs = 3;
		
		this.x = x;
		this.y = y;
		this.q = q;
		this.c = c;
		
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(3);

		variables.add(x);
		variables.add(y);
		variables.add(q);
		return variables;
	}

	@Override
	public void consistency(Store store) {


		do {
			
			store.propagationHasOccurred = false;
			
			x.domain.inMin(store.level, x, c - y.max() - q.max() + 1);

			y.domain.inMin(store.level, y, c - x.max() - q.max() + 1);

			q.domain.inMin(store.level, q, c - x.max() - y.max() + 1);

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
			return IntDomain.BOUND;
	}

	@Override
	public void impose(Store store) {

		x.putModelConstraint(this, getConsistencyPruningEvent(x));
		y.putModelConstraint(this, getConsistencyPruningEvent(y));
		q.putModelConstraint(this, getConsistencyPruningEvent(q));
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void notConsistency(Store store) {

		do {
			
			store.propagationHasOccurred = false;
			
			x.domain.inMax(store.level, x, c - y.min() - q.min());
			y.domain.inMax(store.level, y, c - x.min() - q.min());
			q.domain.inMax(store.level, q, c - x.min() - y.min());
		
		} while (store.propagationHasOccurred);
		
	}

	@Override
	public boolean notSatisfied() {
		return x.max() + y.max() + q.max() <= c;
	}

	@Override
	public void removeConstraint() {
		x.removeConstraint(this);
		y.removeConstraint(this);
		q.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
		return x.min() + y.min() + q.min() > c;
	}

	@Override
	public String toString() {

		return id() + " : XplusYplusQgtC(" + x + ", " + y + ", " + q + ", " + c
				+ " )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			x.weight++;
			y.weight++;
			q.weight++;
		}
	}
}
