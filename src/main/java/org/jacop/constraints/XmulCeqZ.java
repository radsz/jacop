/**
 *  XmulCeqZ.java 
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
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.FailException;

/**
 * Constraint X * C #= Z
 * 
 * Boundary consistency is used.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 3.1
 */

public class XmulCeqZ extends PrimitiveConstraint {

	static int idNumber = 1;

	/**
	 * It specifies variable x in constraint x * c = z. 
	 */
	public IntVar x;

	/**
	 * It specifies constant c in constraint x * c = z. 
	 */
	public int c;

	/**
	 * It specifies variable x in constraint x * c = z. 
	 */
	public IntVar z;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"x", "c", "z"};

	/**
	 * It constructs a constraint X * C = Z.
	 * @param x variable x.
	 * @param c constant c.
	 * @param z variable z.
	 */
	public XmulCeqZ(IntVar x, int c, IntVar z) {

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
	public void consistency (Store store) {

	    if (c != 0)
		do {

		    store.propagationHasOccurred = false;
				
		    // Bounds for X
		    IntervalDomain xBounds = IntDomain.divIntBounds(z.min(), z.max(), c, c);

		    x.domain.in(store.level, x, xBounds);

		    // Bounds for Z
		    IntervalDomain zBounds = IntDomain.mulBounds(x.min(), x.max(), c, c);

		    z.domain.in(store.level, z, zBounds);
				
		} while (store.propagationHasOccurred);
	    else
		z.domain.in(store.level, z, 0, 0);
	}

	@Override
	public void notConsistency (Store store) {

	    if (c != 0) {

		if ( x.singleton() ) 

		    z.domain.inComplement(store.level, z, x.value()*c);

		if ( z.singleton() ) {
		    IntervalDomain xBounds;

		    try {
			xBounds = IntDomain.divIntBounds(z.min(), z.max(), c, c);
		    } catch (FailException e) {
			// z/c does not produce integer value; nothing to do since inequality holds
			return;
		    }

		    x.domain.inComplement(store.level, x, xBounds.value());
		}

	    }
	    else
		z.domain.inComplement(store.level, z, 0);
	}

	@Override
	public boolean satisfied() {
		IntDomain Xdom = x.dom(), Zdom = z.dom();
		return Xdom.singleton() && Zdom.singleton()
		&& Xdom.min() * c == Zdom.min();
	}

	@Override
	public boolean notSatisfied() {

	    return ! z.domain.isIntersecting(IntDomain.mulBounds(x.min(), x.max(), c, c));

	    // IntDomain Xdom = x.dom();
	    // IntDomain Zdom = z.dom();
	    // return Xdom.singleton() && Zdom.singleton() && Xdom.min() * c != Zdom.min();
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
			return IntDomain.GROUND;
		}

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
	public void removeConstraint() {
		x.removeConstraint(this);
		z.removeConstraint(this);
	}

	@Override
	public String toString() {

		return id() + " : XmulCeqZ(" + x + ", " + c + ", " + z + " )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			x.weight++;
			z.weight++;
		}
	}

}
