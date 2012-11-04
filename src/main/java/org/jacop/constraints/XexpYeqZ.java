/**
 *  XexpYeqZ.java 
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
 * Constraint X ^ Y #= Z
 * 
 * Boundary consistecny is used.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 3.1
 */

public class XexpYeqZ extends Constraint {

	static int idNumber = 1;

	/**
	 * It specifies the variable x in equation x^y = z.
	 */
	public IntVar x;

	/**
	 * It specifies the variable y in equation x^y = z.
	 */
	public IntVar y;
	
	/**
	 * It specifies the variable z in equation x^y = z.
	 */
	public IntVar z;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"x", "y", "z"};

	/**
	 * It constructs constraint X^Y=Z.
	 * @param x variable x.
	 * @param y variable y.
	 * @param z variable z.
	 */
	public XexpYeqZ(IntVar x, IntVar y, IntVar z) {
		
		assert (x != null) : "Variable x is null";
		assert (y != null) : "Variable y is null";
		assert (z != null) : "Variable z is null";

		assert (x.min() >= 0) : "Variable x has a domain which allows negative values";
		assert (y.min() > 0) : "Variable y has a domain which allows negative values and zero";
		assert (z.min() >= 0) : "Variable z has a domain which allows negative values";
		
		numberId = idNumber++;
		numberArgs = 3;
		
		this.x = x;
		this.y = y;
		this.z = z;
		
	}

	double aLog(double a, double x) {
		return Math.log(x) / Math.log(a);
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

		double xMin, xMax, yMin, yMax, zMin, zMax;
		
		do {
			
			store.propagationHasOccurred = false;

			// compute bounds for x
			    xMin = Math.max(Math.pow(z.min(), 1.0 / y.max()), x.min());
			    xMax = Math.min(Math.pow(z.max(), 1.0 / y.min()), x.max());

			// compute bounds for y
			if (x.max()==0 || z.min()==0)
			    yMin = y.min();
			else
			    if (x.max() != 1)
				yMin = Math.max(aLog(x.max(), z.min()), y.min());
			    else
				yMin = y.min();
			if (x.min()==0 || z.max()==0)
			    yMax = y.max();
			else 
			    if (x.min() != 1)
				yMax = Math.min(aLog(x.min(), z.max()), y.max());
			    else
				yMax = y.max();

			// compute bounds for z
			zMin = Math.max(Math.pow(x.min(), y.min()), z.min());
			zMax = Math.min(Math.pow(x.max(), y.max()), z.max());

			if ((int) Math.floor(xMin) > (int) Math.ceil(xMax))
			    throw Store.failException;
			else
			    x.domain.in(store.level, x, (int) Math.floor(xMin), (int) Math.ceil(xMax) );

			y.domain.in(store.level, y, (int) Math.floor(yMin), (int) Math.ceil(yMax) );

			if ((int) Math.floor(zMin) > (int) Math.ceil(zMax))
			   throw Store.failException;
			else
			    z.domain.in(store.level, z, (int) Math.floor(zMin), (int) Math.ceil(zMax) );
			
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
	public void impose(Store Store) {
		x.putModelConstraint(this, getConsistencyPruningEvent(x));
		y.putModelConstraint(this, getConsistencyPruningEvent(y));
		z.putModelConstraint(this, getConsistencyPruningEvent(z));
		Store.addChanged(this);
		Store.countConstraint();
	}

	@Override
	public void removeConstraint() {
		x.removeConstraint(this);
		y.removeConstraint(this);
		z.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
		IntDomain xDom = x.dom(), yDom = y.dom(), zDom = z.dom();
		return xDom.singleton() && yDom.singleton() && zDom.singleton()
				&& Math.pow(xDom.min(), yDom.min()) == zDom.min();
	}

	@Override
	public String toString() {

		return id() + " : XexpYeqZ(" + x + ", " + y + ", " + z + " )";

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
