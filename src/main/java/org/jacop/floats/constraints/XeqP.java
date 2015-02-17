/**
 *  XeqP.java 
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

import org.jacop.constraints.Constraint;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;

/**
 * Constraints X #= P for X and P floats
 * 
 * Domain consistency is used.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class XeqP extends Constraint {

	static int idNumber = 1;

	/**
	 * It specifies a left hand variable in equality constraint. 
	 */
	public IntVar x;

	/**
	 * It specifies a right hand variable in equality constraint. 
	 */
	public FloatVar p;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"x", "p"};

	/**
	 * It constructs constraint X = P.
	 * @param x variable x.
	 * @param p variable p.
	 */
	public XeqP(IntVar x, FloatVar p) {

		assert (x != null) : "Variable x is null";
		assert (p != null) : "Variable p is null";

		numberId = idNumber++;
		numberArgs = 2;

		this.x = x;
		this.p = p;
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(2);

		variables.add(x);
		variables.add(p);

		return variables;
	}

	@Override
	public void consistency(Store store) {

	    do {
			
		// domain consistency
		int xMin;
		if (Math.abs(p.min()) < (double)IntDomain.MaxInt)
		    xMin = (int)( Math.round(Math.ceil(p.min())) );
		else
		    xMin = IntDomain.MinInt;

		int xMax;
		if (Math.abs(p.max()) < (double)IntDomain.MaxInt)
		    xMax = (int)( Math.round(Math.floor(p.max())) ) ;
		else
		    xMax = IntDomain.MaxInt;

		if (xMin > xMax) {
		    int t = xMax;
		    xMax = xMin;
		    xMin = t;
		}

		x.domain.in(store.level, x, xMin, xMax);
			
		store.propagationHasOccurred = false;

		p.domain.in(store.level, p, x.min(), x.max());

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
		return IntDomain.ANY;
	}

	@Override
	public void impose(Store store) {
		x.putModelConstraint(this, getConsistencyPruningEvent(x));
		p.putModelConstraint(this, getConsistencyPruningEvent(p));
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void removeConstraint() {
		x.removeConstraint(this);
		p.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
	    return x.singleton() && p.singleton() && 
		x.min() <= p.max() && x.max() >= p.min();
	}

	@Override
	public String toString() {
		return id() + " : XeqP(" + x + ", " + p + " )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			x.weight++;
			p.weight++;
		}
	}

	// @Override
	// public int getNestedPruningEvent(Var var, boolean mode) {

	// 	// If consistency function mode
	// 	if (mode) {
	// 		if (consistencyPruningEvents != null) {
	// 			Integer possibleEvent = consistencyPruningEvents.get(var);
	// 			if (possibleEvent != null)
	// 				return possibleEvent;
	// 		}
	// 		return IntDomain.ANY;
	// 	}

		// If notConsistency function mode
		// else {
		// 	if (notConsistencyPruningEvents != null) {
		// 		Integer possibleEvent = notConsistencyPruningEvents.get(var);
		// 		if (possibleEvent != null)
		// 			return possibleEvent;
		// 	}
		// 	return IntDomain.GROUND;
		// }

	// }

	// @Override
	// public int getNotConsistencyPruningEvent(Var var) {

	// 	// If notConsistency function mode
	// 	if (notConsistencyPruningEvents != null) {
	// 		Integer possibleEvent = notConsistencyPruningEvents.get(var);
	// 		if (possibleEvent != null)
	// 			return possibleEvent;
	// 	}
	// 	return IntDomain.GROUND;
		
	// }

	// @Override
	// public void notConsistency(Store store) {

	// 	if (p.singleton())
	// 		x.domain.inComplement(store.level, x, p.value());
		
		
	// 	if (x.singleton())
	// 		p.domain.inComplement(store.level, p, x.value());

	// }

	// @Override
	// public boolean notSatisfied() {

	// 	return ! x.domain.isIntersecting(p.domain);

	// }
}
