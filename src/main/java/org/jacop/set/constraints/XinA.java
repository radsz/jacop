/**
 *  XinA.java 
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

package org.jacop.set.constraints;

import java.util.ArrayList;

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It creates a constraint that makes sure that the value assigned to integer variable x is
 * included in the set assigned to the set variable a.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski. 
 * 
 * @version 4.2
 */

public class XinA extends PrimitiveConstraint {

	static int idNumber = 1;

	/**
	 * It specifies variable a.
	 */
	public IntVar x;
	
	/**
	 * It specifies variable b.
	 */
	public SetVar a;

	// private boolean aHasChanged = true;

	/**
	 * It specifies if the inclusion relation is strict.
	 */
	public boolean strict = false;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"x", "a", "strict"};

	/**
	 * It constructs an XinY constraint to restrict the domain of the variables X and Y.
	 * @param x variable x that is restriction to be a subset of y.
	 * @param a variable that is restricted to contain x.
	 * @param strict it specifies if the inclusion relation is strict.
	 */
	public XinA(IntVar x, SetVar a, boolean strict) {
		
		this(x, a);
		this.strict = strict;
		
	}

	/**
	 * It constructs an XinA constraint to restrict the domain of the variables X and A.
	 * @param x variable x that is restriction to be a subset of A.
	 * @param a variable that is restricted to contain x.
	 */
	public XinA(IntVar x, SetVar a) {
		
		assert(a != null) : "Variable a is null";
		assert(x != null) : "Variable x is null";

		this.numberId = idNumber++;
		this.numberArgs = 2;
		
		this.x = x;
		this.a = a;
		
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(2);

		variables.add(x);
		variables.add(a);

		return variables;
	}

	@Override
	public void consistency(Store store) {

			// if (aHasChanged)
				x.domain.in(store.level, x, a.domain.lub());

			if (strict)
				a.domain.inCardinality(store.level, a, 2, Integer.MAX_VALUE);				
			else
				a.domain.inCardinality(store.level, a, 1, Integer.MAX_VALUE);
			
			// if(x.singleton())
			// 	a.domain.inGLB(store.level, a, x.value());
			
			if (!x.domain.isIntersecting(a.domain.lub()))
				throw Store.failException;

			// aHasChanged = false;
			
	}

	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		
		if (var == x)
			return IntDomain.ANY;
		else
			return SetDomain.ANY;		
	}

	@Override
	public int getNotConsistencyPruningEvent(Var var) {

		// If notConsistency function mode
		if (notConsistencyPruningEvents != null) {
			Integer possibleEvent = notConsistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		
		if (var == x)
			return IntDomain.GROUND;
		else
			return SetDomain.GLB;		

	}

	@Override
	public String id() {
		if (id != null)
			return id;
		else
			return this.getClass().getSimpleName() + numberId;
	}

	@Override
	public void impose(Store store) {
		
		x.putModelConstraint(this, getConsistencyPruningEvent(x));
		a.putModelConstraint(this, getConsistencyPruningEvent(a));

		store.addChanged(this);
		store.countConstraint();
		
	}

	@Override
	public void notConsistency(Store store) {

		// if (x.singleton())
		// 	a.domain.inLUBComplement(store.level, a, x.value());
		
		IntDomain xDom = x.domain.subtract(a.domain.glb());
		
		if (xDom.getSize() == 0)
			throw Store.failException;
		
		x.domain.in(store.level, x, xDom);
		
	}

	@Override
	public boolean notSatisfied() {

		return !a.domain.lub().isIntersecting(x.domain);

	}

	@Override
	public void removeConstraint() {
		x.removeConstraint(this);
		a.removeConstraint(this);

	}

	@Override
	public boolean satisfied() {

		return a.domain.glb().contains(x.domain);
		
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
			
			if (var == x)
				return IntDomain.ANY;
			else
				return SetDomain.GLB;		

		}
		// If notConsistency function mode
		else {
			if (notConsistencyPruningEvents != null) {
				Integer possibleEvent = notConsistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			
			if (var == x)
				return IntDomain.GROUND;
			else
				return SetDomain.GLB;		

		}
	}


	@Override
	public String toString() {
		return id() + " : XinA(" + x + ", " + a + " )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			x.weight++;
			a.weight++;
		}
	}	

	
	@Override
	public void queueVariable(int level, Var variable) {
		
		// if (variable == a) {
		// 	aHasChanged  = true;
		// 	return;
		// }
		
	}
}
