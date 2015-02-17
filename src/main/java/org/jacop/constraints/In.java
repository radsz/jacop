/**
 *  In.java 
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

import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Constraints X to belong to a specified domain. 
 * 
 * Domain consistency is used.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class In extends PrimitiveConstraint {

	static int IdNumber = 1;

	/**
	 * It specifies variable x whose domain must lie within a specified domain.
	 */
	public IntVar x;

	/**
	 * It specifies domain d which restricts the possible value of the specified variable.
	 */
	public IntDomain dom;
	
	/**
	 * It specifies all the values which can not be taken by a variable.
	 */
	private IntDomain DomComplement;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"x", "dom"};

	/**
	 * It constructs an In constraint to restrict the domain of the variable.
	 * @param x variable x for which the restriction is applied.
	 * @param dom the domain to which the variables domain is restricted.
	 */
	public In(IntVar x, IntDomain dom) {
	
		assert (x != null) : "Variable x is null";
		assert (dom != null) : "Domain dom is null";
		
		numberId = IdNumber++;
		numberArgs = 1;
		
		this.x = x;
		this.dom = dom;
		this.DomComplement = dom.complement();
		
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(1);

		variables.add(x);
		return variables;
	}


	@Override
	public void consistency(Store store) {
		x.domain.in(store.level, x, dom);
		
		removeConstraint();
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
		x.putModelConstraint(this, getConsistencyPruningEvent(x));
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void notConsistency(Store store) {
	    // wrong it only does not need to be included in dom
	    // x.domain.in(store.level, x, DomComplement);

	    if (dom.contains(x.domain))
		throw Store.failException;
	}

	@Override
	public boolean notSatisfied() {
	    return !x.domain.isIntersecting(dom);
		// !dom.contains(x.domain);
	}

	@Override
	public void removeConstraint() {
		x.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
	    return x.singleton() && 
		dom.contains(x.domain);
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
			return IntDomain.ANY;
		}
		// If notConsistency function mode
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
	public String toString() {
		return id() + " : In(" + x + ", " + dom + " )";
	}


	@Override
	public Constraint getGuideConstraint() {
		return new XeqC(x, x.min());
	}

	@Override
	public int getGuideValue() {
		return x.min();
	}

	@Override
	public Var getGuideVariable() {
		return x;
	}

	@Override
	public void supplyGuideFeedback(boolean feedback) {
	}

    @Override
	public void increaseWeight() {
		if (increaseWeight) {
			x.weight++;
		}
	}	
	
}
