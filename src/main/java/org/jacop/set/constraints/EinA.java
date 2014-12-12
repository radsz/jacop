/**
 *  EinA.java 
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
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * 
 * It constructs a constraint which makes sure that a given element is 
 * in the domain of the set variable.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class EinA extends PrimitiveConstraint {

	static int idNumber = 1;

	/**
	 * It specifies the element which must be present in the set variable.
	 */
	public int element;

	/**
	 * It specifies the set variable which must contain a specified element.
	 */
	public SetVar a;

	/**
	 * It specifies if the inclusion relation is strict.
	 */
	public boolean strict = false;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"element", "a", "strict"};

	/**
	 * It constructs an eInA constraint to restrict the domain of the variable.
	 * @param a variable a for which the restriction is applied.
	 * @param element the element that has to be a part of the variable domain.
	 * @param strict it specifies if the inclusion relation is strict.
	 */
	public EinA(int element, SetVar a, boolean strict) {

		this(element, a);
		this.strict = strict;
		
	}

	/**
	 * It constructs an eInA constraint to restrict the domain of the variable.
	 * @param a variable a for which the restriction is applied.
	 * @param element the element that has to be a part of the variable domain.
	 */
	public EinA(int element, SetVar a) {

		assert (a != null) : "Variable a is null";

		numberId = idNumber++;
		numberArgs = 1;
		
		this.a = a;
		this.element = element;
		
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(1);

		variables.add(a);
		return variables;
	}

	@Override
	public void consistency(Store store) {

		a.domain.inGLB(store.level, a, element);

		if (strict)
			a.domain.inCardinality(store.level, a, 2, Integer.MAX_VALUE);
		
	}

	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		
		return SetDomain.GLB;		
		
	}

	@Override
	public int getNotConsistencyPruningEvent(Var var) {

		// If notConsistency function mode
		if (notConsistencyPruningEvents != null) {
			Integer possibleEvent = notConsistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return SetDomain.ANY;
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
		a.putModelConstraint(this, getConsistencyPruningEvent(a));
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void notConsistency(Store store) {

		// FIXME, TODO, check notConsistency() functions in other set constraints.
		a.domain.inLUBComplement(store.level, a, element);

	}

	@Override
	public boolean notSatisfied() {
		
		return !a.domain.lub().contains(element);
				
	}

	@Override
	public void removeConstraint() {
		a.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
		
		return a.domain.glb().contains(element);
		
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
			return SetDomain.ANY;
		}
		// If notConsistency function mode
		else {
			if (notConsistencyPruningEvents != null) {
				Integer possibleEvent = notConsistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return SetDomain.ANY;
		}
	}


	@Override
	public String toString() {
		return id() + " : EinA(" + element + ", " + a + " )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight)
			a.weight++;
	}	

}
