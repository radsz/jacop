/**
 *  AinS.java 
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
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It creates a constraint that makes sure that value of the variable A is included within 
 * a provided set. 
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class AinS extends PrimitiveConstraint {

	static int idNumber = 1;

	/**
	 * It specifies set variable a. 
	 */
	public SetVar a;
	
	/**
	 * It specifies set which must contain the value of set variable A.
	 */
	public IntDomain set;
	
	/**
	 * It specifies if the inclusion relation is strict.
	 */
	public boolean strict;
	
	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"a", "b", "strict"};

	/**
	 * It constructs a constraint that makes sure that value of set variable a is contained
	 * within a provided set. 
	 * 
	 * @param a variable that is restricted to be included within a provided set.
	 * @param set set that is restricted to contain the value of set variable a.
	 */
	public AinS(SetVar a, IntDomain set) {
		this(a, set, false);
	}
	/**
	 * It constructs a constraint that makes sure that value of set variable a is contained
	 * within a provided set. 
	 * 
	 * @param a variable that is restricted to be included within a provided set.
	 * @param set set that is restricted to contain the value of set variable a.
	 */
	public AinS(SetVar a, IntDomain set, boolean strict) {

		assert(a != null) : "Variable A is null";
		assert(set != null) : "Set B is null";

		numberId = idNumber++;
		numberArgs = 1;
		
		this.a = a;
		this.set = set;
		this.strict = strict;

	}


	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(2);

		variables.add(a);

		return variables;
	}

	@Override
	public void consistency(Store store) {

		/**
		 * Consistency of the constraint A in B. 
		 * 
		 * B can not be an empty set. 
		 * 
		 * T1. 
		 * glbA = glbA
		 * lubA = lubA /\ S
		 * 
		 */

		a.domain.inLUB(store.level, a, set);
				
		if (strict && set.getSize() - 1 == a.domain.glb().getSize())
			a.domain.inLUBComplement(store.level, a, set.subtract(a.domain.glb()).value());
		
	}

	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
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
	public void removeConstraint() {
		a.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
		
		return a.domain.lub().lex(set) < 0 && a.singleton();
		
	}

	@Override
	public String toString() {
		return id() + " : AinS(" + a + " '< "+ set + ")";
	}

	@Override
	public void increaseWeight() {
		a.weight++;
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
	public int getNotConsistencyPruningEvent(Var var) {
		
		if (notConsistencyPruningEvents != null) {
			Integer possibleEvent = notConsistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return SetDomain.ANY;

	}


	@Override
	public void notConsistency(Store store) {

		// TODO, test it properly.
		
		if (a.domain.lub().getSize() > set.getSize() + 1)
			return;
		
		if (!set.contains(a.domain.glb()))
			return;
		
		IntDomain result = a.domain.lub().subtract(set);

		if (result.isEmpty())
			if (strict) {
				if (a.domain.lub().getSize() < set.getSize())
					throw Store.failException;
				else {
					a.domain.inGLB(store.level, a, a.domain.lub());
				}
			}
			else
				throw Store.failException;
		
		if (!strict && result.getSize() == 1 ) {
			// to remain inconsistency the last value which can make this constraint 
			// inconsistent must be added to GLB so it becomes notSatisfied.
			a.domain.inGLB(store.level, a, result.value());
		}

		if (strict && result.getSize() == 1 && a.domain.lub().getSize() - 1 < set.getSize()) {
			a.domain.inGLB(store.level, a, result.value());			
		}
		
	}


	@Override
	public boolean notSatisfied() {

		return !set.contains(a.domain.glb()) || (strict && a.domain.glb().eq(set));

	}	

}
