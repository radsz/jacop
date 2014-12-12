/**
 *  AeqS.java 
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
 * It creates an equality constraint to make sure that a set variable
 * is equal to a given set. 
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * 
 * @version 4.2
 */

public class AeqS extends PrimitiveConstraint {

	static int idNumber = 1;

	/**
	 * It specifies set variable a, which must be equal to set variable b. 
	 */
	public SetVar a;
	
	/**
	 * It specifies the set which must be equal to set variable a.
	 */
	public IntDomain set;

	/**
	 * It specifies the size of b. 
	 */
	int sizeOfB;
	
	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"a", "set"};

	/**
	 * It constructs an AeqS constraint to restrict the domain of the variables.
	 * @param a variable a that is forced to be equal to a specified set value.
	 * @param set it specifies the set to which variable a must be equal to.  
	 */
	public AeqS(SetVar a, IntDomain set) {

		assert(a != null) : "Variable A is null";
		assert(set != null) : "Set value is null";
		
		numberId = idNumber++;
		numberArgs = 1;
		
		this.a = a;
		this.set = set;
		this.sizeOfB = set.getSize();
		
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
		 * It computes the consistency of the constraint. 
		 * 
		 * If a set variables is to be equal to the set 
		 * then it is enough to perform the following once. 
		 * 
		 * glbA = s;
		 * lubA = s;
		 * 
		 */
		
		a.domain.inValue(store.level, a, set);

	}

	@Override
	public int getConsistencyPruningEvent(Var var) {

		if (notConsistencyPruningEvents != null) {
			Integer possibleEvent = notConsistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return SetDomain.ANY;
	}

	@Override
	public int getNotConsistencyPruningEvent(Var var) {

		if (notConsistencyPruningEvents != null) {
			Integer possibleEvent = notConsistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return SetDomain.GROUND;
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

	    if(a.singleton() && a.dom().glb().eq(set))
	    	throw Store.failException;
	
	    if (sizeOfB == a.domain.glb().getSize() + 1 
	    	&& sizeOfB == a.domain.lub().getSize()
	    	&& set.contains(a.domain.glb())) {
	    	int value = a.domain.lub().subtract(a.domain.glb()).value();
	    	if (set.contains(value))
	    		a.domain.inLUBComplement(store.level, a, value);
	    	else
	    		a.domain.inValue(store.level, a, a.domain.lub());
	    }
	    
	}

	@Override
	public boolean notSatisfied() {
		
		if(!a.domain.lub().contains(set))
			return true;
		
		if(a.singleton() && !(a.domain.glb().eq(set)))
			return true;
		
		return false;
	}

	@Override
	public void removeConstraint() {
		
		a.removeConstraint(this);
		
	}

	@Override
	public boolean satisfied() {
		
		if(a.domain.singleton(set))
			return true;
		
		return false;
		
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
		return id() + " : AeqS(" + a + ", " + set + " )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight)
			a.weight++;
	}	

}
