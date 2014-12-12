/**
 *  AeqB.java 
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
 * It creates an equality constraint to make sure that two set variables
 * have the same value. 
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class AeqB extends PrimitiveConstraint {

	static int idNumber = 1;

	/**
	 * It specifies set variable a, which must be equal to set variable b. 
	 */
	public SetVar a;
	
	/**
	 * It specifies set variable b, which must be equal to set variable a.
	 */
	public SetVar b;

	private boolean aHasChanged = true;
	private boolean bHasChanged = true;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"a", "b"};

	/**
	 * It constructs an AeqB constraint to restrict the domain of the variables.
	 * @param a variable a restricted to be equal to b.
	 * @param b variable b restricted to be equal to a.
	 */
	public AeqB(SetVar a, SetVar b) {

		assert(a != null) : "Variable a is null";
		assert(b != null) : "Variable b is null";
		
		numberId = idNumber++;
		numberArgs = 2;
		
		this.a = a;
		this.b = b;
		
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(2);

		variables.add(a);
		variables.add(b);
		return variables;
	}

	@Override
	public void consistency(Store store) {
		
		/**
		 * It computes the consistency of the constraint. 
		 * 
		 * If two set variables are to be equal then they
		 * are always reduced to the intersection of their domains. 
		 * 
		 * glbA = glbA \/ glbB
		 * glbB = glbA \/ glbB
		 * 
		 * lubA = lubA /\ lubB
 		 * lubB = lubA /\ lubB
 		 * 
 		 * 
		 */

		// if (bHasChanged)
			a.domain.in(store.level, a, b.dom());

		// if (aHasChanged)
			b.domain.in(store.level, b, a.dom());
		
		a.domain.inCardinality(store.level, a, b.domain.card().min(), b.domain.card().max());
		b.domain.inCardinality(store.level, b, a.domain.card().min(), a.domain.card().max());
	
		aHasChanged = false;
		bHasChanged = false;
		
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
		b.putModelConstraint(this, getConsistencyPruningEvent(b));
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void notConsistency(Store store) {
	    
		if(a.singleton() && 
		   b.singleton() && 
		   a.dom().glb().eq(b.dom().glb()))
	    	throw Store.failException;
		
	}

	@Override
	public boolean notSatisfied() {
		
		if(!a.domain.lub().contains(b.domain.glb()) 
		   || !b.domain.lub().contains(a.domain.glb()))
			return true;
		
		if(a.singleton() 
		   && b.singleton() 
		   && !a.domain.glb().eq(b.domain.glb()))
			return true;
		
		return false;
	}

	@Override
	public void removeConstraint() {
		a.removeConstraint(this);
		b.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
		
		if(a.singleton() && 
		   b.singleton() && 
		   a.domain.glb().eq(b.domain.glb()))
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
		return id() + " : AeqB(" + a + ", " + b + " )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			a.weight++;
			b.weight++;
		}
	}	

	@Override
	public void queueVariable(int level, Var variable) {
		
		if (variable == a) {
			aHasChanged = true;
			return;
		}

		if (variable == b) {
			bHasChanged = true;
			return;
		}
		
	}
}
