/**
 *  AdisjointB.java 
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

import org.jacop.constraints.Constraint;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * The disjoint set constraint makes sure that two set variables
 * do not contain any common element.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class AdisjointB extends Constraint {

	static int IdNumber = 1;

	/**
	 * It specifies set variable a.
	 */
	public SetVar a;
	
	/**
	 * It specifies set variable b.
	 */
	public SetVar b;

	/**
	 * It specifies if the constrain attempts to perform expensive and yet 
	 * unlikely propagation due to cardinality information. 
	 */
	public boolean performCardinalityReasoning = false;

	private boolean aHasChanged = true;
	private boolean bHasChanged = true;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"a", "b"};

	/**
	 * It constructs a disjont set constraint to restrict the domains of the variables A and B.
	 * 
	 * @param a variable that is restricted to not have any element in common with b.
	 * @param b variable that is restricted to not have any element in common with a.
	 */
	public AdisjointB(SetVar a, SetVar b) {
		
		assert (a != null) : "Variable a is null";
		assert (b != null) : "Variable b is null";

		numberId = IdNumber++;
		numberArgs = 1;
		
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
		 * Consistency of the constraint A disjoint with B. 
		 * 
		 * lubA = lubA \ glbB
		 * 
		 * lubB = lubB \ glbA
		 */

		 /** For all sets, A, B apply the rules as specified for A below. 
		 * 
		 * inLUB() functions update cardinalities too if lub has changed.
		 * #A.in(#glbA, #lubA).
		 * 
		 * If #glb is already equal to maximum allowed cardinality then set is specified by glb.
		 * if (#glbA == #A.max()) then A = glbA

		 * If #lub is already equal to minimum allowed cardinality then set is specified by lub. 
		 * if (#lubA == #A.min()) then A = lubA
		 */

		// A.lub = 1+2+4+5, A.glb = 4+5
		if (bHasChanged)
			a.domain.inLUB(store.level, a, a.domain.lub().subtract( b.domain.glb() ) );

		// B.lub = 2+3+7+8, B.glb = 7+8
		if (aHasChanged)
			b.domain.inLUB(store.level, b, b.domain.lub().subtract( a.domain.glb()) ); 

		
		if (performCardinalityReasoning) {
			// TODO implement cardinality reasoning.
			/**
			 *  Cardinality reasoning. 
			 * 
			 * Note : that rules above ensure that (6) is empty. Only 1, 2, 3, 4, and 8
			 * are not empty. 
			 * 
			 * For B)
			 * 
			 * B.min() - (7+8+3 =(here) #glbB + (3) ) - how many elements from B restricts what can be used by A. 
			 * 
			 * (1+4) + (2+5) - max (0, B.min() - (7+8+3) )
			 * #A.inMax( (1+4) + (2+5) - max (0, B.min() - (7+8+3) ) )
			 */

			int maxSizeOfIntersection = -1;

			int elementsReservedForB = b.domain.card().min();

			if (elementsReservedForB > 0) {
				// how many still do we need to reserve after removing what is already within B. 
				elementsReservedForB -= b.domain.glb().getSize();

				if (elementsReservedForB > 0) {
					maxSizeOfIntersection = a.domain.lub().sizeOfIntersection(b.domain.lub());
					assert (maxSizeOfIntersection == a.domain.lub().intersect(b.domain.lub()).getSize() ) : "sizeOfIntersection not properly implemented";

					// how many elements can be added to B without affecting the cardinality of A = #(3).
					// subtract from elementsReservedForB
					elementsReservedForB -= ( b.domain.lub().getSize() - b.domain.glb().getSize() - maxSizeOfIntersection );

					// now elementsReservedForB hold number of elements required for B from aLUB /\ bLUB 

					// TODO, check if that actually does any propagation, under what conditions? 
					a.domain.inCardinality(store.level, a, 0, a.domain.lub().getSize() - elementsReservedForB);
				}
			}

			/** For A)
			 * 
			 * (8+3) + (2+7) - max(0, A.min() - (1+4+5)) 
			 * #B.inMax( (8+3) + (2+7) - max(0, A.min() - (1+4+5)) )
			 * 
			 */

			int elementsReservedForA = a.domain.card().min();

			if (elementsReservedForA > 0) {
				// how many still do we need to reserve after removing what is already within B. 
				elementsReservedForA -= a.domain.glb().getSize();

				if (elementsReservedForA > 0) {

					if (maxSizeOfIntersection == -1) {
						maxSizeOfIntersection = b.domain.lub().sizeOfIntersection(a.domain.lub());
						assert (maxSizeOfIntersection == b.domain.lub().intersect(a.domain.lub()).getSize() ) : "sizeOfIntersection not properly implemented";
					}

					// how many elements can be added to A without affecting the cardinality of B = #(1).
					// subtract from elementsReservedForA
					elementsReservedForA -= ( a.domain.lub().getSize() - a.domain.glb().getSize() - maxSizeOfIntersection );

					// now elementsReservedForA hold number of elements required for A from aLUB /\ bLUB 

					// TODO, check if that actually does any propagation, under what conditions? 
					b.domain.inCardinality(store.level, b, 0, b.domain.lub().getSize() - elementsReservedForA);
				}
			}

		}
		
		aHasChanged = false;
		bHasChanged = false;
	
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
		
		a.putModelConstraint(this,getConsistencyPruningEvent(a));
		b.putModelConstraint(this,getConsistencyPruningEvent(b));

		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void removeConstraint() {
		a.removeConstraint(this);
		b.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
		
		return !a.domain.lub().isIntersecting(b.domain.lub());

	}

	@Override
	public String toString() {
		return id() + " : AdisjointB(" + a + ", " + b +" )";
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
