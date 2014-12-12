/**
 *  AdiffBeqC.java 
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
 * It creates a constraints that subtracts from set variable A the 
 * elements from of the set variable B and assigns the result to set 
 * variable C. 
 * 
 * A \ B = C. 
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class AdiffBeqC extends Constraint {

	static int idNumber = 1;

	/**
	 * It specifies set variable a. 
	 */
	public SetVar a;

	/**
	 * It specifies set variable b. 
	 */
	public SetVar b;

	/**
	 * It specifies set variable c. 
	 */
	public SetVar c;

	/**
	 * It specifies if the constrain attempts to perform expensive and yet 
	 * unlikely propagation due to cardinality information. 
	 */
	public boolean performCardinalityReasoning = false;

	private boolean aHasChanged = true;
	private boolean bHasChanged = true;
	private boolean cHasChanged = true;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"a", "b", "c"};

	/**
	 * It constructs an AdiffBeqC constraint to restrict the domain of the variables A, B and C.
	 * 
	 * @param a set variable a 
	 * @param b set variable b
	 * @param c set variable that is restricted to be the set difference of a and b.
	 */
	public AdiffBeqC(SetVar a, SetVar b, SetVar c) {

		assert (a != null) : "Variable a is null";
		assert (b != null) : "Variable b is null";
		assert (c != null) : "Variable c is null";

		this.numberId = idNumber++;
		this.numberArgs = 3;

		this.a = a;
		this.b = b;
		this.c = c;

	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(2);

		variables.add(a);
		variables.add(b);
		variables.add(c);

		return variables;
	}

	@Override
	public void consistency(Store store) {

		do {
			
			store.propagationHasOccurred = false;

			boolean aHasChanged = this.aHasChanged;
			boolean bHasChanged = this.bHasChanged;
			boolean cHasChanged = this.cHasChanged;

			this.aHasChanged = false;
			this.bHasChanged = false;
			this.cHasChanged = false;

			/**
			 * It computes the consistency of the constraint. 
			 * 
			 * A \ B = C
			 * 
			 * The list of rules to use.
			 */


			/** T9 rule.
			 * 
			 * glbA = glbA \/ glbC
			 * lubA = lubA \ [ lubA \ [ lubC \/ lubB ] ]
			 */

			if (cHasChanged)
				a.domain.inGLB(store.level, a, c.domain.glb());

			if (bHasChanged || cHasChanged)
				a.domain.inLUB(store.level, a, b.domain.lub().union(c.domain.lub()));

			/** T10 rule.
			 * 
			 * glbB = glbB
			 * lubB = lubB \ glbC
			 */

			if (cHasChanged)
				b.domain.inLUB(store.level, b, b.domain.lub().subtract( c.domain.glb() ) );

			/** T11
			 * glbC = glbC \/ [ glbA \ lubB ]
			 * lubC = lubC /\ [ lubA \ glbB ] 
			 */

			if (aHasChanged || bHasChanged) {
				c.domain.inGLB(store.level, c, a.domain.glb().subtract(b.domain.lub()));
				c.domain.inLUB(store.level, c, a.domain.lub().subtract(b.domain.glb()));
			}

			// FIXME, TODO, implement cardinality based reasoning. 
			/** For all sets, A, B, C apply the rules as specified for A below. 
			 * 
			 * lA = min(#glbA, #A.min())
			 * rA = max(#lubA, #A.max())
			 * 
			 * #A.in(#glbA, #lubA).
			 * 
			 * If #glb is already equal to maximum allowed cardinality then set is specified by glb.
			 * if (#glbA == #A.max()) then A = glbA
			 * If #lub is already equal to minimum allowed cardinality then set is specified by lub. 
			 * if (#lubA == #A.min()) then A = lubA
			 *
			 */

			if (performCardinalityReasoning) {

				/** Cardinality reasoning. 
				 * 
				 *  For C)
				 *  
				 *  (2+5+6+7) - lubA /\ lubB - how many elements can be removed by B
				 *  (4) - glbA \ lubB - how many elements have to be in C. 
				 *  
				 *  #C.inMin( (4) + max( #A.min() - (4) - min( (2+5+6+7), #B.max() - (8) ) , 0)  );
				 *  
				 *  A.min - (4) - How many must be added. 
				 *  min( (2+7), B.max-8) how many can be added to B so they can cause removals from A.  
				 *  C.inMin( (4) + max(0, (A.min - (4)) - min ( 2+7, B.max - (8))) 
				 */

				// TODO, check the code below, so that is can fire and propagate properly.

				int aMinCard = a.domain.card().min();
				if (aMinCard > 0) {
					int sizeOf4 = a.domain.glb().subtract(b.domain.lub()).getSize();

					if (aMinCard - sizeOf4 > 0) {
						int sizeOf8 = b.domain.glb().getSize();
						if (sizeOf8 > 0) {
							sizeOf8 = b.domain.glb().subtract(a.domain.lub()).getSize();
						}
						int sizeOf2_7 = a.domain.lub().intersect(b.domain.lub()).subtract(a.domain.glb()).getSize();
						int min = b.domain.card().max() - sizeOf8;
						if (min > sizeOf2_7)
							min = sizeOf2_7;
						int max = aMinCard - sizeOf4 - min;
						if (max > 0) {
							c.domain.inCardinality(store.level, c, sizeOf4 + max, Integer.MAX_VALUE);
						}
					}
				}


				/** Cardinality reasoning. 
				 * 
				 *  For C)
				 *  
				 *  (1+2+4+5) - lubA \ glbB - how many elements can be placed in C. 
				 *  (6) - glbA /\ glbB - how many elements used in A are not placed in C. 
				 *  max( #B.min()-(8+3+7), 0) - how many elements in B are also in (1+2+4+5). 
				 *  
				 *  #C.inMax( min ( #A.max() - (6), (1+2+4+5) - max( #B.min()-(3+6+7+8), 0) ,  ) );
				 *  
				 *  
				 */

				int sizeOf6 = a.domain.glb().intersect(b.domain.glb()).getSize();
				int minLeft = a.domain.card().max() - sizeOf6;
				int sizeOf1_2_4_5 = a.domain.lub().subtract(b.domain.glb()).getSize();
				int minRight = sizeOf1_2_4_5;
				int max = b.domain.card().min();
				if (max > 0) {
					int sizeOf6_7_8 = b.domain.glb().getSize();
					max -= sizeOf6_7_8;
					if (max > 0) {
						int sizeOf3 = b.domain.lub().subtract(a.domain.lub()).subtract(b.domain.glb()).getSize();
						max -= sizeOf3;
						if (max > 0) {
							minRight -= max;
						}
					}
				}
				if (minLeft < minRight)
					c.domain.inCardinality(store.level, c, Integer.MIN_VALUE, minLeft);
				else
					c.domain.inCardinality(store.level, c, Integer.MIN_VALUE, minRight);


				/** Cardinality reasoning. 
				 * For B) 
				 * 
				 * (1+2+4+5) - how many elements can be placed in C. 
				 * (4+5) - minimum required contribution of A into C. 
				 * max( 0, (4+5)-#C.max()) - how many elements in required contribution are more than what is allowed by #C.
				 * #A.min()-(6+7) - minimum number of elements that must be put in A and are not taken care of by glbB. 
				 * max( 0, #A.min() - (6-7) - #C.max() ) - how many elements needs still to be taken out by B.  
				 * 
				 * #B.inMin( max ( (6+7+8)+max(0, (4+5)-#C.max()), (6+7+8) + max( 0, #A.min() - (6-7) - #C.max() ) );
				 * #B.inMin( (6+7+8) + max(0, 5-(#C.max()-4), #A.min() - (6-7) - #C.max() )
				 */

				int sizeOf_4_5 = a.domain.glb().subtract(b.domain.glb()).getSize();
				minLeft = b.domain.glb().getSize() + Math.max(0, sizeOf_4_5 - c.domain.card().max());
				minRight = a.domain.card().max() - c.domain.card().max();
				if (minLeft < minRight)
					minLeft = minRight;

				b.domain.inCardinality(store.level, c, b.domain.glb().getSize() + minLeft, Integer.MAX_VALUE);

				/** Cardinality reasoning.
				 * #C.min()-(1+4) - number of elements required from lubB to get minimum size C. 
				 * lubB - (#C.min() - (1+4)) - remaining elements after removing those required for C. 
				 * 
				 * #B.inMax( lubB - ( C.min()-(1+4) ) );
				 */

				int sizeOf1_4 = a.domain.lub().subtract(b.domain.lub()).getSize();
				int min = c.domain.card().min() - sizeOf1_4; 

				if (min > 0)
					b.domain.inCardinality(store.level, b, Integer.MIN_VALUE, b.domain.lub().getSize() - min);

				/** Cardinality reasoning. 
				 * 
				 * For A) 
				 * 
				 * #C.min() - requirement from C. 
				 * (6)      - elements from A not contributing to C but contributing to #A
				 * #B.min() - (2+3+7+8) - number of elements that B must eventually put in area (5) thus reducing current contribution of A. 
				 * 
				 * 
				 * #A.inMin( max( #C.min() + (6) + max(0, B.min()-(2+3+7+8)) , ?? ) );
				 * 
				 */

				min = c.domain.card().min() + b.domain.glb().intersect(a.domain.glb()).getSize();
				if (b.domain.lub().getSize() - a.domain.lub().getSize() < b.domain.card().min()) {
					min = min + Math.max(0, b.domain.card().min() - b.domain.lub().subtract(a.domain.glb()).getSize());
				}

				a.domain.inCardinality(store.level, a, min, Integer.MAX_VALUE);

				/** Cardinality reasoning. 
				 * 
				 * #A.inMax ( #C.max() + min (#B.max()-(8), (2+5+6+7) ) ) ;
				 * Triggering conditions :
				 * glbA, lubA, glbB, lubB, glbC, lubC
				 * 
				 * #A.BOUND, #B.BOUND, #C.BOUND.
				 * 
				 */

			}

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
		b.putModelConstraint(this, getConsistencyPruningEvent(b));
		c.putModelConstraint(this, getConsistencyPruningEvent(c));
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void removeConstraint() {
		a.removeConstraint(this);
		b.removeConstraint(this);
		c.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
		return (a.singleton() 
				&& b.singleton() 
				&& c.singleton() 
				&& a.domain.subtract(b.domain).eq(c.domain));
	}

	@Override
	public String toString() {
		return id() + " : AdiffBeqC(" + a + ", " + b + ", "+ c +" )";
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			a.weight++;
			b.weight++;
			c.weight++;
		}
	}	

	@Override
	public void queueVariable(int level, Var variable) {

		if (variable == a) {
			aHasChanged = true;
			return;
		} 
		else if (variable == b) {
			bHasChanged = true;
			return;
		} else if (variable == c) {
			cHasChanged = true;
			return;
		}

	}

}
