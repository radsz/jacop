/**
 *  AintersectBeqC.java 
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
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It creates a constraint that makes sure that A intersected with B 
 * is equal to C. A /\ B = C. 
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class AintersectBeqC extends Constraint {

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
	 * It constructs an AintersectBeqC constraint.
	 * 
	 * @param a set variable a, which is being intersected with set variable b.
	 * @param b set variable b, which is being intersected with set variable a.
	 * 
	 * @param c variable that is restricted to be the intersection of a and b.
	 */
	public AintersectBeqC(SetVar a, SetVar b, SetVar c) {

		assert(a != null) : "Variable a is null";
		assert(b != null) : "Variable b is null";
		assert(c != null) : "Variable c is null";

		numberId = idNumber++;
		numberArgs = 3;
		
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

		// FIXME, TODO, implement cardinality reasoning as specified in the comments.

		/**
		 * It computes the consistency of the constraint. 
		 * 
		 * A /\ B = C
		 * 
		 * The list of rules to use.
		 * 
		 * T7
		 * 
		 * glbA = glbA /\ glbC
		 * lubA = lubA \ ( ( lubA /\ glbB) \ lubC )
		 * glbB = glbB /\ glbC
		 * lubB = lubB \ ( ( lubB /\ glbA) \ lubC )
		 * 
		 */

		do {
			
			store.propagationHasOccurred = false;
			
			boolean aHasChanged = this.aHasChanged;
			boolean bHasChanged = this.bHasChanged;
			boolean cHasChanged = this.cHasChanged;
			
			this.aHasChanged = false;
			this.bHasChanged = false;
			this.cHasChanged = false;
			
			if (cHasChanged)
				a.domain.inGLB(store.level, a, c.domain.glb());

			if (bHasChanged || cHasChanged) {
				IntDomain temp = b.domain.glb().subtract(c.domain.lub());
				if (!temp.isEmpty())
					a.domain.inLUB(store.level, a, a.domain.lub().subtract( temp ) );
			}

			if (cHasChanged)
				b.domain.inGLB(store.level, b, c.domain.glb());

			if (cHasChanged || aHasChanged) {
				IntDomain temp = a.domain.glb().subtract(c.domain.lub());
				if (!temp.isEmpty())
					b.domain.inLUB(store.level, b, b.domain.lub().subtract( temp ) );
			}

			/** T8 
			 * 
			 * glbC = glbC \/ ( glbA /\ glbB )
			 * lubC = lubC /\ lubA /\ lubB
			 * 
			 */

			if (bHasChanged || aHasChanged)
				c.domain.inGLB(store.level, c, a.domain.glb().intersect(b.domain.glb()));

			if (bHasChanged || aHasChanged)
				c.domain.inLUB(store.level, c, a.domain.lub().intersect(b.domain.lub()));

			if (performCardinalityReasoning) {
				/** For all sets, A, B, C apply the rules as specified for A below. 
				 * 
				 * #A.in(#glbA, #lubA).
				 * 
				 * If #glb is already equal to maximum allowed cardinality then set is specified by glb.
				 * if (#glbA == #A.max()) then A = glbA
				 * If #lub is already equal to minimum allowed cardinality then set is specified by lub. 
				 * if (#lubA == #A.min()) then A = lubA
				 */

				/** Cardinality reasoning. 
				 * 
				 * 
				 * for A) 
				 * 
				 * (4) - elements in A which can not be in B, therefore not in C. 
				 * 
				 * #A.inMin( (4) + #C.min() );
				 */

				int sizeOf4 = a.domain.glb().subtract(b.domain.lub()).getSize();
				a.domain.inCardinality(store.level, a, sizeOf4 + c.domain.card().min(), Integer.MAX_VALUE);

				/** Cardinality reasoning. 
				 * (2+5+6+7) - maximum size intersection 
				 * #B.max() - (8) - maximum number of elements from B which can still end up in the intersection.
				 * 
				 * #(7+6)-#C.max() - no of elements which can not be used by A. 
				 *  
				 * #A.inMax( #A.lub() - ( #(7+6) - #C.max() ) );
				 * 
				 */

				int sizeOf_6_7 = a.domain.lub().intersect(b.domain.glb()).getSize();
				if (sizeOf_6_7 > c.domain.card().max()) {
					int reserved = sizeOf_6_7 - c.domain.card().max();
					a.domain.inCardinality(store.level, a, Integer.MIN_VALUE, a.domain.lub().getSize() - reserved);
				}

				/** Cardinality reasoning. 
				 * for B) 
				 * 
				 * (8) - elements in B which can not be in A, therefore not in C. 
				 * 
				 * #B.inMin( (8) + #C.min() );
				 */

				int sizeOf8 = b.domain.glb().subtract(a.domain.lub()).getSize();
				b.domain.inCardinality(store.level, b, sizeOf8 + c.domain.card().min(), Integer.MAX_VALUE);

				/** Cardinality reasoning. 
				 * 
				 * (2+5+6+7) - maximum size intersection 
				 * #A.max() - (4) - maximum number of elements from A which can still end up in the intersection.
				 * 
				 * #B.inMax( (3+8) + min ( (2+5+6+7), #C.max() )   );
				 * #B.inMax( #A.max() - (4) )
				 */

				int sizeOf_5_6 = b.domain.lub().intersect(a.domain.glb()).getSize();
				if (sizeOf_5_6 > c.domain.card().max()) {
					int reserved = sizeOf_5_6 - c.domain.card().max();
					b.domain.inCardinality(store.level, b, Integer.MIN_VALUE, b.domain.lub().getSize() - reserved);
				}	

				/** Cardinality reasoning. 
				 * 
				 * for C) 
				 * 
				 * (6) + max( 0, max(0, #A.min() - (1+4)) + max(0, #B.min() - (3+8)) + (6) - (2+5+7+6)) - number of elements that must be in 6
				 * 
				 * #C.inMin( (6) + max( 0, max(0, #A.min() - (1+4)) + max(0, #B.min() - (3+8)) - (2+5+7)) );
				 */

				int sizeOf1_4 = a.domain.lub().subtract(b.domain.lub()).getSize();
				int sizeOf3_8 = b.domain.lub().subtract(a.domain.lub()).getSize();
				int sizeOf6 = a.domain.glb().intersect(b.domain.glb()).getSize();
				int sizeOf2_5_6_7 = a.domain.lub().intersect(b.domain.lub()).getSize();

				int max = Math.max(a.domain.card().min() - sizeOf1_4, 0) + 
				Math.max(b.domain.card().min() - sizeOf3_8, 0);

				max -= sizeOf6 + sizeOf2_5_6_7;
				if (max > 0)
					c.domain.inCardinality(store.level, c, sizeOf6 + max, Integer.MAX_VALUE);

				/** Cardinality reasoning. 
				 * #A.max() - (4) - all elements of A which may end up in the intersection.  
				 * #B.max() - (8) - all elements of B which may end up in the intersection. 
				 * 
				 * #C.inMax( min( #A.max() - (4), #B.max() - (8) )). 
				 * 
				 */

				c.domain.inCardinality(store.level, c, Integer.MIN_VALUE, a.domain.card().max() - sizeOf4);
				c.domain.inCardinality(store.level, c, Integer.MIN_VALUE, b.domain.card().max() - sizeOf8);

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
		a.putModelConstraint(this,getConsistencyPruningEvent(a));
		b.putModelConstraint(this,getConsistencyPruningEvent(b));
		c.putModelConstraint(this,getConsistencyPruningEvent(c));

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
		return a.singleton() 
			   && b.singleton() 
			   && c.singleton() 
			   && a.domain.intersect(b.domain).eq(c.domain);
	}

	@Override
	public String toString() {
		return id() + " : AintersectBeqC(" + a + ", " + b + ", " + c + " )";
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

		if (variable == b) {
			bHasChanged = true;
			return;
		}

		if (variable == c) {
			cHasChanged = true;
			return;
		}
		
	}

}
