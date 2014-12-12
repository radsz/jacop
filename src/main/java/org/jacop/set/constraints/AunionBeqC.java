/**
 *  AunionBeqC.java 
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
 * It creates a constraint that makes sure that A union B is equal to C. 
 * A \/ B = C. 
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * 
 * @version 4.2
 */

public class AunionBeqC extends Constraint {

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
	 * It constructs an AunionBeqC constraint to restrict the domain of the variables A, B and C.
	 * 
	 * @param a 
	 * @param b 
	 * @param c variable that is restricted to be the union of a and b.
	 */
	
	public AunionBeqC(SetVar a, SetVar b, SetVar c) {

		assert (a != null) : "Variable a is null";
		assert (b != null) : "Variable b is null";
		assert (c != null) : "Variable c is null";

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

		do {
			
			store.propagationHasOccurred = false;

			boolean aHasChanged = this.aHasChanged;
			boolean bHasChanged = this.bHasChanged;
			boolean cHasChanged = this.cHasChanged;

			this.aHasChanged = false;
			this.bHasChanged = false;
			this.cHasChanged = false;

			SetDomain aDom = a.dom();
			SetDomain bDom = b.dom();
			SetDomain cDom = c.dom();

			/**
			 * It computes the consistency of the constraint. 
			 * 
			 * A /\ B = C
			 * 
			 * The list of rules to use.
			 * 
			 * T5.
			 * 
			 * glbA = glbA \/ ( glbC \ lubB )
			 * lubA = lubA /\ lubC
			 * 
			 * glbB = glbB \/ ( glbC \ lubA )
			 * lubB = lubB /\ lubC
			 */

			if (cHasChanged || bHasChanged)
				if (cDom.lub().getSize() > 0) {
					IntDomain glbA = cDom.glb().subtract(bDom.lub());
					if (glbA.getSize() > 0)
						a.domain.inGLB(store.level, a, glbA);
				}

			if (cHasChanged)
				a.domain.inLUB(store.level, a, cDom.lub());

			if (aHasChanged || cHasChanged)
				if (cDom.lub().getSize() > 0) {
					IntDomain glbB = cDom.glb().subtract(aDom.lub());
					if (glbB.getSize() > 0)
						b.domain.inGLB(store.level, b, glbB);
				}

			if (cHasChanged)
				b.domain.inLUB(store.level, b, cDom.lub());

			/**
			 * 
			 * T6.
			 * 
			 * glbC = glbC \/ glbA \/ glbB
			 * lubC = lubC /\ ( lubA \/ lubB )
			 */

			if (aHasChanged)
				c.domain.inGLB(store.level, c, aDom.glb());
			if (bHasChanged)
				c.domain.inGLB(store.level, c, bDom.glb());
			if (aHasChanged || bHasChanged)
				c.domain.inLUB(store.level, c, aDom.lub().union(bDom.lub()));

			/** 
			 * For all sets, A, B, C apply the rules as specified for A below. 
			 * 
			 * #A.in(#glbA, #lubA).
			 * 
			 * If #glb is already equal to maximum allowed cardinality then set is specified by glb.
			 * if (#glbA == #A.max()) then A = glbA
			 * If #lub is already equal to minimum allowed cardinality then set is specified by lub. 
			 * if (#lubA == #A.min()) then A = lubA
			 */

			if (performCardinalityReasoning) {
				/** Cardinality reasoning
				 * 
				 * For C) 
				 * 
				 * (4) + (8) - elements already in union 
				 * 
				 * max ( #A.min - (4), #B.min() - (8) ) - the minimum number of elements which have to be added to A or B which will end up in the union. 
				 * #A.min - (4) + #B.min() - (8) - (2+5+6+7) - the elements which have to be added minus what can be added at the same time to both sets.
				 * (4+5+6) + (6+7+8) - 6 - this is already taken care of as it does not contain other cardinalities only set operations. 
				 *  
				 * #C.inMin( max ( #A.min - (4), #B.min() - (8) ) )
				 * #C.inMin( #A.min - (4) + #B.min() - (8) - (2+5+6+7) )
				 */

				int sizeOf_4 = a.domain.glb().subtract(b.domain.lub()).getSize();
				int sizeOf_8 = b.domain.glb().subtract(a.domain.lub()).getSize();
				int maxLeft = a.domain.card().min() - sizeOf_4;
				int maxRight = b.domain.card().min() - sizeOf_8;

				c.domain.inCardinality(store.level, c, Math.max(maxLeft, maxRight),
						Integer.MAX_VALUE);

				int sizeOf_2_5_6_7 = a.domain.lub().subtract(b.domain.lub()).getSize();

				c.domain.inCardinality(store.level, c, maxLeft + maxRight - sizeOf_2_5_6_7, Integer.MAX_VALUE);

				/** Cardinality reasoning
				 * for A)
				 * 
				 * #C.min() - (2, 3, 7, 8) - elements required by C which can not be contributed by B without contributing to A. 
				 * 
				 * #A.inMin( #C.min() - (2, 3, 7, 8) )
				 * 
				 * #C.max() - (8)
				 * 
				 * #A.inMax( #C.max() - (8) );
				 *
				 */

				int sizeOf_2_3_7_8 = b.domain.lub().subtract(a.domain.glb()).getSize();

				a.domain.inCardinality(store.level, a, c.domain.card().min() - sizeOf_2_3_7_8,
						c.domain.card().max() - sizeOf_8);

				/** Cardinality reasoning
				 * for B)
				 * 
				 * #C.min() - (4) - (1) - elements required by C which can not be contributed by A without contributing to B. 
				 * 
				 * #B.inMin( #C.min() - (4) - (1) )
				 * 
				 * #C.max() - (4)
				 * 
				 * #B.inMax( #C.max() - (4) );
				 * 
				 */

				int sizeOf_1_2_4_5 = a.domain.lub().subtract(b.domain.glb()).getSize();

				b.domain.inCardinality(store.level, b, c.domain.card().min() - sizeOf_1_2_4_5,
						c.domain.card().max() - sizeOf_4);


				// FIXME, implement the cardinality based reasoning. 

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
		return (a.singleton() && b.singleton() && c.singleton() && a.domain.union(b.domain).eq(c.domain));
	}

	@Override
	public String toString() {
		return id() + " : AunionBeqC(" + a + ", " + b + ", " + c + " )";
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
