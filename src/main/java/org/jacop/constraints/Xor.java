/**
 *  Xor.java 
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
import org.jacop.util.SimpleHashSet;

/**
 * Xor constraint - xor("constraint", B).
 *
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Xor extends PrimitiveConstraint {

	static int idNumber = 1;

	/**
	 * It specifies constraint c, which status must satisfy xor relationship with variable b. 
	 */
	public PrimitiveConstraint c;

	/**
	 * It specifies variable b, which boolean status must satisfy xor relationship with status of constraint c. 
	 */
	public IntVar b;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"c", "b"};

	/**
	 * It constructs a xor constraint.
	 * @param c constraint c.
	 * @param b boolean variable b.
	 */
	public Xor(PrimitiveConstraint c, IntVar b) {

		assert (c != null) : "Constraint c is null";
		assert (b != null) : "Variable b is null";
		assert (b.min() >= 0 && b.max() <= 1) : "Variable b = " + b + " has to have domain 0..1";

		if (b.min() < 0 || b.max() > 1)
			throw new IllegalArgumentException("Variable b in xor constraint nust have domain 0..1");

		numberId = idNumber++;
		numberArgs = (short) (1 + c.numberArgs);

		this.c = c;
		this.b = b;

	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(1);

		variables.add(b);
		variables.addAll(c.arguments());

		return variables;
	}

	@Override
	public void consistency(Store store) {

		// Does not need to loop on newPropagation since
		// the constraint C loops itself
		if (b.max() == 0)  // C must be true
			c.consistency(store);
		else if (b.min() == 1)  // C must be false
			c.notConsistency(store);
		else if (c.satisfied())
			b.domain.in(store.level, b, 0, 0);
		else if (c.notSatisfied())
			b.domain.in(store.level, b, 1, 1);

	}

	@Override
	public int getNestedPruningEvent(Var var, boolean mode) {

		return getConsistencyPruningEvent(var);

	}


	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}

		if (var == b)
			return IntDomain.GROUND;
		else {

			int eventAcross = -1;

			if (c.arguments().contains(var)) {
				int event = c.getNestedPruningEvent(var, true);
				if (event > eventAcross)
					eventAcross = event;
			}

			if (c.arguments().contains(var)) {
				int event = c.getNestedPruningEvent(var, false);
				if (event > eventAcross)
					eventAcross = event;
			}

			if (eventAcross == -1)
				return Domain.NONE;
			else
				return eventAcross;				
		}
	}


	@Override
	public int getNotConsistencyPruningEvent(Var var) {

		// If notConsistency function mode
		if (notConsistencyPruningEvents != null) {
			Integer possibleEvent = notConsistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		if (var == b)
			return IntDomain.GROUND;
		else {

			int eventAcross = -1;

			if (c.arguments().contains(var)) {
				int event = c.getNestedPruningEvent(var, true);
				if (event > eventAcross)
					eventAcross = event;
			}

			if (c.arguments().contains(var)) {
				int event = c.getNestedPruningEvent(var, false);
				if (event > eventAcross)
					eventAcross = event;
			}

			if (eventAcross == -1)
				return Domain.NONE;
			else
				return eventAcross;				
		}
	}

	@Override
	public void impose(Store store) {

		SimpleHashSet<Var> variables = new SimpleHashSet<Var>();

		variables.add(b);

		for (Var V : c.arguments())
			variables.add(V);

		while (!variables.isEmpty()) {
			Var V = variables.removeFirst();
			V.putModelConstraint(this, getConsistencyPruningEvent(V));
		}

		c.include(store);

		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void include(Store store) {
	    c.include(store);
	}

	@Override
	public void removeConstraint() {

		b.removeConstraint(this);

		for (Var V : c.arguments())
			V.removeConstraint(this);

	}

	@Override
	public boolean satisfied() {
		IntDomain Bdom = b.dom();
		return (Bdom.min() == 0 && c.satisfied())
		|| (Bdom.max() == 1 && c.notSatisfied());
	}

	@Override
	public String toString() {

		return id() + " : Xor(" + c + ", " + b + " )";
	}

	@Override
	public void notConsistency(Store store) {

		// Does not need to loop on newPropagation since
		// the constraint C loops itself
		if (b.max() == 0)  // C must be false
			c.notConsistency(store);
		else if (b.min() == 1) // C must be true
			c.consistency(store);
		else if (c.satisfied())
			b.domain.in(store.level, b, 1, 1);
		else if (c.notSatisfied())
			b.domain.in(store.level, b, 0, 0);

	}

	@Override
	public boolean notSatisfied() {
		IntDomain bDom = b.dom();
		return (bDom.min() == 1 && c.satisfied())
		|| (bDom.max() == 0 && c.notSatisfied());
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			b.weight++;
			c.increaseWeight();
		}
	}

}
