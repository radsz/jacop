/**
 *  EqBool.java 
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * If all x's are equal to each other then result variable is equal 1. Otherwise, result variable 
 * is equal to zero. It restricts the domains of all variables to be either 0 or 1.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class EqBool extends PrimitiveConstraint {

	static int counter = 1;

	/**
	 * It specifies x variables in the constraint. 
	 */
	public IntVar [] list;

	/**
	 * It specifies variable result in the constraint. 
	 */
	public IntVar result;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"list", "result"};

	/**
	 * It constructs eqBool. 
	 * 
	 * @param list list of x's which must all be equal to the same value to make result equal 1.
	 * @param result variable which is equal 0 if x's contain different values. 
	 */
	public EqBool(IntVar [] list, IntVar result) {

		assert (list != null) : "List of x's is null";
		assert (result != null) : "Result variable is null";

		numberId = counter++;
		numberArgs = (short)(list.length + 1);

		this.list = new IntVar[list.length];
		for (int i = 0; i < list.length; i++) {
			assert (list[i] != null) : i + "-th element in the list is null";
			this.list[i] = list[i];
		}

		this.result = result;

		assert ( checkInvariants() == null) : checkInvariants();

	}

	/**
	 * It constructs eqBool. 
	 * 
	 * @param list list of variables which must all be equal to the same value to make result equal 1.
	 * @param result variable which is equal 0 if variables from list contain different values. 
	 */
	public EqBool(ArrayList<? extends IntVar> list, IntVar result) {

		numberId = counter++;
		numberArgs = (short)(list.size()+1);

		this.list = new IntVar[list.size()];
		for (int i = 0; i < this.list.length; i++) {
			assert (list.get(i) != null) : i + "-th element in the list is null";
			this.list[i] = list.get(i);
		}
		
		this.list = new IntVar[list.size()];

		for (int i = 0; i < this.list.length; i++)
			this.list[i] = list.get(i);

		this.result = result;

		assert ( checkInvariants() == null) : checkInvariants();

	}

	/**
	 * It checks invariants required by the constraint. Namely that
	 * boolean variables have boolean domain. 
	 * 
	 * @return the string describing the violation of the invariant, null otherwise.
	 */
	public String checkInvariants() {

		for (IntVar var : list)
			if (var.min() < 0 || var.max() > 1)
				return "Variable " + var + " does not have boolean domain";

		return null;
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(list.length + 1);

		variables.add(result);
		for (int i = 0; i < list.length; i++)
			variables.add(list[i]);
		return variables;
	}

	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return IntDomain.BOUND;
	}

	@Override
	public int getNotConsistencyPruningEvent(Var var) {

		// If notConsistency function mode
		if (notConsistencyPruningEvents != null) {
			Integer possibleEvent = notConsistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return IntDomain.GROUND;
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
			return IntDomain.GROUND;
		}
	}

	// registers the constraint in the constraint store
	@Override
	public void impose(Store store) {

		result.putModelConstraint(this, getConsistencyPruningEvent(result));

		for (Var V : list)
			V.putModelConstraint(this, getConsistencyPruningEvent(V));

		store.addChanged(this);
		store.countConstraint();

	}

	public void consistency(Store store) {

		int x1 = 0, x0 = 0, index_01 = 0;

		for (int i = 0; i < list.length; i++) {
			if (list[i].min() == 1) x1++;
			else
				if (list[i].max() == 0) x0++;
				else
					index_01 = i;
		}

		if (result.min() == 1) {

			if (x0 > 0)
				for (int i=0; i<list.length; i++)
					list[i].domain.in(store.level, list[i], 0, 0);
			if (x1 > 0)
				for (int i=0; i<list.length; i++)
					list[i].domain.in(store.level, list[i], 1, 1);

		}
		else {
			if (result.max() == 0) {
				if (x0 == 0 && x1 == list.length - 1)
					list[index_01].domain.in(store.level, list[index_01], 0, 0);
				if (x1 == 0 && x0 == list.length - 1)
					list[index_01].domain.in(store.level, list[index_01], 1, 1);
			}
		}

		if (x0 > 0 && x1 > 0)
			result.domain.in(store.level, result, 0, 0);

		if (x0 == list.length || x1 == list.length) 
			result.domain.in(store.level, result, 1, 1);

	}

	@Override
	public void notConsistency(Store store) {

		do {

			store.propagationHasOccurred = false;
			
			int x1 = 0, x0 = 0, index_01 = 0;

			for (int i = 0; i < list.length; i++) {
				if (list[i].min() == 1) x1++;
				else
					if (list[i].max() == 0) x0++;
					else
						index_01 = i;
			}

			if (result.min() == 1) {

				if (x0 == 0 && x1 == list.length - 1)
					list[index_01].domain.in(store.level, list[index_01], 0, 0);
				if (x1 == 0 && x0 == list.length - 1)
					list[index_01].domain.in(store.level, list[index_01], 1, 1);

			}
			else {
				if (result.max() == 0) {
					if (x0 > 0)
						for (int i=0; i<list.length; i++)
							list[i].domain.in(store.level, list[i], 0, 0);
					if (x1 > 0)
						for (int i=0; i<list.length; i++)
							list[i].domain.in(store.level, list[i], 1, 1);
				}
			}

			if (x0 > 0 && x1 > 0)
				result.domain.in(store.level, result, 1, 1);

			if (x0 == list.length || x1 == list.length) 
				result.domain.in(store.level, result, 0, 0);

		} while (store.propagationHasOccurred);

	}

	@Override
	public boolean satisfied() {

		if (result.max() == 0) {

			int x1 = 0, x0 = 0;

			for (int i = 0; i < list.length; i++) {

				if (list[i].min() == 1) x1++;
				else if (list[i].max() == 0) x0++;

				if (x0 > 0 && x1 > 0)
					return true;
			}

			return false;

		}
		else {

			if (result.min() == 1) {

				for (int i = 0; i < list.length - 1; i++)
					if (!list[i].singleton() || !list[i+1].singleton() || list[i].value() != list[i+1].value())
						return false;					

				return true;
			}

		}

		return false;

	}

	@Override
	public boolean notSatisfied() {

		if (result.max() == 0) {

			int x1 = 0, x0 = 0;

			for (int i = 0; i < list.length; i++) {

				if (list[i].min() == 1) x1++;
				else if (list[i].max() == 0) x0++;

				if (x0 > 0 && x1 > 0)
					return false;
			}

			if (x0 == list.length || x1 == list.length)
				return true;

		}
		else {

			if (result.min() == 1) {

				int x1 = 0, x0 = 0;

				for (int i = 0; i < list.length; i++) {

					if (list[i].min() == 1) x1++;
					else if (list[i].max() == 0) x0++;

					if (x0 > 0 && x1 > 0)
						return true;
				}

				return false;
			}

		}

		return false;


	}


	@Override
	public void removeConstraint() {
		result.removeConstraint(this);
		for (int i = 0; i < list.length; i++) {
			list[i].removeConstraint(this);
		}
	}

	@Override
	public String toString() {

		StringBuffer resultString = new StringBuffer( id() );

		resultString.append(" : eqBool( ");
		for (int i = 0; i < list.length; i++) {
			resultString.append( list[i] );
			if (i < list.length - 1)
				resultString.append(", ");
		}
		resultString.append(", ");
		resultString.append(result);
		resultString.append(")");
		return resultString.toString();
	}

	ArrayList<Constraint> constraints;

	@Override
	public ArrayList<Constraint> decompose(Store store) {

		constraints = new ArrayList<Constraint>();

		PrimitiveConstraint [] eqConstraints = new PrimitiveConstraint[list.length];

		IntervalDomain booleanDom = new IntervalDomain(0, 1);

		for (int i = 0; i < eqConstraints.length - 1; i++) {
			eqConstraints[0] = new XeqY(list[i], list[i+1]);
			constraints.add(new In(list[i], booleanDom));
		}

		constraints.add( new In(result, booleanDom));

		constraints.add( new Eq(new And(eqConstraints), new XeqC(result, 1)) );

		return constraints;
	}

	@Override
	public void imposeDecomposition(Store store) {

		if (constraints == null)
			decompose(store);

		for (Constraint c : constraints)
			store.impose(c, queueIndex);

	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			result.weight++;
			for (Var v : list) v.weight++;
		}
	}

}
