/**
 *  XorBool.java
 *   
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
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Constraint ( x_0 xor x_1 xor ... xor x_n ) <=> y
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class XorBool extends PrimitiveConstraint {

	/*
	 * The logical XOR (exclusive OR) function gives True if an odd number of its arguments 
	 * is True, and the rest are False. It gives False if an even number of its arguments is True, 
	 * and the rest are False.
	 *
	 * For two arguments the truth table is
	 *
	 * X | Y | Z
	 * 0   0   0
	 * 0   1   1
	 * 1   0   1
	 * 1   1   0
	 */

	static int idNumber = 1;

	/**
	 * It specifies variables x for the constraint.
	 */
	public IntVar[] x;

        public IntVar y;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
    public static String[] xmlAttributes = {"x", "y"};

	/** It constructs constraint (x_0 xor x_1 xor ... xor x_n ) <=> y.
	 * @param x variables x.
	 * @param y variable y.
	 */
    public XorBool(IntVar[] x, IntVar y) {

		assert (x != null) : "Variables x is null";
		assert (y != null) : "Variable y is null";

	        queueIndex = 0;
		numberId = idNumber++;
		numberArgs = x.length + 1;

		this.x = x;
		this.y = y;

		assert ( checkInvariants() == null) : checkInvariants();

	}

	/**
	 * It checks invariants required by the constraint. Namely that
	 * boolean variables have boolean domain. 
	 * 
	 * @return the string describing the violation of the invariant, null otherwise.
	 */
	public String checkInvariants() {

	    for (IntVar e : x)
		if (e.min() < 0 || e.max() > 1)
		    return "Variable " + x + " does not have boolean domain";
	
		if (y.min() < 0 || y.max() > 1)
			return "Variable " + y + " does not have boolean domain";

		return null;
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(3);

		for (IntVar e : x)
		    variables.add(e);

		variables.add(y);

		return variables;
	}

	@Override
	public void consistency(Store store) {

	    do {
		
		store.propagationHasOccurred = false;

		IntVar nonGround = null;

		int numberOnes = 0;
		for (IntVar e : x)
		    if (e.min() == 1)
			numberOnes++;
		    else if (e.max() != 0)
			nonGround = e;

		int numberZeros = 0;
		for (IntVar e : x)
		    if (e.max() == 0)
			numberZeros++;
		    else if (e.min() != 1)
			nonGround = e;

		if (numberOnes + numberZeros == x.length)
		    if (numberOnes % 2 == 1)
			y.domain.in(store.level, y, 1, 1);
		    else
			y.domain.in(store.level, y, 0, 0);
		else if (numberOnes + numberZeros == x.length - 1)
		    if (y.min() == 1)
			if (numberOnes % 2 == 1)
			    nonGround.domain.in(store.level, nonGround, 0,0);
			else
			    nonGround.domain.in(store.level, nonGround, 1,1);
		    else if (y.max() == 0)
			if (numberOnes % 2 == 1)
			    nonGround.domain.in(store.level, nonGround, 1,1);
			else
			    nonGround.domain.in(store.level, nonGround, 0,0);

	    } while (store.propagationHasOccurred);
	}

        @Override
	public void notConsistency(Store store) {
		
	    do {
			
		store.propagationHasOccurred = false;			

		IntVar nonGround = null;

		int numberOnes = 0;
		for (IntVar e : x)
		    if (e.min() == 1)
			numberOnes++;
		    else if (e.max() != 0)
			nonGround = e;

		int numberZeros = 0;
		for (IntVar e : x)
		    if (e.max() == 0)
			numberZeros++;
		    else if (e.min() != 1)
			nonGround = e;

		if (numberOnes + numberZeros == x.length)
		    if (numberOnes % 2 == 1)
			y.domain.in(store.level, y, 0, 0);
		    else 
			y.domain.in(store.level, y, 1, 1);
		else if (numberOnes + numberZeros == x.length - 1)
		    if (y.min() == 1)
			if (numberOnes % 2 == 1)
			    nonGround.domain.in(store.level, nonGround, 1,1);
			else
			    nonGround.domain.in(store.level, nonGround, 0,0);
		    else if (y.max() == 0)
			if (numberOnes % 2 == 1)
			    nonGround.domain.in(store.level, nonGround, 0,0);
			else
			    nonGround.domain.in(store.level, nonGround, 1,1);

		} while (store.propagationHasOccurred);
		
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
			return IntDomain.GROUND;
		}
		// If notConsistency function mode
		else {
			if (notConsistencyPruningEvents != null) {
				Integer possibleEvent = notConsistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return IntDomain.BOUND;
		}
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
	public void impose(Store store) {

	    for (IntVar e : x)
		e.putModelConstraint(this, getConsistencyPruningEvent(e));

		y.putModelConstraint(this, getConsistencyPruningEvent(y));

		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public boolean satisfied() {

	    if (! y.singleton())
		return false;
	    else
		for (IntVar e : x)
		    if (! e.singleton())
			return false;

	    int sum = 0;
	    for (IntVar e : x)
		sum += e.value();

	    if (sum % 2 == 1 && y.min() == 1)
		return true;
	    else if (sum % 2 == 0 && y.max() == 0)
		return true;

	    return false;

	}

	@Override
	public boolean notSatisfied() {

	    if (! y.singleton())
		return false;
	    else
		for (IntVar e : x)
		    if (! e.singleton())
			return false;

	    int sum = 0;
	    for (IntVar e : x)
		sum += e.value();

	    if (sum % 2 == 1 && y.min() == 0)
		return true;
	    else if (sum % 2 == 0 && y.min() == 1)
		return true;

	    return false;
	}

	@Override
	public void removeConstraint() {
	    for (IntVar e : x)
		e.removeConstraint(this);

	    y.removeConstraint(this);
	}

	@Override
	public String toString() {

	    return id() + " : XorBool( (" + java.util.Arrays.asList(x) + ") <=>  " + y + ")";
	}

	@Override
	public void increaseWeight() {
	    if (increaseWeight) 
		for (IntVar e : x)
		    e.weight++;
	}

}
