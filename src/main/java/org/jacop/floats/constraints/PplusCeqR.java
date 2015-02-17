/**
 *  PplusCeqR.java 
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

package org.jacop.floats.constraints;

import java.util.ArrayList;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;

/**
 * Constraint P + C #= R
 * 
 * Bound consistency is used.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class PplusCeqR extends PrimitiveConstraint {

    static int idNumber = 1;

    /**
     * It specifies variable p in constraint p+c=r. 
     */
    public FloatVar p;

    /**
     * It specifies constant c in constraint p+c=r. 
     */
    double c;

    /**
     * It specifies variable r in constraint p+c=r. 
     */
    public FloatVar r;

	
    /**
     * It specifies the arguments required to be saved by an XML format as well as 
     * the constructor being called to recreate an object from an XML format.
     */
    public static String[] xmlAttributes = {"p", "c", "r"};

    /** It constructs constraint P+C=R.
     * @param p variable p.
     * @param c constant c.
     * @param r variable r.
     */
    public PplusCeqR(FloatVar p, double c, FloatVar r) {
		
	assert (p != null) : "Variable p is null";
	assert (r != null) : "Variable r is null";

	numberId = idNumber++;
	numberArgs = 3;

	this.p = p;
	this.c = c;
	this.r = r;
    }

    @Override
    public ArrayList<Var> arguments() {

	ArrayList<Var> variables = new ArrayList<Var>(2);

	variables.add(p);
	variables.add(r);
	return variables;
	
    }

    @Override
    public void consistency(Store store) {
		
	do {
	    store.propagationHasOccurred = false;

	    FloatIntervalDomain pDom = FloatDomain.subBounds(r.min(), r.max(), c, c);
	    p.domain.in(store.level, p, pDom.min(), pDom.max());

	    FloatIntervalDomain rDom = FloatDomain.addBounds(p.min(), p.max(), c, c);
	    r.domain.in(store.level, r, rDom.min(), rDom.max());

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

	p.putModelConstraint(this, getConsistencyPruningEvent(p));
	r.putModelConstraint(this, getConsistencyPruningEvent(r));
	store.addChanged(this);
	store.countConstraint();
    }

    @Override
    public void notConsistency(Store store) {
	
	do {
			
	    store.propagationHasOccurred = false;

	    if (r.singleton() )
		p.domain.inComplement(store.level, p, r.min() - c);

	    if (p.singleton())
		r.domain.inComplement(store.level, r, p.min() + c);
			
	} while (store.propagationHasOccurred);
		
    }

    @Override
    public boolean notSatisfied() {
	FloatDomain pDom = p.dom(), rDom = r.dom();
	return (pDom.max() + c < rDom.min() || 
		pDom.min() + c > rDom.max());
    }

    @Override
    public void removeConstraint() {
	p.removeConstraint(this);
	r.removeConstraint(this);
    }

    @Override
    public boolean satisfied() {

	return (p.singleton() && r.singleton() 
		&& r.value() - p.value() - c < FloatDomain.epsilon(r.value() - p.value() - c));
		
    }

    @Override
    public String toString() {

	return id() + " : PplusCeqR(" + p + ", " + c + ", " + r + " )";
    }

    @Override
    public void increaseWeight() {
	if (increaseWeight) {
	    p.weight++;
	    r.weight++;
	}
    }
			
    public FloatVar derivative(Store store, FloatVar f, java.util.Set<FloatVar> vars, FloatVar x) {
	if (f.equals(r)) {
	    // f = p + c
	    // f' = d(p) 
	    FloatVar v = Derivative.getDerivative(store, p, vars, x);
	    return v;
		
	}
	else if (f.equals(p)) {
	    // f = r - c
	    // f' = d(r)
	    FloatVar v = Derivative.getDerivative(store, r, vars, x);
	    return v;
		
	}

	return null;

    }
}
