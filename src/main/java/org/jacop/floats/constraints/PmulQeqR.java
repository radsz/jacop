/**
 *  PmulQeqR.java 
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
import org.jacop.core.Store;
import org.jacop.core.Var;

import org.jacop.constraints.Constraint;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;

/**
 * Constraint P * Q = R for floats
 * 
 * Boundary consistency is used.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class PmulQeqR extends Constraint {

    static int counter = 1;

    /**
     * It specifies variable p in constraint p * q = r. 
     */
    public FloatVar p;

    /**
     * It specifies variable q in constraint p * q = r. 
     */
    public FloatVar q;

    /**
     * It specifies variable r in constraint p * q = r. 
     */
    public FloatVar r;

    boolean xSquare = false;

    /**
     * It specifies the arguments required to be saved by an XML format as well as 
     * the constructor being called to recreate an object from an XML format.
     */
    public static String[] xmlAttributes = {"p", "q", "r"};

    /**
     * It constructs a constraint P * Q = R.
     * @param p variable p.
     * @param q variable q.
     * @param r variable r.
     */
    public PmulQeqR(FloatVar p, FloatVar q, FloatVar r) {

	assert (p != null) : "Variable p is null";
	assert (q != null) : "Variable q is null";
	assert (r != null) : "Variable r is null";

	numberId = counter++;
	numberArgs = 3;

	xSquare = (p == q);

	this.p = p;
	this.q = q;
	this.r = r;
    }

    @Override
    public ArrayList<Var> arguments() {

	ArrayList<Var> variables = new ArrayList<Var>(3);

	variables.add(p);
	variables.add(q);
	variables.add(r);
	return variables;
    }

    @Override
    public void consistency (Store store) {

	// identity elements
	if (p.equals(r)) {
	    q.domain.in(store.level, q, 1.0, 1.0); 
	    return;
	}
	else if (q.equals(r)) {
	    p.domain.in(store.level, p, 1.0, 1.0);
	    return;
	}

	if (xSquare)  // P^2 = R
	    do {
				
		if (r.max() < 0)
		    throw Store.failException;

		store.propagationHasOccurred = false;

		// Bounds for R
		// FloatIntervalDomain rBounds = FloatDomain.mulBounds(p.min(), p.max(), p.min(), p.max());
		// r.domain.in(store.level, r, rBounds);

		double p1 = Math.min(p.min()*p.min(), p.max()*p.max());
		double p2 = Math.max(p.min()*p.min(), p.max()*p.max());
		double min = (p1 <= p2) ? p1 : p2;
		double max = (p1 >= p2) ? p1 : p2;
		if (p.min() <= 0.0 && p.max() >= 0.0) {
		    min = 0.0;
		    max = FloatDomain.up(max);
		}
		else {
		    min = FloatDomain.down(min);
		    max = FloatDomain.up(max);
		}
		r.domain.in(store.level, r, min, max);

		// Bounds for P
		double pMin;
		if (r.min() <= 0.0)
		    pMin = 0.0;
		else
		    pMin = Math.sqrt(r.min());

		double pMax;
		if (r.max() < 0.0)
		    throw Store.failException;
		else
		    pMax = Math.sqrt(r.max());

		if ( pMin > pMax ) 
		    throw Store.failException;

		FloatDomain dom = new FloatIntervalDomain(FloatDomain.down(-pMax), FloatDomain.up(-pMin));
		dom.unionAdapt(FloatDomain.down(pMin), FloatDomain.up(pMax));

		p.domain.in(store.level, p, dom);

	    } while(store.propagationHasOccurred);
	else    // P*Q = R

	    do {

		store.propagationHasOccurred = false;

		// Bounds for P
		FloatIntervalDomain pBounds = FloatDomain.divBounds(r.min(), r.max(), q.min(), q.max());

		p.domain.in(store.level, p, pBounds); //.min(), pBounds.max());

		// Bounds for Q
		FloatIntervalDomain qBounds = FloatDomain.divBounds(r.min(), r.max(), p.min(), p.max());

		q.domain.in(store.level, q, qBounds); //.min(), qBounds.max());

		// Bounds for R
		FloatIntervalDomain rBounds = FloatDomain.mulBounds(p.min(), p.max(), q.min(), q.max());

		r.domain.in(store.level, r, rBounds); //.min(), rBounds.max());

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
	return IntDomain.BOUND;
    }

    @Override
    public void impose(Store store) {
	p.putModelConstraint(this, getConsistencyPruningEvent(p));
	q.putModelConstraint(this, getConsistencyPruningEvent(q));
	r.putModelConstraint(this, getConsistencyPruningEvent(r));
	store.addChanged(this);
	store.countConstraint();
    }

    @Override
    public void removeConstraint() {
	p.removeConstraint(this);
	q.removeConstraint(this);
	r.removeConstraint(this);
    }

    @Override
    public boolean satisfied() {
	FloatDomain pDom = p.dom(), qDom = q.dom(), rDom = r.dom();
	return pDom.singleton() && qDom.singleton() && rDom.singleton()
	    && pDom.min() * qDom.min() == rDom.min();
    }

    @Override
    public String toString() {

	return id() + " : PmulQeqR(" + p + ", " + q + ", " + r + " )";
    }


    @Override
    public void increaseWeight() {
	if (increaseWeight) {
	    p.weight++;
	    q.weight++;
	    r.weight++;
	}
    }

    public FloatVar derivative(Store store, FloatVar f, java.util.Set<FloatVar> vars, FloatVar x) {

	if (f.equals(r)) {
	    // f = p * q
	    // f' = p*d(q) + d(p)*q
	    FloatVar v1 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v2 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    Derivative.poseDerivativeConstraint(new PmulQeqR(Derivative.getDerivative(store, p, vars, x), q, v1));
	    Derivative.poseDerivativeConstraint(new PmulQeqR(Derivative.getDerivative(store, q, vars, x), p, v2));
	    Derivative.poseDerivativeConstraint(new PplusQeqR(v1, v2, v));
	    return v;
		
	}
	else if (f.equals(p)) {
	    // f = r / q
	    // f' = (d(r) - (r/q)*d(q))/q
	    FloatVar v1 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v2 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v3 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    Derivative.poseDerivativeConstraint(new PdivQeqR(r, q, v1));
	    Derivative.poseDerivativeConstraint(new PmulQeqR(v1, Derivative.getDerivative(store, q, vars, x), v2));
	    Derivative.poseDerivativeConstraint(new PminusQeqR(Derivative.getDerivative(store, r, vars, x), v2, v3));
	    Derivative.poseDerivativeConstraint(new PdivQeqR(v3, q, v));
	    return v;
	}
	else if (f.equals(q)) {
	    // f = r / p
	    // f' = (d(r) - (r/p)*d(p))/p
	    FloatVar v1 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v2 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v3 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    Derivative.poseDerivativeConstraint(new PdivQeqR(r, p, v1));
	    Derivative.poseDerivativeConstraint(new PmulQeqR(v1, Derivative.getDerivative(store, p, vars, x), v2));
	    Derivative.poseDerivativeConstraint(new PminusQeqR(Derivative.getDerivative(store, r, vars, x), v2, v3));
	    Derivative.poseDerivativeConstraint(new PdivQeqR(v3, p, v));
	    return v;

	}

	return null;

    }

}
