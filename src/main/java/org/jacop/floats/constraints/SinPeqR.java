/**
 *  SinPeqR.java 
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
import java.lang.Math;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.SmallDenseDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

import org.jacop.constraints.Constraint;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatInterval;
import org.jacop.floats.core.InternalException;

/**
 * Constraints sin(P) = R
 * 
 * Bounds consistency can be used; third parameter of constructor controls this.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class SinPeqR extends Constraint {

    static int IdNumber = 1;

    boolean firstConsistencyCheck = true;

    int firstConsistencyLevel;

    /**
     * It contains variable p.
     */
    public FloatVar p;

    /**
     * It contains variable q.
     */
    public FloatVar q;

    /**
     * It specifies the arguments required to be saved by an XML format as well as 
     * the constructor being called to recreate an object from an XML format.
     */
    public static String[] xmlAttributes = {"p", "q"};

    /**
     * It constructs sin(P) = Q constraints.
     * @param p variable P
     * @param q variable Q
     */
    public SinPeqR(FloatVar p, FloatVar q) {

	assert (p != null) : "Variable p is null";
	assert (q != null) : "Variable q is null";

	numberId = IdNumber++;
	numberArgs = 2;

	this.queueIndex = 1;
	this.p = p;
	this.q = q;
    }


    @Override
    public ArrayList<Var> arguments() {

	ArrayList<Var> variables = new ArrayList<Var>(2);

	variables.add(p);
	variables.add(q);
	return variables;
    }

    @Override
    public void removeLevel(int level) {
	if (level == firstConsistencyLevel) 
	    firstConsistencyCheck = true;
    }

    @Override
    public void consistency(Store store) {

	if (firstConsistencyCheck) {
	    q.domain.in(store.level, q, -1.0, 1.0);
	    firstConsistencyCheck = false;
	    firstConsistencyLevel = store.level;
	}

	boundConsistency(store);

    }

    void boundConsistency(Store store) {

	// System.out.println ("1. SinPeqR("+p+", "+q+")");

	if (p.max() - p.min() >= 2*FloatDomain.PI)
	    return;

	do {

	    store.propagationHasOccurred = false;

	    if (satisfied())
	    	return;

	    double min = p.min();
	    double max = p.max();
	    if (p.min() < -2*FloatDomain.PI || p.max() > 2*FloatDomain.PI) {
		// normalize to -2*PI..2*PI

		FloatInterval normP = normalize(p);
		min = normP.min();
		max = normP.max();

		// System.out.println ("Not-normalized " + p);
		// System.out.println ("Normalized interval within -2*PI..2*PI interval = " + min + ".." + max);
	    }

	    int intervalForMin = intervalNo(min);
	    int intervalForMax = intervalNo(max);

	    // System.out.println ("min in interval " + intervalForMin + ", max in interval " + intervalForMax);

	    double qMin=-1.0, qMax=1.0;
	    switch (intervalForMin) {

	    case 1: 
		switch (intervalForMax) {
		case 1: 
		    qMin = Math.sin(min);
		    qMax = Math.sin(max);
		    qMin = FloatDomain.down(qMin);
		    qMax = FloatDomain.up(qMax);
		    break;
		case 2: 
		    qMin = Math.min(Math.sin(min), Math.sin(max));
		    qMax = 1.0;
		    qMin = FloatDomain.down(qMin);
		    break;
		case 3: 
		case 4: 
		case 5: 
		    qMin = -1.0;
		    qMax =  1.0;		    
		    break;
		default: 
		    throw new InternalException("Selected impossible case in sin, cos, asin or acos constraint");
		};
		break;

	    case 2: 
		switch (intervalForMax) {
		case 2: 
		    qMin = Math.sin(max);
		    qMax = Math.sin(min);
		    qMin = FloatDomain.down(qMin);
		    qMax = FloatDomain.up(qMax);
		    break;
		case 3: 
		    qMin = -1.0;
		    qMax = Math.max(Math.sin(min), Math.sin(max));
		    qMax = FloatDomain.up(qMax);
		    break;
		case 4: 
		case 5: 
		    qMin = -1.0;
		    qMax =  1.0;		    
		break;
		default: 
		    throw new InternalException("Selected impossible case in sin, cos, asin or acos constraint");
		};
		break;

	    case 3: 
		switch (intervalForMax) {
		case 3: 
		    qMin = Math.sin(min);
		    qMax = Math.sin(max);
		    qMin = FloatDomain.down(qMin);
		    qMax = FloatDomain.up(qMax);
		    break;
		case 4: 
		    qMin = Math.min(Math.sin(min), Math.sin(max));
		    qMax = 1.0; 
		    qMin = FloatDomain.down(qMin);
		    break;
		case 5: 
		    qMin = -1.0;
		    qMax =  1.0;		    
		    break;
		default: 
		    throw new InternalException("Selected impossible case in sin, cos, asin or acos constraint");
		};
		break;

	    case 4: 
		switch (intervalForMax) {
		case 4: 
		    qMin = Math.sin(max);
		    qMax = Math.sin(min);
		    qMin = FloatDomain.down(qMin);
		    qMax = FloatDomain.up(qMax);
		    break;
		case 5: 
		    qMin = -1.0;
		    qMax = Math.max(Math.sin(min), Math.sin(max));
		    qMax = FloatDomain.up(qMax);
		    break;
		default:
		    throw new InternalException("Selected impossible case in sin, cos, asin or acos constraint");
		}
		break;

	    case 5: 
		switch (intervalForMax) {
		case 5: 
		    qMin = Math.sin(min);
		    qMax = Math.sin(max);
		    qMin = FloatDomain.down(qMin);
		    qMax = FloatDomain.up(qMax);
		    break;
		default: 
		    throw new InternalException("Selected impossible case in sin, cos, asin or acos constraint");
		};
		break;
	    default: 
		throw new InternalException("Selected impossible case in sin, cos, asin or acos constraint");
	    };

	    // System.out.println (q + " in " + qMin + ".." + qMax);

	    q.domain.in(store.level, q, qMin, qMax);

	    // System.out.println ("q after in " + q);
	    // p update
	    double pMin = Math.asin(qMin);  // range -PI/2..PI/2
	    double pMax = Math.asin(qMax);  // range -PI/2..PI/2

	    // System.out.println ("asin result " + p + " in " + pMin +".." + pMax + " copied to  n times -PI/2 .. PI/2");
	    
	    pMin = FloatDomain.down(pMin);
	    pMax = FloatDomain.up(pMax);
	    if (java.lang.Double.isNaN(pMin))
	    	pMin = -FloatDomain.PI/2;
	    if (java.lang.Double.isNaN(pMax))
	    	pMax = FloatDomain.PI/2;

	    double low, high;
	    double k = Math.floor(p.min()/(2*FloatDomain.PI));
	    low = FloatDomain.down(pMin + 2*k*FloatDomain.PI);
	    k = Math.ceil(p.max()/(2*FloatDomain.PI));
	    high = FloatDomain.up(pMax + 2*k*FloatDomain.PI);
	    FloatIntervalDomain pDom = new FloatIntervalDomain(low, high);

	    // System.out.println ("2. " + p + " in " + pDom  + " low..high = " + low+".."+high + ", k = " + k);

	    p.domain.in(store.level, p, pDom); //.min(), pDom.max());

	    // System.out.println ("p after in " + p);

	} while (store.propagationHasOccurred);

	// System.out.println ("2. SinPeqR("+p+", "+q+")");

    }

    /*
     * Normalizes argument to interval -2*PI..2*PI
     */
    FloatInterval normalize(FloatVar v) {
	double min = v.min();
	double max = v.max();

	double normMin = FloatDomain.down(min % (2*FloatDomain.PI));
	double maxmin = max-min;
	double normMax = FloatDomain.up(normMin + maxmin);

	if (normMax >= 2*FloatDomain.PI) {
	    normMin = FloatDomain.down(normMin - 2*FloatDomain.PI);
	    normMax = FloatDomain.up(normMax - 2*FloatDomain.PI);
	}

	return new FloatInterval(normMin, normMax);

    }

    // double rest(double d, boolean min) {

    // 	double rest = d % (2*FloatDomain.PI);

    // 	if (min)
    // 	    rest = FloatDomain.down(rest);
    // 	else
    // 	    rest = FloatDomain.up(rest);

    // 	return rest;
    // }

    int intervalNo(double d) {
	if (d >= -2.0*FloatDomain.PI && d <= -1.5*FloatDomain.PI)
	    return 1;
	if (d >= -1.5*FloatDomain.PI && d <= -0.5*FloatDomain.PI)
	    return 2;
	if (d >= -0.5*FloatDomain.PI && d <= 0.5*FloatDomain.PI)
	    return 3;
	if (d >= 0.5*FloatDomain.PI && d <= 1.5*FloatDomain.PI)
	    return 4;
	if (d >= 1.5*FloatDomain.PI && d <= 2.0*FloatDomain.PI)
	    return 5;
	else 
	    return 0;  // should not return this
    }

    @Override
    public int getConsistencyPruningEvent(Var var) {

	// consistency function mode
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
	store.addChanged(this);
	store.countConstraint();
    }

    @Override
    public void removeConstraint() {
	p.removeConstraint(this);
	q.removeConstraint(this);
    }

    @Override
    public boolean satisfied() {

	if (p.singleton() && q.singleton()) {
	    double sinMin = Math.sin(p.min()), sinMax = Math.sin(p.max());
	    
	    FloatInterval minDiff = (sinMin <  q.min()) ?  new FloatInterval(sinMin, q.min()) : new FloatInterval(q.min(), sinMin);
	    FloatInterval maxDiff = (sinMax <  q.max()) ?  new FloatInterval(sinMax, q.max()) : new FloatInterval(q.max(), sinMax);

	    return minDiff.singleton() && maxDiff.singleton();
	}
	else
	    return false;
    }


    @Override
    public String toString() {

	StringBuffer result = new StringBuffer( id() );

	result.append(" : SinPeqR(").append(p).append(", ").append(q).append(" )");

	return result.toString();

    }

    @Override
    public void increaseWeight() {
	if (increaseWeight) {
	    p.weight++;
	    q.weight++;
	}
    }

    public FloatVar derivative(Store store, FloatVar f, java.util.Set<FloatVar> vars, FloatVar x) {
	if (f.equals(q)) {
	    // f = sin(p)
	    // f' = cos(p) * d(p)
	    FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v1 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    Derivative.poseDerivativeConstraint(new CosPeqR(p, v1));
	    Derivative.poseDerivativeConstraint(new PmulQeqR(v1, Derivative.getDerivative(store, p, vars, x), v));
	    return v;
	}
	else if (f.equals(p)) {
	    // f = asin(q)
	    // f' = d(q) * 1/sqrt(1-q^2)
	    FloatVar v = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v1 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v2 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v3 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    FloatVar v4 = new FloatVar(store, Derivative.MIN_FLOAT, Derivative.MAX_FLOAT);
	    Derivative.poseDerivativeConstraint(new PmulQeqR(q, q, v1));
	    Derivative.poseDerivativeConstraint(new PminusQeqR(new FloatVar(store, 1.0, 1.0), v1, v2));
	    Derivative.poseDerivativeConstraint(new SqrtPeqR(v2, v3));
	    Derivative.poseDerivativeConstraint(new PdivQeqR(new FloatVar(store, 1.0, 1.0), v3, v4));
	    Derivative.poseDerivativeConstraint(new PmulQeqR(Derivative.getDerivative(store, q, vars, x), v4, v));
	    return v;		
	}

	return null;

    }

}
