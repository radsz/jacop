/**
 *  RootBNode.java 
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

package org.jacop.floats.constraints.linear;

/**
 * Binary Node of the tree representing linear constraint.
 * 
 * @author Krzysztof Kuchcinski
 * @version 4.2
 */

import org.jacop.core.IntDomain;
import org.jacop.core.Interval;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.linear.BoundsVar;
import org.jacop.floats.constraints.linear.BoundsVarValue;

public class RootBNode extends BNode {

    // right hand value
    double val;
    // relation
    byte rel;

    public RootBNode(Store store) {
	super(store);
    }

    public RootBNode(Store store, double min, double max) {
	super(store, min, max);
    }

    void propagateAndPrune() {

	boolean changed = propagateForRoot();
	    
	if (changed) {

	    prune();

	    propagateForRoot();

	}
    }

    void propagate() {

	propagateForRoot();
	    
    }

    boolean propagateForRoot() { // result indicate whthter bounds are changed (true) or not changed (flase)

	FloatDomain d = FloatDomain.addBounds(left.min(), left.max(), right.min(), right.max());
	double min = d.min();
	double max = d.max();

	switch (rel) {
	case Linear.eq : 
	    if (min > val || max < val) 
		throw Store.failException;
	    break;
	case Linear.lt : 
	    if (min >= val)
		throw Store.failException;
	    break;
	case Linear.le : 
	    if (min > val)
		throw Store.failException;
	    break;
	case Linear.gt : 
	    if (max <= val)
		throw Store.failException;
	    break;
	case Linear.ge : 
	    if (max < val)
		throw Store.failException;
	    break;
	case Linear.ne : 
	    if (min == max && min == val)
		throw Store.failException;
	    break;
	}

	double current_min = min();
	double current_max = max();

	FloatDomain l = FloatDomain.addBounds(left.lb(), left.ub(), right.lb(), right.ub());
	double lb = l.min();
	double ub = l.max();

	// if (current_min < min || current_max > max) {
	//     bound.update(min, max, lb, ub);

	//     return true;
	// }

	// =====
	if (min > current_min) 
	    if (max < current_max) {

		if (min > max) 
		    throw Store.failException;

		bound.update(min, max, lb, ub);

		return true;
	    }
	    else {

		if (min > current_max) 
		    throw Store.failException;

		bound.update(min, current_max, lb, ub);

		return true;
	    }
	else
	    if (max < current_max) {

		if (current_min > max)
		    throw Store.failException;

		bound.update(current_min, max, lb, ub);

		return true;
	    }
	// =====

	return false;
    }

    void prune() {

	double min = min();
	double max = max();

	switch (rel) {
	case Linear.eq : //============================================= 
	    min = val;
	    max = val;
	    break;
	case Linear.lt : //=============================================
	    max = FloatDomain.previous(val);
	    break;
	case Linear.le : //=============================================
	    max = val;
	    break;
	case Linear.ne : //=============================================
	    if ( val >= min && val<= max )
		if (min == val) {
		    if (FloatDomain.next(min) <= max) {
			min = FloatDomain.next(min);
		    }
		    else
			throw Store.failException;
		}
		else {
		    if (max == val)
			if (FloatDomain.previous(max) >= min) {
			    max = FloatDomain.previous(max);
			}
			else
			    throw Store.failException;
		}
	    break;
	case Linear.gt : //=============================================
	    min = FloatDomain.next(val);
	    break;
	case Linear.ge : //=============================================
	    min = val;
	    break;
	}

	prune(min, max);

    }

   public String toString() {
	return super.toString() + " (rel = " + rel + ", val = " + val + ")";
    }
}
