/**
 *  AbsPeqR.java 
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
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.SmallDenseDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

import org.jacop.constraints.Constraint;
import org.jacop.floats.core.FloatVar;

/**
 * Constraints |P| #= R
 * 
 * Bounds consistency can be used; third parameter of constructor controls this.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class AbsPeqR extends Constraint {

    static int IdNumber = 1;

    static final boolean debugAll = false;

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
     * It constructs |P| = Q constraints.
     * @param p variable P1
     * @param q variable Q
     */
    public AbsPeqR(FloatVar p, FloatVar q) {

	assert (p != null) : "Variable p is null";
	assert (q != null) : "Variable q is null";

	numberId = IdNumber++;
	numberArgs = 2;

	this.queueIndex = 0;
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
	    q.domain.inMin(store.level, q, 0.0);
	    firstConsistencyCheck = false;
	    firstConsistencyLevel = store.level;
	}

	boundConsistency(store);

    }

    void boundConsistency(Store store) {

	do {

	    if (p.min() >= 0) {
		// possible domain consistecny for this case
		// p.domain.in(store.level, p, q.domain);
		// store.propagationHasOccurred = false;
		// q.domain.in(store.level, q, p.domain);

		// bounds consistency
		p.domain.in(store.level, p, q.min(), q.max());

		store.propagationHasOccurred = false;

		q.domain.in(store.level, q, p.min(), p.max());
	    }
	    else if (p.max() < 0) {
		p.domain.in(store.level, p, -q.max(), -q.min());

		store.propagationHasOccurred = false;

		q.domain.in(store.level, q, -p.max(), -p.min());			
	    }
	    else { // p.min() < 0 && p.max() >= 0
		// int pBound = Math.max(q.min(), q.max());
		double pBound = q.max();   // q is always >= 0
		p.domain.in(store.level, p, -pBound, pBound);

		store.propagationHasOccurred = false;

		q.domain.inMax(store.level, q, Math.max(-p.min(), p.max()));
	    }

	} while (store.propagationHasOccurred);

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
	return p.singleton() && q.singleton()
	    && (p.min() == q.min() || -p.min() == q.min());
    }


    @Override
    public String toString() {

	StringBuffer result = new StringBuffer( id() );

	result.append(" : absPeqR(").append(p).append(", ").append(q).append(" )");

	return result.toString();

    }

    @Override
    public void increaseWeight() {
	if (increaseWeight) {
	    p.weight++;
	    q.weight++;
	}
    }

}
