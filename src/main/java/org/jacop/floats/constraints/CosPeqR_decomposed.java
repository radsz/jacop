/**
 *  CosPeqR_decomposed.java 
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

import org.jacop.core.Var;
import org.jacop.core.Store;
import org.jacop.constraints.Constraint;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;


/**
 * Constraints cos(P) = R
 * 
 * Bounds consistency can be used; third parameter of constructor controls this.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class CosPeqR_decomposed extends Constraint {

    static int IdNumber = 1;

    /**
     * It contains variable p.
     */
    public FloatVar p;

    /**
     * It contains variable q.
     */
    public FloatVar q;

    /**
     * It contains constraints of the CosPeqR_decomposed constraint decomposition. 
     */
    ArrayList<Constraint> constraints;

    /**
     * It constructs cos(P) = Q constraints.
     * @param p variable P
     * @param q variable Q
     */
    public CosPeqR_decomposed(FloatVar p, FloatVar q) {

	assert (p != null) : "Variable p is null";
	assert (q != null) : "Variable q is null";

	numberId = IdNumber++;
	numberArgs = 2;

	this.p = p;
	this.q = q;
    }


    @Override
    public ArrayList<Var> arguments() {
	ArrayList<Var> args = new ArrayList<Var>();

	for (Constraint c : constraints)
	    for (Var v : c.arguments())
		args.add(v);

	return args;
    }

    @Override
    public void consistency(Store store) {
	// for (Constraint c : constraints)
	//     c.consistency(store);
    }

    @Override
    public int getConsistencyPruningEvent(Var var) {

	int event=-1;
	for (Constraint c : constraints)
	    if (event <= c.getConsistencyPruningEvent(var))
		event = c.getConsistencyPruningEvent(var);

	return event;
    }

    @Override
    public void impose(Store store) {
	constraints = new ArrayList<Constraint>();

	FloatVar pPlus = new FloatVar(store, FloatDomain.MinFloat, FloatDomain.MaxFloat);
	Constraint c1 = new PplusCeqR(p, FloatDomain.PI/2, pPlus);
	Constraint c2 = new SinPeqR(pPlus, q);

	constraints.add(c1);
	constraints.add(c2);

	c1.impose(store);
	c2.impose(store);
    }

    @Override
    public void queueVariable(int level, Var V) {

    }

    @Override
    public void removeConstraint() {

	for (Constraint c : constraints)
	    c.removeConstraint();

    }

    @Override
    public boolean satisfied() {
	boolean sat = true;
	for (Constraint c : constraints)
	    sat = sat && c.satisfied();

	return sat;
    }

    @Override
    public void increaseWeight() {
	for (Constraint c : constraints)
	    c.increaseWeight();
    }

    @Override
    public String toString() {

    	StringBuffer result = new StringBuffer( id() + ": {");

    	// result.append(" : CosPeqR_decomposed(").append(p).append(", ").append(q).append(" )");

	for (Constraint c : constraints)
	    result.append(c).append(" }");

    	return result.toString();

    }

}
