/**
 *  VarWeightNode.java 
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

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.linear.BoundsVar;
import org.jacop.floats.constraints.linear.BoundsVarValue;
import org.jacop.floats.constraints.linear.Linear;

public class VarWeightNode extends VariableNode {

    double weight;

    // bounds for this node
    BoundsVar bound;

    public VarWeightNode(Store store, FloatVar v, double w){

	id = n++;
	this.store = store;
	bound = new BoundsVar(store);

	var = v;
	weight = w;

	bound.value.setValue(FloatDomain.MinFloat, FloatDomain.MaxFloat, FloatDomain.MinFloat, FloatDomain.MaxFloat);

    }


    void propagate() {

	FloatIntervalDomain mul = FloatDomain.mulBounds(var.min(), var.max(), weight, weight);
	double min = mul.min();
	double max = mul.max();

	double lb = min;
	double ub = max;

	double node_min = min();
	double node_max = max();

	if (min > node_min) 
	    if (max < node_max) {

		updateBounds(min, max, lb, ub);

		parent.propagate();

	    }
	    else {
		
		if (min > node_max) 
		    throw Store.failException;

		updateBounds(min, node_max, lb, ub);

		parent.propagate();

	    }
	else
	    if (max < node_max) {

		if (node_min > max) 
		    throw Store.failException;

		updateBounds(node_min, max, lb, ub);

		parent.propagate();

	    }
    }


    void propagateAndPrune() {

	FloatIntervalDomain mul = FloatDomain.mulBounds(var.min(), var.max(), weight, weight);
	double min = mul.min();
	double max = mul.max();

	double lb = min;
	double ub = max;

	double node_min = min();
	double node_max = max();

	if (min > node_min) 
	    if (max < node_max) {

		updateBounds(min, max, lb, ub);

		parent.propagateAndPrune();
		
	    }
	    else {
		if (min > node_max)
		    throw Store.failException;

		updateBounds(min, node_max, lb, ub);

		parent.propagateAndPrune();

	    }
	else
	    if (max < node_max) {

		if (node_min > max)
		    throw Store.failException;

		updateBounds(node_min, max, lb, ub);

		parent.propagateAndPrune();

	    }

    }

    void prune() {

	double lMin = min();
	double lMax = max();

	FloatIntervalDomain d = FloatDomain.divBounds(lMin, lMax, weight, weight);
	double divMin = d.min();
	double divMax = d.max();

	var.domain.in(store.level, var, divMin, divMax);

    }

     double min() {
	 return ((BoundsVarValue)bound.value()).min;
    }

    double max() {
	return ((BoundsVarValue)bound.value()).max;
    }

    double lb() {
	 return ((BoundsVarValue)bound.value()).lb;
    }

    double ub() {
	return ((BoundsVarValue)bound.value()).ub;
    }

    void updateBounds(double min, double max, double lb, double ub) {

	bound.update(min, max, lb, ub);
    }

   public String toString() {
	return super.toString() + " (rel = " + rel + ", " + var + " * " + weight + ")" + ", ("+bound+")";
    }
}
