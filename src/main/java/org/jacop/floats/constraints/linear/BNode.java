/**
 *  BNode.java 
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

import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatInterval;
import org.jacop.core.Store;
import org.jacop.floats.constraints.linear.BoundsVar;
import org.jacop.floats.constraints.linear.BoundsVarValue;

public class BNode extends BinaryNode {

    // bounds for this node
    BoundsVar bound;

    public BNode(Store store) {
	id = n++;
	bound = new BoundsVar(store);
    }

    public BNode(Store store, double min, double max) {
	id = n++;
	bound = new BoundsVar(store, min, max);
    }

    public BNode(Store store, double min, double max, double lb, double ub) {
	id = n++;
	bound = new BoundsVar(store, min, max, lb, ub);
    }


    void propagate() {

	FloatDomain d = FloatDomain.addBounds(left.min(), left.max(), right.min(), right.max());
	double min = d.min();
	double max = d.max();

	d = FloatDomain.addBounds(left.lb(), left.ub(), right.lb(), right.ub());
	double lb = d.min();
	double ub = d.max();

	double node_min = min();
	double node_max = max();

	if (min > node_min) 
	    if (max < node_max) {

		if (min > max) 
		    throw Store.failException;

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
	    else {  // no change in the domain but it was called since the children have been changed;
		    // do prune and do not contine to propagate

	    	return;
	    }
    }

    void propagateAndPrune() {

	FloatDomain d = FloatDomain.addBounds(left.min(), left.max(), right.min(), right.max());
	double min = d.min();
	double max = d.max();

	double node_min = min(); 
	double node_max = max();

	d = FloatDomain.addBounds(left.lb(), left.ub(), right.lb(), right.ub());
	double lb = d.min();
	double ub = d.max();

	if (min > node_min) 
	    if (max < node_max) {

		if (min > max) 
		    throw Store.failException;

		updateBounds(min, max, lb, ub);

		prune(min, max);

		parent.propagateAndPrune();

	    }
	    else {

		if (min > node_max) 
		    throw Store.failException;

		updateBounds(min, node_max, lb, ub);

		prune(min, node_max);

		parent.propagateAndPrune();

	    }
	else
	    if (max < node_max) {

		if (node_min > max)
		    throw Store.failException;

		updateBounds(node_min, max, lb, ub);

		prune(node_min, max);

		parent.propagateAndPrune();

	    }
	    else {  // no change in the domain but it was called since the children have been changed;
		    // do prune and do not contine to propagate

		prune(node_min, node_max);

	    	return;
	    }

    }

    void prune() {

    	double min = min();
    	double max = max();

    	prune(min, max);

    }

    void prune(double min, double max) {
	
	boolean left_changed = false, right_changed = false;
	boolean changed = false;

	left_changed = pruneNode(min, max, left, right);

	right_changed = pruneNode(min, max, right, left);

	if (left_changed) 
	    left.prune();
	if (right_changed) 
	    right.prune();
    }

    boolean pruneNode(double min, double max,  BinaryNode node, BinaryNode sibling) {

	double node_min = node.min();
	double node_max = node.max();

	double sibling_min = sibling.min();
	double sibling_max = sibling.max();

	FloatDomain bound = FloatDomain.subBounds(min, max, sibling_min, sibling_max);
	double new_node_min = bound.min();
	double new_node_max = bound.max();

	double lb = node.lb();
	double ub = node.ub();

	if (new_node_min > node_min) 
	    if (new_node_max < node_max) {

		if (new_node_min > new_node_max) 
		    throw Store.failException;

		node.updateBounds(new_node_min, new_node_max, lb, ub);

		return true;
	    }
	    else {

		if (new_node_min > node_max) 
		    throw Store.failException;

		node.updateBounds(new_node_min, node_max, lb, ub);

		return true;
	    }
	else
	    if (new_node_max < node_max) {

		if (node_min > new_node_max) 
		    throw Store.failException;

		node.updateBounds(node_min, new_node_max, lb, ub);

		return true;
	    }
	    else {

		return false;
	    }
    }

    double min() {
	return ((BoundsVarValue)bound.value()).min;
    }

    double max() {
	return  ((BoundsVarValue)bound.value()).max;
    }

    double lb() {
	return ((BoundsVarValue)bound.value()).lb;
    }

    double ub() {
	return  ((BoundsVarValue)bound.value()).ub;
    }

    void updateBounds(double min, double max, double lb, double ub) {
	bound.update(min, max, lb, ub);
    }

    public String toString() {
	return super.toString() + "("+bound.stamp()+")"+ " : " + bound;
    }

}
