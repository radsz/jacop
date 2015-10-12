/**
 *  OrBool.java 
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

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * OrBool constraint implements logic and operation on its arguments
 * and returns result.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class OrBool extends PrimitiveConstraint {

    PrimitiveConstraint c = null;

    /**
     * It constructs and constraint on variables.
     * @param a parameters variable.
     * @param result variable.
     */
    public OrBool(IntVar[] a, IntVar result) {
	if (a.length == 2)
	    c = new OrBoolSimple(a[0], a[1], result);
	else
	    c = new OrBoolVector(a, result);
    }

    /**
     * It constructs and constraint on variables.
     * @param a parameters variable.
     * @param result variable.
     */
    public OrBool(ArrayList<IntVar> a, IntVar result) {

	if (a.size() == 2)
	    c = new OrBoolSimple(a.get(0), a.get(1), result);
	else
	    c = new OrBoolVector(a.toArray(new IntVar[a.size()]), result);
    }

    /**
     * It constructs and constraint on variables.
     * @param a parameters variable.
     * @param result variable.
     */
    public OrBool(IntVar a, IntVar b, IntVar result) {
	c = new OrBoolSimple(a, b, result);
    }

    @Override
    public ArrayList<Var> arguments() {

	return c.arguments();
    }

    @Override
    public void consistency(Store store) {
	c.consistency(store);
    }

    @Override
    public void notConsistency(Store store) {
	c.consistency(store);
    }

    @Override
    public int getConsistencyPruningEvent(Var var) {
	return c.getConsistencyPruningEvent(var);

    }

    @Override
    public int getNestedPruningEvent(Var var, boolean mode) {
	return c.getNestedPruningEvent(var, mode);
    }

    @Override
    public int getNotConsistencyPruningEvent(Var var) {
	return c.getNotConsistencyPruningEvent(var);
    }

   
    @Override
    public String id() {
	return c.id();
    }

    @Override
    public void impose(Store store) {
	c.impose(store);
    }

    @Override
    public void queueVariable(int level, Var V) {
	c.queueVariable(level, V);
    }

    @Override
    public void removeConstraint() {
	c.removeConstraint();
    }

    @Override
    public boolean satisfied() {
	return c.satisfied();
    }

    @Override
    public boolean notSatisfied() {
	return c.satisfied();
    }

    @Override
    public void include(Store store) {
	c.include(store);
    }

    @Override
    public String toString() {
	return c.toString();
    }

    @Override
    public void increaseWeight() {
	c.increaseWeight();
    }

}
