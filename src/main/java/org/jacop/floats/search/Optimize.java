/**
 *  Optimize.java 
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

package org.jacop.floats.search;

import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.Search;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Not;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatInterval;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.floats.constraints.PlteqC;
import org.jacop.floats.constraints.PgtC;

import java.lang.Double;

/**
 * Implements optimization for floating point varibales
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.1
 */

public class Optimize  {

    Store store;
    DepthFirstSearch search;
    FloatVar cost;
    SplitSelectFloat<FloatVar> split;
    SelectChoicePoint select;
    Var[] variables;
    double costValue = Double.NaN;

    boolean printInfo = true;

    public Optimize(Store store, DepthFirstSearch search, SelectChoicePoint select, FloatVar cost) {

	this.store = store;
	this.search = search;
	this.select = select;
	this.cost = cost;

	search.setAssignSolution(false);
	search.setPrintInfo(false);

	variables = ((SplitSelectFloat)select).searchVariables;
	search.setSolutionListener(new ResultListener<Var>(variables));

	split = new SplitSelectFloat<FloatVar>(store, new FloatVar[] {cost}, null);
    }

    public boolean minimize() {

	PrimitiveConstraint choice = split.getChoiceConstraint(0);

	if (choice == null) 
	    return true;

	double selValue = ((PlteqC)choice).c;
	if (costValue != Double.NaN)
	    if (costValue < selValue) {
		choice = new PlteqC(cost, costValue);
	    }

	store.setLevel(store.level+1);

	boolean result = search.labeling(store, select);

	if (result) {

		if (printInfo)
		    System.out.println ("% Current cost bounds: " + cost + "\n----------");
		// System.out.println ("choice point: "+ choice);

		store.impose(choice);
		result = minimize();

		if (result) {

		    store.removeLevel(store.level);
		    store.setLevel(store.level-1);

		    return result;
		}
		else {
		    // System.out.println ("not choice point: " + choice);

		    store.impose(new Not(choice));
		    result = minimize();

		    store.removeLevel(store.level);
		    store.setLevel(store.level-1);

		    return result;
		}
	}
	else {
	    // System.out.println ("Level = " + store.level + ", FAIL");

	    store.removeLevel(store.level);
	    store.setLevel(store.level-1);

	    return false;
	}
    }

    // public boolean maximize() {
    // 	split.leftFirst = false;

    // 	return minimize();
    // }


    public class ResultListener<T extends Var> extends SimpleSolutionListener<T> {

	Var[] var;

	public ResultListener(Var[] v) {
	    var = v;
	}

	public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

	    boolean returnCode = super.executeAfterSolution(search, select);

	    costValue = cost.max();

	    System.out.println (java.util.Arrays.asList(var));
	    System.out.println ("% Found solution with cost " + cost);

	    return returnCode;
	}
    }
}
