/*
 * RestartSearch.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.search.restart;

import org.jacop.core.Store;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.constraints.XltC;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.PlteqC;

import org.jacop.search.DepthFirstSearch;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.SolutionListener;
import org.jacop.search.ConsistencyListener;
import org.jacop.search.PrioritySearch;
;
/**
 * Implements restart search. Only cost as IntVar is possible.
 *
 * @param <T> type of variables used in this search.
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */

public class RestartSearch<T extends Var> {

    Store store;
    DepthFirstSearch<T> search;
    SelectChoicePoint<T> select;
    Calculator calculator;
    SolutionListener lastSolutionListener;
    CustomReport reportSolution = null;

    Search<T> lastNotNullSearch;
    
    Var cost;
    int intCostValue = Integer.MAX_VALUE;;
    double floatCostValue = Double.MAX_VALUE;

    int numberRestarts = 0;

    boolean timeOutCheck = false;
    long timeOut;
    
    @SuppressWarnings("unchecked") 
    public RestartSearch(Store store, DepthFirstSearch<T> s, SelectChoicePoint<T> sel, Calculator calculator, Var cost) {
	this.search = s;
	this.calculator = calculator;
	this.cost = cost;
	this.select = sel;
	this.store = store;
	
	DepthFirstSearch<T> ns = search;
	lastNotNullSearch = ns;

	do {

	    if (ns instanceof PrioritySearch) {
		((PrioritySearch)ns).addRestartCalculator((PrioritySearch)ns, calculator);
	    }

	    // add calculator & do not assign solutions
	    ConsistencyListener cs = ns.getConsistencyListener();
	    ns.setConsistencyListener(calculator);
	    ns.consistencyListener.setChildrenListeners(cs);
	    ns.setAssignSolution(false);
	    ns.setPrintInfo(false);
	    lastNotNullSearch = ns;

	    // find next search
	    if (ns.childSearches == null)
		ns = null;
	    else 
		ns = (DepthFirstSearch<T>)ns.childSearches[0];
	} while (ns != null);

	if (cost != null) {
	    lastSolutionListener = lastNotNullSearch.getSolutionListener();
	    lastSolutionListener.setChildrenListeners(new CostListener<T>());
	}
    }

    public RestartSearch(Store store, DepthFirstSearch<T> s, SelectChoicePoint<T> sel, Calculator calculator) {
	this(store, s, sel, calculator, null);
    }

    public boolean labeling() {

	store.setLevel(store.level+1); 
	boolean result = true, atLeastOneSolution = false;
	while (result) {

	    if (cost == null)
		result = search.labeling(store, select);
	    else
		result = search.labeling(store, select, cost);

	    atLeastOneSolution |= result;
	    
	    int sl = ((SimpleSolutionListener)lastNotNullSearch.getSolutionListener()).solutionLimit;
	    if (sl > 0 && search.getSolutionListener().solutionsNo() >= sl) 
		return true;

	    if (timeOutCheck && System.currentTimeMillis() > timeOut)
		return true;
	    
	    if (result)	    
		if (cost != null) {
		    if (!calculator.pointsExhausted())
			result = false;
		    if (cost instanceof IntVar)
			store.impose(new XltC((IntVar)cost, intCostValue));
		    else if (cost instanceof FloatVar)
			store.impose(new PlteqC((FloatVar)cost, FloatDomain.previousForMinimization(floatCostValue)));
		}
		else
		    break; // single solution for satisfy search found
	    else { // no result
		if (calculator.pointsExhausted()) {
		    if (cost != null) {
			result = true;
		    }
		    else if (!atLeastOneSolution)
			result = true;
		}
	    }
	    calculator.newLimit();

	    if (result)
		numberRestarts++;
	}

	store.removeLevel(store.level); 
	store.setLevel(store.level-1);

	return true;
    }

    public int getIntCost() {
	return intCostValue;
    }

    public double getFloatCost() {
	return floatCostValue;
    }

    public void addReporter(CustomReport r) {
	reportSolution = r;
    }


    public int restarts() {
	return numberRestarts;
    }
    
    public void setTimeOut(long tOut) {
	timeOutCheck = true;
	timeOut = System.currentTimeMillis() + tOut * 1000;
    }

    public void setTimeOutMilliseconds(long tOut) {
	timeOutCheck = true;
        timeOut = System.currentTimeMillis() + tOut;
    }

    public class CostListener<T extends Var> extends SimpleSolutionListener<T> { 
 
   	public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) { 

            boolean returnCode = super.executeAfterSolution(search, select);

	    if (reportSolution != null)
		reportSolution.report();

	    if (cost instanceof IntVar)
		intCostValue = ((IntVar)cost).value();
	    else if (cost instanceof FloatVar)
		floatCostValue = ((FloatVar)cost).value();

	    return returnCode; 
      } 
   }
}
