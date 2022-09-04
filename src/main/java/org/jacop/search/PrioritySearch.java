/*
 * PrioritySearch.java
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

package org.jacop.search;

import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.IntVar;
import org.jacop.constraints.XltC;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.constraints.PlteqC;
import org.jacop.search.restart.Calculator;

import java.util.BitSet;
import java.util.ArrayList;
import java.util.List;

/**
 * PrioritySearch selects first a row in the matrix based on metric of
 * the variable at the pririty vector. As soon as a row is choosen,
 * variables are selected for indomain method.  The row selection is
 * done with the help of pririty variable comparators. Two comparators
 * can be employed main and tiebreaking one. If two are not sufficient
 * to differentiate two rows than the lexigraphical ordering is used.
 *
 * Based on paper "Priority Search with MiniZinc" by Thibaut Feydy,
 * Adrian Goldwaser, Andreas Schutt, Peter J. Stuckey,and Kenneth
 * D. Young, in ModRef'2017: The Sixtenth International Workshop on
 * Constraint Modelling and Reformulation at CP 2017.
 *
 * @param <T> type of variable being used in the Search.
 * @author Krzysztof Kuchcinski
 * @version 4.9
 */

@SuppressWarnings("unchecked")
public class PrioritySearch<T extends Var> extends DepthFirstSearch<T> {

    static final boolean debugAll = false;

    int n;  // length of priority variables and sub-vectors
    T[] priority;
    ComparatorVariable<T> comparator;

    DepthFirstSearch[] search;

    BitSet visited;

    T[] allVars;
    
    int noSolutions = 0;

    int solutionsLimit = -1; //Integer.MAX_VALUE;
    boolean solutionsReached = false;	
	
    /**
     * It constructs a PrioritySearch variable ordering.
     *
     * @param priority       prority variables used to select a sub-vector of vars (row)
     * @param dfs            vector of depth first searches to be selected from; they must have SelectChoicePoint set.
     * @param comparator     the variable comparator to choose the proper sub.search.
     // * @param indomain       variable ordering value to be used to determine value for a given variable.
     */
    public PrioritySearch(T[] priority, ComparatorVariable<T> comparator, DepthFirstSearch<T>[] dfs) {
	int pLength = priority.length;
	int vLength = dfs.length;
	if (pLength != vLength)
	    throw new RuntimeException("length of priority variables and depth first searches must be the same");

	n = priority.length;
	this.priority = priority;
	this.comparator = comparator;
	this.visited = new BitSet(n);
	    
	search = new DepthFirstSearch[2*dfs.length];
	for (int i = 0; i < n; i++) {

	    dfs[i].setMasterSearch(this);
	    search[2*i] = dfs[i];
	    if (!dfs[i].getClass().getName().equals("org.jacop.search.PrioritySearch") && dfs[i].heuristic == null)
		throw new RuntimeException("heuristic in depth first search must be set");

	    search[2*i+1] = new LinkingSearch<T>(this);
	    DepthFirstSearch last = lastSearch(dfs[i]);
	    last.addChildSearch(search[2*i+1]);
	    search[2*i+1].setMasterSearch(last);
	}
	this.allVars = getVariables(this);

    }

    DepthFirstSearch lastSearch(DepthFirstSearch dfs) {
	DepthFirstSearch<T> ns = dfs;
	DepthFirstSearch lastNotNullSearch = ns;
	
	do {
	    lastNotNullSearch = ns;
	    // find next search
	    if (ns.childSearches == null)
		ns = null;
	    else 
		ns = (DepthFirstSearch<T>)ns.childSearches[0];
	} while (ns != null);

	return lastNotNullSearch;
    }
    
    public boolean labeling(Store store, SelectChoicePoint<T> select) {

	heuristic = select;
	return labeling(store);
    }
    
    public boolean labeling(Store store) {

        this.store = store;
	((SimpleSolutionListener)solutionListener).setVariables(allVars);

	for (DepthFirstSearch dfs: search)
	    dfs.setStore(store);

        if (store.raiseLevelBeforeConsistency) {
            store.raiseLevelBeforeConsistency = false;
            store.setLevel(store.level + 1);
        }

        depth = store.level;

        if (costVariable == null)
            optimize = false;

        if (initializeListener != null)
            initializeListener.executedAtInitialize(store);

        boolean result = store.consistency();
        store.setLevel(store.level + 1);
        depth = store.level;

	visited.clear();
	int subSearch = getSubSearch();
	visited.set(subSearch);

        if (result) {

	    try {
		result = search[2*subSearch].labeling();
	    }
	    catch (SolutionsLimitReached e) {
		solutionsReached = true;
		if (printInfo)
		    System.out.println("Solution limit " + solutionsLimit + " reached");
	    }

	    visited.set(subSearch, false);
	    
        }
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
        depth--;

        if (exitListener != null)
            exitListener.executedAtExit(store, noSolutions);

	for (int i = 0; i < n; i++) 
	    timeOutOccured |= search[2*i].timeOutOccured;

        if (timeOutOccured) {

            if (printInfo)
                System.out.println("Time-out " + tOut + "s");

        }

        if (noSolutions > 0) {

            if (assignSolution)
                assignSolution();

            if (printInfo)
		System.out.println(statistics());

            return true;
        } else {

            if (printInfo) {

                System.out.println("No solution found.");

                StringBuffer buf = new StringBuffer();

                buf.append("Depth First Search " + id + "\n");
                buf.append("\n");
                buf.append("Nodes : ").append(nodes).append("\n");
                buf.append("Decisions : ").append(decisions).append("\n");
                buf.append("Wrong Decisions : ").append(wrongDecisions).append("\n");
                buf.append("Backtracks : ").append(numberBacktracks).append("\n");
                buf.append("Max Depth : ").append(maxDepthExcludePaths).append("\n");

                System.out.println(buf.toString());

            }

            return false;
        }

    }

    public boolean labeling(Store store, SelectChoicePoint<T> select, Var costVar) {

	return labeling(store, costVar);
    }
    
    public boolean labeling(Store store, Var costVar) {

	this.store = store;
	((SimpleSolutionListener)solutionListener).setVariables(allVars);

	if (solutionsLimit == -1)
	    solutionsLimit = Integer.MAX_VALUE;
	
	for(DepthFirstSearch dfs : search) {
	    DepthFirstSearch ns = dfs;
	    do {
		ns.setStore(store);
		ns.setCostVar(costVar);
		ns.respectSolutionListenerAdvice = true;
		// find next search
		ns = (ns.childSearches == null) ? null : (DepthFirstSearch<T>)ns.childSearches[0];
	    } while (ns != null);	    
	}
	
        if (store.raiseLevelBeforeConsistency) {
            store.raiseLevelBeforeConsistency = false;
            store.setLevel(store.level + 1);
        }

        // heuristic = select;  // has selection already
        depth = store.level;
        costVariable = costVar;
	for (int i = 0; i < n; i++) {
	    search[2*i].costVariable = costVar;
	}
        optimize = true;
        cost = null;

        if (initializeListener != null)
            initializeListener.executedAtInitialize(store);

        boolean result = store.consistency();
        store.setLevel(store.level + 1);
        depth = store.level;

	visited.clear();
	int subSearch = getSubSearch();
	visited.set(subSearch);
	
	if (result) {
	    try {
		result = search[2*subSearch].labeling();
	    }
	    catch (SolutionsLimitReached e) {
		getStatistics();

		solutionsReached = true;
		if (printInfo)
		    System.out.println("Solution limit " + solutionsLimit + " reached");
	    }
	    
	    visited.set(subSearch, false);	    
        }
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
        depth--;

	getStatistics();

	if (exitListener != null)
            exitListener.executedAtExit(store, noSolutions);

	for (int i = 0; i < n; i++) 
	    timeOutOccured |= search[2*i].timeOutOccured;

        if (timeOutOccured) {

            if (printInfo)
                System.out.println("Time-out " + tOut + "s");

        }

        if (noSolutions > 0) {

            if (assignSolution)
                assignSolution();

            if (printInfo)
                if (costVariable instanceof IntVar)
                    System.out.println("Solution cost is " + search[0].costValue);
                else if (costVariable instanceof FloatVar)
                    System.out.println("Solution cost is " + search[0].costValueFloat);

            if (printInfo)
		System.out.println(statistics());

            return true;

        } else {

            if (printInfo) {

                System.out.println("No solution found.");
		
		System.out.println(statistics());

            }

            return false;
        }

    }

    public boolean labeling() {

	this.store = allVars[0].getStore();
	((SimpleSolutionListener)solutionListener).setVariables(allVars);

	for(DepthFirstSearch dfs : search) 
	    dfs.setStore(store);

	if (costVariable != null) {
	    for(DepthFirstSearch dfs : search) {
		dfs.setCostVar(costVariable);
		dfs.respectSolutionListenerAdvice = true;
		dfs.costVariable = costVariable;
	    }
	    optimize = true;
	    cost = null;

	    if (solutionsLimit == -1)
		solutionsLimit = Integer.MAX_VALUE;
	}
	
        boolean raisedLevel = false;

        if (store.raiseLevelBeforeConsistency) {
            store.raiseLevelBeforeConsistency = false;
            store.setLevel(store.level + 1);
            raisedLevel = true;
        }

        depth = store.level;
        cost = null;

        if (costVariable == null)
            optimize = false;

        if (initializeListener != null)
            initializeListener.executedAtInitialize(store);

        // Iterative Solution listener sets it to zero so it can find the next batch, so it has to be executed
        // after initialize listener.
        // int solutionNoBeforeSearch = solutionListener.solutionsNo();

        // If constraints employ only one time execution of the part of
        // the consistency technique then the results of that part must be
        // stored in one level above the level search starts from as this
        // can be removed.
        boolean result = store.consistency();
        store.setLevel(store.level + 1);
        depth = store.level;

	visited.clear();
	int subSearch = getSubSearch();
	visited.set(subSearch);
	
        if (result) {
	    try {
		result = search[2*subSearch].labeling();
	    }
	    catch (SolutionsLimitReached e) {
		getStatistics();
		
		solutionsReached = true;
		if (printInfo)
		    System.out.println("Solution limit " + solutionsLimit + " reached");
	    }
	    
	    visited.set(subSearch, false);	    
        }

        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
        depth--;

	getStatistics();

	if (exitListener != null)
            exitListener.executedAtExit(store, solutionListener.solutionsNo());

	for (int i = 0; i < n; i++) 
	    timeOutOccured |= search[2*i].timeOutOccured;

        if (timeOutOccured) {

            if (printInfo)
                System.out.println("Time-out " + tOut + "s");

        }

        if (noSolutions > 0) {
	    // update number solutions in solution listener; otherwise it will be zero :(
	    ((SimpleSolutionListener)solutionListener).setSolutionsNo(noSolutions);

            if (printInfo) {
                if (costVariable != null)
                    if (costVariable instanceof IntVar)
                        System.out.println("Solution cost is " + costValue);
                    else if (costVariable instanceof IntVar)
                        System.out.println("Solution cost is " + costVariable.dom());

		if (printInfo)
		    System.out.println(statistics());
            }

            if (raisedLevel) {
                store.removeLevel(store.level);
                store.setLevel(store.level - 1);
            }

            if (masterSearch == null)
                return true;
            else
                return result;

        } else {

            if (printInfo) {

                System.out.println("No solution found.");

		System.out.println(statistics());

            }

            if (raisedLevel) {
                store.removeLevel(store.level);
                store.setLevel(store.level - 1);
            }

            return false;
        }

    }

    @Override
    public boolean label(int n) {
	 throw new RuntimeException("Method label is not defined for PrioritySearch.");
    }

    @Override
    public int getNodes() {
	nodes = 0;
	for (DepthFirstSearch<Var> l : search) {
	    nodes += l.getNodes();

	    if (l.childSearches != null)
		nodes += l.childSearches[0].getNodes();
	}
	return nodes;
    }

    @Override
    public int getDecisions() {
	decisions = 0;
	for (DepthFirstSearch<Var> l : search) {
	    decisions += l.getDecisions();

	    if (l.childSearches != null)
		decisions += l.childSearches[0].getDecisions();
	}
	return decisions;
    }

    @Override
    public int getWrongDecisions() {
	wrongDecisions = 0;
	for (DepthFirstSearch<Var> l : search) {
	    wrongDecisions += l.getWrongDecisions();

	    if (l.childSearches != null)
		wrongDecisions += l.childSearches[0].getWrongDecisions();
	}
	return wrongDecisions;
    }

    @Override
    public int getBacktracks() {
	numberBacktracks = 0;
	for (DepthFirstSearch<Var> l : search) {
	    numberBacktracks += l.getBacktracks();

	    if (l.childSearches != null)
		numberBacktracks += l.childSearches[0].getBacktracks();
	}
	return numberBacktracks;
    }

    @Override
    public int getMaximumDepth() {
	maxDepthExcludePaths = 0;
	for (DepthFirstSearch<Var> l : search) {
	    maxDepthExcludePaths += l.getMaximumDepth();

	    if (l.childSearches != null)
		maxDepthExcludePaths += l.childSearches[0].getMaximumDepth();

	}
	return maxDepthExcludePaths;
    }

    public void getStatistics() {

	nodes = getNodes();
	decisions = getDecisions();
	wrongDecisions = getWrongDecisions();
	numberBacktracks = getBacktracks();
	maxDepthExcludePaths = getMaximumDepth();
    }
    
    String statistics() {

	StringBuffer buf = new StringBuffer();

	buf.append("No solutions : ").append(noSolutions).append("\n");
	buf.append("Nodes : ").append(nodes).append("\n");
	buf.append("Decisions : ").append(decisions).append("\n");
	buf.append("Wrong Decisions : ").append(wrongDecisions).append("\n");
	buf.append("Backtracks : ").append(numberBacktracks).append("\n");
	buf.append("Max Depth : ").append(maxDepthExcludePaths).append("\n");

	return buf.toString();
    }

    public void setCostVariable(Var cost) {
	costVariable = cost;
    }
    
    int getSubSearch() {

	int current = 0;
	while (current < n && visited.get(current))
	    current++;
	if (current == n)
	    return n;

	if (comparator != null) {
	    double currentMeasure = comparator.metric(priority[current]);
	    for (int i = current+1; i < n; i++) {
		if (comparator.compare(currentMeasure, priority[i]) < 0 && ! visited.get(i)) {
		    current = i;
		currentMeasure = comparator.metric(priority[current]);
		}
	    }
	}
	
	return current;
    }

    public T[] getVariables(PrioritySearch ps) {

	T[] varsArray;
    	List<T> vars = new ArrayList<>();

	for (int i = 0; i < ps.search.length/2; i++) {
	    SelectChoicePoint<T> heuristic =  ps.search[2*i].heuristic;

	    if (heuristic == null) {
		// PrioritySearch
		T[] vs = null;
		for (int j = 0; j < ps.search.length/2; j++) {
		    vs = getVariables((PrioritySearch)ps.search[2*j]);

		}

		for (int k = 0; k < vs.length; k++) 
		    vars.add(vs[k]);

	    } else {
		java.util.Map<T, Integer> position = heuristic.getVariablesMapping();

		for (java.util.Iterator<T> itr = position.keySet().iterator(); itr.hasNext();) {
		    T current = itr.next();
		    vars.add(current);
		}
	    }
	}

    	varsArray = (T[]) new Var[vars.size()];
    	for (int i = 0; i < vars.size(); i++) 
	    varsArray[i] = vars.get(i);

    	return varsArray;
    }

    public void addRestartCalculator(DepthFirstSearch s, Calculator calc) {

	DepthFirstSearch[] ns = null;
	if (s instanceof PrioritySearch)
	    ns  = ((PrioritySearch)s).getSearchSeq();
	else
	    ns = new DepthFirstSearch[] {s};

	for (DepthFirstSearch dfs : ns)
	    if (dfs instanceof PrioritySearch) {
		for (int i = 0; i < ((PrioritySearch)dfs).search.length/2; i++) {
	    	    addRestartCalculator(((PrioritySearch)dfs).search[2*i], calc);
	    	}
	    } else {
		ConsistencyListener consist = dfs.getConsistencyListener();
		dfs.setConsistencyListener(calc);
		dfs.consistencyListener.setChildrenListeners(consist);
	    }
    }
    
    public void setSolutionLimit(int no) {
	solutionsLimit = no;
    }

    public DepthFirstSearch[] getSearchSeq() {
	return search;
    }
    
    public String toString() {
        StringBuffer b  = new StringBuffer();

	b.append("PrioritySearch(").append(java.util.Arrays.asList(priority)).append(", ").append(comparator.getClass().getName());

	b.append(", [");
	for (int i = 0; i < search.length/2; i++) {
	    b.append(search[2*i]+", ");
	}
	b.append("])");

	return b.toString();
    }

    class LinkingSearch<T extends Var> extends DepthFirstSearch<T> {

	DepthFirstSearch master;
	
	LinkingSearch(DepthFirstSearch m) {
	    master = m;
	}

	void constraineCost() {
	    if (costVariable instanceof IntVar) {
		int newCost = ((IntVar) costVariable).dom().max();

		if (newCost < costValue) {
		    costValue = newCost;
		    master.costValue = newCost;
			    
		    for (int i = 0; i < n; i++) {
			DepthFirstSearch ls = lastSearch(search[2*i]);
 			ls.costValue = ((IntVar) costVariable).dom().max();
			ls.cost = new XltC((IntVar) search[2*i].costVariable, newCost);
		    }
		}

	    } else if (costVariable instanceof FloatVar) {
		double newCost = ((FloatVar) costVariable).dom().max();

		if (newCost < costValueFloat) {
		    costValueFloat = newCost;
		    master.costValueFloat = newCost;

		    for (int i = 0; i < n; i++) {
			DepthFirstSearch ls = lastSearch(search[2*i]);
			ls.costValueFloat = ((FloatVar) costVariable).dom().max();
			ls.cost = new PlteqC((FloatVar) search[2*i].costVariable, FloatDomain.previousForMinimization(newCost));
		    }
		}
	    }
	}

	void constraineCostFromChild(DepthFirstSearch child) {
	    if (costVariable instanceof IntVar) {
		int newCost = child.costValue;

		if (newCost < costValue) {
		    costValue = newCost;
		    master.costValue = newCost;
			    
		    for (int i = 0; i < n; i++) {
			DepthFirstSearch ls = lastSearch(search[2*i]);
 			ls.costValue = newCost;
			ls.cost = new XltC((IntVar) search[2*i].costVariable, newCost);
		    }
		}

	    } else if (costVariable instanceof FloatVar) {
		double newCost = child.costValueFloat;

		if (newCost < costValueFloat) {
		    costValueFloat = newCost;
		    master.costValueFloat = newCost;

		    for (int i = 0; i < n; i++) {
			DepthFirstSearch ls = lastSearch(search[2*i]);
			ls.costValueFloat = newCost;
			ls.cost = new PlteqC((FloatVar) search[2*i].costVariable, FloatDomain.previousForMinimization(newCost));
		    }
		}
	    }
	}

	public boolean labeling() {

    	    int index = getSubSearch();
	    if (index < n) {
		visited.set(index);

		boolean result = search[2*index].labeling();

		visited.set(index, false);
		return result;

	    } else { // index == n
		if (costVariable != null) {

		    if (master.childSearches != null) {

			 DepthFirstSearch childSearch = null;

			 for (DepthFirstSearch child : (DepthFirstSearch[])master.childSearches) {
			    childSearch = child;
			    child.setStore(store);
			    child.getSolutionListener().setParentSolutionListener(solutionListener);
			    child.setCostVar(costVariable);
                            int currentChildSolutionNo = child.getSolutionListener().solutionsNo();

		    	    boolean result = child.labeling();

		    	    if (result) {
				// gets here when the limit of solutions was reached
		    		break;
			    } else {
				if (child.getSolutionListener().solutionsNo() > currentChildSolutionNo) {
				    noSolutions = child.getSolutionListener().solutionsNo();

				    constraineCostFromChild(child);

				    if (noSolutions >= solutionsLimit)
					throw new SolutionsLimitReached();

				    master.solutionListener.executeAfterSolution(this, null);

				    visited.set(index, false);
				    return false;
				}
			    }
		    	}

			 noSolutions += childSearch.getSolutionListener().solutionsNo();
			 constraineCostFromChild(childSearch);
			 if (noSolutions >= solutionsLimit)
			     throw new SolutionsLimitReached();

			master.solutionListener.executeAfterSolution(this, null);

		    	visited.set(index, false);
		    	return false;
		    }
		    else {  // no child search

			constraineCost();
			noSolutions++;

			if (noSolutions >= solutionsLimit)
			    throw new SolutionsLimitReached();

			master.solutionListener.executeAfterSolution(this, null);

			visited.set(index, false);
			return false;
		    }
		} else if (master.childSearches != null) { // no optimization and child search
		    DepthFirstSearch childSearch = null;

		    for (DepthFirstSearch child : (DepthFirstSearch[])master.childSearches) {
			childSearch = child;
			child.setStore(store);
			child.getSolutionListener().setParentSolutionListener(solutionListener);
			int currentChildSolutionNo = child.getSolutionListener().solutionsNo();

			boolean result = child.labeling();

			if (result) {
			    // gets here when the limit of solutions was reached
			    break;
			} else {
			    if (child.getSolutionListener().solutionsNo() > currentChildSolutionNo) {
				noSolutions = child.getSolutionListener().solutionsNo();

				if (noSolutions >= solutionsLimit)
				    throw new SolutionsLimitReached();				    
				    
				master.solutionListener.executeAfterSolution(this, null);

				visited.set(index, false);
				return false;
			    }
			}
		    }

		    noSolutions += childSearch.getSolutionListener().solutionsNo();
		    if (noSolutions >= solutionsLimit)
			throw new SolutionsLimitReached();

		    master.solutionListener.executeAfterSolution(this, null);

		    visited.set(index, false);
		    return false;
		} else { // not optimization and no child search
		    noSolutions++;

		    master.solutionListener.executeAfterSolution(this, null);

		    if (noSolutions >= solutionsLimit)
			throw new SolutionsLimitReached();
		    
		    visited.set(index, false);
		    return false;
		}
	    }
	}
    }

    public int noSolutions() {
	return noSolutions;
    }
    
    final static class SolutionsLimitReached extends RuntimeException {

	SolutionsLimitReached() {
	}
    }
}

