/**
 *  DepthFirstSearch.java 
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

package org.jacop.search;

import java.lang.reflect.Array;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XltC;
import org.jacop.core.Domain;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.SwitchesPruningLogging;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.constraints.PltC;

/**
 * Implements Depth First Search with number of possible plugins (listeners) to
 * be attached to modify the search.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 * @param <T> type of variables used in this search. 
 */

public class DepthFirstSearch<T extends Var> implements Search<T> {

    //@todo make debugAll be used in printing statements.
    static final boolean debugAll = true;

    /**
     * If it is set to true then the optimizing search will 
     * quit the search if this action is indicated by the solution
     * listener.
     */
    public boolean respectSolutionListenerAdvice = false;

    /**
     * It decides if the found solution is immediately assigned to
     * the store.* If the solution is not assigned immediately
     * after the search is concluded but later then special care
     * may be required. As soon as search exits all
     * propagations (including the first time consistency execution
     * of the constraints) may be forgotten. Even worse some
     * values of the variables for which the constraint was
     * never aware of (not even at impose time) may appear back in
     * the domain. The best remedy for this problem is to call
     * store.consistency() method once and only once after the
     * model is imposed and before the search is executed and never
     * remove the level at which the store resides after
     * store.consistency() method is executed.
     */

    boolean assignSolution = true;

    /**
     * It specifies after how many backtracks the search exits.
     */
    long backtracksOut = -1;

    /**
     * It specifies if the backtrack out is on.
     */

    boolean backtracksOutCheck = false;

    /**
     * It specifies if search can exit before the search has finished.
     */
    boolean check = false;

    /**
     * It represents the constraint which enforces that next solution is better
     * than currently best solution.
     */

    Constraint cost = null;

    /**
     * It represents the cost value of currently best solution for IntVar cost.
     */
    public int costValue = Integer.MAX_VALUE;

    /**
     * It represents the cost value of currently best solution for FloatVar cost.
     */
    public double costValueFloat = FloatDomain.MaxFloat;

    /**
     * It represents the cost variable.
     */

    public Var costVariable = null;

    boolean optimize = false;
	
    /**
     * It stores number of nodes with decisions during search.
     */
    int decisions = 0;

    /**
     * It specifies after how many decisions the search exits.
     */
    long decisionsOut = -1;

    /**
     * It specifies if the decisions out is on.
     */
    boolean decisionsOutCheck = false;

    /**
     * It represents current depth of store used in search.
     */
    int depth = 0;

    /**
     * It stores current depth of the search excluding paths in a search tree.
     */

    int depthExcludePaths = 0;

    /**
     * It represents the choice point selection heuristic.
     */

    SelectChoicePoint<T> heuristic = null;

    /**
     * It is invoked when returning from left or right child.
     */

    public ExitChildListener<T> exitChildListener;

    /**
     * It is invoked when consistency function has been executed.
     */

    public ConsistencyListener consistencyListener;

    /**
     * It is executed when a solution is found.
     */

    public SolutionListener<T> solutionListener = new SimpleSolutionListener<T>();

    /**
     * It is executed when search is started, before entering the search.
     */

    public InitializeListener initializeListener;
		
    /**
     * It stores the maximum depth reached during search.
     */
    int maxDepth = 0;

    /**
     * It stores the maximum depth of the search excluding paths.
     */
    int maxDepthExcludePaths = 0;

    /**
     * It stores number of nodes visited during search.
     */
    int nodes = 0;

    /**
     * It specifies after how many nodes the search exits.
     */
    long nodesOut = -1;

    /**
     * It specifies if the nodes out is on.
     */
    boolean nodesOutCheck = false;

    /**
     * It stores number of backtracks during search. A backtrack is a search
     * node for which all children has failed.
     */
    int numberBacktracks = 0;

    /**
     * It decides if information about search is printed.
     */

    boolean printInfo = true;

    /**
     * It stores searches which will be executed when this one has assign all
     * its variables.
     */

    public Search<? extends Var>[] childSearches;

    /**
     * If this search is a sub-search then this pointer will point out to the
     * master search (i.e. the search which have invoked this search).
     */

    public Search<? extends Var> masterSearch;

    /**
     * It represents store within which a search is performed.
     */

    public Store store = null;

    /**
     * The object informed about the determination of the timeout.
     */

    TimeOutListener timeOutListener = null;

    /**
     * It is executed upon search exit. It allows to add learnt constraints.
     */

    ExitListener exitListener = null;

    /**
     * It specifies the exact time point after which the timeout will occur (in
     * miliseconds).
     */

    long timeOut;

    /**
     * It specifies if the timeout is on.
     */

    boolean timeOutCheck = false;

    /**
     * It specifies that the time-out has occured
     */

    public boolean timeOutOccured;

    /**
     * It specifies the number of seconds after which the search will timeout.
     */

    long tOut = -1;

    /**
     * It stores number of wrong decisions during search. A wrong decision is a
     * leaf of a search which has failed.
     */

    int wrongDecisions = 0;

    /**
     * It specifies after how many wrong decisions the search exits.
     */

    long wrongDecisionsOut = -1;

    /**
     * It specifies if the wrong decisions out is on.
     */

    boolean wrongDecisionsOutCheck = false;

    static int no = 0;

    /**
     * It specifies the id of the search.
     */
    public String id = "DFS" + no;

    /**
     * It specifies if for setVar based search the left branch should impose EinA constraint.
     */
    public boolean einAinleftTree = true;
	
    /**
     * It sets the id of the store.
     * @param name the id of the store object.
     */
    public void setID(String name) {
	id = name;
    }

    public String id() {
	return id;
    }

    /**
     * It specifies current child search.
     */

    public DepthFirstSearch() {

	no++;

    }

    public void setChildSearch(Search<? extends Var>[] child) {

        if (childSearches != null) {
            for (Search<? extends Var> c : childSearches)
                c.setMasterSearch(null);
        }
	childSearches = child;

        if (childSearches != null) {
            for (Search<? extends Var> c : childSearches)
                c.setMasterSearch(this);
        }

    }

    public void addChildSearch(Search<? extends Var> child) {

	if (childSearches == null) {
	    childSearches = (Search<? extends Var>[])Array.newInstance(child.getClass(), 1);
	    // FIXME, check and removed.
	    //		childSearches = new Search[1];
	    childSearches[0] = child;
	} else {

	    Search<? extends Var>[] old = childSearches;
	    childSearches = (Search<? extends Var>[])Array.newInstance(child.getClass(), childSearches.length + 1);
	    // FIXME, check and remove.
	    //	childSearches = new Search[childSearches.length + 1];
	    System.arraycopy(old, 0, childSearches, 0, old.length);
	    childSearches[old.length] = child;
	}

        child.setMasterSearch(this);

    }

    /**
     * It remembers what child search has been already examined.
     */
    public int currentChildSearch = -1;

    public void setSelectChoicePoint(SelectChoicePoint<T> select) {
	heuristic = select;
    }

    /**
     * It returns number of backtracks performed by the search.
     */
    public int getBacktracks() {
	return numberBacktracks;
    }

    /**
     * It returns number of decisions performed by the search.
     */
    public int getDecisions() {
	return decisions;
    }

    /**
     * It returns the maximum depth reached by a search.
     */

    public int getMaximumDepth() {
	return maxDepthExcludePaths;
    }

    /**
     * It returns number of search nodes explored by the search.
     */
    public int getNodes() {
	return nodes;
    }

    /**
     * It returns number of wrong decisions performed by the search.
     */
    public int getWrongDecisions() {
	return wrongDecisions;
    }

    public Domain[] getSolution() {
	return solutionListener.getSolution(solutionListener.solutionsNo());
    }

    public Domain[] getSolution(int no) {
	return solutionListener.getSolution(no);
    }

    public T[] getVariables() {

	T[] vars = solutionListener.getVariables();

	if (vars != null)
	    return vars;

	assert (false) : "Fix it. Uncomment below.";
		
	return null;
		
	/*
	  IdentityHashMap<T, Integer> position = heuristic.getVariablesMapping();

	  vars = new Var[position.size()];

	  for (Iterator<? extends Var> itr = position.keySet().iterator(); itr
	  .hasNext();) {
	  Var current = itr.next();
	  vars[position.get(current)] = current;
	  }

	  return vars;
		
	*/
    }

    public SolutionListener<T> getSolutionListener() {

	return solutionListener;

    }

    /**
     * This function is called recursively to assign variables one by one.
     */

    public boolean label(int firstVariable) {

	int val = 0;
	T fdv;
	PrimitiveConstraint choice = null;
	boolean consistent;

	// int textInterfaceLength = 0;

	if (check) {

	    if (timeOutCheck)
		if (System.currentTimeMillis() > timeOut) {
		    timeOutOccured = true;
		    if (timeOutListener != null)
			timeOutListener.executedAtTimeOut(solutionListener
							  .solutionsNo());
		    return false;
		}

	    if (nodesOutCheck)
		if (nodes > nodesOut) {
		    timeOutOccured = true;
		    if (timeOutListener != null)
			timeOutListener.executedAtTimeOut(solutionListener
							  .solutionsNo());
		    return false;
		}

	    if (decisionsOutCheck)
		if (decisions > decisionsOut) {
		    timeOutOccured = true;
		    if (timeOutListener != null)
			timeOutListener.executedAtTimeOut(solutionListener
							  .solutionsNo());
		    return false;
		}

	    if (wrongDecisionsOutCheck)
		if (wrongDecisions > wrongDecisionsOut) {
		    timeOutOccured = true;
		    if (timeOutListener != null)
			timeOutListener.executedAtTimeOut(solutionListener
							  .solutionsNo());
		    return false;
		}

	    if (backtracksOutCheck)
		if (numberBacktracks > backtracksOut) {
		    timeOutOccured = true;
		    if (timeOutListener != null)
			timeOutListener.executedAtTimeOut(solutionListener
							  .solutionsNo());
		    return false;
		}

	}

	// Instead of imposing constraint just restrict bounds
	// -1 since costValue is the cost of last solution
	if (optimize && cost != null)
	    try {
		// cost IntVar
		if (costVariable instanceof IntVar) {
		    if (((IntVar)costVariable).min() <= costValue - 1)
			((IntVar)costVariable).domain.in(store.level, (IntVar)costVariable,
							 ((IntVar)costVariable).min(), costValue - 1);
		    else {
			if (consistencyListener != null)
			    consistencyListener.executeAfterConsistency(false);

			return false;
		    }
		}
		// cost FloatVar
		else if (costVariable instanceof FloatVar) {
		    if (((FloatVar)costVariable).min() <= FloatDomain.previous(costValueFloat))
			((FloatVar)costVariable).domain.in(store.level, (FloatVar)costVariable,
							   ((FloatVar)costVariable).min(), FloatDomain.previous(costValueFloat));
		    else {
			if (consistencyListener != null)
			    consistencyListener.executeAfterConsistency(false);

			return false;
		    }
		}
	    } catch (FailException f) {
		if (consistencyListener != null)
		    consistencyListener.executeAfterConsistency(false);
		return false;
	    }

	// all search nodes begins here
	nodes++;
		
	consistent = store.consistency();
				
	if (consistencyListener != null)
	    consistent = consistencyListener.executeAfterConsistency(consistent);
		
	if (!consistent) {
	    // Failed leaf of the search tree
	    wrongDecisions++;
	    return false;
	} else { // consistent

	    store.setLevel(++depth);
	    maxDepth = (depth > maxDepth) ? depth : maxDepth;

	    // Delete function indicates which is next variable for
	    // labeling

	    fdv = heuristic.getChoiceVariable(firstVariable);

	    if (fdv != null) {

		val = heuristic.getChoiceValue();				
		assert (store.currentConstraint == null);

		//		maybe a boolean flag, if search should work
		//		C, not(C) versus not(C), C;
				
		/**
		 * Possible changes to Search. Indomain returns int. 
		 * for intVar it is an assignment. inValue(). 
		 * for serVar this is EinA() constraint, inGLB(value)
		 * add boolean flag reversedOrder = false; 
		 * Only accepted for SetVar search. 
		 * Double check that firstVariable is ok with this
		 * non grounding of values even in case of var,value pair.
		 */
				
		if (fdv instanceof IntVar)
		    ((IntDomain)fdv.dom()).inValue(store.level, (IntVar)fdv, val);
				
		if (fdv instanceof SetVar)
		    if (einAinleftTree)
			((SetDomain)fdv.dom()).inGLB(store.level, (SetVar)fdv, val);
		    else
			((SetDomain)fdv.dom()).inLUBComplement(store.level, (SetVar)fdv, val);
				
		decisions++;

		depthExcludePaths++;
		if (depthExcludePaths > maxDepthExcludePaths)
		    maxDepthExcludePaths = depthExcludePaths;

	    } else {

		choice = heuristic.getChoiceConstraint(firstVariable);

		if (choice == null) {

		    // Solution already found so this is not a search node
		    nodes--;
		    // Execute subsearches if given.
					
		    if (childSearches != null) {

			boolean childResult = false;
                        boolean childFoundSolution = false;
			currentChildSearch = 0;

			for (; currentChildSearch < childSearches.length
				 && !childResult; currentChildSearch++) {
			    childSearches[currentChildSearch].getSolutionListener().setParentSolutionListener(solutionListener);
			    childSearches[currentChildSearch].setStore(store);

			    if (costVariable != null)
				childSearches[currentChildSearch].setCostVar(costVariable);

                            int currentChildSolutionNo = childSearches[currentChildSearch].getSolutionListener().solutionsNo();
			    childResult = childSearches[currentChildSearch].labeling();
                            if (childSearches[currentChildSearch].getSolutionListener().solutionsNo() > currentChildSolutionNo)
                                childFoundSolution = true;

			    if (childResult)
				break;

                            if (costVariable != null) {
				if (costVariable instanceof IntVar) {
				    int childCostValue = childSearches[currentChildSearch].getCostValue();
				    if (childCostValue < costValue) {
					costValue = childCostValue;
					cost = new XltC((IntVar)costVariable, costValue);
				    }
				    if (childCostValue <= ((IntVar)costVariable).min())
					// other child searches will not be able to find any solutions.
					break;
				    else {
					((IntVar)costVariable).domain.inMax(store.level, (IntVar)costVariable, childCostValue - 1);
				    }
				}
				else if (costVariable instanceof FloatVar) {
				    double childCostValue = childSearches[currentChildSearch].getCostValueFloat();
				    if (childCostValue < costValueFloat) {
					costValueFloat = childCostValue;
					// cost = new PltC((FloatVar)costVariable, costValueFloat);
					cost = new org.jacop.floats.constraints.PlteqC((FloatVar)costVariable, FloatDomain.previous(costValueFloat)); //costValueFloat - FloatDomain.epsilon(costValueFloat));
				    }
				    if (childCostValue <= ((FloatVar)costVariable).min())
					// other child searches will not be able to find any solutions.
					break;
				    else {
					((FloatVar)costVariable).domain.inMax(store.level, (FloatVar)costVariable, FloatDomain.previous(childCostValue));
				    }
				}
			    }
			}

			if (childResult && costVariable != null) {
			    if (costVariable instanceof IntVar) {
				int childCostValue = childSearches[currentChildSearch].getCostValue();
				if (childCostValue < costValue)
				    costValue = childCostValue;
				cost = new XltC((IntVar)costVariable, costValue);
			    }
			    else if (costVariable instanceof FloatVar) {
				double childCostValue = childSearches[currentChildSearch].getCostValueFloat();
				if (childCostValue < costValueFloat) 
				    costValueFloat = childCostValue;
				cost = new PltC((FloatVar)costVariable, costValueFloat);
				// cost = new org.jacop.floats.constraints.PlteqC((FloatVar)costVariable, FloatDomain.previous(costValueFloat)); //costValueFloat - FloatDomain.epsilon(costValueFloat));
			    }

			}
						
			boolean stopMasterSearch = false;
						
			if (childResult || childFoundSolution) {
			    // Child search found solution, so there is a
			    // solution
			    // for this search too.

			    stopMasterSearch = solutionListener.executeAfterSolution(this, heuristic);

                            if (!childResult)
                                stopMasterSearch = false;
			}

			store.removeLevel(depth);
			store.setLevel(--depth);
			fdv = null;						
						
			if (!respectSolutionListenerAdvice && optimize) {

			    return false;
			}

			return stopMasterSearch;

		    }

		    if (costVariable != null) {
			// it does not mean there is an optimization, only that we want to remember the value
			// of the costVariable
			if (costVariable instanceof IntVar) {
			    costValue = ((IntVar)costVariable).dom().min();
			    cost = new XltC((IntVar)costVariable, costValue);
			}
			else if (costVariable instanceof FloatVar) {
			    costValueFloat = ((FloatVar)costVariable).dom().max();
			    cost = new PltC((FloatVar)costVariable, costValueFloat);
			    // cost = new org.jacop.floats.constraints.PlteqC((FloatVar)costVariable, FloatDomain.previous(costValueFloat)); //costValueFloat - FloatDomain.epsilon(costValueFloat));
			}

		    }
					
		    if (!respectSolutionListenerAdvice && optimize) {

			solutionListener.executeAfterSolution(this, heuristic);

			store.removeLevel(depth);
			store.setLevel(--depth);
					
			return false;
		    }
					
		    boolean returnCode = solutionListener.executeAfterSolution(this, heuristic);
					
		    store.removeLevel(depth);
		    store.setLevel(--depth);
					
		    return returnCode;

		} else {

		    assert (store.currentConstraint == null);
		    store.impose(choice);
		    decisions++;

		    depthExcludePaths++;
		    if (depthExcludePaths > maxDepthExcludePaths)
			maxDepthExcludePaths = depthExcludePaths;

		}

	    }

	    // choice point imposed.
			
	    consistent = label(heuristic.getIndex());

	    if (exitChildListener != null)
		if ((choice == null && !exitChildListener.leftChild(fdv, val,
								    consistent))
		    || (choice != null && !exitChildListener.leftChild(
								       choice, consistent))) {
		    store.removeLevel(depth);
		    store.setLevel(--depth);
		    depthExcludePaths--;
		    fdv = null;
		    return false;
		}

            if (consistent) {
		fdv = null;
		store.removeLevel(depth);
		store.setLevel(--depth);
		depthExcludePaths--;
		return true;
	    } else {

		// Assigning current variable to a value indicated by
		// indomain result in a failure, this value is removed
		// from the domain and label is called recursively with
		// the same currentVariable.

		store.removeLevel(depth);

		Object args[] = {depth, fdv, val};

                if (SwitchesPruningLogging.traceSearchTree) {
		    SwitchesPruningLogging.log(choice == null, DepthFirstSearch.class, "Store level: {}, Right branch: {} \\ {}", args);
		    SwitchesPruningLogging.log(choice != null, DepthFirstSearch.class, "Store level: {}, Right branch: {}", depth, choice);
                }

		if (choice != null) {

		    assert (store.currentConstraint == null);

		    store.setLevel(store.level);

		    store.impose(new Not(choice));
					
		    consistent = label(firstVariable);

		    if (exitChildListener != null)
			exitChildListener.rightChild(choice, consistent);

		    if (!consistent)
			numberBacktracks++;

		    store.removeLevel(depth);

					
		}
		//				else if (!fdv.dom().singleton(val)) {
		else if (!fdv.dom().singleton()) {

		    assert (store.currentConstraint == null);
						
		    store.setLevel(store.level);

		    if (fdv instanceof IntVar)
			((IntDomain)fdv.dom()).inComplement(store.level, (IntVar)fdv, val);

		    if (fdv instanceof SetVar)
			if (einAinleftTree)
			    ((SetDomain)fdv.dom()).inLUBComplement(store.level, (SetVar)fdv, val);
			else	
			    ((SetDomain)fdv.dom()).inGLB(store.level, (SetVar)fdv, val);

		    consistent = label(firstVariable);

		    if (exitChildListener != null)
			exitChildListener.rightChild(fdv, val, consistent);

		    if (!consistent)
			numberBacktracks++;

		    store.removeLevel(depth);

		} else {
		    fdv = null;
		    consistent = false;
		}

		store.setLevel(--depth);

		depthExcludePaths--;

		if (consistent) {
		    return true;
		} else {
		    return false;
		}
	    }
	}
    }

    public void setStore(Store store) {
	this.store = store;
    }

    public void setCostVar(Var cost) {

	costVariable = cost;

    }

    /**
     * It is a labeling function called if the search is a sub-search being
     * called from the parent search. It never assigns a solution as it will be
     * immediately retracted by search calling this one.
     */

    public boolean labeling() {

	boolean raisedLevel = false;

	if (store.raiseLevelBeforeConsistency) {
	    store.raiseLevelBeforeConsistency = false;
	    store.setLevel(store.level + 1);
	    raisedLevel = true;
	}

	depth = store.level;
	cost = null;
	// 		timeOutOccured = false;
	// 		timeOut = System.currentTimeMillis() + tOut * 1000;

	if (costVariable == null)
	    optimize = false;

	// 		decisions = 0;
	// 		numberBacktracks = 0;
	// 		nodes = 0;
	// 		wrongDecisions = 0;
	// 		depthExcludePaths = 0;
	// 		maxDepthExcludePaths = 0;

	if (initializeListener != null)
	    initializeListener.executedAtInitialize(store);
		
	// Iterative Solution listener sets it to zero so it can find the next batch, so it has to be executed
	// after initialize listener.
	int solutionNoBeforeSearch = solutionListener.solutionsNo();
		
	// If constraints employ only one time execution of the part of 
	// the consistency technique then the results of that part must be
	// stored in one level above the level search starts from as this
	// can be removed. 
	boolean result = store.consistency();
	store.setLevel(store.level + 1);
	depth = store.level;
		
	if (result)
	    result = label(0);

	store.removeLevel(store.level);
	store.setLevel(store.level - 1);
	depth--;			
				
	if (exitListener != null)
	    exitListener.executedAtExit(store, solutionListener.solutionsNo());

	if (timeOutOccured) {

	    if (printInfo)
		System.out.println("Time-out " + tOut + "s");

	}

	if (solutionListener.solutionsNo() > solutionNoBeforeSearch) {

	    if (printInfo) {
		if (costVariable != null)
		    if (costVariable instanceof IntVar)
			System.out.println("Solution cost is " + costValue);
		    else if (costVariable instanceof IntVar)
			System.out.println("Solution cost is " + costVariable.dom());
			
		System.out.println(this);
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
				
		StringBuffer buf = new StringBuffer();
				
		buf.append("Depth First Search " + id + "\n");
		buf.append("\n");
		buf.append("Nodes : ").append(nodes).append("\n");
		buf.append("Decisions : ").append(decisions).append("\n");
		buf.append("Wrong Decisions : ").append(wrongDecisions).append("\n");
		buf.append("Backtracks : ").append(numberBacktracks).append("\n");
		buf.append("Max Depth : ").append(maxDepthExcludePaths).append("\n");

		System.out.println( buf.toString() );
				
	    }			

	    if (raisedLevel) {
		store.removeLevel(store.level);
		store.setLevel(store.level - 1);
	    }

	    return false;
	}

    }

    public boolean labeling(Store store, SelectChoicePoint<T> select) {

	this.store = store;

	if (store.raiseLevelBeforeConsistency) {
	    store.raiseLevelBeforeConsistency = false;
	    store.setLevel(store.level + 1);
	}

	heuristic = select;
	depth = store.level;
	// 		timeOutOccured = false;
	// 		timeOut = System.currentTimeMillis() + tOut * 1000;

	if (costVariable == null)
	    optimize = false;
		
	// 		decisions = 0;
	// 		numberBacktracks = 0;
	// 		nodes = 0;
	// 		wrongDecisions = 0;
	// 		depthExcludePaths = 0;
	// 		maxDepthExcludePaths = 0;

	if (initializeListener != null)
	    initializeListener.executedAtInitialize(store);
		
	// Iterative Solution listener sets it to zero so it can find the next batch, so it has to be executed
	// after initialize listener.
	int solutionNoBeforeSearch = solutionListener.solutionsNo();
		
	boolean result = store.consistency();
	store.setLevel(store.level + 1);
	depth = store.level;

	if (result) 
	    result = label(0);

	store.removeLevel(store.level);
	store.setLevel(store.level - 1);
	depth--;			

	if (exitListener != null)
	    exitListener.executedAtExit(store, solutionListener.solutionsNo() - solutionNoBeforeSearch);

	if (timeOutOccured) {

	    if (printInfo)
		System.out.println("Time-out " + tOut + "s");

	}

	if (solutionListener.solutionsNo() > solutionNoBeforeSearch) {
			
	    if (assignSolution)
		assignSolution();

	    if (printInfo)
		System.out.println(this);
			
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

		System.out.println( buf.toString() );
				
	    }			
	    return false;
	}

    }

    public boolean labeling(Store store, SelectChoicePoint<T> select, Var costVar) {

	this.store = store;

	if (store.raiseLevelBeforeConsistency) {
	    store.raiseLevelBeforeConsistency = false;
	    store.setLevel(store.level + 1);
	}

	heuristic = select;
	depth = store.level;
	costVariable = costVar;
	optimize = true;
	cost = null;
	// 		timeOutOccured = false;
	// 		timeOut = System.currentTimeMillis() + tOut * 1000;

	// 		decisions = 0;
	// 		numberBacktracks = 0;
	// 		nodes = 0;
	// 		wrongDecisions = 0;
	// 		depthExcludePaths = 0;
	// 		maxDepthExcludePaths = 0;

	if (initializeListener != null)
	    initializeListener.executedAtInitialize(store);
		
	// Iterative Solution listener sets it to zero so it can find the next batch, so it has to be executed
	// after initialize listener.
	int solutionNoBeforeSearch = solutionListener.solutionsNo();
		
	boolean result = store.consistency();
	store.setLevel(store.level + 1);
	depth = store.level;
		
	if (result)
	    result = label(0);

	store.removeLevel(store.level);
	store.setLevel(store.level - 1);
	depth--;		
		
	if (exitListener != null)
	    exitListener.executedAtExit(store, solutionListener.solutionsNo());

	if (timeOutOccured) {

	    if (printInfo)
		System.out.println("Time-out " + tOut + "s");

	}

	if (solutionListener.solutionsNo() > solutionNoBeforeSearch) {
			
	    if (assignSolution)
		assignSolution();

	    if (printInfo)
		if (costVariable instanceof IntVar)
		    System.out.println("Solution cost is " + costValue);
		else if (costVariable instanceof FloatVar)
		    System.out.println("Solution cost is " + costVariable.dom());

	    if (printInfo)
		System.out.println(this);

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

		System.out.println( buf.toString() );
				
	    }
	    return false;
	}

    }

    /**
     * It decides if a solution is assigned to store after search exits.
     * 
     * @param value defines if solution is assigned.
     */

    public void setAssignSolution(boolean value) {
	assignSolution = value;
    }

    /**
     * It turns on the backtrack out.
     * 
     * @param out
     *            defines how many backtracks are performed before the search
     *            exits.
     */
    public void setBacktracksOut(long out) {
	backtracksOut = out;
	check = true;
	backtracksOutCheck = true;
    }

    /**
     * It turns on the decisions out.
     * 
     * @param out
     *            defines how many decisions are made before the search exits.
     */
    public void setDecisionsOut(long out) {
	decisionsOut = out;
	check = true;
	decisionsOutCheck = true;
    }

    /**
     * It turns on the nodes out.
     * 
     * @param out
     *            defines how many nodes are visited before the search exits.
     */
    public void setNodesOut(long out) {
	nodesOut = out;
	check = true;
	nodesOutCheck = true;
    }

    /**
     * It decides if information about search is printed.
     * 
     * @param value
     *            defines if info is printed to standard output.
     */

    public void setPrintInfo(boolean value) {
	printInfo = value;
    }

    /**
     * It turns on the timeout.
     * 
     * @param out
     *            defines how many seconds before the search exits.
     */
    public void setTimeOut(long out) {
	tOut = out;
	check = true;
	timeOutCheck = true;
	timeOut = System.currentTimeMillis() + tOut * 1000;
    }

    /**
     * It turns on the wrong decisions out.
     * 
     * @param out
     *            defines how many wrong decisions are made before the search
     *            exits.
     */
    public void setWrongDecisionsOut(long out) {
	wrongDecisionsOut = out;
	check = true;
	wrongDecisionsOutCheck = true;
    }

    public void setMasterSearch(Search<? extends Var> master) {

	masterSearch = master;

    }

    @Override
	public String toString() {

	StringBuffer buf = new StringBuffer();

	buf.append("Depth First Search " + id + "\n");

	buf.append(heuristic);

	buf.append("\n" + solutionListener.toString());

	if (costVariable != null)
	    if (costVariable instanceof IntVar)
		buf.append("Cost " + costValue + "\n");
	    else if (costVariable instanceof FloatVar)
		buf.append("Cost " + costVariable.dom() + "\n");

	buf.append("Nodes : ").append(nodes).append("\n");
	buf.append("Decisions : ").append(decisions).append("\n");
	buf.append("Wrong Decisions : ").append(wrongDecisions).append("\n");
	buf.append("Backtracks : ").append(numberBacktracks).append("\n");
	buf.append("Max Depth : ").append(maxDepthExcludePaths).append("\n");

	return buf.toString();
    }

    public boolean assignSolution() {

	if (solutionListener.solutionsNo() != 0)
	    return assignSolution( solutionListener.solutionsNo() - 1);
	else
	    return assignSolution( 0 );
		
    }

    public boolean assignSolution(int no) {

	boolean result;
		
	if (solutionListener.isRecordingSolutions())
	    result = solutionListener.assignSolution(store, no);
	else
	    result = solutionListener.assignSolution(store, 0);

	if (!result)
	    return false;

	if (childSearches != null) {
	    int match = -1;
			
	    currentChildSearch = 0;
	    for (; currentChildSearch < childSearches.length
		     && match == -1; currentChildSearch++)
		match = childSearches[currentChildSearch].getSolutionListener().findSolutionMatchingParent(no);
			
	    if (match == -1)
		return false;
	    return childSearches[currentChildSearch-1].assignSolution(match);
	}

	return true;

    }

    public ConsistencyListener getConsistencyListener() {
	return consistencyListener;
    }

    public ExitChildListener<T> getExitChildListener() {
	return exitChildListener;
    }

    public ExitListener getExitListener() {
	return exitListener;
    }

    public TimeOutListener getTimeOutListener() {
	return timeOutListener;
    }

    public void setSolutionListener(SolutionListener<T> listener) {
	solutionListener = listener;
    }

    public void setConsistencyListener(ConsistencyListener listener) {
	consistencyListener = listener;
    }

    public void setExitChildListener(ExitChildListener<T> listener) {
	exitChildListener = listener;
    }

    public void setExitListener(ExitListener listener) {
	exitListener = listener;
    }

    public void setTimeOutListener(TimeOutListener listener) {
	timeOutListener = listener;
    }

    public InitializeListener getInitializeListener() {
	return initializeListener;
    }

    public void setInitializeListener(InitializeListener listener) {
	initializeListener = listener;
    }
	
    public void printAllSolutions() {
    	solutionListener.printAllSolutions();
    }

    public Var getCostVariable() {
	return costVariable;
    }

    public int getCostValue() {
	return costValue;
    }

    public double getCostValueFloat() {
	return costValueFloat;
    }

    public void setOptimize(boolean value) {
	optimize = value;
    }
	
}
