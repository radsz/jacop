/**
 *  Search.java 
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

import org.jacop.core.Domain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * All searches needs to implement this interface in order to be manipulable by
 * a large variety of search listeners. Of course, the search which implements
 * this interface will need to call appropriate functions of attached listeners
 * in the right place and act accordingly to the output of listeners.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 * @param <T> type of variables used in this search.
 */

public interface Search<T extends Var> {

	/**
	 * It specifies the sub-searches for the current search. In order for the
	 * current search to succeed at least one of those must succeed. If there
	 * are no sub-searches then the current search succeeds if all variables
	 * within select choice point object are assigned and all constraints
	 * attached to those variables are satisfied.
	 * @param child the array containing all children searches.
	 */

	public void setChildSearch(Search<? extends Var>[] child);

	/**
	 * It adds another child search to this one.
	 * @param child the search which is being added as child search.
	 */
	public void addChildSearch(Search<? extends Var> child);

	/**
	 * It returns number of backtracks performed by the search.
	 * @return the number of backtracks.
	 */
	public int getBacktracks();

	
	/**
	 * It returns the cost variable. 
	 * @return cost variable.
	 */
	public Var getCostVariable();
	
	
	/**
	 * It returns the value of the cost int variable for the best solution.
	 * @return the cost value.
	 */
	public int getCostValue();

	/**
	 * It returns the value of the cost float variable for the best solution.
	 * @return the cost value.
	 */
	public double getCostValueFloat();
	
	/**
	 * It sets the optimization flag.
	 * @param value true if the search should optimize, false otherwise.
	 */
	public void setOptimize(boolean value);
	
	/**
	 * It returns number of decisions performed by the search.
	 * @return the number of decisions.
	 */
	public int getDecisions();

	/**
	 * It returns the maximum depth reached by a search.
	 * @return the maximum depth.
	 */

	public int getMaximumDepth();

	/**
	 * It returns number of search nodes explored by the search.
	 * @return number of search nodes.
	 */
	public int getNodes();

	/**
	 * It returns number of wrong decisions performed by the search.
	 * @return number of wrong decisions.
	 */
	public int getWrongDecisions();

	/**
	 * It returns the solution (an assignment of values to variables). 
	 * @return an array constituting the assignments.
	 */
	public Domain[] getSolution();

	/**
	 * It returns the solution specified by the search. The first
	 * solution has an index 1.
	 * 
	 * @param no the solution we are interested in.
	 * @return an array constituting the assignments.
	 */
	public Domain[] getSolution(int no);

	/**
	 * It returns the order of variables used by functions returning a solution
	 * in terms of the values.
	 * 
	 * @return an array of variables as used by functions getSolution.
	 */
	public T[] getVariables();

	/**
	 * This function is called recursively to assign variables one by one.
	 * @param firstVariable the index to the first variable which has not been grounded yet.
	 * @return true if the solution was found.
	 */

	boolean label(int firstVariable);

	/**
	 * It performs search, first by setting up the internal items/attributes of search, 
	 * followed later by a call to labeling function with argument specifying the index
	 * of the first not grounded variable.
	 *  
	 * @return true if the solution was found.
	 */
	public boolean labeling();

	/**
	 * It performs search using supplied choice point selection heuristic.
	 * @param store the store within which the search is conducted.
	 * @param select the selection choice point heuristic.
	 * @return true if the solution was found.
	 */
	public boolean labeling(Store store, SelectChoicePoint<T> select);

	/**
	 * It performs search using supplied choice point selection heuristic, 
	 * as well as costVariable as aim at finding an optimal solution.
	 * 
	 * @param store constraint store which will be used by labeling.
	 * @param select the selection choice point heuristic.
	 * @param costVar variable to specify cost.
	 * @return true if the solution was found.
	 */
	public boolean labeling(Store store, SelectChoicePoint<T> select, Var costVar);

	/**
	 * It decides if a solution is assigned to store after search exits.
	 * 
	 * @param value defines if solution is assigned.
	 * 
	 */

	public void setAssignSolution(boolean value);

	/**
	 * It turns on the backtrack out.
	 * 
	 * @param out defines how many backtracks are performed before the search
	 *            exits.
	 */
	public void setBacktracksOut(long out);

	/**
	 * It turns on the decisions out.
	 * 
	 * @param out defines how many decisions are made before the search exits.
	 */
	public void setDecisionsOut(long out);

	/**
	 * It turns on the nodes out.
	 * 
	 * @param out
	 *            defines how many nodes are visited before the search exits.
	 */
	public void setNodesOut(long out);

	/**
	 * It decides if information about search is printed.
	 * 
	 * @param value
	 *            defines if info is printed to standard output.
	 */

	public void setPrintInfo(boolean value);

	/**
	 * It turns on the timeout.
	 * 
	 * @param out
	 *            defines how many seconds before the search exits.
	 */
	public void setTimeOut(long out);

	/**
	 * It turns on the wrong decisions out.
	 * 
	 * @param out
	 *            defines how many wrong decisions are made before the search
	 *            exits.
	 */
	public void setWrongDecisionsOut(long out);

	public String toString();

	/**
	 * It returns the root Solution Listener.
	 * @return the root Solution Listener.
	 */
	public SolutionListener<T> getSolutionListener();

	/**
	 * It returns the root of the Consistency Listener.
	 * @return the root Consistency Listener.
	 */
	public ConsistencyListener getConsistencyListener();

	/**
	 * It returns the root of the ExitChildListener.
	 * @return the root of ExitChildListener.
	 */
	public ExitChildListener<T> getExitChildListener();

	/**
	 * It returns the root of the ExitListener.
	 * @return the root of ExitListener.
	 */
	public ExitListener getExitListener();

	/**
	 * It returns the root of the TimeOutListener.
	 * @return the root of the TimeOutListener.
	 */
	public TimeOutListener getTimeOutListener();

	/**
	 * It returns the root of the InitializationListener. 
	 * @return the root of the InitializeListener. 
	 */
	public InitializeListener getInitializeListener();
	
	/**
	 * It returns the root of the SolutionListener.
	 * @param listener the root of the SolutionListener.
	 */
	public void setSolutionListener(SolutionListener<T> listener);

	/**
	 * It sets the root of the Consistency Listener.
	 * @param listener the new root.
	 */
	public void setConsistencyListener(ConsistencyListener listener);

	/**
	 * It sets the root of the ExitChild listener.
	 * @param listener the new root.
	 */
	public void setExitChildListener(ExitChildListener<T> listener);

	/**
	 * It sets the root of the Exit Listener.
	 * @param listener the new root.
	 */
	public void setExitListener(ExitListener listener);

	/**
	 * It sets the root of the TimeOutListener. 
	 * @param listener the new root.
	 */
	public void setTimeOutListener(TimeOutListener listener);
	
	/**
	 * It sets the root of the InitializeListener.
	 * @param listener the new root.
	 */
	public void setInitializeListener(InitializeListener listener);
	
	/**
	 * It sets the select choice point object. 
	 * @param select the choice point heuristic used by search. 
	 */
	public void setSelectChoicePoint(SelectChoicePoint<T> select);

	/**
	 * It sets the reference to the store in the context of which the search operates.
	 * @param store the store in which context the search operates.
	 */
	public void setStore(Store store);

	/**
	 * It sets the reference to the cost variable. It does not automatically mean 
	 * that the search optimizes. 
	 * @param cost variable used as a cost metric.
	 */
	public void setCostVar(Var cost);

	/**
	 * If the search is called by a master search then the search may need to
	 * obtain some information about the master search. For example, the textual
	 * description of the solution.
	 * @param master master search which will be/is calling that slave search.
	 */

	public void setMasterSearch(Search<? extends Var> master);

	/**
	 * It returns the string id of the search.
	 * @return the string id of the search.
	 */
	public String id();

	/**
	 * The first solution has index 0.
	 * @param no the solution number which we want to enforce in the store.
	 * @return true if the store is consistent after imposing the solution.
	 */
	public boolean assignSolution(int no);

	
	/**
	 * It assigns the last solution.
	 * @return true if the store is consistent after imposing the last solution.
	 */
	public boolean assignSolution();

	
	/**
	 * It prints all solutions.
	 */
	public void printAllSolutions();

}
