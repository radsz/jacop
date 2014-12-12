/**
 *  SolutionListener.java 
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

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Domain;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Defines an interface which needs to be implemented by all classes which wants
 * to be informed about the solution.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 * @param <T> type of variable for which the solution is being stored.
 */

public interface SolutionListener<T extends Var> {

	/**
	 * It is executed by search after a solution is found. 
	 * 
	 * @param search the search which have found a solution.  
	 * @param select the select choice point heuristic
	 * @return false forces the search to keep looking for a solution, true then the search will accept a solution.
	 */

	public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select);

	/**
	 * It imposes the constraints, so the last found solution is enforced.
	 * @param store store in which the solution is enforced.
	 * @param no the number of the solution to be enforced.
	 * @return true if the store is consistent after enforcing a solution, false otherwise.
	 */

	public boolean assignSolution(Store store, int no);

	/**
	 * It returns the string representation of the last solution.
	 */

	public String toString();

	/**
	 * It returns the variables in the same order as the one used to encode
	 * solutions.
	 * @return list of variables
	 */
	public T[] getVariables();

	/**
	 * It returns all solutions. Each solution is in a separate array.
	 * @return first dimension is indexed by solution, second dimension is indexed by a variable.
	 */

	public Domain[][] getSolutions();

	/**
	 * It returns a collection of constraints which represent the last found
	 * solution.
	 * @return the set of constraints which imposed enforce the last found solution.
	 */

	public PrimitiveConstraint[] returnSolution();

	/**
	 * It returns the solution number no. The first solution has an index 0.
	 * @param no it obtains the solution with a given index.
	 * @return array containing assignments to search variables.
	 */

	public Domain[] getSolution(int no);

	/**
	 * It returns number of solutions found while using this choice point
	 * selector.
	 * @return the number of solutions.
	 */

	public int solutionsNo();

	/**
	 * It will enforce the solution listener to instruct search to keep looking
	 * for a solution making the search explore the whole search space.
	 * @param status true if we are interested in search for all solutions, false otherwise.
	 */

	public void searchAll(boolean status);

	/**
	 * It records each solution so it can be later retrieved and used. Search will
	 * always record the last solution.
	 * @param status true if we are interested in recording all solutions, false otherwise.
	 */

	public void recordSolutions(boolean status);

	/**
	 * It allows to inform sub-search of what is the current number of the
	 * solution in master search.
	 * @param parent solution listener used by a master search.
	 */

	public void setParentSolutionListener(SolutionListener<? extends Var> parent);

	/**
	 * For a given master solution finds any solution within that listener which 
	 * matches the master solution.
	 * @param parentSolutionNo solution number of the parent for which we search matching solution.
	 * @return -1 if no solution was found, otherwise the index of the solution.
	 */
	public int findSolutionMatchingParent(int parentSolutionNo);

	
	public int getParentSolution(int childSolutionNo);
	
	/**
	 * It sets the children listeners for this solution listener.
	 * @param children an array containing children listeners.
	 */
	public void setChildrenListeners(SolutionListener<T>[] children);

	/**
	 * It sets the child listener for this solution listener. 
	 * @param child the child listener.
	 */
	public void setChildrenListeners(SolutionListener<T> child);

	/**
	 * It specifies if the solution listener is recording solutions or not.
	 * @return true if all solutions are recorded, false if only the last one is recorded.
	 */
	public boolean isRecordingSolutions();

	/**
	 * It checks if the sufficient number of solutions was found.
	 * 
	 * @return true if the limit of found solutions has been reached.
	 */
	public boolean solutionLimitReached();

	/**
	 * It sets the solution limit.
	 * @param limit the maximal number of solutions we are interested in.
	 */
	public void setSolutionLimit(int limit);

	/**
	 * It prints all the solutions.
	 */
	public void printAllSolutions();

}
