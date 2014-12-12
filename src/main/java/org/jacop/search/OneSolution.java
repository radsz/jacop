/**
 *  OneSolution.java 
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

import org.jacop.core.Var;
import org.jacop.core.Store;

/**
 * Defines functionality for OneSolution plug-in, that is the search
 * with this plug-in will stop after funding first solution. Each call
 * to this search will restore the functionality and the search will
 * again search for a single solution.
 * 
 * @author Krzysztof Kuchcinski
 * @version 4.2
 */

public class OneSolution<T extends Var>  extends SimpleSolutionListener<T> implements ConsistencyListener, InitializeListener {

    boolean solutionFound = false;

    ConsistencyListener[] childrenConsistencyListeners;
    
    InitializeListener[] childrenInitializeListeners;

    public OneSolution() {
    }

    /*
     * Initilize listener
     */
    public void executedAtInitialize(Store store) {
	solutionFound = false;
    }

    /**
     * It sets the children listeners of this initialize listener.
     * @param children
     */
    public void setChildrenListeners(InitializeListener[] children) {

	childrenInitializeListeners = children;

    }
	
    /**
     * It sets one child listener for this initialize listener.
     * @param child the child of this initialize listener.
     */
    public void setChildrenListeners(InitializeListener child) {
	
	childrenInitializeListeners = new InitializeListener[1];
	childrenInitializeListeners[0] = child;

    }

    /*
     * Solution listener
     */
    public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

	boolean returnCode = super.executeAfterSolution(search, select);

	solutionFound = true;

	return returnCode;
    }

    /*
     * Consistency listener
     */
    public boolean executeAfterConsistency(boolean consistent) {

	if (solutionFound)
	    return false;
	else 
	    return consistent;
    }

    public void setChildrenListeners(ConsistencyListener[] children) {

	childrenConsistencyListeners = children; //

    }

    public void setChildrenListeners(ConsistencyListener child) {

	childrenConsistencyListeners = new ConsistencyListener[1];
	childrenConsistencyListeners[0] = child;

    }

}
