/**
 *  LDS.java 
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
import org.jacop.core.Var;

/**
 * Defines functionality of limited discrepancy search. Plugin in this object to
 * search to change your depth first search into limited discrepancy search.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 * @param <T> type of variable being used in the search.
 */

public class LDS<T extends Var> implements ExitChildListener<T> {

	boolean timeOut = false;

	int noDiscrepancies;

	int maxNoDiscrepancies;

	boolean recentExitingLeftChildGoingForDiscrepancy = false;

	boolean recentExitingRightChild = false;

	ExitChildListener<T>[] exitChildListeners;

	/**
	 * The search will not be allowed to deviate more than maxDiscrepancies
	 * times from the heuristic (e.g. variable and value ordering) in the
	 * search.
	 * @param maxDiscrepancies maximal number of discrepancies allowed.
	 */

	public LDS(int maxDiscrepancies) {

		assert (maxDiscrepancies >= 0);

		this.maxNoDiscrepancies = maxDiscrepancies;

	}

	/**
	 * It is executed after exiting the left child. The parameters specify the
	 * variable and value used in the choice point. The parameter status
	 * specifies the return code from the child. The return parameter of this
	 * function specifies if the search should continue undisturbed or exit the
	 * current search node with value false.
	 */

	public boolean leftChild(T var, int value, boolean status) {

		if (!status) {
			// we will enter right node if we can, thus increasing the
			// discrepancy.
			noDiscrepancies++;

			if (noDiscrepancies >= maxNoDiscrepancies) {

				// maximum number of discrepancies reached, returning false
				// since we do not want to
				if (exitChildListeners != null) {
					for (int i = 0; i < exitChildListeners.length; i++)
						exitChildListeners[i].leftChild(var, value, status);
				}

				noDiscrepancies--;
				return false;

			} else {

				if (exitChildListeners != null) {
					boolean code = false;
					for (int i = 0; i < exitChildListeners.length; i++)
						code |= exitChildListeners[i].leftChild(var, value,
								status);

					// the children listeners disallow entering the right child
					// so there will be no disrepancy as counted.
					if (!code)
						noDiscrepancies--;
					return code;
				}

				return true;

			}
		}

		// the search exits with the solution, so no discrepancy is required.
		return status;

	}

	/**
	 * It is executed after exiting the left child. The parameters specify the
	 * choice point. The parameter status specifies the return code from the
	 * child. The return parameter of this function specifies if the search
	 * should continue undisturbed or exit the current search node with false.
	 * If the continuing to the right child will exceed the number of allowed 
	 * discrepancies then this function will return false so the right child 
	 * will not be explored.
	 */

	public boolean leftChild(PrimitiveConstraint choice, boolean status) {

		if (!status) {
			// we will enter right node if we can, thus increasing the
			// discrepancy.
			noDiscrepancies++;

			if (noDiscrepancies >= maxNoDiscrepancies) {

				// maximum number of discrepancies reached, returning false
				// since we do not want to
				if (exitChildListeners != null) {
					for (int i = 0; i < exitChildListeners.length; i++)
						exitChildListeners[i].leftChild(choice, status);
				}

				noDiscrepancies--;
				return false;

			} else {

				if (exitChildListeners != null) {
					boolean code = false;
					for (int i = 0; i < exitChildListeners.length; i++)
						code |= exitChildListeners[i].leftChild(choice, status);

					// the children listeners disallow entering the right child
					// so there will be no disrepancy as counted.
					if (!code)
						noDiscrepancies--;
					return code;
				}

				return true;
			}
		}

		// solution was found, no discrepancy calculation needed.
		return status;
	}

	/**
	 * Exiting the right children requires reduction of the current
	 * number of discrepancies being used.
	 */

	public void rightChild(T var, int value, boolean status) {

		noDiscrepancies--;

	}

    public void rightChild(PrimitiveConstraint choice, boolean status) {

		noDiscrepancies--;

	}

    public void setChildrenListeners(ExitChildListener<T>[] children) {

		exitChildListeners = children;
	}

	public void setChildrenListeners(ExitChildListener<T> child) {
		exitChildListeners = new ExitChildListener[1];
		exitChildListeners[0] = child;
	}

}
