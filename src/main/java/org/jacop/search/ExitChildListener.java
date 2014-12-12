/**
 *  ExitChildListener.java 
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
 * Defines a listener which is called by the search if a child node is exited.
 * It works for both the right and left child.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 * @param <T> type of variable used in the search.
 */

public interface ExitChildListener<T extends Var> {

	/**
	 * It is executed after exiting the left child. 
	 * 
	 * @param var variable used in the choice point.
	 * @param value value used in the choice point.
	 * @param status true if the solution was found in the child subtree, false otherwise.
	 * @return true if the search should continue undisturbed, false if it should 
	 * exit the current node with false
	 */

	public boolean leftChild(T var, int value, boolean status);

	/**
	 * It is executed after exiting the left child. 
	 * 
	 * @param choice primitive constraint used as the base of the choice point.
	 * @param status true if the solution was found in the child subtree, false otherwise.
	 * @return true if the search should continue undisturbed to the right node, false if it should 
	 * exit the current node with false
	 */

	public boolean leftChild(PrimitiveConstraint choice, boolean status);

	/**
	 * It is executed after exiting the right child. 
	 * 
	 * @param var variable used in the choice point.
	 * @param value value used in the choice point.
	 * @param status true if the solution was found in the child subtree, false otherwise.
	 * exit the current node with false
	 */
	public void rightChild(T var, int value, boolean status);

	/**
	 * It is executed after exiting the right child. 
	 * 
	 * @param choice primitive constraint used as the base of the choice point.
	 * @param status true if the solution was found in the child subtree, false otherwise.
	 * exit the current node with false
	 */

	public void rightChild(PrimitiveConstraint choice, boolean status);

	/**
	 * It sets the children listeners for the current listener.
	 * @param children array containing children listeners.
	 */
	public void setChildrenListeners(ExitChildListener<T>[] children);

	
	/**
	 * It adds one child listener.
	 * @param child added child listener.
	 */
	public void setChildrenListeners(ExitChildListener<T> child);

}
