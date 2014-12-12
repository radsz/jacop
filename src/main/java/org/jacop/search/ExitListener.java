/**
 *  ExitListener.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *  Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

import org.jacop.core.Store;

/**
 * This listener is executed when search has finished executing is about to exit
 * the labeling procedure.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public interface ExitListener {

	/**
	 * It is executed right after time out is determined.
	 * @param store store in the context of which the search took place.
	 * @param solutionsNo the number of solutions found.
	 */

	public void executedAtExit(Store store, int solutionsNo);

	/**
	 * It sets the children of this exit listener.
	 * @param children an array containing the children.
	 */
	public void setChildrenListeners(ExitListener[] children);

	/**
	 * It sets one child listener.
	 * @param child the only child listener used by this listener.
	 */
	public void setChildrenListeners(ExitListener child);

}
