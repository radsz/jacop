/**
 *  ConsistencyListener.java 
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


/**
 * Defines an interface of an object which can be plugined into the search right
 * after executing the consistency function (at the beginning of each search
 * node). Using children listeners it is possible to attach multiple number of
 * listeners working together in any fashion.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public interface ConsistencyListener {

	/**
	 * It is executed right after consistency of the current search node. 
	 * Returning true when the parameter was false is not advised as things 
	 * like invalid solutions can be found.
	 * @param consistent specifies if the consistency call returned true or false.
	 * @return true if the search should continue, false if the search should act as the consistency returned false.
	 */

	public boolean executeAfterConsistency(boolean consistent);

	/**
	 * Each of the child listeners will be called and the return code from them
	 * will be combined (taken into account) by a parent).
	 * @param children the children listeners attached to this listener.
	 */
	public void setChildrenListeners(ConsistencyListener[] children);

	/**
	 * Setting one child listener.
	 * @param child the only child listener added to this consistency listener.
	 */

	public void setChildrenListeners(ConsistencyListener child);

}
