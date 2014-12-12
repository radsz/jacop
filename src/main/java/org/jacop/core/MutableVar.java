/**
 *  MutableVar.java 
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

package org.jacop.core;

/**
 * Standard mutable variable definition
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public interface MutableVar {

	/**
	 * It returns the earlier value of variable comparing to the current one.
	 * @return previous value of a mutable variable.
	 */
	public MutableVarValue previous();

	/**
	 * It removes given level from mutable variable.
	 * @param removeLevel it specifies the level which is being removed.
	 */
	public void removeLevel(int removeLevel);

	/**
	 * It replace the current representation of the value with a new
	 * representation. It ignores the store level.
	 * @param o value to which a mutable variable is set.
	 */
	public void setCurrent(MutableVarValue o);

	/**
	 * It returns string representation of Mutable variable.
	 */
	public String toString();

	/**
	 * It updates the value of a mutable variable based on value given as a
	 * parameter, the stamp level of current value and stamp value of passed
	 * value.
	 * @param value it specifies the new value of a mutable variable.
	 */
	public void update(MutableVarValue value);

	/**
	 * It returns current value of MutableVariable.
	 * @return current value of the mutable variable.
	 */
	public MutableVarValue value();
}
