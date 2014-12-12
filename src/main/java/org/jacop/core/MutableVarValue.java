/**
 *  MutableVarValue.java 
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
 * Standard mutable variable's value definition
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public interface MutableVarValue {

	/**
	 * It clones the value of mutable variable. It includes the stamp, pointer
	 * to earlier value, and current value of variable.
	 * @return clone of the mutable variable value.
	 */
	public Object clone();

	/**
	 * It returns the earlier value of mutable variable.
	 * @return earlier value of mutable variable.
	 */
	public MutableVarValue previous();

	/**
	 * It replaces the earlier value of a mutable variable with value passed as
	 * parameter.
	 * @param o the previous value for this mutable variable.
	 */
	public void setPrevious(MutableVarValue o);

	/**
	 * It sets the stamp of value of mutable variable.
	 * @param stamp the new stamp of value of mutable variable
	 */
	public void setStamp(int stamp);

	/**
	 * It returns the stamp value of value of mutable variable.
	 * @return the current stamp of value of mutable variable.
	 */
	public int stamp();

	/**
	 * It returns string representation of the current value of mutable
	 * variable.
	 */
	public String toString();
}
