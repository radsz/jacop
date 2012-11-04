/**
 *  LexicographicalOrder.java 
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
package org.jacop.constraints.geost;

/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 *
 * It defines the necessary functionalities needed to define a lexicographical ordering
 * of k-dimensional points.
 *
 */
public interface LexicographicalOrder {

	/**
	 * It compares two k-dimensional points.
	 * 
	 * @param p1
	 * @param p2
	 * @return comparison result: a negative value if p1 is smaller than p2,
	 * 0 if p1 is equal to p2, and a positive value if p1 is larger than p2.
	 */
	public int compare(int[] p1, int[] p2);
	
	/**
	 * It provides the precedence level of the given dimension. 0 is the most significant.
	 * 
	 * @param dimension
	 * @return integer value of the precedence level.
	 */
	public int precedenceOf(int dimension);
	
	/**
	 * It provides the dimension corresponding to the given precedence level
	 * 
	 * @param precedenceLevel
	 * @return an integer value of the dimension.
	 */
	public int dimensionAt(int precedenceLevel);

	/**
	 * It shifts the lexicographical order so that the most significant dimension
	 * is set to d.
	 * 
	 * @param d the dimension to be considered most significant
	 */
	public void setMostSignificantDimension(int d);

	/**
	 * This is equivalent to the call precedenceOf(0).
	 * 
	 * @return the most significant dimension
	 */
	public int getMostSignificantDimension();
	
	
	/**
	 * It returns the ordering of dimensions used when no shift is applied
	 * (i.e. when the most significant dimension is not changed)
	 * 
	 * @return the ordering of dimensions without a shift.
	 */
	public int[] masterOrdering();
	
}
