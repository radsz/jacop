/**
 *  Rectangle.java 
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

package org.jacop.constraints;

import java.util.ArrayList;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * Defines a rectangle used in the diffn constraint.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Rectangle {

	int dim;

	/**
	 * It specifies the length of the rectangle in each dimension.
	 */
	public IntVar[] length;

	/**
	 * It specifies the origin of the rectangle in each dimension. 
	 */
	public IntVar[] origin;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"length", "origin"};

	/**
	 * It constructs a rectangle.
	 * 
	 * @param length the length of the rectangle in each dimension. 
	 * @param origin the origin of the rectangle in each dimension.
	 */
	public Rectangle(IntVar[] length, IntVar[] origin) {
		dim = length.length;
		
		origin = new IntVar[dim];
		length = new IntVar[dim];
		for (int i = 0; i < dim; i++) {
			origin[i] = length[i];
			length[i] = origin[i];
		}
	}

	/**
	 * It constructs a rectangle.
	 * 
	 * @param list it specifies for each dimension (one after the other) its origin and length.
	 *  
	 */
	public Rectangle(IntVar[] list) {
		dim = list.length / 2;
		origin = new IntVar[dim];
		length = new IntVar[dim];
		for (int i = 0; i < dim; i++) {
			origin[i] = list[i];
			length[i] = list[i + dim];
		}
	}

	/**
	 * It constructs a rectangle.
	 * 
	 * @param list it specifies for each dimension (one after the other) its origin and length.
	 *  
	 */
	public Rectangle(ArrayList<? extends IntVar> list) {
		this(list.toArray(new IntVar[list.size()]));
	}

	/**
	 * It constructs a rectangle.
	 * @param rect the rectangle based on which a new rectangle is created.
	 * 
	 */
	public Rectangle(Rectangle rect) {
		
		this.dim = rect.dim;
		this.length = new IntVar[this.dim];
		this.origin = new IntVar[this.dim];
	
		System.arraycopy(rect.length, 0, this.length, 0, rect.length.length);
		System.arraycopy(rect.origin, 0, this.origin, 0, rect.origin.length);

	}
	
	int dim() {
		return dim;
	}

	
	/**
	 * It returns true if this rectangle overlaps with a given rectangle. 
	 * 
	 * @param r the rectangle for which the overlapping is being checked. 
	 * @return true if rectangles overlap, false otherwise.
	 */
	public boolean domOverlap(Rectangle r) {
		boolean overlap = true;
		int min1, max1, min2, max2;
		int i = 0;
		while (overlap && i < dim) {
			IntDomain originIdom = origin[i].dom();
			IntDomain ROriginIdom = r.origin[i].dom();
			min1 = originIdom.min();
			max1 = originIdom.max() + length[i].max();
			min2 = ROriginIdom.min();
			max2 = ROriginIdom.max() + r.length[i].max();
			overlap = overlap && intervalOverlap(min1, max1, min2, max2);
			i++;
		}
		return overlap;
	}

	boolean intervalOverlap(int min1, int max1, int min2, int max2) {
		return !(min1 >= max2 || max1 <= min2);
	}

	IntVar length(int i) {
		return length[i];
	}

	
	/**
	 * It computes the maximum level of any variable constituting the rectangle.
	 * 
	 * @return the maximum level. 
	 */
	public int maxLevel() {
		int level = 0;
		int i = 0;
		while (i < dim) {
			int originStamp = origin[i].level(), lengthStamp = length[i]
					.level();
			if (level < originStamp)
				level = originStamp;
			if (level < lengthStamp)
				level = lengthStamp;
			i++;
		}
		return level;
	}

	long minArea() {
		long area = 1;
		for (int i = 0; i < dim; i++)
			area *= length[i].min();
		return area;
	}

	
	/**
	 * It checks if a minimum length in any dimension of the rectangle can be equal 0.
	 * 
	 * @return true if in any dimension the rectangle has minimum possible length equal 0, false otherwise.
	 */
	public boolean minLengthEq0() {
		boolean use = false;

		int i = 0;
		while (!use && i < dim) {
			use = (length[i].min() == 0);
			i++;
		}
		return use;
	}

	
	public boolean minUse(int selDimension, IntRectangle u) {
		boolean use = true;
		int start, stop;

		int i = 0;
//		int j = 0;
		while (use && i < dim) {
			if (i != selDimension) {
				IntDomain originIdom = origin[i].dom();
				start = originIdom.max();
				stop = originIdom.min() + length[i].min();
				if (start < stop) {
					u.add(start, stop - start);
//					j++;
				} else
					use = false;
			} else {
				u.add(-1, -1);
			}
			i++;
		}
		return use;
	}

	public boolean minUse(IntRectangle u) {
		boolean use = true;
		int start, stop;

		int i = 0;
//		int j = 0;
		while (use && i < dim) {
			IntDomain originI = origin[i].dom();
			start = originI.max();
			stop = originI.min() + length[i].min();
			if (start < stop) {
				u.add(start, stop - start);
//				j++;
			} else
				use = false;
			i++;
		}
		return use;
	}

	Var origin(int i) {
		return origin[i];
	}

	
	/**
	 * It checks whether the rectangle is completely fixed. 
	 * 
	 * @return true if all variables constituting rectangle are grounded, false otherwise.
	 */
	public boolean settled() {
		boolean sat = true;
		int i = 0;
		while (sat && i < dim) {
			sat = sat && origin[i].singleton() && length[i].singleton();
			i++;
		}
		return sat;
	}

	@Override
	public String toString() {
		String S = "[";
		for (int i = 0; i < dim; i++) {
			S += origin[i] + ", ";
		}
		for (int i = 0; i < dim; i++) {
			S += length[i];
			if (i < dim - 1)
				S += ", ";
		}
		S += "]";
		return S;
	}

}
