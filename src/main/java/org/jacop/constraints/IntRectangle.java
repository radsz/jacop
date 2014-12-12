/**
 *  IntRectangle.java 
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

/**
 * Defines a rectangle with integer origine and length used in the diffn
 * constraint.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

class IntRectangle {

	int dim = 0;

	int[] length;

	int[] origin;

	public IntRectangle(ArrayList<Integer> R) {
		dim = R.size() / 2;
		origin = new int[dim];
		length = new int[dim];
		for (int i = 0; i < dim; i++) {
			origin[i] = R.get(i);
			length[i] = R.get(i + dim);
		}
	}

	public IntRectangle(int size) {
		origin = new int[size];
		length = new int[size];
	}

	public IntRectangle(int[] R) {
		dim = R.length / 2;
		origin = new int[dim];
		length = new int[dim];
		for (int i = 0; i < dim; i++) {
			origin[i] = R[i];
			length[i] = R[i + dim];
		}
	}

	void add(int o, int l) {
		origin[dim] = o;
		length[dim] = l;
		dim++;
	}

	int dim() {
		return dim;
	}

	public boolean domOverlap(Rectangle R) {
		boolean overlap = true;
		int min1, max1, min2, max2;
		int i = 0;
		while (overlap && i < dim) {
			min1 = origin[i];
			max1 = origin[i] + length[i];
			IntDomain RoriginIDom = R.origin[i].dom();
			min2 = RoriginIDom.min();
			max2 = RoriginIDom.max() + R.length[i].max();
			overlap = overlap && intervalOverlap(min1, max1, min2, max2);
			i++;
		}
		return overlap;
	}

	boolean intervalOverlap(int min1, int max1, int min2, int max2) {
		return !(min1 >= max2 || max1 <= min2);
	}

	int length(int i) {
		return length[i];
	}

	int origin(int i) {
		return origin[i];
	}

	public boolean overlap(IntRectangle R) {
		boolean overlap = true;
		int min1, max1, min2, max2;
		int i = 0;
		while (overlap && i < dim) {
			min1 = origin[i];
			max1 = min1 + length[i];
			min2 = R.origin[i];
			max2 = min2 + R.length[i];
			overlap = overlap && intervalOverlap(min1, max1, min2, max2);
			i++;
		}
		return overlap;
	}

	void setDim(int i) {
		dim = i;
	}

	@Override
	public String toString() {
		String S = "[";
		for (int i = 0; i < dim; i++) {
			S = S + origin[i] + ", ";
		}
		for (int i = 0; i < dim; i++) {
			S = S + length[i];
			if (i < dim - 1)
				S = S + ", ";
		}
		S = S + "]";
		return S;
	}
}
