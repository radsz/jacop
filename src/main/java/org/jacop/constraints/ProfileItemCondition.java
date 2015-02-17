/**
 *  ProfileItemCondition.java 
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

import java.util.Iterator;
import java.util.LinkedList;

/**
 * Defines a basic structure used to update profile DisjointConditional when
 * some rectangles can share the same place.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

class ProfileItemCondition extends ProfileItem {

	LinkedList<int[]> rectangles = new LinkedList<int[]>();

	ProfileItemCondition() {
	}

	ProfileItemCondition(int a, int b, int val, int[] rect) {
		super(a, b, val);
		rectangles.add(rect);
	}

	ProfileItemCondition(int a, int b, int val, LinkedList<int[]> rects) {
		super(a, b, val);
		rectangles.addAll(rects);
	}

	void addRect(int[] r) {
		rectangles.add(r);
	}

	int exclusiveRectsSize(ExclusiveList exList) {
		int rectHight = 0;
		// for (Iterator e = rectangles.listIterator(0); e.hasNext();) {
		// int[] el = (int[])e.next();
		// if (exList.onList(el[0]))
		// rectHight += el[1];
		// }

		for (int i = 0; i < exList.size(); i++) {
			ExclusiveItem exI = exList.get(i);
		 
			for (Iterator<int[]> e = rectangles.listIterator(0); e.hasNext();) {
				int[] el = e.next();
		 
				if (exI.i2 == el[0] && exI.cond.min() == 0)
					rectHight += el[1];
			}
		}
		 
		return rectHight;
	}

	void overlap(ProfileItemCondition a, ProfileItemCondition left,
			ProfileItemCondition overlap, ProfileItemCondition right,
			ExclusiveList exList, int[] r) {

		if (a.min == min) {
			// left = null;
			if (a.max < max) {
				if (min != a.max) {
					int val = exclusiveRectsSize(exList);
					int v = (val == 0) ? a.value : (a.value > val) ? a.value
							- val : 0;
					overlap.set(min, a.max, value + v, rectangles);
					int[] rR = { r[0], v };
					overlap.addRect(rR);

				}
				right.set(a.max, max, value, rectangles);
			} else {
				// Max <= a.Max
				int val = exclusiveRectsSize(exList);
				int v = (val == 0) ? a.value : (a.value > val) ? a.value - val
						: 0;
				overlap.set(min, max, value + v, rectangles);
				int[] rR = { r[0], v };
				overlap.addRect(rR);
				if (max != a.max)
					right.set(max, a.max, a.value, r);
			}
		} else {
			// a.Min != Min
			if (a.min < min) {
				left.set(a.min, min, a.value, r);
				if (a.max == max) {
					int val = exclusiveRectsSize(exList);
					int v = (val == 0) ? a.value : (a.value > val) ? a.value
							- val : 0;
					overlap.set(min, max, value + v, rectangles);
					int[] rR = { r[0], v };
					overlap.addRect(rR);
					// right = null;
				} else {
					if (a.max < max) {
						if (min != a.max) {
							int val = exclusiveRectsSize(exList);
							int v = (val == 0) ? a.value
									: (a.value > val) ? a.value - val : 0;
							overlap.set(min, a.max, value + v, rectangles);
							int[] rR = { r[0], v };
							overlap.addRect(rR);
						}
						right.set(a.max, max, value, rectangles);
					} else {
						// Max <= a.Max
						int val = exclusiveRectsSize(exList);
						int v = (val == 0) ? a.value
								: (a.value > val) ? a.value - val : 0;
						overlap.set(min, max, value + v, rectangles);
						int[] rR = { r[0], v };
						overlap.addRect(rR);
						if (max != a.max)
							right.set(max, a.max, a.value, r);
					}
				}
			} else {
				// Min < a.Min
				left.set(min, a.min, value, rectangles);
				if (a.max == max) {
					int val = exclusiveRectsSize(exList);
					int v = (val == 0) ? a.value : (a.value > val) ? a.value
							- val : 0;
					overlap.set(a.min, a.max, value + v, rectangles);
					int[] rR = { r[0], v };
					overlap.addRect(rR);
					// right = null;
				} else {
					if (a.max < max) {
						int val = exclusiveRectsSize(exList);
						int v = (val == 0) ? a.value
								: (a.value > val) ? a.value - val : 0;
						overlap.set(a.min, a.max, value + v, rectangles);
						int[] rR = { r[0], v };
						overlap.addRect(rR);
						right.set(a.max, max, value, rectangles);
					} else {
						// Max <= a.Max
						int val = exclusiveRectsSize(exList);
						int v = (val == 0) ? a.value
								: (a.value > val) ? a.value - val : 0;
						overlap.set(a.min, max, value + v, rectangles);
						int[] rR = { r[0], v };
						overlap.addRect(rR);
						if (max != a.max)
							right.set(max, a.max, a.value, r);
					}
				}
			}
		}
	}

	void set(int a, int b, int val, int[] r) {
		super.set(a, b, val);
		rectangles.add(r);
	}

	void set(int a, int b, int val, LinkedList<int[]> r) {
		super.set(a, b, val);
		rectangles.addAll(r);
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer("{[");
		result.append(min).append("..").append(max).append(") = ").append(value).append(", [");
		
		for (Iterator<int[]> e = rectangles.listIterator(0); e.hasNext();) {
			int[] el = e.next();
			result.append("[").append(el[0]).append(", ").append(el[1]).append("], ");
		}
		result.append("]");
		
		return result.toString();

	}
	
}
