/**
 *  ProfileItem.java 
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


/**
 * Defines a basic structure used to update profile for cumulative constraint.
 * It consists if to time-points and a value denoting the interval [a, b) (a
 * belongs to it nad b does not) and the value.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class ProfileItem {

	/**
	 * It specifies the starting point of the profile item. 
	 */
	public int min = -1;

	/**
	 * It specifies the ending point of the profile item. 
	 */
	public int max = -1;

	/**
	 * It specifies the amount by which this profile item contributes in the profile.
	 */
	public int value = -1;

	short type = Profile.cumul;

	/**
	 * It constructs a profile item. By default it is a cumulative profile item. 
	 */
	public ProfileItem() { 
	}

	/**
	 * It constructs a profile item which spans over interval (a, b) with a given amount
	 * specified by val. 
	 * 
	 * @param a starting point of the profile item.
	 * @param b ending point of the profile item. 
	 * @param val the contribution of the item towards the profile.
	 */
	public ProfileItem(int a, int b, int val) { 
		min = a;
		max = b;
		value = val;
	}

	/**
	 * It constructs the profile item with a given type.
	 * @param type it specifies the type of the profile item.
	 */
	public ProfileItem(short type) { 
		this.type = type;
	}

	/**
	 * It constructs a profile item of a given type spanning across the given interval
	 * and contributing a given amount towards the profile. 
	 * 
	 * @param type it specifies the type of the profile item.
	 * @param a it specifies the starting point of the profile item.
	 * @param b it specifies the ending point of the profile item. 
	 * @param val it specifies how much this profile item contributes in the profile.
	 */
	public ProfileItem(short type, int a, int b, int val) { 
		this.type = type;
		min = a;
		max = b;
		value = val;
	}

	/**
	 * It returns the ending point of the profile item. 
	 * @return the ending point of the profile item. 
	 */
	public int max() {
		return max;
	}
	
	/**
	 * It returns the starting point of the profile item. 
	 * @return the starting point of the profile item. 
	 */
	public int min() {
		return min;
	}

	
	/**
	 * It compute the overlap with the specified profile item. The results are given as profile items too. 
	 * 
	 * @param a the object for which the overlap with current object is being computed. 
	 * @param left the left part of this profile item which is not being overlapped.
	 * @param overlap the overlapped part. 
	 * @param right the right part of this profile item which is not being overlapped.
	 */
	public void overlap(ProfileItem a, 
						ProfileItem left, 
						ProfileItem overlap,
						ProfileItem right) {

		if (a.min == min) {
			// left = null;
			if (a.max < max) {
				if (min != a.max) {
					int v = (type == Profile.cumul) ? v = a.value + value // cumulative
					// is sum
							: ((a.value > value) ? a.value : value); // diff2
					// is
					// max
					overlap.set(min, a.max, v);
				}
				right.set(a.max, max, value);
			} else {
				// Max <= a.Max
				int v = (type == Profile.cumul) ? v = a.value + value // cumulative is
				// sum
						: ((a.value > value) ? a.value : value); // diff2 is
				// max
				overlap.set(min, max, v);
				if (max != a.max)
					right.set(max, a.max, a.value);
			}
		} else {
			if (a.min < min) {
				left.set(a.min, min, a.value);
				if (a.max == max) {
					int v = (type == Profile.cumul) ? v = a.value + value // cumulative
					// is sum
							: ((a.value > value) ? a.value : value); // diff2
					// is
					// max
					overlap.set(min, max, v);
					// right = null;
				} else {
					if (a.max < max) {
						if (min != a.max) {
							int v = (type == Profile.cumul) ? v = a.value + value // cumulative
							// is
									// sum
									: ((a.value > value) ? a.value : value); // diff2
							// is
							// max
							overlap.set(min, a.max, v);
						}
						right.set(a.max, max, value);
					} else {
						// Max <= a.Max
						int v = (type == Profile.cumul) ? v = a.value + value // cumulative
						// is
								// sum
								: ((a.value > value) ? a.value : value); // diff2
						// is
						// max
						overlap.set(min, max, v);
						if (max != a.max)
							right.set(max, a.max, a.value);
					}
				}
			} else {
				// Min < a.Min
				left.set(min, a.min, value);
				if (a.max == max) {
					int v = (type == Profile.cumul) ? v = a.value + value // cumulative
					// is sum
							: ((a.value > value) ? a.value : value); // diff2
					// is
					// max
					overlap.set(a.min, a.max, v);
					// right = null;
				} else {
					if (a.max < max) {
						int v = (type == Profile.cumul) ? v = a.value + value // cumulative
						// is
								// sum
								: ((a.value > value) ? a.value : value); // diff2
						// is
						// max
						overlap.set(a.min, a.max, v);
						right.set(a.max, max, value);
					} else {
						// Max <= a.Max
						int v = (type == Profile.cumul) ? v = a.value + value // cumulative
						// is
								// sum
								: ((a.value > value) ? a.value : value); // diff2
						// is
						// max
						overlap.set(a.min, max, v);
						if (max != a.max)
							right.set(max, a.max, a.value);
					}
				}
			}
		}
	}

	
	/**
	 * It sets the attributes of the profile item. 
	 * 
	 * @param a the starting point of the profile item. 
	 * @param b the ending point of the profile item. 
	 * @param val the amount contributed towards a profile by this profile item. 
	 */
	public void set(int a, int b, int val) {
		min = a;
		max = b;
		value = val;
	}

	/**
	 * It sets the ending point of the profile item. 
	 * @param b
	 */
	public void setMax(int b) {
		max = b;
	}

	/**
	 * It sets the starting point of the profile item.
	 * @param a
	 */
	public void setMin(int a) {
		min = a;
	}

	/**
	 * It sets the amount by which this profile item is contributing towards the profile.
	 * @param val
	 */
	public void setValue(int val) {
		value = val;
	}

	/**
	 * It computes subtraction of a given item and returns the result. 
	 * @param a the item being subtracted from this profile item. 
	 * @param left the left part remaining after subtraction. 
	 * @param right the right part remaining after subtraction. 
	 */
	public void subtract(ProfileItem a, ProfileItem left, ProfileItem right) {

		if (min == a.min) {
			if (max > a.max)
				right.set(a.max, max, value);
		} else {
			if (min < a.min) {
				if (max <= a.min)
					left.set(min, max, value);
				else {
					if (max > a.min && max <= a.max)
						left.set(min, a.min, value);
					else if (max > a.max) {
						// a.Max < Max
						right.set(a.max, max, value);
						left.set(min, a.min, value);
					}
				}
			} else {
				// a.Min < Min
				if (min <= a.max) {
					if (max > a.max)
						right.set(a.max, max, value);
				} else
					// Min > a.Max
					right.set(min, max, value);
			}
		}
	}

	@Override
	public String toString() {
		return "[" + min + ".." + max + ") = " + value;
	}

	/**
	 * It returns the amount which is being contributed by this profile item to the profile.
	 * 
	 * @return the amount contributed by this profile item to the profile.
	 */
	public int value() {
		return value;
	}
}
