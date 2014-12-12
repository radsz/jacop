/**
 *  Profile.java 
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
import java.util.Iterator;

/**
 * Defines a basic data structure to keep the profile for the diffn/1 and
 * cumulative/4 constraints. It consists of ordered pair of time points and the
 * current value.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Profile extends ArrayList<ProfileItem> {

	private static final long serialVersionUID = 8683452581100000012L;

	static final boolean trace = false;

	static final int cumul = 0;
	static final int diffn = 1;
	
	protected int maxProfileItemHeight = 0;

	short type = cumul;

	/**
	 * It constructs the prophet file. 
	 */
	public Profile() {
	}

	/**
	 * It constructs the profile of a given type (e.g. for cumulative). 
	 * @param type
	 */
	public Profile(short type) {
		this.type = type;
	}

	/**
	 * It adds given amount (val) to the profile between a and b.
	 * 
	 * @param a the minimum range at which it is being added.
	 * @param b the maximum range at which it is being added.
	 * @param val the amount by which the profiles is updated.
	 */
	public void addToProfile(int a, int b, int val) {
		ProfileItem p;
		int i = 0;
		boolean notFound = true;

		if (size() == 0) {
			if (trace)
				System.out.println("1. Add " + "[" + a + ".." + b + ")" + "="
						+ val + " at position 0");
			add(new ProfileItem(type, a, b, val));
			if (maxProfileItemHeight < val)
				maxProfileItemHeight = val;
		} else {
			while (i < size() && notFound) {
				p = get(i);
				if (b <= p.min) {
					if (a != b) {
						if (b == p.min && val == p.value) {
							if (trace)
								System.out.println("2a. Change " + "[" + a
										+ ".." + p.max + ")" + "=" + val
										+ " at position " + i);
							p.min = a;
							if (i > 0) {
								ProfileItem previousP = get(i - 1);
								if (a == previousP.max
										&& previousP.value == val) {
									p.min = previousP.min;
									remove(i - 1);
									notFound = false;
									i--;
								}
							}
						} else {
							if (i > 0) {
								p = get(i - 1);
								if (a == p.max && val == p.value)
									p.max = b;
								else
									add(i, new ProfileItem(type, a, b, val));
							} else {
								if (trace)
									System.out.println("2b. Add " + "[" + a
											+ ".." + b + ")" + "=" + val
											+ " at position " + i);
								add(i, new ProfileItem(type, a, b, val));
							}
						}
					}
					notFound = false;
					i++;
					if (maxProfileItemHeight < val)
						maxProfileItemHeight = val;
				} else {
					if (p.max <= a) {
						if (i == size() - 1) {
							if (a != b) {
								if (p.max == a && val == p.value) {
									if (trace)
										System.out.println("3a. Change " + "["
												+ p.min + ".." + b + ")" + "="
												+ val + " at position " + i);
									p.max = b;
									if (maxProfileItemHeight < val)
										maxProfileItemHeight = val;
								} else {
									if (trace)
										System.out.println("3b. Add " + "[" + a
												+ ".." + b + ")" + "=" + val
												+ " at position "
												+ (i + 1));
									add(i + 1, new ProfileItem(type, a, b, val));
									if (maxProfileItemHeight < val)
										maxProfileItemHeight = val;
								}
							}
							i++;
							notFound = false;
						} else
							i++;
					} else {
						ProfileItem new1 = new ProfileItem(type), new2 = new ProfileItem(
								type), new3 = new ProfileItem(type);
						p.overlap(new ProfileItem(type, a, b, val), new1, new2,
								new3);

						if (trace)
							System.out.println("Overlap of " + "[" + a + ".."
									+ b + ")" + "=" + val + " and " + p
									+ "\nResult = " + new1 + ", " + new2 + ", "
									+ new3);

						remove(i);

						if (new1.min != -1) {
							ProfileItem previous;
							if (i != 0)
								previous = get(i - 1);
							else
								previous = new ProfileItem(type);
							if (previous.max == new1.min
									&& previous.value == new1.value) {
								if (trace)
									System.out.println("4a. Change " + "["
											+ previous.min + ".." + new1.max
											+ ")" + "=" + val + " at position "
											+ i);
								previous.setMax(new1.max);
							} else {
								if (trace)
									System.out.println("4b. Adding " + new1);
								add(i, new1);
								if (maxProfileItemHeight < new1.value)
									maxProfileItemHeight = new1.value;
								i++;
							}
						}

						if (new2.min != -1) {
							ProfileItem previous;
							if (i != 0)
								previous = get(i - 1);
							else
								previous = new ProfileItem(type);
							if (previous.max == new2.min
									&& previous.value == new2.value) {
								if (trace)
									System.out.println("5a. Change " + "["
											+ previous.min + ".." + new2.max
											+ ")" + "=" + val + " at position "
											+ i);
								previous.setMax(new2.max);
							} else {
								if (trace)
									System.out.println("5b. Adding " + new2);
								add(i, new2);
								if (maxProfileItemHeight < new2.value)
									maxProfileItemHeight = new2.value;
								i++;
							}
						}
						if (new3.min != -1 && new3.min != new3.max) {
							addToProfile(new3.min, new3.max, new3.value);
						}
						notFound = false;
					}
				}
			}
		}
	}

	
	/**
	 * It returns the max height of the profile item encountered in the profile. 
	 * @return the max height. 
	 */
	public int max() {
		return maxProfileItemHeight;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer("[");

		for (Iterator<ProfileItem> e = iterator(); e.hasNext();) {
			result.append(e.next().toString());
			if (e.hasNext())
				result.append(", ");
		}
		result.append("]");
		return result.toString();
	}
	
}
