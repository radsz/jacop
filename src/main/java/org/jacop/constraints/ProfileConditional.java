/**
 *  ProfileConditional.java 
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
 * Defines a basic data structure to keep the profile for the
 * disjointConditonal/2
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

class ProfileConditional extends ArrayList<ProfileItemCondition> {

	private static final long serialVersionUID = 8683452581100000010L;

	static final boolean trace = false;

	int MaxProfile = 0;

	ProfileConditional() {
	}

	void addToProfile(int index, int a, int b, int val, ExclusiveList exList) {
		ProfileItemCondition p;
		int i = 0;
		boolean notFound = true;

		if (trace) {
			System.out.println(index + "  --------------------------");
			System.out.println(exList);
		}

		if (size() == 0) {
			if (trace)
				System.out.println("1. Add " + "[" + a + ".." + b + ")" + "="
						+ val + " at position 0");
			int[] r = { index, val };
			add(new ProfileItemCondition(a, b, val, r));
			if (MaxProfile < val)
				MaxProfile = val;
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
							// !!!! b==p.Min
							// p.Min = a;
							int[] r = { index, val };
							add(i + 1, new ProfileItemCondition(a, b, val, r));
						} else {
							// b < p.Min
							if (i > 0) {
								p = get(i - 1);
								if (a == p.max && val == p.value) {
									// !!! a == p.Max
									// p.Max = b;
									int[] r = { index, val };
									add(i, new ProfileItemCondition(a, b, val,
											r));
								} else {
									int[] r = { index, val }; // OK
									add(i, new ProfileItemCondition(a, b, val,
											r));
								}
							} else {
								if (trace)
									System.out.println("2b. Add " + "[" + a
											+ ".." + b + ")" + "=" + val
											+ " at position " + i);
								int[] r = { index, val }; // OK
								add(i, new ProfileItemCondition(a, b, val, r));
							}
						}
					}
					notFound = false;
					i++;
					if (MaxProfile < val)
						MaxProfile = val;
				} else {
					// b > p.Min
					if (p.max <= a) {
						if (i == size() - 1) {
							if (a != b) {
								if (p.max == a && val == p.value) {
									if (trace)
										System.out.println("3a. Change " + "["
												+ p.min + ".." + b + ")" + "="
												+ val + " at position " + i);
									// !!! b > p.Min && p.Max == a
									// p.Max = b;
									int[] r = { index, val }; // OK
									add(i + 1, new ProfileItemCondition(a, b,
											val, r));
								} else {
									// b > p.Max && p.Max < a
									if (trace)
										System.out.println("3b. Add " + "[" + a
												+ ".." + b + ")" + "=" + val
												+ " at position "
												+ (i + 1));
									int[] r = { index, val }; // OK
									add(i + 1, new ProfileItemCondition(a, b,
											val, r));
								}
							}
							i++;
							notFound = false;
						} else
							i++;
					} else {
						// b > p.Min && a < p.Max; [a,b) overlaps p
						ProfileItemCondition new1 = new ProfileItemCondition(), new2 = new ProfileItemCondition(), new3 = new ProfileItemCondition();
						int[] r = { index, val };

						if (trace)
							System.out.println("Overlap of " + "[" + a + ".."
									+ b + ")" + "=" + val + ", [" + index
									+ "] " + " and " + p);

						p.overlap(new ProfileItemCondition(a, b, val, r), new1,
								new2, new3, exList, r);
						if (trace)
							System.out.println("Result = " + new1 + ", " + new2
									+ ", " + new3);

						remove(i);
						// left
						if (new1.min != -1) {
							ProfileItemCondition previous;
							if (i != 0)
								previous = get(i - 1);
							else
								previous = new ProfileItemCondition();
							if (previous.max == new1.min
									&& previous.value == new1.value) {
								if (trace)
									System.out.println("4a. Change " + "["
											+ previous.min + ".." + new1.max
											+ ")" + "=" + val + " at position "
											+ i);
								// !!!
								// previous.setMax(new1.Max);
								if (new1.min == a) {
									add(i, new1);
									i++;
								} else {
									add(i, new1);
									i++;
								}
							} else {
								if (trace)
									System.out.println("4b. Adding " + new1);
								// !!!
								new1.rectangles = p.rectangles;
								add(i, new1);
								if (MaxProfile < new1.value)
									MaxProfile = new1.value;
								i++;
							}
						}
						// middle
						if (new2.min != -1) {
							ProfileItemCondition previous;
							if (i != 0)
								previous = get(i - 1);
							else
								previous = new ProfileItemCondition();
							if (previous.max == new2.min
									&& previous.value == new2.value) {
								if (trace)
									System.out.println("5a. Change " + "["
											+ new2.min + ".." + new2.max + ")"
											+ "=" + val + " at position " + i);
								// !!!
								// previous.setMax(new2.Max);
								if (new2.min == a) {
									add(i, new2);
									i++;
								} else {
									add(i, new2);
									i++;
								}
							} else {
								if (trace)
									System.out.println("5b. Adding " + new2);
								// !!!
								add(i, new2);
								if (MaxProfile < new2.value)
									MaxProfile = new2.value;
								i++;
							}
						}
						// right
						if (new3.min != -1 && new3.min != new3.max) {
							if (new3.max == b) {
								// rest of [a,b)
								// System.out.println("***"+this);
								// System.out.println("adding "+index+", ["+a+",
								// "+b+")="+val);
								addToProfile(index, new3.min, new3.max, val,
										exList);
								i++;
							} else {
								// rest of the old profile
								add(i, new3);
								i++;
							}
						}
						notFound = false;
					}
				}
			}
		}
		if (trace)
			System.out.println("########\n" + this);
	}

	int max() {
		return MaxProfile;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer("[");

		for (Iterator<ProfileItemCondition> e = iterator(); e.hasNext();) {
			
			result.append(e.next());
			if (e.hasNext())
				result.append(", ");

		}
		
		result.append("]");
		
		return result.toString();
	}
	
}
