/**
 *  Diff.java 
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
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.TreeSet;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Diff constraint assures that any two rectangles from a vector of rectangles
 * does not overlap in at least one direction. It is a simple implementation which
 * does not use sophisticated techniques for efficient backtracking.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 3.1
 */

public class Diff extends Constraint {

	static int IdNumber = 1;

	static final boolean trace = false, traceNarr = false;

	Store currentStore = null;
	

	int minPosition = 0;
	int stamp = 0;

    // use to collect information on possible length of rectangles for pruning
    ArrayList<Integer> durMax;
    //boolean durMaxDecided = false;

	HashSet<IntVar> variableQueue = new HashSet<IntVar>();

	/**
	 * It specifies the list of rectangles which are of interest for this diff constraint. 
	 */
	public Rectangle rectangles[];

	/**
	 * It specifies if the constraint should compute and use the profile.
	 */
	public boolean doProfile = true;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"rectangles", "doProfile"};

	/**
	 * It specifies a diff constraint. 
	 * @param rectangles list of rectangles which can not overlap in at least one dimension.
	 * @param doProfile should the constraint compute and use the profile functionality.
	 */
	public Diff(Rectangle[] rectangles, boolean doProfile) {

		assert (rectangles != null) : "Rectangles list is null";

		this.queueIndex = 2;
		this.numberId = IdNumber++;

		this.rectangles = new Rectangle[rectangles.length];
		this.doProfile = doProfile;
		
		for (int i = 0; i < rectangles.length; i++) {
			assert (rectangles[i] != null) : i + "-th rectangle in the list is null";
			assert (rectangles[i].dim != 2) : "The rectangle has to have exactly two dimensions";
			this.rectangles[i] = new Rectangle( rectangles[i] );
		}
		
	}

	/**
	 * It specifies a diff constraint. 
	 * @param rectangles list of rectangles which can not overlap in at least one dimension.
	 */
	public Diff(IntVar[][] rectangles) {

		assert (rectangles != null) : "Rectangles list is null";

		queueIndex = 2;
		IntVar[] R;
		
		numberId = IdNumber++;
		int size = rectangles[0].length;
		this.rectangles = new Rectangle[rectangles.length];

		for (int i = 0; i < rectangles.length; i++) {
			assert (rectangles[i] != null) : i + "-th list within rectangles list is null";
			R = rectangles[i];
			if (R.length == size) {
				Rectangle rect = new Rectangle(R);
				this.rectangles[i] = rect;
				numberArgs = (short) (numberArgs + size);
			} else {
				String s = "\nNot equal sizes of rectangle vectors in Diff";
				throw new IllegalArgumentException(s);
			}
		}
		if (size / 2 != 2) {
			String s = "\nRectangles of size > 2 not currently supported by Diff";
			throw new IllegalArgumentException(s);

		}
	}

	
	/**
	 * It constructs a diff constraint.
	 * @param o1 list of variables denoting origin of the rectangle in the first dimension.
	 * @param o2 list of variables denoting origin of the rectangle in the second dimension.
	 * @param l1 list of variables denoting length of the rectangle in the first dimension.
	 * @param l2 list of variables denoting length of the rectangle in the second dimension.
	 * @param profile it specifies if the profile should be computed and used.
	 */
	public Diff(IntVar[] o1, 
				IntVar[] o2,
				IntVar[] l1, 
				IntVar[] l2,
				boolean profile) {
		this(o1, o2, l1, l2);
		doProfile = profile;
	}

	/**
	 * It constructs a diff constraint.
	 * @param origin1 list of variables denoting origin of the rectangle in the first dimension.
	 * @param origin2 list of variables denoting origin of the rectangle in the second dimension.
	 * @param length1 list of variables denoting length of the rectangle in the first dimension.
	 * @param length2 list of variables denoting length of the rectangle in the second dimension.
	 */

	public Diff(IntVar[] origin1, 
				IntVar[] origin2,
				IntVar[] length1, 
				IntVar[] length2) {

		assert (origin1 != null) : "o1 list is null";
		assert (origin2 != null) : "o2 list is null";
		assert (length1 != null) : "l1 list is null";
		assert (length2 != null) : "l2 list is null";

		this.queueIndex = 2;
		
		this.numberId = IdNumber++;

		int size = origin1.length;
		if (size == origin1.length && size == origin2.length && size == length1.length
				&& size == length2.length) {
			
			this.rectangles = new Rectangle[size];
			
			for (int i = 0; i < size; i++) {
				IntVar[] R = { origin1[i], origin2[i], length1[i], length2[i] };
				Rectangle rect = new Rectangle(R);
				this.rectangles[i] = rect;
				this.numberArgs = (short) (numberArgs + 4);
			}
			
		} else {
			String s = "\nNot equal sizes of Variable vectors in Diff";
			throw new IllegalArgumentException(s);
		}
	}
	
	/**
	 * It specifies a diffn constraint. 
	 * @param rectangles list of rectangles which can not overlap in at least one dimension.
	 */
	public Diff(ArrayList<? extends ArrayList<? extends IntVar>> rectangles) {

		queueIndex = 2;
		numberId = IdNumber++;
		
		int size = (rectangles.get(0)).size();
		this.rectangles = new Rectangle[rectangles.size()];

		int i = 0;

		for (ArrayList<? extends IntVar> R : rectangles)
			if (R.size() == size) {
				Rectangle rect = new Rectangle(R);
				this.rectangles[i] = rect;
				i++;
				numberArgs = (short) (numberArgs + size);
			} else {
				String s = "\nNot equal sizes of rectangle vectors in Diff";
				throw new IllegalArgumentException(s);
			}
		// }
		if (size / 2 != 2) {
			String s = "\nRectangles of size > 2 not currently supported by Diff";
			throw new IllegalArgumentException(s);
		}
	}

	/**
	 * It specifies a diff constraint. 
	 * @param profile specifies is the profiles are used.
	 * @param rectangles list of rectangles which can not overlap in at least one dimension.
	 */
	public Diff(ArrayList<? extends ArrayList<? extends IntVar>> rectangles,
				boolean profile) {
		
		this(rectangles);
		doProfile = profile;
	
	}

	
	/**
	 * It constructs a diff constraint.
	 * @param o1 list of variables denoting origin of the rectangle in the first dimension.
	 * @param o2 list of variables denoting origin of the rectangle in the second dimension.
	 * @param l1 list of variables denoting length of the rectangle in the first dimension.
	 * @param l2 list of variables denoting length of the rectangle in the second dimension.
	 */
	public Diff(ArrayList<? extends IntVar> o1,
				ArrayList<? extends IntVar> o2,
				ArrayList<? extends IntVar> l1,
				ArrayList<? extends IntVar> l2) {

		this(o1.toArray(new IntVar[o1.size()]), 
			 o2.toArray(new IntVar[o2.size()]), 
			 l1.toArray(new IntVar[l1.size()]), 
			 l2.toArray(new IntVar[l2.size()]));
		
	}

	/**
	 * It constructs a diff constraint.
	 * @param o1 list of variables denoting origin of the rectangle in the first dimension.
	 * @param o2 list of variables denoting origin of the rectangle in the second dimension.
	 * @param l1 list of variables denoting length of the rectangle in the first dimension.
	 * @param l2 list of variables denoting length of the rectangle in the second dimension.
	 * @param profile it specifies if the profile should be computed and used.
	 */
	public Diff(ArrayList<? extends IntVar> o1,
				ArrayList<? extends IntVar> o2, 
				ArrayList<? extends IntVar> l1,
				ArrayList<? extends IntVar> l2,
				boolean profile) {
		this(o1, o2, l1, l2);
		doProfile = profile;
	}

	/**
	 * It specifies a diff constraint. 
	 * @param profile specifies is the profiles are used.
	 * @param rectangles list of rectangles which can not overlap in at least one dimension.
	 */
	public Diff(IntVar[][] rectangles, boolean profile) {
		this(rectangles);
		doProfile = profile;
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>();

		for (Rectangle r : rectangles) {
			for (int i = 0; i < r.dim; i++)
				variables.add(r.origin[i]);
			for (int i = 0; i < r.dim(); i++)
				variables.add(r.length[i]);
		}
		return variables;
	}

	@Override
	public void removeLevel(int level) {
		variableQueue.clear();
	}

	@Override
	public void consistency(Store store) {

		currentStore = store;

		do {

			store.propagationHasOccurred = false;
			
			HashSet<IntVar> fdvs = variableQueue;
			variableQueue = new HashSet<IntVar>();
			// System.out.println(fdvs);
			narrowRectangles(fdvs);
			
		} while (store.propagationHasOccurred);
		
	}

	boolean containsChangedVariable(Rectangle r, HashSet<IntVar> fdvQueue) {
		boolean contains = false;
		int dim = r.dim;
		int i = 0;
		while (!contains && i < dim) {
			contains = contains || fdvQueue.contains(r.origin[i])
					|| fdvQueue.contains(r.length[i]);
			i++;
		}
		return contains;
	}
	
	boolean findRectangles(Rectangle r, ArrayList<IntRectangle> UsedRect,
			ArrayList<Rectangle> ProfileCandidates, HashSet<IntVar> fdvQueue) {

		boolean contains = false, checkArea = false;

		long area = 0;
		long commonArea = 0;
		int totalNumberOfRectangles = 0;
		int dim = r.dim;
		int startMin[] = new int[dim];
		int stopMax[] = new int[dim];
		int minLength[] = new int[dim];
		int r_min[] = new int[dim], r_max[] = new int[dim];
		for (int i = 0; i < startMin.length; i++) {
			startMin[i] = IntDomain.MaxInt;
			stopMax[i] = 0;
			minLength[i] = r.length[i].min();

			IntDomain rOriginDom = r.origin[i].dom();
			r_min[i] = rOriginDom.min();
			r_max[i] = rOriginDom.max() + r.length[i].max();
		}

		int sOriginMin[] = new int[dim], sOriginMax[] = new int[dim], sLengthMin[] = new int[dim];

		for (Rectangle s : rectangles) {

			boolean overlap = true;

			if (r != s) {
				boolean sChanged = containsChangedVariable(s, fdvQueue);

				IntRectangle Use = new IntRectangle(dim);
				long sArea = 1;
				long partialCommonArea = 1;

				boolean use = true, minLength0 = false;
				int s_min, s_max, start, stop;
				int m = 0, j = 0;

				while (overlap && m < dim) {
					// check if domains of r and s overlap
					IntDomain sOriginIdom = s.origin[m].dom();
					IntDomain sLengthIdom = s.length[m].dom();
					int sLengthIMin = sLengthIdom.min();
					int sOriginIMax = sOriginIdom.max();
					s_min = sOriginIdom.min();
					s_max = sOriginIMax + sLengthIdom.max();

					overlap = overlap
					&& intervalOverlap(r_min[m], r_max[m], s_min, s_max);

					// min start, max stop and min length
					sOriginMin[m] = s_min;
					sOriginMax[m] = sOriginIMax + sLengthIMin;
					sLengthMin[m] = sLengthIMin;

					// check if s occupies some space
					start = sOriginIMax;
					stop = s_min + sLengthIMin;
					if (start < stop) {
						Use.add(start, stop - start);
						j++;
					} else
						use = false;

					// min length == 0
					minLength0 = minLength0 || (sLengthMin[m] <= 0);

					m++;
				}

				if (overlap) {
					if (use) { // rectangles taking space
						UsedRect.add(Use);
						contains = contains || sChanged;
					}

					if (!minLength0) { // profile candiates
						if (j > 0) {
							ProfileCandidates.add(s);
							contains = contains || sChanged;
						}

						checkArea = true;
						totalNumberOfRectangles++;
						for (int i = 0; i < dim; i++) {
							if (sOriginMin[i] < startMin[i])
								startMin[i] = sOriginMin[i];
							if (sOriginMax[i] > stopMax[i])
								stopMax[i] = sOriginMax[i];
							if (minLength[i] > sLengthMin[i])
								minLength[i] = sLengthMin[i];

							sArea *= sLengthMin[i];
						}
						area += sArea;
					} // profile candidate end

					// calculate area within rectangle r possible placement
					for (int i = 0; i < dim; i++) {
						if (sOriginMin[i] <= r_min[i]) {
							if (sOriginMax[i] <= r_max[i]) {
								int distance1 = sOriginMin[i] + sLengthMin[i] - r_min[i];
								sLengthMin[i] = (distance1 > 0 ) ? distance1 : 0;
							}
							else {
								// sOriginMax[i] > r_max[i])
								int rmax = r.origin[i].max() + r.length[i].min();

								int distance1 = sOriginMin[i] + sLengthMin[i] - r_min[i];
								int distance2 = sLengthMin[i] - (sOriginMax[i] - rmax);
								if (distance1 > rmax - r_min[i]) distance1 = rmax - r_min[i];
								if (distance2 > rmax - r_min[i]) distance2 = rmax - r_min[i];
								if (distance1 < distance2)
									sLengthMin[i] = (distance1 > 0) ? distance1 : 0;
								else
									if (distance2 > 0) {
										if (distance2 < sLengthMin[i])
											sLengthMin[i] = distance2;
									}
									else
										sLengthMin[i] = 0;
							}
						}
						else // sOriginMin[i] > r_min[i]
							if (sOriginMax[i] > r_max[i]) {
								int distance2 = sLengthMin[i] - (sOriginMax[i] - (r.origin[i].max() + r.length[i].min()));
								if (distance2 > 0) {
									if (distance2 < sLengthMin[i])
										sLengthMin[i] = distance2;
								}
								else
									sLengthMin[i] = 0;
							}

						partialCommonArea = partialCommonArea * sLengthMin[i];
					}
					// end for
					commonArea += partialCommonArea;
				}
				if (commonArea + r.minArea() > (r_max[0]-r_min[0])*(r_max[1]-r_min[1])) 
					throw Store.failException;

			}
		}

		if (checkArea) { // check whether there is
			// enough room for all rectangles
			area += r.minArea();
			long availArea = 1;
			long rectNumber = 1;
			for (int i = 0; i < startMin.length; i++) {
				IntDomain rOriginIdom = r.origin[i].dom();
				IntDomain rLengthIdom = r.length[i].dom();
				int rOriginIMin = rOriginIdom.min(), rOriginIMax = rOriginIdom
				.max(), rLengthIMin = rLengthIdom.min();
				if (rOriginIMin < startMin[i])
					startMin[i] = rOriginIMin;
				if (rOriginIMax + rLengthIMin > stopMax[i])
					stopMax[i] = rOriginIMax + rLengthIMin;
			}
			boolean checkRectNumber = true;
			for (int i = 0; i < startMin.length; i++) {
				availArea *= (stopMax[i] - startMin[i]);
				if (minLength[i] != 0)
				    rectNumber *= ((stopMax[i] - startMin[i]) / minLength[i]);
				else 
				    checkRectNumber = false;
			}

			if (availArea < area)
				throw Store.failException;
			else
			    // check whether there is enough room for
			    // all minimal rectangles
			    if (checkRectNumber && rectNumber < (totalNumberOfRectangles + 1))
				throw Store.failException;

		}

		return contains;
	}	
		
	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
			if (consistencyPruningEvents != null) {
				Integer possibleEvent = consistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return IntDomain.ANY;
	}

	Rectangle[] getRectangles() {
		return rectangles;
	}

	@Override
	public String id() {
		if (id != null)
			return id;
		else
			return  this.getClass().getSimpleName() + numberId;
	}

	// registers the constraint in the constraint store
	@Override
	public void impose(Store store) {
		Var v;
		int level = store.level;

		// When should it deregister? If there is any
		// time for it, then it should be implemented
		store.registerRemoveLevelListener(this);

		for (Rectangle r : rectangles) {
			for (int i = 0; i < r.dim(); i++) {
				v = r.origin[i];
				v.putModelConstraint(this, getConsistencyPruningEvent(v));
				queueVariable(level, v);

				v = r.length[i];
				v.putModelConstraint(this, getConsistencyPruningEvent(v));
				queueVariable(level, v);
			}
		}
		store.addChanged(this);
		store.countConstraint();
	}

	boolean intervalOverlap(int min1, int max1, int min2, int max2) {
		return !(min1 >= max2 || max1 <= min2);
	}

	Pair minForbiddenInterval(int start, int i, Rectangle r,
			ArrayList<IntRectangle> ConsideredRect) {

		if (notFit(i, r, ConsideredRect, start)) {
			// System.out.println("New start = " + start + ".." + (int)(start +
			// minPosition));
			return new Pair(start, start + minPosition);
		} else
			return new Pair(-1, -1);
	}

	void narrowIth(int i, Rectangle r, ArrayList<IntRectangle> UsedRect,
			ArrayList<Rectangle> ProfileCandidates) {
		int s;
		int j = (i == 0) ? 1 : 0;
		int rLengthIMin = r.length[i].min();
		int barierSize = 0;

		durMax = new ArrayList<Integer>();
		durMax.add(IntDomain.MaxInt);

		if (ProfileCandidates.size() != 0 && doProfile)
			profileNarrowing(i, r, ProfileCandidates);

		durMax = new ArrayList<Integer>();
		durMax.add(IntDomain.MaxInt);

		if (UsedRect.size() != 0) {

			IntRectangle[] UsedRectArray = new IntRectangle[UsedRect.size()];

			UsedRectArray = UsedRect.toArray(UsedRectArray);

			TreeSet<IntRectangle> starts = new TreeSet<IntRectangle>(
					new DimIMinComparator<IntRectangle>(i));
			for (IntRectangle m : UsedRectArray)
				starts.add(m);

			int sizeOfstartsOfR = (r.origin[0].domain.noIntervals() > r.origin[1].domain
					.noIntervals()) ? r.origin[0].domain.noIntervals()
					: r.origin[1].domain.noIntervals();

			IntRectangle[] startsOfR = new IntRectangle[sizeOfstartsOfR];

			for (int k = 0; k < sizeOfstartsOfR; k++)
				startsOfR[k] = new IntRectangle(r.dim);

			for (int k = 0; k < r.dim; k++) {
				IntDomain rOrigin = r.origin[k].dom();
				int rOriginSize = rOrigin.noIntervals();
				for (int n = 0; n < sizeOfstartsOfR; n++) {
					if (n < rOriginSize)
						startsOfR[n].add(rOrigin.leftElement(n), 0);
					else
						startsOfR[n].add(rOrigin.min(), 0);
				}
			}
			for (IntRectangle rect : startsOfR) {
				// System.out.print(rect+" ");
				starts.add(rect);
			}
			// System.out.println();

			ArrayList<IntRectangle> ConsideredRect = new ArrayList<IntRectangle>();
			for (IntRectangle ir : starts) {
				s = ir.origin[i];
				// System.out.println("*** start = " + s);

				ConsideredRect.clear();

				for (IntRectangle t : UsedRectArray) {
					int tCompletion = t.origin[i] + t.length[i];

					if (t.origin[i] <= s && s - rLengthIMin < tCompletion) {
						ConsideredRect.add(t);
						// rectSize += t.length[j];
					}
				}

				if (ConsideredRect.size() != 0
				// && rSize < (rectSize + (rLengthJMin - 1) *
				// ConsideredRect.size())
				) {

					IntDomain rIdom = r.origin[i].dom();
					if (s >= rIdom.min() && s <= rIdom.max()) {
						// System.out.println("Checking rectangles in dimension
						// "+i+
						// " starting at time interval "+ s + ".."
						// +(int)(s+r.length(i).min()-1)+
						// "\nCosideredRect =" + ConsideredRect);

						Pair exclude = minForbiddenInterval(s, i, r,
								ConsideredRect);

						if (exclude.Max != -1) {
							IntervalDomain Update = new IntervalDomain(IntDomain.MinInt,
									exclude.Min - r.length[i].min());
							Update.unionAdapt(exclude.Max, IntDomain.MaxInt);

							if (traceNarr) 
								System.out.print("7. Obligatory rectangles Narrow "
												+ r.origin[i] + " in " + Update);

							r.origin[i].domain.in(currentStore.level, r.origin[i], Update);

							if (traceNarr)
								System.out.println(" -->" + r.origin[i]);

							computeNewMaxDuration(r.origin[i], r.length[i].min(), exclude.Min, exclude.Max);

							//System.out.println ("7. length = "+   durMax);
						}
					}
				}
			}

			// Update rectangles length in direction i
			// sort rectangles on increasing origin i
			if (trace)
			    System.out.println ("10. length = " + durMax);

			int lengthLimit = 0;
			for (int l : durMax)
			    if (lengthLimit < l) lengthLimit = l;

			if (traceNarr)
			    System.out.println("10. Duration " + r.length[i] + " <-- 0.." + lengthLimit);

			r.length[i].domain.in(currentStore.level, r.length[i], 0, lengthLimit);

		}
	}


    void computeNewMaxDuration(IntVar start, int durMin, int excludeMin, int excludeMax) {

	// System.out.println ("+++ "+start + " exclude ["+ excludeMin + "," +excludeMax+ "]");

	int dMax = IntDomain.MaxInt;
	
	for (IntervalEnumeration ie = start.dom().intervalEnumeration(); ie.hasMoreElements();) {
	    Interval i = ie.nextElement();

	    if (excludeMax >= i.min() && excludeMin <= i.max()) {
		dMax = excludeMin - i.min();
		break;
	    }
	}
	if (dMax < durMax.get(durMax.size() - 1))
	    durMax.set(durMax.size() - 1, dMax);

	if (start.dom().contains(excludeMax)) {
	    durMax.add(IntDomain.MaxInt);
	}

	if (trace)
	    System.out.println ("+++ "+durMax);

    }


	void narrowRectangle(Rectangle r, ArrayList<IntRectangle> UsedRect,
			ArrayList<Rectangle> ProfileCandidates) {

		if (trace) {
			System.out.println("Narrowing " + r);
			System.out.println(UsedRect);
		}

		for (int i = 0; i < r.dim; i++) {
			// narrow in i-th dimension
		    narrowIth(i, r, UsedRect, ProfileCandidates);
		}
	}

	void narrowRectangles(HashSet<IntVar> fdvQueue) {
		boolean needToNarrow = false;
		ArrayList<IntRectangle> UsedRect = new ArrayList<IntRectangle>();
		ArrayList<Rectangle> ProfileCandidates = new ArrayList<Rectangle>();

		for (Rectangle r : rectangles) {
			boolean settled = true, minLengthEq0 = false;
			int maxLevel = 0;
			for (int i = 0; i < r.dim; i++) {
				IntDomain rOrigin = r.origin[i].dom();
				IntDomain rLength = r.length[i].dom();
				settled = settled && rOrigin.singleton() && rLength.singleton();

				minLengthEq0 = minLengthEq0 || (rLength.min() <= 0);

				int originStamp = rOrigin.stamp, lengthStamp = rLength.stamp;
				if (maxLevel < originStamp)
					maxLevel = originStamp;
				if (maxLevel < lengthStamp)
					maxLevel = lengthStamp;
			}

			if (//!minLengthEq0 && // Check for rectangle r which has
					// all lengths > 0
					!(settled && maxLevel < currentStore.level)) {
				// and are not fixed already

				// System.out.println(r+", "+ containsChangedVariable(r,
				// fdvQueue));
				needToNarrow = needToNarrow
						|| containsChangedVariable(r, fdvQueue);

				UsedRect.clear();
				ProfileCandidates.clear();
				boolean ntN = findRectangles(r, UsedRect, ProfileCandidates,
						fdvQueue);
				needToNarrow = needToNarrow || ntN;

				// Checking r against all s with minUse in the domain of r
				if (needToNarrow)
					narrowRectangle(r, UsedRect, ProfileCandidates);
			}
		}
	}

	boolean notFit(int i, Rectangle r, ArrayList<IntRectangle> ConsideredRect,
			int barierPosition) {
		Profile barrier = new Profile( (short) Profile.diffn );
		int minimalAfter = 0;
		int j = 0;
		boolean excludedState = true;
		while (excludedState && j < r.dim) {
			if (i != j) {
				// System.out.println(r.toStringFull()+"\n"+ConsideredRect );
				IntDomain rOriginJdom = r.origin[j].dom();
				IntDomain rLengthJdom = r.length[j].dom();
				int minJ = rOriginJdom.min();
				int maxJ = rOriginJdom.max() + rLengthJdom.min();
				int durJ = rLengthJdom.min();

				int currentJposition = minJ;
				// System.out.println("max position for r=" + maxJ+
				// ", min duration of r=" + durJ+", start position=" +
				// currentJposition);
				barrier.clear();
				for (IntRectangle hinder : ConsideredRect) {
					// System.out.println("["+ hinder.origin[j] + ".."
					// + (int)(hinder.origin[j]
					// + hinder.length[j]) +"), "
					// + (int)(hinder.origin[i] + hinder.length[i] -
					// barierPosition));
					int hinderJ = hinder.origin[j];
					int hinderValue = hinder.origin[i] + hinder.length[i]
							- barierPosition;
					barrier.addToProfile(hinderJ, hinderJ + hinder.length[j],
							hinderValue);
					if (minimalAfter > hinderValue)
						minimalAfter = hinderValue;
				}
				// System.out.println("Barrier : " + barrier);

				int k = 0, barrierSize = barrier.size();
				while (k < barrierSize && excludedState) {
					ProfileItem p = barrier.get(k);
					int hinderStart = p.min;
					int hinderStop = p.max;
					if (hinderStart - currentJposition >= durJ)
						excludedState = false;
					currentJposition = hinderStop;
					k++;
					// System.out.println("Hinder = " + hinderStart + ".." +
					// hinderStop);
					// System.out.println("*** Excluded = " + excludedState);
				}
				if (excludedState && maxJ - currentJposition >= durJ)
					excludedState = false;

				if (excludedState) {
					ProfileItem first = barrier.get(0);
					ProfileItem last = barrier.get(barrier.size() - 1);
					if (minJ < first.min) // exist free space before first
						// obstacle
						barrier.addToProfile(minJ, first.min, minimalAfter);
					if (maxJ > last.max) // exist free space after last
						// obstacle
						barrier.addToProfile(last.max, maxJ, minimalAfter);
					ArrayList<Interval> toAdd = new ArrayList<Interval>();
					for (int m = 0; m < barrier.size() - 1; m++) {
						ProfileItem p = barrier.get(m);
						ProfileItem pNext = barrier.get(m + 1);
						if (p.max != pNext.min)
							toAdd.add(new Interval(p.max, pNext.min));
					}
					// for (ProfileItem p : barrier) System.out.print(p + " ");
					for (Interval v : toAdd) {
						// System.out.println("\n*** adding " + v);
						barrier.addToProfile(v.min, v.max, minimalAfter);
					}
					// for (ProfileItem p : barrier) System.out.print(p + " ");
					// System.out.println("minimalAfter = " + minimalAfter);

					int minSizeAfterBarier = IntDomain.MaxInt;
					for (int m = 0; m < barrier.size(); m++) {
						ProfileItem p = barrier.get(m);
						if (p.value < minSizeAfterBarier) {
							if (p.value == minimalAfter
									&& p.max - p.min >= durJ) {
								minSizeAfterBarier = minimalAfter;
								break;
							}
							if (p.value > minimalAfter)
								minSizeAfterBarier = p.value;
						}
					}
					minPosition = minSizeAfterBarier;

					// System.out.print("==> [");
					// for (ProfileItem p : barrier) System.out.print(p + " ");
					// System.out.println("], minSizeAfterBarrier = " +
					// minSizeAfterBarier);
				}
			}
			j++;
		}

		// System.out.println("2. " + excludedState + ", minPosition = " +
		// minPosition);
		return excludedState;
	}

	void profileCheckInterval(Store store, DiffnProfile Profile, int limit,
			IntVar Start, IntVar Duration, int iMin, int i_max,
			IntVar Resources) {

		int dur = Duration.min();
		int iMax = i_max + dur;
		for (ProfileItem p : Profile) {
			if (trace)
				System.out.println("Comparing " + "[" + iMin + ", " + i_max
						+ "]" + " with profile item " + p);

			if (intervalOverlap(iMin, iMax, p.min, p.max)) {
				if (limit - p.value < Resources.min()) {
					// Check for possible narrowing of Start or fail
					IntDomain StartDom = Start.dom();
					int updateMin = p.min - dur + 1, updateMax = p.max - 1;

					if (!(updateMin > StartDom.max() || updateMax < StartDom.min())) {

						IntervalDomain Update = new IntervalDomain(IntDomain.MinInt,
								p.min - dur);
						Update.unionAdapt(p.max, IntDomain.MaxInt);

						if (traceNarr)
							System.out.print("6. Profile Narrowed " + Start
									+ " \\ " + Update);

						Start.domain.in(store.level, Start, Update);

						if (traceNarr)
							System.out.println(" => " + Start);

						computeNewMaxDuration(Start, dur, p.min, p.max);

						int lengthLimit = 0;
						for (int l : durMax)
						    if (lengthLimit < l) lengthLimit = l;
						
						if (traceNarr)
						    System.out.println("6b. Length " + Duration + " <-- 0.." + lengthLimit);

						Duration.domain.in(currentStore.level, Duration, 0, lengthLimit);

					}
				} else {
					IntDomain StartDom = Start.dom();
					int start = StartDom.max(), stop = StartDom.min() + dur;
					if (start < stop
							&& intervalOverlap(start, stop, p.min, p.max)) {
						int updateMax = limit - p.value;
						if (updateMax < Resources.max()) {
							IntervalDomain Update = new IntervalDomain(0, updateMax);

							if (traceNarr)
								System.out.println("8. Profile Narrowed "
										+ Resources + " in " + Update);

							Resources.domain.in(store.level, Resources, Update);

							if (traceNarr)
								System.out.println(" => " + Resources);

						}
					}
				}
			}
		}
	}

	void profileCheckRectangle(DiffnProfile Profile, Rectangle r, int i, int j) {

		IntVar s = r.origin[i];
		IntVar dur = r.length[i];
		IntVar resUse = r.length[j];
		IntDomain rOriginJdom = r.origin[j].dom();
		int limit = rOriginJdom.max() + resUse.max() - rOriginJdom.min();

		if (trace)
			System.out.println("Start time = " + s + ", resource use = "
					+ resUse);

		IntDomain sDom = s.dom();

		for (int m = 0; m < sDom.noIntervals(); m++) {
			profileCheckInterval(currentStore, Profile, limit, s, dur, sDom
					.leftElement(m), sDom.rightElement(m), resUse);
		}
	}

	void profileNarrowing(int i, Rectangle r,
			ArrayList<Rectangle> ProfileCandidates) {
		// check profile first

		IntDomain rOriginIdom = r.origin[i].dom();
		int rOriginIdomMin = rOriginIdom.min();
		int rOriginIdomMax = rOriginIdom.max();
		DiffnProfile Profile = new DiffnProfile();

		for (int j = 0; j < r.dim; j++) {
			if (j != i) {
				Profile.make(j, i, r, rOriginIdomMin, rOriginIdomMax
						+ r.length[i].min(), ProfileCandidates);

				if (Profile.size() != 0) {
					if (trace) {
						System.out.println(r + "\n" + ProfileCandidates);
						System.out.println("Profile in dimension " + i
								+ " and " + j + "\n" + Profile);
					}

					profileCheckRectangle(Profile, r, i, j);

				}
			}
		}
	}

	@Override
	public void queueVariable(int level, Var V) {
		if (level == stamp)
			variableQueue.add((IntVar)V);
		else {
			variableQueue.clear();
			stamp = level;
			variableQueue.add((IntVar)V);
		}
	}

	@Override
	public void removeConstraint() {
		for (Rectangle R : rectangles) {
			for (int i = 0; i < R.dim; i++) {
				Var v = R.origin[i];
				v.removeConstraint(this);
				v = R.length[i];
				v.removeConstraint(this);
			}
		}
	}

	@Override
	public boolean satisfied() {
		boolean sat = true;

		Rectangle recti, rectj;
		int i = 0;
		while (sat && i < rectangles.length) {
			recti = rectangles[i];
			int j = i + 1;
			while (sat && j < rectangles.length) {
				rectj = rectangles[j];
				sat = sat && !recti.domOverlap(rectj);
				j++;
			}
			i++;
		}
		return sat;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer( id() );
		
		result.append(" : diff (");

		int i = 0;
		for (Rectangle R : rectangles) {
			result.append(R);
			if (i < rectangles.length - 1)
				result.append(", ");
			i++;
		}
		return result.append(")").toString();
	}


	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			for (Rectangle r : rectangles) { 
				for (Var v : r.length) v.weight++;
				for (Var v : r.origin) v.weight++;
			}
		}
	}

	class DimIMinComparator<T extends IntRectangle> implements Comparator<T> {

		int i;

		DimIMinComparator() {
		}

		DimIMinComparator(int dimension) {
			i = dimension;
		}

		public int compare(T o1, T o2) {
			int v1 = o1.origin[i];
			int v2 = o2.origin[i];
			return v1 - v2;
		}

	}

	class Pair {
		int Min, Max;

		Pair(int i1, int i2) {
			Min = i1;
			Max = i2;
		}
	}
	
}



