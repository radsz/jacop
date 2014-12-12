/**
 *  Assignment.java 
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
import java.util.HashMap;
import java.util.LinkedHashSet;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Assignment constraint implements facility to improve channeling constraints
 * between dual viewpoints of permutation models.
 * It enforces the relationship x[d[i]-shiftX]=i+shiftD and d[x[i]-shiftD]=i+shiftX. 
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * 
 * @version 4.2
 */

public class Assignment extends Constraint {

	static int counter = 1;

	/**
	 * It specifies a list of variables d. 
	 */
	public IntVar d[];
	/**
	 * It specifies a shift applied to variables d.
	 */
	public int shiftD = 0;
	
	HashMap<IntVar, Integer> ds;
	
	/**
	 * It specifies a list of variables x. 
	 */
	public IntVar x[];	
	/**
	 * It specifies a shift applied to variables x.
	 */
	public int shiftX = 0;
	
	HashMap<IntVar, Integer> xs;
	

	LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<IntVar>();
	boolean firstConsistencyCheck = true;
	int firstConsistencyLevel;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"x", "d", "shiftX", "shiftD"};

	/**
	 * It enforces the relationship x[d[i]-shiftX]=i+shiftD and
	 * d[x[i]-shiftD]=i+shiftX. 
	 * @param xs array of variables x
	 * @param ds array of variables d
	 * @param shiftX a shift of indexes in X array.
	 * @param shiftD a shift of indexes in D array.
	 */
	public Assignment(IntVar[] xs, IntVar[] ds, int shiftX, int shiftD) {

		numberId = counter++;

		this.shiftX = shiftX;
		this.shiftD = shiftD;
		this.x = new IntVar[xs.length];
		for (int i = 0; i < xs.length; i++)
			this.x[i] = xs[i];

		this.d = new IntVar[ds.length];
		for (int i = 0; i < ds.length; i++)
			this.d[i] = ds[i];
	
		this.queueIndex = 1;

		this.xs = new HashMap<IntVar, Integer>(xs.length * 2);
		this.ds = new HashMap<IntVar, Integer>(ds.length * 2);

		for (int i = 0; i < xs.length; i++) {
			this.xs.put(x[i], i + shiftX);
			this.ds.put(d[i], i + shiftD);
		}

		this.numberArgs = (short) ( xs.length + ds.length );

	}

	/**
	 * It enforces the relationship x[d[i]-shiftX]=i+shiftD and
	 * d[x[i]-shiftD]=i+shiftX. 
	 * @param xs arraylist of variables x
	 * @param ds arraylist of variables d
	 * @param shiftX 
	 * @param shiftD 
	 */
	public Assignment(ArrayList<? extends IntVar> xs,
			ArrayList<? extends IntVar> ds, 
			int shiftX, 
			int shiftD) {

		this(xs.toArray(new IntVar[xs.size()]), ds.toArray(new IntVar[ds.size()]), shiftX, shiftD);

	}


	/**
	 * It constructs an Assignment constraint with shift equal 0. It
	 * enforces relation - d[x[j]] = i and x[d[i]] = j.
	 * @param xs arraylist of x variables
	 * @param ds arraylist of d variables
	 */
	public Assignment(ArrayList<? extends IntVar> xs,
			ArrayList<? extends IntVar> ds) {

		this(xs.toArray(new IntVar[xs.size()]), ds.toArray(new IntVar[ds.size()]), 0, 0);

	}

	/**
	 * It enforces the relationship x[d[i]-min]=i+min and
	 * d[x[i]-min]=i+min. 
	 * @param xs arraylist of variables x
	 * @param ds arraylist of variables d
	 * @param min shift
	 */
	public Assignment(ArrayList<? extends Var> xs,
			ArrayList<? extends Var> ds, 
			int min) {

		this(xs.toArray(new IntVar[xs.size()]), ds.toArray(new IntVar[ds.size()]), min, min);

	}


	/**
	 * It constructs an Assignment constraint with shift equal 0. It
	 * enforces relation - d[x[i]] = i and x[d[i]] = i.
	 * @param xs array of x variables
	 * @param ds array of d variables
	 */
	public Assignment(IntVar[] xs, IntVar[] ds) {

		this(xs, ds, 0, 0);

	}

	/**
	 * It enforces the relationship x[d[i]-min]=i+min and
	 * d[x[i]-min]=i+min. 
	 * @param xs array of variables x
	 * @param ds array of variables d
	 * @param min shift
	 */
	public Assignment(IntVar[] xs, IntVar[] ds, int min) {

		this(xs, ds, min, min);

	}


	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(
				x.length * 2 + 1);

		for (int i = 0; i < x.length; i++) {
			variables.add(x[i]);
			variables.add(d[i]);
		}

		return variables;
	}

	@Override
	public void removeLevel(int level) {
		variableQueue = new LinkedHashSet<IntVar>();
		if (level == firstConsistencyLevel)
			firstConsistencyCheck = true;
	}


	IntervalDomain rangeX;
	IntervalDomain rangeD;

	@Override
	public void consistency(Store store) {

		if (firstConsistencyCheck) {

			rangeX = new IntervalDomain(0 + shiftX, x.length - 1
					+ shiftX);

			rangeD = new IntervalDomain(0 + shiftD, x.length - 1
					+ shiftD);

			for (int i = 0; i < x.length; i++) {

				IntDomain alreadyRemoved = rangeD.subtract(x[i].domain);

				x[i].domain.in(store.level, x[i], shiftD, x.length - 1 + shiftD);

				if (!alreadyRemoved.isEmpty())
					for (ValueEnumeration enumer = alreadyRemoved
							.valueEnumeration(); enumer.hasMoreElements();) {

						int xValue = enumer.nextElement();

						d[xValue - shiftD].domain.inComplement(store.level,
								d[xValue - shiftD], i + shiftX);

					}

				if (x[i].singleton()) {
					int position = x[i].value() - shiftD;
					d[position].domain.in(store.level, d[position], i + shiftX, i
							+ shiftX);
				}

			}

			for (int i = 0; i < d.length; i++) {

				IntDomain alreadyRemoved = rangeX.subtract(d[i].domain);

				d[i].domain.in(store.level, d[i], shiftX, x.length - 1 + shiftX);

				if (!alreadyRemoved.isEmpty())
					for (ValueEnumeration enumer = alreadyRemoved
							.valueEnumeration(); enumer.hasMoreElements();) {

						int dValue = enumer.nextElement();

						x[dValue - shiftX].domain.inComplement(store.level,
								x[dValue - shiftX], i + shiftD);

					}

				if (d[i].singleton()) {

					x[d[i].value() - shiftX].domain.in(store.level, x[d[i].value()
					                                                  - shiftX], i + shiftD, i + shiftD);
				}

			}

			firstConsistencyCheck = false;
			firstConsistencyLevel = store.level;

		}

		while (!variableQueue.isEmpty()) {

			LinkedHashSet<IntVar> fdvs = variableQueue;

			variableQueue = new LinkedHashSet<IntVar>();

			for (IntVar V : fdvs) {

				IntDomain vPrunedDomain = V.recentDomainPruning();

				if (!vPrunedDomain.isEmpty()) {

					Integer position = xs.get(V);
					if (position == null) {
						// d variable has been changed
						position = ds.get(V);

						vPrunedDomain = vPrunedDomain.intersect(rangeX);

						if (vPrunedDomain.isEmpty())
							continue;

						for (ValueEnumeration enumer = vPrunedDomain
								.valueEnumeration(); enumer.hasMoreElements();) {

							int dValue = enumer.nextElement() - shiftX;

							if (dValue >= 0 && dValue < x.length)
								x[dValue].domain.inComplement(store.level,
										x[dValue], position);
						}

						if (V.singleton())
							x[V.value() - shiftX].domain.in(store.level, x[V.value() - shiftX], position, position);

					} else {
						// x variable has been changed

						vPrunedDomain = vPrunedDomain.intersect(rangeD);

						if (vPrunedDomain.isEmpty())
							continue;

						for (ValueEnumeration enumer = vPrunedDomain
								.valueEnumeration(); enumer.hasMoreElements();) {

							int xValue = enumer.nextElement() - shiftD;

							if (xValue >= 0 && xValue < d.length)
								d[xValue].domain.inComplement(store.level,
										d[xValue], position);

							if (V.singleton())
								d[V.value() - shiftD].domain.in(store.level, d[V.value() - shiftD], position, position);

						}

					}

				}

			}

		}

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

	// registers the constraint in the constraint store
	@Override
	public void impose(Store store) {

		store.registerRemoveLevelListener(this);

		for (int i = 0; i < x.length; i++) {
			x[i].putModelConstraint(this, getConsistencyPruningEvent(x[i]));
			d[i].putModelConstraint(this, getConsistencyPruningEvent(d[i]));
		}

		store.addChanged(this);
		store.countConstraint();

		store.raiseLevelBeforeConsistency = true;

	}

	@Override
	public void queueVariable(int level, Var var) {
		variableQueue.add((IntVar)var);
	}

	@Override
	public void removeConstraint() {

		for (int i = 0; i < x.length; i++)
			x[i].removeConstraint(this);

		for (int i = 0; i < d.length; i++)
			d[i].removeConstraint(this);

	}

	@Override
	public boolean satisfied() {

		int i = 0;
		while (i < x.length) {
			if (!x[i].singleton())
				return false;
			if (!d[i].singleton())
				return false;
			i++;
		}

		return true;

	}

	@Override
	public String toString() {

		StringBuffer result = new StringBuffer( id() );

		result.append(" : assignment([");

		for (int i = 0; i < x.length; i++) {
			result.append(x[i]);
			if (i < x.length - 1)
				result.append(", ");
		}
		result.append("], [");

		for (int i = 0; i < d.length; i++) {
			result.append(d[i]);
			if (i < d.length - 1)
				result.append(", ");
		}
		result.append("])");

		return result.toString();
	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			for (Var v : x) v.weight++;
			for (Var v : d) v.weight++;
		}
	}

}
