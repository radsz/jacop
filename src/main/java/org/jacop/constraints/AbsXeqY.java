/**
 *  AbsXeqY.java 
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
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.SmallDenseDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Constraints |X| #= Y
 * 
 * Domain and bounds consistency can be used; third parameter of constructor controls this.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class AbsXeqY extends PrimitiveConstraint {

	static int IdNumber = 1;

	static final boolean debugAll = false;

	boolean firstConsistencyCheck = true;

    boolean domainConsistent = false;

	int firstConsistencyLevel;

	/**
	 * It contains variable x.
	 */
	public IntVar x;

	/**
	 * It contains variable y.
	 */
	public IntVar y;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"x", "y"};

	/**
	 * It constructs |X| = Y constraints.
	 * @param x variable X1
	 * @param y variable Y
	 */
	public AbsXeqY(IntVar x, IntVar y) {

		assert (x != null) : "Variable x is null";
		assert (y != null) : "Variable y is null";

		numberId = IdNumber++;
		numberArgs = 2;

		this.queueIndex = 0;
		this.x = x;
		this.y = y;
	}

	/**
	 * It constructs |X| = Y constraints.
	 * @param x variable X1
	 * @param y variable Y
	 * @param domConsistency controls which consistency method is used; true = domain, false = bound
	 */
    public AbsXeqY(IntVar x, IntVar y, boolean domConsistency) {
	    this(x, y);

	    domainConsistent = domConsistency;

	    if (domainConsistent)
		this.queueIndex = 1;
	    else
		this.queueIndex = 0;
	}


	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(2);

		variables.add(x);
		variables.add(y);
		return variables;
	}

	@Override
	public void removeLevel(int level) {
		if (level == firstConsistencyLevel) 
			firstConsistencyCheck = true;
	}

	@Override
	public void consistency(Store store) {

		if (firstConsistencyCheck) {
			y.domain.inMin(store.level, y, 0);
			firstConsistencyCheck = false;
			firstConsistencyLevel = store.level;
		}

		if (domainConsistent)
		    domainConsistency(store);
		else
		    boundConsistency(store);

	}

    void domainConsistency(Store store) {

		do {

			store.propagationHasOccurred = false;

			if (debugAll)
				System.out.println("X " + x + " Y " + y);

			IntervalDomain xDom;

			if (x.domain.domainID() == IntDomain.IntervalDomainID)
				xDom = (IntervalDomain) x.domain;
			else {

				if (x.domain.domainID() == IntDomain.SmallDenseDomainID)
					xDom = ((SmallDenseDomain)x.domain).toIntervalDomain();
				else {

					xDom = new IntervalDomain();
					IntervalEnumeration enumer = x.domain.intervalEnumeration();
					while (enumer.hasMoreElements()) {
						Interval next = enumer.nextElement();
						xDom.unionAdapt(next);
					}					
				}
			}

			IntervalDomain yDom1 = new IntervalDomain(xDom.size + 1);

			int i = 0;
			Interval[] intervals = xDom.intervals;
			for (; i < xDom.size; i++)
				if (intervals[i].max > 0)
					break;

			int j = i;
			if (j == xDom.size)
				j--;

			for (; j >= 0; j--)
				if (intervals[j].max <= 0)
					yDom1.unionAdapt(-intervals[j].max, -intervals[j].min);

			if (i < xDom.size && intervals[i].min < 0
					&& intervals[i].max > 0) {

				if (-intervals[i].min > intervals[i].max)
					yDom1.unionAdapt(0, -intervals[i].min);
				else
					yDom1.unionAdapt(0, intervals[i].max);

			}

			IntervalDomain yDom = new IntervalDomain(xDom.size + 1);

			for (; i < xDom.size; i++)
				yDom.unionAdapt(intervals[i]);

			yDom.addDom(yDom1);

			if (debugAll)
				System.out.println("new Ydom " + yDom);

			// @todo, test more the change from yDom1 to yDom.
			y.domain.in(store.level, y, yDom);

			xDom = new IntervalDomain(xDom.size + 1);


			if (y.domain.domainID() == IntDomain.IntervalDomainID)
				yDom = (IntervalDomain) y.domain;
			else {

				if (y.domain.domainID() == IntDomain.SmallDenseDomainID)
					yDom = ((SmallDenseDomain)y.domain).toIntervalDomain();
				else {

					yDom = new IntervalDomain();
					IntervalEnumeration enumer = y.domain.intervalEnumeration();
					while (enumer.hasMoreElements()) {
						Interval next = enumer.nextElement();
						yDom.unionAdapt(next);
					}					
				}
			}

			for (i = yDom.size - 1; i >= 0; i--)
				xDom.unionAdapt(-yDom.intervals[i].max, -yDom.intervals[i].min);

			xDom.addDom(yDom);

			if (debugAll)
				System.out.println("new Xdom " + xDom);

			x.domain.in(store.level, x, xDom);

		} while (store.propagationHasOccurred);

    }

    void boundConsistency(Store store) {

	do {

	    if (x.min() >= 0) {
		// possible domain consistecny for this case
		// x.domain.in(store.level, x, y.domain);
		// store.propagationHasOccurred = false;
		// y.domain.in(store.level, y, x.domain);

		// bounds consistency
		x.domain.in(store.level, x, y.min(), y.max());

		store.propagationHasOccurred = false;

		y.domain.in(store.level, y, x.min(), x.max());
	    }
	    else if (x.max() < 0) {
		x.domain.in(store.level, x, -y.max(), -y.min());

		store.propagationHasOccurred = false;

		y.domain.in(store.level, y, -x.max(), -x.min());			
	    }
	    else { // x.min() < 0 && x.max() >= 0
		// int xBound = Math.max(y.min(), y.max());
		int xBound = y.max();   // y is always >= 0
		x.domain.in(store.level, x, -xBound, xBound);

		store.propagationHasOccurred = false;

		y.domain.inMax(store.level, y, Math.max(-x.min(), x.max()));
	    }

	} while (store.propagationHasOccurred);

    }


	@Override
	public int getNestedPruningEvent(Var var, boolean mode) {

		// If consistency function mode
		if (mode) {
			if (consistencyPruningEvents != null) {
				Integer possibleEvent = consistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			
			if (domainConsistent)
			    return IntDomain.ANY;
			else
			    return IntDomain.BOUND;
		}
		// If notConsistency function mode
		else {
			if (notConsistencyPruningEvents != null) {
				Integer possibleEvent = notConsistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return IntDomain.GROUND;
		}
	}

	@Override
	public int getConsistencyPruningEvent(Var var) {

		// consistency function mode
		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}

		if (domainConsistent)
		    return IntDomain.ANY;
		else
		    return IntDomain.BOUND;

	}


	@Override
	public int getNotConsistencyPruningEvent(Var var) {
		// notConsistency function mode
		if (notConsistencyPruningEvents != null) {
			Integer possibleEvent = notConsistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return IntDomain.GROUND;
	}

	@Override
	public void impose(Store store) {
		x.putModelConstraint(this, getConsistencyPruningEvent(x));
		y.putModelConstraint(this, getConsistencyPruningEvent(y));
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void notConsistency(Store store) {

		do {
			store.propagationHasOccurred = false;

			if (y.singleton()) {

				x.domain.inComplement(store.level, x, y.value());
				x.domain.inComplement(store.level, x, -y.value());

			}

			if (x.singleton()) {

				if (x.value() >= 0)
					y.domain.inComplement(store.level, y, x.value());
				else
					y.domain.inComplement(store.level, y, -x.value());
			}

		} while (store.propagationHasOccurred);

	}

	@Override
	public boolean notSatisfied() {

		IntDomain xDom = x.domain;
		IntDomain yDom = y.domain;
		int xSize = xDom.noIntervals();
		for (int i = 0; i < xSize; i++) {

			int right = xDom.rightElement(i);

			if (right <= 0) {
				if (yDom.isIntersecting(-right, -xDom.leftElement(i)))
					return false;
			} else {

				int left = xDom.leftElement(i);
				if (left >= 0) {
					if (yDom.isIntersecting(left, right))
						return false;
				} else {

					if (yDom.isIntersecting(0, -left))
						return false;
					if (yDom.isIntersecting(0, right))
						return false;
				}

			}

		}

		return true;

	}

	@Override
	public void removeConstraint() {
		x.removeConstraint(this);
		y.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
		return x.singleton() && y.singleton()
		&& (x.min() == y.min() || -x.min() == y.min());
	}


	@Override
	public String toString() {

		StringBuffer result = new StringBuffer( id() );

		result.append(" : absXeqY(").append(x).append(", ").append(y).append(" )");

		return result.toString();

	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			x.weight++;
			y.weight++;
		}
	}

}
