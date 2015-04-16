/**
 *  BoundsVarValue.java
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

package org.jacop.floats.constraints.linear;

import org.jacop.core.MutableVarValue;

/**
 * Defines a current bounds for the Linear constraint.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.2
 */

class BoundsVarValue implements MutableVarValue {

    BoundsVarValue previousBoundsVarValue = null;

    double min, max;

    double lb, ub;

    int stamp = 0;

    // Constructors
    BoundsVarValue() {
    }

    BoundsVarValue(double min, double max, double lb, double ub) {
	this.min = min;
	this.max = max;

	this.lb = lb;
	this.ub = ub;
    }

    // Methods

    @Override
	public Object clone() {

	BoundsVarValue Val = new BoundsVarValue(min, max, lb, ub);
	Val.stamp = stamp;
	Val.previousBoundsVarValue = previousBoundsVarValue;
	return Val;
    }

    public MutableVarValue previous() {
	return previousBoundsVarValue;
    }

    public void setPrevious(MutableVarValue n) {
	previousBoundsVarValue = (BoundsVarValue) n;
    }

    public void setStamp(int s) {
	stamp = s;
    }

    void setValue(double min, double max, double lb, double ub) {
	this.min = min;
	this.max = max;

	this.lb = lb;
	this.ub = ub;
    }

    public int stamp() {
	return stamp;
    }

    @Override
	public String toString() {

	return min+".."+max + ", "+lb+".."+ub;
    }
}
