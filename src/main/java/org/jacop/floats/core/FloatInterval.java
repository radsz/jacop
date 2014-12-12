/**
 *  FloatInterval.java 
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

package org.jacop.floats.core;

import java.lang.Math;

/**
 * Defines interval of numbers which is part of FDV definition which consist of
 * one or several intervals.
 * 
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public final class FloatInterval {

    /**
     * It specifies the minimal value in the interval.
     */
    public final double min;

    /**
     * It specifies the maximal value in the interval.
     */
    public final double max;

    /**
     * It creates the largest possible interval.
     */
    public FloatInterval() {
	min = FloatDomain.MinFloat;
	max = FloatDomain.MaxFloat;
    }

    /**
     * It creates an interval with a given minimum and maximal value.
     * @param min the minimal value in the interval (the left bound). 
     * @param max the maximal value in the interval (the right bound).
     */
    public FloatInterval(double min, double max) {

	assert (min <= max) : "min value " + min + 
	    " is larger than max value " + max;

	this.min = min;
	this.max = max;

    }

    @Override
    public Object clone() {
	return new FloatInterval(min, max);
    }

    /**
     * It checks equality between intervals.
     * @param interval the inerval to which the comparison is made.
     * @return true if an input interval is equal to this one.
     */
    public boolean eq(FloatInterval interval) {
	// return min == interval.min && max == interval.max;

	double v = Math.max(Math.abs(min - interval.min), Math.abs(max - interval.max));
	return v <= FloatDomain.epsilon(v);

    }

    /**
     * It returns the right bound of the interval (maximum value).
     * @return the maximal value from the interval.
     */
    public double max() {
	return max;
    }

    /**
     * It returns the left range of the interval (minimum value).
     * @return the minimal value from the interval.
     */
    public double min() {
	return min;
    }

    /**
     * It checks if an intervals contains only one value (singleton).
     * @return true if domain has only one value.
     */
    public boolean singleton() {

	// double large = (Math.abs(max) >= Math.abs(min)) ? max : min;  
	double small = (Math.abs(max) >= Math.abs(min)) ? min : max;  

	return (max-min) <= FloatDomain.epsilon(small);

    }

    /**
     * It checks if an intervals contains only value c.
     * @param c integer value to which the singleton is compared to.
     * @return true if variable has a singleton domain and it is equal to value c.
     */

    public boolean singleton(double c) {
	// return (min == max && min == c);

	return (max - min) <= FloatDomain.epsilon(max-min) && c <= max && c >= min;
    }

    @Override
    public String toString() {

	java.util.Locale locale = new java.util.Locale("ENGLISH", "GERMANY");
	long p = new Double(Math.ceil(Math.log10(1/FloatDomain.precision()))).longValue();
	String form = (Math.abs(min) >= 1.0E+7d || 
		       Math.abs(max) >= 1.0E+7 || 
		       (Math.abs(min) <= 1.0E-3 && min != 0) || 
		       (Math.abs(max) <= 1.0E-3 && max != 0)) ? "%."+p+"e" : "%."+p+"f";

	String result;

	if (!FloatDomain.intervalPrint && singleton())
	    result = String.format(locale, form, (double)((min+max)/2)); // mean value if singleton considering precision
	else
	    result = String.format(locale, form, min) + ".." + String.format(locale, form, max);  // String.format("%.16f..%.16f", min, max); // interval

	// result += "[±"+ FloatDomain.ulp(min) + "]";

	return result;
    }

}
