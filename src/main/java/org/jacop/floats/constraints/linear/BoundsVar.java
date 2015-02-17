/**
 *  BoundsVar.java 
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

import org.jacop.core.MutableVar;
import org.jacop.core.MutableVarValue;
import org.jacop.core.Store;

/**
 * Defines a variable for Linear constraints to keep intermediate bounds
 * values
 * 
 * @author Krzysztof Kuchcinski
 * @version 4.2
 */

class BoundsVar implements MutableVar {

    int index;

    Store store;

    BoundsVarValue value = null;

    BoundsVar(Store store) {
	BoundsVarValue val = new BoundsVarValue();
	value = val;
	index = store.putMutableVar(this);
	this.store = store;
    }

    BoundsVar(Store store, double min, double max) {
	BoundsVarValue val = new BoundsVarValue();

	assert(min <= max) : "Min value " + min + " greater than max value " + max + " in BoundsVar";

	val.min = min;
	val.max = max;
	value = val;
	index = store.putMutableVar(this);
	this.store = store;
    }

    BoundsVar(Store store, double min, double max, double lb, double ub) {
	BoundsVarValue val = new BoundsVarValue();

	assert(min <= max) : "Min value " + min + " greater than max value " + max + " in BoundsVar";

	val.min = min;
	val.max = max;
	val.lb = lb;
	val.ub = ub;
	value = val;
	index = store.putMutableVar(this);
	this.store = store;
    }

    int index() {
	return index;
    }

    public MutableVarValue previous() {
	return value.previousBoundsVarValue;
    }

    public void removeLevel(int removeLevel) {
	if (value.stamp == removeLevel) {
	    value = value.previousBoundsVarValue;
	}
    }

    public void setCurrent(MutableVarValue o) {
	value = (BoundsVarValue) o;
    }

    int stamp() {
	return value.stamp;
    }

    @Override
	public String toString() {
		
	StringBuffer result = new StringBuffer();
	result.append( "BoundsVar[").append( index ).append("] = [");
	result.append( value ).append( "]" );
	return result.toString();
    }

    public void update(MutableVarValue val) {
	if (value.stamp == store.level) {

	    value.setValue(((BoundsVarValue)val).min, ((BoundsVarValue)val).max,
			   ((BoundsVarValue)val).lb, ((BoundsVarValue)val).ub);

	} else if (value.stamp < store.level) {

	    val.setStamp(store.level);
	    val.setPrevious(value);
	    value = (BoundsVarValue) val;

	}
    }


    public void update(double min, double max, double lb, double ub) {
	if (value.stamp == store.level) {

	    // value.setValue(min, max);
	    value.min = min;
	    value.max = max;

	    value.lb = lb;
	    value.ub = ub;

	} else if (value.stamp < store.level) {
	    
	    BoundsVarValue val = new BoundsVarValue(min, max, lb, ub);
	    val.stamp = store.level;
	    val.setPrevious(value);
	    value = val;

	}
    }

    public MutableVarValue value() {
	return value;
    }
}
