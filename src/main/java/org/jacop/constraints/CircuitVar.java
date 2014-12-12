/**
 *  CircuitVar.java 
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

import org.jacop.core.MutableVar;
import org.jacop.core.MutableVarValue;
import org.jacop.core.Store;

/**
 * Defines a Variable for Circuit constraints and related operations on it. It
 * keeps current next node and previous node for the circuit
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

class CircuitVar implements MutableVar {

	int index;

	Store store;

	CircuitVarValue value = null;

	CircuitVar(Store store) {
		CircuitVarValue val = new CircuitVarValue();
		value = val;
		index = store.putMutableVar(this);
		this.store = store;
	}

	CircuitVar(Store store, int next, int previous) {
		CircuitVarValue val = new CircuitVarValue();
		val.next = next;
		val.previous = previous;
		value = val;
		index = store.putMutableVar(this);
		this.store = store;
	}

	int index() {
		return index;
	}

	public MutableVarValue previous() {
		return value.nextCircuitVarValue;
	}

	public void removeLevel(int removeLevel) {
		if (value.stamp == removeLevel)
			value = value.nextCircuitVarValue;
	}

	public void setCurrent(MutableVarValue o) {
		value = (CircuitVarValue) o;
	}

	int stamp() {
		return value.stamp;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer();

		result.append("CircuitVar[").append( (index + 1) ).append("] = ");
		
		result.append(value);
		
		return result.toString();
		
	}

	public void update(MutableVarValue val) {

		// if ( value.stamp > store.level ) {
		// System.out.println("Warning old stamps not removed");
		// System.exit(-1);
		// }

		if (value.stamp == store.level) {
			// System.out.print("1. Level: "+store.level()+", IN "+VarValue+",
			// New " + val);
			value.setValue(((CircuitVarValue) val).next,
					((CircuitVarValue) val).previous);
			// System.out.println(", OUT "+ VarValue);
		} else if (value.stamp < store.level) {
			// System.out.print("2. Level: "+store.level()+", IN "+this+", New "
			// + val);

			val.setStamp(store.level);
			val.setPrevious(value);
			value = (CircuitVarValue) val;

			// System.out.println("\n=> OUT "+ this+"\nOLD "+ value().next());
		}
	}

	public MutableVarValue value() {
		return value;
	}

}
