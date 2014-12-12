/**
 *  DisjointCondVar.java 
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

import java.util.Vector;

import org.jacop.core.MutableVar;
import org.jacop.core.MutableVarValue;
import org.jacop.core.Store;

/**
 * Defines a Variable for Diff2 constraints and related operations on it. It
 * keeps current recatngles for evaluation ([[R2, R3], [R1, R3], ...]
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

class DisjointCondVar implements MutableVar {

	int index;

	Store store;

	DisjointCondVarValue value = null;

	DisjointCondVar(Store S) {
		DisjointCondVarValue val = new DisjointCondVarValue();
		value = val;
		index = S.putMutableVar(this);
		store = S;
	}

	DisjointCondVar(Store S, RectangleWithCondition[] R) {
		value = new DisjointCondVarValue(R);
		index = S.putMutableVar(this);
		store = S;
	}

	DisjointCondVar(Store S, Vector<RectangleWithCondition> R) {
		value = new DisjointCondVarValue();
		value.setValue(R);
		index = S.putMutableVar(this);
		store = S;
	}

	int index() {
		return index;
	}

	public MutableVarValue previous() {
		return value.previousDisjointCondVarValue;
	}

	public void removeLevel(int removeLevel) {
		if (value.stamp == removeLevel) {
			value = value.previousDisjointCondVarValue;
		}
	}

	public void setCurrent(MutableVarValue o) {
		value = (DisjointCondVarValue) o;
	}

	int stamp() {
		return value.stamp;
	}

	@Override
	public String toString() {
		String S = "DisjointCondVar[" + index + "] = [";
		DisjointCondVarValue val = value;
		S = S + val + "]";
		return S;
	}

	public void update(MutableVarValue val) {
		// DisjointCondVarValue VarValue = (DisjointCondVarValue)value();
		if (value.stamp == store.level) {
			// System.out.print("1. Level: "+store.level()+", IN "+VarValue+",
			// New " + val);
			value.setValue(((DisjointCondVarValue) val).Rects);
			// System.out.println(", OUT "+ value);
		} else if (value.stamp < store.level) {
			// System.out.print("2. Level: "+store.level()+", IN "+this+", New "
			// + val);
			val.setStamp(store.level);
			val.setPrevious(value);
			value = (DisjointCondVarValue) val;

			// System.out.println("\n=> OUT "+ this+ "\nOLD "+ value().next());
		}
	}

	public MutableVarValue value() {
		return value;
	}
}
