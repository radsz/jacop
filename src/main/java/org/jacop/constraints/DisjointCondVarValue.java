/**
 *  DisjointCondVarValue.java 
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

import org.jacop.core.MutableVarValue;

/**
 * Defines a current value of the Diff2Var and related operations on it.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

class DisjointCondVarValue implements MutableVarValue {

	DisjointCondVarValue previousDisjointCondVarValue = null;

	RectangleWithCondition[] Rects;

	int stamp = 0;

	DisjointCondVarValue() {
	}

	DisjointCondVarValue(RectangleWithCondition[] R) {
		Rects = R;
	}

	@Override
	public Object clone() {

		DisjointCondVarValue val = new DisjointCondVarValue(Rects);
		val.stamp = stamp;
		val.previousDisjointCondVarValue = previousDisjointCondVarValue;
		return val;
		
	}

	public MutableVarValue previous() {
		return previousDisjointCondVarValue;
	}

	public void setPrevious(MutableVarValue n) {
		previousDisjointCondVarValue = (DisjointCondVarValue) n;
	}

	public void setStamp(int s) {
		stamp = s;
	}

	void setValue(RectangleWithCondition[] R) {
		Rects = R;
	}

	void setValue(Vector<RectangleWithCondition> VR) {
		Rects = new RectangleWithCondition[VR.size()];
		for (int i = 0; i < Rects.length; i++)
			Rects[i] = VR.get(i);
	}

	public int stamp() {
		return stamp;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer();
		
		for (int i = 0; i < Rects.length; i++)
			if (i == Rects.length - 1)
				result.append(Rects[i]);
			else
				result.append(Rects[i]).append(", ");
		
		return result.toString();
	}
	
}
