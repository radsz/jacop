/**
 *  ExclusiveList.java 
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

import org.jacop.core.IntVar;

/**
 * Defines a list of exclusive items.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

class ExclusiveList extends ArrayList<ExclusiveItem> {

	private static final long serialVersionUID = 8683452581100000004L;

	ExclusiveList() {
		super();
	}

	IntVar condition(int n, int m) {
		IntVar c = null;
		int i = 0;
		while (c == null && i < size()) {
			ExclusiveItem v = get(i);
			if (((n + 1) == v.i1 && (m + 1) == v.i2)
					|| ((m + 1) == v.i1 && (n + 1) == v.i2))
				c = v.cond;
			i++;
		}
		return c;
	}

	ArrayList<? extends IntVar> fdvs(int index) {
		ArrayList<IntVar> list = new ArrayList<IntVar>();
		for (int i = 0; i < size(); i++) {
			ExclusiveItem v = get(i);
			if (index == v.i1 && !v.cond.singleton())
				list.add(v.cond);
			else if (index == v.i2 && !v.cond.singleton())
				list.add(v.cond);
		}
		return list;
	}

	ExclusiveList listFor(int index) {
		ExclusiveList list = new ExclusiveList();
		for (int i = 0; i < size(); i++) {
			ExclusiveItem v = get(i);
			if (index == v.i1)
				list.add(v);
			else if (index == v.i2)
				list.add(new ExclusiveItem(v.i2, v.i1, v.cond));
		}
		return list;
	}

	boolean onList(int index) {
		boolean found = false;
		int i = 0;
		while (!found && i < size()) {
			ExclusiveItem v = get(i);
			found = index == v.i1 || index == v.i2;
			i++;
		}
		return found;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer("[");
		
		for (int i = 0; i < this.size(); i++) {
			
			result.append(this.get(i).toString());
			
			if (i + 1 < this.size())
				result.append(", ");
		}
		
		result.append("]");
		
		return result.toString();
	}
	
}
