/*
 * TableMill.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints.table;

import org.jacop.core.IntVar;
import java.util.ArrayList;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.IntDomain;

/**
 * TableMill generates tables for different constraint to be used in Table constraint
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class TableMill {

    final static int tableMaxSize = 50_000;

    static public int[][] linear(IntVar[] x, int[] w, int b) {

	ArrayList<int[]> support = new ArrayList<int[]>();
	int[] assignment = new int[x.length];

	ArrayList<int[]> table =  linearSupport(x, w, b, 0, 0, support, assignment);

	int[][] t = null;
	if (table != null)
	    t = table.toArray(new int[table.size()][x.length]);
	
	return t;
    }

    static ArrayList<int[]> linearSupport(IntVar[] x, int[] w, int b, int sum, int index, ArrayList<int[]> support, int[] assignment) {
	
	if (index == x.length) {
	    if (sum == b) {
		int[] a = new int[assignment.length];
		System.arraycopy(assignment, 0, a, 0, assignment.length);
		support.add(a);
		if (support.size() > tableMaxSize)
		    return null;
	    }
	}
	else
	    for (ValueEnumeration val = x[index].domain.valueEnumeration(); val.hasMoreElements(); ) {
		int element = val.nextElement();

		int newSum = sum + element * w[index];

		assignment[index] = element;
		linearSupport(x, w, b, newSum, index+1, support, assignment);
	}
	return support;
    }

    static public int[][] elementSupport(IntVar index, int[] list, IntVar value, int offset) {

	ArrayList<int[]> support = new ArrayList<int[]>();
	IntDomain valDom = value.domain;
	for (ValueEnumeration val = index.domain.valueEnumeration(); val.hasMoreElements(); ) {
	    int e = val.nextElement();
	    int listEl = list[e-1-offset];
	    if (valDom.contains(listEl))
		support.add(new int[] {e, listEl});
		if (support.size() > tableMaxSize)
		    return null;
	}

	int[][] t = support.toArray(new int[support.size()][2]);	
	return t;
	
    }
}
