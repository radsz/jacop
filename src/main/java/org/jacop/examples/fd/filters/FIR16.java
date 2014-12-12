/**
 *  FIR16.java 
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

package org.jacop.examples.fd.filters;

import java.util.ArrayList;

/**
 * FIR benchmark (16-point FIR filter)
 * 
 * Source: Kaijie Wu and Ramesh Karri, "Algorithm-Level Recomputing with Shifted
 * Operands -- A Register Transfer Level Concurrent Error Detection Technique"
 * IEEE Trans. on CAD, vol. 25, no. 3, March 2006.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class FIR16 extends Filter {

	/**
	 * It constructs a simple FIR16 filter.
	 */
	public FIR16() {
		this(1, 2);
	}

	
	/**
	 * It constructs a FIR16 filter with the specified delay
	 * for the addition and multiplication operation.
	 * 
	 * @param addDel the delay of the addition operation.
	 * @param mulDel the delay of the multiplication operation.
	 */

	public FIR16(int addDel, int mulDel) {
		this.addDel = addDel;
		this.mulDel = mulDel;
		
		name = "FIR16";

		int dependencies[][] = { { 0, 17 }, { 1, 17 }, { 2, 18 }, { 3, 19 },
				{ 4, 20 }, { 5, 21 }, { 6, 22 }, { 7, 23 }, { 8, 24 }, { 9, 25 },
				{ 10, 26 }, { 11, 27 }, { 12, 28 }, { 13, 29 }, { 14, 30 },
				{ 15, 31 }, { 16, 32 }, { 17, 18 }, { 18, 19 }, { 19, 20 },
				{ 20, 21 }, { 21, 22 }, { 22, 23 }, { 23, 24 }, { 24, 25 },
				{ 25, 26 }, { 26, 27 }, { 27, 28 }, { 28, 29 }, { 29, 30 },
				{ 30, 31 }, { 31, 32 } };
		this.dependencies = dependencies;
		
		int ids[] = { mulId, mulId, mulId, mulId, mulId, mulId, mulId, mulId,
				mulId, mulId, mulId, mulId, mulId, mulId, mulId, mulId, mulId,
				addId, addId, addId, addId, addId, addId, addId, addId, addId,
				addId, addId, addId, addId, addId, addId, addId };
		this.ids = ids;
		
		int last[] = { 32 };
		this.last = last;
	}

	@Override
	public ArrayList<String> names() {
		ArrayList<String> names = new ArrayList<String>(23);

		names.add("+1");
		names.add("*2");
		names.add("+3");
		names.add("+4");
		names.add("+5");
		names.add("+6");
		names.add("+7");
		names.add("+8");
		names.add("+9");
		names.add("+10");
		names.add("*11");
		names.add("+12");
		names.add("*13");
		names.add("+14");
		names.add("*15");
		names.add("+16");
		names.add("*17");
		names.add("+18");
		names.add("*19");
		names.add("+20");
		names.add("*21");
		names.add("+22");
		names.add("*23");

		return names;
	}

	@Override
	public ArrayList<String> namesPipeline() {
		ArrayList<String> names = new ArrayList<String>(23);

		names.add("+1");
		names.add("*2");
		names.add("+3");
		names.add("+4");
		names.add("+5");
		names.add("+6");
		names.add("+7");
		names.add("+8");
		names.add("+9");
		names.add("+10");
		names.add("*11");
		names.add("+12");
		names.add("*13");
		names.add("+14");
		names.add("*15");
		names.add("+16");
		names.add("*17");
		names.add("+18");
		names.add("*19");
		names.add("+20");
		names.add("*21");
		names.add("+22");
		names.add("*23");

		names.add("+1a");
		names.add("*2a");
		names.add("+3a");
		names.add("+4a");
		names.add("+5a");
		names.add("+6a");
		names.add("+7a");
		names.add("+8a");
		names.add("+9a");
		names.add("+10a");
		names.add("*11a");
		names.add("+12a");
		names.add("*13a");
		names.add("+14a");
		names.add("*15a");
		names.add("+16a");
		names.add("*17a");
		names.add("+18a");
		names.add("*19a");
		names.add("+20a");
		names.add("*21a");
		names.add("+22a");
		names.add("*23a");

		names.add("+1b");
		names.add("*2b");
		names.add("+3b");
		names.add("+4b");
		names.add("+5b");
		names.add("+6b");
		names.add("+7b");
		names.add("+8b");
		names.add("+9b");
		names.add("+10b");
		names.add("*11b");
		names.add("+12b");
		names.add("*13b");
		names.add("+14b");
		names.add("*15b");
		names.add("+16b");
		names.add("*17b");
		names.add("+18b");
		names.add("*19b");
		names.add("+20b");
		names.add("*21b");
		names.add("+22b");
		names.add("*23b");

		return names;
	}
}
