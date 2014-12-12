/**
 *  EWF.java 
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
 * It specifies EWF benchmark.
 * 
 * Source:
 * 
 * @see "Michel, P. and Lauther U. and Duzy, P., The Synthesis Approach to Digital System Design, Kluwer Academic Publisher, 1992"
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class EWF extends Filter {

	/**
	 * It constructs a simple EWF filter.
	 */
	public EWF() {
		this(1, 2);
	}

	
	/**
	 * It constructs a EWF filter with the specified delay
	 * for the addition and multiplication operation.
	 * 
	 * @param addDel the delay of the addition operation.
	 * @param mulDel the delay of the multiplication operation.
	 */
	public EWF(int addDel, int mulDel) {
		
		this.addDel = addDel;
		this.mulDel = mulDel;
		
		name = "EWF";

		int dependencies[][] = { { 0, 2 }, { 0, 15 }, { 0, 17 }, { 1, 4 },
				{ 1, 8 }, { 1, 11 }, { 2, 3 }, { 2, 7 }, { 2, 9 }, { 3, 4 },
				{ 4, 5 }, { 4, 6 }, { 4, 10 }, { 5, 7 }, { 6, 8 }, { 7, 9 },
				{ 7, 10 }, { 8, 11 }, { 8, 13 }, { 8, 19 }, { 9, 12 }, { 10, 13 },
				{ 11, 14 }, { 12, 15 }, { 14, 16 }, { 15, 17 }, { 15, 18 },
				{ 15, 29 }, { 16, 20 }, { 16, 28 }, { 16, 19 }, { 17, 21 },
				{ 18, 22 }, { 19, 23 }, { 20, 24 }, { 21, 27 }, { 22, 25 },
				{ 22, 32 }, { 23, 26 }, { 23, 33 }, { 16, 28 }, { 24, 28 },
				{ 25, 30 }, { 26, 31 }, { 27, 29 }, { 30, 32 }, { 31, 33 } };

		this.dependencies = dependencies;
		
		int ids[] = { addId, addId, addId, addId, addId, mulId, mulId, addId,
				addId, addId, addId, addId, mulId, addId, mulId, addId, addId,
				addId, addId, addId, addId, mulId, addId, addId, mulId, mulId,
				mulId, addId, addId, addId, addId, addId, addId, addId };
		this.ids = ids;
		
		int last[] = { 13, 24, 28, 29, 30, 31, 32, 33 };
		this.last = last;
		
	}

	@Override
	public ArrayList<String> names() {
		ArrayList<String> names = new ArrayList<String>(34);

		names.add("+1");
		names.add("+2");
		names.add("+3");
		names.add("+4");
		names.add("+5");
		names.add("*6");
		names.add("*7");
		names.add("+8");
		names.add("+9");
		names.add("+10");
		names.add("+11");
		names.add("+12");
		names.add("*13");
		names.add("+14");
		names.add("*15");
		names.add("+16");
		names.add("+17");
		names.add("+18");
		names.add("+19");
		names.add("+20");
		names.add("+21");
		names.add("*22");
		names.add("+23");
		names.add("+24");
		names.add("*25");
		names.add("*26");
		names.add("*27");
		names.add("+28");
		names.add("+29");
		names.add("+30");
		names.add("+31");
		names.add("+32");
		names.add("+33");
		names.add("+34");

		return names;
	}

	@Override
	public ArrayList<String> namesPipeline() {
		ArrayList<String> names = new ArrayList<String>(34);

		names.add("+1");
		names.add("+2");
		names.add("+3");
		names.add("+4");
		names.add("+5");
		names.add("*6");
		names.add("*7");
		names.add("+8");
		names.add("+9");
		names.add("+10");
		names.add("+11");
		names.add("+12");
		names.add("*13");
		names.add("+14");
		names.add("*15");
		names.add("+16");
		names.add("+17");
		names.add("+18");
		names.add("+19");
		names.add("+20");
		names.add("+21");
		names.add("*22");
		names.add("+23");
		names.add("+24");
		names.add("*25");
		names.add("*26");
		names.add("*27");
		names.add("+28");
		names.add("+29");
		names.add("+30");
		names.add("+31");
		names.add("+32");
		names.add("+33");
		names.add("+34");

		names.add("+1a");
		names.add("+2a");
		names.add("+3a");
		names.add("+4a");
		names.add("+5a");
		names.add("*6a");
		names.add("*7a");
		names.add("+8a");
		names.add("+9a");
		names.add("+10a");
		names.add("+11a");
		names.add("+12a");
		names.add("*13a");
		names.add("+14a");
		names.add("*15a");
		names.add("+16a");
		names.add("+17a");
		names.add("+18a");
		names.add("+19a");
		names.add("+20a");
		names.add("+21a");
		names.add("*22a");
		names.add("+23a");
		names.add("+24a");
		names.add("*25a");
		names.add("*26a");
		names.add("*27a");
		names.add("+28a");
		names.add("+29a");
		names.add("+30a");
		names.add("+31a");
		names.add("+32a");
		names.add("+33a");
		names.add("+34a");

		names.add("+1b");
		names.add("+2b");
		names.add("+3b");
		names.add("+4b");
		names.add("+5b");
		names.add("*6b");
		names.add("*7b");
		names.add("+8b");
		names.add("+9b");
		names.add("+10b");
		names.add("+11b");
		names.add("+12b");
		names.add("*13b");
		names.add("+14b");
		names.add("*15b");
		names.add("+16b");
		names.add("+17b");
		names.add("+18b");
		names.add("+19b");
		names.add("+20b");
		names.add("+21b");
		names.add("*22b");
		names.add("+23b");
		names.add("+24b");
		names.add("*25b");
		names.add("*26b");
		names.add("*27b");
		names.add("+28b");
		names.add("+29b");
		names.add("+30b");
		names.add("+31b");
		names.add("+32b");
		names.add("+33b");
		names.add("+34b");

		return names;
	}
}
