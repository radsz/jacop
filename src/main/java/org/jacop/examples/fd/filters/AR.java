/**
 *  AR.java 
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
 * It specifies AR benchmark.
 * 
 * Source:
 * 
 * Rajiv Jain, Alice C. Parker "Experience with the ADAM Synthesis System" 26th
 * ACM/IEEE Design Automation Conference, 1989. and Rajiv Jain, Alice C. Parker,
 * Nohbyung Park, "Predicting Sysem-Level Area and Dealy for Pipelined and
 * Nonpipelined Designs" IEEE Trans. on CAD, vol. 11, no. 8, August 1992.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class AR extends Filter {
	
	/**
	 * It creates a default AR filter with defaul delays for the operations.
	 */
	public AR() {
		this(1, 2);
	}
	
	/**
	 * It possible to specify the delay of the addition and multiplication.
	 * @param addDel the delay of the addition operation.
	 * @param mulDel the delay of the multiplication operation.
	 */
	public AR(int addDel, int mulDel) {
		
		this.addDel = addDel;
		this.mulDel = mulDel;
		name = "AR";
		
		int dependencies[][] = { { 0, 8 }, { 1, 8 }, { 2, 9 }, { 3, 9 }, { 4, 10 },
				{ 5, 10 }, { 6, 11 }, { 7, 11 }, { 8, 26 }, { 9, 27 }, { 10, 12 },
				{ 11, 13 }, { 12, 15 }, { 12, 16 }, { 13, 14 }, { 13, 17 },
				{ 14, 18 }, { 15, 18 }, { 16, 19 }, { 17, 19 }, { 18, 21 },
				{ 18, 22 }, { 19, 20 }, { 19, 23 }, { 20, 24 }, { 21, 24 },
				{ 22, 25 }, { 23, 25 }, { 24, 26 }, { 25, 27 } };
		
		this.dependencies = dependencies;

		int ids[] = { mulId, mulId, mulId, mulId, mulId, mulId, mulId,
				mulId, addId, addId, addId, addId, addId, addId, mulId, mulId,
				mulId, mulId, addId, addId, mulId, mulId, mulId, mulId, addId,
				addId, addId, addId };
		
		this.ids = ids;
		
		int last[] = { 12, 13, 26, 27 };
		this.last = last;
	
	}

	@Override
	public ArrayList<String> names() {
	
		ArrayList<String> names = new ArrayList<String>(11);

		names.add("*1");
		names.add("*2");
		names.add("*3");
		names.add("*4");
		names.add("*5");
		names.add("*6");
		names.add("*7");
		names.add("*8");
		names.add("+9");
		names.add("+10");
		names.add("+11");
		names.add("+12");
		names.add("+13");
		names.add("+14");
		names.add("*15");
		names.add("*16");
		names.add("*17");
		names.add("*18");
		names.add("+19");
		names.add("+20");
		names.add("*21");
		names.add("*22");
		names.add("*23");
		names.add("*24");
		names.add("+25");
		names.add("+26");
		names.add("+27");
		names.add("+28");

		return names;
	}

	@Override
	public ArrayList<String> namesPipeline() {

		ArrayList<String> names = new ArrayList<String>(11);

		names.add("*1");
		names.add("*2");
		names.add("*3");
		names.add("*4");
		names.add("*5");
		names.add("*6");
		names.add("*7");
		names.add("*8");
		names.add("+9");
		names.add("+10");
		names.add("+11");
		names.add("+12");
		names.add("+13");
		names.add("+14");
		names.add("*15");
		names.add("*16");
		names.add("*17");
		names.add("*18");
		names.add("+19");
		names.add("+20");
		names.add("*21");
		names.add("*22");
		names.add("*23");
		names.add("*24");
		names.add("+25");
		names.add("+26");
		names.add("+27");
		names.add("+28");

		names.add("*1a");
		names.add("*2a");
		names.add("*3a");
		names.add("*4a");
		names.add("*5a");
		names.add("*6a");
		names.add("*7a");
		names.add("*8a");
		names.add("+9a");
		names.add("+10a");
		names.add("+11a");
		names.add("+12a");
		names.add("+13a");
		names.add("+14a");
		names.add("*15a");
		names.add("*16a");
		names.add("*17a");
		names.add("*18a");
		names.add("+19a");
		names.add("+20a");
		names.add("*21a");
		names.add("*22a");
		names.add("*23a");
		names.add("*24a");
		names.add("+25a");
		names.add("+26a");
		names.add("+27a");
		names.add("+28a");

		names.add("*1b");
		names.add("*2b");
		names.add("*3b");
		names.add("*4b");
		names.add("*5b");
		names.add("*6b");
		names.add("*7b");
		names.add("*8b");
		names.add("+9b");
		names.add("+10b");
		names.add("+11b");
		names.add("+12b");
		names.add("+13b");
		names.add("+14b");
		names.add("*15b");
		names.add("*16b");
		names.add("*17b");
		names.add("*18b");
		names.add("+19b");
		names.add("+20b");
		names.add("*21b");
		names.add("*22b");
		names.add("*23b");
		names.add("*24b");
		names.add("+25b");
		names.add("+26b");
		names.add("+27b");
		names.add("+28b");

		return names;
	}
}
