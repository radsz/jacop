/**
 *  DCT.java 
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
 * It specifies DCT benchmark.
 * 
 * Source:
 * 
 * Nestor, J.A.; Krishnamoorthy, G.; "SALSA: a new approach to scheduling with
 * timing constraints" IEEE Transactions on Computer-Aided Design of Integrated
 * Circuits and Systems, Volume 12, Issue 8, Aug. 1993 Page(s):1107 - 1122
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class DCT extends Filter {

	/**
	 * It constructs a DCT filter problem with default delays for 
	 */
	public DCT() {
		this(1, 2);
	}

	/**
	 * It constructs a DCT filter with specific delays for 
	 * addition and multiplication operation.
	 * 
	 * @param addDel delay of the addition operation.
	 * @param mulDel delay of the multiplication operation.
	 */
	public DCT(int addDel, int mulDel) {
		
		this.addDel = addDel;
		this.mulDel = mulDel;
		
		name = "DCT";

		int dependencies[][] = { { 0, 8 }, { 0, 16 }, { 0, 17 }, { 1, 8 },
				{ 1, 19 }, { 1, 20 }, { 2, 9 }, { 2, 22 }, { 2, 23 }, { 3, 9 },
				{ 3, 25 }, { 3, 26 }, { 4, 10 }, { 4, 11 }, { 5, 10 }, { 5, 11 },
				{ 6, 12 }, { 6, 13 }, { 7, 12 }, { 7, 13 }, { 8, 14 }, { 8, 18 },
				{ 9, 14 }, { 9, 24 }, { 10, 27 }, { 11, 15 }, { 11, 29 },
				{ 12, 28 }, { 13, 15 }, { 13, 31 }, { 14, 21 }, { 15, 30 },
				{ 16, 32 }, { 17, 38 }, { 18, 32 }, { 18, 34 }, { 19, 34 },
				{ 20, 36 }, { 21, 33 }, { 21, 35 }, { 21, 36 }, { 21, 38 },
				{ 22, 35 }, { 23, 37 }, { 24, 37 }, { 24, 39 }, { 25, 33 },
				{ 26, 39 }, { 27, 44 }, { 27, 45 }, { 28, 44 }, { 28, 45 },
				{ 29, 46 }, { 30, 46 }, { 30, 47 }, { 31, 47 }, { 32, 40 },
				{ 33, 40 }, { 34, 41 }, { 35, 41 }, { 36, 42 }, { 37, 42 },
				{ 38, 43 }, { 39, 43 } };

		this.dependencies = dependencies;
		
		int ids[] = { addId, addId, addId, addId, addId, addId, addId, addId,
				addId, addId, addId, addId, addId, addId, addId, addId, mulId,
				mulId, mulId, mulId, mulId, mulId, mulId, mulId, mulId, mulId,
				mulId, mulId, mulId, mulId, mulId, mulId, addId, addId, addId,
				addId, addId, addId, addId, addId, addId, addId, addId, addId,
				addId, addId, addId, addId };

		this.ids = ids;
		
		int last[] = { 40, 41, 42, 43, 44, 45, 46, 47 };
		this.last = last;
	}

	@Override
	public ArrayList<String> names() {
		ArrayList<String> names = new ArrayList<String>(48);

		names.add("-1");
		names.add("-2");
		names.add("-3");
		names.add("-4");
		names.add("+5");
		names.add("+6");
		names.add("+7");
		names.add("+8");
		names.add("+9");
		names.add("+10");
		names.add("+11");
		names.add("-12");
		names.add("+13");
		names.add("-14");
		names.add("+15");
		names.add("+16");
		names.add("*17");
		names.add("*18");
		names.add("*19");
		names.add("*20");
		names.add("*21");
		names.add("*22");
		names.add("*23");
		names.add("*24");
		names.add("*25");
		names.add("*26");
		names.add("*27");
		names.add("*28");
		names.add("*29");
		names.add("*30");
		names.add("*31");
		names.add("*32");
		names.add("+33");
		names.add("+34");
		names.add("+35");
		names.add("+36");
		names.add("+37");
		names.add("+38");
		names.add("+39");
		names.add("+40");
		names.add("+41");
		names.add("+42");
		names.add("+43");
		names.add("+44");
		names.add("-45");
		names.add("+46");
		names.add("+47");
		names.add("+48");

		return names;
	}

	@Override
	public ArrayList<String> namesPipeline() {
		ArrayList<String> names = new ArrayList<String>(48);

		names.add("-1");
		names.add("-2");
		names.add("-3");
		names.add("-4");
		names.add("+5");
		names.add("+6");
		names.add("+7");
		names.add("+8");
		names.add("+9");
		names.add("+10");
		names.add("+11");
		names.add("-12");
		names.add("+13");
		names.add("-14");
		names.add("+15");
		names.add("+16");
		names.add("*17");
		names.add("*18");
		names.add("*19");
		names.add("*20");
		names.add("*21");
		names.add("*22");
		names.add("*23");
		names.add("*24");
		names.add("*25");
		names.add("*26");
		names.add("*27");
		names.add("*28");
		names.add("*29");
		names.add("*30");
		names.add("*31");
		names.add("*32");
		names.add("+33");
		names.add("+34");
		names.add("+35");
		names.add("+36");
		names.add("+37");
		names.add("+38");
		names.add("+39");
		names.add("+40");
		names.add("+41");
		names.add("+42");
		names.add("+43");
		names.add("+44");
		names.add("-45");
		names.add("+46");
		names.add("+47");
		names.add("+48");

		names.add("-1a");
		names.add("-2a");
		names.add("-3a");
		names.add("-4a");
		names.add("+5a");
		names.add("+6a");
		names.add("+7a");
		names.add("+8a");
		names.add("+9a");
		names.add("+10a");
		names.add("+11a");
		names.add("-12a");
		names.add("+13a");
		names.add("-14a");
		names.add("+15a");
		names.add("+16a");
		names.add("*17a");
		names.add("*18a");
		names.add("*19a");
		names.add("*20a");
		names.add("*21a");
		names.add("*22a");
		names.add("*23a");
		names.add("*24a");
		names.add("*25a");
		names.add("*26a");
		names.add("*27a");
		names.add("*28a");
		names.add("*29a");
		names.add("*30a");
		names.add("*31a");
		names.add("*32a");
		names.add("+33a");
		names.add("+34a");
		names.add("+35a");
		names.add("+36a");
		names.add("+37a");
		names.add("+38a");
		names.add("+39a");
		names.add("+40a");
		names.add("+41a");
		names.add("+42a");
		names.add("+43a");
		names.add("+44a");
		names.add("-45a");
		names.add("+46a");
		names.add("+47a");
		names.add("+48a");

		names.add("-1b");
		names.add("-2b");
		names.add("-3b");
		names.add("-4b");
		names.add("+5b");
		names.add("+6b");
		names.add("+7b");
		names.add("+8b");
		names.add("+9b");
		names.add("+10b");
		names.add("+11b");
		names.add("-12b");
		names.add("+13b");
		names.add("-14b");
		names.add("+15b");
		names.add("+16b");
		names.add("*17b");
		names.add("*18b");
		names.add("*19b");
		names.add("*20b");
		names.add("*21b");
		names.add("*22b");
		names.add("*23b");
		names.add("*24b");
		names.add("*25b");
		names.add("*26b");
		names.add("*27b");
		names.add("*28b");
		names.add("*29b");
		names.add("*30b");
		names.add("*31b");
		names.add("*32b");
		names.add("+33b");
		names.add("+34b");
		names.add("+35b");
		names.add("+36b");
		names.add("+37b");
		names.add("+38b");
		names.add("+39b");
		names.add("+40b");
		names.add("+41b");
		names.add("+42b");
		names.add("+43b");
		names.add("+44b");
		names.add("-45b");
		names.add("+46b");
		names.add("+47b");
		names.add("+48b");

		return names;
	}
}
