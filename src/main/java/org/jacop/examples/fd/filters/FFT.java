/**
 *  FFT.java 
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
 * It specifies FFT benchmark.
 * 
 * Source: Naotaka Ohsawa, Masanori Hariyama and Michitaka Kameyama
 * "High-Performance Field Programmable VLSI Processor Based on a Direct
 * Allocation of a Control/Data Flow Graph" IEEE Computer Society Annual
 * Symposium on VLSI p. 0095
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class FFT extends Filter {

	/**
	 * It constructs a simple FFT filter.
	 */
	public FFT() {
		this(1, 2);
	}

	
	/**
	 * It constructs a FFT filter with the specified delay
	 * for the addition and multiplication operation.
	 * 
	 * @param addDel the delay of the addition operation.
	 * @param mulDel the delay of the multiplication operation.
	 */
	public FFT(int addDel, int mulDel) {
		
		this.addDel = addDel;
		this.mulDel = mulDel;
		
		name = "FFT";

		int dependencies[][] = { { 0, 4 }, { 1, 4 }, { 2, 5 }, { 3, 5 }, { 4, 6 },
				{ 4, 7 }, { 5, 8 }, { 5, 9 } };
		this.dependencies = dependencies;
		
		int ids[] = { mulId, mulId, mulId, mulId, addId, addId, addId, addId,
				addId, addId };
		this.ids = ids;
		
		int last[] = { 6, 7, 8, 9 };
		this.last = last;
	}

	@Override
	public ArrayList<String> names() {
		ArrayList<String> names = new ArrayList<String>(10);

		names.add("*1");
		names.add("*2");
		names.add("*3");
		names.add("*4");
		names.add("+5");
		names.add("+6");
		names.add("+7");
		names.add("+8");
		names.add("+9");
		names.add("+10");
		return names;
	}

	@Override
	public ArrayList<String> namesPipeline() {
		ArrayList<String> names = new ArrayList<String>(10);

		names.add("*1");
		names.add("*2");
		names.add("*3");
		names.add("*4");
		names.add("+5");
		names.add("+6");
		names.add("+7");
		names.add("+8");
		names.add("+9");
		names.add("+10");

		names.add("*1a");
		names.add("*2a");
		names.add("*3a");
		names.add("*4a");
		names.add("+5a");
		names.add("+6a");
		names.add("+7a");
		names.add("+8a");
		names.add("+9a");
		names.add("+10a");

		names.add("*1b");
		names.add("*2b");
		names.add("*3b");
		names.add("*4b");
		names.add("+5b");
		names.add("+6b");
		names.add("+7b");
		names.add("+8b");
		names.add("+9b");
		names.add("+10b");

		return names;
	}
}
