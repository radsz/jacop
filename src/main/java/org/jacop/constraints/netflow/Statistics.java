/**
 *  Statistics.java 
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

package org.jacop.constraints.netflow;

import java.text.DecimalFormat;

/**
 *
 * This class stores all the statistics gather during the execution of the network flow constraint. 
 * 
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public class Statistics {
	
	private static final DecimalFormat DF = new DecimalFormat("0.###");

	public static int consistencyCalls = 0;
	public static int consistencyIterations = 0;
	public static final Statistics NVARS = new Statistics();
	public static final Statistics XVARS = new Statistics();
	public static final Statistics WVARS = new Statistics();
	public static final Statistics SVARS = new Statistics();

	public int arcsExamined = 0;
	public int arcsPruned = 0;
	public int amountPruned = 0;
	public long maxScoreSum = 0L;
	public long minScoreSum = 0L;
	
	private void toString(StringBuilder str) {
	
		str.append("\t# arcs examined : ");
		str.append(arcsExamined);
		str.append("\t(avg ");
		str.append(DF.format((double)arcsExamined / consistencyIterations));
		
		str.append(")\n\t# arcs pruned   : ");
		str.append(arcsPruned);
		str.append("\t(avg ");
		str.append(DF.format((double)arcsPruned / arcsExamined));
		
		str.append(")\n\tAmount pruned   : ");
		str.append(amountPruned);
		str.append("\t(avg ");
		str.append(DF.format((double)amountPruned / arcsPruned));
		
		str.append(")\n\tAvg max score   : ");
		str.append(DF.format((double)maxScoreSum / consistencyIterations));
		str.append("\n\tAvg min score   : ");
		str.append(DF.format((double)minScoreSum / consistencyIterations));
	
	}
	
	public String toString() {
	
		StringBuilder str = new StringBuilder();
		toString(str);
		return str.toString();
		
	}
	
	public static String asString() {
		
		StringBuilder str = new StringBuilder();

		str.append("# consistency calls      : ");
		str.append(consistencyCalls);
		
		str.append("\n# consistency iterations : ");
		str.append(consistencyIterations);
		str.append("\t(avg ");
		str.append(DF.format((double)consistencyIterations / consistencyCalls));
		str.append(")");
		
		if (NVARS.arcsExamined > 0) {
			str.append("\nFor X-variables GAC-pruning (node with degree <= 2)\n");
			NVARS.toString(str);
		}
		if (XVARS.arcsExamined > 0) {
			str.append("\nFor X-variables\n");
			XVARS.toString(str);
		}
		if (WVARS.arcsExamined > 0) {
			str.append("\nFor W-variables\n");
			WVARS.toString(str);
		}
		if (SVARS.arcsExamined > 0) {
			str.append("\nFor S-variables\n");
			SVARS.toString(str);
		}
		return str.toString();
	}
	
}
