/**
 *  Conference.java 
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

package org.jacop.examples.fd;

import java.util.ArrayList;

import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.Cumulative;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * It solves a simple conference session placement problem.
 * 
 * @author Radoslaw Szymanek
 * 
 * It solves a simple conference example problem, where different sessions 
 * must be scheduled according to the specified constraints.
 *
 */

public class Conference extends ExampleFD {

	@Override
	public void model() {

		// Creating constraint store
		store = new Store();
		vars = new ArrayList<IntVar>();
		
		// session letter
		// A, B, C, D, E, F, G, H, I, J, K
		// session index number
		// 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10
		int iA = 0, iB = 1, iC = 2, iD = 3, iE = 4, iF = 5;
		int iG = 6, iH = 7, iI = 8, iJ = 9, iK = 10;

		IntVar[] sessions = new IntVar[11];

		for (int i = 0; i < 11; i++) {
			sessions[i] = new IntVar(store, "session[" + i + "]", 1, 4);
			vars.add(sessions[i]);
		}

		// Imposing inequalities constraints between sessions

		// A != J
		store.impose(new XneqY(sessions[iA], sessions[iJ]));
		// I != J
		store.impose(new XneqY(sessions[iI], sessions[iJ]));
		// E != I
		store.impose(new XneqY(sessions[iE], sessions[iI]));
		// C != F
		store.impose(new XneqY(sessions[iC], sessions[iF]));
		// F != G
		store.impose(new XneqY(sessions[iF], sessions[iG]));
		// D != H
		store.impose(new XneqY(sessions[iD], sessions[iH]));
		// B != D
		store.impose(new XneqY(sessions[iB], sessions[iD]));
		// E != K
		store.impose(new XneqY(sessions[iE], sessions[iK]));

		IntVar[] temp = new IntVar[4];
		// different times - B, G, H, I
		temp[0] = sessions[iB];
		temp[1] = sessions[iG];
		temp[2] = sessions[iH];
		temp[3] = sessions[iI];
		store.impose(new Alldifferent(temp));
		// different times - A, B, C, H
		temp[0] = sessions[iA];
		temp[1] = sessions[iB];
		temp[2] = sessions[iC];
		temp[3] = sessions[iH];
		store.impose(new Alldifferent(temp));

		temp = new IntVar[3];
		// different times - A, E, G
		temp[0] = sessions[iA];
		temp[1] = sessions[iE];
		temp[2] = sessions[iG];
		store.impose(new Alldifferent(temp));

		// different times - B, H, K
		temp[0] = sessions[iB];
		temp[1] = sessions[iH];
		temp[2] = sessions[iK];
		store.impose(new Alldifferent(temp));

		// different times - D, F, J
		temp[0] = sessions[iD];
		temp[1] = sessions[iF];
		temp[2] = sessions[iJ];
		store.impose(new Alldifferent(temp));

		// sessions precedence

		// E < J, D < K, F < K
		store.impose(new XltY(sessions[iE], sessions[iJ]));
		store.impose(new XltY(sessions[iD], sessions[iK]));
		store.impose(new XltY(sessions[iF], sessions[iK]));

		// session assignment
		store.impose(new XeqC(sessions[iA], 1));
		store.impose(new XeqC(sessions[iJ], 4));

		// There are 3 sessions per half a day, last hald a day only 2
		// Every half a day is a resource of capacity 3, and session J which
		// is assigned the last half a day has a resource requirement 2, others
		// 1.

		IntVar one = new IntVar(store, "one", 1, 1);
		IntVar two = new IntVar(store, "two", 2, 2);
		IntVar three = new IntVar(store, "three", 3, 3);

		IntVar[] durations = new IntVar[11];
		for (int d = 0; d < 11; d++)
			durations[d] = one;

		IntVar[] resources = new IntVar[11];
		for (int r = 0; r < 11; r++)
			resources[r] = one;

		resources[iJ] = two;

		// last parameter true enforces edge finding propagation algorithm
		store.impose(new Cumulative(sessions, durations, resources, three,
						true, true));

	}
			
	
	
	/**
	 * It executes the program which solves this simple problem.
	 * @param args no arguments are read.
	 */
	public static void main(String args[]) {

		Conference example = new Conference();
		
		example.model();

		if (example.searchAllAtOnce())
			System.out.println("Solution(s) found");
		
	}			

}
