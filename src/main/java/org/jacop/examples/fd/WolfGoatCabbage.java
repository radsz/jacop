/**
 *  WolfGoatCabbage.java 
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

import org.jacop.constraints.ExtensionalSupportVA;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Sum;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * A simple logic problem of transporting wolf, goat, and cabbage over the river.  
 *
 * @author Radoslaw Szymanek
 * 
 * We need to transfer the cabbage, the goat and the wolf from one bank of the river to 
 * the other bank. But there is only one seat available on his boat !
 * 
 * Furthermore, if the goat and the cabbage stay together as we are leaving on a boat, 
 * the goat will eat the cabbage. And if the wolf and the goat stay together as we are leaving, 
 * the wolf will eat the goat !
 */

public class WolfGoatCabbage extends ExampleFD {

	/**
	 * It specifies number of moves allowed (one move is from one river bank to the other)
	 */
	public int numberInnerMoves = 1;
	
	@Override
	public void model() {
	
		System.out.println("Creating model for solution with " + numberInnerMoves
				+ " intermediate steps");
		// Creating constraint store
		store = new Store();
		vars = new ArrayList<IntVar>();
		
		IntVar left = new IntVar(store, "left", 0, 0);
		IntVar right = new IntVar(store, "right", 2, 2);

		IntVar[] wolf = new IntVar[2 + numberInnerMoves];
		IntVar[] goat = new IntVar[2 + numberInnerMoves];
		IntVar[] cabbage = new IntVar[2 + numberInnerMoves];

		wolf[0] = goat[0] = cabbage[0] = left;
		wolf[numberInnerMoves + 1] = goat[numberInnerMoves + 1] = cabbage[numberInnerMoves + 1] = right;

		for (int i = 1; i < numberInnerMoves + 1; i++) {

			wolf[i] = new IntVar(store, "wolfStateInMove" + i, 0, 2);
			goat[i] = new IntVar(store, "goatStateInMove" + i, 0, 2);
			cabbage[i] = new IntVar(store, "cabbageStateInMove" + i, 0, 2);

			vars.add(wolf[i]);
			vars.add(goat[i]);
			vars.add(cabbage[i]);
			
		}

		// {0, 1, 0}, any item was on left bank and end up on boat so boat
		// was on left bank too
		int[][] allowedTransitions = { { 0, 1, 0 }, { 1, 0, 0 },
				{ 2, 1, 2 }, { 1, 2, 2 }, { 0, 0, 0 }, { 0, 0, 2 },
				{ 2, 2, 0 }, { 2, 2, 2 } };

		for (int i = 0; i < numberInnerMoves + 1; i++) {

			IntVar[] temp = { wolf[i], wolf[i + 1], null };
			if (i % 2 == 0)
				temp[2] = left;
			else
				temp[2] = right;

			store
			.impose(new ExtensionalSupportVA(temp,
					allowedTransitions));

			temp[0] = goat[i];
			temp[1] = goat[i + 1];

			store
			.impose(new ExtensionalSupportVA(temp,
					allowedTransitions));

			temp[0] = cabbage[i];
			temp[1] = cabbage[i + 1];

			store
			.impose(new ExtensionalSupportVA(temp,
					allowedTransitions));
		}

		IntVar[] bw = new IntVar[numberInnerMoves];
		IntVar[] bg = new IntVar[numberInnerMoves];
		IntVar[] bc = new IntVar[numberInnerMoves];

		for (int i = 1; i < numberInnerMoves + 1; i++) {
			// at most one item on boat

			bw[i - 1] = new IntVar(store, "wolfOnBoatInMove" + i, 0, 1);
			bg[i - 1] = new IntVar(store, "goatOnBoatInMove" + i, 0, 1);
			bc[i - 1] = new IntVar(store, "cabbageOnBoatInMove" + i, 0, 1);

			store.impose(new Reified(new XeqC(wolf[i], 1), bw[i - 1]));
			store.impose(new Reified(new XeqC(goat[i], 1), bg[i - 1]));
			store.impose(new Reified(new XeqC(cabbage[i], 1), bc[i - 1]));

			IntVar[] b = { bw[i - 1], bg[i - 1], bc[i - 1] };

			IntVar numberOnBoat = new IntVar(store, "numberOnBoatInMove" + i, 0,
					1);
			store.impose(new Sum(b, numberOnBoat));

			store.impose(new XneqY(wolf[i], goat[i]));
			store.impose(new XneqY(goat[i], cabbage[i]));

		}

	}
	
	/**
	 * It executes a program which finds the optimal trip 
	 * and load of the boat between the river banks so all
	 * parties survive.
	 * 
	 * @param args no argument is used.
	 */
	public static void main(String args[]) {

		int numberInnerMoves = 1;
		boolean result = false;
		
		while (numberInnerMoves < 20 && !result) {

			WolfGoatCabbage example = new WolfGoatCabbage();
			example.numberInnerMoves = numberInnerMoves;
			
			example.model();
			
			if (!example.searchMostConstrainedStatic())
				System.out.println("No Solution(s) found for " + example.numberInnerMoves + " innermoves");
			else
				result = true;
				
			numberInnerMoves++;
		}
		
		
	}		
	
}
