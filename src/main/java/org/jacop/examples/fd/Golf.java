/**
 *  Golf.java 
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
import org.jacop.constraints.And;
import org.jacop.constraints.Element;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XltC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * A simple logic puzzle about golf players. 
 * 
 * @author Mariusz Czarnojan, Krystian Burka, and Radoslaw Szymanek
 *
 * "A Round of Golf"

 * When the Sunny Hills Country Club golf course isn't in use by club members,
 * of course, it's open to the club's employees. 
 * Recently, Jack and three other workers at the golf course got together on their day 
 * off to play a round of eighteen holes of golf. 
 * Afterward, all four, including Mr. Green, went to the clubhouse to total their scorecards. 
 * Each man works at a different job (one is a short-order cook), and each shot a different score
 * in the game. No one scored below 70 or above 85 strokes.
 * From the clues below, can you discover each man's full name, job and golf score? 
 * 
 * 1. Bill, who is not the maintenance man, plays golf often and had the lowest score of the foursome.
 * 2. Mr. Clubb, who isn't Paul, hit several balls into the woods and scored ten strokes
 *    more than the pro-shop clerk.
 * 3. In some order, Frank and the caddy scored four and seven more strokes than Mr. Sands. 
 * 4. Mr. Carter thought his score of 78 was one of his better games, even though Frank's score
 *    was lower.
 * 5. None of the four scored exactly 81 strokes.
 * 
 * Solution
 * Bill Sands Cook 71
 * Jack Clubb Maint 85
 * Paul Carter Caddy 78
 * Frank Green Clerk 75
 */


public class Golf extends ExampleFD {

	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		
		System.out.println("Program to solve Golf problem ");

		// First names of golf players.
		String[] FNNames = { "Bill", "Paul", "Frank", "Jack" };
		// Creation of indexes for ease of referring.
		int iBill = 0, iPaul = 1, iFrank = 2, iJack = 3;

		// Last names of golf players.
		String[] LNNames = { "Clubb", "Carter", "Sands", "Green" };
		// Creation of indexes for ease of referring.
		int /* iGreen = 0, */ iClubb = 1, iCarter = 2, iSands = 3;
		
		// Jobs of the golf players.
		String[] JobsNames = { "Maint", "Caddy", "Clerk", "Cook" };
		// Creation of indexes for ease of referring.
		int iMaint = 0, iCaddy = 1, iClerk = 2 /*, iCook = 3 */ ;

		// FDV's arrays
		IntVar FN[] = new IntVar[4];
		IntVar LN[] = new IntVar[4];
		IntVar Jobs[] = new IntVar[4];

		// Creating all FDVs.
		for (int i = 0; i < 4; i++) {
			// Domains are given through use of the function addDom.
			// Value 81 is not included due to clue no. 5.
			// Bounds 70 and 85 are derived from the problem description.
			FN[i] = new IntVar(store, FNNames[i]);
			FN[i].addDom(70, 80);
			FN[i].addDom(82, 85);

			LN[i] = new IntVar(store, LNNames[i]);
			LN[i].addDom(70, 80);
			LN[i].addDom(82, 85);

			Jobs[i] = new IntVar(store, JobsNames[i]);
			Jobs[i].addDom(70, 80);
			Jobs[i].addDom(82, 85);
			
			vars.add(FN[i]); vars.add(LN[i]); vars.add(Jobs[i]);
		}

		// Each player (firstname, lastname, job) has a different score.
		store.impose(new Alldifferent(FN));
		store.impose(new Alldifferent(LN));
		store.impose(new Alldifferent(Jobs));

		// 1. Bill, who is not the maintenance man, plays golf often and had the
		// lowest score of the foursome.

		store.impose(new XneqY(FN[iBill], Jobs[iMaint]));
		store.impose(new XltY(FN[iBill], FN[iPaul]));
		store.impose(new XltY(FN[iBill], FN[iFrank]));
		store.impose(new XltY(FN[iBill], FN[iJack]));

		// 2. Mr. Clubb, who isn't Paul, hit several balls into the woods and
		// scored ten strokes
		// more than the pro-shop clerk.

		store.impose(new XneqY(LN[iClubb], FN[iPaul]));
		store.impose(new XplusCeqZ(Jobs[iClerk], 10, LN[iClubb]));

		// 3. In some order, Frank and the caddy scored four and seven more
		// strokes than Mr. Sands.
		PrimitiveConstraint[] c1 = { new XplusCeqZ(LN[iSands], 4, FN[iFrank]),
				new XplusCeqZ(LN[iSands], 7, Jobs[iCaddy]) };
		PrimitiveConstraint[] c2 = { new XplusCeqZ(LN[iSands], 7, FN[iFrank]),
				new XplusCeqZ(LN[iSands], 4, Jobs[iCaddy]) };

		store.impose(new Or(new And(c1), new And(c2)));

		// 4. Mr. Carter thought his score of 78 was one of his better games,
		// even though Frank's score was lower.

		store.impose(new XeqC(LN[iCarter], 78));
		store.impose(new XltY(FN[iFrank], LN[iCarter]));
		store.impose(new XltC(FN[iFrank], 78));

		// 5. None of the four scored exactly 81 strokes.
		// It is redundant as these unary constraints have been already taken
		// into account during
		// domain creation process.
		store.impose(new XneqC(FN[iBill], 81));
		store.impose(new XneqC(FN[iPaul], 81));
		store.impose(new XneqC(FN[iFrank], 81));
		store.impose(new XneqC(FN[iJack], 81));
		store.impose(new XneqY(FN[iPaul], LN[iClubb]));

		// Every ith variable in LN must have a coresponding variable in FN.
		// Every ith variable in Jobs must have a coresponding variable in FN.
		// Important as size of the domain variables is larger than the number
		// of variables
		// and Alldifferent is not sufficient.
		for (int i = 0; i < 4; i++) {
			IntVar el1 = new IntVar(store, "i" + i + "LN", 1, 4);
			IntVar el2 = new IntVar(store, "i" + i + "Jobs", 1, 4);

			store.impose(new Element(el1, LN, FN[i]));
			store.impose(new Element(el2, Jobs, FN[i]));
		}

	}

	/**
	 * It executes a simple program to solve this logic puzzle.
	 * @param args no arguments is used.
	 */
	public static void main(String args[]) {

		Golf example = new Golf();
		
		example.model();

		if (example.search())
			System.out.println("Solution(s) found");
		
	}		
	
}
