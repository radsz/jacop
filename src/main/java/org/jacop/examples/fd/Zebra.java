/**
 *  Zebra.java 
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
import org.jacop.constraints.Eq;
import org.jacop.constraints.Not;
import org.jacop.constraints.Or;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * It models and solves Zebra logic puzzle.
 * 
 * @author Radoslaw Szymanek
 * 
 * It was given at The German Institute of Logical Thinking in Berlin, 1981. And 98% FAILED.
 *
 * Conditions
 *
 * 1. The Englishman lives in the red house. 
 * 2. The Spaniard owns a dog.
 * 3. The Japanese is a painter.
 * 4. The Italian drinks tea.
 * 5. The Norwegian lives in the first house on the left.
 * 6. The owner of the green house drinks coffee.
 * 7. The green house is on the right of the white one.
 * 8. The sculptor breeds snails.
 * 9. The diplomat lives in the yellow house.
 * 10. Milk is drunk in the middle house.
 * 11. The Norwegian's house is next to the blue one.
 * 12. The violinist drinks fruit juice.
 * 13. The fox is in a house next to that of the doctor.
 * 14. The horse is in a house next to that of the diplomat.
 * Q. Who owns a Zebra, and who drinks water?
 * 
 * They sometimes smoke different brands of cigarettes too, 
 * but that's apparently no longer politically correct, so they all quit. 
 */

public class Zebra extends ExampleFD {

	
	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		
		System.out.println("Program to solve Zebra problem ");

		String[] colorNames = { "red", "green", "white", "yellow", "blue" };
		int ired = 0, igreen = 1, iwhite = 2, iyellow = 3, iblue = 4;
		String[] nationalityNames = { "english", "spaniard", "japanese",
				"italian", "norwegian" };
		int ienglish = 0, ispaniard = 1, ijapanese = 2, iitalian = 3, inorwegian = 4;

		String[] petNames = { "dog", "snails", "fox", "horse", "zebra" };
		int idog = 0, isnails = 1, ifox = 2, ihorse = 3 /*, izebra = 4 */;
		String[] professionNames = { "painter", "sculptor", "diplomat",
				"violinist", "doctor" };
		int ipainter = 0, isculptor = 1, idiplomat = 2, iviolinist = 3, idoctor = 4;
		String[] drinkNames = { "tea", "coffee", "milk", "juice", "water" };
		int itea = 0, icoffee = 1, imilk = 2, ijuice = 3 /* , iwater = 4 */;

		IntVar color[] = new IntVar[5];
		IntVar nationality[] = new IntVar[5];
		IntVar drink[] = new IntVar[5];
		IntVar pet[] = new IntVar[5];
		IntVar profession[] = new IntVar[5];

		for (int i = 0; i < 5; i++) {
			color[i] = new IntVar(store, colorNames[i], 1, 5);
			pet[i] = new IntVar(store, petNames[i], 1, 5);
			drink[i] = new IntVar(store, drinkNames[i], 1, 5);
			nationality[i] = new IntVar(store, nationalityNames[i], 1, 5);
			profession[i] = new IntVar(store, professionNames[i], 1, 5);
			vars.add(color[i]); vars.add(nationality[i]); vars.add(pet[i]);
			vars.add(drink[i]); vars.add(profession[i]);
		}

		store.impose(new Alldifferent(color));
		store.impose(new Alldifferent(pet));
		store.impose(new Alldifferent(drink));
		store.impose(new Alldifferent(nationality));
		store.impose(new Alldifferent(profession));

		// S1 to S10
		store.impose(new XeqY(nationality[ienglish], color[ired]));
		store.impose(new XeqY(nationality[ispaniard], pet[idog]));
		store.impose(new XeqY(nationality[ijapanese], profession[ipainter]));
		store.impose(new XeqY(nationality[iitalian], drink[itea]));
		store.impose(new XeqC(nationality[inorwegian], 1));
		store.impose(new XeqY(color[igreen], drink[icoffee]));
		store.impose(new XplusCeqZ(color[iwhite], 1, color[igreen]));
		store.impose(new XeqY(profession[isculptor], pet[isnails]));
		store.impose(new XeqY(profession[idiplomat], color[iyellow]));
		store.impose(new XeqC(drink[imilk], 3));

		// S11
		store.impose(new XneqY(nationality[inorwegian], color[iblue]));

		store.impose(new Eq(new XplusCeqZ(nationality[inorwegian], 1,
				color[iblue]), new Not(new XplusCeqZ(color[iblue], 1,
				nationality[inorwegian]))));

		// Using reified constraints
		// FDV binary[] = new FDV[2];
		// binary[0] = new FDV(store, "binary1", 0, 1);
		// binary[1] = new FDV(store, "binary2", 0, 1);

		// store.impose(new Reified(new XplusCeqZ(nationality[inorwegian],
		// 1, color[iblue]),
		// binary[0]));

		// store.impose(new Reified(new XplusCeqZ(color[iblue], 1,
		// nationality[inorwegian]),
		// binary[1]));
		// store.impose(new XneqY(binary[0], binary[1]));

		// Using Or constraint
		// store.impose(new Or(new XplusCeqZ(nationality[inorwegian],
		// 1, color[iblue]),
		// new XplusCeqZ(color[iblue],
		// 1, nationality[inorwegian])));

		// S12
		store.impose(new XeqY(profession[iviolinist], drink[ijuice]));

		// S13
		store.impose(new XneqY(pet[ifox], profession[idoctor]));
		store.impose(new Or(new XplusCeqZ(pet[ifox], 1, profession[idoctor]),
				new XplusCeqZ(profession[idoctor], 1, pet[ifox])));

		// S14

		store.impose(new XneqY(pet[ihorse], profession[idiplomat]));
		// store.impose(new Or(new XplusCeqZ(pet[ihorse], 1,
		// profession[idiplomat]),
		// new XplusCeqZ(profession[idiplomat], 1,
		// pet[ihorse])));

		IntVar distance3 = new IntVar(store, "distance3", -1, 1);
		store.impose(new XplusYeqZ(distance3, pet[ihorse],
				profession[idiplomat]));

		vars.add(distance3);

	}
	
	
	/**
	 * It executes the program to solve this simple logic puzzle.
	 * 
	 * @param args no argument is used.
	 */
	public static void main(String args[]) {

		Zebra example = new Zebra();
		
		example.model();

		if (example.searchMostConstrainedStatic())
			System.out.println("Solution(s) found");
		
	}			
	
	
}
