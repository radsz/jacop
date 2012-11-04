/**
 *  StonesOfHeaven.java 
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
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * It solves a simple logic puzzle about artifacts. 
 * 
 * @author Janusz Kociolek, Sebastian Czypek, and Radoslaw Szymanek
 * 
 * Title: Stones of Heaven
 * Author: Jo Mason
 * Publication: Dell Logic Puzzles
 * Issue: April, 1998
 * Page: 13
 *
 * Wan Li, a dealer in Chinese antiques and artifacts, had an excellent
 * month recently when he made sales to four customers from around the
 * world -- Finland, Italy, Japan, and the United States -- who were
 * willing and able to pay very good prices. The four items were rare
 * jade figurines (a belt buckle, dragon, grasshopper, and horse), each
 * carved from a different color of jade (dark green, light green, red,
 * and white). Each piece dates from a different Chinese dynasty (Ching,
 * Ming, Sung, and Tang). Can you match each figurine with its color and
 * dynasty, and give the home country of each buyer?
 *
 *
 * 1. The rare white dragon (which the American didn't buy) didn't come
 * from the Sung dynasty.
 *
 * 2. The exquisite belt buckle (which wasn't any shade of green) was
 * created in 618 A.D. for an emperor of the Tang dynasty.
 *
 * 3. Three of the figurines were the one bought by the Finn (which
 * wasn't the dragon), the one from the Ching dynasty (which didn't go
 * to the buyer from Japan), and the light green object (which wasn't
 * the horse).
 * 
 * 4. The American decided against both the grasshopper and the piece
 * from the Sung dynasty, neither of which she felt would match her
 * home decor.
 *
 *
 * Belt buckle, red, Tang, U.S
 * Dragon, white, Ching, Italy
 * Grasshopper, light green, Ming, Japan
 * Horse, dark green, Sung, Finland
 *
 */

public class StonesOfHeaven extends ExampleFD {

	@Override
	public void model() {
		
		store = new Store();
		vars = new ArrayList<IntVar>();
		
		System.out.println("Solution for problem Stones of Heaven");

		String[] ColorNames = { "red", "light green", "white", "dark green" };
		int /* ired = 0, */ iLgreen = 1, iwhite = 2, iDgreen = 3;

		String[] CountryNames = { "USA", "Finland", "Japan", "Italy" };
		int iusa = 0, ifin = 1, ijapan = 2 /*, iitaly = 3 */ ;

		String[] ItemNames = { "belt buckle", "dragon", "grasshopper", "horse" };
		int ibelt = 0, idragon = 1, igrasshopper = 2, ihorse = 3;

		String[] DynastyNames = { "Ching", "Ming", "Sung", "Tang" };
		int iChing = 0, /* iMing = 1, */ iSung = 2, iTang = 3;

		IntVar Color[] = new IntVar[4];
		IntVar Country[] = new IntVar[4];
		IntVar Item[] = new IntVar[4];
		IntVar Dynasty[] = new IntVar[4];

		for (int i = 0; i < 4; i++) {
			Color[i] = new IntVar(store, ColorNames[i], 1, 4);
			Country[i] = new IntVar(store, CountryNames[i], 1, 4);
			Item[i] = new IntVar(store, ItemNames[i], 1, 4);
			Dynasty[i] = new IntVar(store, DynastyNames[i], 1, 4);
			vars.add(Color[i]); vars.add(Country[i]); vars.add(Item[i]); vars.add(Dynasty[i]);
		}

		store.impose(new Alldifferent(Color));
		store.impose(new Alldifferent(Country));
		store.impose(new Alldifferent(Item));
		store.impose(new Alldifferent(Dynasty));

		// 1. The rare white dragon (which the American didn't buy) didn't come
		// from the Sung dynasty.

		store.impose(new XeqY(Color[iwhite], Item[idragon]));
		store.impose(new XneqY(Dynasty[iSung], Item[idragon]));
		store.impose(new XneqY(Country[iusa], Item[idragon]));

		// 2. The exquisite belt buckle (which wasn't any shade of green) was
		// created in 618 A.D. for an emperor of the Tang dynasty.

		store.impose(new XneqY(Item[ibelt], Color[iLgreen]));
		store.impose(new XneqY(Item[ibelt], Color[iDgreen]));
		store.impose(new XeqY(Item[ibelt], Dynasty[iTang]));

		// 3. Three of the figurines were the one bought by the Finn (which
		// wasn't the dragon), the one from the Ching dynasty (which didn't go
		// to the buyer from Japan), and the light green object (which wasn't
		// the horse).
		store.impose(new XneqY(Country[ifin], Item[idragon]));
		store.impose(new XneqY(Country[ifin], Dynasty[iChing]));
		store.impose(new XneqY(Country[ifin], Color[iLgreen]));

		store.impose(new XneqY(Dynasty[iChing], Country[ijapan]));
		store.impose(new XneqY(Dynasty[iChing], Color[iLgreen]));

		store.impose(new XneqY(Color[iLgreen], Item[ihorse]));

		// 4. The American decided against both the grasshopper and the piece
		// from the Sung dynasty, neither of which she felt would match her
		// home decor.
		store.impose(new XneqY(Country[iusa], Item[igrasshopper]));
		store.impose(new XneqY(Country[iusa], Dynasty[iSung]));

		store.impose(new XneqY(Item[igrasshopper], Dynasty[iSung]));
	
	}

	/**
	 * It executes a simple program to solve this logic puzzle.
	 * @param args
	 */
	public static void main(String args[]) {

		StonesOfHeaven example = new StonesOfHeaven();
		
		example.model();

		if (example.search())
			System.out.println("Solution(s) found");
		
	}		
		
}
