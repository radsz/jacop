/**
 *  FourIslands.java 
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
import org.jacop.constraints.Element;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 *
 * It is a very simple puzzle about islands and bridges.
 *
 * @author Waldemar Sliwinski, Zdzislaw Zawada, and Radoslaw Szymanek
 *
 * A tiny nation in the South Pacific contains four islands connected by
 * bridges as shown (see below). Each of the four islands (Pwana, Quero,
 * Rayou, and Skern) boasts a different primary export (alabaster,
 * bananas, coconuts, and durian fruit) and a different tourist
 * attraction (hotel, ice skating rink, jai alai stadium, and koala
 * preserve). Can you find the name, export, and tourist attraction of
 * each island on the map?
 *
 *    N
 *  W   E     *compass directions
 *    S
 *
 * A, B, C, D are the islands
 *
 * (A) -- (B)
 *  |      |
 *  |      |
 * (C) -- (D)
 *
 * (view with non-proportional font)
 * 1. The island noted for its koala preserve is due south of Pwana.
 *
 * 2. The island with the largest alabaster quarry is due west of Quero.
 *
 * 3. The island with the resort hotel is due east of the one that exports durian fruit.
 *
 * 4. Skern and the island with the jai alai stadium are connected by a north-south bridge. 
 *
 * 5. Rayou and the island that exports bananas are connected by an east-west bridge.
 *
 * 6. The islands noted for the South Pacific's largest ice skating rink and for the jai alai stadium are not connected by a bridge.
 *
 * Determine: Island location -- Island name -- Export -- Tourist Attraction
 *
 * ANSWER:
 * Northwest, Pwana, durian fruit, ice skating rink
 * Northeast, Skern, coconuts, hotel
 * Southwest, Rayou, alabaster, koala preserve
 * Southeast, Quero, bananas, jai alai stadium
 *
 */

public class FourIslands extends ExampleFD {

	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		
		System.out.println("Program to solve Four Islands problem ");

		// names of islands
		String[] islandNames = { "Pwana", "Quero", "Rayou", "Skern" };
		int iPwana = 0, iQuero = 1, iRayou = 2, iSkern = 3;

		// names of exported goods
		String[] exportNames = { "alabaster", "bananas", "coconuts",
				"durian_fruit" };
		int iAlabaster = 0, iBananas = 1, /* iCoconuts = 2, */ iDurianFruit = 3;

		// names of attractions
		String[] attractionNames = { "hotel", "ice_skating_rink",
				"jai_alai_stadium", "koala_preserve" };
		int iHotel = 0, iIceSkating = 1, iJaiAlai = 2, iKoala = 3;

		// names of location
		String[] locationNames = { "northwest", "northeast", "southwest",
				"southeast" };
		int iNorthWest = 0, iNorthEast = 1, iSouthWest = 2, iSouthEast = 3;

		// arrays of variables
		IntVar island[] = new IntVar[4];
		IntVar export[] = new IntVar[4];
		IntVar attraction[] = new IntVar[4];
		IntVar location[] = new IntVar[4];

		for (int i = 0; i < 4; i++) {
			island[i] = new IntVar(store, islandNames[i], 0, 3);
			export[i] = new IntVar(store, exportNames[i], 0, 3);
			attraction[i] = new IntVar(store, attractionNames[i], 0, 3);
			location[i] = new IntVar(store, locationNames[i], 0, 3);
			vars.add(island[i]); vars.add(export[i]); 
			vars.add(attraction[i]); vars.add(location[i]);
		}

		store.impose(new Alldifferent(island));
		store.impose(new Alldifferent(export));
		store.impose(new Alldifferent(attraction));
		store.impose(new Alldifferent(location));

		// each map direction has an associated value
		store.impose(new XeqC(location[iNorthWest], 0));
		store.impose(new XeqC(location[iNorthEast], 1));
		store.impose(new XeqC(location[iSouthWest], 2));
		store.impose(new XeqC(location[iSouthEast], 3));

		// Clue no. 1. The island noted for its koala preserve is due
		// south of Pwana.

		store.impose(new XneqY(attraction[iKoala], location[iNorthWest]));
		store.impose(new XneqY(attraction[iKoala], location[iNorthEast]));
		// island pwana is not south.
		store.impose(new XneqY(island[iPwana], location[iSouthWest]));
		store.impose(new XneqY(island[iPwana], location[iSouthEast]));
		// based on values assigned two maps directions
		store.impose(new XplusCeqZ(island[iPwana], 2, attraction[iKoala]));

		// Clue no. 2. The island with the largest alabaster quarry is
		// due west of Quero.
		store.impose(new XneqY(island[iQuero], location[iNorthWest]));
		store.impose(new XneqY(island[iQuero], location[iSouthWest]));
		// alabaster is not east.
		store.impose(new XneqY(export[iAlabaster], location[iNorthEast]));
		store.impose(new XneqY(export[iAlabaster], location[iSouthEast]));
		// based on values assigned two maps directions
		store.impose(new XplusCeqZ(export[iAlabaster], 1, island[iQuero]));

		// Clue no. 3. The island with the resort hotel is due east of
		// the one that exports durian fruit.
		store.impose(new XneqY(attraction[iHotel], location[iNorthWest]));
		store.impose(new XneqY(attraction[iHotel], location[iSouthWest]));
		// durian fruit is not east.
		store.impose(new XneqY(export[iDurianFruit], location[iNorthEast]));
		store.impose(new XneqY(export[iDurianFruit], location[iSouthEast]));
		// based on values assigned two maps directions
		store.impose(new XplusCeqZ(export[iDurianFruit], 1,
						attraction[iHotel]));

		// Clue no. 4 Skern and the island with the jai alai stadium
		// are connected by a north-south bridge.

		// based on values assigned two maps directions
		// an array of possible values for an island skern
		int aSkern[] = { 0, 1, 2, 3 };
		// an array of possible values for jai alai stadium
		int aStadion[] = { 2, 3, 0, 1 };

		IntVar iI3 = new IntVar(store, "clue4", 1, 4);

		store.impose(new Element(iI3, aStadion, attraction[iJaiAlai]));
		store.impose(new Element(iI3, aSkern, island[iSkern]));

		// Clue no 5. Rayou and the island that exports bananas are
		// connected by an east-west bridge.

		// Similar to clue 4.
		int aBananas[] = { 0, 1, 2, 3 };
		int aRayou[] = { 1, 0, 3, 2 };

		IntVar iI2 = new IntVar(store, "clue5", 1, 4);

		store.impose(new Element(iI2, aBananas, export[iBananas]));
		store.impose(new Element(iI2, aRayou, island[iRayou]));

		// Clue no. 6. The islands noted for the South Pacific's
		// largest ice skating rink and for the jai alai stadium are
		// not connected by a bridge.

		// Similar to clue no 4.
		int aIceIsland[] = { 0, 1, 3, 2 };
		int aStadionIsland[] = { 3, 2, 0, 1 };

		IntVar iI = new IntVar(store, "clue6", 1, 4);

		store.impose(new Element(iI, aIceIsland, attraction[iIceSkating]));
		store.impose(new Element(iI, aStadionIsland, attraction[iJaiAlai]));
		
	}
	
	/**
	 * It executes a program to solve this simple logic puzzle.
	 * @param args no argument is used.
	 */
	public static void main(String args[]) {

		FourIslands example = new FourIslands();
		
		example.model();

		if (example.search())
			System.out.println("Solution(s) found");
		
	}	
	
	
}
