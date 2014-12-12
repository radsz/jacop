/**
 *  Tunapalooza.java 
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
import org.jacop.constraints.Or;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Sum;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * It solves a simple logic puzzle about music concert. 
 * 
 * @author Lesniak Kamil, Harezlak Roman, Radoslaw Szymanek
 * @version 4.2
 * 
 * Tim and Keri have a full day ahead for themselves as they plan to see
 * and hear everything at Tunapalooza '98, the annual save-the-tuna
 * benefit concert in their hometown. To cover the most ground, they
 * will have to split up.  They have arranged to meet during four rock
 * band acts (Ellyfish, Korrupt, Retread Ed and the Flat Tires, and
 * Yellow Reef) at planned rendezvous points (carnival games,
 * information booth, mosh pit, or T-shirt vendor).  Can you help match
 * each band name with the type of music they play (country, grunge,
 * reggae, or speed metal) and Tim and Kerri's prearranged meeting spot
 * while they play?
 * 
 * 1. Korrupt isn't a country or grunge music band. 
 * 
 * 2. Tim and Kerri won't meet at the carnival games during Ellyfish's performance.
 *
 * 3. The pair won't meet at the T-shirt vendor during the reggae band's show.
 *
 * 4. Exactly two of the following three statements are true:
 * a) Ellyfish plays grunge music.
 * b) Tim and Kerri won't meet at the information booth during a performance by Retread Ed and the Flat Tires.
 * c) The two friends won't meet at the T-shirt vendor while Yellow Reef is playing.
 *
 * 5. The country and speed metal acts are, in some order, Retread Ed and the Flat Tires 
 * and the act during which Tim and Kerri will meet at the mosh pit.
 *
 * 6. The reggae band is neither Korrupt nor the act during which Tim and 
 * Kerri will meet at the information booth.
 *
 * Determine: Band name -- Music type -- Meeting place
 *
 * Given solution : 
 *
 * 1 Ellyfish, grunge,  vendor
 * 2 Korrupt,  metal,   mosh
 * 3 Retread,  country, information 
 * 4 Yellow ,  reggae,  carnival
 * 
 */

public class Tunapalooza extends ExampleFD {

	@Override
	public void model() {

		// Creating constraint store
		store = new Store();
		vars = new ArrayList<IntVar>();
		
		// names
		int Ellyfish = 1, Korrupt = 2, Retread = 3, Yellow = 4;

		// types
		IntVar country = new IntVar(store, "country", 1, 4);
		IntVar grunge = new IntVar(store, "grunge", 1, 4);
		IntVar reggae = new IntVar(store, "reggae", 1, 4);
		IntVar metal = new IntVar(store, "metal", 1, 4);
		// places
		IntVar carnival = new IntVar(store, "carnival", 1, 4);
		IntVar information = new IntVar(store, "information", 1, 4);
		IntVar mosh = new IntVar(store, "mosh", 1, 4);
		IntVar vendor = new IntVar(store, "vendor", 1, 4);

		// arrays of variables
		IntVar types[] = { country, grunge, reggae, metal };
		IntVar places[] = { carnival, information, mosh, vendor };

		for (IntVar v : types)
			vars.add(v);
		for (IntVar v : places)
			vars.add(v);
		
		// All types and places have to be associated with different band.
		store.impose(new Alldifferent(types));
		store.impose(new Alldifferent(places));

		// 1. Korrupt isn't a country or grunge music band.

		store.impose(new And(new XneqC(country, Korrupt), new XneqC(grunge,
				Korrupt)));

		// 2. Tim and Kerri won't meet at the carnival games during Ellyfish's
		// performance.

		store.impose(new XneqC(carnival, Ellyfish));

		// 3. The pair won't meet at the T-shirt vendor during the reggae band's
		// show.

		store.impose(new XneqY(vendor, reggae));

		// 4. Exactly two of the following three statements are true:
		// a) Ellyfish plays grunge music.
		// b) Tim and Kerri won't meet at the information booth during a
		// performance by Retread Ed and the Flat Tires.
		// c) The two friends won't meet at the T-shirt vendor while Yellow Reef
		// is playing.

		IntVar statement1 = new IntVar(store, "s1", 0, 1);
		IntVar statement2 = new IntVar(store, "s2", 0, 1);
		IntVar statement3 = new IntVar(store, "s3", 0, 1);

		store.impose(new Reified(new XeqC(grunge, Ellyfish), statement1));
		store.impose(new Reified(new XneqC(information, Retread), statement2));
		store.impose(new Reified(new XneqC(vendor, Yellow), statement3));

		IntVar two = new IntVar(store, "2", 2, 2);
		IntVar sum[] = { statement1, statement2, statement3 };
		store.impose(new Sum(sum, two));

		for (IntVar v : sum)
			vars.add(v);
		
		// 5. The country and speed metal acts are, in some order, Retread Ed
		// and the Flat Tires
		// and the act during which Tim and Kerri will meet at the mosh pit.

		store.impose(new Or(new XeqY(country, mosh), new XeqY(metal, mosh)));
		store.impose(new Or(new XeqC(country, Retread),
				new XeqC(metal, Retread)));
		store.impose(new XneqC(mosh, Retread));

		// 6. The reggae band is neither Korrupt nor the act during which Tim
		// and
		// Kerri will meet at the information booth.

		store.impose(new XneqC(reggae, Korrupt));
		store.imposeWithConsistency(new XneqY(reggae, information));

	}
		
	/**
	 * It executes the program to solve this simple logic puzzle.
	 * @param args no arguments are used.
	 */
	public static void main(String args[]) {

		Tunapalooza example = new Tunapalooza();
		
		example.model();

		if (example.searchMostConstrainedStatic())
			System.out.println("Solution(s) found");
		
	}		
	
}
