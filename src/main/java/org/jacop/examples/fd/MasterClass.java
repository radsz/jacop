/**
 *  MasterClass.java 
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
import org.jacop.constraints.Or;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
*
* It solves a logic puzzle about singing women.
*
* @author Zbigniew Danielczyk, Mariusz Jedrzejko, and Radoslaw Szymanek
*
* The great mezzo-soprano Flora Nebbiacorno has retired from the
* international opera stage, but she still teaches master classes
* regularly.  At a recent class, her five students were one soprano,
* one mezzo-soprano, two tenors, and one bass.  (The first two voice
* types are women's, and the last two are men's).  Their first names
* are Chris, J.P., Lee, Pat, and Val -- any of which could belong to a
* man or a woman - - and their last names are Kingsley, Robinson,
* Robinson (the two are unrelated but have the same last name), Ulrich,
* and Walker. Can you find the order in which these five sang for the
* class, identifying each by full name and voice type?
*
* 1. The first and second students were, in some order, Pat and the bass.
*
* 2. The second and third students included at least one tenor.
*
* 3. Kingsley and the fifth student (who isn't named Robinson) were, in
* some order, a mezzo-soprano and a tenor.
* 
* 4. Neither the third student, whose name is Robinson, nor Walker has
* the first name of Chris.
* 
* 5. Ulrich is not the bass or the mezzo-soprano.
*
* 6. Neither Lee or Val (who wasn't third) is a tenor.
*
* 7. J.P. wasn't third, and Chris wasn't fifth.
*
* 8. The bass isn't named Robinson.
*
* Determine: Order -- First name -- Last name -- Voice
*/

public class MasterClass extends ExampleFD {

	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		
		System.out.println("Solution to problem Master Class");

		// voice names
		String[] glos = { "mezzosoprano", "soprano", "bass", "tenor_1", "tenor_2" };

		// indexes for ease of referring
		int isopran = 0, imezzosoprano = 1, ibas = 2, itenor1 = 3, itenor2 = 4;

		// people's names
		String[] imie = { "Val", "JP", "Chris", "Lee", "Pat" };

		// indexes for ease of referring
		int iVal = 0, iJP = 1, iChris = 2, iLee = 3, iPat = 4;

		// people's surnames
		String[] nazwisko = { "Kisley", "Robinson_1", "Robinson_2", "Walker",
				"Urlich" };

		// indexes for ease of referring
		int iKinsley = 0, iRobinson1 = 1, iRobinson2 = 2, iWalker = 3, iUrlich = 4;

		// FDV's arrays

		IntVar zglos[] = new IntVar[5];
		IntVar zimie[] = new IntVar[5];
		IntVar znazwisko[] = new IntVar[5];

		// FDV creation
		for (int i = 0; i < 5; i++) {
			zglos[i] = new IntVar(store, glos[i], 1, 5);
			znazwisko[i] = new IntVar(store, nazwisko[i], 1, 5);
			zimie[i] = new IntVar(store, imie[i], 1, 5);
			vars.add(zglos[i]); vars.add(znazwisko[i]); vars.add(zimie[i]);
		}

		// Each variable must take a different value.
		store.impose(new Alldifferent(zglos));
		store.impose(new Alldifferent(zimie));
		store.impose(new Alldifferent(znazwisko));

		// 1. The first and second students were, in some order, Pat and the
		// bass.
		store.impose(new Or(new XeqC(zimie[iPat], 2), new XeqC(zglos[ibas],	2)));

		store.impose(new Or(new XeqC(zimie[iPat], 1), new XeqC(zglos[ibas],	1)));

		// Pat can not be bas, condition not taken care of by the above
		// formulation.
		store.impose(new XneqY(zimie[iPat], zglos[ibas]));

		// 2. The second and third students included at least one tenor.
		// Or constraint is used to deal with 2 tenors in the problem
		// description.
		// Possible to use since "at least one tenor".
		store.impose(new Or(new Or(new XeqC(zglos[itenor1], 2), 
								   new XeqC(zglos[itenor1], 3)),
							new Or(new XeqC(zglos[itenor2], 2),
								   new XeqC(zglos[itenor2], 3))));

		// 3. Kingsley and the fifth student (who isn't named
		// Robinson) were, in some order, a mezzo-soprano and a
		// tenor.

		store.impose(new XneqC(znazwisko[iRobinson1], 5));
		store.impose(new XneqC(znazwisko[iRobinson2], 5));
		store.impose(new XneqC(znazwisko[iKinsley], 5));

		store.impose(new Or(new Or(new XeqY(znazwisko[iKinsley], zglos[itenor1]), 
								   new XeqY(znazwisko[iKinsley], zglos[itenor2])), 
							new XeqY(znazwisko[iKinsley], zglos[isopran])));

		store.impose(new Or(new Or(new XeqC(zglos[itenor1], 5), 
								   new XeqC(zglos[itenor2], 5)),
						    new XeqC(zglos[isopran], 5)));

		// Neither the third student, whose name is Robinson, nor
		// Walker has the first name of Chris.

		store.impose(new XneqY(znazwisko[iWalker], zimie[iChris]));
		store.impose(new XneqY(znazwisko[iRobinson1], zimie[iChris]));
		store.impose(new XneqY(znazwisko[iRobinson2], zimie[iChris]));

		store.impose(new Or(new XeqC(znazwisko[iRobinson1], 3), 
							new XeqC(znazwisko[iRobinson2], 3)));

		// 5. Ulrich is not the bass or the mezzo-soprano.

		store.impose(new XneqY(zglos[imezzosoprano], znazwisko[iUrlich]));
		store.impose(new XneqY(zglos[ibas], znazwisko[iUrlich]));

		// 6. Neither Lee or Val (who wasn't third) is a tenor.

		store.impose(new XneqY(zglos[itenor1], zimie[iLee]));
		store.impose(new XneqY(zglos[itenor2], zimie[iLee]));

		store.impose(new XneqY(zglos[itenor1], zimie[iVal]));
		store.impose(new XneqY(zglos[itenor2], zimie[iVal]));

		store.impose(new XneqC(zimie[iVal], 3));

		// 7. J.P. wasn't third, and Chris wasn't fifth.

		store.impose(new XneqC(zimie[iJP], 3));
		store.impose(new XneqC(zimie[iChris], 5));

		// 8. The bass isn't named Robinson.

		store.impose(new XneqY(zglos[ibas], znazwisko[iRobinson1]));
		store.impose(new XneqY(zglos[ibas], znazwisko[iRobinson2]));

	}

	/**
	 * It executes the program to solve this simple logic puzzle.
	 * @param args no arguments is used.
	 */
	public static void main(String args[]) {

		MasterClass example = new MasterClass();
		
		example.model();

		if (example.search())
			System.out.println("Solution(s) found");
		
	}	
	
}
