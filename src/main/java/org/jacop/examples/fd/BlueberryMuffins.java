/**
 *  BlueberryMuffins.java 
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
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XgtY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * It solves a simple logic puzzle about blueberry muffins.
 * 
 * @author Radoslaw Szymanek
 * 
 *  Logic Puzzle: Blueberry Muffins
 *
 * Description :
 *
 * Daniel made a dozen blueberry muffins on Friday night -- and by
 * the timehe was ready for brunch on Saturday, there were only
 * two left. The other ten had been snitched by his housemates,
 * all of whom had gotten up early because they had to work on
 * Saturday. The fourhousemates include two men named Bill and
 * Mark, and two women named Calla and Lynn; last names are Ellis,
 * Ingham, Oakley, and Summers, and their differing professions
 * are dogcatcher, flautist, secretary, and zookeeper. Can you
 * discover each one's full name, profession, and number of
 * muffins snitched?

 * 1. Each housemate snitched a different number of muffins from one to four.
 * 2. Bill and Ellis snitched a total of six muffins.
 * 3. The secretary (who is a woman) snitched more than the dogcatcher.
 * 4. Mark snitched two more than Summers did.
 * 5. The flautist snitched twice as many as Ms. Oakley did.
 * 6. Calla's last name isn't Ingham.

 * Solution:

 * Calla Oakley dogcatcher 1 muffin
 * Bill Summers flautist 2 muffins
 * Lynn Ingham secretary 3 muffins
 * Mark Ellis zookeeper 4 muffins
 */


public class BlueberryMuffins extends ExampleFD {

	@Override
	public void model() {

		// Constraint store created below.

		store = new Store();
		vars = new ArrayList<IntVar>();
		
		System.out.println("Program to solve Blueberry Muffins ");

		// String arrays with peoples' names.

		String[] lastnames = { "Ellis", "Ingham", "Oakley", "Summers" };

		// Constant indexes to ease referring to variables denoting people.
		int iellis = 0, iingham = 1, ioakley = 2, isummer = 3;

		// String arrays with profession names.

		String[] professionNames = { "dogcatcher", "flautist", "secretary",
				"zookeeper" };

		// Constant indexes to ease referring to profession variables.

		int /* izookeeper = 0, */ idogcatcher = 1, iflautist = 2, isecretary = 3;
		
		// String arrays with firstname.

		String[] firstnames = { "Lynn", "Calla", "Bill", "Mark" };

		// Constant indexes to ease referring to firstname variables.

		int ilynn = 0, icalla = 1, ibill = 2, imark = 3;

		// String arrays with muffin numbers.

		String[] muffinnumbers = { "muffin1", "muffin2", "muffin3", "muffin4" };
		int i1 = 0, i2 = 1, i3 = 2, i4 = 3;

		// Arrays for variables.

		IntVar person[] = new IntVar[4];
		IntVar last[] = new IntVar[4];
		IntVar profession[] = new IntVar[4];
		IntVar muffins[] = new IntVar[4];

		// All variables are created with domain 0..3. Variables from
		// different arrays with the same values denote the same person.

		for (int i = 0; i < 4; i++) {
			last[i] = new IntVar(store, lastnames[i], 0, 3);
			profession[i] = new IntVar(store, professionNames[i], 0, 3);
			muffins[i] = new IntVar(store, muffinnumbers[i], 0, 3);
			person[i] = new IntVar(store, firstnames[i], 0, 3);
			vars.add(last[i]); vars.add(profession[i]); vars.add(muffins[i]);
			vars.add(person[i]);
		}

		// It is not possible that one person had two lastnames, or
		// two professions.
		store.impose(new Alldifferent(person));
		store.impose(new Alldifferent(last));
		store.impose(new Alldifferent(profession));

		// 1. Each housemate snitched a different number of muffins from
		// one to four.
		store.impose(new Alldifferent(muffins));

		// Auxilary variables to help express clue number 2.

		IntVar six = new IntVar(store, "six", 6, 6);
		IntVar I1 = new IntVar(store, "temp1", 1, 4);
		IntVar I2 = new IntVar(store, "temp2", 1, 4);

		// I1 denotes number of muffins taken by Bill.
		store.impose(new Element(I1, muffins, person[ibill]));
		// I2 denotes number of muffins taken by Ellis.
		store.impose(new Element(I2, muffins, last[iellis]));
		// 2. Bill and Ellis snitched a total of six muffins.
		store.impose(new XplusYeqZ(I1, I2, six));

		// 3. The secretary (who is a woman) snitched more than the dogcatcher.

		// secretary is a women, so it must have had the same number
		// as Calla or Lynn.
		store.impose(new Or(new XeqY(profession[isecretary], person[icalla]),
				new XeqY(profession[isecretary], person[ilynn])));

		IntVar I3 = new IntVar(store, "temp3", 1, 4);
		IntVar I4 = new IntVar(store, "temp4", 1, 4);

		// I3 denotes number of muffins taken by secretary.
		store.impose(new Element(I3, muffins, profession[isecretary]));
		// I4 denotes number of muffins taken by dogcatcher
		store.impose(new Element(I4, muffins, profession[idogcatcher]));

		// secretary has snitched more muffins than the dogcatcher.
		store.impose(new XgtY(I3, I4));

		// 4. Mark snitched two more than Summers did.
		store.impose(new Or(new And(new XeqY(last[isummer], muffins[i1]),
				new XeqY(person[imark], muffins[i3])), new And(new XeqY(
				last[isummer], muffins[i2]), new XeqY(person[imark],
				muffins[i4]))));

		// 5. The flautist snitched twice as many as Ms. Oakley did.
		store.impose(new Or(new And(new XeqY(last[ioakley], muffins[i1]),
				new XeqY(profession[iflautist], muffins[i2])), new And(
				new XeqY(last[ioakley], muffins[i2]), new XeqY(
						profession[iflautist], muffins[i4]))));

		// 6. Calla's last name isn't Ingham.
		store.impose(new XneqY(person[icalla], last[iingham]));

	}
	
	
	/**
	 * It executes the program solving this puzzle.
	 * @param args no arguments are read.
	 */
	public static void main(String args[]) {

		BlueberryMuffins example = new BlueberryMuffins();
		
		example.model();

		if (example.search())
			System.out.println("Solution(s) found");
		
	}	
	
}
