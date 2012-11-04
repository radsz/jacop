/**
 *  LectureSeries.java 
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
import org.jacop.constraints.Distance;
import org.jacop.constraints.Element;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XgtY;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
*
* It is a simple logic puzzle about lectures.
*
* @author Grzegorz Moskwa, Marcin Nowak, and Radoslaw Szymanek
* 
* Last week at school was made varied by a series of lectures, one each
* day (Monday through Friday), in the auditorium.  None of the lectures
* was particularly interesting (on choosing a college, physical
* hygiene, modern art, nutrition, and study habits), but the students
* figured that anything that got them out of fourth period was
* okay. The lecturers were two women named Alice and Bernadette, and
* three men named Charles, Duane, and Eddie; last names were Felicidad,
* Garber, Haller, Itakura, and Jeffreys.  Can you find each day's
* lecturer and subject?
* 
* 1. Alice lectured on Monday.
*
* 2. Charles's lecture on physical hygiene wasn't given on Friday.
*
* 3. Dietician Jeffreys gave the lecture on nutrition.
*
* 4. A man gave the lecture on modern art.
*
* 5. Ms. Itakura (*5a) and the lecturer on proper study habits spoke on 
* consecutive days, in one order or the other.(*5b)
*
* 6. Haller gave a lecture sometime after Eddie did.
*
* 7. Duane Felicidad (*7a) gave his lecture sometime before the modern 
* art lecture(*7b)
*
*
* Answer:
*
* Monday, Alice Itakura, choosing a college
* Tuesday, Duane Felicidad, study habits
* Wednesday, Eddie Garber, modern art
* Thursday, Charles Haller, physical hygiene
* Friday, Bernadette Jeffreys, nutrition
*
*/

public class LectureSeries extends ExampleFD {

	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		
		System.out.println("Program to solve Lecture Series ");

		String[] firstNames = { "Alice", "Bernadette", "Charles", "Duane",
				"Eddie" };
		int iAlice = 0, iBernadette = 1, iCharles = 2, iDuane = 3, iEddie = 4;

		String[] lastNames = { "Felicidad", "Garber", "Haller", "Itakura",
				"Jeffreys" };
		int iFelicidad = 0, /* iGarber = 1, */ iHaller = 2, iItakura = 3, iJeffreys = 4;

		String[] daysNames = { "Monday", "Tuesday", "Wednesday", "Thursday",
				"Friday" };
		int iMonday = 0, /* iTuesday = 1, iWednesday = 2, iThursday = 3, */ iFriday = 4;

		String[] subjectsNames = { "College", "Hygiene", "Art", "Nutrition",
				"Study" };
		int /* iCollege = 0, */ iHygiene = 1, iArt = 2, iNutrition = 3, iStudy = 4;

		IntVar first[] = new IntVar[5];
		IntVar last[] = new IntVar[5];
		IntVar days[] = new IntVar[5];
		IntVar subjects[] = new IntVar[5];

		// FDV's creation
		// FDV's with the same value from different groups are related.
		for (int i = 0; i < 5; i++) {
			first[i] = new IntVar(store, firstNames[i], 1, 5);
			last[i] = new IntVar(store, lastNames[i], 1, 5);
			days[i] = new IntVar(store, daysNames[i], 1, 5);
			subjects[i] = new IntVar(store, subjectsNames[i], 1, 5);
			vars.add(first[i]); vars.add(last[i]); vars.add(days[i]); vars.add(subjects[i]);
		}

		// Each element within a group must differ from other elements
		// from the same group.
		store.impose(new Alldifferent(first));
		store.impose(new Alldifferent(last));
		store.impose(new Alldifferent(days));
		store.impose(new Alldifferent(subjects));

		// 1. Alice lectured on Monday.

		store.impose(new XeqY(first[iAlice], days[iMonday]));

		// 2. Charles's lecture on physical hygiene wasn't given on Friday.

		store.impose(new XeqY(first[iCharles], subjects[iHygiene]));
		store.impose(new XneqY(first[iCharles], days[iFriday]));
		store.impose(new XneqY(subjects[iHygiene], days[iFriday]));

		// 3. Dietician Jeffreys gave the lecture on nutrition.
		store.impose(new XeqY(last[iJeffreys], subjects[iNutrition]));

		// 4. A man gave the lecture on modern art.
		store.impose(new XneqY(first[iAlice], subjects[iArt]));
		store.impose(new XneqY(first[iBernadette], subjects[iArt]));

		// 5. Ms. Itakura (*5a) and the lecturer on proper study habits spoke on
		// consecutive days, in one order or the other.(*5b)

		IntVar dayIndex4Itakura = new IntVar(store, "dayIndex4Itakura", 1, 5);
		store.impose(new Element(dayIndex4Itakura, days, last[iItakura]));

		IntVar dayIndex4Study = new IntVar(store, "dayIndex4Study", 1, 5);
		store.impose(new Element(dayIndex4Study, days, subjects[iStudy]));

		IntVar one = new IntVar(store, "1", 1, 1);
		store.impose(new Distance(dayIndex4Itakura, dayIndex4Study, one));

		// Itakura is a woman
		store.impose(new XneqY(last[iItakura], first[iCharles]));
		store.impose(new XneqY(last[iItakura], first[iEddie]));

		// implied constraint
		store.impose(new XneqY(last[iItakura], subjects[iStudy]));

		// 6. Haller gave a lecture sometime after Eddie did.

		IntVar dayIndex4Haller = new IntVar(store, "dayIndex4Haller", 1, 5);
		store.impose(new Element(dayIndex4Haller, days, last[iHaller]));

		IntVar dayIndex4Eddie = new IntVar(store, "dayIndex4Eddie", 1, 5);
		store.impose(new Element(dayIndex4Eddie, days, first[iEddie]));

		store.impose(new XgtY(dayIndex4Haller, dayIndex4Eddie));

		// implied constraints
		// Haller can not be on Monday since after Eddie/
		store.impose(new XneqY(last[iHaller], days[iMonday]));
		// Eddie can not be on Fridays since before Haller
		store.impose(new XneqY(first[iEddie], days[iFriday]));
		// Eddie can not be Haller
		store.impose(new XneqY(first[iEddie], last[iHaller]));

		// 7. Duane Felicidad (*7a) gave his lecture sometime before the modern
		// art lecture(*7b)

		// Duane has a surname Felicidad
		store.impose(new XeqY(first[iDuane], last[iFelicidad]));

		IntVar dayIndex4Duane = new IntVar(store, "dayIndex4Duane", 1, 5);
		store.impose(new Element(dayIndex4Duane, days, first[iDuane]));

		IntVar dayIndex4Art = new IntVar(store, "dayIndex4Art", 1, 5);
		store.impose(new Element(dayIndex4Art, days, subjects[iArt]));

		store.impose(new XltY(dayIndex4Duane, dayIndex4Art));

		// implied constraints
		// Duane can not lecture on modern art.
		store.impose(new XneqY(first[iDuane], subjects[iArt]));
		store.impose(new XneqY(last[iItakura], first[iDuane]));

	}
	
	/**
	 * It executes the program which solves this simple logic puzzle.
	 * @param args no arguments is used.
	 */
	public static void main(String args[]) {

		LectureSeries example = new LectureSeries();
		
		example.model();

		if (example.search())
			System.out.println("Solution(s) found");
		
	}	
	
	
}
