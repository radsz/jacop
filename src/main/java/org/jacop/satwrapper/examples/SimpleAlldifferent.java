/**
 *  Flowers.java 
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

package org.jacop.satwrapper.examples;

import java.util.ArrayList;

import org.jacop.constraints.Alldifferent;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.satwrapper.SatWrapper;
import org.jacop.satwrapper.WrapperDebugModule;

/**
 * 
 * It is quite complex logic puzzle about flowers.
 * 
 * @author Tomasz Szwed, Wojciech Krupa, and Radoslaw Szymanek
 *
 * Each of four women in our office was delighted to receive a floral delivery at her desk this month. Each of the 
 * women (Emma, Kristin, Lynn, and Toni) received flowers from her husband (Doug, Justin, Shane, or Theo) for a 
 * different special occasion. Each bouquet consisted of a different type of flower, and each was delivered 
 * during the first four weeks of February. From the following clues, can you match each woman with her husband 
 * and determine the date on which each woman received flowers, the occasion for the flowers, and the type of 
 * flowers in each bouquet?
 * 
 *
 * Calendar for February
 *
 * Mon  Tue   Wed   Thu   Fri
 * -     1     2     3     4
 * 7    8     9    10    11
 * 14   15    16    17    18
 * 21   22    23    24    25
 *
 * 1. No two women received flowers on the same day of the week, and no two received flowers during the same week.
 *
 * 2. The woman who received flowers for Valentine's Day had them delivered on either Friday the 11th or 
 * Monday the 14th.
 *
 * 3. Emma received flowers one day later in the week than the woman who received flowers to celebrate a promotion.
 *
 * 4. Lynn received flowers either the week before or the week after the woman who received violets.
 *
 * 5. Justin's wife received flowers on either Monday the 7th (in which case she is the one who received white roses) 
 * or on Thursday the 24th (in which case she is the woman who received flowers to celebrate her birthday).
 *
 * 6. Theo's wife didn't receive flowers exactly eight days before the woman who received chrysanthemums.
 *
 * 7. Toni's husband is either Doug or Shane.
 *
 * 8. One woman received either chrysanthemums or white roses for her wedding anniversary.
 *
 * 9. Kristin received flowers on either Tuesday the 1st (in which case she is 
 * the one who received daisies) or Friday the 18th (in which case she received them from Doug).
 *
 * 10. Shane's wife received flowers during the second week of the month.
 *
 * Determine: woman, husband, date, occasion, type of flowers
 *
 */
@SuppressWarnings("unused")
public class SimpleAlldifferent extends ExampleFD {
		
	private SatWrapper wrapper;


	@Override
	public void model() {

		System.out.println("Program to solve Flower logic puzzle");

		store = new Store();
		vars = new ArrayList<IntVar>();
		
		wrapper = new SatWrapper();
		store.impose(wrapper);

		String[] wifeWeek = { "Emma", "Kristin", "Lynn", "Toni" };
		String[] wifeDay = { "EmmaDay", "KristinDay", "LynnDay", "ToniDay" };
		// index to women for ease of referring.
		int iEmma = 0, iKristin = 1, iLynn = 2, iToni = 3;

		String[] husbandWeek = { "Doug", "Justin", "Shane", "Theo" };
		String[] husbandDay = { "DougDay", "JustinDay", "ShaneDay", "TheoDay" };
		// index to men for ease of referring.
		int iDoug = 0, iJustin = 1, iShane = 2, iTheo = 3;

		String[] flowerWeek = { "Violets", "Roses", "Chrys", "Daises" };
		String[] flowerDay = { "VioletsDay", "RosesDay", "ChrysDay",
				"DaisesDay" };
		// index to flowers for ease of referring.
		int iViolets = 0, iRoses = 1, iChrys = 2, iDaises = 3;

		String[] occasionWeek = { "Walentynki", "Awans", "Urodziny", "Rocznica" };
		String[] occasionDay = { "WalentynkiDay", "AwansDay", "UrodzinyDay",
				"RocznicaDay" };
		// index to occasions for ease of referring.
		int iWalentynki = 0, iAwans = 1, iUrodziny = 2, iRocznica = 3;

		// For each (wife, husband, flower, occassion) there are two sets of
		// variables. One denotes a day and the
		// other denotes the week.

		int n = 4; // 2, 3 or 4
		IntVar wifeT[] = new IntVar[n];

		for (int i = 0; i < n; i++) {
			// Days in February are from 1 to 28.
			wifeT[i] = new IntVar(store, wifeWeek[i], 1, 4);
			vars.add(wifeT[i]);
			wrapper.register(wifeT[i]);
		}

		
		// 1. No two women received flowers on the same day of the week, and no
		// two received
		// flowers during the same week.
		store.imposeToSat(new Alldifferent(wifeT));
		//store.impose(new Alldifferent(wifeT));
		
	}

	
	/**
	 * It executes the program which solves this logic puzzle.
	 * @param args no argument is used.
	 */
	public static void main(String args[]) {

		SimpleAlldifferent example = new SimpleAlldifferent();
		
		example.model();
		

		// add debug and stat modules
		//StatModule mod = new StatModule(false);
		//example.wrapper.addSolverComponent(mod);
		WrapperDebugModule d = new WrapperDebugModule();
		example.wrapper.addSolverComponent(d);
		d.initialize(example.wrapper);
		
		if (example.searchAllAtOnce())
			System.out.println("Solution(s) found");
		
		// prints stats
		//mod.logStats();
		
	}		
	
}
