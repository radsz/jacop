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

package org.jacop.examples.fd;

import java.util.ArrayList;

import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.And;
import org.jacop.constraints.Element;
import org.jacop.constraints.Not;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

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


public class Flowers extends ExampleFD {
		
	@Override
	public void model() {

		System.out.println("Program to solve Flower logic puzzle");

		store = new Store();
		vars = new ArrayList<IntVar>();

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

		IntVar wifeT[] = new IntVar[4];
		IntVar wifeD[] = new IntVar[4];
		IntVar husbandT[] = new IntVar[4];
		IntVar husbandD[] = new IntVar[4];
		IntVar flowerT[] = new IntVar[4];
		IntVar flowerD[] = new IntVar[4];
		IntVar occasionT[] = new IntVar[4];
		IntVar occasionD[] = new IntVar[4];

		for (int i = 0; i < 4; i++) {
			// Days in February are from 1 to 28.
			husbandD[i] = new IntVar(store, husbandDay[i], 1, 28);
			wifeD[i] = new IntVar(store, wifeDay[i], 1, 28);
			occasionD[i] = new IntVar(store, occasionDay[i], 1, 28);
			flowerD[i] = new IntVar(store, flowerDay[i], 1, 28);
			// There are 4 weeks in February.
			husbandT[i] = new IntVar(store, husbandWeek[i], 1, 4);
			wifeT[i] = new IntVar(store, wifeWeek[i], 1, 4);
			occasionT[i] = new IntVar(store, occasionWeek[i], 1, 4);
			flowerT[i] = new IntVar(store, flowerWeek[i], 1, 4);
		}

		// 1. No two women received flowers on the same day of the week, and no
		// two received
		// flowers during the same week.
		store.impose(new Alldifferent(wifeT));
		store.impose(new Alldifferent(wifeD));
		store.impose(new Alldifferent(husbandT));
		store.impose(new Alldifferent(husbandD));
		store.impose(new Alldifferent(flowerT));
		store.impose(new Alldifferent(flowerD));
		store.impose(new Alldifferent(occasionT));
		store.impose(new Alldifferent(occasionD));

		// Since there are 28 days, there must be explicit constraints to make
		// sure
		// that days match up. (
		for (int x = 0; x < 4; x++) {

			IntVar xz = new IntVar(store, "xz" + x, 1, 4);
			vars.add(xz);
			store.impose(new Element(xz, wifeD, husbandD[x]));

			IntVar xc = new IntVar(store, "xc" + x, 1, 4);
			vars.add(xc);
			store.impose(new Element(xc, occasionD, husbandD[x]));

			IntVar xy = new IntVar(store, "xy" + x, 1, 4);
			vars.add(xy);
			store.impose(new Element(xy, flowerD, husbandD[x]));
		}

		// Channeling constraints between day number and week.

		int el[] = { 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3,
				3, 4, 4, 4, 4 };

		store.impose(new Element(wifeD[iEmma], el, wifeT[iEmma]));
		store.impose(new Element(wifeD[iKristin], el, wifeT[iKristin]));
		store.impose(new Element(wifeD[iLynn], el, wifeT[iLynn]));
		store.impose(new Element(wifeD[iToni], el, wifeT[iToni]));

		store.impose(new Element(husbandD[iDoug], el, husbandT[iDoug]));
		store.impose(new Element(husbandD[iJustin], el, husbandT[iJustin]));
		store.impose(new Element(husbandD[iShane], el, husbandT[iShane]));
		store.impose(new Element(husbandD[iTheo], el, husbandT[iTheo]));

		store.impose(new Element(flowerD[iViolets], el, flowerT[iViolets]));
		store.impose(new Element(flowerD[iRoses], el, flowerT[iRoses]));
		store.impose(new Element(flowerD[iChrys], el, flowerT[iChrys]));
		store.impose(new Element(flowerD[iDaises], el, flowerT[iDaises]));

		store.impose(new Element(occasionD[iWalentynki], el,
				occasionT[iWalentynki]));
		store.impose(new Element(occasionD[iAwans], el, occasionT[iAwans]));
		store.impose(new Element(occasionD[iUrodziny], el,
						occasionT[iUrodziny]));
		store.impose(new Element(occasionD[iRocznica], el,
						occasionT[iRocznica]));

		// 2. The woman who received flowers for Valentine's Day had them
		// delivered
		// on either Friday the 11th or Monday the 14th.
		PrimitiveConstraint ogr2[] = { new XeqC(occasionD[iWalentynki], 11),
				new XeqC(occasionD[iWalentynki], 14) };
		store.impose(new Or(ogr2));

		// 3. Emma received flowers one day later in the week than the woman who
		// received flowers to celebrate a promotion.

		store.impose(new XplusCeqZ(wifeD[iEmma], -8, occasionD[iAwans]));

		// 4. Lynn received flowers either the week before or the week after
		// the woman who received violets.

		PrimitiveConstraint ogr4[] = {
				new XplusCeqZ(wifeT[iLynn], 1, flowerT[iViolets]),
				new XplusCeqZ(wifeT[iLynn], -1, flowerT[iViolets]) };
		store.impose(new Or(ogr4));

		// 5. Justin's wife received flowers on either Monday the 7th
		// (in which case she is the one who received white roses) or
		// on Thursday the 24th (in which case she is the woman who received
		// flowers to celebrate her birthday).

		PrimitiveConstraint and5a[] = { new XeqC(husbandD[iJustin], 7),
				new XeqC(flowerD[iRoses], 7),
				new XeqY(husbandD[iJustin], flowerD[iRoses]) };

		PrimitiveConstraint and5b[] = { new XeqC(husbandD[iJustin], 24),
				new XeqC(occasionD[iUrodziny], 24),
				new XeqY(husbandD[iJustin], occasionD[iUrodziny]) };

		PrimitiveConstraint ogr5[] = { new And(and5a), new And(and5b) };

		store.impose(new Or(ogr5));

		// 6. Theo's wife didn't receive flowers exactly eight days before
		// the woman who received chrysanthemums.

		store.impose(new Not(new XplusCeqZ(husbandD[iTheo], 8,
						flowerD[iChrys])));

		// 7. Toni's husband is either Doug or Shane.

		PrimitiveConstraint ogr7[] = {
				new XeqY(wifeD[iToni], husbandD[iShane]),
				new XeqY(wifeD[iToni], husbandD[iDoug]) };
		store.impose(new Or(ogr7));

		// 8. One woman received either chrysanthemums or white roses for
		// her wedding anniversary.
		PrimitiveConstraint ogr8[] = {
				new XeqY(occasionD[iRocznica], flowerD[iChrys]),
				new XeqY(occasionD[iRocznica], flowerD[iRoses]) };
		store.impose(new Or(ogr8));

		// 9. Kristin received flowers on either Tuesday the 1st
		// (in which case she is the one who received daisies) or
		// Friday the 18th (in which case she received them from Doug).

		PrimitiveConstraint and9a[] = { new XeqC(wifeD[iKristin], 1),
				new XeqC(flowerD[iDaises], 1),
				new XeqY(wifeD[iKristin], flowerD[iDaises]) };

		PrimitiveConstraint and9b[] = { new XeqC(wifeD[iKristin], 18),
				new XeqC(husbandD[iDoug], 18),
				new XeqY(wifeD[iKristin], husbandD[iDoug]) };

		PrimitiveConstraint ogr9[] = { new And(and9a), new And(and9b) };
		store.impose(new Or(ogr9));

		// 10. Shane's wife received flowers during the second week of the
		// month.
		store.impose(new XeqC(husbandT[iShane], 2));

		for (IntVar v : wifeT)
			vars.add(v);
		for (IntVar v : wifeD)
			vars.add(v);
		for (IntVar v : husbandT)
			vars.add(v);
		for (IntVar v : husbandD)
			vars.add(v);
		for (IntVar v : occasionT)
			vars.add(v);
		for (IntVar v : occasionD)
			vars.add(v);
		for (IntVar v : flowerT)
			vars.add(v);
		for (IntVar v : flowerD)
			vars.add(v);		
		
	}

	
	/**
	 * It executes the program which solves this logic puzzle.
	 * @param args no argument is used.
	 */
	public static void main(String args[]) {

		Flowers example = new Flowers();
		
		example.model();

		if (example.search())
			System.out.println("Solution(s) found");
		
	}		
	
}
