/**
 *  CalendarMen.java 
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
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XgtY;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/** 
 * 
 * It solves a simple logic puzzle about sport calendar. 
 * 
 * @author Michal Tonderski, Szymon Sieklucki, and Radoslaw Szymanek
 * 
 * Title: Calendar Men
 * Author of a logic puzzle: Alex Knight
 * Publication: Dell Logic Puzzles
 * Issue: December, 1998
 * Page: 52
 * Stars: 5
 *
 * To raise some money for college sports programs, students 
 * at a local junior college produced and sold an "Athlete of 
 * the Month" calendar. Each month of the year featured a 
 * photograph of a different man (first names are Antonio, 
 * Brett, Cliff, Dabney, Ed, Francisco, Griff, Harry, Ivor, 
 * John, Karl, and Lorenzo; last names are Moross, Nelsen, 
 * O'Rourke, Paulos, Quarello, Reede, Sheldon, Taylor, Uhler,
 * Vickers, Wang and Xiao) engaged in a different sport
 * (archery, badminton, croquet, football, golf, hockey, 
 * lacrosse, pole vaulting, rowing, squash, tennis, and 
 * volleyball). Can you find the full name
 * and sport of each month's athlete?
 */

public class CalendarMen extends ExampleFD {

	@Override
	public void model() {

		store = new Store();
		vars = new ArrayList<IntVar>();

		System.out.println("This program solves logic puzzle Calendar Men");

		// Firstnames of people involved

		String[] firstNames = { "Antonio", "Brett", "Cliff", "Dabney", "Ed",
				"Francisco", "Griff", "Harry", "Ivor", "John", "Karl",
				"Lorenzo" };

		// indexes for people involved for ease of referring later.
		int iAntonio = 0, iBrett = 1, /* iCliff = 2, */ iDabney = 3, iEd = 4, 
			iFrancisco = 5, iGriff = 6, iHarry = 7, iIvor = 8, iJohn = 9, 
			iKarl = 10, iLorenzo = 11;

		// Lastnames of people involved

		String[] lastNames = { "Moross", "Nelsen", "O_Rourke", "Paulos",
				"Quarello", "Reede", "Sheldon", "Taylor", "Uhler", "Vickers",
				"Wang", "Xiao" };

		// indexes for people involved for ease of referring later.
		int iMoross = 0, iNelsen = 1, iO_Rourke = 2, iPaulos = 3, iQuarello = 4, 
			iReede = 5, iSheldon = 6, iTaylor = 7, iUhler = 8, /* iVickers = 9, */ 
			iWang = 10, iXiao = 11;

		// Names of sports

		String[] sportNames = { "archery", "badminton", "croquet", "football",
				"golf", "hockey", "lacrosse", "vaulting", "rowing", "squash",
				"tennis", "volleyball" };

		// indexes for sports involved for ease of referring later.
		int iarchery = 0, ibadminton = 1, icroquet = 2, ifootball = 3, igolf = 4, 
			ihockey = 5, ilacrosse = 6, ivaulting = 7, irowing = 8, isquash = 9, 
			itennis = 10, ivolleyball = 11;

		// Three sets of variables, the same values at different sets denote
		// relation between appropriate variables.

		IntVar first[] = new IntVar[12];
		IntVar last[] = new IntVar[12];
		IntVar sport[] = new IntVar[12];

		for (int i = 0; i < 12; i++) {
			first[i] = new IntVar(store, firstNames[i], 1, 12);
			last[i] = new IntVar(store, lastNames[i], 1, 12);
			sport[i] = new IntVar(store, sportNames[i], 1, 12);
			vars.add(first[i]); vars.add(last[i]); vars.add(sport[i]);
		}

		store.impose(new Alldifferent(first));
		store.impose(new Alldifferent(last));
		store.impose(new Alldifferent(sport));

		// Constraints imposition
		// 1. Francisco, Sheldon, and the volleyball
		// player were featured in April, July, and
		// October, in some order.
		// Lista_1 is filled with allowed months (April, July, October). Then
		// indexes I1, I2, and I3
		// which must be different can freely point to any of the months.
		IntVar I_1_1 = new IntVar(store, "c1_1_m", 1, 3);
		IntVar I_1_2 = new IntVar(store, "c1_2_m", 1, 3);
		IntVar I_1_3 = new IntVar(store, "c1_3_m", 1, 3);

		vars.add(I_1_1);
		vars.add(I_1_2);
		vars.add(I_1_3);

		store.impose(new XneqY(I_1_1, I_1_2));
		store.impose(new XneqY(I_1_2, I_1_3));
		store.impose(new XneqY(I_1_1, I_1_3));

		int lista_1[] = { 4, 7, 10 };

		store.impose(new Element(I_1_1, lista_1, first[iFrancisco]));

		store.impose(new Element(I_1_2, lista_1, last[iSheldon]));

		store.impose(new Element(I_1_3, lista_1, sport[ivolleyball]));

		// 2. Karl, Moross, and the hockey player were
		// featured in consecutive months, but not
		// necessarily in that order.

		// It is implemented in the similar way as clue no. 1. However, we do
		// not use integers but variables. This allows us not to specify exact months.

		IntVar I_2_1 = new IntVar(store, "c2_1_m", 1, 3);
		IntVar I_2_2 = new IntVar(store, "c2_2_m", 1, 3);
		IntVar I_2_3 = new IntVar(store, "c2_3_m", 1, 3);

		vars.add(I_2_1);
		vars.add(I_2_2);
		vars.add(I_2_3);

		store.impose(new XneqY(I_2_1, I_2_2));
		store.impose(new XneqY(I_2_2, I_2_3));
		store.impose(new XneqY(I_2_1, I_2_3));

		IntVar X1 = new IntVar(store, "c2_1_x", 1, 12);
		IntVar X2 = new IntVar(store, "c2_2_x", 1, 12);
		IntVar X3 = new IntVar(store, "c2_3_x", 1, 12);

		vars.add(X1);
		vars.add(X2);
		vars.add(X3);

		store.impose(new XplusCeqZ(X1, 1, X2));
		store.impose(new XplusCeqZ(X1, 2, X3));

		IntVar lista_2[] = { X1, X2, X3 };

		store.impose(new Element(I_2_1, lista_2, first[iKarl]));

		store.impose(new Element(I_2_2, lista_2, last[iMoross]));

		store.impose(new Element(I_2_3, lista_2, sport[ihockey]));

		// 3. Lorenzo appeared an even number of months
		// after the squash player.

		// even auxilary variable is defined and used.
		IntVar even = new IntVar(store, "even"); 
		even.addDom(2, 2);
		even.addDom(4, 4);
		even.addDom(6, 6);
		even.addDom(8, 8);
		even.addDom(10, 10);

		vars.add(even);
		
		store.impose(new XplusYeqZ(sport[isquash], even, first[iLorenzo]));

		// 4. Ivor, O'Rourke, and the tennis player were
		// featured in June, September, and December,
		// in some order.

		// look at the description of clue no. 1.

		IntVar D1 = new IntVar(store, "c4_1_m", 1, 3);
		IntVar D2 = new IntVar(store, "c4_2_m", 1, 3);
		IntVar D3 = new IntVar(store, "c4_3_m", 1, 3);

		vars.add(D1);
		vars.add(D2);
		vars.add(D3);

		store.impose(new XneqY(D1, D2));
		store.impose(new XneqY(D2, D3));
		store.impose(new XneqY(D1, D3));

		int lista_4[] = { 6, 9, 12 };

		store.impose(new Element(D1, lista_4, first[iIvor]));
		store.impose(new Element(D2, lista_4, last[iO_Rourke]));
		store.impose(new Element(D3, lista_4, sport[itennis]));

		// 5. Wang was featured the month immediately after John, and two months
		// immediately before Nelsen.

		store.impose(new XplusCeqZ(last[iWang], -1, first[iJohn]));

		store.impose(new XplusCeqZ(last[iWang], 2, last[iNelsen]));

		// 6. Taylor was shown rowing exactly four months after Antonio Xiao's
		// picture, and exactly four months before Harry was shown playing
		// badminton.

		store.impose(new XplusCeqZ(first[iAntonio], 4, last[iTaylor]));

		store.impose(new XplusCeqZ(last[iTaylor], 4, first[iHarry]));

		store.impose(new XeqY(last[iTaylor], sport[irowing]));

		store.impose(new XeqY(first[iAntonio], last[iXiao]));

		store.impose(new XeqY(first[iHarry], sport[ibadminton]));

		// 7. Dabney was featured the month immediately after Paulos.

		store.impose(new XplusCeqZ(first[iDabney], -1, last[iPaulos]));

		// 8. The football player was featured exactly four months after
		// Quarello.

		store.impose(new XplusCeqZ(sport[ifootball], -4, last[iQuarello]));

		// 9. Griff, Reede, and the archer were featured in January, May, and
		// September, in some order.
		// Look at the description of clue no. 1.

		IntVar I_9_1 = new IntVar(store, "c9_1_m", 1, 3);
		IntVar I_9_2 = new IntVar(store, "c9_2_m", 1, 3);
		IntVar I_9_3 = new IntVar(store, "c9_3_m", 1, 3);

		vars.add(I_9_1);
		vars.add(I_9_2);
		vars.add(I_9_3);

		store.impose(new XneqY(I_9_1, I_9_2));
		store.impose(new XneqY(I_9_2, I_9_3));
		store.impose(new XneqY(I_9_1, I_9_3));

		int lista_9[] = { 1, 5, 9 };

		store.impose(new Element(I_9_1, lista_9, first[iGriff]));
		store.impose(new Element(I_9_2, lista_9, last[iReede]));
		store.impose(new Element(I_9_3, lista_9, sport[iarchery]));

		// 10. Brett, Ed, and Lorenzo were featured in consecutive months,
		// though not necessarily in that order.
		// Look at the description of clue no. 2.

		IntVar I_10_1 = new IntVar(store, "c10_1_m", 1, 3);
		IntVar I_10_2 = new IntVar(store, "c10_2_m", 1, 3);
		IntVar I_10_3 = new IntVar(store, "c10_3_m", 1, 3);

		vars.add(I_10_1);
		vars.add(I_10_2);
		vars.add(I_10_3);

		store.impose(new XneqY(I_10_1, I_10_2));
		store.impose(new XneqY(I_10_2, I_10_3));
		store.impose(new XneqY(I_10_1, I_10_3));

		IntVar W1 = new IntVar(store, "c10_1_x", 1, 12);
		IntVar W2 = new IntVar(store, "c10_2_x", 1, 12);
		IntVar W3 = new IntVar(store, "c10_3_x", 1, 12);

		vars.add(W1);
		vars.add(W2);
		vars.add(W3);

		store.impose(new XplusCeqZ(W1, 1, W2));
		store.impose(new XplusCeqZ(W1, 2, W3));

		IntVar lista_10[] = { W1, W2, W3 };

		store.impose(new Element(I_10_1, lista_10, first[iBrett]));
		store.impose(new Element(I_10_2, lista_10, first[iEd]));
		store.impose(new Element(I_10_3, lista_10, first[iLorenzo]));

		// 11. Ed, Uhler, and the croquet player were featured in consecutive
		// months, though not necessarily in that order.
		// Look at the description of clue no. 2.

		IntVar K1 = new IntVar(store, "c11_1_m", 1, 3);
		IntVar K2 = new IntVar(store, "c11_2_m", 1, 3);
		IntVar K3 = new IntVar(store, "c11_3_m", 1, 3);

		vars.add(K1);
		vars.add(K2);
		vars.add(K3);

		store.impose(new XneqY(K1, K2));
		store.impose(new XneqY(K2, K3));
		store.impose(new XneqY(K1, K3));

		IntVar Q1 = new IntVar(store, "c11_1_x", 1, 12);
		IntVar Q2 = new IntVar(store, "c11_2_x", 1, 12);
		IntVar Q3 = new IntVar(store, "c11_3_x", 1, 12);

		vars.add(Q1);
		vars.add(Q2);
		vars.add(Q3);

		store.impose(new XplusCeqZ(Q1, 1, Q2));
		store.impose(new XplusCeqZ(Q1, 2, Q3));

		IntVar lista_11[] = { Q1, Q2, Q3 };

		store.impose(new Element(K1, lista_11, first[iEd]));
		store.impose(new Element(K2, lista_11, last[iUhler]));
		store.impose(new Element(K3, lista_11, sport[icroquet]));

		// 12. Dabney, Nelsen, and the lacrosse player were featured in April,
		// June, and August, in some order.
		// Look at the description of clue no. 1.

		IntVar L1 = new IntVar(store, "c12_1_m", 1, 3);
		IntVar L2 = new IntVar(store, "c12_2_m", 1, 3);
		IntVar L3 = new IntVar(store, "c12_3_m", 1, 3);

		vars.add(L1);
		vars.add(L2);
		vars.add(L3);

		store.impose(new XneqY(L1, L2));
		store.impose(new XneqY(L2, L3));
		store.impose(new XneqY(L1, L3));

		int lista_12[] = { 4, 6, 8 };

		store.impose(new Element(L1, lista_12, first[iDabney]));
		store.impose(new Element(L2, lista_12, last[iNelsen]));
		store.impose(new Element(L3, lista_12, sport[ilacrosse]));

		// 13. Brett doesn't play lacrosse.

		store.impose(new XneqY(first[iBrett], sport[ilacrosse]));

		// 14. Dabney isn't Wang.

		store.impose(new XneqY(first[iDabney], last[iWang]));

		// 15. Antonio doesn't play hockey.

		store.impose(new XneqY(first[iAntonio], sport[ihockey]));

		// 16. The pole vaulter appeared sometime after the golfer.

		store.impose(new XgtY(sport[ivaulting], sport[igolf]));

	}
			
	/**
	 * It creates a model of this logic puzzle using mostly 
	 * primitive constraints.
	 */
	public void modelBasic() {

		store = new Store();
		vars = new ArrayList<IntVar>();
		
		System.out.println("This program solves logic puzzle Calendar Men");

		String[] firstnameID = { "Antonio", "Brett", "Cliff", "Dabney", "Ed",
				"Francisco", "Griff", "Harry", "Ivor", "John", "Karl",
		"Lorentzo" };

		int iAntonio = 0, iBrett = 1, /* iCliff = 2, */ iDabney = 3, iEd = 4, 
			iFrancisco = 5, iGriff = 6, iHarry = 7, iIvor = 8, iJohn = 9, 
			iKarl = 10, iLorentzo = 11;

		String[] surnameID = { "Moross", "Nelsen", "ORourke", "Paulos",
				"Quarello", "Reede", "Sheldon", "Taylor", "Uhler", "Vickers",
				"Wang", "Xiao" };

		int iMoross = 0, iNelsen = 1, iORourke = 2, iPaulos = 3, iQuarello = 4, 
			iReede = 5, iSheldon = 6, iTaylor = 7, iUhler = 8, /* iVickers = 9, */ 
			iWang = 10, iXiao = 11;

		String[] sportID = { "archery", "badmington", "croquet", "football",
				"golf", "hockey", "lacrosse", "p_vauliting", "rowing",
				"squash", "tennis", "volleyball" };

		int iarchery = 0, ibadmington = 1, icroquet = 2, ifootball = 3, igolf = 4,
			ihockey = 5, ilacrosse = 6, ip_vauliting = 7, irowing = 8, isquash = 9, 
			itennis = 10, ivolleyball = 11;

		IntVar firstname[] = new IntVar[12];
		IntVar surname[] = new IntVar[12];
		IntVar sport[] = new IntVar[12];

		for (int i = 0; i < 12; i++) {
			firstname[i] = new IntVar(store, firstnameID[i], 1, 12);
			surname[i] = new IntVar(store, surnameID[i], 1, 12);
			sport[i] = new IntVar(store, sportID[i], 1, 12);
			vars.add(firstname[i]); vars.add(surname[i]); vars.add(sport[i]);
		}

		store.impose(new Alldifferent(firstname));
		store.impose(new Alldifferent(surname));
		store.impose(new Alldifferent(sport));

		// 1. Francisco, Sheldon, and the volleyball player were featured in
		// April, July, and October, in some order.

		store.impose(new XneqY(firstname[iFrancisco], surname[iSheldon]));
		store.impose(new XneqY(firstname[iFrancisco], sport[ivolleyball]));
		store.impose(new XneqY(surname[iSheldon], sport[ivolleyball]));

		PrimitiveConstraint[] v11 = { new XeqC(firstname[iFrancisco], 4),
				new XeqC(firstname[iFrancisco], 7),
				new XeqC(firstname[iFrancisco], 10) };

		PrimitiveConstraint[] v12 = { new XeqC(surname[iSheldon], 4),
				new XeqC(surname[iSheldon], 7), new XeqC(surname[iSheldon], 10) };

		PrimitiveConstraint[] v13 = { new XeqC(sport[ivolleyball], 4),
				new XeqC(sport[ivolleyball], 7),
				new XeqC(sport[ivolleyball], 10) };

		store.impose(new Or(v11));
		store.impose(new Or(v12));
		store.impose(new Or(v13));

		// 2. Karl, Moross, and the hockey player were featured in consecutive
		// months, but not necessarily in that order.

		store.impose(new XneqY(surname[iMoross], firstname[iKarl]));
		store.impose(new XneqY(surname[iMoross], sport[ihockey]));
		store.impose(new XneqY(firstname[iKarl], sport[ihockey]));

		PrimitiveConstraint[] v24 = {
				new XplusCeqZ(firstname[iKarl], 1, surname[iMoross]),
				new XplusCeqZ(surname[iMoross], 1, sport[ihockey]) };

		PrimitiveConstraint[] v25 = {
				new XplusCeqZ(firstname[iKarl], 1, sport[ihockey]),
				new XplusCeqZ(sport[ihockey], 1, surname[iMoross]) };

		PrimitiveConstraint[] v26 = {
				new XplusCeqZ(surname[iMoross], 1, firstname[iKarl]),
				new XplusCeqZ(firstname[iKarl], 1, sport[ihockey]) };

		PrimitiveConstraint[] v27 = {
				new XplusCeqZ(surname[iMoross], 1, sport[ihockey]),
				new XplusCeqZ(sport[ihockey], 1, firstname[iKarl]) };

		PrimitiveConstraint[] v28 = {
				new XplusCeqZ(sport[ihockey], 1, surname[iMoross]),
				new XplusCeqZ(surname[iMoross], 1, firstname[iKarl]) };

		PrimitiveConstraint[] v29 = {
				new XplusCeqZ(sport[ihockey], 1, firstname[iKarl]),
				new XplusCeqZ(firstname[iKarl], 1, surname[iMoross]) };

		PrimitiveConstraint[] v23 = { new And(v24), new And(v25), new And(v26),
				new And(v27), new And(v28), new And(v29) };
		store.impose(new Or(v23));

		// 3. Lorenzo appeared an even number of months after the squash player.

		IntVar offset1 = new IntVar(store, "offset1", 1, 5);
		IntVar offset2 = new IntVar(store, "offset2", 2, 10);
		store.impose(new XmulCeqZ(offset1, 2, offset2));

		store.impose(new XplusYeqZ(sport[isquash], offset2,
				firstname[iLorentzo]));

		// 4. Ivor, O'Rourke, and the tennis player were featured in June,
		// September, and December, in some order.

		store.impose(new XneqY(firstname[iIvor], surname[iORourke]));
		store.impose(new XneqY(firstname[iIvor], sport[itennis]));
		store.impose(new XneqY(surname[iORourke], sport[itennis]));

		PrimitiveConstraint[] v41 = { new XeqC(firstname[iIvor], 6),
				new XeqC(firstname[iIvor], 9), new XeqC(firstname[iIvor], 12) };

		PrimitiveConstraint[] v42 = { new XeqC(surname[iORourke], 6),
				new XeqC(surname[iORourke], 9), new XeqC(surname[iORourke], 12) };

		PrimitiveConstraint[] v43 = { new XeqC(sport[itennis], 6),
				new XeqC(sport[itennis], 9), new XeqC(sport[itennis], 12) };

		store.impose(new Or(v41));
		store.impose(new Or(v42));
		store.impose(new Or(v43));

		// 5. Wang was featured the month immediately after John, and two months
		// immediately before Nelsen.

		store.impose(new XneqY(firstname[iJohn], surname[iWang]));
		store.impose(new XneqY(firstname[iJohn], surname[iNelsen]));
		store.impose(new XplusCeqZ(firstname[iJohn], 1, surname[iWang]));
		store.impose(new XplusCeqZ(surname[iWang], 2, surname[iNelsen]));

		// 6. Taylor was shown rowing exactly four months after
		// Antonio Xiao's picture, and exactly four months before
		// Harry was shown playing badminton.

		store.impose(new XeqY(surname[iTaylor], sport[irowing]));
		store.impose(new XeqY(firstname[iHarry], sport[ibadmington]));
		store.impose(new XeqY(firstname[iAntonio], surname[iXiao]));
		store.impose(new XneqY(surname[iTaylor], firstname[iHarry]));
		store.impose(new XplusCeqZ(surname[iTaylor], 4, firstname[iHarry]));
		store.impose(new XplusCeqZ(firstname[iAntonio], 4, surname[iTaylor]));
		store.impose(new XneqY(firstname[iAntonio], sport[ibadmington]));
		store.impose(new XneqY(firstname[iAntonio], sport[irowing]));

		// 7. Dabney was featured the month immediately after Paulos.

		store.impose(new XneqY(firstname[iDabney], surname[iPaulos]));
		store.impose(new XplusCeqZ(surname[iPaulos], 1, firstname[iDabney]));

		// 8. The football player was featured exactly four months after
		// Quarello.

		store.impose(new XneqY(sport[ifootball], surname[iQuarello]));
		store.impose(new XplusCeqZ(surname[iQuarello], 4, sport[ifootball]));

		// 9. Griff, Reede, and the archer were featured in January, May, and
		// September, in some order.

		store.impose(new XneqY(firstname[iGriff], surname[iReede]));
		store.impose(new XneqY(firstname[iGriff], sport[iarchery]));
		store.impose(new XneqY(surname[iReede], sport[iarchery]));

		PrimitiveConstraint[] v91 = { new XeqC(firstname[iGriff], 1),
				new XeqC(firstname[iGriff], 5), new XeqC(firstname[iGriff], 9) };

		PrimitiveConstraint[] v92 = { new XeqC(surname[iReede], 1),
				new XeqC(surname[iReede], 5), new XeqC(surname[iReede], 9) };

		PrimitiveConstraint[] v93 = { new XeqC(sport[iarchery], 1),
				new XeqC(sport[iarchery], 5), new XeqC(sport[iarchery], 9) };

		store.impose(new Or(v91));
		store.impose(new Or(v92));
		store.impose(new Or(v93));

		// 10. Brett, Ed, and Lorenzo were featured in consecutive months,
		// though not necessarily in that order.

		PrimitiveConstraint[] v100 = {
				new XplusCeqZ(firstname[iBrett], 1, firstname[iEd]),
				new XplusCeqZ(firstname[iEd], 1, firstname[iLorentzo]) };

		PrimitiveConstraint[] v101 = {
				new XplusCeqZ(firstname[iBrett], 1, firstname[iLorentzo]),
				new XplusCeqZ(firstname[iLorentzo], 1, firstname[iEd]) };

		PrimitiveConstraint[] v102 = {
				new XplusCeqZ(firstname[iEd], 1, firstname[iBrett]),
				new XplusCeqZ(firstname[iBrett], 1, firstname[iLorentzo]) };

		PrimitiveConstraint[] v103 = {
				new XplusCeqZ(firstname[iEd], 1, firstname[iLorentzo]),
				new XplusCeqZ(firstname[iLorentzo], 1, firstname[iBrett]) };

		PrimitiveConstraint[] v104 = {
				new XplusCeqZ(firstname[iLorentzo], 1, firstname[iEd]),
				new XplusCeqZ(firstname[iEd], 1, firstname[iBrett]) };

		PrimitiveConstraint[] v105 = {
				new XplusCeqZ(firstname[iLorentzo], 1, firstname[iBrett]),
				new XplusCeqZ(firstname[iBrett], 1, firstname[iEd]) };

		PrimitiveConstraint[] v106 = { new And(v100), new And(v101),
				new And(v102), new And(v103), new And(v104), new And(v105) };

		store.impose(new Or(v106));

		// 11. Ed, Uhler, and the croquet player were featured in consecutive
		// months, though not necessarily in that order.

		store.impose(new XneqY(surname[iUhler], firstname[iEd]));
		store.impose(new XneqY(surname[iUhler], sport[icroquet]));
		store.impose(new XneqY(firstname[iEd], sport[icroquet]));

		PrimitiveConstraint[] v111 = {
				new XplusCeqZ(firstname[iEd], 1, surname[iUhler]),
				new XplusCeqZ(surname[iUhler], 1, sport[icroquet]) };

		PrimitiveConstraint[] v112 = {
				new XplusCeqZ(firstname[iEd], 1, sport[icroquet]),
				new XplusCeqZ(sport[icroquet], 1, surname[iUhler]) };

		PrimitiveConstraint[] v113 = {
				new XplusCeqZ(surname[iUhler], 1, firstname[iEd]),
				new XplusCeqZ(firstname[iEd], 1, sport[icroquet]) };

		PrimitiveConstraint[] v114 = {
				new XplusCeqZ(surname[iUhler], 1, sport[icroquet]),
				new XplusCeqZ(sport[icroquet], 1, firstname[iEd]) };

		PrimitiveConstraint[] v115 = {
				new XplusCeqZ(sport[icroquet], 1, surname[iUhler]),
				new XplusCeqZ(surname[iUhler], 1, firstname[iEd]) };

		PrimitiveConstraint[] v116 = {
				new XplusCeqZ(sport[icroquet], 1, firstname[iEd]),
				new XplusCeqZ(firstname[iEd], 1, surname[iUhler]) };

		PrimitiveConstraint[] v110 = { new And(v111), new And(v112),
				new And(v113), new And(v114), new And(v115), new And(v116) };

		store.impose(new Or(v110));

		// 12. Dabney, Nelsen, and the lacrosse player were featured in April,
		// June, and August, in some order.

		store.impose(new XneqY(firstname[iDabney], surname[iNelsen]));
		store.impose(new XneqY(firstname[iDabney], sport[ilacrosse]));
		store.impose(new XneqY(surname[iNelsen], sport[ilacrosse]));

		PrimitiveConstraint[] v121 = { new XeqC(firstname[iDabney], 4),
				new XeqC(firstname[iDabney], 6),
				new XeqC(firstname[iDabney], 8) };

		PrimitiveConstraint[] v122 = { new XeqC(surname[iNelsen], 4),
				new XeqC(surname[iNelsen], 6), new XeqC(surname[iNelsen], 8) };

		PrimitiveConstraint[] v123 = { new XeqC(sport[ilacrosse], 4),
				new XeqC(sport[ilacrosse], 6), new XeqC(sport[ilacrosse], 8) };

		store.impose(new Or(v121));
		store.impose(new Or(v122));
		store.impose(new Or(v123));

		// 13. Brett doesn't play lacrosse.

		store.impose(new XneqY(firstname[iBrett], sport[ilacrosse]));

		// 14. Dabney isn't Wang.

		store.impose(new XneqY(firstname[iDabney], surname[iWang]));

		// 15. Antonio doesn't play hockey.

		store.impose(new XneqY(firstname[iAntonio], sport[ihockey]));

		// 16. The pole vaulter appeared sometime after the golfer.

		store.impose(new XltY(sport[igolf], sport[ip_vauliting])); // X < Y

	}


	/**
	 * It executes the program solving this puzzle using two different models.
	 * @param args no arguments read.
	 */
	public static void test(String args[]) {

		CalendarMen example = new CalendarMen();

		example.model();

		if (example.searchSmallestDomain(false))
			System.out.println("Solution(s) found");

		CalendarMen exampleBasic = new CalendarMen();

		exampleBasic.modelBasic();

		if (exampleBasic.searchSmallestDomain(false))
			System.out.println("Solution(s) found");


	}			

	/**
	 * It executes the program solving this puzzle using the best approach.
	 * @param args no arguments read.
	 */
	public static void main(String args[]) {

		CalendarMen example = new CalendarMen();

		example.model();

		if (example.searchSmallestDomain(false))
			System.out.println("Solution(s) found");

	}			

		
}
