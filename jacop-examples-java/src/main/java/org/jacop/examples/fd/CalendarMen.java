/*
 * CalendarMen.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/.
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
 * It solves a simple logic puzzle about sport calendar.
 *
 * <p>Title: Calendar Men Author of a logic puzzle: Alex Knight Publication: Dell Logic Puzzles
 * Issue: December, 1998 Page: 52 Stars: 5
 *
 * <p>To raise some money for college sports programs, students at a local junior college produced
 * and sold an "Athlete of the Month" calendar. Each month of the year featured a photograph of a
 * different man (first names are Antonio, Brett, Cliff, Dabney, Ed, Francisco, Griff, Harry, Ivor,
 * John, Karl, and Lorenzo; last names are Moross, Nelsen, O'Rourke, Paulos, Quarello, Reede,
 * Sheldon, Taylor, Uhler, Vickers, Wang and Xiao) engaged in a different sport (archery, badminton,
 * croquet, football, golf, hockey, lacrosse, pole vaulting, rowing, squash, tennis, and
 * volleyball). Can you find the full name and sport of each month's athlete?
 *
 * @author Michal Tonderski, Szymon Sieklucki, and Radoslaw Szymanek
 * @version 5.0
 */
public class CalendarMen extends ExampleFd {

  private static final String SOLUTION_FOUND = "Solution(s) found";

  /**
   * It executes the program solving this puzzle using two different models.
   *
   * @param args no arguments read.
   */
  public static void test(String[] args) {

    CalendarMen example = new CalendarMen();

    example.model();

    if (example.searchSmallestDomain(false)) {
      IO.println(SOLUTION_FOUND);
    }

    CalendarMen exampleBasic = new CalendarMen();

    exampleBasic.modelBasic();

    if (exampleBasic.searchSmallestDomain(false)) {
      IO.println(SOLUTION_FOUND);
    }
  }

  /**
   * It executes the program solving this puzzle using the best approach.
   *
   * @param args no arguments read.
   */
  static void main(String[] args) {

    CalendarMen example = new CalendarMen();

    example.model();

    if (example.searchSmallestDomain(false)) {
      IO.println(SOLUTION_FOUND);
    }
  }

  @Override
  public void model() {

    store = new Store();
    vars = new ArrayList<>();

    IO.println("This program solves logic puzzle Calendar Men");

    String[] firstNames = {
      "Antonio",
      "Brett",
      "Cliff",
      "Dabney",
      "Ed",
      "Francisco",
      "Griff",
      "Harry",
      "Ivor",
      "John",
      "Karl",
      "Lorenzo"
    };

    String[] lastNames = {
      "Moross",
      "Nelsen",
      "O_Rourke",
      "Paulos",
      "Quarello",
      "Reede",
      "Sheldon",
      "Taylor",
      "Uhler",
      "Vickers",
      "Wang",
      "Xiao"
    };

    String[] sportNames = {
      "archery",
      "badminton",
      "croquet",
      "football",
      "golf",
      "hockey",
      "lacrosse",
      "vaulting",
      "rowing",
      "squash",
      "tennis",
      "volleyball"
    };

    // indexes for people involved for ease of referring later.
    final int iAntonio = 0;
    final int iBrett = 1; /* iCliff = 2, */
    final int iDabney = 3;
    final int iEd = 4;
    final int iFrancisco = 5;
    final int iGriff = 6;
    final int iHarry = 7;
    final int iIvor = 8;
    final int iJohn = 9;
    final int iKarl = 10;
    final int iLorenzo = 11;

    final int iMoross = 0;
    final int iNelsen = 1;
    final int iO_Rourke = 2;
    final int iPaulos = 3;
    final int iQuarello = 4;
    final int iReede = 5;
    final int iSheldon = 6;
    final int iTaylor = 7;
    final int iUhler = 8; /* iVickers = 9, */
    final int iWang = 10;
    final int iXiao = 11;

    final int iarchery = 0;
    final int ibadminton = 1;
    final int icroquet = 2;
    final int ifootball = 3;
    final int igolf = 4;
    final int ihockey = 5;
    final int ilacrosse = 6;
    final int ivaulting = 7;
    final int irowing = 8;
    final int isquash = 9;
    final int itennis = 10;
    final int ivolleyball = 11;

    IntVar[] first = createVariables(firstNames);
    IntVar[] last = createVariables(lastNames);
    IntVar[] sport = createVariables(sportNames);

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

    int[] lista_1 = {4, 7, 10};

    store.impose(Element.choose(I_1_1, lista_1, first[iFrancisco]));

    store.impose(Element.choose(I_1_2, lista_1, last[iSheldon]));

    store.impose(Element.choose(I_1_3, lista_1, sport[ivolleyball]));

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

    IntVar x1 = new IntVar(store, "c2_1_x", 1, 12);
    IntVar x2 = new IntVar(store, "c2_2_x", 1, 12);
    IntVar x3 = new IntVar(store, "c2_3_x", 1, 12);

    vars.add(x1);
    vars.add(x2);
    vars.add(x3);

    store.impose(new XplusCeqZ(x1, 1, x2));
    store.impose(new XplusCeqZ(x1, 2, x3));

    IntVar[] lista_2 = {x1, x2, x3};

    store.impose(Element.choose(I_2_1, lista_2, first[iKarl]));

    store.impose(Element.choose(I_2_2, lista_2, last[iMoross]));

    store.impose(Element.choose(I_2_3, lista_2, sport[ihockey]));

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

    IntVar d1 = new IntVar(store, "c4_1_m", 1, 3);
    IntVar d2 = new IntVar(store, "c4_2_m", 1, 3);
    IntVar d3 = new IntVar(store, "c4_3_m", 1, 3);

    vars.add(d1);
    vars.add(d2);
    vars.add(d3);

    store.impose(new XneqY(d1, d2));
    store.impose(new XneqY(d2, d3));
    store.impose(new XneqY(d1, d3));

    int[] lista_4 = {6, 9, 12};

    store.impose(Element.choose(d1, lista_4, first[iIvor]));
    store.impose(Element.choose(d2, lista_4, last[iO_Rourke]));
    store.impose(Element.choose(d3, lista_4, sport[itennis]));

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

    int[] lista_9 = {1, 5, 9};

    store.impose(Element.choose(I_9_1, lista_9, first[iGriff]));
    store.impose(Element.choose(I_9_2, lista_9, last[iReede]));
    store.impose(Element.choose(I_9_3, lista_9, sport[iarchery]));

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

    IntVar w1 = new IntVar(store, "c10_1_x", 1, 12);
    IntVar w2 = new IntVar(store, "c10_2_x", 1, 12);
    IntVar w3 = new IntVar(store, "c10_3_x", 1, 12);

    vars.add(w1);
    vars.add(w2);
    vars.add(w3);

    store.impose(new XplusCeqZ(w1, 1, w2));
    store.impose(new XplusCeqZ(w1, 2, w3));

    IntVar[] lista_10 = {w1, w2, w3};

    store.impose(Element.choose(I_10_1, lista_10, first[iBrett]));
    store.impose(Element.choose(I_10_2, lista_10, first[iEd]));
    store.impose(Element.choose(I_10_3, lista_10, first[iLorenzo]));

    // 11. Ed, Uhler, and the croquet player were featured in consecutive
    // months, though not necessarily in that order.
    // Look at the description of clue no. 2.

    IntVar k1 = new IntVar(store, "c11_1_m", 1, 3);
    IntVar k2 = new IntVar(store, "c11_2_m", 1, 3);
    IntVar k3 = new IntVar(store, "c11_3_m", 1, 3);

    vars.add(k1);
    vars.add(k2);
    vars.add(k3);

    store.impose(new XneqY(k1, k2));
    store.impose(new XneqY(k2, k3));
    store.impose(new XneqY(k1, k3));

    IntVar q1 = new IntVar(store, "c11_1_x", 1, 12);
    IntVar q2 = new IntVar(store, "c11_2_x", 1, 12);
    IntVar q3 = new IntVar(store, "c11_3_x", 1, 12);

    vars.add(q1);
    vars.add(q2);
    vars.add(q3);

    store.impose(new XplusCeqZ(q1, 1, q2));
    store.impose(new XplusCeqZ(q1, 2, q3));

    IntVar[] lista_11 = {q1, q2, q3};

    store.impose(Element.choose(k1, lista_11, first[iEd]));
    store.impose(Element.choose(k2, lista_11, last[iUhler]));
    store.impose(Element.choose(k3, lista_11, sport[icroquet]));

    // 12. Dabney, Nelsen, and the lacrosse player were featured in April,
    // June, and August, in some order.
    // Look at the description of clue no. 1.

    IntVar l1 = new IntVar(store, "c12_1_m", 1, 3);
    IntVar l2 = new IntVar(store, "c12_2_m", 1, 3);
    IntVar l3 = new IntVar(store, "c12_3_m", 1, 3);

    vars.add(l1);
    vars.add(l2);
    vars.add(l3);

    store.impose(new XneqY(l1, l2));
    store.impose(new XneqY(l2, l3));
    store.impose(new XneqY(l1, l3));

    int[] lista_12 = {4, 6, 8};

    store.impose(Element.choose(l1, lista_12, first[iDabney]));
    store.impose(Element.choose(l2, lista_12, last[iNelsen]));
    store.impose(Element.choose(l3, lista_12, sport[ilacrosse]));

    // 13. Brett doesn't play lacrosse.

    store.impose(new XneqY(first[iBrett], sport[ilacrosse]));

    // 14. Dabney isn't Wang.

    store.impose(new XneqY(first[iDabney], last[iWang]));

    // 15. Antonio doesn't play hockey.

    store.impose(new XneqY(first[iAntonio], sport[ihockey]));

    // 16. The pole vaulter appeared sometime after the golfer.

    store.impose(new XgtY(sport[ivaulting], sport[igolf]));
  }

  /** It creates a model of this logic puzzle using mostly primitive constraints. */
  public void modelBasic() {

    store = new Store();
    vars = new ArrayList<>();

    IO.println("This program solves logic puzzle Calendar Men");

    String[] firstnameId = {
      "Antonio",
      "Brett",
      "Cliff",
      "Dabney",
      "Ed",
      "Francisco",
      "Griff",
      "Harry",
      "Ivor",
      "John",
      "Karl",
      "Lorentzo"
    };

    final int iAntonio = 0;
    final int iBrett = 1; /* iCliff = 2, */
    final int iDabney = 3;
    final int iEd = 4;
    final int iFrancisco = 5;
    final int iGriff = 6;
    final int iHarry = 7;
    final int iIvor = 8;
    final int iJohn = 9;
    final int iKarl = 10;
    final int iLorentzo = 11;

    String[] surnameId = {
      "Moross",
      "Nelsen",
      "ORourke",
      "Paulos",
      "Quarello",
      "Reede",
      "Sheldon",
      "Taylor",
      "Uhler",
      "Vickers",
      "Wang",
      "Xiao"
    };

    final int iMoross = 0;
    final int iNelsen = 1;
    final int iOrourke = 2;
    final int iPaulos = 3;
    final int iQuarello = 4;
    final int iReede = 5;
    final int iSheldon = 6;
    final int iTaylor = 7;
    final int iUhler = 8; /* iVickers = 9, */
    final int iWang = 10;
    final int iXiao = 11;

    String[] sportId = {
      "archery",
      "badmington",
      "croquet",
      "football",
      "golf",
      "hockey",
      "lacrosse",
      "p_vauliting",
      "rowing",
      "squash",
      "tennis",
      "volleyball"
    };

    final int iarchery = 0;
    final int ibadmington = 1;
    final int icroquet = 2;
    final int ifootball = 3;
    final int igolf = 4;
    final int ihockey = 5;
    final int ilacrosse = 6;
    final int ip_vauliting = 7;
    final int irowing = 8;
    final int isquash = 9;
    final int itennis = 10;
    final int ivolleyball = 11;

    IntVar[] firstname = createVariables(firstnameId);
    IntVar[] surname = createVariables(surnameId);
    IntVar[] sport = createVariables(sportId);

    store.impose(new Alldifferent(firstname));
    store.impose(new Alldifferent(surname));
    store.impose(new Alldifferent(sport));

    // 1. Francisco, Sheldon, and the volleyball player were featured in
    // April, July, and October, in some order.

    store.impose(new XneqY(firstname[iFrancisco], surname[iSheldon]));
    store.impose(new XneqY(firstname[iFrancisco], sport[ivolleyball]));
    store.impose(new XneqY(surname[iSheldon], sport[ivolleyball]));

    PrimitiveConstraint[] v11 = {
      new XeqC(firstname[iFrancisco], 4),
      new XeqC(firstname[iFrancisco], 7),
      new XeqC(firstname[iFrancisco], 10)
    };

    PrimitiveConstraint[] v12 = {
      new XeqC(surname[iSheldon], 4),
      new XeqC(surname[iSheldon], 7),
      new XeqC(surname[iSheldon], 10)
    };

    PrimitiveConstraint[] v13 = {
      new XeqC(sport[ivolleyball], 4),
      new XeqC(sport[ivolleyball], 7),
      new XeqC(sport[ivolleyball], 10)
    };

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
      new XplusCeqZ(surname[iMoross], 1, sport[ihockey])
    };

    PrimitiveConstraint[] v25 = {
      new XplusCeqZ(firstname[iKarl], 1, sport[ihockey]),
      new XplusCeqZ(sport[ihockey], 1, surname[iMoross])
    };

    PrimitiveConstraint[] v26 = {
      new XplusCeqZ(surname[iMoross], 1, firstname[iKarl]),
      new XplusCeqZ(firstname[iKarl], 1, sport[ihockey])
    };

    PrimitiveConstraint[] v27 = {
      new XplusCeqZ(surname[iMoross], 1, sport[ihockey]),
      new XplusCeqZ(sport[ihockey], 1, firstname[iKarl])
    };

    PrimitiveConstraint[] v28 = {
      new XplusCeqZ(sport[ihockey], 1, surname[iMoross]),
      new XplusCeqZ(surname[iMoross], 1, firstname[iKarl])
    };

    PrimitiveConstraint[] v29 = {
      new XplusCeqZ(sport[ihockey], 1, firstname[iKarl]),
      new XplusCeqZ(firstname[iKarl], 1, surname[iMoross])
    };

    PrimitiveConstraint[] v23 = {
      new And(v24), new And(v25), new And(v26), new And(v27), new And(v28), new And(v29)
    };
    store.impose(new Or(v23));

    // 3. Lorenzo appeared an even number of months after the squash player.

    IntVar offset1 = new IntVar(store, "offset1", 1, 5);
    IntVar offset2 = new IntVar(store, "offset2", 2, 10);
    store.impose(new XmulCeqZ(offset1, 2, offset2));

    store.impose(new XplusYeqZ(sport[isquash], offset2, firstname[iLorentzo]));

    // 4. Ivor, O'Rourke, and the tennis player were featured in June,
    // September, and December, in some order.

    store.impose(new XneqY(firstname[iIvor], surname[iOrourke]));
    store.impose(new XneqY(firstname[iIvor], sport[itennis]));
    store.impose(new XneqY(surname[iOrourke], sport[itennis]));

    PrimitiveConstraint[] v41 = {
      new XeqC(firstname[iIvor], 6), new XeqC(firstname[iIvor], 9), new XeqC(firstname[iIvor], 12)
    };

    PrimitiveConstraint[] v42 = {
      new XeqC(surname[iOrourke], 6),
      new XeqC(surname[iOrourke], 9),
      new XeqC(surname[iOrourke], 12)
    };

    PrimitiveConstraint[] v43 = {
      new XeqC(sport[itennis], 6), new XeqC(sport[itennis], 9), new XeqC(sport[itennis], 12)
    };

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

    PrimitiveConstraint[] v91 = {
      new XeqC(firstname[iGriff], 1), new XeqC(firstname[iGriff], 5), new XeqC(firstname[iGriff], 9)
    };

    PrimitiveConstraint[] v92 = {
      new XeqC(surname[iReede], 1), new XeqC(surname[iReede], 5), new XeqC(surname[iReede], 9)
    };

    PrimitiveConstraint[] v93 = {
      new XeqC(sport[iarchery], 1), new XeqC(sport[iarchery], 5), new XeqC(sport[iarchery], 9)
    };

    store.impose(new Or(v91));
    store.impose(new Or(v92));
    store.impose(new Or(v93));

    // 10. Brett, Ed, and Lorenzo were featured in consecutive months,
    // though not necessarily in that order.

    PrimitiveConstraint[] v100 = {
      new XplusCeqZ(firstname[iBrett], 1, firstname[iEd]),
      new XplusCeqZ(firstname[iEd], 1, firstname[iLorentzo])
    };

    PrimitiveConstraint[] v101 = {
      new XplusCeqZ(firstname[iBrett], 1, firstname[iLorentzo]),
      new XplusCeqZ(firstname[iLorentzo], 1, firstname[iEd])
    };

    PrimitiveConstraint[] v102 = {
      new XplusCeqZ(firstname[iEd], 1, firstname[iBrett]),
      new XplusCeqZ(firstname[iBrett], 1, firstname[iLorentzo])
    };

    PrimitiveConstraint[] v103 = {
      new XplusCeqZ(firstname[iEd], 1, firstname[iLorentzo]),
      new XplusCeqZ(firstname[iLorentzo], 1, firstname[iBrett])
    };

    PrimitiveConstraint[] v104 = {
      new XplusCeqZ(firstname[iLorentzo], 1, firstname[iEd]),
      new XplusCeqZ(firstname[iEd], 1, firstname[iBrett])
    };

    PrimitiveConstraint[] v105 = {
      new XplusCeqZ(firstname[iLorentzo], 1, firstname[iBrett]),
      new XplusCeqZ(firstname[iBrett], 1, firstname[iEd])
    };

    PrimitiveConstraint[] v106 = {
      new And(v100), new And(v101), new And(v102), new And(v103), new And(v104), new And(v105)
    };

    store.impose(new Or(v106));

    // 11. Ed, Uhler, and the croquet player were featured in consecutive
    // months, though not necessarily in that order.

    store.impose(new XneqY(surname[iUhler], firstname[iEd]));
    store.impose(new XneqY(surname[iUhler], sport[icroquet]));
    store.impose(new XneqY(firstname[iEd], sport[icroquet]));

    PrimitiveConstraint[] v111 = {
      new XplusCeqZ(firstname[iEd], 1, surname[iUhler]),
      new XplusCeqZ(surname[iUhler], 1, sport[icroquet])
    };

    PrimitiveConstraint[] v112 = {
      new XplusCeqZ(firstname[iEd], 1, sport[icroquet]),
      new XplusCeqZ(sport[icroquet], 1, surname[iUhler])
    };

    PrimitiveConstraint[] v113 = {
      new XplusCeqZ(surname[iUhler], 1, firstname[iEd]),
      new XplusCeqZ(firstname[iEd], 1, sport[icroquet])
    };

    PrimitiveConstraint[] v114 = {
      new XplusCeqZ(surname[iUhler], 1, sport[icroquet]),
      new XplusCeqZ(sport[icroquet], 1, firstname[iEd])
    };

    PrimitiveConstraint[] v115 = {
      new XplusCeqZ(sport[icroquet], 1, surname[iUhler]),
      new XplusCeqZ(surname[iUhler], 1, firstname[iEd])
    };

    PrimitiveConstraint[] v116 = {
      new XplusCeqZ(sport[icroquet], 1, firstname[iEd]),
      new XplusCeqZ(firstname[iEd], 1, surname[iUhler])
    };

    PrimitiveConstraint[] v110 = {
      new And(v111), new And(v112), new And(v113), new And(v114), new And(v115), new And(v116)
    };

    store.impose(new Or(v110));

    // 12. Dabney, Nelsen, and the lacrosse player were featured in April,
    // June, and August, in some order.

    store.impose(new XneqY(firstname[iDabney], surname[iNelsen]));
    store.impose(new XneqY(firstname[iDabney], sport[ilacrosse]));
    store.impose(new XneqY(surname[iNelsen], sport[ilacrosse]));

    PrimitiveConstraint[] v121 = {
      new XeqC(firstname[iDabney], 4),
      new XeqC(firstname[iDabney], 6),
      new XeqC(firstname[iDabney], 8)
    };

    PrimitiveConstraint[] v122 = {
      new XeqC(surname[iNelsen], 4), new XeqC(surname[iNelsen], 6), new XeqC(surname[iNelsen], 8)
    };

    PrimitiveConstraint[] v123 = {
      new XeqC(sport[ilacrosse], 4), new XeqC(sport[ilacrosse], 6), new XeqC(sport[ilacrosse], 8)
    };

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

  /** Creates variables for a given array of names. */
  private IntVar[] createVariables(String[] names) {
    IntVar[] vars = new IntVar[12];
    for (int i = 0; i < 12; i++) {
      vars[i] = new IntVar(store, names[i], 1, 12);
      this.vars.add(vars[i]);
    }
    return vars;
  }
}
