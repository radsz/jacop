/*
 * SendMoreMoney.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.examples.fd;

import java.util.ArrayList;
import org.jacop.constraints.*;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.*;

/**
 * It is a simple arithmetic logic puzzle, where SEND+MORE=MONEY.
 *
 * <p>Find for the equation on the left what digits are represented by the letters different letters
 * represent different digits
 *
 * <p>SEND 9567 +MORE ======={@literal >}+1085 MONEY 10652
 *
 * @author Radoslaw Szymanek
 * @version 4.10
 */
public class SendMoreMoney extends ExampleFD {

  /*
   * This creates a standard model using simple basic constraints.
   */

  /**
   * It executes the program to solve this simple logic puzzle.
   *
   * @param args no arguments used.
   */
  public static void main(String args[]) {

    SendMoreMoney exampleBasic = new SendMoreMoney();

    exampleBasic.modelBasic();

    if (exampleBasic.search()) IO.println("Solution found.");

    SendMoreMoney exampleGlobal = new SendMoreMoney();

    exampleGlobal.model();

    if (exampleGlobal.search()) IO.println("Solution found.");
  }

  /**
   * 1. Every CP program consists of two parts. The first one is a model and the second one is the
   * specification of the search.
   *
   * <p>The model consists of variables and constraints.
   */
  public void modelBasic() {

    vars = new ArrayList<IntVar>();

    store = new Store();

    // Creating an array for FDVs
    IntVar letters[] = new IntVar[8];

    // Creating FDV (finite domain variables)
    // with indexes for accessing
    int iS = 0, iE = 1, iN = 2, iD = 3;
    int iM = 4, iO = 5, iR = 6, iY = 7;

    letters[iS] = new IntVar(store, "S", 0, 9);
    letters[iE] = new IntVar(store, "E", 0, 9);
    letters[iN] = new IntVar(store, "N", 0, 9);
    letters[iD] = new IntVar(store, "D", 0, 9);
    letters[iM] = new IntVar(store, "M", 0, 9);
    letters[iO] = new IntVar(store, "O", 0, 9);
    letters[iR] = new IntVar(store, "R", 0, 9);
    letters[iY] = new IntVar(store, "Y", 0, 9);

    for (IntVar x : letters) vars.add(x);

    // Imposing inequalities constraints between letters
    // This nested loop imposes inequality constraint
    // for all pairs of letters
    // Since there are 8 different letters this will create
    // 0+1+2+3+4+5+6+7 = 28 inequality constraints

    for (int i = 0; i < letters.length; i++)
      for (int j = i - 1; j >= 0; j--) store.impose(new XneqY(letters[j], letters[i]));

    // Each letter is SEND number has a different value
    // which depends on the position of this letter
    // SEND = 1000 * S + 100 * E + N * 10 + D * 1
    IntVar numbersSEND[] = new IntVar[4];
    IntVar valueSEND = new IntVar(store, "SEND", 0, 9999);

    // Creates FDV for each position in SEND with
    // appropriate domain, they all start with zero
    // since a letter could be zero and the position
    // value is also zero
    numbersSEND[0] = new IntVar(store, "v(SinSEND)", 0, 9000);
    numbersSEND[1] = new IntVar(store, "v(EinSEND)", 0, 900);
    numbersSEND[2] = new IntVar(store, "v(NinSEND)", 0, 90);
    numbersSEND[3] = new IntVar(store, "v(DinSEND)", 0, 9);

    // Creates and imposes constraints which enforce
    // relationship between letter and value of its position
    // in the number SEND
    store.impose(new XmulCeqZ(letters[iS], 1000, numbersSEND[0]));
    store.impose(new XmulCeqZ(letters[iE], 100, numbersSEND[1]));
    store.impose(new XmulCeqZ(letters[iN], 10, numbersSEND[2]));
    store.impose(new XmulCeqZ(letters[iD], 1, numbersSEND[3]));

    // Succesively adds position to get value of the number SEND
    IntVar valueSEinSEND = new IntVar(store, "v(SEinSEND)", 0, 9900);
    IntVar valueNDinSEND = new IntVar(store, "v(NDinSEND)", 0, 99);

    store.impose(new XplusYeqZ(numbersSEND[0], numbersSEND[1], valueSEinSEND));
    store.impose(new XplusYeqZ(numbersSEND[2], numbersSEND[3], valueNDinSEND));
    store.impose(new XplusYeqZ(valueSEinSEND, valueNDinSEND, valueSEND));

    // Each letter in MORE number has a different value
    // which depends on the position of this letter
    // MORE = 1000 * M + 100 * O + R * 10 + E * 1
    IntVar numbersMORE[] = new IntVar[4];
    IntVar valueMORE = new IntVar(store, "MORE", 0, 9999);

    // Creates FDV for each position in MORE with
    // appropriate domain, they all start with zero
    // since a letter could be zero and the position
    // value is also zero
    numbersMORE[0] = new IntVar(store, "v(MinMORE)", 0, 9000);
    numbersMORE[1] = new IntVar(store, "v(OinMORE)", 0, 900);
    numbersMORE[2] = new IntVar(store, "v(RinMORE)", 0, 90);
    numbersMORE[3] = new IntVar(store, "v(EinMORE)", 0, 9);

    // Creates and imposes constraints which enforce
    // relationship between letter and value of its position
    // in the number MORE
    store.impose(new XmulCeqZ(letters[iM], 1000, numbersMORE[0]));
    store.impose(new XmulCeqZ(letters[iO], 100, numbersMORE[1]));
    store.impose(new XmulCeqZ(letters[iR], 10, numbersMORE[2]));
    store.impose(new XmulCeqZ(letters[iE], 1, numbersMORE[3]));

    // Successively adds position to get value of the number MORE
    IntVar valueMOinMORE = new IntVar(store, "v(MOinMORE)", 0, 9900);
    IntVar valueREinMORE = new IntVar(store, "v(REinMORE)", 0, 99);

    store.impose(new XplusYeqZ(numbersMORE[0], numbersMORE[1], valueMOinMORE));
    store.impose(new XplusYeqZ(numbersMORE[2], numbersMORE[3], valueREinMORE));
    store.impose(new XplusYeqZ(valueMOinMORE, valueREinMORE, valueMORE));

    // Each letter in MONEY number has a different value
    // which depends on the position of this letter
    // MONEY = 10000 * M + 1000 * O + N * 100 + E * 10 + Y * 1
    IntVar numbersMONEY[] = new IntVar[5];
    IntVar valueMONEY = new IntVar(store, "MONEY", 0, 99999);

    // Creates FDV for each position in MONEY with
    // appropriate domain, they all start with zero
    // since a letter could be zero and the position
    // value is also zero
    numbersMONEY[0] = new IntVar(store, "v(MinMONEY)", 0, 90000);
    numbersMONEY[1] = new IntVar(store, "v(OinMONEY)", 0, 9000);
    numbersMONEY[2] = new IntVar(store, "v(NinMONEY)", 0, 900);
    numbersMONEY[3] = new IntVar(store, "v(EinMONEY)", 0, 90);
    numbersMONEY[4] = new IntVar(store, "v(YinMONEY)", 0, 9);

    store.impose(new XmulCeqZ(letters[iM], 10000, numbersMONEY[0]));
    store.impose(new XmulCeqZ(letters[iO], 1000, numbersMONEY[1]));
    store.impose(new XmulCeqZ(letters[iN], 100, numbersMONEY[2]));
    store.impose(new XmulCeqZ(letters[iE], 10, numbersMONEY[3]));
    store.impose(new XmulCeqZ(letters[iY], 1, numbersMONEY[4]));

    // Successively adds position to get value of the number MONEY
    IntVar valueMOinMONEY = new IntVar(store, "v(MOinMONEY)", 0, 99000);
    IntVar valueNEinMONEY = new IntVar(store, "v(NEinMONEY)", 0, 990);
    IntVar valueMONEinMONEY = new IntVar(store, "v(MONEinMONEY)", 0, 99990);

    store.impose(new XplusYeqZ(numbersMONEY[0], numbersMONEY[1], valueMOinMONEY));
    store.impose(new XplusYeqZ(numbersMONEY[2], numbersMONEY[3], valueNEinMONEY));
    store.impose(new XplusYeqZ(valueMOinMONEY, valueNEinMONEY, valueMONEinMONEY));
    store.impose(new XplusYeqZ(valueMONEinMONEY, numbersMONEY[4], valueMONEY));

    // Main equation of the problem SEND + MORE = MONEY
    store.impose(new XplusYeqZ(valueSEND, valueMORE, valueMONEY));

    // Since S is the first digit of SEND
    // and M is the first digit of MORE or MONEY
    // both letters can not be equal to zero
    store.impose(new XneqC(letters[iS], 0));
    store.impose(new XneqC(letters[iM], 0));
  }

  /** This creates a standard search, which looks for a single solution. */
  @Override
  public boolean search() {

    /*
    	store.consistency();
    	store.print();
    */

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<IntVar>(
            vars.toArray(new IntVar[1]), new SmallestDomain<IntVar>(), new IndomainMin<IntVar>());

    search = new DepthFirstSearch<IntVar>();

    boolean result = search.labeling(store, select);

    return result;
  }

  /**
   * 1. Every CP program consists of two parts. The first one is a model and the second one is the
   * specification of the search. This creates a model which uses global constraints to provide
   * consize modeling. The model consists of variables and constraints.
   */
  @Override
  public void model() {

    vars = new ArrayList<IntVar>();

    store = new Store();

    IntVar s = new IntVar(store, "S", 0, 9);
    IntVar e = new IntVar(store, "E", 0, 9);
    IntVar n = new IntVar(store, "N", 0, 9);
    IntVar d = new IntVar(store, "D", 0, 9);
    IntVar m = new IntVar(store, "M", 0, 9);
    IntVar o = new IntVar(store, "O", 0, 9);
    IntVar r = new IntVar(store, "R", 0, 9);
    IntVar y = new IntVar(store, "Y", 0, 9);

    IntVar valueSEND = new IntVar(store, "v(SEND)", 0, 9999);
    IntVar valueMORE = new IntVar(store, "v(MORE)", 0, 9999);
    IntVar valueMONEY = new IntVar(store, "v(MONEY)", 0, 99999);

    // Creating arrays for FDVs
    IntVar digits[] = {s, e, n, d, m, o, r, y};
    IntVar send[] = {s, e, n, d};
    IntVar more[] = {m, o, r, e};
    IntVar money[] = {m, o, n, e, y};

    for (IntVar v : digits) vars.add(v);

    store.impose(new Alldiff(digits));

    int[] weights5 = {10000, 1000, 100, 10, 1};
    int[] weights4 = {1000, 100, 10, 1};

    store.impose(new LinearInt(send, weights4, "==", valueSEND));
    // store.impose(new SumWeight(send, weights4, valueSEND));
    store.impose(new LinearInt(more, weights4, "==", valueMORE));
    // store.impose(new SumWeight(more, weights4, wvalueMORE));
    store.impose(new LinearInt(money, weights5, "==", valueMONEY));
    // store.impose(new SumWeight(money, weights5, valueMONEY));

    store.impose(new XplusYeqZ(valueSEND, valueMORE, valueMONEY));

    int[] weightsImplied = {1000, 91, 10, 1, -9000, -900, -90};
    IntVar[] varsImplied = {s, e, r, d, m, o, n};
    store.impose(new LinearInt(varsImplied, weightsImplied, "==", y));
    // store.impose(new SumWeight(varsImplied, weightsImplied, y));

    store.impose(new XneqC(s, 0));
    store.impose(new XneqC(m, 0));
  }
}
