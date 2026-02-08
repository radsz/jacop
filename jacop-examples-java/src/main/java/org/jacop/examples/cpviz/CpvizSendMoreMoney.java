/*
 * CpvizSendMoreMoney.java
 * This file is part of org.jacop.
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

package org.jacop.examples.cpviz;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.TraceGenerator;

/**
 * It shows how to visualize solving process for SendMoreMoney problem.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class CpvizSendMoreMoney {

  Store store = new Store();
  List<IntVar> vars;
  Search<IntVar> search;

  // Find for the equation on the left
  // what digits are represented by the letters
  // different letters represent different digits

  // SEND 9567
  // +MORE =======> +1085
  // MONEY 10652

  /*
   * This creates a standard model using simple basic constraints.
   */

  static void main(String[] args) {

    CpvizSendMoreMoney exampleGlobal = new CpvizSendMoreMoney();

    exampleGlobal.modelGlobal();
  }

  /** Creates the constraint model for the SEND+MORE=MONEY problem using basic constraints. */
  public void model() {

    vars = new ArrayList<>();
    store = new Store();

    // Creating an array for IntVars
    IntVar[] letters = new IntVar[8];

    // Creating IntVar (finite domain variables)
    // with indexes for accessing
    final int iS = 0;
    final int iE = 1;
    final int iN = 2;
    final int iD = 3;
    final int iM = 4;
    final int iO = 5;
    final int iR = 6;
    final int iY = 7;
    letters[iS] = new IntVar(store, "S", 0, 9);
    letters[iE] = new IntVar(store, "E", 0, 9);
    letters[iN] = new IntVar(store, "N", 0, 9);
    letters[iD] = new IntVar(store, "D", 0, 9);
    letters[iM] = new IntVar(store, "M", 0, 9);
    letters[iO] = new IntVar(store, "O", 0, 9);
    letters[iR] = new IntVar(store, "R", 0, 9);
    letters[iY] = new IntVar(store, "Y", 0, 9);

    vars.addAll(Arrays.asList(letters));

    // Imposing inequalities constraints between letters
    // This nested loop imposes inequality constraint
    // for all pairs of letters
    // Since there are 8 different letters this will create
    // 0+1+2+3+4+5+6+7 = 28 inequality constraints

    for (int i = 0; i < letters.length; i++) {
      for (int j = i - 1; j >= 0; j--) {
        store.impose(new XneqY(letters[j], letters[i]));
      }
    }

    //     // Main equation of the problem SEND + MORE = MONEY
    //     store.impose(new XplusYeqZ(valueSend, valueMore, valueMoney));

    // Since S is the first digit of SEND
    // and M is the first digit of MORE or MONEY
    // both letters can not be equal to zero
    store.impose(new XneqC(letters[iS], 0));
    store.impose(new XneqC(letters[iM], 0));

    // 1000*S + 91*E - 90*N + D - 9000*M - 900*O + 10*R = Y
    IntVar s1 = new IntVar(store, 0, 9000);
    store.impose(new XmulCeqZ(letters[iS], 1000, s1));
    IntVar s2 = new IntVar(store, 0, 1000);
    store.impose(new XmulCeqZ(letters[iE], 91, s2));
    IntVar s3 = new IntVar(store, -1000, 0);
    store.impose(new XmulCeqZ(letters[iN], -90, s3));
    IntVar s4 = new IntVar(store, -100000, 0);
    store.impose(new XmulCeqZ(letters[iM], -9000, s4));
    IntVar s5 = new IntVar(store, -100000, 0);
    store.impose(new XmulCeqZ(letters[iO], -900, s5));
    IntVar s6 = new IntVar(store, 0, 100);
    store.impose(new XmulCeqZ(letters[iR], 10, s6));

    IntVar t1 = new IntVar(store, -100000, 100000);
    store.impose(new XplusYeqZ(s1, s2, t1));
    IntVar t2 = new IntVar(store, -100000, 100000);
    store.impose(new XplusYeqZ(t1, s3, t2));
    IntVar t3 = new IntVar(store, -100000, 100000);
    store.impose(new XplusYeqZ(t2, s4, t3));
    IntVar t4 = new IntVar(store, -100000, 100000);
    store.impose(new XplusYeqZ(t3, s5, t4));
    IntVar t5 = new IntVar(store, -100000, 100000);
    store.impose(new XplusYeqZ(t4, s6, t5));
    store.impose(new XplusYeqZ(t5, letters[iD], letters[iY]));

    store.consistency();
    //       System.out.println(vars);
    //   }

    //   /**
    //    * This creates a standard search, which looks for a single solution.
    //    */

    //   public boolean search() {

    SelectChoicePoint<IntVar> varSelect =
        new SimpleSelect<>(vars.toArray(new IntVar[1]), null, new IndomainMin<>());

    search = new DepthFirstSearch<>();

    // Trace --->

    TraceGenerator<IntVar> select = new TraceGenerator<>(search, varSelect);

    //     TraceGenerator<IntVar> select = new TraceGenerator<IntVar>(varSelect, true);
    select.addTracedVar(letters[iE]);

    //     search.setConsistencyListener((ConsistencyListener)select);
    //     search.setExitChildListener((ExitChildListener<IntVar>)select);
    //   search.setExitListener((ExitListener)select);
    // <---

    search.labeling(store, select);

    //     return result;

  }

  /**
   * Creates the constraint model for the SEND+MORE=MONEY problem using global constraints. This
   * provides more concise modeling using Alldifferent and LinearInt constraints.
   */
  public void modelGlobal() {

    vars = new ArrayList<>();
    store = new Store();

    // Creating IntVar (finite domain variables)
    IntVar s = new IntVar(store, "S", 0, 9);
    IntVar e = new IntVar(store, "E", 0, 9);
    IntVar n = new IntVar(store, "N", 0, 9);
    IntVar d = new IntVar(store, "D", 0, 9);
    IntVar m = new IntVar(store, "M", 0, 9);
    IntVar o = new IntVar(store, "O", 0, 9);
    IntVar r = new IntVar(store, "R", 0, 9);
    IntVar y = new IntVar(store, "Y", 0, 9);

    IntVar valueSend = new IntVar(store, "v(SEND)", 0, 9999);
    IntVar valueMore = new IntVar(store, "v(MORE)", 0, 9999);
    IntVar valueMoney = new IntVar(store, "v(MONEY)", 0, 99999);

    // Creating arrays for IntVars
    IntVar[] digits = {s, e, n, d, m, o, r, y};
    IntVar[] send = {s, e, n, d, valueSend};
    IntVar[] more = {m, o, r, e, valueMore};
    IntVar[] money = {m, o, n, e, y, valueMoney};

    vars.addAll(Arrays.asList(digits));

    // Imposing inequalities constraints between letters
    // Only one global constraint
    store.impose(new Alldifferent(digits));

    int[] weights5 = {10000, 1000, 100, 10, 1, -1};
    int[] weights4 = {1000, 100, 10, 1, -1};

    // Constraints for getting value for words
    // SEND = 1000 * S + 100 * E + N * 10 + D * 1
    // MORE = 1000 * M + 100 * O + R * 10 + E * 1
    // MONEY = 10000 * M + 1000 * O + 100 * N + E * 10 + Y * 1
    store.impose(new LinearInt(send, weights4, "==", 0));
    store.impose(new LinearInt(more, weights4, "==", 0));
    // store.impose(new SumWeight(money, weights5, valueMoney));
    store.impose(new LinearInt(money, weights5, "==", 0));

    // Main equation of the problem SEND + MORE = MONEY
    store.impose(new XplusYeqZ(valueSend, valueMore, valueMoney));

    //     // 1000*S + 91*E - 90*N + D - 9000*M - 900*O + 10*R = Y
    //     int[] w = {1000, 91, -90, 1, -9000, -900, 10};
    //     IntVar[] vs = {s, e, n, d, m, o, r};
    //     store.impose(new SumWeight(vs, w, y));

    // Since S is the first digit of SEND
    // and M is the first digit of MORE or MONEY
    // both letters can not be equal to zero
    store.impose(new XneqC(s, 0));
    store.impose(new XneqC(m, 0));

    store.consistency();

    SelectChoicePoint<IntVar> varSelect =
        new SimpleSelect<>(vars.toArray(new IntVar[1]), null, new IndomainMin<>());

    search = new DepthFirstSearch<>();

    // Trace --->
    TraceGenerator<IntVar> select =
        new TraceGenerator<>(search, varSelect, new IntVar[] {s, e, n, d, m, o, r, y});

    //     TraceGenerator<IntVar> select = new TraceGenerator<IntVar>(varSelect, true, new IntVar[]
    // {s, e, n, d, m, o, r, y});

    //     search.setConsistencyListener((ConsistencyListener)select);
    //      search.setExitChildListener((ExitChildListener<IntVar>)select);
    //   search.setExitListener((ExitListener)select);
    // <---

    search.labeling(store, select);

    //     return result;

  }
}
