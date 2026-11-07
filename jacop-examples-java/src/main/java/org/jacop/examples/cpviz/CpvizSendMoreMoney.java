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
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.examples.fd.SendMoreMoney;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.TraceGenerator;

/**
 * It shows how to visualize solving process for SendMoreMoney problem.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class CpvizSendMoreMoney extends SendMoreMoney {

  static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    CpvizSendMoreMoney exampleGlobal = new CpvizSendMoreMoney();

    exampleGlobal.modelGlobal();
  }

  /** Creates the constraint model for the SEND+MORE=MONEY problem using basic constraints. */
  @Override
  public void model() {

    vars = new ArrayList<>();
    store = new org.jacop.core.Store();

    final int iS = 0;
    final int iE = 1;
    final int iN = 2;
    final int iD = 3;
    final int iM = 4;
    final int iO = 5;
    final int iR = 6;
    final int iY = 7;

    IntVar[] letters = new IntVar[8];
    letters[iS] = new IntVar(store, "S", 0, 9);
    letters[iE] = new IntVar(store, "E", 0, 9);
    letters[iN] = new IntVar(store, "N", 0, 9);
    letters[iD] = new IntVar(store, "D", 0, 9);
    letters[iM] = new IntVar(store, "M", 0, 9);
    letters[iO] = new IntVar(store, "O", 0, 9);
    letters[iR] = new IntVar(store, "R", 0, 9);
    letters[iY] = new IntVar(store, "Y", 0, 9);

    vars.addAll(Arrays.asList(letters));

    for (int i = 0; i < letters.length; i++) {
      for (int j = i - 1; j >= 0; j--) {
        store.impose(new XneqY(letters[j], letters[i]));
      }
    }

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

    SelectChoicePoint<IntVar> varSelect =
        new SimpleSelect<>(vars.toArray(IntVar[]::new), null, new IndomainMin<>());

    searchLabel = new DepthFirstSearch<>();

    TraceGenerator<IntVar> traceSelect = new TraceGenerator<>(searchLabel, varSelect);
    traceSelect.addTracedVar(letters[iE]);

    searchLabel.labeling(store, traceSelect);
  }

  /**
   * Creates the constraint model for the SEND+MORE=MONEY problem using global constraints. This
   * provides more concise modeling using Alldiff and LinearInt constraints.
   */
  public void modelGlobal() {

    buildModel();
    store.consistency();

    SelectChoicePoint<IntVar> varSelect =
        new SimpleSelect<>(vars.toArray(IntVar[]::new), null, new IndomainMin<>());

    searchLabel = new DepthFirstSearch<>();

    TraceGenerator<IntVar> traceSelect =
        new TraceGenerator<>(searchLabel, varSelect, vars.toArray(IntVar[]::new));

    searchLabel.labeling(store, traceSelect);
  }
}
