/*
 * Loan.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.examples.floats;

import lombok.extern.slf4j.Slf4j;
import org.jacop.core.Store;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.PrintOutListener;

/** Example for loan calculation using float constraints. */
@Slf4j
public class Loan {

  /**
   * It executes the program which computes values for tan(x) = -x.
   *
   * @param args no arguments
   */
  static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    Loan example = new Loan();

    if (args.length != 4) {
      log.info("Wring number of parameters");
    } else {
      double i = Double.parseDouble(args[0]);
      double p = Double.parseDouble(args[1]);
      double r = Double.parseDouble(args[2]);
      double b4 = Double.parseDouble(args[3]);

      example.loan(i, p, r, b4);
    }
  }

  /**
   * Models and solves a loan payment problem over four quarters.
   *
   * @param i the interest rate
   * @param p the principal initially borrowed (0.0 if unknown)
   * @param r the quarterly repayment (0.0 if unknown)
   * @param b4 the balance owing at end (negative value if unknown)
   */
  public void loan(double i, double p, double r, double b4) {

    // ￼￼￼LOAN1 I = 0.04;
    //            P = 1000.0;
    //            R = 260.0;
    //            result B4 = 65.78
    //             P = 1000.0;
    //             B4 = 0.0;
    //             result R=275.49 (precision 1e-11)
    //             R = 250.0;
    //             B4 = 0.0;
    //        result P = 907.47 (precision 1e-4)

    log.info(
        "\nProgram to solve loan payments under four quaeter\nI- interest rate, P- principal initially borrowed\n"
            + "R- quarterly repayment and B4- balance owing at end\nParameters:");

    Store store = new Store();

    FloatDomain.setPrecision(1e-13);

    FloatVar one = new FloatVar(store, "1.0", 1.0, 1.0);

    FloatVar repayment; // quarterly repayment
    if (r != 0.0) {
      repayment = new FloatVar(store, "R", r, r);
      log.info("R = " + r);
    } else {
      repayment = new FloatVar(store, "R", FloatDomain.MIN_FLOAT, FloatDomain.MAX_FLOAT);
      log.info("R = ?");
    }

    FloatVar principal; // principal initially borrowed
    if (p != 0.0) {
      principal = new FloatVar(store, "P", p, p);
      log.info("P = " + p);
    } else {
      principal = new FloatVar(store, "P", FloatDomain.MIN_FLOAT, FloatDomain.MAX_FLOAT);
      log.info("P = ?");
    }

    FloatVar interestRate = new FloatVar(store, "I", i, i); // interest rate

    FloatVar balance1 =
        new FloatVar(
            store, "B1", FloatDomain.MIN_FLOAT, FloatDomain.MAX_FLOAT); // balance after one quarter

    FloatVar balance4; // balance owing at end
    if (b4 >= 0.0) {
      balance4 = new FloatVar(store, "B4", b4, b4);
      log.info("B4 = " + b4);
    } else {
      balance4 = new FloatVar(store, "B4", FloatDomain.MIN_FLOAT, FloatDomain.MAX_FLOAT);
      log.info("B4 = ?");
    }

    FloatVar t1 = new FloatVar(store, "t1", 1.0, 2.0);
    store.impose(new PplusQeqR(one, interestRate, t1));
    FloatVar t2 = new FloatVar(store, "t2", FloatDomain.MIN_FLOAT, FloatDomain.MAX_FLOAT);
    store.impose(new PmulQeqR(principal, t1, t2));
    FloatVar negRepayment =
        new FloatVar(store, "negR", FloatDomain.MIN_FLOAT, FloatDomain.MAX_FLOAT);
    FloatVar zero = new FloatVar(store, "0.0", 0.0, 0.0);
    store.impose(new PplusQeqR(repayment, negRepayment, zero));
    store.impose(new PplusQeqR(t2, negRepayment, balance1));

    FloatVar t3 = new FloatVar(store, "t3", FloatDomain.MIN_FLOAT, FloatDomain.MAX_FLOAT);
    store.impose(new PmulQeqR(balance1, t1, t3));
    FloatVar balance2 =
        new FloatVar(
            store,
            "B2",
            FloatDomain.MIN_FLOAT,
            FloatDomain.MAX_FLOAT); // balance after two quarters
    store.impose(new PplusQeqR(t3, negRepayment, balance2));

    FloatVar t4 = new FloatVar(store, "t4", FloatDomain.MIN_FLOAT, FloatDomain.MAX_FLOAT);
    store.impose(new PmulQeqR(balance2, t1, t4));
    FloatVar balance3 =
        new FloatVar(
            store,
            "B3",
            FloatDomain.MIN_FLOAT,
            FloatDomain.MAX_FLOAT); // balance after three quarters
    store.impose(new PplusQeqR(t4, negRepayment, balance3));

    FloatVar t5 = new FloatVar(store, "t5", FloatDomain.MIN_FLOAT, FloatDomain.MAX_FLOAT);
    store.impose(new PmulQeqR(balance3, t1, t5));
    store.impose(new PplusQeqR(t5, negRepayment, balance4));

    // solve minimize cost;
    DepthFirstSearch<FloatVar> label = new DepthFirstSearch<>();
    SplitSelectFloat<FloatVar> s =
        new SplitSelectFloat<>(
            store,
            new FloatVar[] {balance1, balance2, balance3, balance4, principal, repayment},
            null);
    // s.leftFirst = false;

    label.setSolutionListener(new PrintOutListener<>());

    label.labeling(store, s);

    log.info(balance4 + "\n" + principal + "\n" + repayment);

    log.info("Precision = " + FloatDomain.precision());
  }
}
