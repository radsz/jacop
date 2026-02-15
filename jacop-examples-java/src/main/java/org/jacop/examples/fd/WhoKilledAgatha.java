/*
 * WhoKilledAgatha.java
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
import java.util.Arrays;
import org.jacop.constraints.Eq;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XlteqC;
import org.jacop.core.Domain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;

/**
 * Who killed agatha? (The Dreadsbury Mansion Murder Mystery).
 *
 * <p>This is a standard benchmark for theorem proving. <a
 * href="http://www.lsv.ens-cachan.fr/~goubault/H1.dist/H1.1/Doc/h1003.html">...</a> """ Someone in
 * Dreadsbury Mansion killed Aunt Agatha. Agatha, the butler, and Charles live in Dreadsbury
 * Mansion, and are the only ones to live there. A killer always hates, and is no richer than his
 * victim. Charles hates noone that Agatha hates. Agatha hates everybody except the butler. The
 * butler hates everyone not richer than Aunt Agatha. The butler hates everyone whom Agatha hates.
 * Noone hates everyone. Who killed Agatha? """
 *
 * <p>Originally from F. J. Pelletier: Seventy-five problems for testing automatic theorem provers.
 * Journal of Automated Reasoning, 2: 191â€“216, 1986.
 *
 * <p>Compare with the following models: - MiniZinc: <a
 * href="http://www.hakank.org/minizinc/who_killed_agatha.mzn">...</a> - Comet: <a
 * href="http://www.hakank.org/comet/who_killed_agatha.mzn">...</a> - Gecode: <a
 * href="http://www.hakank.org/gecode/who_killed_agatha.cpp">...</a>
 *
 * <p>This Choco model was created by Hakan Kjellerstrand (hakank@bonetmail.com) Also, see my Choco
 * page: <a href="http://www.hakank.org/choco/">...</a>
 *
 * <p>This JaCoP model was created by Hakan Kjellerstrand (hakank@bonetmail.com) <a
 * href="http://www.hakank.org/JaCoP/">...</a> .
 *
 * @author Hakan Kjellerstrand and Radoslaw Szymanek
 * @version 5.0
 */
public class WhoKilledAgatha extends ExampleFd {

  /**
   * It runs the program which solves the logic puzzle "Who killed Agatha".
   *
   * @param args parameters (none)
   */
  static void main(String[] args) {

    WhoKilledAgatha example = new WhoKilledAgatha();
    example.model();

    if (example.search()) {
      IO.println("Solution(s) found");
    }
  } // end main

  /** Imposes richer symmetry: if i is richer than j then j is not richer than i. */
  private void imposeRicherSymmetry(IntVar[][] richer, int n) {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (i != j) {
          store.impose(new Eq(new XeqC(richer[i][j], 1), new XeqC(richer[j][i], 0)));
        }
      }
    }
  }

  /** Creates the constraint model for the "Who Killed Agatha" logic puzzle. */
  @Override
  public void model() {

    int n = 3;
    store = new Store();

    IntVar the_killer = new IntVar(store, "the_killer", 0, n - 1);

    final int agatha = 0;
    final int butler = 1;
    final int charles = 2;

    IntVar[][] hates = new IntVar[n][n];
    IntVar[][] richer = new IntVar[n][n];
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        hates[i][j] = new IntVar(store, "hates:" + i + "->" + j, 0, 1);
        richer[i][j] = new IntVar(store, "richer:" + i + "->" + j, 0, 1);
      }
    }

    vars = new ArrayList<>();

    // "A killer always hates, and is no richer than his victim."
    for (int i = 0; i < n; i++) {
      store.impose(new IfThen(new XeqC(the_killer, i), new XeqC(hates[i][agatha], 1)));
      store.impose(new IfThen(new XeqC(the_killer, i), new XeqC(richer[i][agatha], 0)));
    }

    for (int i = 0; i < n; i++) {
      store.impose(new XeqC(richer[i][i], 0));
    }

    imposeRicherSymmetry(richer, n);

    // "Agatha hates everybody except the butler. "
    store.impose(new XeqC(hates[agatha][charles], 1));
    store.impose(new XeqC(hates[agatha][agatha], 1));
    store.impose(new XeqC(hates[agatha][butler], 0));

    for (int i = 0; i < n; i++) {
      store.impose(new IfThen(new XeqC(hates[agatha][i], 1), new XeqC(hates[charles][i], 0)));
    }

    for (int i = 0; i < n; i++) {
      store.impose(new IfThen(new XeqC(richer[i][agatha], 0), new XeqC(hates[butler][i], 1)));
    }

    for (int i = 0; i < n; i++) {
      store.impose(new IfThen(new XeqC(hates[agatha][i], 1), new XeqC(hates[butler][i], 1)));
    }

    vars.add(the_killer);
    for (int i = 0; i < n; i++) {
      vars.addAll(Arrays.asList(hates[i]).subList(0, n));
    }
    for (int i = 0; i < n; i++) {
      vars.addAll(Arrays.asList(richer[i]).subList(0, n));
    }

    for (int i = 0; i < n; i++) {
      IntVar a_sum = new IntVar(store, "a_sum" + i, 0, n);
      store.impose(new SumInt(hates[i], "==", a_sum));
      store.impose(new XlteqC(a_sum, 2));
      vars.add(a_sum);
    }
  }

  @Override
  public boolean search() {

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]), new SmallestDomain<>(), new IndomainMin<>());

    searchLabel = new DepthFirstSearch<>();
    searchLabel.getSolutionListener().searchAll(true);
    searchLabel.getSolutionListener().recordSolutions(true);
    boolean result = searchLabel.labeling(store, select);

    // output
    if (result) {

      int numSolutions = searchLabel.getSolutionListener().solutionsNo();

      IO.println("Number of Solutions: " + numSolutions);

      for (int s = 1; s <= numSolutions; s++) {
        Domain[] res = searchLabel.getSolutionListener().getSolution(s);
        int len = res.length;

        IO.println("the_killer: " + res[0]);

        // print the result
        for (Domain re : res) {
          IO.print(re + " ");
        }
        IO.println();
      }

    } else {

      IO.println("No solution.");
    }

    return result;
  }
} // end class
