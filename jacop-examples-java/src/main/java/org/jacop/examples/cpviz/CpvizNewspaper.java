/*
 * CpvizNewspaper.java
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

import org.jacop.core.IntVar;
import org.jacop.examples.fd.Newspaper;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestMax;
import org.jacop.search.TraceGenerator;

/**
 * It is a simple newspaper reading job-shop like scheduling problem with visualization.
 *
 * <p>Uses the same model as {@link Newspaper} but runs search with TraceGenerator for
 * visualization.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class CpvizNewspaper extends Newspaper {

  /**
   * It executes the program which solves this newspaper problem with visualization.
   *
   * @param args no argument is used.
   */
  static void main(String[] args) {

    CpvizNewspaper example = new CpvizNewspaper();

    example.model();
  }

  @Override
  public void model() {

    cost = buildModel(250);

    SelectChoicePoint<IntVar> varSelect =
        new SimpleSelect<>(vars.toArray(new IntVar[0]), new SmallestMax<>(), new IndomainMin<>());

    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();

    IntVar[] abcd = new IntVar[16];
    int i = 0;
    for (IntVar v : algy) {
      abcd[i++] = v;
    }
    for (IntVar v : bertie) {
      abcd[i++] = v;
    }
    for (IntVar v : charlie) {
      abcd[i++] = v;
    }
    for (IntVar v : digby) {
      abcd[i++] = v;
    }

    TraceGenerator<IntVar> select = new TraceGenerator<>(search, varSelect, abcd);

    search.labeling(store, select, cost);
  }
}
