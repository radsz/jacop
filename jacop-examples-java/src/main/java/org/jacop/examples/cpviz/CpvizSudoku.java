/*
 * CpvizSudoku.java This file is part of org.jacop.
 *
 * <p>JaCoP is a Java Constraint Programming solver.
 *
 * <p>Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 * <p>This program is free software: you can redistribute it and/or modify it under the terms of the
 * GNU Affero General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * <p>This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Affero General Public License for more details.
 *
 * <p>Notwithstanding any other provision of this License, the copyright owners of this work
 * supplement the terms of this License with terms prohibiting misrepresentation of the origin of
 * this work and requiring that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license terms is in accordance with
 * Section 7 of GNU Affero General Public License version 3.
 *
 * <p>You should have received a copy of the GNU Affero General Public License along with this
 * program. If not, see http://www.gnu.org/licenses/.
 *
 * <p>A simple model to solve Sudoku problem.
 */

package org.jacop.examples.cpviz;

import org.jacop.core.IntVar;
import org.jacop.examples.fd.Sudoku;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.TraceGenerator;

/**
 * It shows how to visualize the solving process for Sudoku problem.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class CpvizSudoku extends Sudoku {

  /**
   * It specifies the main executable function creating a model for a particular Sudoku.
   *
   * @param args not used.
   */
  static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    CpvizSudoku example = new CpvizSudoku();

    example.modelBasic();
  }

  @Override
  protected int[][] getDescription() {
    return new int[][] {
      {0, 0, 0, 0, 0, 0, 0, 0, 0},
      {0, 6, 8, 4, 0, 1, 0, 7, 0},
      {0, 0, 0, 0, 8, 5, 3, 0, 0},
      {0, 2, 6, 8, 0, 9, 0, 4, 7},
      {0, 0, 7, 0, 0, 0, 9, 0, 0},
      {0, 5, 0, 1, 0, 6, 2, 0, 3},
      {0, 4, 0, 6, 1, 0, 0, 0, 0},
      {0, 3, 0, 2, 0, 7, 6, 9, 0},
      {0, 0, 0, 0, 0, 0, 0, 0, 0}
    };
  }

  @Override
  protected int[][] getDescriptionBasic() {
    return getDescription();
  }

  /** Creates the constraint model for Sudoku using global Alldistinct constraints. */
  @Override
  public void model() {

    buildModel(getDescription());
    runTraceSearch(vars.toArray(IntVar[]::new));
  }

  /** It specifies the model using mostly primitive constraints. */
  @Override
  public void modelBasic() {

    buildModelBasic(getDescriptionBasic());
    store.consistency();
    runTraceSearch(flattenElements());
  }

  private void runTraceSearch(IntVar[] searchVars) {

    SelectChoicePoint<IntVar> choicePoint =
        new SimpleSelect<>(searchVars, null, new IndomainMin<>());

    DepthFirstSearch<IntVar> dfs = new DepthFirstSearch<>();

    IntVar[] gridOrder = flattenElements();
    TraceGenerator<IntVar> traceSelect = new TraceGenerator<>(dfs, choicePoint, gridOrder);

    dfs.labeling(store, traceSelect);
  }

  private IntVar[] flattenElements() {
    IntVar[] el = new IntVar[elements.length * elements[0].length];
    int k = 0;
    for (IntVar[] row : elements) {
      for (int j = 0; j < elements[0].length; j++) {
        el[k++] = row[j];
      }
    }
    return el;
  }
}
