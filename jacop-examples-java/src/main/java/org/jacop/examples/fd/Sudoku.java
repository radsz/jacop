/*
 * Sudoku.java
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
import java.util.List;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * A simple model to solve Sudoku problem.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class Sudoku extends ExampleFd {

  /** The Sudoku grid; shared with subclasses. */
  protected IntVar[][] elements;

  private static final String SOLUTION_FOUND = "Solution(s) found";

  /** Returns the puzzle description for model(); 0 = unknown, &gt;0 = known value. */
  protected int[][] getDescription() {
    return new int[][] {
      {0, 1, 0, 4, 2, 0, 0, 0, 5},
      {0, 0, 2, 0, 7, 1, 0, 3, 9},
      {0, 0, 0, 0, 0, 0, 0, 4, 0},
      {2, 0, 7, 1, 0, 0, 0, 0, 6},
      {0, 0, 0, 0, 4, 0, 0, 0, 0},
      {6, 0, 0, 0, 0, 7, 4, 0, 3},
      {0, 7, 0, 0, 0, 0, 0, 0, 0},
      {1, 2, 0, 7, 3, 0, 5, 0, 0},
      {3, 0, 0, 0, 8, 2, 0, 7, 0}
    };
  }

  /** Returns the puzzle description for modelBasic(). */
  protected int[][] getDescriptionBasic() {
    return getDescription();
  }

  /**
   * It specifies the main executable function creating a model for a particular Sudoku.
   *
   * @param args not used.
   */
  static void main(String[] args) {

    Sudoku example = new Sudoku();

    example.model();

    if (example.searchSmallestDomain(false)) {
      IO.println(SOLUTION_FOUND);
    }

    printMatrix(example.elements, example.elements.length, example.elements[0].length);
  }

  /**
   * It specifies the testing function creating a model for a particular Sudoku.
   *
   * @param args not used.
   */
  public static void test(String[] args) {

    Sudoku example = new Sudoku();

    example.model();

    if (example.searchSmallestDomain(false)) {
      IO.println(SOLUTION_FOUND);
    }

    printMatrix(example.elements, example.elements.length, example.elements[0].length);

    example = new Sudoku();

    example.modelBasic();

    if (example.searchSmallestDomain(false)) {
      IO.println(SOLUTION_FOUND);
    }

    printMatrix(example.elements, example.elements.length, example.elements[0].length);
  }

  /** Builds the Sudoku model using Alldistinct constraints. */
  protected void buildModel(int[][] description) {
    createVariables(description);
    addAlldistinctConstraints();
  }

  /** Builds the Sudoku model using primitive XneqY constraints. */
  protected void buildModelBasic(int[][] description) {
    createVariables(description);
    addXneqYConstraints();
  }

  /** Creates variables for the Sudoku grid. */
  private void createVariables(int[][] description) {
    int noRows = 3;
    int noColumns = 3;

    store = new Store();
    vars = new ArrayList<>();

    elements = new IntVar[noRows * noColumns][noRows * noColumns];

    for (int i = 0; i < noRows * noColumns; i++) {
      for (int j = 0; j < noRows * noColumns; j++) {
        if (description[i][j] == 0) {
          elements[i][j] = new IntVar(store, "f" + i + j, 1, noRows * noColumns);
          vars.add(elements[i][j]);
        } else {
          elements[i][j] = new IntVar(store, "f" + i + j, description[i][j], description[i][j]);
        }
      }
    }
  }

  /** Adds Alldistinct constraints for rows, columns, and blocks. */
  private void addAlldistinctConstraints() {
    int noRows = 3;
    int noColumns = 3;

    for (int i = 0; i < noRows * noColumns; i++) {
      store.impose(new Alldistinct(elements[i]));
    }

    for (int j = 0; j < noRows * noColumns; j++) {
      IntVar[] column = new IntVar[noRows * noColumns];
      for (int i = 0; i < noRows * noColumns; i++) {
        column[i] = elements[i][j];
      }
      store.impose(new Alldistinct(column));
    }

    for (int i = 0; i < noRows; i++) {
      for (int j = 0; j < noColumns; j++) {
        List<IntVar> block = new ArrayList<>();
        for (int k = 0; k < noColumns; k++) {
          block.addAll(
              Arrays.asList(elements[i * noColumns + k]).subList(j * noRows, noRows + j * noRows));
        }
        store.impose(new Alldistinct(block));
      }
    }
  }

  /** Adds XneqY constraints for rows, columns, and blocks. */
  private void addXneqYConstraints() {
    int noRows = 3;
    int noColumns = 3;

    for (int i = 0; i < noRows * noColumns; i++) {
      for (int k = 0; k < noRows * noColumns; k++) {
        for (int j = k + 1; j < noRows * noColumns; j++) {
          store.impose(new XneqY(elements[i][k], elements[i][j]));
        }
      }
    }

    for (int i = 0; i < noRows * noColumns; i++) {
      for (int k = 0; k < noRows * noColumns; k++) {
        for (int j = k + 1; j < noRows * noColumns; j++) {
          store.impose(new XneqY(elements[k][i], elements[j][i]));
        }
      }
    }

    for (int i = 0; i < noRows; i++) {
      for (int j = 0; j < noColumns; j++) {
        List<IntVar> block = new ArrayList<>();
        for (int k = 0; k < noColumns; k++) {
          block.addAll(
              Arrays.asList(elements[i * noColumns + k]).subList(j * noRows, noRows + j * noRows));
        }
        for (int k = 0; k < noColumns * noRows; k++) {
          for (int m = k + 1; m < noColumns * noRows; m++) {
            store.impose(new XneqY(block.get(k), block.get(m)));
          }
        }
      }
    }
  }

  @Override
  public void model() {
    buildModel(getDescription());
  }

  /** It specifies the model using mostly primitive constraints. */
  public void modelBasic() {
    buildModelBasic(getDescriptionBasic());
  }
}
