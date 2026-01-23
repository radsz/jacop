/*
 * Nonogram.java
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

package org.jacop.examples.fd.nonogram;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.regex.Pattern;
import org.jacop.constraints.ExtensionalSupportMDD;
import org.jacop.constraints.regular.Regular;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.jacop.search.SelectChoicePoint;
import org.jacop.util.fsm.FSM;
import org.jacop.util.fsm.FSMState;
import org.jacop.util.fsm.FSMTransition;

/**
 * It solves a nonogram example problem, sometimes also called Paint by Numbers.
 *
 * @author Radoslaw Szymanek
 * @version 4.10
 */
public class Nonogram extends ExampleFD {

  /** The value that represents a black dot. */
  public final int black = 1;

  /** The value that represents a white dot. */
  public final int white = 0;

  /**
   * It specifies if the slide based decomposition of the regular constraint should be applied. This
   * decomposition uses ternary extensional support constraints. It achieves GAC if FSM is
   * deterministic.
   */
  public final boolean slideDecomposition = false;

  /** It specifies if the regular constraint should be used. */
  public final boolean regular = true;

  /**
   * It specifies if one extensional constraint based on MDD created from FSM should be used. The
   * translation process works if FSM is deterministic.
   */
  public final boolean extensionalMDD = false;

  /** A board to be painted in white/black dots. */
  public IntVar[][] board;

  /** It specifies a rule for each row. */
  public int[][] row_rules = {
    {0, 0, 0, 0, 2, 2, 3},
    {0, 0, 4, 1, 1, 1, 4},
    {0, 0, 4, 1, 2, 1, 1},
    {4, 1, 1, 1, 1, 1, 1},
    {0, 2, 1, 1, 2, 3, 5},
    {0, 1, 1, 1, 1, 2, 1},
    {0, 0, 3, 1, 5, 1, 2},
    {0, 3, 2, 2, 1, 2, 2},
    {2, 1, 4, 1, 1, 1, 1},
    {0, 2, 2, 1, 2, 1, 2},
    {0, 1, 1, 1, 3, 2, 3},
    {0, 0, 1, 1, 2, 7, 3},
    {0, 0, 1, 2, 2, 1, 5},
    {0, 0, 3, 2, 2, 1, 2},
    {0, 0, 0, 3, 2, 1, 2},
    {0, 0, 0, 0, 5, 1, 2},
    {0, 0, 0, 2, 2, 1, 2},
    {0, 0, 0, 4, 2, 1, 2},
    {0, 0, 0, 6, 2, 3, 2},
    {0, 0, 0, 7, 4, 3, 2},
    {0, 0, 0, 0, 7, 4, 4},
    {0, 0, 0, 0, 7, 1, 4},
    {0, 0, 0, 0, 6, 1, 4},
    {0, 0, 0, 0, 4, 2, 2},
    {0, 0, 0, 0, 0, 2, 1}
  };

  /** It specifies a rule for each column. */
  public int[][] col_rules = {
    {0, 0, 1, 1, 2, 2},
    {0, 0, 0, 5, 5, 7},
    {0, 0, 5, 2, 2, 9},
    {0, 0, 3, 2, 3, 9},
    {0, 1, 1, 3, 2, 7},
    {0, 0, 0, 3, 1, 5},
    {0, 7, 1, 1, 1, 3},
    {1, 2, 1, 1, 2, 1},
    {0, 0, 0, 4, 2, 4},
    {0, 0, 1, 2, 2, 2},
    {0, 0, 0, 4, 6, 2},
    {0, 0, 1, 2, 2, 1},
    {0, 0, 3, 3, 2, 1},
    {0, 0, 0, 4, 1, 15},
    {1, 1, 1, 3, 1, 1},
    {2, 1, 1, 2, 2, 3},
    {0, 0, 1, 4, 4, 1},
    {0, 0, 1, 4, 3, 2},
    {0, 0, 1, 1, 2, 2},
    {0, 7, 2, 3, 1, 1},
    {0, 2, 1, 1, 1, 5},
    {0, 0, 0, 1, 2, 5},
    {0, 0, 1, 1, 1, 3},
    {0, 0, 0, 4, 2, 1},
    {0, 0, 0, 0, 0, 3}
  };

  /**
   * It executes the program which solves this simple problem.
   *
   * @param args no arguments are read.
   */
  static void main(String[] args) {

    Nonogram example = new Nonogram();

    example.model();
    if (example.searchAll()) {
      IO.println("Solution(s) found");
    }

    example.printMatrix(example.board);
  }

  /**
   * It executes the program which solves this simple problem.
   *
   * @param args no arguments are read.
   */
  public static void test(String[] args) {

    Nonogram example = new Nonogram();

    example.model();
    if (example.searchAll()) {
      IO.println("Solution(s) found");
    }
    example.printMatrix(example.board);

    for (int i = 0; i <= 150; i++) {

      StringBuilder no = new StringBuilder(String.valueOf(i));
      while (no.length() < 3) {
        no.insert(0, "0");
      }

      IO.println("Problem file data" + no + ".nin");
      example.readFromFile("ExamplesJaCoP/nonogramRepository/data" + no + ".nin");
      example.model();

      if (example.searchAll()) {
        IO.println("Solution(s) found");
      }

      example.printMatrix(example.board);
    }
  }

  public void readFromFile(String filename) {

    String[] lines = new String[100];

    int[] dimensions = new int[2];

    /* read from file args[0] or qcp.txt */
    try (BufferedReader in =
        new BufferedReader(
            new InputStreamReader(new FileInputStream(filename), StandardCharsets.UTF_8))) {

      String str;

      str = in.readLine();

      Pattern pat = Pattern.compile(" ");
      String[] result = pat.split(str);

      int current = 0;
      for (String s : result) {
        try {
          int currentNo = Integer.parseInt(s);
          dimensions[current++] = currentNo;
        } catch (Exception _) {

        }
      }

      lines = new String[dimensions[0] + dimensions[1]];

      int n = 0;

      while ((str = in.readLine()) != null && n < lines.length) {
        lines[n] = str;
        n++;
      }
      // in.close(); not needed; auto close
    } catch (FileNotFoundException _) {
      System.err.println("I can not find file " + filename);
    } catch (IOException _) {
      System.err.println("Something is wrong with file" + filename);
    }

    row_rules = new int[dimensions[1]][];
    col_rules = new int[dimensions[0]][];

    // Transforms strings into ints
    for (int i = 0; i < lines.length; i++) {

      Pattern pat = Pattern.compile(" ");
      String[] result = pat.split(lines[i]);

      int[] sequence = new int[result.length];

      int current = 0;
      for (String s : result) {
        try {
          sequence[current++] = Integer.parseInt(s);
        } catch (Exception _) {
        }
      }

      if (i < row_rules.length) {
        row_rules[i] = sequence;
      } else {
        col_rules[i - row_rules.length] = sequence;
      }
    }
  }

  /**
   * It produces and FSM given a sequence representing a rule. e.g. [2, 3] specifies that there are
   * two black dots followed by three black dots.
   *
   * @param sequence a sequence representing a rule. e.g. [2, 3]
   * @return Finite State Machine used by Regular automaton to enforce proper sequence.
   */
  public FSM createAutomaton(int[] sequence) {

    FSM result = new FSM();

    FSMState currentState = new FSMState();

    result.initState = currentState;
    IntDomain blackEncountered = new IntervalDomain(black, black);
    IntDomain whiteEncountered = new IntervalDomain(white, white);

    FSMTransition white = new FSMTransition(whiteEncountered, currentState);
    currentState.addTransition(white);

    for (int i = 0; i < sequence.length; i++) {
      if (sequence[i] == 0) {
        continue;
      }
      for (int j = 0; j < sequence[i]; j++) {
        // Black transition
        FSMState nextState = new FSMState();
        FSMTransition black = new FSMTransition(blackEncountered, nextState);
        currentState.addTransition(black);
        result.allStates.add(currentState);
        currentState = nextState;
      }
      // White transitions
      if (i + 1 != sequence.length) {
        FSMState nextState = new FSMState();
        white = new FSMTransition(whiteEncountered, nextState);
        currentState.addTransition(white);
        result.allStates.add(currentState);
        currentState = nextState;
      }

      white = new FSMTransition(whiteEncountered, currentState);
      currentState.addTransition(white);
    }

    result.allStates.add(currentState);
    result.finalStates.add(currentState);

    return result;
  }

  @Override
  public void model() {

    // Creating constraint store
    store = new Store();
    vars = new ArrayList<>();

    // Specifying what values are allowed.
    IntervalDomain values = new IntervalDomain();
    values.unionAdapt(black, black);
    values.unionAdapt(white, white);

    // Specifying the board with allowed values.
    board = new IntVar[row_rules.length][col_rules.length];

    for (int i = 0; i < board.length; i++) {
      for (int j = 0; j < board[0].length; j++) {
        board[i][j] = new IntVar(store, "board[" + i + "][" + j + "]", values.clone());
      }
    }

    // Zigzag based variable ordering.
    for (int m = 0; m < row_rules.length + col_rules.length - 1; m++) {
      for (int j = 0; j <= m && j < col_rules.length; j++) {
        int i = m - j;
        if (i >= row_rules.length) {
          continue;
        }
        vars.add(board[i][j]);
      }
    }

    IO.println("Size " + vars.size());

    // Making sure that rows respect the rules.
    for (int i = 0; i < row_rules.length; i++) {

      FSM result = this.createAutomaton(row_rules[i]);

      if (slideDecomposition) {
        store.imposeDecomposition(new Regular(result, board[i]));
      }

      if (regular) {
        store.impose(new Regular(result, board[i]));
      }

      if (extensionalMDD) {
        store.impose(new ExtensionalSupportMDD(result.transformDirectlyIntoMDD(board[i])));
      }
    }

    // Making sure that columns respect the rules.
    for (int i = 0; i < col_rules.length; i++) {

      FSM result = createAutomaton(col_rules[i]);
      IntVar[] column = new IntVar[row_rules.length];

      for (int j = 0; j < column.length; j++) {
        column[j] = board[j][i];
      }

      if (slideDecomposition) {
        store.imposeDecomposition(new Regular(result, column));
      }

      if (regular) {
        store.impose(new Regular(result, column));
      }

      if (extensionalMDD) {
        store.impose(new ExtensionalSupportMDD(result.transformDirectlyIntoMDD(column)));
      }
    }
  }

  /**
   * It specifies simple search method based on most constrained static and lexigraphical ordering
   * of values. It searches for all solutions.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchAll() {

    long T1, T2;

    // In case of nonograms, value ordering does not matter since we
    // a) search for all solutions
    // b) all variables have binary domain.
    SelectChoicePoint<IntVar> select =
        new InputOrderSelect<>(store, vars.toArray(new IntVar[1]), new IndomainMin<>());

    search = new DepthFirstSearch<>();

    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.setAssignSolution(true);

    IO.println("Search has begun ...");

    T1 = System.currentTimeMillis();

    boolean result = search.labeling(store, select);

    T2 = System.currentTimeMillis();

    if (result) {
      IO.println("Number of solutions " + search.getSolutionListener().solutionsNo());
      search.printAllSolutions();
    } else {
      IO.println("Failed to find any solution");
    }

    IO.println("\n\t*** Execution time = " + (T2 - T1) + " ms");

    return result;
  }

  /**
   * It prints a matrix of variables. All variables must be grounded.
   *
   * @param matrix matrix containing the grounded variables.
   */
  public void printMatrix(IntVar[][] matrix) {

    for (IntVar[] intVars : matrix) {
      for (IntVar intVar : intVars) {
        if (intVar.value() == black) {
          IO.print("0");
        } else {
          IO.print(" ");
        }
      }
      IO.println();
    }
  }
}
