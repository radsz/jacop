/*
 * MineSweeper.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Hakan Kjellerstrand and Radoslaw Szymanek
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

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XeqC;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleMatrixSelect;
import org.jacop.search.SmallestDomain;

/**
 * It models and solves Minesweeper problem.
 *
 * <p>This is a port of Hakan's MiniZinc model <a
 * href="http://www.hakank.org/minizinc/minesweeper.mzn">...</a>
 *
 * <p>which is commented in the (swedish) blog post "Fler constraint programming-modeller i
 * MiniZinc, t.ex. Minesweeper och Game of Life" <a
 * href="http://www.hakank.org/webblogg/archives/001231.html">...</a>
 *
 * <p>See also
 *
 * <p>The first 10 examples are from gecode/examples/minesweeper.cc <a
 * href="http://www.gecode.org/gecode-doc-latest/minesweeper_8cc-source.html">...</a>
 *
 * <p><a href="http://www.janko.at/Raetsel/Minesweeper/index.htm">...</a>
 *
 * <p><a href="http://en.wikipedia.org/wiki/Minesweeper_(computer_game)">...</a>
 *
 * <p>Ian Stewart on Minesweeper: <a
 * href="http://www.claymath.org/Popular_Lectures/Minesweeper/">...</a>
 *
 * <p>Richard Kaye's Minesweeper Pages: <a
 * href="http://web.mat.bham.ac.uk/R.W.Kaye/minesw/minesw.htm">...</a>
 *
 * <p>Some Minesweeper Configurations: <a
 * href="http://web.mat.bham.ac.uk/R.W.Kaye/minesw/minesw.pdf">...</a>
 *
 * @author Hakan Kjellerstrand (hakank@bonetmail.com) and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class MineSweeper extends ExampleFd {

  /** It represents the unknown value in the problem matrix. */
  public static final int X = -1;

  public int[][] problem;
  int r; // number of rows
  int c; // number of cols
  IntVar[][] game; // The FDV version of the problem matrix.
  IntVar[][] mines; // solution matrix: 0..1 where 1 means mine.

  private static final String ROW_01_10 = "...01.10...";

  /**
   * It transforms string representation of the problem into an array of ints representation.
   *
   * @param description array of strings representing the problem.
   * @return two dimensional array of ints representing the problem.
   */
  public static int[][] readFromArray(String[] description) {

    int r = description.length;
    int c = description[0].trim().length();

    int[][] problem = new int[r][c]; // The problem matrix

    for (int i = 0; i < description.length; i++) {

      String str = description[i];
      str = str.trim();

      // the problem matrix
      for (int j = 0; j < c; j++) {
        String s = str.substring(j, j + 1);
        if (".".equals(s)) {
          problem[i][j] = X;
        } else {
          problem[i][j] = Integer.parseInt(s);
        }
      } // end for
    } // end for

    return problem;
  }

  /**
   * One of the possible MineSweeper problems.
   *
   * @return description of the problem used by the function to create a constraint model.
   */
  public static String[] problem1() {
    return new String[] {"..2.3.", "2.....", "..24.3", "1.34..", ".....3", ".3.3.."};
  }

  /**
   * One of the possible MineSweeper problems.
   *
   * @return description of the problem used by the function to create a constraint model.
   */
  public static String[] problem2() {
    return new String[] {
      "1..2.2.2..",
      ".32...4..1",
      "...13...4.",
      "3.1...3...",
      ".21.1..3.2",
      ".3.2..2.1.",
      "2..32..2..",
      ".3...32..3",
      "..3.33....",
      ".2.2...22."
    };
  }

  /**
   * One of the possible MineSweeper problems.
   *
   * @return description of the problem used by the function to create a constraint model.
   */
  public static String[] problem3() {
    return new String[] {
      "2...3.1.", ".5.4...1", "..5..4..", "2...4.5.", ".2.4...2", "..5..4..", "2...5.4.", ".3.3...2"
    };
  }

  /**
   * One of the possible MineSweeper problems.
   *
   * @return description of the problem used by the function to create a constraint model.
   */
  public static String[] problem4() {
    return new String[] {
      "0.0.1..11.",
      "1.2.2.22..",
      "......2..2",
      ".23.11....",
      "0......2.1",
      "...22.1...",
      ".....3.32.",
      ".5.2...3.1",
      ".3.1..3...",
      ".2...12..0"
    };
  }

  /**
   * One of the possible MineSweeper problems.
   *
   * @return description of the problem used by the function to create a constraint model.
   */
  public static String[] problem5() {
    return new String[] {
      ".21.2.2...",
      ".4..3...53",
      "...4.44..3",
      "4.4..5.6..",
      "..45....54",
      "34....55..",
      "..4.4..5.5",
      "2..33.6...",
      "36...3..4.",
      "...4.2.21."
    };
  }

  /**
   * One of the possible MineSweeper problems.
   *
   * @return description of the problem used by the function to create a constraint model.
   */
  public static String[] problem6() {
    return new String[] {
      ".32..1..", "....1..3", "3..2...4", ".5...5..", "..6...5.", "3...5..4", "2..5....", "..2..34."
    };
  }

  /**
   * One of the possible MineSweeper problems.
   *
   * @return description of the problem used by the function to create a constraint model.
   */
  public static String[] problem7() {
    return new String[] {
      ".1.....3.",
      "...343...",
      "244...443",
      "...4.4...",
      ".4.4.3.6.",
      "...4.3...",
      "123...133",
      "...322...",
      ".2.....3."
    };
  }

  /**
   * One of the possible MineSweeper problems.
   *
   * @return description of the problem used by the function to create a constraint model.
   */
  public static String[] problem8() {
    return new String[] {
      ".......", ".23435.", ".1...3.", "...5...", ".1...3.", ".12234.", "......."
    };
  }

  /**
   * One of the possible MineSweeper problems.
   *
   * @return description of the problem used by the function to create a constraint model.
   */
  public static String[] problem9() {
    return new String[] {
      "2...2...2",
      ".4.4.3.4.",
      "..4...1..",
      ".4.3.3.4.",
      "2.......2",
      ".5.4.5.4.",
      "..3...3..",
      ".4.3.5.6.",
      "2...1...2",
    };
  }

  /**
   * One of the possible MineSweeper problems.
   *
   * @return description of the problem used by the function to create a constraint model.
   */
  public static String[] problemTest() {
    return new String[] {
      "2...2...2",
      ".4...3.4.",
      "..4...1..",
      ".4.3.3...",
      "2...22..2",
      ".5..3..4.",
      "...2..3..",
      ".4.....6.",
      "2...1...2",
    };
  }

  /**
   * One of the possible MineSweeper problems.
   *
   * @return description of the problem used by the function to create a constraint model.
   */
  public static String[] problemKayeSplitter() {
    return new String[] {
      "...0...0...",
      ROW_01_10,
      ROW_01_10,
      "00001110000",
      ".1111.1111.",
      "...1.2.1...",
      ".1111.1111.",
      "00001110000",
      ROW_01_10,
      ROW_01_10,
      "...0...0..."
    };
  }

  /**
   * The collection of MineSweeper problems.
   *
   * @return description of the problem used by the function to create a constraint model.
   */
  public static String[][] problems() {
    return new String[][] {
      problem1(),
      problem2(),
      problem3(),
      problem4(),
      problem5(),
      problem6(),
      problem7(),
      problem8(),
      problem9()
    };
  }

  /**
   * Reads a minesweeper file. File format: # a comment which is ignored % a comment which also is
   * ignored number of rows number of columns {@literal <} row number of neighbours lines...
   * {@literal >}
   *
   * <p>0..8 means number of neighbours, "." mean unknown (may be a mine)
   *
   * <p>Example (from minesweeper0.txt) # Problem from Gecode/examples/minesweeper.cc problem 0 6 6
   * ..2.3. 2..... ..24.3 1.34.. .....3 .3.3..
   *
   * @param file it specifies the filename containing the problem description.
   * @return the int array description of the problem.
   */
  public static int[][] readFile(String file) {

    log.info("readFile(" + file + ")");

    try (BufferedReader inr =
        new BufferedReader(
            new InputStreamReader(new FileInputStream(file), StandardCharsets.UTF_8))) {
      return parseMineSweeperLines(readNonCommentLines(inr));
    } catch (IOException e) {
      log.info("{}", e);
      return null;
    }
  }

  private static List<String> readNonCommentLines(BufferedReader inr) throws IOException {
    List<String> lines = new ArrayList<>();
    String str;
    while ((str = inr.readLine()) != null && !str.isEmpty()) {
      str = str.trim();
      if (str.startsWith("#") || str.startsWith("%")) {
        continue;
      }
      log.info(str);
      lines.add(str);
    }
    return lines;
  }

  private static int[][] parseMineSweeperLines(List<String> lines) {
    if (lines.isEmpty()) {
      return null;
    }
    int r = Integer.parseInt(lines.get(0));
    int c = Integer.parseInt(lines.get(1));
    int[][] problem = new int[r][c];
    for (int lineIndex = 2; lineIndex < lines.size(); lineIndex++) {
      String[] row = lines.get(lineIndex).split("");
      for (int j = 1; j <= c; j++) {
        String s = row[j];
        problem[lineIndex - 2][j - 1] = ".".equals(s) ? -1 : Integer.parseInt(s);
      }
    }
    return problem;
  } // end readFile

  /**
   * It executes the program to solve any MineSweeper problem. It is possible to supply the filename
   * containing the problem specification.
   *
   * @param args the filename containing the problem description.
   */
  static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    long t1;
    long t2;
    long t;
    t1 = System.currentTimeMillis();

    MineSweeper minesweeper = new MineSweeper();

    for (int i = 0; i < problems().length; i++) {

      t1 = System.currentTimeMillis();

      minesweeper.problem = MineSweeper.readFromArray(problems()[i]);

      minesweeper.model();

      minesweeper.searchSpecific(true);

      t2 = System.currentTimeMillis();
      t = t2 - t1;
      log.info("\n\t*** Execution time = " + t + " ms");
    }

    if (args.length > 0) {
      minesweeper.problem = MineSweeper.readFile(args[0]);
    }

    if (minesweeper.problem == null) {
      minesweeper.problem = MineSweeper.readFromArray(MineSweeper.problemKayeSplitter());
    }

    minesweeper.model();
    minesweeper.searchSpecific(false);

    minesweeper.problem = MineSweeper.readFromArray(MineSweeper.problemTest());
    minesweeper.model();
    minesweeper.searchSpecific(true);

    t2 = System.currentTimeMillis();
    t = t2 - t1;
    log.info("\n\t*** Execution time = " + t + " ms");
  } // end main

  @Override
  public void model() {

    store = new Store();

    if (problem == null) {
      problem = readFromArray(problem1());
    }

    r = problem.length;
    c = problem[0].length;

    initMinesAndGameVariables();
    addMineSweeperConstraints();
  } // end model

  private void initMinesAndGameVariables() {
    mines = new IntVar[r][c];
    game = new IntVar[r][c];
    for (int i = 0; i < r; i++) {
      for (int j = 0; j < c; j++) {
        mines[i][j] = new BooleanVar(store, "m_" + i + "_" + j);
        game[i][j] = new IntVar(store, "g_" + i + "_" + j, -1, 8);
      }
    }
  }

  private void addMineSweeperConstraints() {
    for (int i = 0; i < r; i++) {
      for (int j = 0; j < c; j++) {
        if (problem[i][j] > X) {
          imposeCellConstraints(i, j);
        }
      }
    }
  }

  private void imposeCellConstraints(int i, int j) {
    store.impose(new XeqC(game[i][j], problem[i][j]));
    store.impose(new XeqC(mines[i][j], 0));
    List<IntVar> lst = new ArrayList<>();
    for (int a = -1; a <= 1; a++) {
      for (int b = -1; b <= 1; b++) {
        if (i + a >= 0 && j + b >= 0 && i + a < r && j + b < c) {
          lst.add(mines[i + a][j + b]);
        }
      }
    }
    store.impose(new SumInt(lst, "==", game[i][j]));
  }

  /**
   * It executes special search with solution printing to present the solutions.
   *
   * @param recordSolutions specifies if the solutions should be recorded.
   */
  public void searchSpecific(boolean recordSolutions) {

    // Note: This uses the SimpleMatrixSelect since
    // mines is a matrix.
    SelectChoicePoint<IntVar> select =
        new SimpleMatrixSelect<>(mines, new SmallestDomain<>(), new IndomainMin<>());

    searchLabel = new DepthFirstSearch<>();
    searchLabel.getSolutionListener().searchAll(true);
    searchLabel.getSolutionListener().recordSolutions(recordSolutions);

    boolean result = searchLabel.labeling(store, select);

    int numSolutions = searchLabel.getSolutionListener().solutionsNo();

    if (result) {

      if (numSolutions <= 100) {
        searchLabel.printAllSolutions();
      } else {
        log.info("Too many solutions to print...");
      }

      if (numSolutions > 1) {
        log.info("\nThe last solution:");
      } else {
        log.info("\nThe solution:");
      }

      for (int i = 0; i < r; i++) {
        for (int j = 0; j < c; j++) {
          IO.print(mines[i][j].value() + " ");
        }
        log.info("");
      }

      log.info("numSolutions: " + numSolutions);

    } else {

      log.info("No solutions.");
    } // end if result
  } // end search
} // end class
