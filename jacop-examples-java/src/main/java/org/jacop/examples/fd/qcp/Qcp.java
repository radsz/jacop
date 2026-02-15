/*
 * Qcp.java
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

package org.jacop.examples.fd.qcp;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.examples.fd.ExampleFd;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMiddle;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.Shaving;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.jacop.search.TransformExtensional;

/**
 * It solves QuasiGroup Completion Problem (Qcp).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class Qcp extends ExampleFd {

  // It uses correct InputOrder tie breaking (lex)

  /** It contains constraints which can be used to guide shaving. */
  public final List<Constraint> shavingConstraints = new ArrayList<>();

  /** It specifies the file containing the description of the problem. */
  public String filename = "src/main/java/org/jacop/examples/fd/qcp/psqwh-25-235-0081.pls";

  /** It contains the order of the Qcp being solved. */
  public int n;

  private static final String SOLUTION_FOUND = " Solution(s) found ";

  /**
   * It executes the program which solves the Qcp in multiple different ways.
   *
   * @param args the first argument is the name of the file containing the problem.
   */
  public static void test(String[] args) {

    Qcp example = new Qcp();

    if (args.length > 0) {
      example.filename = args[0];
    }

    example.model();

    if (example.searchSmallestDomain(false)) {
      IO.print(SOLUTION_FOUND);
    }

    example = new Qcp();

    if (args.length > 0) {
      example.filename = args[0];
    }

    example.model();

    if (example.searchWithRestarts()) {
      IO.print(SOLUTION_FOUND);
    }

    example = new Qcp();

    if (args.length > 0) {
      example.filename = args[0];
    }

    example.model();

    if (example.searchWithShaving()) {
      IO.print(SOLUTION_FOUND);
    }

    example = new Qcp();

    if (args.length > 0) {
      example.filename = args[0];
    }

    example.model();
    example.store.variableWeightManagement = true;

    if (example.searchWeightedDegree()) {
      IO.print(SOLUTION_FOUND);
    }
  }

  /**
   * It executes the program which solves the Qcp in multiple different ways.
   *
   * @param args the first argument is the name of the file containing the problem.
   */
  void main(String[] args) {

    Qcp example = new Qcp();

    if (args.length > 0) {
      example.filename = args[0];
    }

    IO.println("Solving Qcp with restart search.");
    example.model();

    if (example.searchWithRestarts()) {
      IO.print(SOLUTION_FOUND);
    }
  }

  @Override
  public void model() {

    String[] lines = readLinesFromFile();
    n = n - 1;
    int[][] numbers = parseLinesToNumbers(lines);
    store = new Store();
    store.queueNo = 4;
    vars = new ArrayList<>();
    IntVar[][] x = createVariables(n, numbers);
    imposeAlldistinctConstraints(n, x);
  }

  private String[] readLinesFromFile() {
    String[] lines = new String[100];
    try {
      BufferedReader in =
          new BufferedReader(
              new InputStreamReader(new FileInputStream(filename), StandardCharsets.UTF_8));
      String str;
      while ((str = in.readLine()) != null) {
        lines[n] = str;
        n++;
      }
    } catch (FileNotFoundException _) {
      System.err.println(
          "You need to run this program in a directory that contains the required file.");
      System.err.println("I can not find file " + filename);
      throw new RuntimeException(
          "You need to run this program in a directory that contains the required file : "
              + filename);
    } catch (IOException _) {
      System.err.println("Something is wrong with file" + filename);
    }
    return lines;
  }

  private int[][] parseLinesToNumbers(String[] lines) {
    int[][] numbers = new int[n][n];
    for (int i = 1; i < n + 1; i++) {
      Pattern pat = Pattern.compile(" ");
      String[] result = pat.split(lines[i]);
      int current = 0;
      for (String s : result) {
        try {
          int currentNo = Integer.parseInt(s);
          numbers[i - 1][current++] = currentNo;
        } catch (Exception _) {
          // Ignore parsing errors
        }
      }
    }
    return numbers;
  }

  private IntVar[][] createVariables(int size, int[][] numbers) {
    IntVar[][] x = new IntVar[size][size];
    for (int i = 0; i < size; i++) {
      for (int j = 0; j < size; j++) {
        if (numbers[i][j] == -1) {
          x[i][j] = new IntVar(store, "x" + i + "_" + j, 0, size - 1);
          vars.add(x[i][j]);
        } else {
          x[i][j] = new IntVar(store, "x" + i + "_" + j, numbers[i][j], numbers[i][j]);
        }
        vars.add(x[i][j]);
      }
    }
    return x;
  }

  private void imposeAlldistinctConstraints(int size, IntVar[][] x) {
    for (int i = 0; i < size; i++) {
      Constraint cx = new Alldistinct(x[i]);
      store.impose(cx);
      shavingConstraints.add(cx);
      IntVar[] y = new IntVar[size];
      for (int j = 0; j < size; j++) {
        y[j] = x[j][i];
      }
      Constraint cy = new Alldistinct(y);
      store.impose(cy);
      shavingConstraints.add(cy);
    }
  }

  /**
   * It performs search with shaving guided by constraints.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchWithShaving() {

    Shaving<IntVar> shaving = new Shaving<>();
    shaving.setStore(store);
    shaving.quickShave = true;

    for (Constraint c : shavingConstraints) {
      shaving.addShavingConstraint(c);
    }

    long begin = System.currentTimeMillis();

    searchLabel = new DepthFirstSearch<>();
    searchLabel.setPrintInfo(true);

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(vars.toArray(new IntVar[1]), null, new IndomainMiddle<>());

    searchLabel.setConsistencyListener(shaving);
    searchLabel.setExitChildListener(shaving);

    boolean result = searchLabel.labeling(store, select);

    long end = System.currentTimeMillis();

    IO.println("Number of milliseconds " + (end - begin));
    IO.println("Ratio " + (shaving.successes * 100 / (shaving.successes + shaving.failures)));

    return result;
  }

  /**
   * It transforms part of the problem into an extensional costraint to improve propagation and
   * search process.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchAllTransform() {

    final long T1 = System.currentTimeMillis();

    TransformExtensional transform = new TransformExtensional();

    store.consistency();

    for (int i = 7; i < 16; i++) {
      for (int j = 14; j < 22; j++) {
        if (!vars.get(i * n + j).singleton()) {
          transform.variablesTransformationScope.add(vars.get(i * n + j));
        }
      }
    }

    IO.println(transform.variablesTransformationScope);

    final SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]), new SmallestDomain<>(), new IndomainMin<>());

    searchLabel = new DepthFirstSearch<>();
    searchLabel.getSolutionListener().searchAll(true);
    searchLabel.getSolutionListener().recordSolutions(true);

    searchLabel.setInitializeListener(transform);
    transform.solutionLimit = 50000;

    boolean result = searchLabel.labeling(store, select);

    long T2 = System.currentTimeMillis();
    long T = T2 - T1;
    IO.println("\n\t*** Execution time = " + T + " ms");

    return result;
  }
}
