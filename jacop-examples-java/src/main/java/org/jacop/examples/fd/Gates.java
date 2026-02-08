/*
 * Gates.java
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
import java.util.function.BiFunction;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ExtensionalSupportStr;
import org.jacop.constraints.table.SimpleTable;
import org.jacop.core.BooleanVar;
import org.jacop.core.Domain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.MostConstrainedStatic;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;

/**
 * It specifies an adder using gates specified by extensional constraints.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Gates extends ExampleFd {

  /**
   * It executes a program to solve gates problems.
   *
   * @param args parameters (none)
   */
  static void main(String[] args) {

    long T1;
    long T2;
    long T;
    T1 = System.currentTimeMillis();

    Gates example = new Gates();
    example.model();

    if (example.searchSpecific()) {
      IO.println("Solution found.");
    }

    T2 = System.currentTimeMillis();
    T = T2 - T1;
    IO.println("\n\t*** Execution time = " + T + " ms");
  }

  /**
   * Creates a table constraint using SimpleTable representation.
   *
   * @param vars variables to be constrained
   * @param tuples allowed tuples defining the constraint
   * @return a SimpleTable constraint
   */
  public static Constraint tableConstraintProviderUsingSimpleTable(IntVar[] vars, int[][] tuples) {
    return new SimpleTable(vars, tuples);
  }

  /**
   * Creates a table constraint using ExtensionalSupportStr representation.
   *
   * @param vars variables to be constrained
   * @param tuples allowed tuples defining the constraint
   * @return an ExtensionalSupportStr constraint
   */
  public static Constraint tableConstraintProviderUsingExtensionalStr(
      IntVar[] vars, int[][] tuples) {
    return new ExtensionalSupportStr(vars, tuples);
  }

  @Override
  public void model() {
    model(Gates::tableConstraintProviderUsingSimpleTable);
  }

  /**
   * Creates the constraint model for the adder circuit using gates.
   *
   * @param tableConstraintProvider function providing table constraint implementation
   */
  public void model(BiFunction<IntVar[], int[][], Constraint> tableConstraintProvider) {

    store = new Store();
    vars = new ArrayList<>();

    BooleanVar a = new BooleanVar(store, "a");
    BooleanVar b = new BooleanVar(store, "b");
    BooleanVar c = new BooleanVar(store, "c");
    BooleanVar sum = new BooleanVar(store, "sum");
    BooleanVar carry = new BooleanVar(store, "carry");
    vars.add(a);
    vars.add(b);
    vars.add(c);
    vars.add(sum);
    vars.add(carry);

    BooleanVar nca = new BooleanVar(store, "nca");

    BooleanVar[] t = new BooleanVar[2];
    for (int i = 0; i < t.length; i++) {
      t[i] = new BooleanVar(store);
    }

    // sum part
    xor(c, nca, sum, tableConstraintProvider);
    xor(a, b, nca, tableConstraintProvider);

    // carry part
    or(t[0], t[1], carry, tableConstraintProvider);
    and(c, nca, t[1], tableConstraintProvider);
    and(a, b, t[0], tableConstraintProvider);

    IO.println(
        "\nBooleanVariable store size: "
            + store.size()
            + "\nNumber of constraints: "
            + store.numberConstraints());
  }

  /**
   * It imposes an extensional constraint enforcing an and relationship between two input parameters
   * and an output parameter.
   *
   * @param in1 the first input parameter.
   * @param in2 the second input parameter.
   * @param out the output parameter.
   * @param tableConstraintProvider function that when provided input to create table constraint
   *     will create one.
   */
  public void and(
      BooleanVar in1,
      BooleanVar in2,
      BooleanVar out,
      BiFunction<IntVar[], int[][], Constraint> tableConstraintProvider) {

    int[][] tuples = {{0, 0, 0}, {0, 1, 0}, {1, 0, 0}, {1, 1, 1}};

    store.impose(tableConstraintProvider.apply(new BooleanVar[] {in1, in2, out}, tuples));
  }

  /**
   * It imposes an extensional constraint enforcing an or relationship between two input parameters
   * and an output parameter.
   *
   * @param in1 the first input parameter.
   * @param in2 the second input parameter.
   * @param out the output parameter.
   * @param tableConstraintProvider function that when provided input to create table constraint
   *     will create one.
   */
  public void or(
      BooleanVar in1,
      BooleanVar in2,
      BooleanVar out,
      BiFunction<IntVar[], int[][], Constraint> tableConstraintProvider) {

    int[][] tuples = {{0, 0, 0}, {0, 1, 1}, {1, 0, 1}, {1, 1, 1}};

    store.impose(tableConstraintProvider.apply(new BooleanVar[] {in1, in2, out}, tuples));
  }

  /**
   * It imposes an extensional constraint enforcing an xor relationship between two input parameters
   * and an output parameter.
   *
   * @param in1 the first input parameter.
   * @param in2 the second input parameter.
   * @param out the output parameter.
   * @param tableConstraintProvider function that when provided input to create table constraint
   *     will create one.
   */
  public void xor(
      BooleanVar in1,
      BooleanVar in2,
      BooleanVar out,
      BiFunction<IntVar[], int[][], Constraint> tableConstraintProvider) {

    int[][] tuples = {{0, 0, 0}, {0, 1, 1}, {1, 0, 1}, {1, 1, 0}};

    store.impose(tableConstraintProvider.apply(new BooleanVar[] {in1, in2, out}, tuples));
  }

  /**
   * It imposes an extensional constraint enforcing an not relationship between input parameter and
   * an output parameter.
   *
   * @param in the first input parameter.
   * @param out the output parameter.
   * @param tableConstraintProvider function that when provided input to create table constraint
   *     will create one.
   */
  public void not(
      BooleanVar in,
      BooleanVar out,
      BiFunction<IntVar[], int[][], Constraint> tableConstraintProvider) {

    int[][] tuples = {{0, 1}, {1, 0}};

    store.impose(tableConstraintProvider.apply(new BooleanVar[] {in, out}, tuples));
  }

  /**
   * It provides a specific search with extensive printout of the result.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchSpecific() {

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]), new MostConstrainedStatic<>(), new IndomainMin<>());

    search = new DepthFirstSearch<>();

    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(true);

    boolean searchResult = search.labeling(store, select);

    if (searchResult) {
      IO.println("\nYes");
      Domain[][] solutions = new Domain[search.getSolutionListener().solutionsNo()][];
      for (int i = 1; i <= solutions.length; i++) {
        solutions[i - 1] = search.getSolution(i);
      }

      IO.println("\nAll solutions:\n");
      for (IntVar v : vars) {
        IO.print(v.id() + "\t");
      }
      IO.println("\n-------------------------------------");
      for (Domain[] solution : solutions) {
        for (int i = 0; i < solutions[0].length; i++) {
          IO.print(solution[i] + "\t");
        }
        IO.println();
      }
    } else {
      IO.println("\nNo");
    }

    return searchResult;
  }
}
