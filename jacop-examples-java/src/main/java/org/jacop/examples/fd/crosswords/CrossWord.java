/*
 * Store.java
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

package org.jacop.examples.fd.crosswords;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.ExtensionalSupportMdd;
import org.jacop.constraints.XeqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.examples.fd.ExampleFd;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.SmallestDomain;
import org.jacop.util.Mdd;

/**
 * It is an example of the power of ExtensionalSupportMdd constraint which can be used to
 * efficiently model and solve CrossWord puzzles.
 *
 * <p>This program uses problem instances and dictionary obtained from Hadrien Cambazard.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class CrossWord extends ExampleFd {

  final int r = 5; // number of rows
  final int c = 5; // number of column
  final int[] wordSizesPrimitive = {4, 5};
  // * - black wall
  // letter - letter which must be in crossword
  // _ - unknown letter, any letter is accepted.
  final List<Integer> wordSizes = new ArrayList<>();
  final Map<Integer, Mdd> mdds = new HashMap<>();
  final char[][] crosswordTemplate = {
    {'*', '_', '_', '_', '_'},
    {'_', '_', '_', 'l', '_'},
    {'_', '_', '_', '_', '_'},
    {'_', 'e', '_', '_', '_'},
    {'_', '_', 'm', '_', '_'}
  };
  public String defaultDictionary = "src/main/java/org/jacop/examples/fd/crosswords/words";
  IntVar[][] x; // the solution
  IntVar blank;

  /**
   * It executes the program to create a model and solve crossword problem.
   *
   * @param args no arguments used.
   */
  static void main(String[] args) {

    String filename;
    if (args.length == 1) {
      filename = args[0];
      IO.println("Using file " + filename);
    }

    CrossWord m = new CrossWord();

    m.model();

    long T1;
    long T2;
    T1 = System.currentTimeMillis();

    m.searchAllAtOnceNoRecord();

    T2 = System.currentTimeMillis();

    IO.println("\n\t*** Execution time = " + (T2 - T1) + " ms");
  } // end main

  /** Model(). */
  @Override
  public void model() {

    store = new Store();

    blank = new IntVar(store, "blank", 'a', 'z');

    for (int s : wordSizesPrimitive) {
      wordSizes.add(s);
    }

    x = new IntVar[crosswordTemplate.length][];

    for (int i = 0; i < crosswordTemplate.length; i++) {
      x[i] = new IntVar[crosswordTemplate[i].length];
    }

    readDictionaryFromFile(defaultDictionary, wordSizes);

    // initiate structures and variables

    for (int i = 0; i < r; i++) {
      for (int j = 0; j < c; j++) {
        if (crosswordTemplate[i][j] != '*') {
          x[i][j] = new IntVar(store, "x_" + i + "_" + j, 'a', 'z');
          if (crosswordTemplate[i][j] != '_') {
            store.impose(new XeqC(x[i][j], crosswordTemplate[i][j]));
          }
        }
      }
    }

    for (int i = 0; i < r; i++) {
      processWordSequence(i, true);
    }

    for (int j = 0; j < c; j++) {
      processWordSequence(j, false);
    }

    vars = new ArrayList<>();

    for (int i = 0; i < r; i++) {
      for (int j = 0; j < c; j++) {
        if (x[i][j] != null) {
          vars.add(x[i][j]);
        }
      }
    }
  }

  /**
   * Processes a sequence of cells (row or column) to extract words and impose constraints.
   *
   * @param index the row or column index
   * @param isRow true if processing a row, false if processing a column
   */
  private void processWordSequence(int index, boolean isRow) {
    List<Var> word = new ArrayList<>();
    int length = isRow ? c : r;

    for (int pos = 0; pos < length; pos++) {
      int row = isRow ? index : pos;
      int col = isRow ? pos : index;

      if (crosswordTemplate[row][col] == '*') {
        imposeWordConstraint(word);
        word.clear();
      } else {
        word.add(x[row][col]);
      }
    }

    if (!word.isEmpty()) {
      imposeWordConstraint(word);
    }
  }

  /**
   * Imposes extensional constraint on a word if its size matches allowed word sizes.
   *
   * @param word the list of variables representing a word
   */
  private void imposeWordConstraint(List<Var> word) {
    if (wordSizes.contains(word.size())) {
      Mdd mdd4word = mdds.get(word.size()).reuse(word.toArray(new IntVar[0]));
      store.impose(new ExtensionalSupportMdd(mdd4word));
    }
  }

  /**
   * It prints a variable crosswordTemplate.
   *
   * @param crossWordTemplate the template
   */
  public void printSolution(char[][] crossWordTemplate) {

    IO.println();
    for (int i = 0; i < r; i++) {
      for (int j = 0; j < c; j++) {
        if (crossWordTemplate[i][j] != '*') {
          IO.print((char) x[i][j].value() + " ");
        } else {
          IO.print("* ");
        }
      }
      IO.println();
    }
  }

  /** Returns true if the line should be skipped (comment or wrong length). */
  private static boolean skipDictionaryLine(String line, int wordSize) {
    if (line.startsWith("#") || line.startsWith("%")) {
      return true;
    }
    return line.length() != wordSize;
  }

  /**
   * It reads a dictionary. For every word length specified it reads a dictionary and creates an Mdd
   * representation of it for use by an extensional constraint.
   *
   * @param file filename containing dictionary
   * @param wordSizes size of the words
   */
  public void readDictionaryFromFile(String file, List<Integer> wordSizes) {

    for (int wordSize : wordSizes) {

      int wordCount = 0;
      IntVar[] list = new IntVar[wordSize];
      Arrays.fill(list, blank);
      int[] tupleForGivenWord = new int[wordSize];
      Mdd resultForWordSize = new Mdd(list);

      try (BufferedReader inr =
          new BufferedReader(
              new InputStreamReader(new FileInputStream(file), StandardCharsets.UTF_8))) {

        String str;
        while ((str = inr.readLine()) != null && !str.isEmpty()) {
          str = str.trim();
          if (skipDictionaryLine(str, wordSize)) {
            continue;
          }
          for (int i = 0; i < wordSize; i++) {
            tupleForGivenWord[i] = str.charAt(i);
          }
          wordCount++;
          resultForWordSize.addTuple(tupleForGivenWord);
        }

      } catch (IOException e) {
        IO.println(e);
      }

      IO.println("There are " + wordCount + " words of size " + wordSize);
      resultForWordSize.reduce();
      mdds.put(wordSize, resultForWordSize);
    }
  }

  /**
   * It searches for all solutions. It does not record them and prints every tenth of them.
   *
   * @return true if any solution was found, false otherwise.
   */
  public boolean searchAllAtOnceNoRecord() {

    long T1;
    T1 = System.currentTimeMillis();

    searchLabel = new DepthFirstSearch<>();
    searchLabel.setSolutionListener(new PrintListener<>(crosswordTemplate));

    searchLabel.getSolutionListener().searchAll(true);
    searchLabel.getSolutionListener().recordSolutions(false);
    searchLabel.setAssignSolution(true);

    SelectChoicePoint<IntVar> select =
        new SimpleSelect<>(
            vars.toArray(new IntVar[1]), new SmallestDomain<>(), new IndomainMin<>());
    boolean result = searchLabel.labeling(store, select);

    long T2 = System.currentTimeMillis();

    if (result) {
      IO.println("Number of solutions " + searchLabel.getSolutionListener().solutionsNo());
      searchLabel.printAllSolutions();
    } else {
      IO.println("Failed to find any solution");
    }

    IO.println("\n\t*** Execution time = " + (T2 - T1) + " ms");

    return result;
  }

  /** It is a simple print listener to print every tenth solution encountered. */
  public class PrintListener<T extends Var> extends SimpleSolutionListener<T> {

    final char[][] crossWordTemplate;

    /**
     * Constructs a print listener for crossword solutions.
     *
     * @param crosswordTemplate the crossword template to use for printing
     */
    public PrintListener(char[][] crosswordTemplate) {
      this.crossWordTemplate = crosswordTemplate;
    }

    @Override
    public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

      boolean returnCode = super.executeAfterSolution(search, select);

      if (noSolutions % 10 == 0) {
        IO.println("Solution # " + noSolutions);
        printSolution(crossWordTemplate);
      }

      return returnCode;
    }
  }
} // end class
