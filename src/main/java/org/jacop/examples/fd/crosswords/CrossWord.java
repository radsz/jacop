/*
 * Store.java
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

package org.jacop.examples.fd.crosswords;

import org.jacop.constraints.ExtensionalSupportMDD;
import org.jacop.constraints.XeqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.search.*;
import org.jacop.util.MDD;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * It is an example of the power of ExtensionalSupportMDD constraint which can be used
 * to efficiently model and solve CrossWord puzzles.
 *
 * @author : Radoslaw Szymanek
 * @version 4.9
 *          <p>
 *          This program uses problem instances and dictionary obtained from Hadrien Cambazard.
 */
public class CrossWord extends ExampleFD {

    int r = 5;          // number of rows
    int c = 5;          // number of column
    int[] wordSizesPrimitive = {4, 5};
    List<Integer> wordSizes = new ArrayList<Integer>();
    // * - black wall
    // letter - letter which must be in crossword
    // _ - unknown letter, any letter is accepted.

    IntVar[][] x;      // the solution
    IntVar blank;

    String defaultDictionary = "src/main/java/org/jacop/examples/fd/crosswords/words";

    Map<Integer, MDD> mdds = new HashMap<Integer, MDD>();

    char[][] crosswordTemplate =
        {{'*', '_', '_', '_', '_'},
         {'_', '_', '_', 'l', '_'},
         {'_', '_', '_', '_', '_'},
         {'_', 'e', '_', '_', '_'},
         {'_', '_', 'm', '_', '_'}};

    /**
     * model()
     */
    @Override public void model() {

        store = new Store();

        blank = new IntVar(store, "blank", 'a', 'z');

        for (int s : wordSizesPrimitive)
            wordSizes.add(s);

        x = new IntVar[crosswordTemplate.length][];

        for (int i = 0; i < crosswordTemplate.length; i++)
            x[i] = new IntVar[crosswordTemplate[i].length];

        readDictionaryFromFile(defaultDictionary, wordSizes);


        //
        // initiate structures and variables
        //

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

            List<Var> word = new ArrayList<Var>();

            for (int j = 0; j < c; j++) {

                if (crosswordTemplate[i][j] == '*') {
                    if (wordSizes.contains(word.size())) {
                        MDD mdd4word = mdds.get(word.size()).reuse(word.toArray(new IntVar[0]));
                        store.impose(new ExtensionalSupportMDD(mdd4word));
                    }
                    // System.out.println(word);
                    word.clear();
                } else
                    word.add(x[i][j]);

            }

            if (word.size() > 0) {
                if (wordSizes.contains(word.size())) {
                    MDD mdd4word = mdds.get(word.size()).reuse(word.toArray(new IntVar[0]));
                    store.impose(new ExtensionalSupportMDD(mdd4word));
                    // System.out.println(word);
                }
                // System.out.println(word);
                word.clear();
            }

        }

        for (int j = 0; j < c; j++) {

            List<Var> word = new ArrayList<Var>();

            for (int i = 0; i < r; i++) {

                if (crosswordTemplate[i][j] == '*') {
                    if (wordSizes.contains(word.size())) {
                        MDD mdd4word = mdds.get(word.size()).reuse(word.toArray(new IntVar[0]));
                        store.impose(new ExtensionalSupportMDD(mdd4word));
                        // System.out.println(word);
                    }
                    word.clear();
                } else
                    word.add(x[i][j]);

            }

            if (word.size() > 0) {
                if (wordSizes.contains(word.size())) {
                    MDD mdd4word = mdds.get(word.size()).reuse(word.toArray(new IntVar[0]));
                    store.impose(new ExtensionalSupportMDD(mdd4word));
                    // System.out.println(word);
                }
                word.clear();
            }

        }

        vars = new ArrayList<IntVar>();

        for (int i = 0; i < r; i++)
            for (int j = 0; j < c; j++)
                if (x[i][j] != null)
                    vars.add(x[i][j]);

    }


    /**
     * It prints a variable crosswordTemplate.
     *
     * @param crossWordTemplate the template
     */
    public void printSolution(char[][] crossWordTemplate) {

        System.out.println();
        for (int i = 0; i < r; i++) {
            for (int j = 0; j < c; j++) {
                if (crossWordTemplate[i][j] != '*')
                    System.out.print((char)x[i][j].value() + " ");
                else
                    System.out.print("* ");
            }
            System.out.println();
        }

    }

    /**
     * It reads a dictionary. For every word length specified
     * it reads a dictionary and creates an MDD representation
     * of it for use by an extensional constraint.
     *
     * @param file      filename containing dictionary
     * @param wordSizes size of the words
     */
    public void readDictionaryFromFile(String file, List<Integer> wordSizes) {

        for (int wordSize : wordSizes) {

            int wordCount = 0;

            IntVar[] list = new IntVar[wordSize];
            for (int i = 0; i < wordSize; i++)
                list[i] = blank;

            int[] tupleForGivenWord = new int[wordSize];
            MDD resultForWordSize = new MDD(list);

            try (BufferedReader inr = new BufferedReader(new InputStreamReader(new FileInputStream(file), "UTF-8"))) {

                String str;
                while ((str = inr.readLine()) != null && str.length() > 0) {

                    str = str.trim();

                    // ignore comments
                    // starting with either # or %
                    if (str.startsWith("#") || str.startsWith("%")) {
                        continue;
                    }

                    if (str.length() != wordSize)
                        continue;

                    for (int i = 0; i < wordSize; i++) {
                        tupleForGivenWord[i] = str.charAt(i);
                    }

                    wordCount++;
                    resultForWordSize.addTuple(tupleForGivenWord);

                    //   				lineCount++;

                } // end while

            } catch (IOException e) {
                System.out.println(e);
            }

            System.out.println("There are " + wordCount + " words of size " + wordSize);
            resultForWordSize.reduce();
            mdds.put(wordSize, resultForWordSize);
        }

    }


    /**
     * It searches for all solutions. It does not record them and prints
     * every tenth of them.
     *
     * @return true if any solution was found, false otherwise.
     */
    public boolean searchAllAtOnceNoRecord() {

        long T1, T2;
        T1 = System.currentTimeMillis();

        SelectChoicePoint<IntVar> select =
            new SimpleSelect<IntVar>(vars.toArray(new IntVar[1]), new SmallestDomain<IntVar>(), new IndomainMin<IntVar>());

        search = new DepthFirstSearch<IntVar>();
        search.setSolutionListener(new PrintListener<IntVar>(crosswordTemplate));

        search.getSolutionListener().searchAll(true);
        search.getSolutionListener().recordSolutions(false);
        search.setAssignSolution(true);

        boolean result = search.labeling(store, select);

        T2 = System.currentTimeMillis();

        if (result) {
            System.out.println("Number of solutions " + search.getSolutionListener().solutionsNo());
            search.printAllSolutions();
        } else
            System.out.println("Failed to find any solution");

        System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");

        return result;
    }



    /**
     * It executes the program to create a model and solve
     * crossword problem.
     *
     * @param args no arguments used.
     */
    public static void main(String args[]) {

        String filename = "";
        if (args.length == 1) {
            filename = args[0];
            System.out.println("Using file " + filename);
        }

        CrossWord m = new CrossWord();

        m.model();

        long T1, T2;
        T1 = System.currentTimeMillis();

        m.searchAllAtOnceNoRecord();

        T2 = System.currentTimeMillis();

        System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");

    } // end main

    /**
     * It is a simple print listener to print every tenth solution encountered.
     */
    public class PrintListener<T extends Var> extends SimpleSolutionListener<T> {

        char[][] crossWordTemplate;

        public PrintListener(char[][] crosswordTemplate) {
            this.crossWordTemplate = crosswordTemplate;
        }

        @Override public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

            boolean returnCode = super.executeAfterSolution(search, select);


            if (noSolutions % 10 == 0) {
                System.out.println("Solution # " + noSolutions);
                printSolution(crossWordTemplate);
            }

            return returnCode;
        }


    }

} // end class

