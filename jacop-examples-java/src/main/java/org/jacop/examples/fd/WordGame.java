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

package org.jacop.examples.fd;

import org.jacop.constraints.ExtensionalSupportMDD;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XneqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.SmallestDomain;
import org.jacop.util.MDD;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Scanner;

/**
 * Inspired by time spent together with Ralph Nemer. It was fun playing together. I also had fun solving this one
 * as CP problem ;).
 *
 * @author Radoslaw Szymanek
 */
public class WordGame {

    public static String defaultDictionary = "src/main/java/org/jacop/examples/fd/crosswords/words";

    public static void main(String args[]) {

        Store store = new Store();

        // Define the unknown word with 5 variables (one for each letter)
        IntVar[] unknownWord = new IntVar[5];
        for (int i = 0; i < 5; i++) {
            unknownWord[i] = new IntVar(store, "Letter" + (i + 1), 'a', 'z');
        }

        store.impose(new ExtensionalSupportMDD(readDictionaryFor5LetterWords(defaultDictionary, unknownWord)));

        for (int attempt = 1; attempt <= 8; attempt++) {
            System.out.println("Attempt " + attempt);

            // Set up search
            SelectChoicePoint<IntVar> select = new SimpleSelect<>(unknownWord,
                    new SmallestDomain<>(), new IndomainMin<>());
            Search<IntVar> search = new DepthFirstSearch<>();
            PrintListener<IntVar> simpleSolutionListener = new PrintListener<IntVar>();
            search.setSolutionListener(simpleSolutionListener);
            simpleSolutionListener.searchAll(true);
            simpleSolutionListener.recordSolutions(false);
            search.setAssignSolution(false);
            search.setPrintInfo(false);

            // Get the user's guess word and its quality from the input
            char[] userGuess = getUserGuess();
            char[] quality = getUserGuessQuality();

            // Add constraints based on the provided quality of the guess
            for (int i = 0; i < 5; i++) {
                if (quality[i] == '!') {
                    for (IntVar unknownLetter : unknownWord) {
                        store.impose(new XneqC(unknownLetter, userGuess[i]));
                    }
                } else if (quality[i] == '+') {
                    store.impose(new XeqC(unknownWord[i], userGuess[i]));
                } else if (quality[i] == '-') {

                    ArrayList<PrimitiveConstraint> constraints = new ArrayList<>();
                    for (int j = 0; j < 5; j++) {
                        if (i != j) {
                            constraints.add( new XeqC(unknownWord[j], userGuess[i]));
                        }
                    }
                    store.impose(new Or(constraints));
                }
            }

            store.consistency();

            // Find solutions up to the specified limit
            search.labeling(store, select);

            if (search.getSolutionListener().solutionsNo() == 1) {
                // Found one and one solution.
                break;
            }

        }
    }

    /**
     * It is a simple print listener to print every tenth solution encountered.
     */
    public static class PrintListener<T extends Var> extends SimpleSolutionListener<T> {

        @Override public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

            boolean returnCode = super.executeAfterSolution(search, select);

            for (int i = 0; i < vars.length; i++) {
                System.out.print((char)((IntVar)vars[i]).dom().min());
            }
            System.out.println(" ");

            return returnCode;
        }


    }

    /**
     * It reads a dictionary for 5-letter words and creates an MDD representation
     * of it for use by an extensional constraint.
     *
     * @param file      filename containing dictionary
     * @return the created MDD for 5-letter words
     */
    public static MDD readDictionaryFor5LetterWords(String file, IntVar[] list) {

        int wordSize = 5;

        int[] tupleForGivenWord = new int[wordSize];
        MDD resultForWordSize = new MDD(list);

        try (BufferedReader inr = new BufferedReader(new InputStreamReader(new FileInputStream(file), "UTF-8"))) {
            String str;
            while ((str = inr.readLine()) != null && str.length() > 0) {
                str = str.trim();
                // ignore comments starting with either # or %
                if (str.startsWith("#") || str.startsWith("%")) {
                    continue;
                }

                if (str.length() != wordSize)
                    continue;

                for (int i = 0; i < wordSize; i++) {
                    tupleForGivenWord[i] = str.charAt(i);
                }

                resultForWordSize.addTuple(tupleForGivenWord);
            } // end while

        } catch (IOException e) {
            System.out.println(e);
        }

        resultForWordSize.reduce();
        return resultForWordSize;
    }

    private static char[] getUserGuessQuality() {
        Scanner scanner = new Scanner(System.in);
        System.out.println("Enter the quality of your guess:");
        System.out.println("! : The letter is not present in the unknown word.");
        System.out.println("+ : The letter is present and in the correct position in the unknown word.");
        System.out.println("- : The letter is present but not in the correct position in the unknown word.");
        System.out.print("Quality: ");
        String input = scanner.nextLine();
        return input.toCharArray();
    }

    private static char[] getUserGuess() {
        Scanner scanner = new Scanner(System.in);
        System.out.print("Enter your guess word: ");
        String input = scanner.nextLine();
        return input.toCharArray();
    }

} // end class

