/*
 * Queens.java
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

import java.util.ArrayList;

import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Element;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 *
 * It models the queens problem in different ways as well as applies 
 * different search methods.
 *
 * @author Radoslaw Szymanek
 * @version 4.5
 *
 */
public class Queens extends ExampleFD {

    // Place n queens on a chessboard of size nxn
    // so none queen checks another queen
    // This program uses only primitive (basic) constraints

    // Example of queen placement in 4x4 chessboard
    // ---------
    // | | |Q| |
    // ---------
    // |Q| | | |
    // ---------
    // | | | |Q|
    // ---------
    // | |Q| | |
    // ---------

    /**
     * It specifies the size of chessboard to be used in the model.
     */
    public int numberQ = 550;

    /**
     * This model uses only primitive constraints.
     */
    public void modelBasic() {

        // Creating constraint store
        store = new Store();
        vars = new ArrayList<IntVar>();

        // I-th queen variable represents the placement
        // of a queen in i-th column
        // There are n columns so there are n variables
        IntVar queens[] = new IntVar[numberQ];

        // Each queen variable has a domain from 1 to numberQ
        // Value of queen variable represents the row
        for (int i = 0; i < numberQ; i++) {
            queens[i] = new IntVar(store, "Q" + (i + 1), 1, numberQ);
            vars.add(queens[i]);
        }
        // Queens from different columns can not be placed
        // in the same row, therefore the values
        // must be different
        for (int i = 0; i < queens.length; i++)
            for (int j = i - 1; j >= 0; j--)
                store.impose(new XneqY(queens[i], queens[j]));

        // Notice that j index starts from i+1
        for (int i = 0; i < queens.length; i++)
            for (int j = i + 1; j < queens.length; j++) {

                // Temporary variable denotes the chessboard
                // field in j-th column which is checked by
                // i-th column queen
                // If temporarty variable has value outside
                // range 1..numberQ then i-th column queen
                // does not check any field in j-th column

                // Checking diagonals like this \
                // Note that C constant is positive
                IntVar temporary = new IntVar(store, -2 * numberQ, 2 * numberQ);
                store.impose(new XplusCeqZ(queens[j], j - i, temporary));
                store.impose(new XneqY(queens[i], temporary));

                // Checking diagonals like this /
                // Note that C constant is negative
                temporary = new IntVar(store, -2 * numberQ, 2 * numberQ);
                store.impose(new XplusCeqZ(queens[j], -(j - i), temporary));
                store.impose(new XneqY(queens[i], temporary));

            }

    }


    /**
     * This model uses dual model to solve Queens problems.
     */
    public void modelChanneling() {

        // Creating constraint store
        store = new Store();
        vars = new ArrayList<IntVar>();

        // Global model

        IntVar queens[] = new IntVar[numberQ];

        for (int i = 0; i < numberQ; i++) {
            queens[i] = new IntVar(store, "Q" + (i + 1), 1, numberQ);
            vars.add(queens[i]);
        }

        store.impose(new Alldiff(queens));

        IntVar[] diagonalUp = new IntVar[queens.length];
        IntVar[] diagonalDown = new IntVar[queens.length];

        diagonalUp[0] = queens[0]; // diagonal like this /
        diagonalDown[0] = queens[0]; // diagonal like this \

        for (int i = 1; i < queens.length; i++) {

            diagonalUp[i] = new IntVar(store, -2 * numberQ, 2 * numberQ);
            store.impose(new XplusCeqZ(queens[i], i, diagonalUp[i]));

            diagonalDown[i] = new IntVar(store, -2 * numberQ, 2 * numberQ);
            store.impose(new XplusCeqZ(queens[i], -i, diagonalDown[i]));

        }

        store.impose(new Alldiff(diagonalUp));
        store.impose(new Alldiff(diagonalDown));

        // Channeling constraints

        IntVar[] values = new IntVar[numberQ];

        IntVar queensRows[] = new IntVar[numberQ];

        for (int i = 0; i < numberQ; i++) {
            queensRows[i] = new IntVar(store, "Qrows" + (i + 1), 1, numberQ);
            vars.add(queensRows[i]);
        }

        for (int i = 0; i < numberQ; i++)
            values[i] = new IntVar(store, "val-" + (i + 1), i + 1, i + 1);

        for (int i = 0; i < numberQ; i++)
            store.impose(Element.choose(queensRows[i], queens, values[i]));

    }

    @Override public void model() {

        // Creating constraint store
        store = new Store();
        vars = new ArrayList<IntVar>();

        // I-th queen variable represents the placement
        // of a queen in i-th column
        // There are n columns so there are n variables
        IntVar queens[] = new IntVar[numberQ];

        for (int i = 0; i < numberQ; i++) {
            queens[i] = new IntVar(store, "Q" + (i + 1), 1, numberQ);
            vars.add(queens[i]);
        }
        // symmetry breaking - not usefull in this problem
        // FDV one = new FDV(store, "one", 1, 1);
        // FDV firstRowPosition = new FDV(store, "firstRowPosition", 0,
        // numberQ);
        // store.impose(new Element(firstRowPosition, queens, one));
        // store.impose(new XltY(queens[0], firstRowPosition));

        store.impose(new Alldiff(queens));

        IntVar[] diagonalUp = new IntVar[queens.length];
        IntVar[] diagonalDown = new IntVar[queens.length];

        diagonalUp[0] = queens[0]; // diagonal like this /
        diagonalDown[0] = queens[0]; // diagonal like this \

        for (int i = 1; i < queens.length; i++) {

            // Position of every queen is shifted based on a distance
            // to column 1, If any queen can check another on diagonal
            // then the position after shifting will be equal to the
            // position of the checked queen. Therefore the diagonal list
            // is used in Alldifferent constraint
            diagonalUp[i] = new IntVar(store, -2 * numberQ, 2 * numberQ);
            store.impose(new XplusCeqZ(queens[i], i, diagonalUp[i]));

            diagonalDown[i] = new IntVar(store, -2 * numberQ, 2 * numberQ);
            store.impose(new XplusCeqZ(queens[i], -i, diagonalDown[i]));

        }

        // Imposes constraints so queens can not check each other using
        // diagonals.
        store.impose(new Alldiff(diagonalUp));
        store.impose(new Alldiff(diagonalDown));

    }

    /**
     * It executes different models and search methods to solve Queens problem.
     * @param args first argument specifies the size of the chessboard.
     */
    public static void main(String args[]) {

        Queens example = new Queens();

        // It is possible to supply the program
        // with the chessboard size
        if (args.length != 0)
            example.numberQ = Integer.parseInt(args[0]);

        example.model();

        if (example.searchSmallestMiddle())
            System.out.println("Solution(s) found");

    }


    /**
     * It executes different models and search methods to solve Queens problem.
     * @param args first argument specifies the size of the chessboard.
     */
    public static void test(String args[]) {

        Queens example = new Queens();

        // It is possible to supply the program
        // with the chessboard size
        if (args.length != 0)
            example.numberQ = Integer.parseInt(args[0]);

        example.model();

        if (example.searchSmallestMiddle())
            System.out.println("Solution(s) found");

        example = new Queens();

        // It is possible to supply the program
        // with the chessboard size
        if (args.length != 0)
            example.numberQ = Integer.parseInt(args[0]);

        example.modelBasic();

        if (example.searchLDS(3))
            System.out.println("Solution(s) found");

        example = new Queens();

        // It is possible to supply the program
        // with the chessboard size
        if (args.length != 0)
            example.numberQ = Integer.parseInt(args[0]);

        example.modelChanneling();

        if (example.searchSmallestMiddle())
            System.out.println("Solution(s) found");

    }

}
