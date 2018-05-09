/*
 * BIBD.java
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
import java.util.List;

import org.jacop.constraints.AndBool;
import org.jacop.constraints.SumInt;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 *
 * It models and solves Balanced Incomplete Block Design (BIBD) problem (CSPLIB-P28). 
 *
 * @author Radoslaw Szymanek
 * @version 4.5
 */

public class BIBD extends ExampleFD {

    /**
     * It specifies number of rows in the incidence matrix.
     */
    public int v = 7;
    /**
     * It specifies number of columns in the incidence matrix.
     */
    public int b = 7;
    /**
     * It specifies number of ones in each row.
     */
    public int r = 3;
    /**
     * It specifies number of ones in each column.
     */
    public int k = 3;
    /**
     * It specifies the value of the scalar product of any two distinct rows.
     */
    public int lambda = 1;

    IntVar[][] x;

    @Override public void model() {

        store = new Store();
        vars = new ArrayList<IntVar>();

        // Get problem size n from second program argument.
        x = new IntVar[v][b];

        for (int i = 0; i < v; i++)
            for (int j = 0; j < b; j++) {
                x[i][j] = new BooleanVar(store, "x" + i + "_" + j);
                vars.add(x[i][j]);
            }

        IntVar rVar = new IntVar(store, "r", r, r);
        IntVar kVar = new IntVar(store, "k", k, k);
        IntVar lambdaVar = new IntVar(store, "lambda", lambda, lambda);

        for (int i = 0; i < v; i++) {
            store.impose(new SumInt(x[i], "==", rVar), 1);
        }

        for (int j = 0; j < b; j++) {
            IntVar[] column = new IntVar[v];
            for (int i = 0; i < v; i++)
                column[i] = x[i][j];
            store.impose(new SumInt(column, "==", kVar), 1);
        }

        for (int i = 0; i - 1 < v; i++)
            for (int j = i + 1; j < v; j++) {

                List<IntVar> result = new ArrayList<IntVar>();

                for (int m = 0; m < b; m++) {
                    BooleanVar product = new BooleanVar(store, "p" + i + "_" + j + "_" + m);
                    BooleanVar[] array = {(BooleanVar) x[i][m], (BooleanVar) x[j][m]};
                    store.imposeDecomposition(new AndBool(array, product), 0);
                    result.add(product);
                }

                store.impose(new SumInt(result, "==", lambdaVar), 1);
            }

    }


    /**
     * It executes the program to solve the Langford problem.
     * It is possible to specify two parameters. If no
     * parameter is used then default values for n and m are used.
     *
     * @param args the first parameter denotes n, the second parameter denotes m.
     */
    public static void main(String args[]) {

        BIBD example = new BIBD();

        if (args.length > 1) {
            try {
                example.v = Integer.parseInt(args[0]);
                example.b = Integer.parseInt(args[1]);
                example.r = Integer.parseInt(args[2]);
                example.k = Integer.parseInt(args[3]);
                example.lambda = Integer.parseInt(args[4]);
            } catch (Exception ex) {
                System.out.println("Program parameters if provided must specify v, b, r, k, and lambda");
            }
        }

        example.model();

        if (example.searchAllAtOnce()) {
            System.out.println("Solution(s) found");

            ExampleFD.printMatrix(example.x, example.v, example.b);

        }
    }


}
