/**
 *  SurvoPuzzle.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.jacop.examples.fd;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;

import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Sum;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
*
* It solves Survo puzzle.
*
* http://en.wikipedia.org/wiki/Survo_Puzzle
* """
* Survo puzzle is a kind of logic puzzle presented (in April 2006) and studied 
* by Seppo Mustonen. The name of the puzzle is associated to Mustonen's 
* Survo system which is a general environment for statistical computing and 
* related areas.
* 
* In a Survo puzzle the task is to fill an m * n table by integers 1,2,...,m*n so 
* that each of these numbers appears only once and their row and column sums are 
* equal to integers given on the bottom and the right side of the table. 
* Often some of the integers are given readily in the table in order to 
* guarantee uniqueness of the solution and/or for making the task easier.
* """
* 
* See also
* http://www.survo.fi/english/index.html
* http://www.survo.fi/puzzles/index.html
*
* References:
* - Mustonen, S. (2006b). "On certain cross sum puzzles"
*   http://www.survo.fi/papers/puzzles.pdf 
* - Mustonen, S. (2007b). "Enumeration of uniquely solvable open Survo puzzles." 
*   http://www.survo.fi/papers/enum_survo_puzzles.pdf 
* - Kimmo Vehkalahti: "Some comments on magic squares and Survo puzzles" 
*   http://www.helsinki.fi/~kvehkala/Kimmo_Vehkalahti_Windsor.pdf
*
*
* @author Hakan Kjellerstrand and Radoslaw Szymanek
* 
*/

public class SurvoPuzzle extends ExampleFD {

    int r;          // number of rows
    int c;          // number of column
    int[] rowsums;  // row sums
    int[] colsums;  // col sums
    int[][] matrix; // the clues matrix

    IntVar[][] x;      // the solution
    IntVar[] x_arr;    // x as an array, for alldifferent


    /**
     *
     *  model()
     *
     */
    @Override
	public void model() {

        store = new Store();

        if (matrix == null) {

            System.out.println("Using the default problem.");

            /* Default problem:
             *
             * http://www.survo.fi/puzzles/280708.txt, the third puzzle
             * Survo puzzle 128/2008 (1700) #364-35846
             */
            int r_tmp = 3;
            int c_tmp = 6;
            int[] rowsums_tmp = {30, 86, 55};
            int[] colsums_tmp = {22, 11, 42, 32, 27, 37};
            int[][] matrix_tmp = {{0, 0,  0, 0, 0, 0},
                                  {0, 0, 18, 0, 0, 0},
                                  {0, 0,   0, 0, 0, 0}};

            r = r_tmp;
            c = c_tmp;
            rowsums = rowsums_tmp;
            colsums = colsums_tmp;
            matrix = matrix_tmp;

        }

        //
        // initiate structures and variables
        //
        x = new IntVar[r][c];
        x_arr = new IntVar[r*c];
        for(int i = 0; i < r; i++) {
            for(int j = 0; j < c; j++) {
                x[i][j] = new IntVar(store, "x_" + i + "_" + j, 1, r*c);
                if (matrix[i][j] > 0) {
                    store.impose(new XeqC(x[i][j], matrix[i][j]));
                }
                x_arr[c*i+j] = new IntVar(store, "xa_" + i + "_" + j, 1, r*c);
                store.impose(new XeqY(x_arr[c*i+j],x[i][j])); 
            }
        }

        //
        // row sums
        //
        for(int i = 0; i < r; i++) {
            IntVar r_sum = new IntVar(store, "r_" + i, 1, r*c*r*c);
            store.impose(new Sum(x[i], r_sum));
            store.impose(new XeqC(r_sum, rowsums[i]));
        }


        //
        // column sums
        //
        for(int j = 0; j < c; j++) { 
            ArrayList<IntVar> cols = new ArrayList<IntVar>();
            for(int i = 0; i < r; i++) {
                cols.add(x[i][j]);
            }
            IntVar c_sum = new IntVar(store, "c_" + j, 1, r*c*r*c);
            store.impose(new Sum(cols, c_sum));
            store.impose(new XeqC(c_sum, colsums[j]));
        }

        // Alldifferent on the array version.
        store.impose(new Alldiff(x_arr));

        vars = new ArrayList<IntVar>();
        
        for (IntVar v : x_arr)
        	vars.add(v);
        
    }

    /**
     * It prints a matrix of variables. All variables must be grounded.
     * @param matrix matrix containing the grounded variables.
     * @param rows number of elements in the first dimension.
     * @param cols number of elements in the second dimension.
     */
    public static void printMatrix(IntVar[][] matrix, int rows, int cols) {

        for(int i = 0; i < rows; i++) {
            for(int j = 0; j < cols; j++) {
                System.out.print(matrix[i][j].value() + " ");
            }
            System.out.println();
        }

    } 
    
    
    /**
     *
     * readFile()
     *
     * Reads a Survo puzzle in the following format
     * 
     * % From http://www.survo.fi/puzzles/280708.txt
     * % Survo puzzle 128/2008 (1700) #364-35846
     * A  B  C  D  E  F
     * 1  *  *  *  *  *  * 30
     * 2  *  * 18  *  *  * 86
     * 3  *  *  *  *  *  * 55
     * 22 11 42 32 27 37
     * @param file the filename containing the problem description.
     *
     */
    public void readFile(String file) {

        System.out.println("readFile(" + file + ")");

        try {

            BufferedReader inr = new BufferedReader(new FileReader(file));
            String str;
            int lineCount = 0;
            ArrayList<ArrayList<Integer>> MatrixI = new ArrayList<ArrayList<Integer>>();
            while ((str = inr.readLine()) != null && str.length() > 0) {
                
                str = str.trim();
                
                // ignore comments
                // starting with either # or %
                if(str.startsWith("#") || str.startsWith("%")) {
                    continue;
                }

                str = str.replace("_", "");                                
                String row[] = str.split("\\s+");
                System.out.println(str);

                // first line: column names: Ignore but count them
                if (lineCount == 0) {
                    c = row.length;
                    colsums = new int[c];
                } else  {

                    // This is the last line: the column sums
                    if (row.length == c) {
                        colsums = new int[row.length];
                        for(int j = 0; j < row.length; j++) {
                            colsums[j] = Integer.parseInt(row[j]);
                        }
                        System.out.println();
                    } else {
                        // Otherwise:
                        // The problem matrix: index 1 .. row.length-1
                        // The row sums: index row.length
                        ArrayList<Integer> this_row = new ArrayList<Integer>();
                        for(int j = 0; j < row.length; j++) {
                            String s = row[j];
                            if (s.equals("*")) {
                                this_row.add(0);
                            } else {
                                this_row.add(Integer.parseInt(s));
                            }
                        }
                        MatrixI.add(this_row);
                    }
                   
                }
                
                lineCount++;

            } // end while

            inr.close();

            //
            // Now we know everything to be known:
            // Construct the problem matrix and column sums.
            //
            r = MatrixI.size();
            rowsums = new int[r];
            matrix = new int[r][c];
            for(int i = 0; i < r; i++) {
                ArrayList<Integer> this_row = MatrixI.get(i);
                for(int j = 1; j < c + 1 ; j++) {
                    matrix[i][j-1] = this_row.get(j);
                }
                rowsums[i] = this_row.get(c+1);
            }
            
            
        } catch (IOException e) {
            System.out.println(e);
        }
        
    } // end readFile


    /**
     *  
     * It executes the program to solve the specified SurvoPuzzle.
     * @param args the first argument specifies the filename containing the puzzle to be solved.
     *
     */
    public static void main(String args[]) {

        String filename = "";
        if (args.length == 1) {
            filename = args[0];
            System.out.println("Using file " + filename);
        }

        SurvoPuzzle m = new SurvoPuzzle();
        if (filename.length() > 0) {
            m.readFile(filename);
        }
        
        m.model();
    	
		long T1, T2;
		T1 = System.currentTimeMillis();
		
        boolean result = m.searchWithMaxRegret();

        if(result) {
            int numSolutions = m.search.getSolutionListener().solutionsNo();
            System.out.println("Number of solutions: " + numSolutions);
            printMatrix(m.x, m.r, m.c);
        }

        T2 = System.currentTimeMillis();

		System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");
        
    } // end main


} // end class

