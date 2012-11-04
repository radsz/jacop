/**
 *  MineSweeper.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Hakan Kjellerstrand and Radoslaw Szymanek
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

import org.jacop.constraints.Sum;
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
*
* It models and solves Minesweeper problem.
*
* @author Hakan Kjellerstrand (hakank@bonetmail.com) and Radoslaw Szymanek
* 
* This is a port of Hakan's MiniZinc model
* http://www.hakank.org/minizinc/minesweeper.mzn
* 
* which is commented in the (swedish) blog post
* "Fler constraint programming-modeller i MiniZinc, t.ex. Minesweeper och Game of Life"
* http://www.hakank.org/webblogg/archives/001231.html
*
* See also
*  
* The first 10 examples are from gecode/examples/minesweeper.cc
* http://www.gecode.org/gecode-doc-latest/minesweeper_8cc-source.html
*
* http://www.janko.at/Raetsel/Minesweeper/index.htm
*
* http://en.wikipedia.org/wiki/Minesweeper_(computer_game)
* 
* Ian Stewart on Minesweeper: http://www.claymath.org/Popular_Lectures/Minesweeper/
*
* Richard Kaye's Minesweeper Pages:
* http://web.mat.bham.ac.uk/R.W.Kaye/minesw/minesw.htm
*
* Some Minesweeper Configurations:
* http://web.mat.bham.ac.uk/R.W.Kaye/minesw/minesw.pdf
*
*
*/

public class MineSweeper extends ExampleFD {

    int r;        // number of rows
    int c;        // number of cols
    
    /**
     * It represents the unknown value in the problem matrix.
     */
    public static int X = -1; 

    IntVar[][] game;    // The FDV version of the problem matrix.
    IntVar[][] mines;   // solution matrix: 0..1 where 1 means mine.

    int [][] problem = null;


	@Override
    public void model() {

        store = new Store();

        if (problem == null)
        	problem = readFromArray(problem2);

        r = problem.length;
        c = problem[0].length;

        //
        // Initialize the constraint variables.
        //
        mines = new IntVar[r][c];
        game  = new IntVar[r][c];
        for(int i = 0; i < r; i++) {
            for(int j = 0; j < c; j++) {

                // 0: no mine, 1: mine
                mines[i][j] = new BooleanVar(store, "m_" + i + "_" + j);

                // mirrors the problem matrix
                game[i][j] = new IntVar(store, "g_" + i + "_" + j, -1, 8);

            }
        }

        // Add the constraints
        for(int i = 0; i < r; i++) {
            for(int j = 0; j < c; j++) {

                // This is a known value of neighbours
                if (problem[i][j] > X) {

                    // mirroring the problem matrix.
                    store.impose(new XeqC(game[i][j], problem[i][j]));

                    // This could not be a mine.
                    store.impose(new XeqC(mines[i][j], 0));

                    // Sum the number of neighbours: same as game[i][j].
                    // 
                    // Note: Maybe this could be modelled more elegant
                    // instead of using an ArrayList.
                    ArrayList<IntVar> lst = new ArrayList<IntVar>();
                    for(int a = -1; a <= 1; a++) {
                        for(int b = -1; b <= 1; b++) {
                            if (i+a >= 0 && j+b >=  0 &&
                                i+a < r && j+b < c) {
                                lst.add(mines[i+a][j+b]);
                            }
                        }                        
                    }
                    store.impose(new Sum(lst, game[i][j]));

                } // end if problem[i][j] > X

            } // end for j

        } // end for i

        // HakankUtil.toXML(store, -1, ".", "minesweeper.xml");

    } // end model


    /**
     * It executes special search with solution printing to present the solutions.
     * @param recordSolutions specifies if the solutions should be recorded.
     */
    public void searchSpecific(boolean recordSolutions) {

        // Note: This uses the SimpleMatrixSelect since
        // mines is a matrix.
        SelectChoicePoint<IntVar> select = 
            new SimpleMatrixSelect<IntVar> (mines,
                              new SmallestDomain<IntVar>(),
                              new IndomainMin<IntVar> ()
                              );
        
        
        search = new DepthFirstSearch<IntVar> ();
        search.getSolutionListener().searchAll(true);
        search.getSolutionListener().recordSolutions(recordSolutions);        
        
        boolean result = search.labeling(store, select);
        
        int numSolutions = search.getSolutionListener().solutionsNo();
        
        if (result) {

            if (numSolutions <= 100) {
                search.printAllSolutions();
            } else {
                System.out.println("Too many solutions to print...");
            }

            if (numSolutions > 1)
            	System.out.println("\nThe last solution:");
            else
            	System.out.println("\nThe solution:");
            
            for(int i = 0; i < r; i++) {
                for(int j = 0; j < c; j++) {
                    System.out.print(mines[i][j].value() + " ");
                }
                System.out.println();
            }

            System.out.println("numSolutions: " + numSolutions);

        } else {

            System.out.println("No solutions.");

        } // end if result


    } // end search

    

    
    /**
     * It transforms string representation of the problem into an array of ints
     * representation.
     * 
     * @param description array of strings representing the problem.
     * @return two dimensional array of ints representing the problem.
     */
    public static int[][] readFromArray(String[] description) {

        int r = description.length;
        int c = description[0].trim().length();
    	
        int[][] problem = new int[r][c]; // The problem matrix
        
        for (int i = 0; i < description.length; i++ ) {
        
        	String str = description[i];        	
        	str = str.trim();

        	// the problem matrix
            for(int j = 0; j < c; j++) {
              String s = str.substring(j, j+1);
              if (s.equals("."))
            	  problem[i][j] = X;
              else 
            	  problem[i][j] = Integer.parseInt(s);

            } // end for
            
        } // end for
    	
        return problem;
        
    }

    
    /**
     * One of the possible MineSweeper problems.
     */
    public static String[] problem1 = {
    		  "..2.3.",
			  "2.....",
			  "..24.3",
			  "1.34..",
			  ".....3",
			  ".3.3.."};

    /**
     * One of the possible MineSweeper problems.
     */
    public static String[] problem2 = {
           ".2.211..",
           "..4.2..2",
           "2..2..3.",
           "2.22.3.3",
           "..1...4.",
           "1...2..3",
           ".2.22.3.",
    	   "1.1..1.1"};
    
    /**
     * One of the possible MineSweeper problems.
     */
    public static String[] problem3 = {
    		"1..2.2.2..",
    		".32...4..1",
    		"...13...4.",
    		"3.1...3...",
    		".21.1..3.2",
    		".3.2..2.1.",
    		"2..32..2..",
    		".3...32..3",
    		"..3.33....",
           	".2.2...22."};
    
    /**
     * One of the possible MineSweeper problems.
     */
    public static String[] problem4 = {
    	   "2...3.1.",
           ".5.4...1",
           "..5..4..",
           "2...4.5.",
           ".2.4...2",
           "..5..4..",
           "2...5.4.",
           ".3.3...2"};
    
    /**
     * One of the possible MineSweeper problems.
     */
    public static String[] problem5 = {
           "0.0.1..11.",
          "1.2.2.22..",
           "......2..2",
           ".23.11....",
           "0......2.1",
           "...22.1...",
           ".....3.32.",
           ".5.2...3.1",
           ".3.1..3...",
           ".2...12..0"};
    
    /**
     * One of the possible MineSweeper problems.
     */
    public static String[] problem6 = {
    	   ".21.2.2...",
           ".4..3...53",
           "...4.44..3",
           "4.4..5.6..",
           "..45....54",
           "34....55..",
           "..4.4..5.5",
           "2..33.6...",
           "36...3..4.",
           "...4.2.21."};
    
    /**
     * One of the possible MineSweeper problems.
     */
    public static String[] problem7 = {
            ".32..1..",
           "....1..3",
           "3..2...4",
           ".5...5..",
           "..6...5.",
           "3...5..4",
           "2..5....",
           "..2..34."};
    
    /**
     * One of the possible MineSweeper problems.
     */
    public static String[] problem8 = {
           ".1.....3.",
           "...343...",
           "244...443",
           "...4.4...",
           ".4.4.3.6.",
           "...4.3...",
           "123...133",
          "...322...",
           ".2.....3."};
    
    /**
     * One of the possible MineSweeper problems.
     */
    public static String[] problem9 = {
           ".......",
           ".23435.",
           ".1...3.",
           "...5...",
           ".1...3.",
          ".12234.",
           "......."};
    
    /**
     * One of the possible MineSweeper problems.
     */
    public static String[] problem10 = {
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

    /**
     * One of the possible MineSweeper problems.
     */
    public static String[] problemTest = {
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

    /**
     * One of the possible MineSweeper problems.
     */
    public static String[] problem_kaye_splitter = {
		"...0...0...",
		"...01.10...",
		"...01.10...",
		"00001110000",
		".1111.1111.",
		"...1.2.1...",
		".1111.1111.",
		"00001110000",
		"...01.10...",
		"...01.10...",
		"...0...0..."};    
    
    
    /**
     * The collection of MineSweeper problems.
     */
    public static String[][] problems = {problem1, problem2, problem3, problem4, problem5, 
    									problem6, problem7, problem8, problem9, problem10};
    

    /**
    *
    * Reads a minesweeper file.
    * File format:
    *  # a comment which is ignored
    *  % a comment which also is ignored
    *  number of rows
    *  number of columns
    *  <
    *    row number of neighbours lines...
    *  >
    * 
    * 0..8 means number of neighbours, "." mean unknown (may be a mine)
    * 
    * Example (from minesweeper0.txt)
    * # Problem from Gecode/examples/minesweeper.cc  problem 0
    * 6
    * 6
    * ..2.3.
    * 2.....
    * ..24.3
    * 1.34..
    * .....3
    * .3.3..
     * @param file it specifies the filename containing the problem description.
     * @return the int array description of the problem.
    *
    */

    public static int[][] readFile(String file) {

        int[][] problem = null; // The problem matrix
        int r = 0;
        int c = 0;
        
        System.out.println("readFile(" + file + ")");
        int lineCount = 0;
        
        try {

            BufferedReader inr = new BufferedReader(new FileReader(file));
            String str;
            while ((str = inr.readLine()) != null && str.length() > 0) {

                str = str.trim();

                // ignore comments
                if(str.startsWith("#") || str.startsWith("%")) {
                    continue;
                }

                System.out.println(str);
                if (lineCount == 0) {
                    r = Integer.parseInt(str); // number of rows
                } else if (lineCount == 1) {
                    c = Integer.parseInt(str); // number of columns
                    problem = new int[r][c];
                } else {
                    // the problem matrix
                    String row[] = str.split("");
                    for(int j = 1; j <= c; j++) {
                        String s = row[j];
                        if (s.equals(".")) {
                            problem[lineCount-2][j-1] = -1;
                        } else {
                            problem[lineCount-2][j-1] = Integer.parseInt(s);
                        }
                    }
                }

                lineCount++;

            } // end while

            inr.close();

        } catch (IOException e) {
            System.out.println(e);
        }

        return problem;
        
    } // end readFile


    /**
     * 
     * It executes the program to solve any MineSweeper problem.
     * It is possible to supply the filename containing the problem specification.
     * 
     * @param args the filename containing the problem description.
     *
     */
    public static void main(String args[]) {

    	long T1, T2, T;
		T1 = System.currentTimeMillis();
        
        MineSweeper minesweeper = new MineSweeper();
        
		for (int i = 0; i < problems.length; i++) {
			
			T1 = System.currentTimeMillis();
        	
			minesweeper.problem = MineSweeper.readFromArray( problems[i] );
			
	        minesweeper.model();
	        
	        minesweeper.searchSpecific( true );
	        
	        T2 = System.currentTimeMillis();
			T = T2 - T1;
			System.out.println("\n\t*** Execution time = " + T + " ms");
			
		}

        if (args.length > 0)
        	minesweeper.problem = MineSweeper.readFile(args[0]);
        
        if (minesweeper.problem == null)
        	minesweeper.problem = MineSweeper.readFromArray(MineSweeper.problem_kaye_splitter);
        	        	
        minesweeper.model( );
        minesweeper.searchSpecific(false);
        
        minesweeper.problem = MineSweeper.readFromArray(MineSweeper.problemTest);
        minesweeper.model( );
        minesweeper.searchSpecific( true );

        T2 = System.currentTimeMillis();
		T = T2 - T1;
		System.out.println("\n\t*** Execution time = " + T + " ms");
		        
    } // end main

} // end class

