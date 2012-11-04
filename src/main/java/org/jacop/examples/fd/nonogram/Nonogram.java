/**
 *  Nonogram.java 
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

package org.jacop.examples.fd.nonogram;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.regex.Pattern;

import org.jacop.constraints.ExtensionalSupportMDD;
import org.jacop.constraints.regular.Regular;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.InputOrderSelect;
import org.jacop.search.SelectChoicePoint;
import org.jacop.util.fsm.FSM;
import org.jacop.util.fsm.FSMState;
import org.jacop.util.fsm.FSMTransition;

/**
 * 
 * It solves a nonogram example problem, sometimes also called Paint by Numbers.
 * 
 * 
 * @author Radoslaw Szymanek
 * 
 */

public class Nonogram extends ExampleFD {

	/**
	 * The value that represents a black dot.
	 */
	public int black = 1;
	
	/**
	 * The value that represents a white dot.
	 */
	public int white = 0;

	/**
	 * A board to be painted in white/black dots.
	 */
	public IntVar[][] board;

	/**
	 * It specifies if the slide based decomposition of the regular constraint
	 * should be applied. This decomposition uses ternary extensional support 
	 * constraints. It achieves GAC if FSM is deterministic. 
	 */
	public boolean slideDecomposition = false;

	/**
	 * It specifies if the regular constraint should be used.
	 */
	public boolean regular = true;

	/**
	 * It specifies if one extensional constraint based on MDD created from FSM
	 * should be used. The translation process works if FSM is deterministic.
	 */
	public boolean extensionalMDD = false;

	public void readFromFile(String filename) {
		
		String lines[] = new String[100];

		int [] dimensions = new int[2];

		/* read from file args[0] or qcp.txt */
		try {

			BufferedReader in = new BufferedReader(new FileReader(filename));
			String str;

			str = in.readLine();

			Pattern pat = Pattern.compile(" ");
			String[] result = pat.split(str);
			
			int current = 0;
			for (int j = 0; j < result.length; j++)
				try {
					int currentNo = new Integer(result[j]);
					dimensions[current++] = currentNo;
				} catch (Exception ex) {

				}
					
			lines = new String[dimensions[0] + dimensions[1]];
			
			int n = 0;
			
			while ((str = in.readLine()) != null && n < lines.length) {
				lines[n] = str;
				n++;
			}
			in.close();
		} catch (FileNotFoundException e) {
			System.err.println("I can not find file " + filename);
		} catch (IOException e) {
			System.err.println("Something is wrong with file" + filename);
		}

		row_rules = new int[dimensions[1]][];
		col_rules = new int[dimensions[0]][];

		// Transforms strings into ints
		for (int i = 0; i < lines.length; i++) {
			
			Pattern pat = Pattern.compile(" ");
			String[] result = pat.split(lines[i]);

			int [] sequence = new int [result.length];
			
			int current = 0;
			for (int j = 0; j < result.length; j++)
				try {
					sequence[current++] = Integer.valueOf(result[j]);
				} catch (Exception ex) {}
				
			if (i < row_rules.length) row_rules[i] = sequence;
			else
				col_rules[i - row_rules.length] = sequence;
		}

	}
	
	
	/**
	 * It produces and FSM given a sequence representing a rule. e.g. [2, 3]
	 * specifies that there are two black dots followed by three black dots.
	 * 
	 * @param sequence
	 * @return Finite State Machine used by Regular automaton to enforce proper sequence.
	 */
	public FSM createAutomaton(int [] sequence) {
		
		FSM result = new FSM();
		
		FSMState currentState = new FSMState();
	
		result.initState = currentState;
		IntDomain blackEncountered = new IntervalDomain(black, black);
		IntDomain whiteEncountered = new IntervalDomain(white, white);
		
		FSMTransition white = new FSMTransition(whiteEncountered, currentState);
		currentState.addTransition(white);
		
		for (int i = 0; i < sequence.length; i++) {
			if (sequence[i] == 0)
				continue;
			for (int j = 0; j < sequence[i]; j++) {
				// Black transition
				FSMState nextState = new FSMState();
				FSMTransition black = new FSMTransition(blackEncountered, nextState);
				currentState.addTransition(black);
				result.allStates.add(currentState);
				currentState = nextState;
			}
			// White transitions
			if (i + 1 != sequence.length) {
				FSMState nextState = new FSMState();
				white = new FSMTransition(whiteEncountered, nextState);
				currentState.addTransition(white);
				result.allStates.add(currentState);
				currentState = nextState;
			}
			
			white = new FSMTransition(whiteEncountered, currentState);
			currentState.addTransition(white);
			
		}
		
		result.allStates.add(currentState);
		result.finalStates.add(currentState);
		
		return result;
	}
	
	
	@Override
	public void model() {

		// Creating constraint store
		store = new Store();
		vars = new ArrayList<IntVar>();

		// Specifying what values are allowed.
		IntervalDomain values = new IntervalDomain();
		values.unionAdapt(black, black);
		values.unionAdapt(white, white);
		
		// Specifying the board with allowed values.
		board = new IntVar[row_rules.length][col_rules.length];
		
		for (int i = 0; i < board.length; i++) 
			for (int j = 0; j < board[0].length; j++) {
				board[i][j] = new IntVar(store, "board[" + i + "][" + j + "]", 
										   values.clone());
			}
		
		// Zigzag based variable ordering. 
		for (int m = 0; m < row_rules.length + col_rules.length - 1; m++) {
			for (int j = 0; j <= m && j < col_rules.length; j++) {
				int i = m - j;
				if (i >= row_rules.length)
					continue;
				vars.add(board[i][j]);
			}
		}		
		
		System.out.println("Size " + vars.size());
		
		// Making sure that rows respect the rules.
		for (int i = 0; i < row_rules.length; i++) {
			
			FSM result = this.createAutomaton(row_rules[i]);
			
			if (slideDecomposition)
				store.imposeDecomposition(new Regular(result, board[i]));
			
			if (regular)
				store.impose(new Regular(result, board[i]));
			
			if (extensionalMDD)
				store.impose(new ExtensionalSupportMDD(result.transformDirectlyIntoMDD(board[i])));
				
			
		}
		
		// Making sure that columns respect the rules.
		for (int i = 0; i < col_rules.length; i++) {
					
			FSM result = createAutomaton(col_rules[i]);
			IntVar[] column = new IntVar[row_rules.length];
			
			for (int j = 0; j < column.length; j++)
				column[j] = board[j][i];
							
			if (slideDecomposition)
				store.imposeDecomposition(new Regular(result, column));

			if (regular)
				store.impose(new Regular(result, column));
			
			if (extensionalMDD)
				store.impose(new ExtensionalSupportMDD(result.transformDirectlyIntoMDD(column)));

		
		}
		
	}
			
	
	/**
	 * It specifies simple search method based on most constrained static and lexigraphical 
	 * ordering of values. It searches for all solutions.
	 * 
	 * @return true if there is a solution, false otherwise.
	 */

	public boolean searchAll() {
		
		long T1, T2;

		// In case of nonograms, value ordering does not matter since we 
		// a) search for all solutions
		// b) all variables have binary domain.
		SelectChoicePoint<IntVar> select = new InputOrderSelect<IntVar>(store, vars.toArray(new IntVar[1]), new IndomainMin<IntVar>());

		search = new DepthFirstSearch<IntVar>();
		
		search.getSolutionListener().searchAll(true);
		search.getSolutionListener().recordSolutions(false);
		search.setAssignSolution(true);
		
		System.out.println("Search has begun ...");
		
		T1 = System.currentTimeMillis();
		
		boolean result = search.labeling(store, select);

		T2 = System.currentTimeMillis();

		if (result) {
			System.out.println("Number of solutions " + search.getSolutionListener().solutionsNo());
			search.printAllSolutions();
		} 
		else
			System.out.println("Failed to find any solution");

		System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");

		return result;
	}
	  /**
     * It prints a matrix of variables. All variables must be grounded.
     * @param matrix matrix containing the grounded variables.
     */
    public void printMatrix(IntVar[][] matrix) {

        for(int i = 0; i < matrix.length; i++) {
            for(int j = 0; j < matrix[i].length; j++) {
            	if ( matrix[i][j].value() == black )
            		System.out.print("0");
            	else
            		System.out.print(" ");
            }
            System.out.println();
        }

    }

	/**
	 * It executes the program which solves this simple problem.
	 * @param args no arguments are read.
	 */
	public static void main(String args[]) {

		Nonogram example = new Nonogram();
		
		example.model();
		if (example.searchAll())
			System.out.println("Solution(s) found");
		
		example.printMatrix(example.board);
				
	}		

	/**
	 * It executes the program which solves this simple problem.
	 * @param args no arguments are read.
	 */
	public static void test(String args[]) {

		Nonogram example = new Nonogram();
		
		example.model();
		if (example.searchAll())
			System.out.println("Solution(s) found");
		example.printMatrix(example.board);
		
		for (int i = 0; i <= 150; i++) {
			
			String no = String.valueOf(i);
			while (no.length() < 3)
				no = "0" + no;
			
			System.out.println("Problem file data" + no + ".nin");
			example.readFromFile("ExamplesJaCoP/nonogramRepository/data" + no + ".nin");
			example.model();
		
			if (example.searchAll())
				System.out.println("Solution(s) found");
		
			example.printMatrix(example.board);
		}
		
	}		

	/**
	 * It specifies a rule for each row.
	 */
	
	public int[][] row_rules = { 
		  {0,0,0,0,2,2,3},
		  {0,0,4,1,1,1,4},
		  {0,0,4,1,2,1,1},
		  {4,1,1,1,1,1,1},
		  {0,2,1,1,2,3,5},
		  {0,1,1,1,1,2,1},
		  {0,0,3,1,5,1,2},
		  {0,3,2,2,1,2,2},
		  {2,1,4,1,1,1,1},
		  {0,2,2,1,2,1,2},
		  {0,1,1,1,3,2,3},
		  {0,0,1,1,2,7,3},
		  {0,0,1,2,2,1,5},
		  {0,0,3,2,2,1,2},
		  {0,0,0,3,2,1,2},
		  {0,0,0,0,5,1,2},
		  {0,0,0,2,2,1,2},
		  {0,0,0,4,2,1,2},
		  {0,0,0,6,2,3,2},
		  {0,0,0,7,4,3,2},
		  {0,0,0,0,7,4,4},
		  {0,0,0,0,7,1,4},
		  {0,0,0,0,6,1,4},
		  {0,0,0,0,4,2,2},
		  {0,0,0,0,0,2,1}
	};
	
	/**
	 * It specifies a rule for each column.
	 */
	
	public int[][] col_rules = { 
		   {0,0,1,1,2,2},
		   {0,0,0,5,5,7},
		   {0,0,5,2,2,9},
		   {0,0,3,2,3,9},
		   {0,1,1,3,2,7},
		   {0,0,0,3,1,5},
		   {0,7,1,1,1,3},
		   {1,2,1,1,2,1},
		   {0,0,0,4,2,4},
		   {0,0,1,2,2,2},
		   {0,0,0,4,6,2},
		   {0,0,1,2,2,1},
		   {0,0,3,3,2,1},
		   {0,0,0,4,1,15},
		   {1,1,1,3,1,1},
		   {2,1,1,2,2,3},
		   {0,0,1,4,4,1},
		   {0,0,1,4,3,2},
		   {0,0,1,1,2,2},
		   {0,7,2,3,1,1},
		   {0,2,1,1,1,5},
		   {0,0,0,1,2,5},
		   {0,0,1,1,1,3},
		   {0,0,0,4,2,1},
		   {0,0,0,0,0,3}
	};
	
	
	
  /*
  public int[][]	row_rules = {
	{2},
	{2},
	{2},
	{2},
	{12},
	{2},
	{2},
	{2},
	{2},
	{2},
	{2},
	{2},
	{2},
	{2},
	{2},
	{2},
	{14},
	{14},
	{1,2},
	{1,2},
	{1,2},
	{1,2},
	{11,2},
	{1,2},
	{1,2},
	{1,2},
	{1,2},
	{1,5},
	{1,5},
	{1,5},
	{1,5},
	{1,5},
	{1,5},
	{1,24},
	{32},
	{26},
	{26},
	{26},
	{3,8,7,2},
	{3,7,6,2},
	{3,7,6,2},
	{3,7,6,2},
	{3,8,7,2},
	{26},
	{34},
	{34},
	{34},
	{34},
	{34},
	{24},
	{5,3,5},
	{3,5,3,5},
	{2,2,24},
	{1,1,24},
	{2,29},
	{5,24,2},
	{3,26,2},
	{41,3},
	{43,2},
	{42,3},
	{41,2},
	{41,2},
	{4,2,2,2,2,5},
	{42},
	{42},
	{42},
	{64},
	{86},
	{83},
	{65},
	{75},
	{71},
	{60,10},
	{6,53,10},
	{6,25,24,10},
	{19,17,3,44},
	{30,12,40},
	{12,19,22},
	{9,24,16},
	{4,20,8,11},
	{5,24,6,2,3},
	{38,6,2,6},
	{45,8,8},
	{52,3},
	{51,1},
	{51,2},
	{50,1},
	{50,1},
	{50,1},
	{34,9,2},
	{31,6,7,7,1},
	{29,10,6,3,5,1},
	{27,8,5,5,3,1},
	{25,5,5,4,10,5,2},
	{23,3,11,2,3,3,5,1},
	{20,3,16,2,8,11,1},
	{18,2,8,4,1,9,3,7,2},
	{15,4,8,5,4,12,5,9,1},
	{11,5,7,8,2,14,5,11,1},
	{7,7,6,13,9,15,15}};
	
	public int[][]	col_rules = {
	{2},
	{4},
	{8},
	{2,13},
	{2,17},
	{2,18},
	{2,19},
	{2,19},
	{2,19},
	{1,2,19},
	{2,2,19},
	{2,2,19},
	{2,2,19},
	{2,2,19},
	{2,2,19},
	{2,2,18},
	{2,26,1},
	{2,9,17,1},
	{2,10,17,1},
	{2,10,16,2},
	{2,9,17,2},
	{2,9,17,2},
	{2,3,3,16,3},
	{13,16,2},
	{13,15,1},
	{12,16,2,1},
	{12,15,2,1},
	{12,15,1,2},
	{11,15,2,3},
	{11,15,1,3},
	{11,14,2,4},
	{1,3,20,14,1,3},
	{1,1,2,23,13,1,4},
	{1,1,1,21,14,2,4},
	{1,1,5,2,22,13,3,3,1},
	{1,1,5,4,5,13,13,2,3,1},
	{1,1,5,2,5,13,12,2,3,1},
	{31,1,6,13,12,3,3,2},
	{1,15,1,6,13,12,3,2,2},
	{1,29,13,12,3,2,3},
	{1,5,32,13,3,2,3},
	{1,42,13,2,3,3},
	{1,29,12,13,2,3,3},
	{29,12,14,1,3,3},
	{2,17,10,12,4,8,3,2},
	{1,2,17,10,12,3,8,4,1},
	{1,2,17,10,12,3,2,9,4,1},
	{1,2,17,23,3,2,10,3},
	{1,2,6,8,22,3,2,11,3},
	{1,2,11,19,11,4,2,11,3},
	{38,19,11,4,2,13,1},
	{38,19,11,25},
	{1,2,11,7,10,12,1,1,3},
	{1,2,12,8,10,12,1,1,5},
	{1,2,17,23,1,1,7},
	{1,2,17,24,1,1,7},
	{1,2,17,10,13,1,1,8},
	{2,17,10,13,1,1,3,5},
	{29,13,4,3,4},
	{29,14,2,4,4},
	{5,19,14,1,2,4},
	{29,14,1,1,3},
	{44,2,2,2},
	{5,20,2,3,1},
	{5,5,14,2,2,2},
	{5,5,15,3,2,1},
	{5,5,15,3,3,1},
	{5,5,15,6,1},
	{5,15,3,3},
	{21,3,3},
	{21,3,3},
	{22,2,2},
	{2,17,2,2},
	{2,2,13,3,1},
	{1,2,13,2,1},
	{2,2,13,2,1},
	{2,1,6,5,4},
	{1,2,14,4},
	{1,14,4},
	{14,2},
	{14,2},
	{14,3},
	{14,2},
	{14,2},
	{15,2},
	{15,2},
	{15,2},
	{5,2,1,1},
	{2,1,2,1,1},
	{2,1,2,1,1},
	{2,1,2,1,1},
	{2,1,2,2,1},
	{2,1,2,2,1},
	{1,2,1,1},
	{1,2,1,1},
	{2,1,4},
	{2,1,4},
	{2,2,5},
	{2,2,5},
	{3}};
	*/
	/*
	public int[][]	row_rules = {
			  {3},
			  {5},
			  {3,1},
			  {2,1},
			  {3,3,4},
			  {2,2,7},
			  {6,1,1},
			  {4,2,2},
			  {1,1},
			  {3,1},
			  {6},
			  {2,7},
			  {6,3,1},
			  {1,2,2,1,1},
			  {4,1,1,3},
			  {4,2,2},
			  {3,3,1},
			  {3,3},
			  {3},
			  {2,1}
			};

	public int[][]	col_rules = 
	 {
	  {2},
	  {1,2},
	  {2,3},
	  {2,3},
	  {3,1,1},
	  {2,1,1},
	  {1,1,1,2,2},
	  {1,1,3,1,3},
	  {2,6,4},
	  {3,3,9,1},
	  {5,3,2},
	  {3,1,2,2},
	  {2,1,7},
	  {3,3,2},
	  {2,4},
	  {2,1,2},
	  {2,2,1},
	  {2,2},
	  {1},
	  {1}
	 };
	*/

	/*
	public int[][] col_rules = { {3}, {1 ,1}, {1,1}, {2}};
	public int[][] row_rules = { {4}, {1,1}, {2}, {1}};
    */	
	
}
