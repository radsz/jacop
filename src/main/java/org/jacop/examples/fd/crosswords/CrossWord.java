/**
 *  Store.java 
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

package org.jacop.examples.fd.crosswords;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;

import org.jacop.constraints.ExtensionalSupportMDD;
import org.jacop.constraints.XeqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.SmallestDomain;
import org.jacop.util.MDD;

/**
*
* It is an example of the power of ExtensionalSupportMDD constraint which can be used
* to efficiently model and solve CrossWord puzzles. 
*
* @author : Radoslaw Szymanek
* 
* This program uses problem instances and dictionary obtained from Hadrien Cambazard.
* 
*/
public class CrossWord extends ExampleFD {

    int r = 5;          // number of rows
    int c = 5;          // number of column
    int[] wordSizesPrimitive = {4, 5};
    ArrayList<Integer> wordSizes = new ArrayList<Integer>();
    // * - black wall
    // letter - letter which must be in crossword
    // _ - unknown letter, any letter is accepted.
    
    IntVar[][] x;      // the solution
    IntVar blank;
    
    String defaultDictionary = "./words";

    HashMap<String, Integer> mapping = new HashMap<String, Integer>();
    HashMap<Integer, String> mappingReverse = new HashMap<Integer, String>();

    
  	HashMap<Integer, MDD> mdds = new HashMap<Integer, MDD>();

    char[][] crosswordTemplate = {{'*', '_', '_', '_', '_'},
                                  {'_', '_', '_', 'l', '_'},
                                  {'_', '_', '_', '_', '_'},
                                  {'_', 'e', '_', '_', '_'},
                                  {'_', '_', 'm', '_', '_'}};

    /**
     *
     *  model()
     *
     */
    @Override
	public void model() {

        store = new Store();

        mapping.put("q", 1); 
        mapping.put("w", 2);
        mapping.put("e", 3);
        mapping.put("r", 4);
        mapping.put("t", 5);
        mapping.put("z", 6);
        mapping.put("u", 7);
        mapping.put("i", 8);
        mapping.put("o", 9);
        mapping.put("p", 10);
        mapping.put("a", 11);
        mapping.put("s", 12);
        mapping.put("d", 13);
        mapping.put("f", 14);
        mapping.put("g", 15);
        mapping.put("h", 16);
        mapping.put("j", 17);
        mapping.put("k", 18);
        mapping.put("l", 19);
        mapping.put("y", 20);
        mapping.put("x", 21);
        mapping.put("c", 22);
        mapping.put("v", 23);
        mapping.put("b", 24);
        mapping.put("n", 25);
        mapping.put("m", 26);

        
        mappingReverse.put(1,"q"); 
        mappingReverse.put(2,"w");
        mappingReverse.put(3,"e");
        mappingReverse.put(4,"r");
        mappingReverse.put(5,"t");
        mappingReverse.put(6,"z");
        mappingReverse.put(7,"u");
        mappingReverse.put(8,"i");
        mappingReverse.put(9,"o");
        mappingReverse.put(10,"p");
        mappingReverse.put(11,"a");
        mappingReverse.put(12,"s");
        mappingReverse.put(13,"d");
        mappingReverse.put(14,"f");
        mappingReverse.put(15,"g");
        mappingReverse.put(16,"h");
        mappingReverse.put(17,"j");
        mappingReverse.put(18,"k");
        mappingReverse.put(19,"l");
        mappingReverse.put(20,"y");
        mappingReverse.put(21,"x");
        mappingReverse.put(22,"c");
        mappingReverse.put(23,"v");
        mappingReverse.put(24,"b");
        mappingReverse.put(25,"n");
        mappingReverse.put(26,"m");

        blank = new IntVar(store, "blank", 1, 26);

        for (int s : wordSizesPrimitive)
            wordSizes.add(s);

        x = new IntVar[crosswordTemplate.length][];

        for (int i = 0; i < crosswordTemplate.length; i++)
           	x[i] = new IntVar[crosswordTemplate[i].length];

        readDictionaryFromFile(defaultDictionary, wordSizes);
        
        
        //
        // initiate structures and variables
        //
        
        for(int i = 0; i < r; i++) {
            for(int j = 0; j < c; j++) {
                if (crosswordTemplate[i][j] != '*') {
                    x[i][j] = new IntVar(store, "x_" + i + "_" + j, 1, 26);
                    if (crosswordTemplate[i][j] != '_') {
                        store.impose(new XeqC(x[i][j], mapping.get(String.valueOf(crosswordTemplate[i][j]))));
                    }
                }
            }
        }
        
        for (int i = 0; i < r; i++) {
        	
        	ArrayList<Var> word = new ArrayList<Var>();

            for(int j = 0; j < c; j++) {

            	if (crosswordTemplate[i][j] == '*') {
            		if (wordSizes.contains(word.size())) {
            			MDD mdd4word = mdds.get(word.size()).reuse(word.toArray(new IntVar[0]));
            			store.impose(new ExtensionalSupportMDD(mdd4word));
            		}
            		// System.out.println(word);
            		word.clear();
            	}
            	else
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

        for(int j = 0; j < c; j++) {

        	ArrayList<Var> word = new ArrayList<Var>();

            for(int i = 0; i < r; i++) {

            	if (crosswordTemplate[i][j] == '*') {
            		if (wordSizes.contains(word.size())) {
            			MDD mdd4word = mdds.get(word.size()).reuse(word.toArray(new IntVar[0]));
            			store.impose(new ExtensionalSupportMDD(mdd4word));
            			// System.out.println(word);
            		}
            		word.clear();
            	}
            	else
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

        for(int i = 0; i < r; i++) 
            for(int j = 0; j < c; j++)
                if (x[i][j] != null)
            	    vars.add(x[i][j]);
                    
    }


    /**
     * It prints a variable crosswordTemplate.
     * @param crossWordTemplate
     */
    public void printSolution(char[][] crossWordTemplate) {

    	System.out.println();
        for(int i = 0; i < r; i++) {
            for(int j = 0; j < c; j++) {
                if (crossWordTemplate[i][j] != '*')
                    System.out.print(mappingReverse.get(x[i][j].value() ) + " ");
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
     * @param file filename containing dictionary
     * @param wordSizes  
     */
    public void readDictionaryFromFile(String file, ArrayList<Integer> wordSizes) {

    	for (int wordSize : wordSizes) {

			int wordCount = 0;

    		IntVar[] list = new IntVar[wordSize];
    		for (int i = 0; i < wordSize; i++)
    			list[i] = blank;

			int[] tupleForGivenWord = new int[wordSize];
    		MDD resultForWordSize = new MDD(list);
    		
    		try {

    			BufferedReader inr = new BufferedReader(new FileReader(file));
    			String str;
 //   			int lineCount = 0;

    			
    			while ((str = inr.readLine()) != null && str.length() > 0) {
                
    				str = str.trim();
                
    				// ignore comments
    				// starting with either # or %
    				if(str.startsWith("#") || str.startsWith("%")) {
    					continue;
    				}

    				if (str.length() != wordSize)
    					continue;
    				
    				for (int i = 0; i < wordSize; i++) {
    					tupleForGivenWord[i] = mapping.get(str.substring(i, i+1));
    				}

    				wordCount++;
    				resultForWordSize.addTuple(tupleForGivenWord);
    				
 //   				lineCount++;

    			} // end while

    			inr.close();

    		}
    		catch (IOException e) {
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
		
		SelectChoicePoint<IntVar> select = new SimpleSelect<IntVar>(vars.toArray(new IntVar[1]),
				new SmallestDomain<IntVar>(), new IndomainMin<IntVar>());

		Search<IntVar> search = new DepthFirstSearch<IntVar>();
		search.setSolutionListener(new PrintListener<IntVar>(crosswordTemplate));
		
		search.getSolutionListener().searchAll(true);
		search.getSolutionListener().recordSolutions(false);
		search.setAssignSolution(true);
		
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
     *  It executes the program to create a model and solve
     *  crossword problem. 
     *  
     *  @todo Add additional parameter which allows to specify the crossword.
     *  
     *  @param args no arguments used.
     *
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

        char [][] crossWordTemplate;
        public PrintListener(char[][] crosswordTemplate) {
            this.crossWordTemplate = crosswordTemplate;
        }

        @Override
		public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

			boolean returnCode = super.executeAfterSolution(search, select);
			
			if (noSolutions % 10 == 0) {
				System.out.println("Solution # " + noSolutions);
				printSolution(crossWordTemplate);
			}
			
			return returnCode;
		}

		
	}
	
} // end class

