/**
 *  SimpleSolutionListener.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *  Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.search;

import java.util.IdentityHashMap;
import java.util.Iterator;

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XeqC;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.SetVar;
import org.jacop.floats.core.FloatVar;

/**
 * It defines a simple solution listener which should be used if some basic
 * functionality of search when a solution is encountered are required.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 * @param <T> type of variable being used in search. 
 */

public class SimpleSolutionListener<T extends Var> implements SolutionListener<T> {

	/**
	 * It specifies if the debugging information should be printed.
	 */
	private static final boolean debug = false;

	/**
	 * It is executed right after consistency of the current search node. The
	 * return code specifies if the search should continue or exit.
	 */
	
	// TODO, change one solution only to limit of solutions.
	
	public T[] vars = null;

	boolean alwaysUpdateToMostRecentSolution = true;
	
	/**
	 * It specifies the number of solutions we want to find.
	 */
	public int solutionLimit = 1;

	protected int noSolutions = 0;

	boolean recordSolutions = false;

	public Domain[][] solutions;

	/**
	 * If this search is a slave search than each solution within this search
	 * must be connected to a solution of the master search. The parentSolutionListener
	 * is a solution listener of the master search.
	 */
	public SolutionListener<? extends Var> parentSolutionListener;

	/**
	 * If this search is a slave search than each solution within this search
	 * must be connected to a solution of the master search. This array stores
	 * for each solution recorded by this solution listener the solution number
	 * of the master slave.
	 */
	public int[] parentSolutionNo;

	/**
	 * It contains children of the solution listener.
	 */
	public SolutionListener<T>[] childrenSolutionListeners;
	
	/**
	 * It returns null if no solution was recorded, or the variables for which
	 * the solution(s) was recorded.
	 */

	public T[] getVariables() {
		return vars;
	}

	public boolean solutionLimitReached() {
		
		return solutionLimit == noSolutions;
	
	}
	
	public void setSolutionLimit(int limit) {
		
		solutionLimit = limit;
		
	}
	
	
	public void setParentSolutionListener(SolutionListener<? extends Var> parent) {

		parentSolutionListener = parent;

	}

	public Domain[][] getSolutions() {

		return solutions;
	}

	/**
	 * It returns the solution number no. The first solution has an index 1.
	 */

	public Domain[] getSolution(int no) {

		assert (no <= noSolutions);
		assert (recordSolutions);
		
		return solutions[no - 1];

	}

	/**
	 * It returns number of solutions found while using this choice point
	 * selector.
	 */

	public int solutionsNo() {
		return noSolutions;
	}

	/**
	 * It records all solutions so they can be later retrieved and
	 * used.
	 */

	public void recordSolutions(boolean status) {

		recordSolutions = status;

	}

    /**
	 * It searches for all solutions, but they do not have to be recorded as
	 * this is decided by another parameter.
	 */
	
	public void searchAll(boolean status) {
		
		if (status)
			solutionLimit = Integer.MAX_VALUE;
		else
			solutionLimit = 1;
		
	}

	/**
	 * It records a solution. It uses the current value of the search variables (they must be 
	 * all grounded) as well as the current number of the solution in master search (if there is one). 
	 */
	public void recordSolution() {

		if (recordSolutions) {

			if (noSolutions >= solutions.length) {

				Domain[][] oldSolutions = solutions;
				solutions = new Domain[noSolutions * 2][];
				System.arraycopy(oldSolutions, 0, solutions, 0, noSolutions);

				int[] oldParentSolutionNo = parentSolutionNo;
				parentSolutionNo = new int[noSolutions * 2];
				System.arraycopy(oldParentSolutionNo, 0, parentSolutionNo, 0,
						noSolutions);

			}

			Domain[] currentSolution = new Domain[vars.length];

			for (int i = 0; i < vars.length; i++) {
				if (!vars[i].singleton())
					throw new RuntimeException("Variable is not grounded in the solution");
				currentSolution[i] = vars[i].dom();
			}
			
			solutions[noSolutions] = currentSolution;

			//TODO connection between parent and child search depending if 
			// they are recording solutions.
			if (parentSolutionListener != null)
					parentSolutionNo[noSolutions] = parentSolutionListener
						.solutionsNo() - 1;

			noSolutions++;

		} else {

			for (int i = 0; i < vars.length; i++) {
			    if (!vars[i].singleton()) 
					throw new RuntimeException("Variable is not grounded in the solution");
				solutions[0][i] = vars[i].dom();
			}
			
			//TODO connection between parent and child search depending if 
			// they are recording solutions.
			if (parentSolutionListener != null)
					parentSolutionNo[0] = parentSolutionListener.solutionsNo();
			noSolutions++;

		}

	}

	public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

		if (vars == null) {

			IdentityHashMap<T, Integer> position = select.getVariablesMapping();

	//		vars = (T[]) new Var[position.size()];
			
			for (Iterator<T> itr = position.keySet().iterator(); itr
					.hasNext();) {
				T current = itr.next();
				if (vars == null) {
					if (current instanceof IntVar)
						vars = (T[]) new IntVar[position.size()];
					if (current instanceof SetVar)
						vars = (T[]) new SetVar[position.size()];	 
					if (current instanceof FloatVar)
						vars = (T[]) new FloatVar[position.size()];	 
				}
				vars[position.get(current)] = current;
			}

			solutions = new Domain[1][vars.length];
			parentSolutionNo = new int[1];

		}

		recordSolution();
				
		if (childrenSolutionListeners != null) {
			boolean code = false;
			for (int i = 0; i < childrenSolutionListeners.length; i++)
				code |= childrenSolutionListeners[i].executeAfterSolution(search, select);
			return code && (solutionLimit <= noSolutions);
		}
		
		return solutionLimit <= noSolutions;

	}

	/**
	 * It assigns the last found solution to the store. If the function returns false
	 * that means that for some reason the solution which was supposed to be a solution is not. 
	 * It can be caused by a number of issues, starting with wrongly implemented plugins, wrongly
	 * implemented consistency or satisfied function of the constraint. 
	 * 
	 * @param store the store in the context of which the search took place.
	 * @return true if the store is consistent after assigning a solution, false otherwise.
	 */
	public boolean assignSolution(Store store) {
		if (recordSolutions)
			return assignSolution(store, noSolutions - 1);
		else
			return assignSolution(store, 0);
	}

	public boolean assignSolution(Store store, int number) {

		if (number == noSolutions - 1 && !recordSolutions)
			number = 0;
		
		assert (number < noSolutions) : "Smaller number of solutions were found.";
		assert (recordSolutions || number == 0) : "The solutions were not stored.";
		assert (solutions.length > number) : "The solution of the given number was not stored.";
		
		if (vars != null) {

			assert ( store.currentConstraint == null);

			for (int i = 0; i < vars.length; i++) {
				vars[i].dom().in(store.level, vars[i], solutions[number][i]);
			}

			boolean result = store.consistency();

			return result;
		} else
			return false;
	}

	@Override
	public String toString() {

		StringBuffer buf = new StringBuffer();

		if (noSolutions > 1) {
			buf.append("\nNo of solutions : " + noSolutions);
			buf.append("\nLast Solution : [");
		} else
			buf.append("\nSolution : [");

		int solutionIndex = 0;
		
		if (recordSolutions)
			solutionIndex = noSolutions - 1;
		
		if (vars != null)
			for (int i = 0; i < vars.length; i++) {
				buf.append(vars[i].id()).append("=").append(
						solutions[solutionIndex][i]);
				if (i < vars.length - 1)
					buf.append(", ");
			}

		buf.append("]\n");

		return buf.toString();
	}

	public PrimitiveConstraint[] returnSolution() {

		return returnSolution(noSolutions - 1);

	}

	/**
	 * It returns the solution with the given number (value 0 denotes the first solution) as
	 * a set of primitive constraints.
	 * @param number the solution number (0 denotes the first solution).
	 * @return set of primitive constraint which if imposed will enforce given solution.
	 */
	public PrimitiveConstraint[] returnSolution(int number) {

		PrimitiveConstraint[] result;

		if (vars != null) {

			result = new PrimitiveConstraint[vars.length];

			int no = 0;

			for (int i = 0; i < vars.length; i++) {
				
				if (vars[i] instanceof IntVar)
					result[no] = new XeqC((IntVar)vars[i], ((IntDomain)solutions[i][number]).min() );
								
				no++;
			}

			return result;
		}

		return null;

	}

	public int findSolutionMatchingParent(int parentNo) {

		if (!isRecordingSolutions()) {
			
			if (parentSolutionNo[0] == parentNo)
				return 0;
			else
				return -1;
			
		}
		
		int left = 0;
		int right = noSolutions - 1;

		int middle = left;

		while (!(left + 1 >= right)) {

			if (debug)
				System.out.println("left " + left + " right " + right + " middle "
								   + middle);

			middle = (left + right) >> 1;

			if (parentSolutionNo[middle] < parentNo)
				left = middle;
			else if (parentSolutionNo[middle] > parentNo)
				right = middle;
			else
				break;

		}

		if (parentSolutionNo[middle] == parentNo)
			return middle;
		else if (parentSolutionNo[right] == parentNo)
			return right;
		else if (parentSolutionNo[left] == parentNo)
			return left;
		else
			return -1;

	}

	public void setChildrenListeners(SolutionListener<T>[] children) {

		childrenSolutionListeners = children;

	}

	public void setChildrenListeners(SolutionListener<T> child) {
		childrenSolutionListeners = new SolutionListener[1];
		childrenSolutionListeners[0] = child;
	}

	public boolean isRecordingSolutions() {
		return recordSolutions;
	}

	
    public void printAllSolutions() {

    	if (recordSolutions) {
    		System.out.println("\nAll solutions: \n");
    		System.out.println("Number of Solutions: " + noSolutions);
                for(int i = 0; i < solutions[0].length; i++) {
    				System.out.print(vars[i].id() + " ");
    			}
                System.out.println();
    		for(int s = 0; s < noSolutions; s++) {
    			for(int i = 0; i < solutions[0].length; i++) {
    				System.out.print(solutions[s][i] + " ");
    			}
    			System.out.println();
    		}
    	}
    	else {
    		
    		if (noSolutions > 0) {
    			System.out.println("\nLast recorded solution: \n");
    			System.out.println("Number of Solutions: " + noSolutions);
    		
                        for(int i = 0; i < solutions[0].length; i++) {
    				System.out.print(vars[i].id() + " ");
    			}
                        System.out.println();
    			for(int i = 0; i < solutions[0].length; i++) {
    				System.out.print(solutions[0][i] + " ");
    			}
    			System.out.println();
    		}
    		else {
    			System.out.println("\nNo solution found. \n");    			
    		}
    	}

    }

	public int getParentSolution(int childSolutionNo) {
		
		if (parentSolutionNo == null || parentSolutionNo.length < childSolutionNo)
			return -1;
		
		return parentSolutionNo[childSolutionNo - 1];
		
	}
	
}
