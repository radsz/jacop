/**
 *  Filter.java 
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

package org.jacop.examples.fd.filters;

import java.util.ArrayList;

/**
 * It provides the basic functionality which must be implemented by any 
 * filter problem. 
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 *
 */
public abstract class Filter {

	/**
	 * It denotes the delay of the addition.
	 */
	public int addDel = 1;
	
	/**
	 * It denotes the delay of the multiplication.
	 */
	public int mulDel = 2;

	/**
	 * It denotes the identifier of the addition.
	 */
	public final static int addId = 1;

	
	/**
	 * It specifies the identifier of the multiplication.
	 */
	public final static int mulId = 2;

	
	/**
	 * It specifies the name of the filter.
	 */
	public String name;
	
	/**
	 * It specifies the dependencies between the operation. Each dependency
	 * is denoted by two element array. The first element of the array denotes 
	 * the operation which must be executed before the operation denoted by 
	 * the second element of the array.
	 */
	public int dependencies[][];
	
	/**
	 * It specifies the type of each operation of a given position.
	 */
	public int ids[];
		
	/**
	 * It denotes the indexes of the operations on which no other operation
	 * depends on. The makespan of the schedule executing given filter depends 
	 * on the maximal execution time of one of this operations.
	 */
	public int last[];
	
	
	/**
	 * It returns the dependencies between operations which need to be satisfy in the 
	 * final solution.
	 * @return list of dependencies.
	 */
	public int[][] dependencies() {
		return dependencies;
	}

	/**
	 * It returns the ids of each operation.
	 * @return an array of ids.
	 */
	public int[] ids() {
		return ids;
	}

	/**
	 * It returns the array with the delays of all operations.
	 * The length of the returned array is equal to the number
	 * of operations in the particular filter problem.
	 * 
	 * @return an array with the delays of the operations.
	 */
	public int[] delays() {

		int[] delays = new int[ids.length];

		for (int i = 0; i < delays.length; i++) {
			if (ids[i] == addId)
				delays[i] = addDel;
			if (ids[i] == mulId)
				delays[i] = mulDel;
		}

		return delays;
	}

	/**
	 * It returns the number of operations in the filter. It 
	 * is not the number of different operations.
	 * @return number of operations present in the filter.
	 */
	public int noOp() {
		return ids.length;
	}

	/**
	 * It returns a string id of the problem.
	 * @return id of the filter problem being modeled and solved.
	 */
	public String name() {
		return name;
	}

	/**
	 * It returns a number of addition operations in the current
	 * problem.
	 * @return number of addition operations.
	 */
	public int noAdd() {
		int plusOp = 0;
		for (int i = 0; i < ids.length; i++)
			if (ids[i] == addId)
				plusOp++;
		return plusOp;
	}

	/**
	 * It returns a number of multiplications operations in the current
	 * problem.
	 * @return number of multiplications operations.
	 */
	public int noMul() {
		int mulOp = 0;
		for (int i = 0; i < ids.length; i++)
			if (ids[i] == mulId)
				mulOp++;
		return mulOp;
	}

	/**
	 * It returns the delay of the addition operation.
	 * @return the delay of the addition operation.
	 */
	public int addDel() {
		return addDel;
	}

	/**
	 * It returns the delay of the multiplication operation.
	 * @return the delay of the multiplication operation.
	 */
	public int mulDel() {
		return mulDel;
	}

	/**
	 * It returns the id of the addition operation.
	 * @return the id of the addition operation.
	 */
	public int addId() {
		return addId;
	}

	/**
	 * It returns the id of the multiplication operation.
	 * @return the id of the multiplication operation.
	 */
	public int mulId() {
		return mulId;
	}

	/** 
	 * It returns the list of operations which are not
	 * preceding any other operation.
	 * @return it returns the indexes of the operations which are used to
	 * compute the makespan of the schedule.
	 */
	public int[] lastOp() {
		return last;
	}

	/**
	 * It specifies the names of the operations for the 
	 * representation of the solution in textual form.
	 * @return list of names.
	 */
	public abstract ArrayList<String> names();

	/**
	 * It specifies the names of the operations for the 
	 * textual representation of the pipelined solution. 
	 * 
	 * @return list of names.
	 */
	public abstract ArrayList<String> namesPipeline();
}
