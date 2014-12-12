/**
 *  ExtensionalSupportVA.java 
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

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.PriorityQueue;
import java.util.regex.Pattern;

import javax.xml.transform.sax.TransformerHandler;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.xml.sax.SAXException;

/**
 * Extensional constraint assures that one of the tuples is enforced in the
 * relation.
 * 
 * This implementation tries to balance the usage of memory versus time
 * efficiency.
 * 
 * @author Radoslaw Szymanek
 * @version 4.2
 */

public class ExtensionalSupportVA extends Constraint {

	// TODO raiseLevelBeforeConsistency may not be needed by this constraint. 
	
	/**
	 * It seeks support for a given variable-value pair.
	 * @param varPosition position of the variable for which the support is seek.
	 * @param value value for which the support is seek.
	 * @return support tuple.
	 */
	public int[] seekSupportVA(int varPosition, int value) {

		if (debugAll)
			System.out.println("Seeking support for " + list[varPosition]
					+ " and value " + value);

		int[] t = setFirstValid(varPosition, value);
		int invalidPosition = -1;
		while (true) {
			t = findFirstAllowed(varPosition, value, t);
			if (t == null)
				return null;
			invalidPosition = seekInvalidPosition(t);
			if (invalidPosition == -1)
				return t;
			// setNextValidPart
			// t = setNextValid(varPosition, value, t, invalidPosition);
			for (int i = invalidPosition + 1; i < list.length; i++)
				if (i != varPosition)
					t[i] = list[i].min();
			boolean cont = false;
			for (int i = invalidPosition; i >= 0; i--)
				if (i != varPosition)
					if (t[i] >= list[i].max())
						t[i] = list[i].min();
					else {
						t[i] = list[i].domain.nextValue(t[i]);
						cont = true;
						break;
					}
			if (!cont)
				return null;
		}

	}

	/**
	 * It computes the first valid tuple for a given variable-value pair.
	 * @param varPosition position of the variable.
	 * @param value value for which the fist valid tuple is seek.
	 * @return first valid tuple.
	 */
	public int[] setFirstValid(int varPosition, int value) {

		int t[] = new int[list.length];

		int noVars = list.length;
		for (int i = 0; i < noVars; i++)
			t[i] = list[i].min();

		t[varPosition] = value;

		return t;
	}

	/**
	 * It finds the first allowed tuple from the given tuple.
	 * @param varPosition position of the variable.
	 * @param value value for which first allowed tuple is seek.
	 * @param t tuple from which the search commences.
	 * @return first allowed tuple for a given variable-value pair.
	 */
	public int[] findFirstAllowed(int varPosition, int value, int[] t) {

		if (debugAll)
			System.out.println("variable" + list[varPosition] + " position "
					+ varPosition + " value " + value);
			
		int[][] tuplesForGivenVariableValuePair = tuples[varPosition][findPosition(
				value, values[varPosition])];

		int left = 0;
		int right = tuplesForGivenVariableValuePair.length - 1;

		if (!(smaller(t, tuplesForGivenVariableValuePair[right]) || equal(t,
				tuplesForGivenVariableValuePair[right]))) {
			return null;
		}

		int position = (left + right) >> 1;

		while (!(left + 1 >= right)) {

			if (smaller(t, tuplesForGivenVariableValuePair[position])) {
				right = position;
			} else {
				left = position;
			}

			position = (left + right) >> 1;

		}

		if (smaller(t, tuplesForGivenVariableValuePair[left])
				|| equal(t, tuplesForGivenVariableValuePair[left])) {
			System.arraycopy(tuplesForGivenVariableValuePair[left], 0, t, 0,
					list.length);
			return t;
		} else {
			System.arraycopy(tuplesForGivenVariableValuePair[right], 0, t, 0,
					list.length);
			return t;
		}
	}

    /**
     * It gives the position of the variable for which current domain of this
     * variable does not hold the used value. It is variable because of which 
     * allowed tuple does not become a support tuple. 
     * @param t tuple being checked.
     * @return -1 if tuple is both valid and allowed (support), otherwise the position.
     */
    public int seekInvalidPosition(int[] t) {

		int noVars = list.length;
		for (int i = 0; i < noVars; i++)
			if (!list[i].domain.contains(t[i]))
				return i;
		return -1;
	}

	static final boolean debugAll = false;

	static final boolean debugPruning = false;

	/**
	 * It specifies the id of the constraint.
	 */
	public static int idNumber = 1;

	boolean firstConsistencyCheck = true;

	int levelOfFirstConsistencyCheck;
	
	int numberTuples = 0;

	/**
	 * It represents tuples which are supports for each of the variables. The
	 * first index denotes variable index. The second index denotes value index.
	 * The third index denotes tuple.
	 */

	int[][][][] tuples;

	private int[][] tuplesFromConstructor;

	/**
	 * It represents values which are supported for a variable.
	 */
	int[][] values;

	LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<IntVar>();

	/**
	 * It stores variables within this extensional constraint, order does
	 * matter.
	 */

	public IntVar[] list;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"list"};

	/**
	 * Partial constructor which stores variables involved in a constraint but
	 * does not get information about tuples yet. The tuples must set separately.
	 * 
	 * @param list 
	 */

	public ExtensionalSupportVA(IntVar[] list) {

		this.list = new IntVar[list.length];
		
		for (int i = 0; i < list.length; i++)
			this.list[i] = list[i];

		this.numberId = idNumber++;
	}

	/**
	 * The constructor does not create local copy of tuples array. Any changes
	 * to this array will reflect on constraint behavior. Most probably
	 * incorrect as other data structures will not change accordingly.
	 * @param variables the constraint scope.
	 * @param tuples the tuples which are supports for the constraint.
	 */

	public ExtensionalSupportVA(ArrayList<? extends IntVar> variables,
			int[][] tuples) {

		this(variables.toArray(new IntVar[1]), tuples);

	}

	/**
	 * Constructor stores reference to tuples until imposition, any changes to
	 * tuples parameter will be reflected in the constraint behavior. Changes to
	 * tuples should not performed under any circumstances. The tuples array is
	 * not copied to save memory and time.
	 * @param variables the constraint scope.
	 * @param tuples the tuples which are supports for the constraint.
	 */

	public ExtensionalSupportVA(IntVar[] variables, int[][] tuples) {

		this.list = new IntVar[variables.length];

		for (int i = 0; i < variables.length; i++)
			list[i] = variables[i];

		tuplesFromConstructor = tuples;

		numberId = idNumber++;
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(list.length + 1);

		for (int i = 0; i < list.length; i++) {
			variables.add(list[i]);
		}

		return variables;
	}

	/**
	 * It puts back tuples which have lost their support status at the level
	 * which is being removed.
	 */

	@Override
	public void removeLevel(int level) {
		variableQueue = new LinkedHashSet<IntVar>();
		
		if (level == levelOfFirstConsistencyCheck) {
			firstConsistencyCheck = true;
		}

	}

	@Override
	public void consistency(Store store) {

		if (debugAll)
			System.out.println("Begin " + this);

		if (firstConsistencyCheck) {
			
			int i = 0;

			for (IntVar v : list) {

				if (values[i].length == 0)
			    	throw Store.failException;

				IntervalDomain update = new IntervalDomain(values[i][0],
						values[i][0]);
				for (int j = 1; j < values[i].length; j++)
					update.unionAdapt(values[i][j], values[i][j]);
				v.domain.in(store.level, v, update);

				i++;
			}
			
			firstConsistencyCheck = false;
			levelOfFirstConsistencyCheck = store.level;
			
		}

		boolean pruned = true;

		while (pruned) {

			pruned = false;
			// For each variable
			for (int varPosition = 0; varPosition < list.length; varPosition++) {
				// for each value

				for (ValueEnumeration enumer = list[varPosition].domain
						.valueEnumeration(); enumer.hasMoreElements();) {

					int value = enumer.nextElement();

					if (debugAll)
						System.out.println("Seeking support for "
								+ list[varPosition] + " and value " + value);
					int[] t = seekSupportVA(varPosition, value);

					if (debugAll)
						System.out.println("Found support?" + !(t == null));

					if (t == null) {
						list[varPosition].domain.inComplement(store.level,
								list[varPosition], value);
						pruned = true;
					}

				}
			}
		}

		if (debugAll)
			System.out.println("End " + this);
	}

	protected int findPosition(int value, int[] values) {

		int left = 0;
		int right = values.length - 1;

		int position = (left + right) >> 1;

		if (debugAll) {
			System.out.println("Looking for " + value);
			for (int v : values)
				System.out.print("val " + v);
			System.out.println("");
		}

		while (!(left + 1 >= right)) {

			if (debugAll)
				System.out.println("left " + left + " right " + right
						+ " position " + position);

			if (values[position] > value) {
				right = position;
			} else {
				left = position;
			}

			position = (left + right) >> 1;

		}

		if (values[left] == value)
			return left;

		if (values[right] == value)
			return right;

		return -1;

	}

	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
			if (consistencyPruningEvents != null) {
				Integer possibleEvent = consistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return IntDomain.ANY;
	}

	@Override
	public void impose(Store store) {

		store.registerRemoveLevelListener(this);

		for (int i = 0; i < list.length; i++) {
			list[i].putModelConstraint(this, getConsistencyPruningEvent(list[i]));
		}

		store.addChanged(this);
		store.countConstraint();

		if (debugAll) {
			for (Var var : list)
				System.out.println("Variable " + var);
		}

		// TO DO, adjust (even simplify) all internal data structures
		// to current domains of variables.
		// filter which ignores all tuples which already are not supports.

		boolean[] stillSupport = new boolean[tuplesFromConstructor.length];

		int noSupports = 0;

		int[][] supportCount = new int[list.length][];

		int i = 0;

		for (int[] t : tuplesFromConstructor) {

			stillSupport[i] = true;

			int j = 0;

			if (debugAll) {
				System.out.print("support for analysis[");
				for (int val : t)
					System.out.print(val + " ");
				System.out.println("]");
			}

			for (int val : t) {

				if (!list[j].dom().contains(val)) {
					stillSupport[i] = false;
					break;
				}

				j++;
			}

			if (stillSupport[i])
				noSupports++;

			if (debugAll) {
				if (!stillSupport[i]) {
					System.out.print("Not support [");
					for (int val : t)
						System.out.print(val + " ");
					System.out.println("]");
				}
			}

			i++;

		}

		if (debugAll) {
			System.out.println("No. still supports " + noSupports);
		}

		int[][] temp4Shrinking = new int[noSupports][];

		i = 0;
		int k = 0;

		for (int[] t : tuplesFromConstructor) {

			if (stillSupport[k]) {
				temp4Shrinking[i] = t;
				i++;

				if (debugAll) {
					System.out.print("Still support [");
					for (int val : t)
						System.out.print(val + " ");
					System.out.println("]");
				}

			}

			k++;

		}

		// Only still supports are kept.

		tuplesFromConstructor = temp4Shrinking;

		numberTuples = tuplesFromConstructor.length;

		// TO DO, just store parameters for later use in impose
		// function, move all code below to impose function.

		this.tuples = new int[list.length][][][];
		this.values = new int[list.length][];

		for (i = 0; i < list.length; i++) {

			HashMap<Integer, Integer> val = new HashMap<Integer, Integer>();

			for (int[] t : tuplesFromConstructor) {

				Integer value = t[i];
				Integer key = val.get(value);

				if (key == null)
					val.put(value, 1 );
				else
					val.put(value, key + 1);
			}

			if (debugAll)
				System.out.println("values " + val.keySet());

			PriorityQueue<Integer> sortedVal = new PriorityQueue<Integer>(val
					.keySet());

			if (debugAll)
				System.out.println("Sorted val size " + sortedVal.size());

			values[i] = new int[sortedVal.size()];
			supportCount[i] = new int[sortedVal.size()];
			this.tuples[i] = new int[sortedVal.size()][][];

			if (debugAll)
				System.out.println("values length " + values[i].length);

			for (int j = 0; j < values[i].length; j++) {

				if (debugAll)
					System.out.println("sortedVal " + sortedVal);

				values[i][j] = sortedVal.poll();
				supportCount[i][j] = val.get( values[i][j] );
				this.tuples[i][j] = new int[supportCount[i][j]][];
			}

//			int m = 0;
			for (int[] t : tuplesFromConstructor) {

				int value = t[i];
				int position = findPosition(value, values[i]);

				this.tuples[i][position][--supportCount[i][position]] = t;
//				m++;

			}

			// TODO, check sorting functionality.
			for (int j = 0; j < tuples[i].length; j++)
				store.sortTuplesWithin(tuples[i][j]);

		}

		tuplesFromConstructor = null;

		firstConsistencyCheck = true;

		store.raiseLevelBeforeConsistency = true;

	}

	@Override
	public void queueVariable(int level, Var var) {

		if (debugAll)
			System.out.println("Var " + var + ((IntVar)var).recentDomainPruning());

		variableQueue.add((IntVar)var);
	}

	@Override
	public void removeConstraint() {

		for (int i = 0; i < list.length; i++)
			list[i].removeConstraint(this);

	}

	@Override
	public boolean satisfied() {

		int i = 0;
		while (i < list.length) {
			if (!list[i].singleton())
				return false;
			i++;
		}

		return true;

	}

	boolean smaller(int[] tuple1, int[] tuple2) {

		int arity = tuple1.length;
		for (int i = 0; i < arity && tuple1[i] <= tuple2[i]; i++)
			if (tuple1[i] < tuple2[i])
				return true;

		return false;

	}

	boolean equal(int[] tuple1, int[] tuple2) {

		int arity = tuple1.length;
		for (int i = 0; i < arity; i++)
			if (tuple1[i] != tuple2[i])
				return false;

		return true;

	}

	@Override
	public String toString() {

		StringBuffer tupleString = new StringBuffer();

		tupleString.append(id());
		tupleString.append("(");

		for (int i = 0; i < list.length; i++) {
			tupleString.append(list[i].toString());
			if (i + 1 < list.length)
				tupleString.append(" ");
		}

		tupleString.append(")");

		if (tuplesFromConstructor != null) {

			int[][] subset = tuplesFromConstructor;

			for (int p1 = 0; p1 < subset.length; p1++)
				for (int p2 = subset.length - 1; p2 > p1; p2--)
					if (smaller(subset[p2], subset[p2 - 1])) {
						int[] temp = subset[p2];
						subset[p2] = subset[p2 - 1];
						subset[p2 - 1] = temp;
					}

			for (int p1 = 0; p1 < subset.length; p1++) {
				for (int p2 = 0; p2 < subset[p1].length; p2++) {
					tupleString.append( subset[p1][p2]);
					if (p2 != subset[p1].length - 1)
						tupleString.append(" ");
				}

				if (p1 != subset.length - 1)
					tupleString.append("|");
			}

			tupleString.append(")");
			return tupleString.toString();

		}

		return tupleString.toString();

	}


	
	
	/**
	 * It writes the content of this object as the content of XML 
	 * element so later it can be used to restore the object from 
	 * XML. It is done after restoration of the part of the object
	 * specified in xmlAttributes. 
	 *  
	 * @param tf a place to write the content of the object. 
	 * @throws SAXException
	 */
	public void toXML(TransformerHandler tf) throws SAXException {
		
		StringBuffer result = new StringBuffer("");

		for (int[][] tuplesForGivenValue : tuples[0]) {
			for (int[] tuple : tuplesForGivenValue) {
				
				result.delete(0, result.length());
				
				for (int i : tuple)
					result.append( String.valueOf(i)).append(" ");
				result.append("|");
				
				tf.characters(result.toString().toCharArray(), 0, result.length());
				
			}
		}
				
	}
	
	
	/**
	 * 
	 * It updates the specified constraint with the information 
	 * stored in the string. 
	 * 
	 * @param object the constraint to be updated.
	 * @param content the information used for update. 
	 */
	public static void fromXML(ExtensionalSupportVA object, String content) {
		
		Pattern pat = Pattern.compile("|");
		String[] result = pat.split( content );

		ArrayList<int[]> tuples = new ArrayList<int[]>(result.length);
		
		for (String element : result) {
			
			Pattern dotSplit = Pattern.compile(" ");
			String[] oneElement = dotSplit.split( element );

			int [] tuple = new int[object.list.length];
			
			int i = 0;
			for (String number : oneElement) {
				try {
					int value = Integer.valueOf(number);
					tuple[i++] = value;
				}
				catch(NumberFormatException ex) {
				};
			}
			
			tuples.add(tuple);
		}
		
		object.tuplesFromConstructor = tuples.toArray(new int[tuples.size()][]);
				
	}
	
	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			for (Var v : list) v.weight++;
		}
	}
	
}
