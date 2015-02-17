/**
 *  ExtensionalSupportSTR.java 
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
import java.util.regex.Pattern;

import javax.xml.transform.sax.TransformerHandler;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;
import org.jacop.util.IndexDomainView;
import org.xml.sax.SAXException;

/**
 * Extensional constraint assures that one of the tuples is enforced in the
 * relation.
 * 
 * This implementation uses technique developed/improved by Christophe Lecoutre.
 * Paper presented at CP2008. We would like to thank him for making his code 
 * available, which helped to create our own version of this algorithm.
 * 
 * @author Radoslaw Szymanek
 * @version 4.2
 */


public class ExtensionalSupportSTR extends Constraint {

	// FIXME, remove the need for this attribute.
	Store store;
	
	/**
	 * It stores variables within this extensional constraint, order does
	 * matter.
	 */

	public IntVar[] list;
	
	/**
	 * 
	 */
	public int[][] tuples;
	
	static int idNumber = 1;
	
	static final boolean debugAll = false;
	
	IndexDomainView [] views;
	
	/**
	 * Gives the position of the first tuple (in the current list) 
	 * or -1 if the current list is empty.
	 */
	public int first;

	/**
	 * Gives the position of the last tuple (in the current list) 
	 * or -1 if the current list is empty.
	 */
	
	public int last;
	
	/**
	 * Gives the position of the next tuple wrt the position given in index, or -1.
	 */
	
	public int[] nexts;

	/**
	 * Gives the first position of the eliminated tuple at a given level.
	 */
	
	public TimeStamp<Integer> headsOfEliminatedTuples;
	
	/**
	 * Gives the last position of the eliminated tuple at a given level.
	 */
		
	public TimeStamp<Integer> tailsOfEliminatedTuples;

	/**
	 * The number of variable-value pairs which need to have support.
	 */
	public int nbGlobalValuesToBeSupported;

	/**
	 * The number of variable-value pairs which need to have support per variable.
	 */
	public int[] nbValuesToBeSupported; // ID = variable position

	
	/**
	 * It stores the position of the first residue.
	 */
	public int firstResidue;

	/**
	 * It stores the position of the last residue.
	 */
	public int lastResidue;
		
	/**
	 * It specifies the number of variables for which validity check within a tuple must be performed.
	 */
	public int nbValidityVariables;

	/**
	 * The positions of the variables for which validity of any tuple must be checked. 
	 */
	public int[] validityVariablePositions; 
	

	/**
	 * It specifies the current number of variables for which it is required to check
	 * if their values from the domains are supported.
	 */
	public int nbSupportsVariables;

	/**
	 * The positions of the variables for which GAC must be checked. 
	 * It does not contain variables which were singletons in previous invocation
	 * of the consistency function.
	 */
	public int[] supportsVariablePositions; 
	
	// for each variable computes the domain as given by all tuples.
	IntervalDomain[] valuesInFocus;
	
	int [] domainSizeAfterConsistency;

	/**
	 * It specifies the mapping of the variable into its index.
	 */
	public HashMap<Var, Integer> varToIndex;

	/**
	 * 
	 */
	public int lastAssignedVariablePosition = -1;
	
	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"list", "reinsertBefore", "residuesBefore"};

	/**
	 * Partial constructor which stores variables involved in a constraint but
	 * does not get information about tuples yet. The tuples must set separately.
	 * 
	 * @param list the variables in the scope of the constraint.
	 * @param reinsertBefore it specifies if the tuples which were removed and are reinstatiated are inserted at the beginning.
	 * @param residuesBefore it specifies if the residue tuples are moved to the beginning. 
	 */

	public ExtensionalSupportSTR(IntVar[] list, 
								boolean reinsertBefore, 
								boolean residuesBefore) {


		this(list, new int [0][0], reinsertBefore, residuesBefore);
	
	}

	
	/**
	 * It constructs an extensional constraint.
	 * @param list the variables in the scope of the constraint.
	 * @param tuples the tuples which are supports.
	 * @param reinsertBefore it specifies if the tuples which were removed and are reinstatiated are inserted at the beginning.
	 * @param residuesBefore it specifies if the residue tuples are moved to the beginning. 
	 */
	public ExtensionalSupportSTR(IntVar[] list, 
								 int[][] tuples, 
								 boolean reinsertBefore,
								 boolean residuesBefore) {

		this.list = new IntVar[list.length];

		for (int i = 0; i < list.length; i++)
			this.list[i] = list[i];

		views = new IndexDomainView[list.length];
		
		this.tuples = tuples;

		numberId = idNumber++;
		
		this.reinsertBefore = reinsertBefore;
		this.residuesBefore = residuesBefore;
		
		this.queueIndex = 1;

	}
	
	
	/**
	 * It creates an extensional constraint.
	 * @param variables the variables in the scope of the constraint.
	 * @param tuples the support tuples.
	 */
	public ExtensionalSupportSTR(IntVar[] variables, int[][] tuples) {
		this(variables, tuples, true, true);
	}
	
	/**
	 * It specifies if the tuples previously removed are re-inserted at the beginning.
	 */
	public boolean reinsertBefore;

	/**
	 * It specifies if the residues are moved at the beginning of the list.
	 */
	public boolean residuesBefore;

	/**
	 * It specifies if there was no first consistency check yet.
	 */
	public boolean firstConsistencyCheck = true;
	
	int firstConsistencyLevel;

	/**
	 * It specifies if there was a backtrack and no yet consistency function execution after backtracking.
	 */
	public boolean backtrackOccured;

	/**
	 * It removes the tuple which is no longer valid.
	 * @param previous the tuple pointing at removed tuple.
	 * @param current the removed tuple.
	 */
	public void remove(int previous, int current) {
		
		if (previous == -1)
			first = nexts[current];
		else
			nexts[previous] = nexts[current];
		if (nexts[current] == -1)
			last = previous;
				
		if (store.level == headsOfEliminatedTuples.stamp()) {
			nexts[current] = headsOfEliminatedTuples.value();
		}
		else
			nexts[current] = -1;
		
		headsOfEliminatedTuples.update(current);
		
		
		if (tailsOfEliminatedTuples.stamp() < store.level ||
			tailsOfEliminatedTuples.value() == -1)
			tailsOfEliminatedTuples.update(current);
		
	}

	
	/**
	 * It moves the residue to the beginning of the list.
	 * @param previous the tuple pointing at tuple residue.
	 * @param current the residue tuple.
	 */
	public void storeResidue(int previous, int current) {
		if (previous == -1)
			first = nexts[current];
		else
			nexts[previous] = nexts[current];
		if (nexts[current] == -1)
			last = previous;
		nexts[current] = firstResidue;
		if (firstResidue == -1)
			lastResidue = current;
		firstResidue = current;
	}	

	@Override
	public ArrayList<Var> arguments() {
		ArrayList<Var> result = new ArrayList<Var>();
		for (Var var : list)
			result.add(var);
		
		return result;
	}

	@Override
	public void removeLevel(int level) {
		
		assert (level > firstConsistencyLevel) 
			: "Constraint has the level at which it has computed its initial state being removed.";
        
		//		It is called upon removing level

		backtrackOccured = true;
		lastAssignedVariablePosition = -1;
		
		// adds tuples which were removed at current level, which is being removed.

		if (headsOfEliminatedTuples.stamp() < store.level)
			return;
		
		if (reinsertBefore) {

			if (tailsOfEliminatedTuples.value() == -1)
				System.out.print("Error");
			
			nexts[tailsOfEliminatedTuples.value()] = first;
			if (first == -1)
				last = tailsOfEliminatedTuples.value();
			first = headsOfEliminatedTuples.value();
			
		} else {
			if (first != -1)
				nexts[last] = headsOfEliminatedTuples.value();
			else
				first = headsOfEliminatedTuples.value();
			last = tailsOfEliminatedTuples.value();
		}
	
	}

	@Override
	public void consistency(Store store) {
		
		if (firstConsistencyCheck) {
		
		

			// adjust (even simplify) all internal data structures
			// to current domains of variables.
			// filter which ignores all tuples which already are not supports.

			boolean[] stillSupport = new boolean[tuples.length];

			int noSupports = 0;

			int i = 0;

			valuesInFocus = new IntervalDomain[list.length];
			
			for (int j = 0; j < list.length; j++)
				valuesInFocus[j] = new IntervalDomain();
			
			for (int[] t : tuples) {

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

				if (stillSupport[i]) {

					noSupports++;
					
					int m = 0;
					for (int val : t) {
						valuesInFocus[m].unionAdapt(val, val);
						m++;
					}
					
				}

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
			
			for (int[] t : tuples) {

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

			tuples = temp4Shrinking;

			if (tuples.length == 0)
				throw Store.failException;

			first = 0;
			nexts = new int[tuples.length];
			for (int j = 0; j < nexts.length; j++)
				nexts[j] = j + 1;
			nexts[nexts.length - 1] = -1;
			last = nexts.length - 1;
			
			
	//		domainSizeAfterConsistency = new int[list.length];

			for (int j = 0; j < views.length; j++) {

				list[j].domain.in(store.level, list[j], valuesInFocus[j]);
				
				views[j] = new IndexDomainView(list[j], true);
			}
			
			//transforms tuples into the ones based on indexes.
			
			// By transforming, it is possible to check validity of the tuple
			// by checking if indexes specified by the tuple still belongs to the 
			// domain.
			
			for (int l = 0; l < tuples.length; l++) {

				int [] originalTuple = tuples[l];
				int [] transformedTuple = new int[originalTuple.length];
				
				for (int m = 0; m < transformedTuple.length; m++)
					transformedTuple[m] = views[m].indexOfValue(originalTuple[m]);
				
				tuples[l] = transformedTuple; 

			}
		
			firstConsistencyCheck = false;
			firstConsistencyLevel = store.level;
		}
		
		if (backtrackOccured) {
			
			for (int i = 0; i < list.length; i++)
				// If it zero it means that it has changed after backtracking so we 
				// need to check this variable. All other variables (not equal to zero)
			    // we do not need to check for validity just because of the backtracking.
				// QueueVariable performed after backtracking and before consistency call
				// registers all variables by setting their size to zero.
				if (domainSizeAfterConsistency[i] != 0)
					domainSizeAfterConsistency[i] = list[i].getSize();
		}
		
		// This part decides for which variables we need to check to guarantee tuples validity. 
		// The ones which have changed since the last execution of the consistency function.
		// Probably store the sizes of variables during last execution. If the size is the
		// same then variable domain has not changed (backtracking is an issue). Upon 
		// backtracking register all changedVariable events by setting the size to -1.
		
		// This part decides for which variables we need to check that all values are supported.
		// the ones who were not singleton during the last execution of the consistency function.
		
		nbValidityVariables = 0;
		nbSupportsVariables = 0;
		nbGlobalValuesToBeSupported = 0;
		
		for (int i = 0; i < list.length; i++) {
			if (list[i].getSize() != domainSizeAfterConsistency[i]) {
				validityVariablePositions[nbValidityVariables++] = i;
			}
			if (domainSizeAfterConsistency[i] != 1) {
				supportsVariablePositions[nbSupportsVariables++] = i;
				views[i].intializeSupportSweep();
				nbGlobalValuesToBeSupported += list[i].getSize();
				nbValuesToBeSupported[i] = list[i].getSize();
			}
				
		}
				
		int lastAssignedIndex = 0;
		if (lastAssignedVariablePosition != -1) 
			lastAssignedIndex = views[lastAssignedVariablePosition].indexOfValue(
					list[lastAssignedVariablePosition].value() );
		
		//int cnt=0;
		firstResidue = -1;
		int previous = -1;
		int current = first;
		while (current != -1) {

			int next = nexts[current];
			int[] checkedTuple = tuples[current];

			boolean valid = lastAssignedVariablePosition == -1 || checkedTuple[lastAssignedVariablePosition] == lastAssignedIndex;
			for (int i = 0; valid && i < nbValidityVariables; i++) {
				int position = validityVariablePositions[i];
				if (!views[position].contains(checkedTuple[position]))
					valid = false;
			}

			if (!valid)
				remove(previous, current);
			
			else {
				int nbbefore = nbGlobalValuesToBeSupported;
				for (int i = nbSupportsVariables - 1; i >= 0; i--) {
					int position = supportsVariablePositions[i];
					
					if (!views[position].setSupport(checkedTuple[position])) {
						nbGlobalValuesToBeSupported--;
						nbValuesToBeSupported[position]--;
						if (nbValuesToBeSupported[position] == 0)
							supportsVariablePositions[i] = supportsVariablePositions[--nbSupportsVariables];
					}
				}
				if (residuesBefore && nbbefore > nbGlobalValuesToBeSupported)
					storeResidue(previous, current);
				else
					previous = current;
			}
			current = next;
		}
				
		if (residuesBefore && firstResidue != -1) {
			nexts[lastResidue] = first;
			if (first == -1)
				last = lastResidue;
			first = firstResidue;
		}
		
		for (int i = 0; i < nbSupportsVariables; i++) {
			int position = supportsVariablePositions[i];		
			if ( nbValuesToBeSupported[position] == list[position].getSize() )
				throw Store.failException;
		}
		
		for (int i = 0; i < nbSupportsVariables; i++)			
			views[ supportsVariablePositions[i] ].removeUnSupportedValues(store);
				
		for (int i = 0; i < list.length; i++) 
			domainSizeAfterConsistency[i] = list[i].getSize();

		backtrackOccured = false;
		
	}

	@Override
	public int getConsistencyPruningEvent(Var var) {
//		 If consistency function mode
			if (consistencyPruningEvents != null) {
				Integer possibleEvent = consistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return IntDomain.ANY;
	}
	
	@Override
	public void impose(Store store) {
		
		this.store = store;
		
		store.registerRemoveLevelListener(this);

		varToIndex = new HashMap<Var, Integer>();
		
		for (int i = 0; i < list.length; i++) {
			list[i].putModelConstraint(this, getConsistencyPruningEvent(list[i]));
			varToIndex.put(list[i], i);
		}

		store.addChanged(this);
		store.countConstraint();

		if (debugAll) {
			for (Var var : list)
				System.out.println("Variable " + var);
		}
				
		headsOfEliminatedTuples = new TimeStamp<Integer>(store, -1 );
		
		tailsOfEliminatedTuples = new TimeStamp<Integer>(store, -1 );
		
		nbValuesToBeSupported = new int[list.length];		
		validityVariablePositions = new int[list.length];
		supportsVariablePositions = new int[list.length];
		
		domainSizeAfterConsistency = new int[list.length];

	}

	@Override
	public void increaseWeight() {
		
		for (Var var : list)
			var.weight++;
				
	}

	@Override
	public void queueVariable(int level, Var V) {
		
		if (backtrackOccured) {
			// Variables have changed after backtracking and before consistency function.
			domainSizeAfterConsistency[varToIndex.get(V)] = 0;
		}
		
		if (V.singleton())
			lastAssignedVariablePosition = varToIndex.get(V);
		
	}

	@Override
	public void removeConstraint() {
		
		for (Var var : list)
			var.removeConstraint(this);
		
	}

	@Override
	public boolean satisfied() {
		// FIXME.
		return false;
	}

	boolean smaller(int[] tuple1, int[] tuple2) {

		int arity = tuple1.length;
		for (int i = 0; i < arity && tuple1[i] <= tuple2[i]; i++)
			if (tuple1[i] < tuple2[i])
				return true;

		return false;

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

		tupleString.append(", ");

		if (tuples != null) {

			int[][] subset = tuples;

			for (int p1 = 0; p1 < subset.length; p1++)
				for (int p2 = subset.length - 1; p2 > p1; p2--)
					if (smaller(subset[p2], subset[p2 - 1])) {
						int[] temp = subset[p2];
						subset[p2] = subset[p2 - 1];
						subset[p2 - 1] = temp;
					}

			for (int p1 = 0; p1 < subset.length; p1++) {
				for (int p2 = 0; p2 < subset[p1].length; p2++) {
					tupleString.append( subset[p1][p2] );
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

		for (int[] tuple : tuples) {

			result.delete(0, result.length());

			for (int i : tuple)
				result.append( String.valueOf(i)).append(" ");
			result.append("|");

			tf.characters(result.toString().toCharArray(), 0, result.length());

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
	public static void fromXML(ExtensionalSupportSTR object, String content) {
		
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
		
		object.tuples = tuples.toArray(new int[tuples.size()][]);
				
	}
	
	
}
