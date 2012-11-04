/**
 *  Sum.java 
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;
import org.jacop.jasat.utils.structures.IntVec;
import org.jacop.satwrapper.SatWrapper;

/**
 * Sum constraint implements the summation over several Variable's . It provides
 * the sum from all Variable's on the list.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 3.0
 */

public class Sum extends Constraint {

	static int counter = 1;

	/**
	 * It specifies the variables to be summed.
	 */
	public IntVar list[];

	/**
	 * It specifies variable sum to store the overall sum of the variables being summed up. 
	 */
	public IntVar sum;

	/**
	 * The sum of grounded variables.
	 */
	private TimeStamp<Integer> sumGrounded;
	
	/**
	 * The position for the next grounded variable.
	 */
	private TimeStamp<Integer> nextGroundedPosition;	

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"list", "sum"};

	/**
	 * It constructs sum constraint which sums all variables and makes it equal to variable sum.
	 * @param list
	 * @param sum
	 */
	public Sum(IntVar[] list, IntVar sum) {
		
		assert (list != null) : "List of variables is null";
		assert (sum != null) : "Sum variable is null";
		
		for (int i = 0; i < list.length; i++)
			assert (list[i] != null) : i + "-th element in list is null";
			
		queueIndex = 1;
		numberId = counter++;
		
		this.sum = sum;
		this.list = new IntVar[list.length];
		
		System.arraycopy(list, 0, this.list, 0, list.length);
		numberArgs += list.length;		
	}

	/**
	 * It creates a sum constraints which sums all variables and makes it equal to variable sum.
	 * @param list variables being summed up.
	 * @param sum the sum variable.
	 */

	public Sum(ArrayList<? extends IntVar> list, IntVar sum) {

		this(list.toArray(new IntVar[list.size()]), sum);
		
	}


	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(list.length + 1);

		variables.add(sum);

		for (Var v : list)
			variables.add(v);

		return variables;
	}

	@Override
	public void consistency(Store store) {
		

		do {

			store.propagationHasOccurred = false;
			
			int pointer = nextGroundedPosition.value();

			int lMin = sumGrounded.value();
			int lMax = lMin;
			
			int sumJustGrounded = 0;

			for (int i = pointer; i < list.length; i++) {
				IntDomain currentDomain = list[i].domain;
				
				if (currentDomain.singleton()) {
					
					if (pointer < i) {
						IntVar grounded = list[i];
						list[i] = list[pointer];
						list[pointer] = grounded;
					}
				
					pointer++;
					sumJustGrounded += currentDomain.min();
					continue;
				}
				
				lMin += currentDomain.min();
				lMax += currentDomain.max();
			}

			nextGroundedPosition.update(pointer);
			sumGrounded.update( sumGrounded.value() + sumJustGrounded );
			
			lMin += sumJustGrounded;
			lMax += sumJustGrounded;
			
			boolean needAdaptMin = false;
			boolean needAdaptMax = false;

			if (sum.min() > lMin)
				needAdaptMin = true;

			if (sum.max() < lMax)
				needAdaptMax = true;

			sum.domain.in(store.level, sum, lMin, lMax);

			store.propagationHasOccurred = false;
			
			int min = sum.min() - lMax;
			int max = sum.max() - lMin;

			if (needAdaptMin && !needAdaptMax)
				for (int i = pointer; i < list.length; i++) {
					IntVar v = list[i];
					v.domain.inMin(store.level, v, min + v.max());
				}

			if (!needAdaptMin && needAdaptMax)
				for (int i = pointer; i < list.length; i++) {
					IntVar v = list[i];
					v.domain.inMax(store.level, v, max + v.min());
				}

			if (needAdaptMin && needAdaptMax)
				for (int i = pointer; i < list.length; i++) {
					IntVar v = list[i];
					v.domain.in(store.level, v, min + v.max(), max + v.min());
				}

		} while (store.propagationHasOccurred);
		
	}


	@Override
	public int getConsistencyPruningEvent(Var var) {

		// If consistency function mode
			if (consistencyPruningEvents != null) {
				Integer possibleEvent = consistencyPruningEvents.get(var);
				if (possibleEvent != null)
					return possibleEvent;
			}
			return IntDomain.BOUND;
	}

	// registers the constraint in the constraint store
	@Override
	public void impose(Store store) {

		sumGrounded = new TimeStamp<Integer>(store, 0);
		nextGroundedPosition = new TimeStamp<Integer>(store, 0);
		
		sum.putModelConstraint(this, getConsistencyPruningEvent(sum));
		
		for (int i = 0; i < list.length; i++) {
			list[i].putModelConstraint(this, getConsistencyPruningEvent(list[i]));
		}
		
		store.addChanged(this);
		store.countConstraint();
	}
        
     /**
	 * impose the constraint to the Sat Wrapper
	 */
	@Override
	public void imposeToSat(SatWrapper wrapper) {
            
		assert list.length > 0 : "sum of 0 variables is nonsense";
		
		//String msg = "";
		//for (int i = 0; i < list.length; ++i)
		//	msg += list[i]+(i == list.length-1 ? "" : "+");
		//wrapper.log(this, "imposeToSat for "+msg+" = ("+sum+")");
		
		// register all variables
		wrapper.register(sum);
		for (IntVar v : list)
			wrapper.register(v);
		
		// create the arrays necessary to generate all combinations
		int[] lowers = new int[list.length];
		int[] uppers = new int[list.length];
		
		// initialize them
		for (int i = 0; i < list.length; ++i) {
			lowers[i] = list[i].domain.min();
			uppers[i] = list[i].domain.max();
		}
		
		// generate and test all combinations
		generateAndTest(wrapper, lowers, uppers);
	}

	/**
	 * generate and test all combinations of values of CP variables. The 
	 * combinations that fits are translated to clauses that are added to the
	 * Sat Wrapper
	 * @param wrapper	the wrapper to add clauses to
	 * @param lowers	the lower bounds
	 * @param uppers	the upper bounds
	 */
	private void
	generateAndTest(SatWrapper wrapper, int[] lowers, int[] uppers) {
		assert lowers.length == uppers.length;
		assert lowers.length == list.length;
		
		// initialize
		int n = list.length;
		int[] currents = new int[n];
		for (int i = 0; i < n; ++i)
			currents[i] = lowers[i];
		
		/*
		 *  generation of all combinations of values
		 */
		
		int i = 0; // current index to increment
		while (true) {
			
			/*
			 * generate a clause for this combination
			 */
			generateClause(wrapper, currents);
			
			// generate next combination (if any)
			if (currents[i] == uppers[i]) {
				// cannot increment any more this column !
				
				// find a column not "full"
				while (i < n && currents[i] == uppers[i]) {
					i++;
				}
				
				if (i == n) {
					// all combinations generated, stop
					//wrapper.log(this, "all clauses generated, exit");
					break;
				} else {
					// increment this column, and reset all lower columns
					currents[i]++;
					for (int j = 0; j < i; ++j)
						currents[j] = lowers[j];
					// go back to 0
					i=0;
				}
			} else {
				
				// increment this column, and go back to first column
				currents[i]++;
				i = 0;
			}
			
			
		}
	}

        /**
	 * should the generation of clauses be exhaustive (prevent bad combinations,
	 * implies result for good combinations) or just deal with combinations
	 * of values that remain in the domain of sum ?
	 * The first case (if exhaustive is true) will take a lot of memory
	 * but may speed up conflict detection.
	 * The second generates less clauses, but may not be as efficient to
	 * detect conflicts.
         * TODO : Check if still true.
	 * NOTE : it seems that setting it to false leads to false solutions, 
	 * because the constraint is not enforced. TODO : remove this flag, then?
	 */
	public static final boolean exhaustive = true;
        
	/**
	 * generate a clause for this combination of values in list
	 * @param wrapper	the wrapper
	 * @param currents	the values of IntVar of this.list
	 */
	private void generateClause(SatWrapper wrapper, int[] currents) {
		
                		// initialize clause
		IntVec clause = new IntVec(wrapper.pool);
                
		// sum of values
		int curSum = 0;
		for (int i = 0; i < list.length; ++i)
			curSum += currents[i];
		
		if (curSum > sum.domain.max() || curSum < sum.domain.min()) {
			// impossible combination !
			
			// only generate a clause if the constraint is exhaustive
			// the clause says that this combination of values if not possible
			// ie list[1] != v1 or list[2] != v2 or ...
			if (exhaustive) {
				clause.clear();
				
				//String msg = "add clause ";
				for (int i = 0; i < list.length; ++i) {
					// 'list[i] != v'
					int iValue = wrapper.cpVarToBoolVar(list[i], currents[i], true);
					clause.add(- iValue);
					//msg += "("+list[i]+"!="+currents[i]+") ";
				}
				
				wrapper.addModelClause(clause.toArray());
				//wrapper.log(this, msg+"; "+clause);
			}
			
		} else {
			// imply the value of sum, ie list[1] == v1 and list[2] == 2 ...
			// and list[n] == vn => sum == (v1+v2...+vn)
			clause.clear();
			
			//String msg = "add clause ";
			for (int i = 0; i < list.length; ++i) {
				// 'list[i] = v'
				int iValue = wrapper.cpVarToBoolVar(list[i], currents[i], true);
				clause.add(- iValue);
				//msg += "("+list[i]+"=="+currents[i]+") ";
			}
			int sumValue = wrapper.cpVarToBoolVar(sum, curSum, true);
			clause.add(sumValue);
			//msg += " ==> ("+sum+"="+curSum+"); ";
			
			wrapper.addModelClause(clause.toArray());
			//wrapper.log(this, msg+clause);
		}
	}

	@Override
	public void removeConstraint() {
		sum.removeConstraint(this);
		for (Var v : list)
			v.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {
		boolean sat = sum.singleton();
		
		int i = list.length - 1, sumAll = 0;
		
		while (sat && i >= 0) {
			sat = list[i].singleton();
			i--;
		}
		if (sat) {
			for (IntVar v : list)
				sumAll += v.min();
		}
		return (sat && sumAll == sum.min());
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer( id() );
		result.append(" : sum( [");

		for (int i = 0; i < list.length; i++) {
			result.append(list[i]);
			if (i < list.length - 1)
				result.append(", ");
		}
		result.append("], ").append(sum).append(" )");
		
		return result.toString();
	}
		
	@Override
	public Constraint getGuideConstraint() {
	
		IntVar proposedVariable = (IntVar)getGuideVariable();
		if (proposedVariable != null)
			return new XeqC(proposedVariable, guideValue);
		else
			return null;
	}

	@Override
	public int getGuideValue() {
		return guideValue; 
	}

	int guideValue = 0;
	
	
	@Override
	public Var getGuideVariable() {
		
		int regret = 1;
		Var proposedVariable = null;

		for (IntVar v : list) {

			IntDomain listDom = v.dom();

			if (v.singleton())
				continue;

			int currentRegret = listDom.nextValue(listDom.min()) - listDom.min();
			
			if (currentRegret > regret) {
				regret = currentRegret;
				proposedVariable = v;
				guideValue = listDom.min();
			}

			currentRegret = listDom.max() - listDom.previousValue(listDom.max());
			
			if (currentRegret > regret) {
				regret = currentRegret;
				proposedVariable = v;
				guideValue = listDom.max();
			}
			
		}

		return proposedVariable;
		
	}


	@Override
	public void supplyGuideFeedback(boolean feedback) {
	}

    @Override
	public void increaseWeight() {
		if (increaseWeight) {
			sum.weight++;
			for (Var v : list) v.weight++;
		}
	}
	
}
