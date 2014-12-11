/**
 *  SumWeight.java 
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;

/**
 * SumWeight constraint implements the weighted summation over several
 * variables . It provides the weighted sum from all variables on the list.
 * The weights are integers.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 3.1
 */

public class SumWeight extends Constraint {

	static int counter = 1;

	/**
	 * It specifies a list of variables being summed.
	 */
	public IntVar list[];

	/**
	 * It specifies a list of weights associated with the variables being summed.
	 */
	public int weights[];

	/**
	 * It specifies variable for the overall sum. 
	 */
	public IntVar sum;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"list", "weights", "sum"};

	/**
	 * @param list
	 * @param weights
	 * @param sum
	 */
	public SumWeight(IntVar[] list, int[] weights, IntVar sum) {

		commonInitialization(list, weights, sum);
		
	}
	
	private void commonInitialization(IntVar[] list, int[] weights, IntVar sum) {
		
		queueIndex = 1;

		assert ( list.length == weights.length ) : "\nLength of two vectors different in SumWeight";

		numberArgs = (short) (list.length + 1);

		numberId = counter++;

		this.sum = sum;

		HashMap<IntVar, Integer> parameters = new HashMap<IntVar, Integer>();

		for (int i = 0; i < list.length; i++) {

			assert (list[i] != null) : i + "-th element of list in SumWeighted constraint is null";
			
			if (parameters.get(list[i]) != null) {
				// variable ordered in the scope of the Sum Weight constraint.
				Integer coeff = parameters.get(list[i]);
				Integer sumOfCoeff = coeff + weights[i];
				parameters.put(list[i], sumOfCoeff);
			}
			else
				parameters.put(list[i], weights[i]);

		}

		assert ( parameters.get(sum) == null) : "Sum variable is used in both sides of SumeWeight constraint.";

		this.list = new IntVar[parameters.size()];
		this.weights = new int[parameters.size()];

		int i = 0;
		for (IntVar var : parameters.keySet()) {
			this.list[i] = var;
			this.weights[i] = parameters.get(var);
			i++;
		}

		checkForOverflow();

	}

	/**
	 * It constructs the constraint SumWeight. 
	 * @param variables variables which are being multiplied by weights.
	 * @param weights weight for each variable.
	 * @param sum variable containing the sum of weighted variables.
	 */
	public SumWeight(ArrayList<? extends IntVar> variables,
			ArrayList<Integer> weights, IntVar sum) {

		int[] w = new int[weights.size()];
		for (int i = 0; i < weights.size(); i++)
			w[i] = weights.get(i);
		
		commonInitialization(variables.toArray(new IntVar[variables.size()]),
							 w,
							 sum);

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
	public void removeLevelLate(int level) {

		backtrackHasOccured = true;

	}


	/**
	 * The sum of grounded variables.
	 */
	private TimeStamp<Integer> sumGrounded;

	/**
	 * The position for the next grounded variable.
	 */
	private TimeStamp<Integer> nextGroundedPosition;	

	@Override
	public void consistency(Store store) {

		if (backtrackHasOccured) {

			backtrackHasOccured = false;

			int pointer = nextGroundedPosition.value();

			lMin = sumGrounded.value();
			lMax = lMin;

			for (int i = pointer; i < list.length; i++) {

				IntDomain currentDomain = list[i].domain;

				assert (!currentDomain.singleton()) : "Singletons should not occur in this part of the array";

				int mul1 = currentDomain.min() * weights[i];
				int mul2 = currentDomain.max() * weights[i];
				// int mul1 = IntDomain.multiply(currentDomain.min(), weights[i]);
				// int mul2 = IntDomain.multiply(currentDomain.max(), weights[i]);
				
				if (mul1 <= mul2) {
				    lMin += mul1;
				    // lMin = add(lMin, mul1);
				    lMinArray[i] = mul1;
				    lMax += mul2;
				    // lMax = add(lMax, mul2);
				    lMaxArray[i] = mul2;
				}
				else {

				    lMin += mul2;
				    // lMin = add(lMin, mul2);
				    lMinArray[i] = mul2;
				    lMax += mul1;
				    // lMax = add(lMax, mul1);
				    lMaxArray[i] = mul1;

				}

			}

		}

		do {
			
			sum.domain.in(store.level, sum, lMin, lMax);

			store.propagationHasOccurred = false;

			int min = sum.min() - lMax;
			int max = sum.max() - lMin;
			// int min = subtract(sum.min(), lMax);
			// int max = subtract(sum.max(), lMin);

			int pointer1 = nextGroundedPosition.value();

			for (int i = pointer1; i < list.length; i++) {

				if (weights[i] == 0)
					continue;

				IntVar v = list[i];

				float d1 = ((float)(min + lMaxArray[i]) / weights[i]);
				float d2 = ((float)(max + lMinArray[i]) / weights[i]);

				int divMin, divMax;
				if (d1 <= d2) {
					divMin = toInt( Math.round( Math.ceil ( d1 ) ) );
					divMax = toInt( Math.round( Math.floor( d2 ) ) );
				}
				else {
					divMin = toInt( Math.round( Math.ceil ( d2 ) ) );
					divMax = toInt( Math.round( Math.floor( d1 ) ) );
				}

				if (divMin > divMax) 
			    	throw Store.failException;

				v.domain.in(store.level, v, divMin, divMax);

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

	@Override
	public void impose(Store store) {

		sumGrounded = new TimeStamp<Integer>(store, 0);
		nextGroundedPosition = new TimeStamp<Integer>(store, 0);
		positionMaping = new HashMap<Var, Integer>();

		store.registerRemoveLevelLateListener(this);

		sum.putModelConstraint(this, getConsistencyPruningEvent(sum));
		for (Var V : list)
			V.putModelConstraint(this, getConsistencyPruningEvent(V));

		lMinArray = new int[list.length];
		lMaxArray = new int[list.length];
		lMin = 0;
		lMax = 0;

		for (int i = 0; i < list.length; i++) {

			assert (positionMaping.get(list[i]) == null) : "The variable occurs twice in the list, not able to make a maping from the variable to its list index.";

			positionMaping.put(list[i], new Integer(i));
			queueVariable(store.level, list[i]);
		}

		store.addChanged(this);
		store.countConstraint();
	}

	int lMin;

	int lMax;

	int[] lMinArray;

	int[] lMaxArray;

	HashMap<Var, Integer> positionMaping;

	boolean backtrackHasOccured = false;

	@Override
	public void queueVariable(int level, Var var) {

		if (var == sum)
			return;

		if (var.singleton()) {

			int pointer = nextGroundedPosition.value();

			int i = positionMaping.get(var);

			if (i < pointer)
				return;

			int value = ((IntVar)var).min();

			int sumJustGrounded = 0;

			int weightGrounded = weights[i];

			if (pointer < i) {
				IntVar grounded = list[i];
				list[i] = list[pointer];
				list[pointer] = grounded;

				positionMaping.put(list[i], i);
				positionMaping.put(list[pointer], pointer);

				int temp = lMinArray[i];
				lMinArray[i] = lMinArray[pointer];
				lMinArray[pointer] = temp;

				temp = lMaxArray[i];
				lMaxArray[i] = lMaxArray[pointer];
				lMaxArray[pointer] = temp;

				weights[i] = weights[pointer];
				weights[pointer] = weightGrounded;

			}

			sumJustGrounded += value * weightGrounded; // add(sumJustGrounded, IntDomain.multiply(value, weightGrounded));

			sumGrounded.update( sumGrounded.value() + sumJustGrounded );

			lMin += sumJustGrounded - lMinArray[pointer]; //add(lMin, sumJustGrounded - lMinArray[pointer]);
			lMax += sumJustGrounded - lMaxArray[pointer];
			lMinArray[pointer] = sumJustGrounded;
			lMaxArray[pointer] = sumJustGrounded;

			pointer++;
			nextGroundedPosition.update(pointer);

		}

		else {

			int i = positionMaping.get(var);

			int mul1 = ((IntVar)var).min() * weights[i];
			int mul2 = ((IntVar)var).max() * weights[i];
			// int mul1 = IntDomain.multiply(((IntVar)var).min(), weights[i]);
			// int mul2 = IntDomain.multiply(((IntVar)var).max(), weights[i]);

			if (mul1 <= mul2) {

			    lMin += mul1 - lMinArray[i]; //add(lMin, mul1 - lMinArray[i]);
			    lMinArray[i] = mul1;

			    lMax += mul2 - lMaxArray[i]; //add(lMax, mul2 - lMaxArray[i]);
			    lMaxArray[i] = mul2;

			}
			else {

			    lMin += mul2 - lMinArray[i]; //add(lMin, mul2 - lMinArray[i]);
			    lMinArray[i] = mul2;

			    lMax += mul1 - lMaxArray[i]; //add(lMax, mul1 - lMaxArray[i]);
			    lMaxArray[i] = mul1;

			}


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

		if (!sum.singleton())
			return false;

		if (nextGroundedPosition.value() != list.length)
			return false;

		if (sumGrounded.value() != sum.value())
			return false;

		return true;

	}

    void checkForOverflow() {

	int s1 = IntDomain.multiply(sum.min(), -1);
	int s2 = IntDomain.multiply(sum.max(), -1);

	int sumMin=0, sumMax=0;
	if (s1 <= s2) {
	    sumMin = add(sumMin, s1);
	    sumMax = add(sumMax, s2);
	}
	else {
	    sumMin = add(sumMin, s2);
	    sumMax = add(sumMax, s1);
	}

	for (int i=0; i<list.length; i++) {
	    int n1 = IntDomain.multiply(list[i].min(), weights[i]);
	    int n2 = IntDomain.multiply(list[i].max(), weights[i]);

	    if (n1 <= n2) {
		sumMin = add(sumMin, n1);
		sumMax = add(sumMax, n2);
	    }
	    else {
		sumMin = add(sumMin, n2);
		sumMax = add(sumMax, n1);
	    }
	}
    }

	@Override
	public String toString() {

		StringBuffer result = new StringBuffer( id() );
		result.append(" : sumWeight( [ ");

		for (int i = 0; i < list.length; i++) {
			result.append(list[i]);
			if (i < list.length - 1)
				result.append(", ");
		}
		result.append("], [");

		for (int i = 0; i < weights.length; i++) {
			result.append( weights[i] );
			if (i < weights.length - 1)
				result.append( ", " );
		}

		result.append( "], ").append(sum).append( " )" );

		return result.toString();

	}

	@Override
	public void increaseWeight() {
		if (increaseWeight) {
			sum.weight++;
			for (Var v : list) v.weight++;
		}
	}

}
