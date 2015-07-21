/**
 *  Max.java 
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
import org.jacop.core.Var;
import org.jacop.core.TimeStamp;

/**
 * Max constraint implements the Maximum/2 constraint. It provides the maximum
 * variable from all variables on the list. 
 * 
 * max(list) = max.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.3
 */

public class Max extends Constraint {

	static int counter = 1;

	/**
	 * It specifies a list of variables among which a maximum value is being searched for.
	 */
	public IntVar list[];

	/**
	 * It specifies variable max which stores the maximum value present in the list. 
	 */
	public IntVar max;

	/**
	 * It specifies length of the list. 
	 */
        int l;

        /**
	 * Defines first position of the variable that needs to be considered
	 */
        private TimeStamp<Integer> position;

        /**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"list", "max"};
	
	/**
	 * It constructs max constraint.
	 * @param max variable denoting the maximum value
	 * @param list the array of variables for which the maximum value is imposed.
	 */
	public Max(IntVar[] list, IntVar max) {

		assert ( list != null ) : "List variable is null";
		assert ( max != null ) : "Min variable is null";

		this.numberId = counter++;
		this.l = list.length;
		this.numberArgs = (short) (l + 1);
		this.max = max;
		this.list = new IntVar[l];

		for (int i = 0; i < l; i++) {
			assert (list[i] != null) : i + "-th variable in the list is null";
			this.list[i] = list[i];
		}

		if (list.length > 1000)  // rule of thumb
		    this.queueIndex = 2;
		else
		    this.queueIndex = 1;

	}

	/**
	 * It constructs max constraint.
	 * @param max variable denoting the maximum value
	 * @param variables the array of variables for which the maximum value is imposed.
	 */
	public Max(ArrayList<? extends IntVar> variables, IntVar max) {

		this(variables.toArray(new IntVar[variables.size()]), max);
		
	}


	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(list.length + 1);

		variables.add(max);
		for (int i = 0; i < list.length; i++)
			variables.add(list[i]);
		return variables;
	}

	@Override
	public void consistency(Store store) {
		
	        int start = position.value();
		IntVar var;
		IntDomain vDom;

		do {

			store.propagationHasOccurred = false;
			
			int minValue = IntDomain.MinInt;
			int maxValue = IntDomain.MinInt;
		
			int maxMax = max.max();
			int minMax = max.min();
			for (int i = start; i < l; i++) {
				
				var = list[i];

				vDom = var.dom();
				int varMin = vDom.min(), varMax = vDom.max();

				if(varMax < minMax) {
				    swap(start, i);
				    start++;
				}
				else if (varMax > maxMax)
					var.domain.inMax(store.level, var, maxMax);

				minValue = (minValue > varMin) ? minValue : varMin;
				maxValue = (maxValue > varMax) ? maxValue : varMax;
			}

			position.update(start);

			max.domain.in(store.level, max, minValue, maxValue);

			if (start == l) // all variables have their max value lower than min value of max variable
			    throw store.failException;
			if (start == list.length-1) { // one variable on the list is maximal; its is min > max of all other variables 
			    list[start].domain.in(store.level, list[start], max.dom());

			    if (max.singleton())
				removeConstraint();

			}
		} while (store.propagationHasOccurred);
		
	}

    private void swap(int i, int j) {
	if ( i != j) {
	    IntVar tmp = list[i];
	    list[i] = list[j];
	    list[j] = tmp;
	}
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

	        position = new TimeStamp<Integer>(store, 0);

		max.putModelConstraint(this, getConsistencyPruningEvent(max));

		for (Var V : list)
			V.putModelConstraint(this, getConsistencyPruningEvent(V));

		store.addChanged(this);
		store.countConstraint();

	}

	@Override
	public void removeConstraint() {
		max.removeConstraint(this);
		for (int i = 0; i < list.length; i++) {
			list[i].removeConstraint(this);
		}
	}

	@Override
	public boolean satisfied() {

		boolean sat = max.singleton();
		int MAX = max.min();
		int i = 0, eq = 0;
		while (sat && i < list.length) {
			if (list[i].singleton() && list[i].value() == MAX)
				eq++;
			sat = list[i].max() <= MAX;
			i++;
		}
		return sat && eq > 0;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer( id() );
		
		result.append(" : max(  [ ");
		for (int i = 0; i < list.length; i++) {
			result.append( list[i] );
			if (i < list.length - 1)
				result.append(", ");
		}
		
		result.append("], ").append(this.max);
		result.append(")");

		return result.toString();
	}

    @Override
	public void increaseWeight() {
		if (increaseWeight) {
			max.weight++;
			for (Var v : list) v.weight++;
		}
	}
}
