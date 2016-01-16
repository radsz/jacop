/**
 *  Min.java 
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
 * Min constraint implements the minimum/2 constraint. It provides the minimum
 * varable from all FD varaibles on the list.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.4
 */

public class Min extends Constraint {

	static int IdNumber = 1;

	/**
	 * It specifies a list of variables among which the minimum value is being searched for. 
	 */
	public IntVar list[];

	/**
	 * It specifies variable min, which stores the minimum value within the whole list.
	 */
	public IntVar min;

	/**
	 * It specifies the length of the list.
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
	public static String[] xmlAttributes = {"list", "min"};

	/**
	 * It constructs min constraint.
	 * @param min variable denoting the minimal value
	 * @param list the array of variables for which the minimal value is imposed.
	 */
	public Min(IntVar[] list, IntVar min) {

		assert ( list != null ) : "List variable is null";
		assert ( min != null ) : "Min variable is null";

		this.numberId = IdNumber++;
		this.l = list.length;
		this.numberArgs = (short) (l + 1) ;
		this.min = min;
		this.list = new IntVar[l];
		
		for (int i = 0; i < l; i++) {
			assert (list[i] != null) : i + "-th variable in a list is null";
			this.list[i] = list[i];
		}

		if (list.length > 1000)  // rule of thumb
		    this.queueIndex = 2;
		else
		    this.queueIndex = 1;
	}
	
	/**
	 * It constructs min constraint.
	 * @param min variable denoting the minimal value
	 * @param list the array of variables for which the minimal value is imposed.
	 */
	public Min(ArrayList<? extends IntVar> list, IntVar min) {

		this(list.toArray(new IntVar[list.size()]), min);
		
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(list.length + 1);

		variables.add(min);
		for (int i = 0; i < list.length; i++)
			variables.add(list[i]);
		return variables;
	}

	@Override
	public void consistency(Store store) {

	        int start = position.value();
		IntVar var;
		IntDomain vDom;

		//@todo keep one variable with the smallest value as watched variable
		// only check for other support if that smallest value is no longer part
		// of the variable domain. 
		
		do {
			
			store.propagationHasOccurred = false;
			
			int minValue = IntDomain.MaxInt;
			int maxValue = IntDomain.MaxInt;

			int minMin = min.min();
			int maxMin = min.max();
			for (int i = start; i < l; i++) {
				var = list[i];

				vDom = var.dom();
				int varMin = vDom.min(), varMax = vDom.max();

				if(varMin > maxMin) {
				    swap(start, i);
				    start++;
				}
				else if (varMin < minMin)
				    var.domain.inMin(store.level, var, minMin);

				minValue = (minValue < varMin) ? minValue : varMin;
				maxValue = (maxValue < varMax) ? maxValue : varMax;
			}

			position.update(start);

			min.domain.in(store.level, min, minValue, maxValue);

			if (start == l) // all variables have their min value greater than max value of min variable
			    throw store.failException;
			if (start == list.length-1) { // one variable on the list is minimal; its is max < min of all other variables
			    list[start].domain.in(store.level, list[start], min.dom());

			    if (min.singleton())
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

		min.putModelConstraint(this, getConsistencyPruningEvent(min));

		for (Var V : list)
			V.putModelConstraint(this, getConsistencyPruningEvent(V));

		store.addChanged(this);
		store.countConstraint();

	}

	@Override
	public void removeConstraint() {
		min.removeConstraint(this);
		for (int i = 0; i < list.length; i++) {
			list[i].removeConstraint(this);
		}
	}
	
	@Override
	public boolean satisfied() {
		
		if ( ! min.singleton() )
			return false;
		
		int minValue = min.max();
		int i = 0;
		boolean eq = false;
		
		while (i < list.length) {
			if (list[i].min() < minValue)
				return false;
			if (!eq && (list[i].singleton() && list[i].value() == minValue))
				eq = true;
			i++;
		}
		
		return eq;
	}

	@Override
	public String toString() {
		StringBuffer result = new StringBuffer( id() );
		
		result.append(" : min( [ ");
		for (int i = 0; i < list.length; i++) {
			result.append( list[i] );
			if (i < list.length - 1)
				result.append(", ");
		}
		
		result.append("], ").append(this.min);
		result.append(")");
		
		return result.toString();
	
	}

    @Override
	public void increaseWeight() {
		if (increaseWeight) {
			min.weight++;
			for (Var v : list) v.weight++;
		}
	}
	
}
