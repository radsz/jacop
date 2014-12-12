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

package org.jacop.floats.constraints;

import java.util.ArrayList;

import org.jacop.constraints.Constraint;

import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.IntDomain;

/**
 * Max constraint implements the Maximum/2 constraint. It provides the maximum
 * variable from all variables on the list. 
 * 
 * max(list) = max.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Max extends Constraint {

	static int counter = 1;

	/**
	 * It specifies a list of variables among which a maximum value is being searched for.
	 */
	public FloatVar list[];

	/**
	 * It specifies variable max which stores the maximum value present in the list. 
	 */
	public FloatVar max;

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
	public Max(FloatVar[] list, FloatVar max) {

		assert ( list != null ) : "List variable is null";
		assert ( max != null ) : "Min variable is null";

		this.queueIndex = 1;
		this.numberId = counter++;
		this.numberArgs = (short) (list.length + 1);
		this.max = max;
		this.list = new FloatVar[list.length];
		
		for (int i = 0; i < list.length; i++) {
			assert (list[i] != null) : i + "-th variable in the list is null";
			this.list[i] = list[i];
		}
	}

	/**
	 * It constructs max constraint.
	 * @param max variable denoting the maximum value
	 * @param variables the array of variables for which the maximum value is imposed.
	 */
	public Max(ArrayList<? extends FloatVar> variables, FloatVar max) {

		this(variables.toArray(new FloatVar[variables.size()]), max);
		
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
		
		FloatVar var;
		FloatDomain vDom;

		do {

			store.propagationHasOccurred = false;
			
			// @todo, optimize, if there is no change on min.min() then
			// the below inMin does not have to be executed.

			double minValue = FloatDomain.MinFloat;
			double maxValue = FloatDomain.MinFloat;
		
			double maxMax = max.max();
			for (int i = 0; i < list.length; i++) {
				
				var = list[i];

				var.domain.inMax(store.level, var, maxMax);

				vDom = var.dom();
				double VdomMin = vDom.min(), VdomMax = vDom.max();
			
				minValue = (minValue > VdomMin) ? minValue : VdomMin;
				maxValue = (maxValue > VdomMax) ? maxValue : VdomMax;

			}

			max.domain.in(store.level, max, minValue, maxValue);

			int n=0, pos=-1;
			for (int i = 0; i < list.length; i++) {
				var = list[i];
				if (minValue > var.max())
				    n++;
				else 
				    pos = i;
			}
			if (n == list.length-1)  // one variable on the list is maximal; its is min > max of all other variables 
			    list[pos].domain.in(store.level, list[pos], max.dom());

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
		double MAX = max.min();
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
