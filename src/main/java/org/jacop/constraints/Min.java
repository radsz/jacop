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

/**
 * Min constraint implements the minimum/2 constraint. It provides the minimum
 * varable from all FD varaibles on the list.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
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

		this.queueIndex = 1;
		this.numberId = IdNumber++;
		this.numberArgs = (short) (list.length + 1) ;
		this.min = min;
		this.list = new IntVar[list.length];
		for (int i = 0; i < list.length; i++) {
			assert (list[i] != null) : i + "-th variable in a list is null";
			this.list[i] = list[i];
		}
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

		IntVar var;
		IntDomain vDom;

		//@todo keep one variable with the smallest value as watched variable
		// only check for other support if that smallest value is no longer part
		// of the variable domain. 
		
		do {
			
			store.propagationHasOccurred = false;
		
			// @todo, optimize, if there is no change on min.min() then
			// the below inMin does not have to be executed.
			
			int minValue = IntDomain.MaxInt;
			int maxValue = IntDomain.MaxInt;
//            int minMaxValue=IntDomain.MaxInt;

			int minMin = min.min();
			for (int i = 0; i < list.length; i++) {
				var = list[i];

				var.domain.inMin(store.level, var, minMin);

				vDom = var.dom();
				int VdomMin = vDom.min(), VdomMax = vDom.max();
				minValue = (minValue < VdomMin) ? minValue : VdomMin;
//                if (minValue > VdomMin) {
//                    minValue = VdomMin;
//                    minMaxValue = var.max();
//                }
//                else if (minValue == VdomMin)
//                    if (minMaxValue > var.max())
//                        minMaxValue = var.max();

				maxValue = (maxValue < VdomMax) ? maxValue : VdomMax;
            }

			min.domain.in(store.level, min, minValue, maxValue);

			int n=0, pos=-1;
			for (int i = 0; i < list.length; i++) {
				var = list[i];
//				if (minMaxValue <= var.min())
                if (maxValue < var.min())
				    n++;
				else 
				    pos = i;
			}
			if (n == list.length-1) // one variable on the list is minimal; its is max < min of all other variables
			    list[pos].domain.in(store.level, list[pos], min.dom());

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
