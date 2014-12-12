/**
 *  Alldifferent.java 
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
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;

/**
 * Alldifferent constraint assures that all FDVs has differnet values. It uses
 * partial consistency technique.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Alldifferent extends Constraint {

	static int idNumber = 1;
	
	/**
	 * It specifies a list of variables which must take different values.
	 */
	public IntVar[] list;
	
	int stamp = 0;

	LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<IntVar>();

	protected HashMap<IntVar, Integer> positionMapping;
	
	protected TimeStamp<Integer> grounded;
	
	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"list"};
	
	/**
	 * It constructs the alldifferent constraint for the supplied variable.
	 * @param list variables which are constrained to take different values.
	 */
	public Alldifferent(IntVar[] list) {

		assert (list != null) : "Variables list is null";
		
		this.numberId = idNumber++;
		this.list = new IntVar[list.length];
		this.numberArgs = (short) list.length;
		
		for (int i = 0; i < list.length; i++) {
			assert (list[i] != null) : i + "-th element in the list is null";
			this.list[i] = list[i];
		}

	}

	/**
	 * It constructs the alldifferent constraint for the supplied variable.
	 * @param variables variables which are constrained to take different values.
	 */

	public Alldifferent(ArrayList<? extends IntVar> variables) {

		numberId = idNumber++;
		list = new IntVar[variables.size()];
		list = variables.toArray(list);

		numberArgs = (short) variables.size();
	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> Variables = new ArrayList<Var>(list.length);

        Variables.addAll(Arrays.asList(list));

		return Variables;
	}

	@Override
	public void consistency(Store store) {

		do {
			
			store.propagationHasOccurred = false;

			LinkedHashSet<IntVar> fdvs = variableQueue;
			variableQueue = new LinkedHashSet<IntVar>();

			for (IntVar Q : fdvs)
				if (Q.singleton()) {
					int qPos = positionMapping.get(Q);
					int groundPos = grounded.value();
					if (qPos > groundPos) {
						list[qPos] = list[groundPos];
						list[groundPos] = Q;
						positionMapping.put(Q, groundPos);
						positionMapping.put(list[qPos], qPos);
						grounded.update(++groundPos);
						for (int i = groundPos; i < list.length; i++)
							list[i].domain.inComplement(store.level, list[i], Q.min());
					}
					else if (qPos == groundPos) {
							grounded.update(++groundPos);
							for (int i = groundPos; i < list.length; i++)
								list[i].domain.inComplement(store.level, list[i], Q.min());
					}
					
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
			return IntDomain.GROUND;
	}
	
	@Override
	public boolean satisfied() {
		 
		 for(int i = grounded.value(); i < list.length; i++)
			 if (!list[i].singleton())
				 return false;
		
		 HashSet<Integer> values = new HashSet<Integer>();

        for (IntVar aList : list)
            if (!values.add(aList.value()))
                return false;

        return true;
		 
	 }

	 @SuppressWarnings("unused")
	private boolean satisfiedFullCheck(Store S) {
	 
		 	int i = 0;
	 
		 	IntervalDomain result = new IntervalDomain();
		 	
		 	while (i < list.length - 1) {
		 			
		 		if (list[i].domain.isIntersecting(result))
		 			return false;
		 			
		 		result.addDom(list[i].domain);
		 			
		 		i++;
		 	}
		 		
		 	return true;
		 	
	 }

	@Override
	public void impose(Store store) {
		int level = store.level;

		int pos = 0;
		positionMapping = new HashMap<IntVar, Integer>();
		for (IntVar v : list) {
			positionMapping.put(v, pos++);
			v.putModelConstraint(this, getConsistencyPruningEvent(v));
			queueVariable(level, v);
		}
		grounded = new TimeStamp<Integer>(store, 0);
		
		store.addChanged(this);
		store.countConstraint();
	}
        
	@Override
	public void queueVariable(int level, Var V) {
		variableQueue.add((IntVar)V);
	}

	@Override
	public void removeConstraint() {
		for (Var v : list)
			v.removeConstraint(this);
	}

	@SuppressWarnings("unused")
	private boolean satisfiedBound() {
		boolean sat = true;
		int i = 0;
		while (sat && i < list.length) {
			IntDomain vDom = list[i].dom();
			int vMin = vDom.min(), vMax = vDom.max();
			int j = i + 1;
			while (sat && j < list.length) {
				IntDomain ljDom = list[j].dom();
				sat = (vMin > ljDom.max() || vMax < ljDom.min());
				j++;
			}
			i++;
		}
		return sat;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer( id() );
		
		result.append(" : alldifferent([");

		for (int i = 0; i < list.length; i++) {
			result.append(list[i]);
			if (i < list.length - 1)
				result.append(", ");
		}
		result.append("])");
		
		return result.toString();
		
	}

    @Override
	public void increaseWeight() {
		if (increaseWeight) {
			for (Var v : list) 
				v.weight++;
		}
	}	

}
