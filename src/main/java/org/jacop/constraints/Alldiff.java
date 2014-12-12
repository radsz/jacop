/**
 *  Alldiff.java 
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
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashSet;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;


/**
 * Alldiff constraint assures that all FDVs has different values. It uses bounds
 * consistency technique as described in the paper by J.-F. Puget, "A fast
 * algorithm for the bound consistency of alldiff constraints", in Proceedings
 * of the Fifteenth National Conference on Artificial Intelligence (AAAI '98),
 * 1998. It implements the method with time complexity O(n^2). Before using
 * bounds consistency it calls consistency method from Alldifferent constraint.
 * 
 * It extends basic functionality of Alldifferent constraint.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class Alldiff extends Alldifferent {

	// it stores the store locally so all the private functions which 
	// are part of the consistency function can throw failure exception
	// without passing store argument every time their function is called.
	Store store;

	int[] min, max, u;

	Comparator<IntVar> maxVariable = new VariablemaxComparator<IntVar>();

	Comparator<IntVar> minVariable = new VariableminComparator<IntVar>();

	protected IntVar[] listAlldiff;	

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"list"};

	/**
	 * It constructs the alldiff constraint for the supplied variable.
	 * @param variables variables which are constrained to take different values.
	 */
	public Alldiff(IntVar[] variables) {

		super(variables);
		Alldifferent.idNumber--;
		
	        this.queueIndex = 2;

		this.numberId = idNumber++;
		this.numberArgs = (short) variables.length;
		listAlldiff = new IntVar[variables.length];
		
		for (int i = 0; i < variables.length; i++)
			listAlldiff[i] = variables[i];

		min = new int[variables.length];
		max = new int[variables.length];
		u = new int[variables.length];
	}

	
	/**
	 * It constructs the alldiff constraint for the supplied variable.
	 * @param variables variables which are constrained to take different values.
	 */
	public Alldiff(ArrayList<? extends IntVar> variables) {
		this(variables.toArray(new IntVar[variables.size()]));
	}


	@Override
	public int getConsistencyPruningEvent(Var var) {

		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return IntDomain.BOUND;
	}

	@Override
	public void impose(Store store) {
		
		this.store = store;

		int level = store.level;

		int pos = 0;
		positionMapping = new HashMap<IntVar, Integer>();
		
		for (IntVar v : listAlldiff) {
			positionMapping.put(v, pos++);
			v.putModelConstraint(this, getConsistencyPruningEvent(v));
			queueVariable(level, v);
		}
		grounded = new TimeStamp<Integer>(store, 0);
		
		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void consistency(Store store) {
		
		if (store.currentQueue == queueIndex) {	
		
			while (!variableQueue.isEmpty()) {
				
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
			}

			if (queueIndex + 1 < store.queueNo) {
				store.changed[queueIndex + 1].add(this);
				return;
			}

		}

		maxPass();
		minPass();

	}

	void minPass() {
		
		Arrays.sort(listAlldiff, minVariable);

		for (int i = 0; i < listAlldiff.length; i++) {
			min[i] = listAlldiff[i].min();
			max[i] = listAlldiff[i].max();
		}

		for (int i = 0; i < listAlldiff.length; i++)
			insertMin(i);
	}

	void maxPass() {
		
		Arrays.sort(listAlldiff, maxVariable);

		for (int i = 0; i < listAlldiff.length; i++) {
			min[i] = listAlldiff[i].min();
			max[i] = listAlldiff[i].max();
		}

		for (int i = 0; i < listAlldiff.length; i++)
			insertMax(i);
	}

	void insertMax(int i) {
		u[i] = min[i];

		int bestMin = IntDomain.MaxInt + 1;
		for (int j = 0; j < i; j++) {
			if (min[j] < min[i]) {
				u[j]++;
				if (u[j] > max[i])
			    	throw Store.failException;
				if (u[j] == max[i] && min[j] < bestMin)
					bestMin = min[j];
			} else
				u[i]++;
		}
		if (u[i] > max[i])
	    	throw Store.failException;
		if (u[i] == max[i] && min[i] < bestMin)
			bestMin = min[i];

		if (bestMin <= IntDomain.MaxInt)
			incrMin(bestMin, max[i], i);
	}

	void incrMin(int a, int b, int i) {
		for (int j = i + 1; j < min.length; j++)
			if (min[j] >= a) {
				listAlldiff[j].domain.inMin(store.level, listAlldiff[j], b + 1);
			}
	}

	void insertMin(int i) {
		u[i] = max[i];

		int bestMax = IntDomain.MinInt - 1;
		for (int j = 0; j < i; j++) {
			if (max[j] > max[i]) {
				u[j]--;
				if (u[j] < min[i])
			    	throw Store.failException;
				if (u[j] == min[i] && max[j] > bestMax)
					bestMax = max[j];
			} else
				u[i]--;
		}
		if (u[i] < min[i])
	    	throw Store.failException;
		if (u[i] == min[i] && max[i] > bestMax)
			bestMax = max[i];

		if (bestMax >= IntDomain.MinInt)
			decrMax(min[i], bestMax, i);
	}

	void decrMax(int a, int b, int i) {
		for (int j = i + 1; j < max.length; j++)
			if (max[j] <= b) {
				listAlldiff[j].domain.inMax(store.level, listAlldiff[j], a - 1);
			}
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer( id() );
		result.append(" : alldiff([");
		
		for (int i = 0; i < listAlldiff.length; i++) {
			result.append(listAlldiff[i]);
			if (i < listAlldiff.length - 1)
				result.append(", ");
		}
		
		result.append("])");
		
		return result.toString();

	}

    class VariablemaxComparator<T extends IntVar> implements Comparator<T> {

		VariablemaxComparator() {
		}

		public int compare(T o1, T o2) {
			return (o1.max() - o2.max());
		}
	}

	class VariableminComparator<T extends IntVar> implements Comparator<T> {

		VariableminComparator() {
		}

		public int compare(T o1, T o2) {
			return (o2.min() - o1.min());
		}
	}
	
}

