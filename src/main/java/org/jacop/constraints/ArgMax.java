/**
 *  ArgMax.java 
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
import org.jacop.core.BoundDomain;
import org.jacop.core.IntervalDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * ArgMax constraint provides the index of the maximum
 * variable from all variables on the list. 
 * 
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class ArgMax extends Constraint {

    static int counter = 1;

    boolean firstConsistencyCheck = true;

    /**
     * It specifies a list of variables among which a maximum value is being searched for.
     */
    public IntVar list[];

    /**
     * It specifies variable max which stores the maximum value present in the list. 
     */
    public IntVar maxIndex;


    /**
     * It specifies indexOffset within an element constraint list[index-indexOffset] = value.
     */
    public int indexOffset;

    /**
     * tirbreak == true --> select element with the lowest index if exist several 
     */
    public boolean tiebreak = true;

    /**
     * It specifies the arguments required to be saved by an XML format as well as 
     * the constructor being called to recreate an object from an XML format.
     */
    public static String[] xmlAttributes = {"list", "maxIndex"};
	
    /**
     * It constructs max constraint.
     * @param maxIndex variable denoting the index of the maximum value
     * @param list the array of variables for which the index of the maximum value is imposed.
     * @param indexOffset the offset for the index that is computed from 1 by default (if needed from 0, use -1 for this parameter)
     * @param tiebreak defines if tie breaking sgould be used (returning the least index if several maximum elements
     */
    public ArgMax(IntVar[] list, IntVar maxIndex, int indexOffset, boolean tiebreak) {

	this(list, maxIndex);
	this.indexOffset = indexOffset;
	this.tiebreak = tiebreak;
    }

    public ArgMax(IntVar[] list, IntVar maxIndex) {

	assert ( list != null ) : "List variable is null";
	assert ( maxIndex != null ) : "MaxIndex variable is null";

	this.queueIndex = 1;
	this.numberId = counter++;
	this.numberArgs = (short) (list.length + 1);
	this.indexOffset = 0;
	this.maxIndex = maxIndex;
	this.list = new IntVar[list.length];
		
	for (int i = 0; i < list.length; i++) {
	    assert (list[i] != null) : i + "-th variable in the list is null";
	    this.list[i] = list[i];
	}
    }

    /**
     * It constructs max constraint.
     * @param maxIndex variable denoting index of the maximum value
     * @param variables the array of variables for which the maximum value is imposed.
     */
    public ArgMax(ArrayList<? extends IntVar> variables, IntVar maxIndex, int indexOffset, boolean tiebreak) {
	this(variables, maxIndex);
	this.indexOffset = indexOffset;
	this.tiebreak = tiebreak;
    }

    public ArgMax(ArrayList<? extends IntVar> variables, IntVar maxIndex) {

	this(variables.toArray(new IntVar[variables.size()]), maxIndex);
		
    }


    @Override
    public ArrayList<Var> arguments() {

	ArrayList<Var> variables = new ArrayList<Var>(list.length + 1);

	variables.add(maxIndex);
	for (int i = 0; i < list.length; i++)
	    variables.add(list[i]);
	return variables;
    }

    @Override
    public void consistency(Store store) {
		
	IntVar var;
	IntDomain vDom;

	if (firstConsistencyCheck) {
	    maxIndex.domain.in(store.level, maxIndex, 1 + indexOffset, list.length + indexOffset);
	    firstConsistencyCheck = false;
	}


	do {

	    store.propagationHasOccurred = false;
			
	    int minValue = IntDomain.MinInt;
	    int maxValue = IntDomain.MinInt;
	    int pos = -1;

	    int singleMaxValue = IntDomain.MinInt;
	    boolean singleExists = false;
	    for (int i = 0; i < maxIndex.min() - 1 - indexOffset; i++) {

		vDom = list[i].dom();
		int VdomMin = vDom.min(), VdomMax = vDom.max();
			
		if (minValue < VdomMin) {
		    minValue = VdomMin;
		    pos = i + 1 + indexOffset;
		}
		if (maxValue < VdomMax) {
		    maxValue = VdomMax;
		}
		if (list[i].singleton()) {
		    singleExists = true;
		    if (list[i].value() > singleMaxValue)
			singleMaxValue = list[i].value();
		}
	    }

	    // for (int i = 0; i < list.length; i++) {
	    for (ValueEnumeration e = maxIndex.dom().valueEnumeration(); e.hasMoreElements();) {
	    	int i = e.nextElement() - 1 - indexOffset;
				
		vDom = list[i].dom();
		int VdomMin = vDom.min(), VdomMax = vDom.max();
			
		if (minValue < VdomMin) {
		    minValue = VdomMin;
		    pos = i + 1 + indexOffset;
		}
		if (maxValue < VdomMax) {
		    maxValue = VdomMax;
		}
	    }


	    if (tiebreak && minValue == maxValue) { // selecting the element with lowest index

		maxIndex.domain.in(store.level, maxIndex, pos, pos);

		for (int i = 0; i < list.length; i++) {

		    IntVar vi = list[i];

		    if (i + 1 + indexOffset < pos)
			vi.domain.inMax(store.level, vi, maxValue - 1);
		    else if (i + 1 + indexOffset > pos)
			vi.domain.inMax(store.level, vi, maxValue);
		}

		return;

	    } else
		{ // no selection of a particular element
		    // BoundDomain d = new BoundDomain(minValue, maxValue);
		    IntervalDomain indexDom = new IntervalDomain();
		    for (int i = 0; i < list.length; i++) {
			var = list[i];
			if (var.max() >= minValue && var.max() <= maxValue) // (d.isIntersecting(var.dom()) )
			    indexDom.addDom(new BoundDomain(i + 1 + indexOffset, i + 1 + indexOffset));
		    }

		    maxIndex.domain.in(store.level, maxIndex, indexDom);

		    if (maxIndex.singleton() && singleExists) {
		    	IntVar sv = list[maxIndex.value() - 1 - indexOffset];
			sv.domain.inMin(store.level, sv, singleMaxValue + 1);
		    }

		    for (int i = 0; i < list.length; i++) {
			var = list[i];

			if (! maxIndex.dom().isIntersecting(new BoundDomain(i+1+indexOffset, i+1+indexOffset))) {
			    if (tiebreak) {
				if(i+1+indexOffset < maxIndex.min()) 
				    var.domain.inMax(store.level, var, maxValue - 1);
				else if (i+1+indexOffset > maxIndex.max())
				    var.domain.inMax(store.level, var, maxValue);
			    } else
				var.domain.inMax(store.level, var, maxValue - 1);
			} 
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
	return IntDomain.BOUND;
    }

    // registers the constraint in the constraint store
    @Override
    public void impose(Store store) {

	maxIndex.putModelConstraint(this, getConsistencyPruningEvent(maxIndex));

	for (Var V : list)
	    V.putModelConstraint(this, getConsistencyPruningEvent(V));

	store.addChanged(this);
	store.countConstraint();

    }

    @Override
    public void removeConstraint() {
	maxIndex.removeConstraint(this);
	for (int i = 0; i < list.length; i++) {
	    list[i].removeConstraint(this);
	}
    }

    @Override
    public boolean satisfied() {

	boolean sat = maxIndex.singleton();

	int MAX = list[maxIndex.value()].value();
	int i = 0, eq = 0;
	while (sat && i < list.length) {
	    if (list[i].singleton() && list[i].value() <= MAX)
		eq++;
	    sat = list[i].max() <= MAX;
	    i++;
	}
		
	return sat && eq == list.length;
    }

    @Override
    public String toString() {
		
	StringBuffer result = new StringBuffer( id() );
		
	result.append(" : ArgMax(  [ ");
	for (int i = 0; i < list.length; i++) {
	    result.append( list[i] );
	    if (i < list.length - 1)
		result.append(", ");
	}
		
	result.append("], ").append(this.maxIndex);
	result.append(")");

	return result.toString();
    }

    @Override
    public void increaseWeight() {
	if (increaseWeight) {
	    maxIndex.weight++;
	    for (Var v : list) v.weight++;
	}
    }
}
