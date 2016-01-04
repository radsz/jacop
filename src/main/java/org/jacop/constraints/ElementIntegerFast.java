/**
 *  ElementIntegerFast.java 
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
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Random;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.core.TimeStamp;

/**
 * ElementIntegerFast constraint defines a relation 
 * list[index - indexOffset] = value. This version uses bounds consistency.
 * 
 * The first element of the list corresponds to index - indexOffset = 1.
 * By default indexOffset is equal 0 so first value within a list corresponds to index equal 1.
 * 
 * If index has a domain from 0 to list.length-1 then indexOffset has to be equal -1 to 
 * make addressing of list array starting from 1.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.3
 */

public class ElementIntegerFast extends Constraint {

    static int idNumber = 1;

    boolean firstConsistencyCheck = true;

    /**
     * It specifies variable index within an element constraint list[index - indexOffset] = value.
     */
    public IntVar index;

    /**
     * It specifies variable value within an element constraint list[index - indexOffset] = value.
     */
    public IntVar value;

    /**
     * It specifies indexOffset within an element constraint list[index - indexOffset] = value.
     */
    public final int indexOffset;

    /**
     * It specifies list of variables within an element constraint list[index - indexOffset] = value.
     * The list is addressed by positive integers ({@code >=1}) if indexOffset is equal to 0. 
     */
    public int list[];
	
    /*
     * Defines if the current list is order (ascending, descending), needs detection (detect)
     * or is not checked (none).
     */
    private TimeStamp<Short> order;

    private short detect = 0, ascending = 1, descending = 2, none = 3;
    
    /**
     * It specifies the arguments required to be saved by an XML format as well as 
     * the constructor being called to recreate an object from an XML format.
     */		
    public static String[] xmlAttributes = {"index", "list", "value", "indexOffset"};

    /**
     * It constructs an element constraint. 
     * 
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     * @param indexOffset shift applied to index variable. 
     */
    public ElementIntegerFast(IntVar index, int[] list, IntVar value, int indexOffset) {

	this.indexOffset = indexOffset;
	commonInitialization(index, list, value);
    }

    private void commonInitialization(IntVar index, int[] list, IntVar value) {

	queueIndex = 1;

	assert (index != null) : "Variable index is null";
	assert (value != null) : "Variable value is null";

	this.numberId = idNumber++;
	this.index = index;
	this.value = value;
	this.numberArgs = (short) (numberArgs + 2);
	this.list = list;

    }

    /**
     * It constructs an element constraint. 
     * 
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     */
    public ElementIntegerFast(IntVar index, ArrayList<? extends Integer> list, IntVar value) {

	this.indexOffset = 0;
		
	int [] listOfInts = new int[list.size()];
	for (int i = 0; i < list.size(); i++)
	    listOfInts[i] = list.get(i);
		
	commonInitialization(index, listOfInts, value);

    }

    /**
     * It constructs an element constraint. 
     * 
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     * @param indexOffset shift applied to index variable. 
     */
    public ElementIntegerFast(IntVar index, ArrayList<? extends Integer> list, IntVar value, int indexOffset) {

	this.indexOffset = indexOffset;
		
	int [] listOfInts = new int[list.size()];
	for (int i = 0; i < list.size(); i++)
	    listOfInts[i] = list.get(i);
		
	commonInitialization(index, listOfInts, value);
    }

    /**
     * It constructs an element constraint. 
     * 
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     */
    public ElementIntegerFast(IntVar index, int[] list, IntVar value) {

	this(index, list, value, 0);

    }


    @Override
    public ArrayList<Var> arguments() {

	ArrayList<Var> variables = new ArrayList<Var>(list.length + 2);

	variables.add(index);
	variables.add(value);

	return variables;
    }

    @Override
    public void consistency(Store store) {

	if (firstConsistencyCheck) {

	    index.domain.in(store.level, index, 1 + this.indexOffset, list.length + this.indexOffset);
	    firstConsistencyCheck = false;
	}

	do {

	    store.propagationHasOccurred = false;

	    short sort = order.value();

	    if (sort == ascending || sort == descending) {
		int minIndex = index.min();
		int maxIndex = index.max();

		if (sort == ascending)
		    value.domain.in(store.level, value, list[minIndex - 1 - indexOffset], list[maxIndex - 1 - indexOffset]);
		else
		    value.domain.in(store.level, value, list[maxIndex - 1 - indexOffset], list[minIndex - 1 - indexOffset]);

		IntervalDomain indexDom = new IntervalDomain(5); // create with size 5 ;)			
		for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements();) {
		    int position = e.nextElement() - 1 - indexOffset;
		    int val = list[position];
		    
		    if (disjoint(value, val))
			if (indexDom.size == 0)
			    indexDom.unionAdapt(position + 1 + indexOffset);
			else
			    // indexes are in ascending order and can be added at the end if the last element
			    // plus 1 is not equal a new value. In such case the max must be changed.
			    indexDom.addLastElement(position + 1 + indexOffset);
		    else
			if (val == list[maxIndex - 1 - indexOffset])
			    break;
		}

		index.domain.in(store.level, index, indexDom.complement());

	    }
	    else if (sort == detect) {
		
		IntDomain vals = new IntervalDomain(5);
	    
		int min = IntDomain.MaxInt;
		int max = IntDomain.MinInt;
		IntervalDomain indexDom = new IntervalDomain(5); // create with size 5 ;)
		boolean asc = true, desc = true;
		int previous = list[index.min() - 1 - indexOffset];

		for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements();) {
		    int position = e.nextElement() - 1 - indexOffset;
		    int val = list[position];
		    
		    if (disjoint(value, val))
			if (indexDom.size == 0)
			    indexDom.unionAdapt(position + 1 + indexOffset);
			else
			    // indexes are in ascending order and can be added at the end if the last element
			    // plus 1 is not equal a new value. In such case the max must be changed.
			    indexDom.addLastElement(position + 1 + indexOffset);
		    else {
			min = Math.min(min, val);
			max = Math.max(max, val);
		    }

		    if (val > previous) 
			desc = false;
		    if (val < previous) 
			asc = false;

		    previous = val;
		}
		if (desc) 
		    order.update(descending);
		if (asc)
		    order.update(ascending);
		
		index.domain.in(store.level, index, indexDom.complement());
		value.domain.in(store.level, value, min, max);

		if (index.singleton()) {
		    int position = index.value() - 1 - indexOffset;
		    value.domain.in(store.level, value, list[position], list[position]);
		    removeConstraint();
		}
	    }
	    else {// sort == none

		IntDomain vals = new IntervalDomain(5);
	    
		int min = IntDomain.MaxInt;
		int max = IntDomain.MinInt;
		IntervalDomain indexDom = new IntervalDomain(5); // create with size 5 ;)
		for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements();) {
		    int position = e.nextElement() - 1 - indexOffset;
		    int val = list[position];

		    if (disjoint(value, val))
			if (indexDom.size == 0)
			    indexDom.unionAdapt(position + 1 + indexOffset);
			else
			    // indexes are in ascending order and can be added at the end if the last element
			    // plus 1 is not equal a new value. In such case the max must be changed.
			    indexDom.addLastElement(position + 1 + indexOffset);
		    else {
			min = Math.min(min, val);
			max = Math.max(max, val);
		    }
		}
		
		index.domain.in(store.level, index, indexDom.complement());
		value.domain.in(store.level, value, min, max);

		if (index.singleton()) {
		    int position = index.value() - 1 - indexOffset;
		    value.domain.in(store.level, value, list[position], list[position]);
		    removeConstraint();
		}
	    }
	} while (store.propagationHasOccurred);
    }

    boolean disjoint(IntVar v1, int v2) {
        if (v1.min() > v2 || v2 > v1.max()) 
            return true;
        else
	    if (! v1.domain.contains(v2))
	    	return true;
	    else
	    	return false;
    }
    
    @Override
    public int getConsistencyPruningEvent(Var var) {

	// If consistency function mode
	if (consistencyPruningEvents != null) {
	    Integer possibleEvent = consistencyPruningEvents.get(var);
	    if (possibleEvent != null)
		return possibleEvent;
	}
	return IntDomain.ANY;
    }

    @Override
    public void impose(Store store) {

	store.registerRemoveLevelListener(this);

	index.putModelConstraint(this, getConsistencyPruningEvent(index));
	value.putModelConstraint(this, getConsistencyPruningEvent(value));

	order = new TimeStamp<Short>(store, detect); // set to detect

	store.addChanged(this);
	store.countConstraint();
    }

    @Override
    public void removeConstraint() {
	index.removeConstraint(this);
	value.removeConstraint(this);
    }

    @Override
    public boolean satisfied() {
	boolean sat = value.singleton();
	if (sat) {
	    int v = value.min();
	    ValueEnumeration e = index.domain.valueEnumeration();
	    while (sat && e.hasMoreElements()) {
		int fdv = list[e.nextElement() - 1 - indexOffset];
		sat = (fdv == v);
	    }
	}
	return sat;
    }

    @Override
    public String toString() {

	StringBuffer result = new StringBuffer( id() );

	result.append(" : elementIntegerFast").append("( ").append(index).append(", [");

	for (int i = 0; i < list.length; i++) {
	    result.append( list[i] );

	    if (i < list.length - 1)
		result.append(", ");
	}

	result.append("], ").append(value).append(" )");

	return result.toString();

    }

    @Override
    public void increaseWeight() {
	if (increaseWeight) {
	    index.weight++;
	    value.weight++;
	}
    }

}
