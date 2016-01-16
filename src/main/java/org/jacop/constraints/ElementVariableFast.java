/**
 *  ElementVariableFast.java 
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

/**
 * ElementVariableFast constraint defines a relation 
 * list[index - indexOffset] = value. This version uses bounds consistency.
 * 
 * The first element of the list corresponds to index - indexOffset = 1.
 * By default indexOffset is equal 0 so first value within a list corresponds to index equal 1.
 * 
 * If index has a domain from 0 to list.length-1 then indexOffset has to be equal -1 to 
 * make addressing of list array starting from 1.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.4
 */

public class ElementVariableFast extends Constraint {

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
    public IntVar list[];
	
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
    public ElementVariableFast(IntVar index, IntVar[] list, IntVar value, int indexOffset) {

	queueIndex = 2;

	assert (index != null) : "Variable index is null";
	assert (list != null) : "Variable list is null";
	assert (value != null) : "Variable value is null";

	this.indexOffset = indexOffset;
	this.numberId = idNumber++;
	this.index = index;
	this.value = value;
	this.numberArgs = (short) (numberArgs + 2);
	this.list = new IntVar[list.length];

	for (int i = 0; i < list.length; i++) {
	    assert (list[i] != null) : i + "-th element of list is null";
	    this.list[i] = list[i];
	    this.numberArgs++;
	}


    }

    /**
     * It constructs an element constraint. 
     * 
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     */
    public ElementVariableFast(IntVar index, ArrayList<? extends IntVar> list, IntVar value) {

	this(index, list.toArray(new IntVar[list.size()]), value, 0);

    }

    /**
     * It constructs an element constraint. 
     * 
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     * @param indexOffset shift applied to index variable. 
     */
    public ElementVariableFast(IntVar index, ArrayList<? extends IntVar> list, IntVar value, int indexOffset) {

	this(index, list.toArray(new IntVar[list.size()]), value, indexOffset);

    }

    /**
     * It constructs an element constraint. 
     * 
     * @param index variable index
     * @param list list of variables from which an index-th element is taken
     * @param value a value of the index-th element from list
     */
    public ElementVariableFast(IntVar index, IntVar[] list, IntVar value) {

	this(index, list, value, 0);

    }


    @Override
    public ArrayList<Var> arguments() {

	ArrayList<Var> variables = new ArrayList<Var>(list.length + 2);

	variables.add(index);
	variables.add(value);

	for (Var v : list)
	    variables.add(v);

	return variables;
    }

    @Override
    public void consistency(Store store) {

	if (firstConsistencyCheck) {

	    index.domain.in(store.level, index, 1 + this.indexOffset, list.length + this.indexOffset);
	    firstConsistencyCheck = false;
	}

	int min = IntDomain.MaxInt;
	int max = IntDomain.MinInt;
	IntervalDomain indexDom = new IntervalDomain(5); // create with size 5 ;)
	for (ValueEnumeration e = index.domain.valueEnumeration(); e.hasMoreElements();) {
	    int position = e.nextElement() - 1 - indexOffset;
		    
	    if (disjoint(value, list[position]))
		if (indexDom.size == 0)
		    indexDom.unionAdapt(position + 1 + indexOffset);
		else
		    indexDom.addLastElement(position + 1 + indexOffset);
	    else {
		min = Math.min(min, list[position].min());
		max = Math.max(max, list[position].max());
	    }
	}
		
	index.domain.in(store.level, index, indexDom.complement());
	value.domain.in(store.level, value, min, max);

	if (index.singleton()) {
	    int position = index.value() - 1 - indexOffset;
	    value.domain.in(store.level, value, list[position].domain);
	    list[ position].domain.in(store.level, list[position], value.domain);

	}
	if (value.singleton() && index.singleton()) {
	    IntVar v = list[index.value() - 1 - indexOffset];
	    v.domain.in(store.level, v, value.value(), value.value());
	    removeConstraint();
	}
    }

    boolean disjoint(IntVar v1, IntVar v2) {
        if (v1.min() > v2.max() || v2.min() > v1.max()) 
            return true;
        else
	    if (! v1.domain.isIntersecting(v2.domain))
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

	for (int i = 0; i < list.length; i++) 
	    list[i].putModelConstraint(this, getConsistencyPruningEvent(list[i]));
		
	store.addChanged(this);
	store.countConstraint();
    }

    @Override
    public void removeConstraint() {
	index.removeConstraint(this);
	value.removeConstraint(this);
	for (Var v : list)
	    v.removeConstraint(this);
    }

    @Override
    public boolean satisfied() {
	boolean sat = value.singleton();
	if (sat) {
	    int v = value.min();
	    ValueEnumeration e = index.domain.valueEnumeration();
	    while (sat && e.hasMoreElements()) {
		IntVar fdv = list[e.nextElement() - 1 - indexOffset];
		sat = fdv.singleton() && fdv.min() == v;
	    }
	}
	return sat;
    }

    @Override
    public String toString() {

	StringBuffer result = new StringBuffer( id() );

	result.append(" : elementVariableFast").append("( ").append(index).append(", [");

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
	    for (Var v : list) v.weight++;
	}
    }

}
