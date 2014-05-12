/**
 *  ElementFloat.java 
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
import java.util.HashMap;
import java.util.Hashtable;

import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatInterval;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatIntervalEnumeration; 


/**
 * ElementFloat constraint defines a relation 
 * list[index - indexOffset] = value.
 * 
 * The first element of the list corresponds to index - indexOffset = 1.
 * By default indexOffset is equal 0 so first value within a list corresponds to index equal 1.
 * 
 * If index has a domain from 0 to list.length-1 then indexOffset has to be equal -1 to 
 * make addressing of list array starting from 1.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 3.1
 */

public class ElementFloat extends Constraint {

    static int idNumber = 1;

    boolean firstConsistencyCheck = true;
    int firstConsistencyLevel;

	
    /**
     * It specifies variable index within an element constraint list[index-indexOffset] = value.
     */
    public IntVar index;

    /**
     * It specifies variable value within an element constraint list[index-indexOffset] = value.
     */
    public FloatVar value;

    /**
     * It specifies indexOffset within an element constraint list[index-indexOffset] = value.
     */
    public final int indexOffset;

    /**
     * It specifies list of variables within an element constraint list[index-indexOffset] = value.
     * The list is addressed by positive integers (>=1) if indexOffset is equal to 0. 
     */
    public double list[];

    /**
     * It specifies for each value what are the possible values of the index variable (it 
     * takes into account indexOffset. 
     */
    Hashtable<Double, IntDomain> mappingValuesToIndex = new Hashtable<Double, IntDomain>();

    boolean indexHasChanged = true;
    boolean valueHasChanged = true;

    /**
     * It holds information about the positions within list array that are equal. It allows
     * to safely skip duplicates when enumerating index domain. 
     */
    ArrayList<IntDomain> duplicates;
	
    /**
     * It specifies the arguments required to be saved by an XML format as well as 
     * the constructor being called to recreate an object from an XML format.
     */	
    public static String[] xmlAttributes = {"index", "list", "value", "indexOffset"};

    /**
     * It constructs an element constraint. 
     * 
     * @param index variable index
     * @param list list of integers from which an index-th element is taken
     * @param value a value of the index-th element from list
     * @param indexOffset shift applied to index variable. 
     */
    public ElementFloat(IntVar index, double[] list, FloatVar value, int indexOffset) {

	this.indexOffset = indexOffset;
	commonInitialization(index, list, value);
		
    }

    private void commonInitialization(IntVar index, double[] list, FloatVar value) {

	queueIndex = 1;

	assert (index != null) : "Argument index is null";
	assert (list != null) : "Argument list is null";
	assert (value != null) : "Argument value is null";
				
	this.numberId = idNumber++;
	this.index = index;
	this.value = value;
	this.numberArgs = (short) (numberArgs + 2);
	this.list = new double[list.length];
	this.queueIndex = 1;
		
	for (int i = 0; i < list.length; i++) {
						
	    Double listElement = list[i];
	    this.list[i] = list[i];
			
	    IntDomain oldFD = mappingValuesToIndex.get(listElement);
	    if (oldFD == null) {
		mappingValuesToIndex.put(listElement, new IntervalDomain(i + 1 + indexOffset, i + 1 + indexOffset));
	    }
	    else
		((IntervalDomain)oldFD).addLastElement(i + 1 + indexOffset);
	    //     			    oldFD.unionAdapt(i + 1 + indexOffset, i + 1 + indexOffset);
			
	}

    }
	
    /**
     * It constructs an element constraint with default indexOffset equal 0.
     * 
     * @param index index variable.
     * @param list list containing variables which one pointed out by index variable is made equal to value variable.  
     * @param value a value variable equal to the specified element from the list. 
     */
    public ElementFloat(IntVar index, ArrayList<Double> list, FloatVar value) {

	this(index, list, value, 0);
		
    }

    /**
     * It constructs an element constraint. 
     * 
     * @param index variable index
     * @param list list of integers from which an index-th element is taken
     * @param value a value of the index-th element from list
     * @param indexOffset shift applied to index variable. 
     */
    public ElementFloat(IntVar index, ArrayList<Double> list, FloatVar value, int indexOffset) {
		
	this.indexOffset = indexOffset;
		
	double [] listOfInts = new double[list.size()];
	for (int i = 0; i < list.size(); i++)
	    listOfInts[i] = list.get(i);
		
	commonInitialization(index, listOfInts, value);
		
    }

    /**
     * It constructs an element constraint with indexOffset by default set to 0.  
     * 
     * @param index variable index
     * @param list list of integers from which an index-th element is taken
     * @param value a value of the index-th element from list
     */

    public ElementFloat(IntVar index, double[] list, FloatVar value) {

	this(index, list, value, 0);
		
    }


    @Override
    public ArrayList<Var> arguments() {

	ArrayList<Var> variables = new ArrayList<Var>(2);

	variables.add(index);
	variables.add(value);
		
	return variables;
		
    }

    @Override
    public void removeLevel(int level) {
	if (level == firstConsistencyLevel)
	    firstConsistencyCheck = true;
    }

    @Override
    public void consistency(Store store) {

	if (firstConsistencyCheck) {

	    index.domain.in(store.level, index, 1 + indexOffset, list.length + indexOffset);
	    firstConsistencyCheck = false;
	    firstConsistencyLevel = store.level;

	}

		
	boolean copyOfValueHasChanged = valueHasChanged;
		
	if (indexHasChanged) {

	    indexHasChanged = false;
	    IntDomain indexDom = index.dom().cloneLight();
	    FloatDomain domValue = new FloatIntervalDomain(5);

	    for (IntDomain duplicate : duplicates) {
		if (indexDom.isIntersecting(duplicate)) {
		    domValue.unionAdapt(list[duplicate.min() - 1 - indexOffset]);

		    indexDom = indexDom.subtract(duplicate);
		}
	    }
			
	    // values of index for duplicated values within list are already taken care of above.
	    for (ValueEnumeration e = indexDom.valueEnumeration(); e.hasMoreElements();) {
		double valueOfElement = list[e.nextElement() - 1 - indexOffset];
		domValue.unionAdapt(valueOfElement);
	    }

	    value.domain.in(store.level, value, domValue);
	    valueHasChanged = false;
			
	}

	// the if statement above can change value variable but those changes can be ignored.
	if (copyOfValueHasChanged) {

	    valueHasChanged = false;
	    FloatDomain valDom = value.dom();
	    IntervalDomain domIndex = new IntervalDomain(5);

	    // for (ValueEnumeration e = valDom.valueEnumeration(); e.hasMoreElements();) {
	    // 	IntDomain i = mappingValuesToIndex.get(e.nextElement());
	    for (FloatIntervalEnumeration e = valDom.floatIntervalEnumeration(); e.hasMoreElements();) {
		FloatInterval fi = e.nextElement();
		for (int i = 0; i<list.length; i++)
		    if (list[i] >= fi.min() && list[i] <= fi.max())
			domIndex.addDom(new IntervalDomain(i + 1 + indexOffset, i + 1 + indexOffset));
	    }

	    index.domain.in(store.level, index, domIndex);
	    indexHasChanged = false;
			
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
	return IntDomain.ANY;
    }

    @Override
    public void impose(Store store) {

	index.putModelConstraint(this, getConsistencyPruningEvent(index));
	value.putModelConstraint(this, getConsistencyPruningEvent(value));

	store.addChanged(this);
	store.countConstraint();
		
	duplicates = new ArrayList<IntDomain>();
		
	HashMap<Double, IntDomain> map = new HashMap<Double, IntDomain>();
		
	for (int pos = 0; pos < list.length; pos++) {
		
	    double el = list[pos];
	    IntDomain indexes = map.get(el);
	    if (indexes == null) {
		indexes = new IntervalDomain(pos + 1 + indexOffset, pos + 1 + indexOffset);
		map.put(el, indexes);
	    }
	    else 
		indexes.unionAdapt(pos + 1 + indexOffset);
	}
		
	for (IntDomain duplicate: map.values()) {
	    if ( duplicate.getSize() > 20 )
		duplicates.add(duplicate);
	}
		
	valueHasChanged = true;
	indexHasChanged = true;
		
    }

    @Override
    public void queueVariable(int level, Var var) {
	if (var == index)
	    indexHasChanged = true;
	else
	    valueHasChanged = true;
    }

    @Override
    public void removeConstraint() {
	index.removeConstraint(this);
	value.removeConstraint(this);
    }

    @Override
    public boolean satisfied() {

	if (value.singleton()) {
		
	    double v = value.min();

            IntDomain duplicate = null;

            for (IntDomain d : duplicates) {
                if (index.domain.isIntersecting(d)) {
                    duplicate = d;
                    break;
                }
            }

	    if (duplicate == null) {
				
		if (!index.singleton())
		    return false;
		else 
		    if (list[index.value() - 1 - indexOffset] == v)
			return true;
			
	    }
	    else {
			
		if (duplicate.contains(index.domain) && list[index.min() - 1 - indexOffset] == v)
		    return true;
			
	    }
			
	    return false;
		
	}
	else
	    return false;
		
    }

    @Override
    public String toString() {
		
	StringBuffer result = new StringBuffer( id() );
		
	result.append(" : elementFloat").append("( ").append(index).append(", [");
		
	for (int i = 0; i < list.length; i++) {
	    result.append( list[i] );
			
	    if (i < list.length - 1)
		result.append(", ");
	}
		
	result.append("], ").append(value).append(", " + indexOffset + " )");

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
