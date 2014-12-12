/**
 *  RandomSelect.java 
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

package org.jacop.search;

import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Random;

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Var;

/**
 * It is simple and customizable selector of decisions (constraints) which will
 * be enforced by search.
 * 
 * @author  Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class RandomSelect<T extends Var> implements SelectChoicePoint<T> {

    static final boolean debugAll = false;

    public T[] searchVariables;

    Indomain<T> valueOrdering;

    /**
     * It stores the original positions of variables to be used for input order
     * tie-breaking.
     */

    public IdentityHashMap<T, Integer> position;

    int currentIndex = 0;

    Random random = new Random();

    /**
     * The constructor to create a simple choice select mechanism.
     * @param variables variables upon which the choice points are created.
     * @param indomain the value heuristic to choose a value for a given variable.
     */
    public RandomSelect(T[] variables, Indomain<T> indomain) {

	position = new IdentityHashMap<T, Integer>();

	int unique = 0;
	for (int i = 0; i < variables.length; i++) {
	    if (position.get(variables[i]) == null)
		position.put(variables[i], unique++);
	}

	this.searchVariables = (T[]) new Var[position.size()];

	for (Iterator<Map.Entry<T, Integer>> itr = position.entrySet()
		 .iterator(); itr.hasNext();) {
	    Map.Entry<T, Integer> e = itr.next();
	    searchVariables[e.getValue()] = e.getKey();
	}

	valueOrdering = indomain;

    }

    /**
     * It returns the variable which is the base on the next choice point. Only
     * if choice is of an X = C type. This function returns null if all
     * variables have a value assigned or a choice point based on other type of
     * constraint is being selected. The parameter index is the last value which
     * have been return by this SelectChoicePoint object which has not been
     * backtracked upon yet.
     */

    public T getChoiceVariable(int index) {

	assert (index < searchVariables.length);

	if (debugAll) {
	    System.out.println ("index = " + index);

	    for (int i = 0; i < searchVariables.length; i++) 
		System.out.print (searchVariables[i] + " ");
	    System.out.println();
	}

	int finalIndex = searchVariables.length;
	T currentVariable;

	do {

	    int size = finalIndex - index;

	    int selectedIndex = index + random.nextInt(size);
	    currentVariable = placeSearchVariable(index, selectedIndex);

	} while (currentVariable.singleton() && ++index < finalIndex);

	if (index == finalIndex) {
	    return null;
	} else {
	    currentIndex = index;

	    if (debugAll)
		System.out.println ("selected " + currentVariable);

	    return currentVariable;
	}
    }

    /**
     * It returns a value which is the base of the next choice point. Only if
     * choice is of an X = C type.
     */

    public int getChoiceValue() {

	assert (currentIndex >= 0);
	assert (currentIndex < searchVariables.length);
	assert (searchVariables[currentIndex].dom() != null);
		
	return valueOrdering.indomain(searchVariables[currentIndex]);

    }

    /**
     * It always returns null as choice point is obtained by getChoiceVariable
     * and getChoiceValue.
     */

    public PrimitiveConstraint getChoiceConstraint(int index) {

	return null;

    }

    /**
     * It returns the variables for which assignment in the solution is given.
     */

    public IdentityHashMap<T, Integer> getVariablesMapping() {

	return position;

    }

    /**
     * It returns the current index. Supplying this value in the next invocation
     * of select will make search for next variable faster without comprimising
     * efficiency.
     */

    public int getIndex() {
	return currentIndex;
    }

    /**
     * It gets as input the index of the variable which is chosen by search to
     * be instantiated at this stage. The variable is positioned at search
     * position.
     * @param searchPosition position at which search store currently choosen variable.
     * @param variablePosition current position of the variable choosen by search. 
     * @return variable choosen to be a base of the choice point.
     */

    public T placeSearchVariable(int searchPosition, int variablePosition) {

	if (searchPosition != variablePosition) {

	    T temp = searchVariables[searchPosition];

	    searchVariables[searchPosition] = searchVariables[variablePosition];

	    searchVariables[variablePosition] = temp;
	}

	return searchVariables[searchPosition];

    }

    public String toString() {
	return ""+java.util.Arrays.asList(searchVariables);
    }
}
