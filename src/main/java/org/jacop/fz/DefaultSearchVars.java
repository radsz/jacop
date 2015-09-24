/**
 *  DefaultSearchVars.java 
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
package org.jacop.fz;

import java.util.Comparator;
import java.util.Arrays;

import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.set.core.SetVar;
import org.jacop.floats.core.FloatVar;

import org.jacop.fz.Tables;
import org.jacop.fz.Options;
    
/**
 * 
 * The class gathers variables and array variables for default or
 * complementary search. Two methods are supported. One gathers all
 * output variables and the second one all non-introduced variables
 * and arrays.
 * 
 * @author Krzysztof Kuchcinski
 * @version 4.3
 *
 */
public class DefaultSearchVars {

    Var[] int_search_variables = new IntVar[0],
	set_search_variables = new SetVar[0],
	bool_search_variables = new BooleanVar[0];
    FloatVar[] float_search_variables = new FloatVar[0];

    Tables dictionary;
    
    /**
     * It constructs the class for collecting default and complementary search variables. 
     * @param dict tables with model variables.
     */
    public DefaultSearchVars(Tables dict) {
	this.dictionary = dict;
    }

    /**
     * It collects all output variables for search. 
     */
    void outputVars() {
	int int_varSize = 0, bool_varSize=0, set_varSize=0, float_varSize=0;

	// ==== Collect ALL OUTPUT variables ====

	// collect output integer & bool variables for search
	for (int i=0; i<dictionary.outputVariables.size(); i++)
	    if (dictionary.outputVariables.get(i) instanceof org.jacop.core.BooleanVar)
		bool_varSize++;
	    else if (dictionary.outputVariables.get(i) instanceof org.jacop.core.IntVar)
		int_varSize++;
	    else if (dictionary.outputVariables.get(i) instanceof org.jacop.set.core.SetVar)
		set_varSize++;
	    else 
		float_varSize++;
	
	for (int i=0; i<dictionary.outputArray.size(); i++)
	    if (dictionary.outputArray.get(i).getArray().length != 0)
		if (dictionary.outputArray.get(i).getArray()[0]  instanceof org.jacop.core.BooleanVar)
		    bool_varSize += dictionary.outputArray.get(i).getArray().length;
		else if (dictionary.outputArray.get(i).getArray()[0]  instanceof org.jacop.core.IntVar)
		    int_varSize += dictionary.outputArray.get(i).getArray().length;
		else if (dictionary.outputArray.get(i).getArray()[0]  instanceof org.jacop.set.core.SetVar)
		    set_varSize += dictionary.outputArray.get(i).getArray().length;
		else 
		    float_varSize += dictionary.outputArray.get(i).getArray().length;

	int_search_variables = new IntVar[int_varSize];
	bool_search_variables = new IntVar[bool_varSize];

	int bool_n=0, int_n=0;
	for (int i=0; i<dictionary.outputArray.size(); i++)
	    for (int j=0; j<dictionary.outputArray.get(i).getArray().length; j++) {
		Var v = dictionary.outputArray.get(i).getArray()[j];
		if (v  instanceof org.jacop.core.BooleanVar) 
		    bool_search_variables[bool_n++] = v;
		else if (dictionary.outputArray.get(i).getArray()[0]  instanceof org.jacop.core.IntVar)
		    int_search_variables[int_n++] = v;
	    }
	for (int i=0; i<dictionary.outputVariables.size(); i++) {
	    Var v = dictionary.outputVariables.get(i);
	    if (v  instanceof org.jacop.core.BooleanVar) 
		bool_search_variables[bool_n++] = v;
	    else if (v  instanceof org.jacop.core.IntVar) 
		int_search_variables[int_n++] = v;	     
	}
	java.util.Arrays.sort(int_search_variables, new DomainSizeComparator<Var>());

	// collect output set variables for search
	int n=0;
	set_search_variables = new SetVar[set_varSize];
	for (int i=0; i<dictionary.outputArray.size(); i++)
	    for (int j=0; j<dictionary.outputArray.get(i).getArray().length; j++)
		if (dictionary.outputArray.get(i).getArray()[0]  instanceof org.jacop.set.core.SetVar)
		    set_search_variables[n++] = dictionary.outputArray.get(i).getArray()[j];
	for (int i=0; i<dictionary.outputVariables.size(); i++)
	    if (dictionary.outputVariables.get(i) instanceof org.jacop.set.core.SetVar)
		set_search_variables[n++] = dictionary.outputVariables.get(i);

	// collect output float variables for search
	n=0;
	float_search_variables = new FloatVar[float_varSize];
	for (int i=0; i<dictionary.outputArray.size(); i++)
	    for (int j=0; j<dictionary.outputArray.get(i).getArray().length; j++)
		if (dictionary.outputArray.get(i).getArray()[0]  instanceof org.jacop.floats.core.FloatVar)
		    float_search_variables[n++] = (FloatVar)dictionary.outputArray.get(i).getArray()[j];
	for (int i=0; i<dictionary.outputVariables.size(); i++)
	    if (dictionary.outputVariables.get(i)  instanceof org.jacop.floats.core.FloatVar)
		float_search_variables[n++] = (FloatVar)dictionary.outputVariables.get(i);
	// ==== End collect output varibales ====
    }

    /**
     * It collects all variables that were identified as search
     * variables by VariablesParameters class during parsing variable
     * definitions.
     */
    void defaultVars() {
	int int_varSize = 0, bool_varSize=0, set_varSize=0, float_varSize=0;

	// collect integer & bool variables for search
	for (int i=0; i<dictionary.defaultSearchVariables.size(); i++)
	    if (dictionary.defaultSearchVariables.get(i) instanceof org.jacop.core.BooleanVar)
		bool_varSize++;
	    else
		int_varSize++;

	for (int i=0; i<dictionary.defaultSearchArrays.size(); i++)
	    if (dictionary.defaultSearchArrays.get(i).length != 0)
		if (dictionary.defaultSearchArrays.get(i)[0]  instanceof org.jacop.core.BooleanVar)
		    bool_varSize += dictionary.defaultSearchArrays.get(i).length;
		else
		    int_varSize += dictionary.defaultSearchArrays.get(i).length;


	int_search_variables = new IntVar[int_varSize];
	bool_search_variables = new IntVar[bool_varSize];

	int bool_n=0, int_n=0;
	for (int i=0; i<dictionary.defaultSearchArrays.size(); i++)
	    for (int j=0; j<dictionary.defaultSearchArrays.get(i).length; j++) {
		Var v = dictionary.defaultSearchArrays.get(i)[j];
		if (v  instanceof org.jacop.core.BooleanVar) 
		    bool_search_variables[bool_n++] = v;
		else
		    int_search_variables[int_n++] = v;
	    }
	for (int i=0; i<dictionary.defaultSearchVariables.size(); i++) {
	    Var v = dictionary.defaultSearchVariables.get(i);
	    if (v  instanceof org.jacop.core.BooleanVar) 
		bool_search_variables[bool_n++] = v;
	    else
		int_search_variables[int_n++] = v;
	}
	java.util.Arrays.sort(int_search_variables, new DomainSizeComparator<Var>());

	// collect set variables for search
	int n=0;
	int varSize = dictionary.defaultSearchSetVariables.size();
	for (int i=0; i<dictionary.defaultSearchSetArrays.size(); i++)
	    varSize += dictionary.defaultSearchSetArrays.get(i).length;

	set_search_variables = new SetVar[varSize];
	for (int i=0; i<dictionary.defaultSearchSetArrays.size(); i++)
	    for (int j=0; j<dictionary.defaultSearchSetArrays.get(i).length; j++)
		set_search_variables[n++] = dictionary.defaultSearchSetArrays.get(i)[j];
	for (int i=0; i<dictionary.defaultSearchSetVariables.size(); i++)
	    set_search_variables[n++] = dictionary.defaultSearchSetVariables.get(i);

	// collect float variables for search
	n=0;
	varSize = dictionary.defaultSearchFloatVariables.size();
	for (int i=0; i<dictionary.defaultSearchFloatArrays.size(); i++)
	    varSize += dictionary.defaultSearchFloatArrays.get(i).length;

	float_search_variables = new FloatVar[varSize];
	for (int i=0; i<dictionary.defaultSearchFloatArrays.size(); i++)
	    for (int j=0; j<dictionary.defaultSearchFloatArrays.get(i).length; j++)
		float_search_variables[n++] = (FloatVar)dictionary.defaultSearchFloatArrays.get(i)[j];
	for (int i=0; i<dictionary.defaultSearchFloatVariables.size(); i++)
	    float_search_variables[n++] = (FloatVar)dictionary.defaultSearchFloatVariables.get(i);
	// ==== End collect guessed search variables ====
    }
    
    Var[] getIntVars() {
	return int_search_variables;
    }

    Var[] getSetVars() {
	return set_search_variables;
    }

    Var[] getBoolVars() {
	return bool_search_variables;
    }

    FloatVar[] getFloatVars() {
	return float_search_variables;
    }

    public String toString() {

	StringBuffer buf = new StringBuffer();

	buf.append("%% default int search variables = array1d(1..");
	buf.append(int_search_variables.length);
	buf.append(Arrays.asList(int_search_variables));
	buf.append(")");
		   
	buf.append("%% default boolean search variables = array1d(1..");
	buf.append(bool_search_variables.length);
	buf.append(Arrays.asList(bool_search_variables));
	buf.append(")");
		   
	buf.append("%% default set search variables = array1d(1..");
	buf.append(set_search_variables.length);
	buf.append(Arrays.asList(set_search_variables));
	buf.append(")");
		   
	buf.append("%% default float search variables = array1d(1..");
	buf.append(float_search_variables.length);
	buf.append(Arrays.asList(float_search_variables));
	buf.append(")");
		   
	return buf.toString();
    }

    class DomainSizeComparator<T extends Var> implements Comparator<T> {

	DomainSizeComparator() { }

	public int compare(T o1, T o2) {
	    int v1 = o1.getSize();
	    int v2 = o2.getSize();
	    return v1 - v2;
	}
    }
}
