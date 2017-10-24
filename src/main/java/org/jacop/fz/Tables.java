/*
 * Tables.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package org.jacop.fz;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;

import org.jacop.floats.core.FloatVar;

/**
 *
 * This class contains information about all variables, including 
 * the variables which are used by search. 
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 *
 */
public class Tables {

    Store store;
    // IntVar zero, one;

    HashMap<Integer, IntVar> constantTable = new HashMap<Integer, IntVar>();

    // intTable keeps both int & bool (0=false, 1=true) parameters
    HashMap<String, Integer> intTable = new HashMap<String, Integer>();

    HashMap<String, Double> floatTable = new HashMap<String, Double>();

    HashMap<String, int[]> intArrayTable = new HashMap<String, int[]>(); // boolean are also stored here as 0/1 values

    HashMap<String, double[]> floatArrayTable = new HashMap<String, double[]>();

    HashMap<String, IntDomain> setTable = new HashMap<String, IntDomain>();

    HashMap<String, IntDomain[]> setArrayTable = new HashMap<String, IntDomain[]>();

    HashMap<String, IntVar> variableTable = new HashMap<String, IntVar>();

    HashMap<String, IntVar[]> variableArrayTable = new HashMap<String, IntVar[]>();

    HashMap<String, FloatVar> variableFloatTable = new HashMap<String, FloatVar>();

    HashMap<String, FloatVar[]> variableFloatArrayTable = new HashMap<String, FloatVar[]>();

    HashMap<String, SetVar> setVariableTable = new HashMap<String, SetVar>();

    HashMap<String, SetVar[]> setVariableArrayTable = new HashMap<String, SetVar[]>();

    ArrayList<Var> outputVariables = new ArrayList<Var>();

    ArrayList<OutputArrayAnnotation> outputArray = new ArrayList<OutputArrayAnnotation>();

    ArrayList<Var> defaultSearchVariables = new ArrayList<Var>();

    ArrayList<Var> defaultSearchFloatVariables = new ArrayList<Var>();

    ArrayList<Var[]> defaultSearchArrays = new ArrayList<Var[]>();

    ArrayList<Var[]> defaultSearchFloatArrays = new ArrayList<Var[]>();

    ArrayList<Var> defaultSearchSetVariables = new ArrayList<Var>();

    ArrayList<Var[]> defaultSearchSetArrays = new ArrayList<Var[]>();

    public Map<IntVar, IntVar> aliasTable = new HashMap<IntVar, IntVar>();

    int numberBoolVariables = 0;    
    
    /**
     * It constructs the storage object to store different objects, like int, array of ints, sets, ... . 
     */
    public Tables() {
    }

    public Tables(Store s) {
        this.store = s;
    }

    public IntVar getConstant(int c) {
        IntVar v = constantTable.get(c);

        if (v == null) {
            v = new IntVar(store, c, c);
            constantTable.put(c, v);
        }

        return v;
    }

    public void addAlias(IntVar b, IntVar v) {
        IntVar x = aliasTable.get(v);
        if (x == null)
            aliasTable.put(v, b);
        else
            System.err.println("%% Double int var alias for bool var");

        // System.out.println(v + " is alias of " + b);
    }

    IntVar getAlias(IntVar b) {
        IntVar v = aliasTable.get(b);
        if (v == null)
            return b;
        else
            return v;
    }

    /**
     * It adds an int parameter.
     *
     * @param ident the identity of the added int parameter.
     * @param val the value of the parameter.
     */
    public void addInt(String ident, int val) {
        intTable.put(ident, val);
    }

    /**
     * It returns an int parameter of a given identity.
     *
     * @param ident the identify of the parameter.
     * @return the int value of the specified parameter.
     */
    public int getInt(String ident) {
        Integer iVal = intTable.get(ident);
        if (iVal != null)
            return iVal.intValue();
        else {
            throw new RuntimeException("Symbol \"" + ident + "\" does not have assigned value when refered; execution aborted");
        }
    }

    /**
     * It returns an Integer parameter of a given identity.
     *
     * @param ident the identify of the parameter.
     * @return the int value of the specified parameter.
     */
    public Integer checkInt(String ident) {
        return intTable.get(ident);
    }


    /**
     * It adds an float parameter.
     *
     * @param ident the identity of the added int parameter.
     * @param val the value of the parameter.
     */
    public void addFloat(String ident, double val) {
        floatTable.put(ident, val);
    }

    /**
     * It returns an float parameter of a given identity.
     *
     * @param ident the identify of the parameter.
     * @return the double value of the specified parameter.
     */
    public double getFloat(String ident) {
        Double dVal = floatTable.get(ident);
        if (dVal != null)
            return dVal.doubleValue();
        else {
            throw new RuntimeException("Symbol \"" + ident + "\" does not have assigned value when refered; execution aborted");
        }
    }

    /**
     * It returns an Double parameter of a given identity.
     *
     * @param ident the identify of the parameter.
     * @return the Double value of the specified parameter.
     */
    public Double checkFloat(String ident) {
        return floatTable.get(ident);
    }


    /**
     * It stores an int array.
     *
     * @param ident the identity of the stored array.
     * @param array the array being stored.
     */
    public void addIntArray(String ident, int[] array) {
        // TODO, asserts to prevent multiple array being put with the same identity?
        // assert ( intArrayTable.get(ident) == null ) : "The int array with identity " + ident + " already exists ";
        intArrayTable.put(ident, array);
    }

    /**
     * It obtains the int array of the given unique identity.
     *
     * @param ident the identity of the required array.
     * @return the int array with the specified identity.
     */
    public int[] getIntArray(String ident) {
        return intArrayTable.get(ident);
    }

    /**
     * It adds a set of the given identity. 
     *
     * @param ident the identity of the set being added. 
     * @param val the set being added.
     */
    public void addSet(String ident, IntDomain val) {
        setTable.put(ident, val);
    }

    /**
     * It returns the set of the given identity.
     *
     * @param ident the identity of the searched set.
     *
     * @return the set of the given identity.
     */
    public IntDomain getSet(String ident) {
        return setTable.get(ident);
    }

    /**
     * It adds the set array to the storage. 
     *
     * @param ident the identity of the added set array.
     * @param array the array being added.
     */
    public void addSetArray(String ident, IntDomain[] array) {
        setArrayTable.put(ident, array);
    }

    /**
     *
     * It returns the set array of the given id.
     * @param ident the unique id of the looked for set array.
     * @return the set array of the given identity. 
     */
    public IntDomain[] getSetArray(String ident) {
        return setArrayTable.get(ident);
    }

    public void addFloatArray(String ident, double[] array) {
        // TODO, asserts to prevent multiple array being put with the same identity?
        // assert ( intArrayTable.get(ident) == null ) : "The int array with identity " + ident + " already exists ";
        floatArrayTable.put(ident, array);
    }

    /**
     * It obtains the int array of the given unique identity.
     *
     * @param ident the identity of the required array.
     * @return the int array with the specified identity.
     */
    public double[] getFloatArray(String ident) {
        return floatArrayTable.get(ident);
    }

    /**
     * It adds a variable with a given identity to the storage. 
     *
     * @param ident the identity of the added variable. 
     * @param var the variable being added.
     */
    public void addVariable(String ident, IntVar var) {
        variableTable.put(ident, var);
    }


    /**
     * It returns the variable of the given identity. 
     *
     * @param ident the identity of the returned variable.
     * @return the variable of the given identity.
     */
    public IntVar getVariable(String ident) {
        return getAlias(variableTable.get(ident));
    }


    /**
     * It adds a variable with a given identity to the storage. 
     *
     * @param ident the identity of the added variable. 
     * @param var the variable being added.
     */
    public void addFloatVariable(String ident, FloatVar var) {
        variableFloatTable.put(ident, var);
    }


    /**
     * It returns the variable of the given identity. 
     *
     * @param ident the identity of the returned variable.
     * @return the variable of the given identity.
     */
    public FloatVar getFloatVariable(String ident) {
        return variableFloatTable.get(ident);
    }


    /**
     * It adds a variable array to the storage.
     *
     * @param ident the identity of the added variable array.
     * @param array the array of variables being added.
     */
    public void addVariableArray(String ident, IntVar[] array) {
        variableArrayTable.put(ident, array);
    }


    /**
     * It returns the variable array of the given identity.
     *
     * @param ident the identity of the returned variable array.
     * @return the variable array of the given identity.
     */
    public IntVar[] getVariableArray(String ident) {
        IntVar[] a = variableArrayTable.get(ident);
        if (a == null) {
            int[] intA = intArrayTable.get(ident);
            if (intA != null) {
                a = new IntVar[intA.length];
                for (int i = 0; i < intA.length; i++) {
                    a[i] = getConstant(intA[i]);
                }
            } else
                return null;
        } else
            for (int i = 0; i < a.length; i++)
                a[i] = getAlias(a[i]);

        return a;
    }


    /**
     * It adds a float variable array to the storage.
     *
     * @param ident the identity of the added variable array.
     * @param array the array of variables being added.
     */
    public void addVariableFloatArray(String ident, FloatVar[] array) {
        variableFloatArrayTable.put(ident, array);
    }


    /**
     * It returns the float variable array of the given identity.
     *
     * @param ident the identity of the returned variable array.
     * @return the variable array of the given identity.
     */
    public FloatVar[] getVariableFloatArray(String ident) {
        FloatVar[] a = variableFloatArrayTable.get(ident);
        if (a == null) {
            double[] floatA = floatArrayTable.get(ident);
	    if (floatA != null) {
		a = new FloatVar[floatA.length];
		for (int i = 0; i < floatA.length; i++) {
		    a[i] = new FloatVar(store, floatA[i], floatA[i]);
		}
	    }
	    else
		throw new IllegalArgumentException("Array identifier does not exist: " + ident);
        }
        return a;
    }

    /**
     * It adds the set variable of the given identity.
     *
     * @param ident the identity of the added set variable.
     * @param var the set variable being added.
     */
    public void addSetVariable(String ident, SetVar var) {
        setVariableTable.put(ident, var);
    }


    /**
     * It returns the set variable of the given identity.
     *
     * @param ident the identity of the returned set variable.
     * @return the set variable of the given identity.
     */
    public SetVar getSetVariable(String ident) {
        return setVariableTable.get(ident);
    }

    /**
     * It stores the array of the set variables with the specified identity.
     *
     * @param ident the identity of the stored array of set variables.
     * @param array the array of set variables being added.
     */
    public void addSetVariableArray(String ident, SetVar[] array) {
        setVariableArrayTable.put(ident, array);
    }


    /**
     * It returns the array of set variables of the given identity.
     *
     * @param ident the identity of the returned array of set variables. 
     * @return the array of set variables with the given identity.
     */
    public SetVar[] getSetVariableArray(String ident) {
        SetVar[] a = (SetVar[]) setVariableArrayTable.get(ident);
        if (a == null) {
            IntDomain[] setA = setArrayTable.get(ident);
            a = new SetVar[setA.length];
            for (int i = 0; i < setA.length; i++) {
                a[i] = new SetVar(store, "", new BoundSetDomain(setA[i], setA[i]));
            }
        }
        return a;
    }


    /**
     * It adds an output variable.
     * @param v the output variable being added.
     */
    public void addOutVar(Var v) {
        outputVariables.add(v);
    }

    /**
     * It checks whether a variable is output variable.
     * @param v the variable to be checked.
     * @return true if variable is output, false otherwise
     */
    public boolean isOutput(Var v) {
        if (outputVariables.contains(v))
            return true;
        else
            for (OutputArrayAnnotation oa : outputArray)
                if (oa.contains(v))
                    return true;

        return false;
    }

    /**
     * It adds an output array annotation. 
     *
     * @param v the output array annotation being added.
     */
    public void addOutArray(OutputArrayAnnotation v) {
        outputArray.add(v);
    }

    /**
     * It adds a search variable. 
     *
     * @param v the search variable being added.
     */
    public void addSearchVar(Var v) {
        defaultSearchVariables.add(v);
    }

    /**
     * It adds a search variable. 
     *
     * @param v the search variable being added.
     */
    public void addSearchFloatVar(Var v) {
        defaultSearchFloatVariables.add(v);
    }

    /**
     * It adds a search array.
     * @param v the search array being added.
     */
    public void addSearchArray(Var[] v) {
        defaultSearchArrays.add(v);
    }

    /**
     * It adds a search array.
     * @param v the search array being added.
     */
    public void addSearchFloatArray(Var[] v) {
        defaultSearchFloatArrays.add(v);
    }

    /**
     * It adds a search set variable. 
     *
     * @param v the set search variable being added.
     */
    public void addSearchSetVar(Var v) {
        defaultSearchSetVariables.add(v);
    }

    /**
     * It adds an array of search set variables.
     * @param v array of set variables being  added
     */
    public void addSearchSetArray(Var[] v) {
        defaultSearchSetArrays.add(v);
    }

    public void setNumberBoolVariables(int n) {
	numberBoolVariables = n;
    }

    public int getNumberBoolVariables() {
	return numberBoolVariables;
    }

    // StringBuilder to be used instead of normal string additions. 

    @SuppressWarnings("unchecked") public String toString() {

        Map[] dictionary = {intTable,   // 0
            intArrayTable,  // 1
            setTable,       // 2
            setArrayTable,  // 3
            variableTable,  // 4
            variableArrayTable,  // 5
            setVariableTable,    // 6
            setVariableArrayTable,  // 7
            floatArrayTable,        // 8
            floatTable,             // 9
            variableFloatTable,     // 10
            variableFloatArrayTable,  // 11
            constantTable,   //12
            aliasTable // 13
        };

        int indexIntArray = 1;
        int indexSetArray = 3;
        int indexVariableArray = 5;
        int indexSetVariableArray = 7;
        int indexFloatArray = 8;
        // int indexFloat = 9;
        int indexFloatVariableArray = 11;
        int indexConstantTable = 12;
        // int indexAliasTable = 13;

        String[] tableNames = {"int",   // 0
            "int arrays",  // 1
            "set",       // 2
            "set arrays",  // 3
            "IntVar",  // 4
            "IntVar Arrays",  // 5
            "SetVar",    // 6
            "SetVar arrays",  // 7
            "float arrays",        // 8
            "float",             // 9
            "FloatVar",     // 10
            "FloatVar arrays",  // 11
            "Constant table", //12
            "Alias table" // 13
        };

        StringBuffer s = new StringBuffer();
        for (int i = 0; i < dictionary.length; i++) {

            // int array || float array
            if (i == indexIntArray) {
	        s.append(tableNames[i] + "\n");
                s.append("{");
                java.util.Set<String> keys = dictionary[i].keySet();
                for (String k : keys) {
                    int[] a = (int[]) dictionary[i].get(k);
                    s.append(k + "=[");
                    for (int j = 0; j < a.length; j++) {
		        s.append(a[j]);
                        if (j < a.length - 1)
			    s.append(", ");
                    }
                    s.append("], ");
                }
                s.append("}\n");
            }
            // float array
            else if (i == indexFloatArray) {
	        s.append(tableNames[i] + "\n");
                s.append("{");
                java.util.Set<String> keys = dictionary[i].keySet();
                for (String k : keys) {
                    double[] a = (double[]) dictionary[i].get(k);
                    s.append(k + "=[");
                    for (int j = 0; j < a.length; j++) {
		        s.append(a[j]);
                        if (j < a.length - 1)
			    s.append(", ");
                    }
                    s.append("], ");
                }
                s.append("}\n");
            }
            // Set Array
            else if (i == indexSetArray) {
	        s.append(tableNames[i] + "\n");
                s.append("{");
                java.util.Set<String> keys = dictionary[i].keySet();
                for (String k : keys) {
		    s.append(k + "=");
                    IntDomain[] a = (IntDomain[]) dictionary[i].get(k);
                    s.append(Arrays.asList(a));
                    s.append(", ");
                }
                s.append("}\n");
            }
            // Variable Array (IntVar, FloatVar, SetVar)
            else if (i == indexVariableArray || i == indexFloatVariableArray || i == indexSetVariableArray) {
	        s.append(tableNames[i] + "\n");
                s.append("{");
                java.util.Set<String> keys = dictionary[i].keySet();
                for (String k : keys) {
                    Var[] a = (Var[]) dictionary[i].get(k);
                    s.append(k + "=");
                    s.append(Arrays.asList(a));
                    s.append(", ");
                }
                s.append("}\n");
            } else if (i == indexConstantTable) {
	        s.append(tableNames[i] + "\n");
                s.append("{");
                java.util.Set<Integer> keys = dictionary[i].keySet();
                for (Integer k : keys) {
                    Var a = (Var) dictionary[i].get(k);
                    s.append(a);
                    s.append(", ");
                }
                s.append("}\n");
            } else {
	        s.append(tableNames[i] + " (" + dictionary[i].size() + ")\n");
                s.append(dictionary[i] + "\n");
            }
        }

        s.append("Output variables = " + outputVariables + "\n");
        s.append("Output arrays = [");
        for (int i = 0; i < outputArray.size(); i++) {
            OutputArrayAnnotation a = outputArray.get(i);
            s.append(a);
            s.append(", ");
        }
	s.append("]\n");
	s.append("Search int variables = " + defaultSearchVariables + "\n");
        s.append("Search int variable arrays = [");
        for (int i = 0; i < defaultSearchArrays.size(); i++) {
            Var[] a = defaultSearchArrays.get(i);
            s.append(Arrays.asList(a));
            s.append(", ");
        }
        s.append("]\n");
        s.append("Search float variables = " + defaultSearchFloatVariables + "\n");
        s.append("Search float variables arrays = [");
        for (int i = 0; i < defaultSearchFloatArrays.size(); i++) {
            Var[] a = defaultSearchFloatArrays.get(i);
            s.append(Arrays.asList(a));
            s.append(", ");
        }
        s.append("]\n");
        s.append("Search set variables = " + defaultSearchSetVariables + "\n");
        s.append("Search set arrays = [");
        for (int i = 0; i < defaultSearchSetArrays.size(); i++) {
            Var[] a = defaultSearchSetArrays.get(i);
            s.append(Arrays.asList(a));
            s.append(", ");
        }
        s.append("]\n");
        return s.toString();
    }
}
