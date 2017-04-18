/**
 * Table.java
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


package org.jacop.constraints.table;

import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
import java.util.BitSet;
import java.util.HashSet;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.Store;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.core.IntDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.constraints.Constraint;
import java.util.Set;

/**
 * Table implements the table constraint using a method presented in 
 *
 * "Compact-Table: Efficient Filtering Table Constraints with Reversible Sparse Bit-Sets" Jordan Demeulenaere, Renaud Hartert, Christophe Lecoutre,
 * Guillaume Perez, Laurent Perron, Jean-Charles Régin, Pierre Schaus. Proc. International Conference on Principles and Practice of Constraint
 * Programming, CP 2016. pp 207-223
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class Table extends Constraint {

    Store store;

    /**
     * Variables within the scope of table constraint
     */
    public IntVar[] x;
    
    /**
     * Tuples specifying the allowed values
     */
    public int[][] tuple;

    /**
     *
     */
    HashMap<IntVar, Integer> varMap = new HashMap<IntVar, Integer>();

    /**
     * Main data structure for the constraint
     */
    ReversibleSparseBitSet rbs;

    /**
     * Data specifying support tuples for each variable; static structure created once when constraint is posed.
     */
    Map<Integer,long[]>[] supports;
    
    Map<Integer, Integer>[] residues;

    HashSet<IntVar> variableQueue = new HashSet<IntVar>();

    private int stamp = 0;
    
    static AtomicInteger idNumber = new AtomicInteger(0);

    static final boolean debug = false;

    /**
     * It constructs a table constraint.
     * @param list the variables in the scope of the constraint.
     * @param tuples the tuples which define alloed values.
     */
    public Table(IntVar[] list, int[][] tuples) {

        this.x = new IntVar[list.length];
	System.arraycopy(list, 0, x, 0, list.length);
	for (int i = 0; i < x.length; i++)
	    varMap.put(x[i], i);

	int tupleLength = tuples[0].length;
        this.tuple = new int[tuples.length][tupleLength];
	for (int i = 0; i < tuples.length; i++) {
	    if (tuples[i].length == tupleLength)
		System.arraycopy(tuples[i], 0, tuple[i], 0, tupleLength);
	    else
		throw new IllegalArgumentException("\nTable: tuples are not of the same size");
	}
	
        numberId = idNumber.incrementAndGet();

        this.queueIndex = 1;

    }

    void init() {

	int n = tuple.length;

	rbs = new ReversibleSparseBitSet(store, x, tuple);

	makeSupport();
    }

    @SuppressWarnings("unchecked")
    void makeSupport() {
	supports = new HashMap[x.length];
	residues = new HashMap[x.length];
	int n = tuple.length;
	int nw = rbs.noWords();
	
	for (int i = 0; i < x.length; i++) {	    
	    supports[i] = new HashMap<Integer,long[]>();
	    residues[i] = new HashMap<Integer, Integer>();
	    for (int j = 0; j < tuple.length; j++) {
		int v = tuple[j][i];
		if (validTuple(j))
		    residues[i].put(v, 0);  // initialize last found support to 0

		    if (supports[i].containsKey(v)) {
			long[] bs = supports[i].get(v);
			setBit(j, bs);
			supports[i].put(v, bs);
		    }
		    else {
			long[] bs = new long[nw];
			setBit(j, bs);
			supports[i].put(v, bs);
		    }
	    }
	}
    }

    long[] setBit(int n, long[] a) {

	int l = n % 64;
	int m = n / 64;
	
	a[m] |= (1L << l);
	
	return a;
    }
    
    boolean validTuple(int index) {

	int[] t = tuple[index];
	int n = t.length;
	int i=0;
	while (i < n) {
	    if (!x[i].dom().contains(t[i]))
		return false;
	    i++;
	}
	return true;
    }

    @Override public int getConsistencyPruningEvent(Var var) {
        // If consistency function mode
        if (consistencyPruningEvents != null) {
            Integer possibleEvent = consistencyPruningEvents.get(var);
            if (possibleEvent != null)
                return possibleEvent;
        }
        return IntDomain.ANY;
    }

    @Override public ArrayList<Var> arguments() {
        ArrayList<Var> result = new ArrayList<Var>();
        for (Var var : x)
            result.add(var);

        return result;
    }

    @Override public void impose(Store store) {
        this.store = store;
        int level = store.level;

        store.registerRemoveLevelListener(this);
	
        for (int i = 0; i < x.length; i++) {
            x[i].putModelConstraint(this, getConsistencyPruningEvent(x[i]));
	    queueVariable(level, x[i]);
	}
	
        store.addChanged(this);
        store.countConstraint();

	init();
    }
    
    @Override public void consistency(Store store) {

	HashSet<IntVar> fdvs = variableQueue;
	variableQueue = new HashSet<IntVar>();

	updateTable(fdvs);
	filterDomains();
    }
    
    @Override public boolean satisfied() {
        // FIXME.
        return false;
    }

    void updateTable(HashSet<IntVar> fdvs) {
	int level = store.level;

	for (IntVar v : fdvs) {
	    
	    // recent pruning	    
	    IntDomain cd = v.dom();
	    IntDomain pd = cd.previousDomain();
	    IntDomain rp;
	    int delta;
	    if (pd == null) {
		rp = cd;
		delta = IntDomain.MaxInt;
	    } else {
		rp = pd.subtract(cd);
		delta = rp.getSize();
		if (delta == 0)
		    continue;
	    }
		
	    rbs.clearMask();
	    int xIndex = varMap.get(v);

	    Map<Integer,long[]> xSupport = supports[xIndex];
	    if (delta < cd.getSize()) { // incremental update
	    	ValueEnumeration e = rp.valueEnumeration();
	    	while (e.hasMoreElements()) {
	    	    long[] bs = xSupport.get(e.nextElement());
	    	    if (bs != null)
	    		rbs.addToMask(bs);
	    	}
	    	rbs.reverseMask();
	    } else { // reset-based update
		rp = cd;
	    	ValueEnumeration e = v.dom().valueEnumeration();
	    	while (e.hasMoreElements()) {
	    	    long[] bs = xSupport.get(e.nextElement());
	    	    if (bs != null)
	    		rbs.addToMask(bs);
	    	}
	    }

	    rbs.intersectWithMask();
	    if (rbs.isEmpty()) 
	    	throw store.failException;
	}
    }

    void filterDomains() {
	for (int i = 0; i < x.length; i++) {
	    int xIndex = varMap.get(x[i]);

	    Map<Integer,long[]> xSupport = supports[xIndex];
	    ValueEnumeration e = x[i].dom().valueEnumeration();
	    while (e.hasMoreElements()) {
		int el = e.nextElement();

		Integer indexInteger = residues[i].get(el);
		if (indexInteger == null) {
		    x[i].domain.inComplement(store.level, x[i], el);
		    continue;
		}
		int index = indexInteger.intValue();

		long[] bs = xSupport.get(el);
		if (bs != null) {
		    if ((rbs.words[index].value() & xSupport.get(el)[index]) == 0L) {
			
			index = rbs.intersectIndex(bs);
			if (index == -1) 
			    x[i].domain.inComplement(store.level, x[i], el);
			else
			    residues[i].put(el, index);
		    }
		} else 
		    x[i].domain.inComplement(store.level, x[i], el);
	    }
	}
    }
    
    @Override public void increaseWeight() {
        for (Var var : x)
            var.weight++;
    }

    @Override public void queueVariable(int level, Var v) {
        if (level == stamp)
            variableQueue.add((IntVar) v);
        else {
            variableQueue.clear();
            stamp = level;
            variableQueue.add((IntVar) v);
        }
    }    

    @Override public void removeLevel(int level) {
        variableQueue.clear();
    }

    @Override public void removeConstraint() {
        for (Var var : x)
            var.removeConstraint(this);
    }

    @Override public String toString() {

	StringBuffer s = new StringBuffer(id());

        s.append(" : table(");
	s.append(java.util.Arrays.asList(x));

	s.append(", [");
	for (int i = 0; i < tuple.length; i++) {
	    s.append("[");
	    for (int j = 0; j < tuple[i].length; j++) {
		s.append(tuple[i][j]);
		if (j < tuple[i].length - 1)
		    s.append(", ");
	    }
	    s.append("]");
	    if (i < tuple.length - 1)
		s.append(", ");
	}
	s.append("])");

	if (debug) {
	    s.append("\n"+rbs);

	    s.append("\nsupports: [");
	    for (int i = 0; i < supports.length; i++) {	    
		s.append(i+": {");
		Map<Integer, long[]> supi = supports[i];
		for (Map.Entry<Integer,long[]> e : supi.entrySet()) {
		    s.append(" "+e.getKey()+"= [");
		    long[] mask = e.getValue();
		    for (int j = 0; j < mask.length; j++) {
			s.append(String.format("0x%08X", mask[j])+" ");
		    }
		    s.append("]");
		}
		s.append("} ");
	    }
	    s.append("]");

	}
	return s.toString();
    }
}
