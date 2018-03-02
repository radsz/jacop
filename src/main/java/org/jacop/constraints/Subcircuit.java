/*
 * Subcircuit.java
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

package org.jacop.constraints;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.util.LengauerTarjan;

/**
 * Subcircuit constraint assures that all variables build a 
 * subcircuit. Value of every variable x[i] points to the next variable in 
 * the subcircuit. If a variable does not belong to a subcircuit it has value of 
 * its position, i.e., x[i] = i.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

public class Subcircuit extends Alldiff {

    static AtomicInteger idNumber = new AtomicInteger(0);

    Store store;

    boolean firstConsistencyCheck = true;

    boolean useSCC = true, useDominance = false;

    int idd = 0;

    int sccLength = 0;

    int[] val;

    Hashtable<Var, Integer> valueIndex = new Hashtable<Var, Integer>();

    int firstConsistencyLevel;

    LengauerTarjan graphDominance;


    /**
     * It constructs a circuit constraint.
     * @param list variables which must form a circuit.
     */
    public Subcircuit(IntVar[] list) {

        checkInputForNullness("list", list);
        checkInputForDuplication("list", list);

        this.numberId = idNumber.incrementAndGet();
        this.list = Arrays.copyOf(list, list.length);
	this.graphDominance = new LengauerTarjan(list.length + 1);

	this.queueIndex = 2;

        int i = 0;
        for (Var v : list)
            valueIndex.put(v, i++);

        val = new int[list.length];

	stack = new int[list.length];
	stack_pointer = 0;	

	String scc = System.getProperty("sub_circuit_scc_pruning");
	String dominance = System.getProperty("sub_circuit_dominance_pruning");
	if ( scc != null)
	    useSCC = Boolean.parseBoolean(scc);
	if ( dominance != null)
	    useDominance = Boolean.parseBoolean(dominance);
	if (useSCC == false && useDominance == false)
	    throw new java.lang.IllegalArgumentException("Wrong property configuration for Subcircuit");		
	
        setScope(list);
    }

    /**
     * It constructs a circuit constraint.
     * @param list variables which must form a circuit.
     */
    public Subcircuit(List<IntVar> list) {
        this(list.toArray(new IntVar[list.size()]));
    }


    @Override public void consistency(Store store) {

        if (firstConsistencyCheck) {
            for (int i = 0; i < list.length; i++)
                list[i].domain.in(store.level, list[i], 1, list.length);

            firstConsistencyCheck = false;
            firstConsistencyLevel = store.level;

        }

        do {

	    store.propagationHasOccurred = false;

            LinkedHashSet<IntVar> fdvs = variableQueue;
            variableQueue = new LinkedHashSet<IntVar>();

            alldifferent(store, fdvs);
	    
            if (!store.propagationHasOccurred) {

		if (useSCC)
		    sccsBasedPruning(store); // strongly connected components

		if (useDominance)
		    dominanceFilter(); // filter based on dominance of nodes

	    }
	    
        } while (store.propagationHasOccurred);
    }

    void alldifferent(Store store, LinkedHashSet<IntVar> fdvs) {

        for (IntVar changedVar : fdvs) {
            if (changedVar.singleton()) {
                for (IntVar var : list)
                    if (var != changedVar)
                        var.domain.inComplement(store.level, var, changedVar.min());
            }
        }

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

    boolean needsListPruning() {

	for (IntVar el : list) {
	    if (!(el.min() >= 1 && el.max() <= list.length))
		return true;
	}
	return false;
    }
    
    // registers the constraint in the constraint store
    @Override public void impose(Store store) {

        this.store = store;

        super.impose(store);

	if (! needsListPruning())
	    firstConsistencyCheck = false;
    }


    @Override public boolean satisfied() {

        if (grounded.value() != list.length)
            return false;

        boolean sat = super.satisfied(); // alldifferent

        if (sat) {
            // check if there are subcricuits that together cover all nodes
            sat = sccs(store) == list.length;
        }
        return sat;
    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : subcircuit([");

        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);
            if (i < list.length - 1)
                result.append(", ");
        }
        result.append("])");

        return result.toString();
    }

    // --- Strongly Connected Conmponents

    // Uses Trajan's algorithm to find strongly connected components
    // Based on the algorithm from the book
    // Robert Sedgewick, Algorithms, 1988, p. 482.

    int[] stack;  // stack for strongly connected compoents algorithm
    int stack_pointer;

    BitSet cycleVar;
    
    private void sccsBasedPruning(Store store) {

        java.util.Arrays.fill(val, 0);

        idd = 0;
	BitSet realCycle = null;
	
        for (int i = 0; i < list.length; i++) {

            sccLength = 0;

            if (val[i] == 0) {

                visit(i);

                if (sccLength == 1)
                    // the scc is of size one => it must be self-cycle
                    list[i].domain.in(store.level, list[i], i + 1, i + 1);
		// check if more than 1 sub-cycle possible
		for (int cv = cycleVar.nextSetBit(0); cv >= 0; cv = cycleVar.nextSetBit(cv + 1)) {
		    if (!list[cv].domain.contains(cv+1))
			if (realCycle != null) // second sub-cycle under creation -> wrong!
			    throw store.failException;
			else {
			    realCycle = cycleVar;
			    break;
			}
		}
	    }
        }

	if (realCycle != null && realCycle.cardinality() < list.length) {
	    // possible cycle found, the rest must be self-loop
	    for (int j = realCycle.nextClearBit(0); j < list.length; j = realCycle.nextClearBit(j + 1))
		    list[j].domain.in(store.level, list[j], j+1, j+1);
	}
    }


    private int sccs(Store store) {

        int totalNodes = 0;

        java.util.Arrays.fill(val, 0);

        idd = 0;

        for (int i = 0; i < list.length; i++) {

            sccLength = 0;

            if (val[i] == 0) {

                visit(i);

                totalNodes += sccLength;

            }
        }

        return totalNodes;
    }

    private int visit(int k) {

        idd++;
        val[k] = idd;
        int min = idd;

	// stack push
	stack[stack_pointer++] = k;

        for (ValueEnumeration e = list[k].dom().valueEnumeration(); e.hasMoreElements(); ) {

            int t = e.nextElement() - 1;

	    int m;
            if (val[t] == 0)
                m = visit(t);
            else 
                m = val[t];
            if (m < min) 
                min = m;
        }

        if (min == val[k]) {

            cycleVar = new BitSet(list.length); 
            sccLength = 0;

            int n;
            do {
		// stack pop
		n = stack[--stack_pointer];
                cycleVar.set(n);

                val[n] = list.length + 1;

                sccLength++;
            } while (n != k);
        }
	
        return min;
    }

    java.util.Random random = new java.util.Random(0);
    
    private void dominanceFilter() {
	int n = list.length;
	
	// find possible roots
	int[] possibleRoots = new int[n];
	int pr = 0;
	for (int v = 0; v < n; v++) {
	    if (! list[v].dom().contains(v+1)) {
		possibleRoots[pr++] = v;
		// break;  // find only first root
	    }
	}
	
	if (pr > 0) {
	    graphDominance(possibleRoots[random.nextInt(pr)]);
	
	    reversedGraphDominance(possibleRoots[random.nextInt(pr)]);
	}
    }
    
    private void graphDominance(int root) {

	int n = list.length;

	graphDominance.init();
	
	// create graph
	for (int v = 0; v < n; v++) {
	    for (ValueEnumeration e = list[v].dom().valueEnumeration(); e.hasMoreElements(); ) {
		int w = e.nextElement() - 1;
		if (v == root || v == w) 
		    graphDominance.addArc(n, w);
		else
		    graphDominance.addArc(v, w);
	    }
	}

	if (graphDominance.dominators(n)) {		
	    for (int v = 0; v < n; v++) {
		if (v != root)
		    for (ValueEnumeration e = list[v].domain.valueEnumeration(); e.hasMoreElements(); ) {
			int w = e.nextElement() - 1;
			if (v != w && graphDominance.dominatedBy(v, w)) {
			    // no back to dominator
			    list[v].domain.inComplement(store.level, list[v], w+1);
			    // no back loop for dominator
			    list[w].domain.inComplement(store.level, list[w], w+1);
			}
		    }
	    }
	}
	else  // root does not reach all nodes -> FAIL
	    throw store.failException;
    }

    private void reversedGraphDominance(int root) {

	int n = list.length;
	
	graphDominance.init();

	// create graph
	// int root = possibleRoots[random.nextInt(pr)];
	for (int v = 0; v < n; v++) {
	    for (ValueEnumeration e = list[v].dom().valueEnumeration(); e.hasMoreElements(); ) {
		int w = e.nextElement() - 1;
		if (w == root || v == w)
		    graphDominance.addArc(n, v);
		else 
		    graphDominance.addArc(w, v);
	    }
	}

	if (graphDominance.dominators(n)) {	    
	    for (int v = 0; v < n; v++) {
		if (v != root)
		    for (ValueEnumeration e = list[v].domain.valueEnumeration(); e.hasMoreElements(); ) {
			int w = e.nextElement() - 1;
			if (v != w && w != root && graphDominance.dominatedBy(w, v)) {
			    // no back loop to dominator
			    list[v].domain.inComplement(store.level, list[v], w+1);
			    // no self loop 
			    list[v].domain.inComplement(store.level, list[v], v+1);
			}
		    }
	    }
	}
	else  // root does not reach all nodes -> FAIL
	    throw store.failException;
    }
}
