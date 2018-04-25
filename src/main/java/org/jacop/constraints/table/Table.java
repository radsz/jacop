/*
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

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.api.Stateful;
import org.jacop.core.Store;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.core.IntDomain;
import org.jacop.core.IntervalDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.constraints.Constraint;
import org.jacop.api.UsesQueueVariable;

/**
 * Table implements the table constraint using a method presented in
 * <p>
 * "Compact-Table: Efficient Filtering Table Constraints with Reversible Sparse Bit-Sets" Jordan Demeulenaere, Renaud Hartert, Christophe Lecoutre,
 * Guillaume Perez, Laurent Perron, Jean-Charles Régin, Pierre Schaus. Proc. International Conference on Principles and Practice of Constraint
 * Programming, CP 2016. pp 207-223
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class Table extends Constraint implements UsesQueueVariable, Stateful {

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
    Map<IntVar, Integer> varMap;

    /**
     * Main data structure for the constraint
     */
    ReversibleSparseBitSet rbs;

    /**
     * Data specifying support tuples for each variable; static structure created once when constraint is posed.
     */
    Map<Integer, long[]>[] supports;

    Map<Integer, Integer>[] residues;

    Set<IntVar> variableQueue = new HashSet<IntVar>();

    int noNoGround;

    static AtomicInteger idNumber = new AtomicInteger(0);

    static final boolean debug = false;

    /**
     * It constructs a table constraint.
     *
     * @param list   the variables in the scope of the constraint.
     * @param tuples the tuples which define alloed values.
     */
    public Table(IntVar[] list, int[][] tuples) {
        this(list, tuples, false);
    }

    /**
     * It constructs a table constraint.
     *
     * @param list   the variables in the scope of the constraint.
     * @param tuples the tuples which define alloed values.
     * @param reuseTuplesArgument specifies if the table of tuples should be used directly without copying.
     */
    public Table(IntVar[] list, int[][] tuples, boolean reuseTuplesArgument) {

        checkInputForNullness(new String[]{"list", "tuples"}, new Object[][]{list, tuples});
        checkInputForDuplication("list", list);
        checkInput(tuples, i -> i.length == list.length, "tuple need to have the same size as list argument.");

        this.x = Arrays.copyOf(list, list.length);
        this.varMap = Var.positionMapping(list, false, this.getClass());

        if (reuseTuplesArgument) {
            this.tuple = tuples;
        }
        else {
	    // create tuples for the constraint; remove non feasible tuples
	    int size = list.length;
	    boolean[] tuplesToRemove = new boolean[tuples.length];
	    int n=0;
	    for (int i = 0; i < tuples.length; i++) {
		for (int j = 0; j < size; j++) {
		    if (! list[j].domain.contains(tuples[i][j])) {
			tuplesToRemove[i] = true;
		    }
		}
		if (tuplesToRemove[i])
		    n++;
	    }
	    int k = tuples.length-n;
	    this.tuple = new int[k][size];
	    int m = 0;
	    for (int i = 0; i < tuples.length; i++) {
		if (! tuplesToRemove[i]) {
		    this.tuple[m] = Arrays.copyOf(tuples[i], size);
		    m++;
		}
	    }
        }

        numberId = idNumber.incrementAndGet();

        this.queueIndex = 1;

        setScope(list);

    }


    @SuppressWarnings("unchecked") long[] makeSupportAndWords(int nw) {
        supports = new HashMap[x.length];
        residues = new HashMap[x.length];
        int n = tuple.length;

        long[] words = new long[nw];
        for (int i = 0; i < x.length; i++) {
            supports[i] = new HashMap<Integer, long[]>();
            residues[i] = new HashMap<Integer, Integer>();
            for (int j = 0; j < n; j++) {
                int v = tuple[j][i];
                if (validTuple(j)) {
                    residues[i].put(v, 0);  // initialize last found support to 0
                    setBit(j, words);       // initialize words for ReversibleSparseBitSet

                    if (supports[i].containsKey(v)) {
                        long[] bs = supports[i].get(v);
                        setBit(j, bs);
                        supports[i].put(v, bs);
                    } else {
                        long[] bs = new long[nw];
                        setBit(j, bs);
                        supports[i].put(v, bs);
                    }
                }
            }
        }
        return words;
    }

    private void setBit(int n, long[] a) {

        int l = n % 64;
        int m = n / 64;
        a[m] |= (1L << l);

    }

    private boolean validTuple(int index) {

        int[] t = tuple[index];
        int n = t.length;
        int i = 0;
        while (i < n) {
            if (!x[i].dom().contains(t[i]))
                return false;
            i++;
        }
        return true;
    }


    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public void impose(Store store) {

        this.store = store;
        super.impose(store);

        int n = tuple.length;
        int lastWordSize = n % 64;
        int numberBitSets = n / 64 + ((lastWordSize != 0) ? 1 : 0);

        rbs = new ReversibleSparseBitSet();

        long[] words = makeSupportAndWords(numberBitSets);

        rbs.init(this.store, words);

    }

    @Override public void consistency(Store store) {

        do {

            store.propagationHasOccurred = false;

            Set<IntVar> fdvs = variableQueue;
            variableQueue = new HashSet<IntVar>();


            updateTable(fdvs);
            filterDomains();

        } while (store.propagationHasOccurred);

        if (noNoGround == 1)
            removeConstraint();

    }

    void updateTable(Set<IntVar> fdvs) {

        for (IntVar v : fdvs) {

            // recent pruning
            IntDomain cd = v.dom();
            IntDomain pd = cd.getPreviousDomain();
            IntDomain rp;
            int delta;
            if (pd == null) {
                rp = cd;
                delta = cd.getSize();
            } else {
                rp = pd.subtract(cd);
                delta = rp.getSize();
                if (delta == 0)
                    continue;
            }

            rbs.clearMask();
            int xIndex = varMap.get(v);

            Map<Integer, long[]> xSupport = supports[xIndex];
	    if (delta < cd.getSize()) { // incremental update
		ValueEnumeration e = rp.valueEnumeration();
		while (e.hasMoreElements()) {
		    long[] bs = xSupport.get(e.nextElement());
		    if (bs != null)
			rbs.addToMask(bs);
		}
		rbs.reverseMask();
            } else { // reset-based update
		Set<Map.Entry<Integer, long[]>> xsEntry = xSupport.entrySet();
		if (cd.getSize() < xsEntry.size()) {
		    // update based on the variable
		    ValueEnumeration e = cd.valueEnumeration();
		    while (e.hasMoreElements()) {
			long[] bs = xSupport.get(e.nextElement());
			if (bs != null)
			    rbs.addToMask(bs);
		    }
		}
		else {
		    // updates based on table values
		    for (Map.Entry<Integer, long[]> e : xsEntry) {
			Integer val = e.getKey();
			long[] bits = e.getValue();
			if (cd.contains(val))
			    rbs.addToMask(bits);
		    }
		}
	    }

            rbs.intersectWithMask();
            if (rbs.isEmpty())
                throw store.failException;
        }
    }

    void filterDomains() {

        noNoGround = 0;
        long[] wrds = rbs.words.value();
        for (int i = 0; i < x.length; i++) {
            IntVar xi = x[i];
            boolean xiSingleton = xi.singleton();
            if (!xiSingleton)
                noNoGround++;

            // check only for not assign variables and variables that become single value at this store level
            if (!xiSingleton || (xiSingleton && xi.dom().stamp() == store.level)) {

                Map<Integer, long[]> xSupport = supports[i];

		Set<Map.Entry<Integer, long[]>> xsEntry = xSupport.entrySet();
		if (xi.dom().getSize() <= xsEntry.size()) { 		
		    // filter based on the variable
		    ValueEnumeration e = xi.dom().valueEnumeration();
		    while (e.hasMoreElements()) {
			int el = e.nextElement();

			long[] bs = xSupport.get(el);
			if (bs != null) {
			    int index = residues[i].get(el);

			    if ((wrds[index] & bs[index]) == 0L) {

				index = rbs.intersectIndex(bs);
				if (index == -1)
				    xi.domain.inComplement(store.level, xi, el);
				else
				    residues[i].put(el, index);
			    }
			} else
			    xi.domain.inComplement(store.level, xi, el);
		    }
		} else {
		    // filter based on the table values
		    IntDomain xDom = new IntervalDomain();
		    for (Map.Entry<Integer, long[]> e : xsEntry) {
			Integer el = e.getKey();
			long[] bs = e.getValue();

			if (xi.domain.contains(el) && bs != null) {
			    int index = residues[i].get(el);
			    
			    xDom.unionAdapt(el, el);

			    if ((wrds[index] & bs[index]) == 0L) {

				index = rbs.intersectIndex(bs);
				if (index == -1)
				    xi.domain.inComplement(store.level, xi, el);
				else 
				    residues[i].put(el, index);
				}
			} else
			    xi.domain.inComplement(store.level, xi, el);
		    }
		    xi.domain.in(store.level, xi, xDom);
		}
            }
        }
    }

    @Override public void queueVariable(int level, Var v) {
        variableQueue.add((IntVar) v);
    }

    public void removeLevel(int level) {
        variableQueue.clear();
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
            s.append("\n" + rbs);

            s.append("\nsupports: [");
            for (int i = 0; i < supports.length; i++) {
                s.append(i + ": {");
                Map<Integer, long[]> supi = supports[i];
                for (Map.Entry<Integer, long[]> e : supi.entrySet()) {
                    s.append(" " + e.getKey() + "= [");
                    long[] mask = e.getValue();
                    for (int j = 0; j < mask.length; j++) {
                        s.append(String.format("0x%08X", mask[j]) + " ");
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
