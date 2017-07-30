/**
 * SimpleTable.java
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

import java.util.Map;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.core.Store;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.core.IntDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.constraints.Constraint;
import org.jacop.core.TimeStamp;
import org.jacop.api.UsesQueueVariable;

/**
 * SimpleTable implements the table constraint using a method presented in
 * <p>
 * "Compact-Table: Efficient Filtering Table Constraints with Reversible Sparse Bit-Sets" Jordan Demeulenaere, Renaud Hartert, Christophe Lecoutre,
 * Guillaume Perez, Laurent Perron, Jean-Charles Régin, Pierre Schaus. Proc. International Conference on Principles and Practice of Constraint
 * Programming, CP 2016. pp 207-223
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class SimpleTable extends Constraint implements UsesQueueVariable {

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
     * Main data structure for the constraint
     */
    TimeStamp<Long> words;
    long mask;

    /**
     *
     */
    HashMap<IntVar, Integer> varMap = new HashMap<IntVar, Integer>();

    /**
     * Data specifying support tuples for each variable; static structure created once when constraint is posed.
     */
    Map<Integer, Long>[] supports;

    HashSet<IntVar> variableQueue = new LinkedHashSet<IntVar>();

    private int stamp = 0;

    int noNoGround;

    static AtomicInteger idNumber = new AtomicInteger(0);

    static final boolean debug = false;

    /**
     * It constructs a table constraint.
     *
     * @param list   the variables in the scope of the constraint.
     * @param tuples the tuples which define alloed values.
     */
    public SimpleTable(IntVar[] list, int[][] tuples) {

        if (tuples.length > 64)
            throw new IllegalArgumentException("\nSimpleTable: number of tuples must be <= 64; is " + tuples.length);

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
                throw new IllegalArgumentException("\nSimpleTable: tuples are not of the same size");
        }

        numberId = idNumber.incrementAndGet();

        this.queueIndex = 1;

        setScope(list);

    }

    @SuppressWarnings("unchecked") void init() {
        supports = new HashMap[x.length];
        int n = tuple.length;

        long wrds = 0;
        for (int i = 0; i < x.length; i++) {
            supports[i] = new HashMap<Integer, Long>();
            for (int j = 0; j < n; j++) {
                int v = tuple[j][i];
                if (validTuple(j)) {
                    wrds |= (1L << j);
                    if (supports[i].containsKey(v)) {
                        long bs = supports[i].get(v);
                        bs |= (1L << j);
                        supports[i].put(v, bs);
                    } else {
                        long bs = (1L << j);
                        supports[i].put(v, bs);
                    }
                }
            }
        }
        words = new TimeStamp<Long>(store, wrds);
    }

    boolean validTuple(int index) {

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
        int level = store.level;

        // store.registerRemoveLevelLateListener(this);

        super.impose(store);
        arguments().stream().forEach( i -> queueVariable(store.level, i));

        init();
    }

    @Override public void consistency(Store store) {

        do {

            store.propagationHasOccurred = false;

            HashSet<IntVar> fdvs = variableQueue;
            variableQueue = new LinkedHashSet<IntVar>();

            updateTable(fdvs);
            filterDomains();

        } while (store.propagationHasOccurred);

        if (noNoGround == 1)
            removeConstraint();

    }

    void updateTable(HashSet<IntVar> fdvs) {

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

            mask = 0;  // clear mask
            int xIndex = varMap.get(v);

            Map<Integer, Long> xSupport = supports[xIndex];
            if (delta < cd.getSize()) { // incremental update
                ValueEnumeration e = rp.valueEnumeration();
                while (e.hasMoreElements()) {
                    Long bs = xSupport.get(e.nextElement());
                    if (bs != null)
                        mask |= (bs.longValue());
                }
                mask = ~mask;
            } else { // reset-based update
                ValueEnumeration e = cd.valueEnumeration();
                while (e.hasMoreElements()) {
                    Long bs = xSupport.get(e.nextElement());
                    if (bs != null)
                        mask |= (bs.longValue());
                }
            }

            boolean empty = intersectWithMask();
            if (empty)
                throw store.failException;
        }
    }

    boolean intersectWithMask() {
        long w = words.value();
        long wOriginal = w;

        w &= mask;

        if (w != wOriginal)
            words.update(w);

        return w == 0;  // empty
    }

    void filterDomains() {

        noNoGround = 0;
        long wrds = words.value();
        for (int i = 0; i < x.length; i++) {
            IntVar xi = x[i];
            boolean xiSingleton = xi.singleton();
            if (!xiSingleton)
                noNoGround++;

            // check only for not assign variables and variables that become single value at this store level
            if (!xiSingleton || (xiSingleton && xi.dom().stamp() == store.level)) {

                Map<Integer, Long> xSupport = supports[i];
                ValueEnumeration e = xi.dom().valueEnumeration();
                while (e.hasMoreElements()) {
                    int el = e.nextElement();

                    Long bs = xSupport.get(el);
                    if (bs != null) {
                        if ((wrds & bs.longValue()) == 0L) {
                            xi.domain.inComplement(store.level, xi, el);
                        }
                    } else
                        xi.domain.inComplement(store.level, xi, el);
                }
            }
        }
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

    @Override public String toString() {

        StringBuffer s = new StringBuffer(id());

        s.append(" : simpleTable(");
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
            s.append("\n0:" + String.format("0x%08X", words.value()));

            s.append("\nsupports: [");
            for (int i = 0; i < supports.length; i++) {
                s.append(i + ": {");
                Map<Integer, Long> supi = supports[i];
                for (Map.Entry<Integer, Long> e : supi.entrySet()) {
                    s.append(" " + e.getKey() + "= [");
                    Long mask = e.getValue();
                    s.append(String.format("0x%08X", mask.longValue()) + " ");
                    s.append("]");
                }
                s.append("} ");
            }
            s.append("]");

        }
        return s.toString();
    }
}
