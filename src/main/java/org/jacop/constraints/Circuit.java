/*
 * Circuit.java
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

import org.jacop.api.Stateful;
import org.jacop.core.*;

import java.util.Arrays;
import java.util.Hashtable;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.util.SophisticatedLengauerTarjan;


/**
 * Circuit constraint assures that all variables build a Hamiltonian
 * circuit. Value of every variable x[i] points to the next variable in
 * the circuit. Variables create one circuit.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */

public class Circuit extends Alldiff implements Stateful {

    int chainLength = 0;

    boolean firstConsistencyCheck = true;

    MutableVar graph[];

    int idd = 0;

    int sccLength = 0;

    int[] val;

    static AtomicInteger idNumber = new AtomicInteger(0);

    Hashtable<Var, Integer> valueIndex = new Hashtable<Var, Integer>();

    int firstConsistencyLevel;

    SophisticatedLengauerTarjan graphDominance;

    /**
     * It constructs a circuit constraint.
     *
     * @param list variables which must form a circuit.
     */
    public Circuit(IntVar[] list) {

        checkInputForNullness("list", list);
        checkInputForDuplication("list", list);

        this.numberId = idNumber.incrementAndGet();
        this.list = Arrays.copyOf(list, list.length);
        this.graphDominance = new SophisticatedLengauerTarjan(list.length + 1);

        this.queueIndex = 2;

        int i = 0;
        for (Var v : list)
            valueIndex.put(v, i++);

        val = new int[list.length];

        setScope(list);
    }

    /**
     * It constructs a circuit constraint.
     *
     * @param list variables which must form a circuit.
     */
    public Circuit(List<IntVar> list) {
        this(list.toArray(new IntVar[list.size()]));
    }


    @Override public void consistency(Store store) {

        if (firstConsistencyCheck) {
            for (int i = 0; i < list.length; i++) {
                list[i].domain.in(store.level, list[i], 1, list.length);
                list[i].domain.inComplement(store.level, list[i], i + 1);
            }
            firstConsistencyCheck = false;
            firstConsistencyLevel = store.level;
        }

        do {

            store.propagationHasOccurred = false;

            LinkedHashSet<IntVar> fdvs = variableQueue;
            variableQueue = new LinkedHashSet<IntVar>();

            alldifferent(store, fdvs);

            oneCircuit(store, fdvs);

        } while (store.propagationHasOccurred);

        sccs(store); // strongly connected components

	/**
	 * dominance-based filtering improves pruning but it is rather
	 * expensive in execution time
	 */
	// dominanceFilter(); // filter based on dominance of nodes

        // if (store.propagationHasOccurred)
        //     store.addChanged(this);

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

    int firstNode(int current) {
        int start = current;
        int first;
        do {
            first = ((CircuitVarValue) graph[current - 1].value()).previous;
            if (first != 0 && first != start) {
                current = first;
                chainLength++;
            }
        } while (first != 0 && first != start);
        return current;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    // registers the constraint in the constraint store
    @Override public void impose(Store store) {

        super.impose(store);

        graph = new CircuitVar[list.length];
        for (int j = 0; j < graph.length; j++)
            graph[j] = new CircuitVar(store, 0, 0);

    }

    int lastNode(Store store, int current) {
        int start = current;
        int last;
        do {
            last = ((CircuitVarValue) graph[current - 1].value()).next;
            if (last != 0) {
                current = last;
                if (++chainLength > graph.length)
                    throw Store.failException;
            }
        } while (last != 0 && last != start);
        if (last == current)
            chainLength = 0;
        return current;
    }

    void oneCircuit(Store store, LinkedHashSet<IntVar> fdvs) {

        IntDomain dom;

        for (IntVar var : fdvs) {
            dom = var.dom();
            if (dom.singleton()) {
                updateChains(var);
                int Qmin = dom.min();

                chainLength = 0;
                int lastInChain = lastNode(store, Qmin);
                int firstInChain = firstNode(Qmin);
                if (chainLength < list.length - 1) {
                    list[lastInChain - 1].domain.inComplement(store.level, list[lastInChain - 1], firstInChain);
                }

            }
        }
    }


    // @todo, what if there is a small circuit ending with zero, it is not consistent but can be satisfied.
    // redesign satisfied function since the implementation of alldiff has changed.
    @Override public boolean satisfied() {

        if (grounded.value() != list.length)
            return false;

        boolean sat = super.satisfied(); // alldifferent

        if (sat) {
            int i = 0;
            int no = 0;
            do {
                i = list[i].min() - 1;
                no++;
            } while (no < list.length && i != 0);
            if (no != list.length || i != 0)
                return false;
        }
        return sat;
    }

    void sccs(Store store) {

        for (int i = 0; i < val.length; i++)
            val[i] = 0;
        idd = 0;

        sccLength = 0;
        visit(0);

    }

    // --- Strongly Connected Conmponents

    // Uses Trajan's algorithm to find strongly connected components
    // if found strongly connected component is shorter than the
    // Hamiltonian circuit length fail is enforced (one is unable to
    // to build a circuit. Based on the algorithm from the book
    // Robert Sedgewick, Algorithms, 1988, p. 482.

    @Override public String toString() {

        StringBuffer result = new StringBuffer(id());
        result.append(" : circuit([");

        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);
            if (i < list.length - 1)
                result.append(", ");
        }
        result.append("])");

        return result.toString();
    }

    @Override public void removeLevel(int level) {
        if (firstConsistencyLevel == level)
            firstConsistencyCheck = true;
    }

    // --- Strongly Connected Conmponents

    void updateChains(IntVar v) {

        int i = valueIndex.get(v);
        int vMin = v.min();

        graph[i].update(new CircuitVarValue(vMin, ((CircuitVarValue) graph[i].value()).previous));
        int j = vMin;
        graph[j - 1].update(new CircuitVarValue(((CircuitVarValue) graph[j - 1].value()).next, i + 1));
    }

    int visit(int k) {

        int m, min = 0, t;
        idd++;
        val[k] = idd;
        min = idd;
        sccLength++;
        for (ValueEnumeration e = list[k].dom().valueEnumeration(); e.hasMoreElements(); ) {
            t = e.nextElement() - 1;
            if (val[t] == 0)
                m = visit(t);
            else
                m = val[t];
            if (m < min)
                min = m;
        }
        if (min == val[k]) {
            if (sccLength != list.length && sccLength != 0) {
                // the scc is shorter than all nodes in the circuit constraints
                sccLength = 0;
                throw Store.failException;
            }
            sccLength = 0;
        }
        return min;
    }

    Random random = new Random(0);

    private void dominanceFilter() {
        int n = list.length;

	if (!graphDominance(random.nextInt(n)))
	    reversedGraphDominance(random.nextInt(n));
    }

    private boolean graphDominance(int root) {

        int n = list.length;
        boolean pruning = false;

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
                            pruning = true;
                            // no back to dominator
                            list[v].domain.inComplement(store.level, list[v], w + 1);
                            // no back loop for dominator
                            list[w].domain.inComplement(store.level, list[w], w + 1);
                        }
                    }
            }
        } else  // root does not reach all nodes -> FAIL
            throw store.failException;

        return pruning;
    }

    private boolean reversedGraphDominance(int root) {

        int n = list.length;
        boolean pruning = false;

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
                            pruning = true;
                            // no back loop to dominator
                            list[v].domain.inComplement(store.level, list[v], w + 1);
                            // no self loop
                            list[v].domain.inComplement(store.level, list[v], v + 1);
                        }
                    }
            }
        } else  // root does not reach all nodes -> FAIL
            throw store.failException;

        return pruning;
    }

}
