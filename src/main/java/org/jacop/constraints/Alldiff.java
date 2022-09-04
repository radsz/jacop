/*
 * Alldiff.java
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

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;


/**
 * Alldiff constraint assures that all FDVs has different values. It uses bounds
 * consistency technique as described in the paper by Alejandro Lopez-Ortiz, Claude-Guy
 * Quimper, John Tromp, Peter van Beek, "A fast and simple algorithm for bounds
 * consistency of the alldifferent constraint", Proceedings of the 18th international
 * joint conference on Artificial intelligence (IJCAI'03), Pages 245-250. Before using
 * bounds consistency it calls consistency method for ground variables.
 * <p>
 * It extends basic functionality of Alldifferent constraint.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.9
 */

public class Alldiff extends Alldifferent {

    static AtomicInteger idNumber = new AtomicInteger(0);

    // it stores the store locally so all the private functions which
    // are part of the consistency function can throw failure exception
    // without passing store argument every time their function is called.
    Store store;

    private Comparator<Element> maxVariable = (o1, o2) -> (o1.var.max() - o2.var.max());

    private Comparator<Element> minVariable = (o1, o2) -> (o1.var.min() - o2.var.min());

    private int[] t; // holds the critical capacity pointers; that is, t[i] points to the
    // predecessor of i in the bounds list.
    private int[] d; // holds the differences between critical capacities; that is d[i] is
    // the difference of capacities between bounds[i] and its predecessor
    // element in the list bounds[t[i]].
    private int[] h; // holds the Hall interval pointers; that is, if h[i] < i then the
    // half-open interval [bounds[h[i]],bounds[i]) is contained in a Hall
    // interval, and otherwise holds a pointer to the Hall interval it
    // belongs to. This Hall interval is represented by a tree, with the
    // root containing the value of its right end.
    private int[] bounds; // is a sorted array of all min’s and max’s.

    private int nb; // holds the number of unique bounds.

    private Element[] minsorted, maxsorted;

    protected Alldiff() {
    }

    /**
     * It constructs the alldiff constraint for the supplied variable.
     *
     * @param variables variables which are constrained to take different values.
     */
    public Alldiff(IntVar[] variables) {

        checkInputForNullness("x", variables);

        this.numberId = idNumber.incrementAndGet();
        this.list = Arrays.copyOf(variables, variables.length);
        this.queueIndex = 2;

        int n = list.length;
        t = new int[2 * n + 2];
        d = new int[2 * n + 2];
        h = new int[2 * n + 2];
        bounds = new int[2 * n + 2];

        minsorted = new Element[n];
        maxsorted = new Element[n];
        for (int i = 0; i < n; i++) {
            Element el = new Element();
            el.var = list[i];
            minsorted[i] = el;
            maxsorted[i] = el;
        }

        setScope(variables);

    }


    /**
     * It constructs the alldiff constraint for the supplied variable.
     *
     * @param variables variables which are constrained to take different values.
     */
    public Alldiff(List<? extends IntVar> variables) {
        this(variables.toArray(new IntVar[variables.size()]));
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public void impose(Store store) {

        if (list.length == 0)
            return;

        super.impose(store);
        this.store = store;

    }

    @Override public void consistency(Store store) {

        if (store.currentQueue == queueIndex) {

	    int groundPos = grounded.value();
            while (!variableQueue.isEmpty()) {

                LinkedHashSet<IntVar> fdvs = variableQueue;
                variableQueue = new LinkedHashSet<>();

                for (IntVar Q : fdvs)
                    if (Q.singleton()) {
                        int qPos = positionMapping.get(Q);
                        if (qPos > groundPos) {
                            list[qPos] = list[groundPos];
                            list[groundPos] = Q;
                            positionMapping.put(Q, groundPos);
                            positionMapping.put(list[qPos], qPos);
			    groundPos++;
                            for (int i = groundPos; i < list.length; i++)
                                list[i].domain.inComplement(store.level, list[i], Q.min());
                        } else if (qPos == groundPos) {
			    groundPos++;
                            for (int i = groundPos; i < list.length; i++)
                                list[i].domain.inComplement(store.level, list[i], Q.min());
                        }
                    }
            }
	    grounded.update(groundPos);

            if (queueIndex + 1 < store.queueNo) {
                store.changed[queueIndex + 1].add(this);
                return;
            }

        }

        // do {
        // store.propagationHasOccurred = false;

        init();
        updateLB();
        updateUB();

        // } while (store.propagationHasOccurred);
    }

    private void init() {
        int n = list.length;
        Arrays.sort(minsorted, 0, n, minVariable);
        Arrays.sort(maxsorted, 0, n, maxVariable);

        int min = minsorted[0].var.min();
        int max = maxsorted[0].var.max() + 1;
        int last = min - 2;
        int nb = 0;
        bounds[0] = last;
        int i = 0, j = 0;
        while (true) {
            if (i < n && min <= max) {
                if (min != last)
                    bounds[++nb] = last = min;

                minsorted[i].minrank = nb;
                if (++i < n)
                    min = minsorted[i].var.min();

            } else {
                if (max != last)
                    bounds[++nb] = last = max;

                maxsorted[j].maxrank = nb;
                if (++j == n)
                    break;

                max = maxsorted[j].var.max() + 1;
            }
        }
        this.nb = nb;
        bounds[nb + 1] = bounds[nb] + 2;
    }

    private void updateLB() {

        for (int i = 1; i <= nb + 1; i++) {
            t[i] = h[i] = i - 1;
            d[i] = bounds[i] - bounds[i - 1];
        }
        for (int i = 0; i < this.list.length; i++) {
            int x = maxsorted[i].minrank;
            int y = maxsorted[i].maxrank;
            int z = pathmax(t, x + 1);
            int j = t[z];

            if (--d[z] == 0) {
                t[z] = z + 1;
                z = pathmax(t, t[z]);
                t[z] = j;
            }
            pathset(t, x + 1, z, z);
            if (d[z] < bounds[z] - bounds[y]) {
                throw store.failException;
            }
            if (h[x] > x) {
                int w = pathmax(h, h[x]);
                maxsorted[i].var.domain.inMin(store.level, maxsorted[i].var, bounds[w]);
                pathset(h, x, w, w);
            }
            if (d[z] == bounds[z] - bounds[y]) {
                pathset(h, h[y], j - 1, y);
                h[y] = j - 1;
            }
        }
    }

    private void updateUB() {

        for (int i = 0; i <= nb; i++) {
            t[i] = h[i] = i + 1;
            d[i] = bounds[i + 1] - bounds[i];
        }
        for (int i = this.list.length - 1; i >= 0; i--) {
            int x = minsorted[i].maxrank;
            int y = minsorted[i].minrank;
            int z = pathmin(t, x - 1);
            int j = t[z];
            if (--d[z] == 0) {
                t[z] = z - 1;
                z = pathmin(t, t[z]);
                t[z] = j;
            }
            pathset(t, x - 1, z, z);
            if (d[z] < bounds[y] - bounds[z]) {
                throw store.failException;
            }
            if (h[x] < x) {
                int w = pathmin(h, h[x]);
                minsorted[i].var.domain.inMax(store.level, minsorted[i].var, bounds[w] - 1);
                pathset(h, x, w, w);
            }
            if (d[z] == bounds[y] - bounds[z]) {
                pathset(h, h[y], j + 1, y);
                h[y] = j + 1;
            }
        }
    }

    private void pathset(int[] v, int start, int end, int to) {
        int next = start;
        int prev = next;
        while (prev != end) {
            next = v[prev];
            v[prev] = to;
            prev = next;
        }
    }

    private int pathmin(int[] v, int i) {
        while (v[i] < i)
            i = v[i];

        return i;
    }

    private int pathmax(int[] v, int i) {
        while (v[i] > i)
            i = v[i];

        return i;
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());
        result.append(" : Alldiff([");

        for (int i = 0; i < list.length; i++) {
            result.append(list[i]);
            if (i < list.length - 1)
                result.append(", ");
        }

        result.append("])");

        return result.toString();

    }

    // Overwritten as QueueForwardQueue checks that constraint has declared this method.
    @Override public void queueVariable(int level, Var var) {
        super.queueVariable(level, var);
    }

    private static class Element {
        private IntVar var;
        private int minrank, maxrank;
    }

}

