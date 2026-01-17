/**
 * SimpleHashSet.java
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

package org.jacop.util;

/*
 * The implementation of the algorithm for finding dominators (sophisticated version) in a directed graph based on 
 * Lengauer and Tarjan algorithm based on paper "A Fast Algorithm for Finding Dominators in a Flowgraph", 
 * ACM Trans. on Programming Languages and Systems, vol. 1, no. 1, July 1979.
 */
public class SophisticatedLengauerTarjan extends LengauerTarjan {


    int[] child;
    int[] size;

    public SophisticatedLengauerTarjan(int n) {
        super(n);

        child = new int[n];
        size = new int[n];
        for (int i = 0; i < n; i++) {
            child[i] = 0;
            size[i] = 1;
        }
    }

    private int eval(int v) {
        if (ancestor[v] == NIL)
            return label[v];
        else {
            compress(v);
            return semi[label[ancestor[v]]] >= semi[label[v]] ? label[v] : label[ancestor[v]];
        }
    }

    private void link(int v, int w) {

        int s = w;

        while (semi[label[w]] < semi[label[child[s]]]) {
            if (size[s] + size[child[child[s]]] >= 2 * size[child[s]]) {
                // small child case
                ancestor[child[s]] = s;
                child[s] = child[child[s]];
            } else {
                // big child case
                size[child[s]] = size[s];
                s = ancestor[s] = child[s];
            }
        }
        label[s] = label[w];
        size[v] = size[v] + size[w];

        if (size[v] < 2 * size[w]) {
            int t = s;
            s = child[v];
            child[v] = t;
        }

        while (s >= 0) {
            ancestor[s] = v;
            s = child[s];
        }
    }

}
