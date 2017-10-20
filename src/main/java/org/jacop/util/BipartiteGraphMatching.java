/*
 * BipartiteGraphMatching.java
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

import java.util.Queue;
import java.util.LinkedList;
import java.util.Arrays;

/* Implementation of Hopcroft Karp algorithm for maximum matching (complexity O(e*sqrt(v)).
 * This algorithm is based on <https://en.wikipedia.org/wiki/Hopcroft–Karp_algorithm>
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */
public class BipartiteGraphMatching {

    static final int NIL = 0;
    static final int INF = Integer.MAX_VALUE;

    // m is  number of vertices on left side and n is a maximum number of vertices on right side of Bipartite Graph
    int m;
    int n;

    // array adj stores adjacents vertices of vertex 'u'. The value of u ranges from 1 to m.  0 is used for
    // dummy vertex
    int[][] adj;

    // These are arrays needed for hopcroftKarp()
    int[] pairU, pairV, dist;

    /**
     * Constructs empty data structure for Hopcroft Karp algorithm for maximum matching
     * edges can be added by addEdge method.
     *
     * @param m
     *            m is  number of vertices on left side (u)
     * @param n
     *            n is a maximum number of vertices on right side (v)
     */
    public BipartiteGraphMatching(int m, int n) {
      this.m = m;
      this.n = n;
      adj = new int[m + 1][];
    }

    /**
     * Constructs data structure for Hopcroft Karp algorithm for maximum matching.
     *
     * @param adj
     *            adjency matrix; adj stores adjacents vertices of vertex 'u'
     * @param m
     *            m is  number of vertices on left side (u)
     * @param n
     *            n is a maximum number of vertices on right side (v)
     */
    public BipartiteGraphMatching(int[][] adj, int m, int n) {

      this.m = m;
      this.n = n;

      this.adj = new int[adj.length][];
	for (int i = 0; i < adj.length; i++) {
	  this.adj[i] = new int[adj[i].length];
	  System.arraycopy(adj[i], 0, this.adj[i], 0, adj[i].length);
	}
    }

    // Returns size of maximum matching
    public int hopcroftKarp() {
        // pairU[u] stores pair of u in matching where u is a vertex on left side of Bipartite Graph.
        // If u doesn't have any pair, then pairU[u] is NIL
        pairU = new int[m + 1];

        // pairV[v] stores pair of v in matching. If v doesn't have any pair, then pairU[v] is NIL
        pairV = new int[n + 1];

        // dist[u] stores distance of left side vertices to u'in augmenting path
        dist = new int[m + 1];

        // Initialize NIL as pair of all vertices
        Arrays.fill(pairU, NIL);
        Arrays.fill(pairV, NIL);

        // Initialize result
        int result = 0;

        // Keep updating the result while there is an augmenting path.
        while (bfs()) {
            // Find a free vertex
            for (int u = 1; u <= m; u++)

                // If current vertex is free and there is
                // an augmenting path from current vertex
                if (pairU[u] == NIL && dfs(u))
                    result++;
        }
        return result;
    }

    // Returns true if there is an augmenting path, else returns false
    boolean bfs() {

        Queue<Integer> Q = new LinkedList<Integer>();

        // First layer of vertices (set distance as 0)
        for (int u = 1; u <= m; u++) {
            // If this is a free vertex, add it to queue
            if (pairU[u] == NIL) {
                // u is not matched
                dist[u] = 0;
                Q.add(u);
            }

            // Else set distance as infinite so that this vertex
            // is considered next time
            else
                dist[u] = INF;
        }

        // Initialize distance to NIL as infinite
        dist[NIL] = INF;

        // Q is going to contain vertices of left side only.
        while (Q.size() > 0) {
            int u = Q.remove();

            // If this node is not NIL and can provide a shorter path to NIL
            if (dist[u] < dist[NIL]) {
                // Get all adjacent vertices of the dequeued vertex u
                for (int v : adj[u]) {
                    // If pair of v is not considered so far (v, pairV[V]) is not yet explored edge.
                    if (dist[pairV[v]] == INF) {
                        // Consider the pair and add it to queue
                        dist[pairV[v]] = dist[u] + 1;
                        // Q.push(pairV[v]);
                        Q.add(pairV[v]);
                    }
                }
            }
        }

        // If we could come back to NIL using alternating path of distinct vertices then there is an
        // augmenting path
        return dist[NIL] != INF;
    }

    // Returns true if there is an augmenting path beginning with free vertex u
    boolean dfs(int u) {
        if (u != NIL) {
            for (int v : adj[u]) {

                // Follow the distances set by BFS
                if (dist[pairV[v]] == dist[u] + 1 && 
                    // If dfs for pair of v also returns
                    // true
                    dfs(pairV[v]) == true) {
                        pairV[v] = u;
                        pairU[u] = v;
                        return true;
                    }
            }

            // If there is no augmenting path beginning with u.
            dist[u] = INF;
            return false;
        }
        return true;
    }

    // To add edge from u to v
    void addEdge(int u, int v) {
        if (adj[u] == null) {
            adj[u] = new int[1];
            adj[u][0] = v;
        } else {
            int[] tmp = new int[adj[u].length + 1];
            System.arraycopy(adj[u], 0, tmp, 0, adj[u].length);
            tmp[adj[u].length] = v; // Add u to v’s list.
            adj[u] = tmp;
        }
    }
}
