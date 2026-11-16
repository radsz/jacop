/*
 * ClauseSimplification.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints.lp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.core.IntVar;
import org.jacop.lcg.LinearForm;

/**
 * Simplifies the clause rows of a model over 0/1 variables before they become rows of a linear
 * relaxation: unit propagation, and the substitution of each literal by the representative of its
 * class of equivalent literals (the strongly connected components of the implication graph of the
 * binary clauses, B. Aspvall, M. F. Plass and R. E. Tarjan, "A linear-time algorithm for testing
 * the truth of certain quantified Boolean formulas", IPL 8(3), 1979). The clauses that lazy clause
 * generation takes are not propagated in the store, so a clause whose other literals unit clauses
 * make false is still long, and the binary conflicts between equivalent copies of a literal do not
 * meet in one clique: the grandtour puzzle of the SAT Competition has 354 unit clauses and 446
 * equivalences, and its at-most-one structure appears only once they are applied, as in the
 * presolve of CP-SAT.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class ClauseSimplification {

  /** The simplified clause rows, over the representatives of the free variables. */
  final List<LinearForm> rows;

  /** The variables that unit propagation fixed. */
  final int units;

  /** The variables substituted by an equivalent literal. */
  final int equivalences;

  /** Whether unit propagation or an equivalence of a literal with its negation refuted them. */
  final boolean refuted;

  private ClauseSimplification(
      List<LinearForm> rows, int units, int equivalences, boolean refuted) {
    this.rows = rows;
    this.units = units;
    this.equivalences = equivalences;
    this.refuted = refuted;
  }

  /**
   * Returns whether the row is a clause row over 0/1 variables: sum(positive) - sum(negative) >= 1
   * - |negative|.
   *
   * @param f the row
   * @return true for a clause row
   */
  static boolean isClause(LinearForm f) {
    if (f.relation() != LinearForm.GE) {
      return false;
    }
    long negative = 0;
    for (int k = 0; k < f.vars().length; k++) {
      long w = f.weights()[k];
      IntVar x = f.vars()[k];
      if (w != 1 && w != -1 || x.min() < 0 || x.max() > 1) {
        return false;
      }
      if (w == -1) {
        negative++;
      }
    }
    return f.c() == 1 - negative;
  }

  /**
   * Simplifies clause rows (see {@link #isClause}); rounds of unit propagation and equivalence
   * substitution alternate up to a fixpoint.
   *
   * @param clauses the clause rows
   * @return the simplified rows, without satisfied clauses, false literals and repeated clauses
   */
  static ClauseSimplification of(List<LinearForm> clauses) {
    Map<IntVar, Integer> column = new IdentityHashMap<>();
    List<IntVar> vars = new ArrayList<>();
    // literals: 2 j for x_j = 1, 2 j + 1 for x_j = 0
    List<int[]> cs = new ArrayList<>(clauses.size());
    for (LinearForm f : clauses) {
      int[] c = new int[f.vars().length];
      for (int k = 0; k < c.length; k++) {
        IntVar x = f.vars()[k];
        int j =
            column.computeIfAbsent(
                x,
                v -> {
                  vars.add(v);
                  return vars.size() - 1;
                });
        c[k] = f.weights()[k] > 0 ? 2 * j : 2 * j + 1;
      }
      cs.add(c);
    }
    int n = vars.size();
    // value of each variable: -1 free, 0 or 1
    int[] value = new int[n];
    for (int j = 0; j < n; j++) {
      IntVar x = vars.get(j);
      value[j] = x.singleton() ? x.value() : -1;
    }
    int units = 0;
    int equivalences = 0;
    for (int round = 0; round < 10; round++) {
      int fixed = propagate(cs, value, n);
      if (fixed < 0) {
        return new ClauseSimplification(List.of(), units, equivalences, true);
      }
      units += fixed;
      cs = reduce(cs, value, null);
      int[] rep = representatives(cs, n);
      if (rep == null) {
        return new ClauseSimplification(List.of(), units, equivalences, true);
      }
      int substituted = 0;
      for (int l = 0; l < 2 * n; l += 2) {
        if (rep[l] != l) {
          substituted++;
        }
      }
      if (substituted == 0 && fixed == 0 && round > 0) {
        break;
      }
      equivalences += substituted;
      cs = reduce(cs, value, rep);
      if (substituted == 0) {
        break;
      }
    }
    List<LinearForm> rows = new ArrayList<>(cs.size());
    for (int[] c : cs) {
      IntVar[] xs = new IntVar[c.length];
      long[] ws = new long[c.length];
      long b = 1;
      for (int k = 0; k < c.length; k++) {
        xs[k] = vars.get(c[k] >> 1);
        if ((c[k] & 1) == 0) {
          ws[k] = 1;
        } else {
          ws[k] = -1;
          b--;
        }
      }
      rows.add(new LinearForm(xs, ws, b, LinearForm.GE));
    }
    return new ClauseSimplification(rows, units, equivalences, false);
  }

  // whether the literal is true (1), false (0) or free (-1) under the values
  private static int truth(int l, int[] value) {
    int v = value[l >> 1];
    return v < 0 ? -1 : ((l & 1) == 0 ? v : 1 - v);
  }

  /**
   * Unit propagation over the clauses: fixes the values and returns how many it fixed, or -1 when a
   * clause has all its literals false.
   */
  private static int propagate(List<int[]> cs, int[] value, int n) {
    // the clauses of each literal, and of each clause the count of literals not false
    int[] count = new int[2 * n + 1];
    for (int[] c : cs) {
      for (int l : c) {
        count[l + 1]++;
      }
    }
    for (int l = 0; l < 2 * n; l++) {
      count[l + 1] += count[l];
    }
    int[] occurs = new int[count[2 * n]];
    int[] fill = Arrays.copyOf(count, 2 * n);
    int[] open = new int[cs.size()];
    boolean[] satisfied = new boolean[cs.size()];
    int[] queue = new int[n];
    int head = 0;
    int tail = 0;
    for (int i = 0; i < cs.size(); i++) {
      int[] c = cs.get(i);
      for (int l : c) {
        occurs[fill[l]++] = i;
        int t = truth(l, value);
        if (t == 1) {
          satisfied[i] = true;
        } else if (t < 0) {
          open[i]++;
        }
      }
    }
    int fixed = 0;
    for (int i = 0; i < cs.size(); i++) {
      if (satisfied[i] || open[i] > 1) {
        continue;
      }
      if (open[i] == 0) {
        return -1;
      }
      for (int l : cs.get(i)) {
        if (truth(l, value) < 0) {
          value[l >> 1] = 1 - (l & 1);
          queue[tail++] = l;
          fixed++;
        }
      }
    }
    while (head < tail) {
      int l = queue[head++];
      for (int k = count[l]; k < count[l + 1]; k++) {
        satisfied[occurs[k]] = true;
      }
      int negated = l ^ 1;
      for (int k = count[negated]; k < count[negated + 1]; k++) {
        int i = occurs[k];
        if (satisfied[i]) {
          continue;
        }
        if (--open[i] == 0) {
          return -1;
        }
        if (open[i] == 1) {
          for (int u : cs.get(i)) {
            int t = truth(u, value);
            if (t == 1) {
              satisfied[i] = true;
              break;
            }
            if (t < 0) {
              value[u >> 1] = 1 - (u & 1);
              queue[tail++] = u;
              fixed++;
              break;
            }
          }
        }
      }
    }
    return fixed;
  }

  /**
   * Rewrites the clauses: drops the satisfied ones and the false literals, replaces each literal by
   * its representative (when given), and drops tautologies and repeated clauses.
   */
  private static List<int[]> reduce(List<int[]> cs, int[] value, int[] rep) {
    List<int[]> out = new ArrayList<>(cs.size());
    Set<List<Integer>> seen = new HashSet<>();
    for (int[] c : cs) {
      int[] d = new int[c.length];
      int m = 0;
      boolean drop = false;
      for (int l : c) {
        int t = truth(l, value);
        if (t == 1) {
          drop = true;
          break;
        }
        if (t == 0) {
          continue;
        }
        d[m++] = rep == null ? l : rep[l];
      }
      if (drop) {
        continue;
      }
      d = Arrays.copyOf(d, m);
      Arrays.sort(d);
      int w = 0;
      for (int k = 0; k < m; k++) {
        if (w > 0 && d[w - 1] == d[k]) {
          continue;
        }
        if (w > 0 && d[w - 1] == (d[k] ^ 1)) {
          drop = true;
          break;
        }
        d[w++] = d[k];
      }
      if (drop) {
        continue;
      }
      d = Arrays.copyOf(d, w);
      List<Integer> key = new ArrayList<>(w);
      for (int l : d) {
        key.add(l);
      }
      if (seen.add(key)) {
        out.add(d);
      }
    }
    return out;
  }

  /**
   * The representative of each literal: the least literal of its strongly connected component in
   * the implication graph of the binary clauses, where a clause (a or b) gives not a -> b and not b
   * -> a. The representative of the negation is the negation of the representative. Returns null
   * when a literal and its negation are in one component.
   */
  private static int[] representatives(List<int[]> cs, int n) {
    int nodes = 2 * n;
    int[] degree = new int[nodes + 1];
    for (int[] c : cs) {
      if (c.length == 2) {
        degree[(c[0] ^ 1) + 1]++;
        degree[(c[1] ^ 1) + 1]++;
      }
    }
    for (int l = 0; l < nodes; l++) {
      degree[l + 1] += degree[l];
    }
    int[] succ = new int[degree[nodes]];
    int[] fill = Arrays.copyOf(degree, nodes);
    for (int[] c : cs) {
      if (c.length == 2) {
        succ[fill[c[0] ^ 1]++] = c[1];
        succ[fill[c[1] ^ 1]++] = c[0];
      }
    }
    // iterative Tarjan
    int[] index = new int[nodes];
    Arrays.fill(index, -1);
    int[] low = new int[nodes];
    boolean[] onStack = new boolean[nodes];
    int[] stack = new int[nodes];
    int sp = 0;
    int[] callNode = new int[nodes];
    int[] callEdge = new int[nodes];
    int[] rep = new int[nodes];
    for (int l = 0; l < nodes; l++) {
      rep[l] = l;
    }
    int counter = 0;
    for (int root = 0; root < nodes; root++) {
      if (index[root] >= 0) {
        continue;
      }
      int depth = 0;
      callNode[0] = root;
      callEdge[0] = degree[root];
      index[root] = low[root] = counter++;
      stack[sp++] = root;
      onStack[root] = true;
      while (depth >= 0) {
        int v = callNode[depth];
        if (callEdge[depth] < degree[v + 1]) {
          int w = succ[callEdge[depth]++];
          if (index[w] < 0) {
            index[w] = low[w] = counter++;
            stack[sp++] = w;
            onStack[w] = true;
            depth++;
            callNode[depth] = w;
            callEdge[depth] = degree[w];
          } else if (onStack[w]) {
            low[v] = Math.min(low[v], index[w]);
          }
        } else {
          if (low[v] == index[v]) {
            int start = sp;
            int least = Integer.MAX_VALUE;
            do {
              start--;
              least = Math.min(least, stack[start]);
            } while (stack[start] != v);
            for (int k = start; k < sp; k++) {
              int u = stack[k];
              onStack[u] = false;
              rep[u] = least;
            }
            sp = start;
          }
          depth--;
          if (depth >= 0) {
            int parent = callNode[depth];
            low[parent] = Math.min(low[parent], low[v]);
          }
        }
      }
    }
    // the components of a literal and of its negation mirror each other; one of them names both
    int[] out = new int[nodes];
    for (int l = 0; l < nodes; l += 2) {
      int r = rep[l];
      int s = rep[l + 1];
      if (r == (l + 1) || r == s) {
        return null;
      }
      // r and s are negations of one component pair; take the pair of the least positive literal
      int a = Math.min(r, s ^ 1);
      out[l] = a;
      out[l + 1] = a ^ 1;
    }
    return out;
  }
}
