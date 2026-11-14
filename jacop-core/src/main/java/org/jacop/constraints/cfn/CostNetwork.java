/*
 * CostNetwork.java
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

package org.jacop.constraints.cfn;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * A cost function network: variables with finite value lists, unary and binary cost functions in
 * extension, a constant, and {@link #HARD} for forbidden tuples. Its cost is a lower bound of the
 * objective of a model (see {@link CostNetworkBound}).
 *
 * <p>{@link #solve} computes a reparametrisation: equivalence-preserving transformations (EPTs)
 * that move costs between the binary functions and the unary ones, as soft arc consistency does (M.
 * C. Cooper, S. de Givry, M. Sanchez, T. Schiex, M. Zytnicki and T. Werner, Soft arc consistency
 * revisited, Artificial Intelligence 174 (2010) 449-478). The moves are those of the edge updates
 * of max-product linear programming (A. Globerson and T. Jaakkola, Fixing max-product: convergent
 * message passing algorithms for MAP LP-relaxations, NIPS 2007), a block coordinate ascent of the
 * dual of the local polytope whose fixed points are virtually arc consistent as in Cooper et al.
 * Costs are scaled integers, so every move is exact and the bound c<sub>0</sub> + &Sigma; min
 * f<sub>i</sub> + &Sigma; min f<sub>ij</sub> holds whatever the rounding of the halves.
 *
 * <p>Before the sweeps, a hard binary function that is a bijection between the values of its two
 * variables merges them (functional variable elimination, as toulbar2's preprocessing does): the
 * frequency pairs |x - y| = k of the radio link frequency assignment problems (CELAR) are such
 * bijections, and message passing alone moves little cost across them.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class CostNetwork {

  /** The cost of a forbidden assignment. */
  public static final long HARD = Long.MAX_VALUE;

  /** The largest absolute finite cost a function may have. */
  public static final long MAX_COST = 1L << 40;

  final int[][] values;

  final long[][] unary;

  // the binary functions by pair i * n + j, i < j, costs row-major over values[i] x values[j]
  final Map<Long, Edge> edges = new HashMap<>();

  long constant;

  /** A binary function over variables i < j, row-major over their values. */
  static final class Edge {
    final int i;
    final int j;
    final long[] cost;

    Edge(int i, int j, long[] cost) {
      this.i = i;
      this.j = j;
      this.cost = cost;
    }
  }

  /**
   * Creates a network with zero cost functions.
   *
   * @param values the values of each variable
   */
  public CostNetwork(int[][] values) {
    this.values = values;
    unary = new long[values.length][];
    for (int i = 0; i < values.length; i++) {
      unary[i] = new long[values[i].length];
    }
  }

  /**
   * Returns the number of variables.
   *
   * @return the number of variables
   */
  public int size() {
    return values.length;
  }

  /**
   * Returns the number of binary functions.
   *
   * @return the binary functions over distinct pairs of variables
   */
  public int edges() {
    return edges.size();
  }

  /**
   * Returns the number of binary cost entries.
   *
   * @return the entries of all binary functions
   */
  public long entries() {
    long s = 0;
    for (Edge e : edges.values()) {
      s += e.cost.length;
    }
    return s;
  }

  /**
   * Adds a constant cost.
   *
   * @param c the cost
   */
  public void addConstant(long c) {
    constant = add(constant, c);
  }

  /**
   * Adds a cost to one value of a variable.
   *
   * @param i the variable
   * @param a the index of the value
   * @param c the cost, or {@link #HARD}
   */
  public void addUnary(int i, int a, long c) {
    unary[i][a] = add(unary[i][a], c);
  }

  /**
   * Adds a binary function.
   *
   * @param i the first variable
   * @param j the second variable, not i
   * @param cost the costs, row-major over the values of i and j, {@link #HARD} for forbidden pairs
   */
  public void addBinary(int i, int j, long[] cost) {
    if (i == j) {
      throw new IllegalArgumentException("a binary function over one variable");
    }
    int di = values[i].length;
    int dj = values[j].length;
    if (cost.length != di * dj) {
      throw new IllegalArgumentException("costs of a wrong size");
    }
    if (i > j) {
      long[] t = new long[cost.length];
      for (int a = 0; a < di; a++) {
        for (int b = 0; b < dj; b++) {
          t[b * di + a] = cost[a * dj + b];
        }
      }
      addOrdered(j, i, t);
    } else {
      addOrdered(i, j, cost.clone());
    }
  }

  private void addOrdered(int i, int j, long[] cost) {
    Edge e = edges.get(key(i, j));
    if (e == null) {
      edges.put(key(i, j), new Edge(i, j, cost));
    } else {
      for (int k = 0; k < cost.length; k++) {
        e.cost[k] = add(e.cost[k], cost[k]);
      }
    }
  }

  private long key(int i, int j) {
    return (long) i * values.length + j;
  }

  /**
   * Writes the network in the wcsp format of toulbar2, values by index, {@link #HARD} as the top
   * cost (one more than the sum of the finite costs). For comparisons with other solvers.
   *
   * @param out where it is written
   */
  public void writeWcsp(java.io.PrintWriter out) {
    long top = 1;
    int functions = 0;
    for (long[] u : unary) {
      for (long c : u) {
        top += c == HARD ? 0 : Math.abs(c);
      }
      functions++;
    }
    for (Edge e : edges.values()) {
      for (long c : e.cost) {
        top += c == HARD ? 0 : Math.abs(c);
      }
    }
    int max = 1;
    for (int[] v : values) {
      max = Math.max(max, v.length);
    }
    out.println(
        "cfn " + values.length + " " + max + " " + (functions + edges.size() + 1) + " " + top);
    StringBuilder sb = new StringBuilder();
    for (int[] v : values) {
      sb.append(v.length).append(' ');
    }
    out.println(sb.toString().trim());
    out.println("0 " + constant + " 0");
    for (int i = 0; i < unary.length; i++) {
      out.println("1 " + i + " 0 " + unary[i].length);
      for (int a = 0; a < unary[i].length; a++) {
        out.println(a + " " + (unary[i][a] == HARD ? top : unary[i][a]));
      }
    }
    for (Edge e : edges.values()) {
      int dj = values[e.j].length;
      out.println("2 " + e.i + " " + e.j + " 0 " + e.cost.length);
      for (int k = 0; k < e.cost.length; k++) {
        out.println(k / dj + " " + k % dj + " " + (e.cost[k] == HARD ? top : e.cost[k]));
      }
    }
    out.flush();
  }

  /** Adds two costs, either of which may be {@link #HARD}. */
  static long add(long a, long b) {
    if (a == HARD || b == HARD) {
      return HARD;
    }
    long s = a + b;
    if (((a ^ s) & (b ^ s)) < 0) {
      throw new ArithmeticException("cost overflow");
    }
    return s;
  }

  /** What {@link #solve} found. */
  public static final class Solution {
    /** The costs were multiplied by it. */
    public final long scale;

    /** The constant of the reparametrised network, scaled. */
    public final long constant;

    /**
     * The unary costs of the reparametrised network, scaled; {@link #HARD} for values that no
     * solution takes. All the binary costs left are at least 0.
     */
    public final long[][] unary;

    /** For each variable, the variable it was merged into, or itself. */
    public final int[] merged;

    /** The sweeps made. */
    public final int sweeps;

    /** The bound after each sweep, scaled, the first entry before any. */
    public final long[] trace;

    /** The binary functions left: the first and the second variable of each, first &lt; second. */
    public final int[] edgeFirst;

    /** The second variable of each binary function left. */
    public final int[] edgeSecond;

    /**
     * The residual costs of each binary function left, scaled, row-major over the values of the
     * first variable; at least 0, the least 0.
     */
    public final long[][] edgeCost;

    Solution(
        long scale,
        long constant,
        long[][] unary,
        int[] merged,
        int sweeps,
        long[] trace,
        int[] edgeFirst,
        int[] edgeSecond,
        long[][] edgeCost) {
      this.edgeFirst = edgeFirst;
      this.edgeSecond = edgeSecond;
      this.edgeCost = edgeCost;
      this.scale = scale;
      this.constant = constant;
      this.unary = unary;
      this.merged = merged;
      this.sweeps = sweeps;
      this.trace = trace;
    }

    /**
     * Returns the bound of the reparametrised network over all values, scaled.
     *
     * @return the constant plus the least unary cost of each variable, {@link #HARD} if a variable
     *     has no value left
     */
    public long bound() {
      long s = constant;
      for (long[] u : unary) {
        long m = HARD;
        for (long c : u) {
          m = Math.min(m, c);
        }
        if (u.length > 0) {
          s = add(s, m);
        }
      }
      return s;
    }

    /**
     * Returns the number of variables merged into others.
     *
     * @return the merged variables
     */
    public int mergedCount() {
      int k = 0;
      for (int i = 0; i < merged.length; i++) {
        if (merged[i] != i) {
          k++;
        }
      }
      return k;
    }
  }

  /**
   * Computes the reparametrisation. The network is changed.
   *
   * @param deadline the System.nanoTime() after which no sweep starts
   * @param maxSweeps the sweeps at most
   * @return the reparametrisation
   */
  public Solution solve(long deadline, int maxSweeps) {
    long total = 1;
    for (long[] u : unary) {
      for (long c : u) {
        if (c != HARD) {
          total += Math.abs(c);
        }
      }
    }
    for (Edge e : edges.values()) {
      for (long c : e.cost) {
        if (c != HARD) {
          total += Math.abs(c);
        }
      }
      if (total > MAX_COST) {
        break;
      }
    }
    // the costs times the scale stay far below 2^63 whatever the moves add up
    long scale = 1;
    while (scale < (1L << 16) && total < (1L << 56) / scale) {
      scale <<= 1;
    }
    scale(scale);
    int[] merged = mergeFunctional();
    List<Edge> list = new ArrayList<>(edges.values());
    list.sort((p, q) -> p.i != q.i ? Integer.compare(p.i, q.i) : Integer.compare(p.j, q.j));
    List<Long> trace = new ArrayList<>();
    trace.add(bound(list));
    int sweeps = 0;
    while (sweeps < maxSweeps && System.nanoTime() < deadline && !list.isEmpty()) {
      for (Edge e : list) {
        update(e);
      }
      sweeps++;
      long b = bound(list);
      trace.add(b);
      if (b == HARD) {
        break;
      }
      int n = trace.size();
      if (n > 6) {
        long before = trace.get(n - 6);
        long gain = b - before;
        // under one unit of the objective in five sweeps, and under 0.01 % of the bound
        if (gain < scale && gain <= Math.abs(b) / 10_000) {
          break;
        }
      }
    }
    // the least cost of each binary function becomes part of the constant; the residual costs left
    // are at least 0
    long c0 = constant;
    int[] ei = new int[list.size()];
    int[] ej = new int[list.size()];
    long[][] residual = new long[list.size()][];
    for (int k = 0; k < list.size(); k++) {
      Edge e = list.get(k);
      long m = HARD;
      for (long c : e.cost) {
        m = Math.min(m, c);
      }
      if (m != HARD) {
        c0 = add(c0, m);
        for (int q = 0; q < e.cost.length; q++) {
          if (e.cost[q] != HARD) {
            e.cost[q] -= m;
          }
        }
      }
      ei[k] = e.i;
      ej[k] = e.j;
      residual[k] = e.cost;
    }
    edges.clear();
    long[] t = new long[trace.size()];
    for (int k = 0; k < t.length; k++) {
      t[k] = trace.get(k);
    }
    return new Solution(scale, c0, unary, merged, sweeps, t, ei, ej, residual);
  }

  private void scale(long s) {
    if (s == 1) {
      return;
    }
    constant *= s;
    for (long[] u : unary) {
      for (int a = 0; a < u.length; a++) {
        if (u[a] != HARD) {
          u[a] *= s;
        }
      }
    }
    for (Edge e : edges.values()) {
      for (int k = 0; k < e.cost.length; k++) {
        if (e.cost[k] != HARD) {
          e.cost[k] *= s;
        }
      }
    }
  }

  // the constant, the least unary cost of each variable and the least cost of each edge
  private long bound(List<Edge> list) {
    long s = constant;
    for (long[] u : unary) {
      if (u.length == 0) {
        continue;
      }
      long m = HARD;
      for (long c : u) {
        m = Math.min(m, c);
      }
      s = add(s, m);
    }
    for (Edge e : list) {
      long m = HARD;
      for (long c : e.cost) {
        m = Math.min(m, c);
      }
      s = add(s, m);
    }
    return s;
  }

  // the MPLP update of one edge as moves: the unary costs of both ends into the edge, half of the
  // least cost of each row back to the first end, the least cost of each column to the second
  private void update(Edge e) {
    long[] f = e.cost;
    long[] ui = unary[e.i];
    long[] uj = unary[e.j];
    int di = ui.length;
    int dj = uj.length;
    for (int a = 0; a < di; a++) {
      long ca = ui[a];
      int row = a * dj;
      for (int b = 0; b < dj; b++) {
        f[row + b] = add(f[row + b], add(ca, uj[b]));
      }
    }
    Arrays.fill(ui, 0);
    Arrays.fill(uj, 0);
    for (int a = 0; a < di; a++) {
      int row = a * dj;
      long m = HARD;
      for (int b = 0; b < dj; b++) {
        m = Math.min(m, f[row + b]);
      }
      if (m == HARD) {
        ui[a] = HARD;
        continue;
      }
      long h = Math.floorDiv(m, 2);
      ui[a] = h;
      for (int b = 0; b < dj; b++) {
        if (f[row + b] != HARD) {
          f[row + b] -= h;
        }
      }
    }
    for (int b = 0; b < dj; b++) {
      long m = HARD;
      for (int a = 0; a < di; a++) {
        m = Math.min(m, f[a * dj + b]);
      }
      if (m == HARD) {
        uj[b] = HARD;
        continue;
      }
      uj[b] = m;
      for (int a = 0; a < di; a++) {
        if (f[a * dj + b] != HARD) {
          f[a * dj + b] -= m;
        }
      }
    }
  }

  // merges the two variables of every hard bijection; returns the representative of each variable
  private int[] mergeFunctional() {
    int n = values.length;
    int[] rep = new int[n];
    for (int i = 0; i < n; i++) {
      rep[i] = i;
    }
    boolean changed = true;
    while (changed) {
      changed = false;
      for (Edge e : new ArrayList<>(edges.values())) {
        // an edge an earlier merge of this pass rewrote is gone from the map
        if (edges.get(key(e.i, e.j)) != e) {
          continue;
        }
        int[] partner = bijection(e);
        if (partner != null) {
          merge(e, partner, rep);
          changed = true;
        }
      }
    }
    return rep;
  }

  // for a function whose finite entries form a partial bijection, the column of each row (-1 for
  // none); null otherwise
  private int[] bijection(Edge e) {
    int di = values[e.i].length;
    int dj = values[e.j].length;
    int[] partner = new int[di];
    boolean[] used = new boolean[dj];
    for (int a = 0; a < di; a++) {
      partner[a] = -1;
      if (unary[e.i][a] == HARD) {
        continue;
      }
      for (int b = 0; b < dj; b++) {
        if (e.cost[a * dj + b] != HARD && unary[e.j][b] != HARD) {
          if (partner[a] >= 0 || used[b]) {
            return null;
          }
          partner[a] = b;
          used[b] = true;
        }
      }
    }
    return partner;
  }

  // merges j into i along partner (row a of i goes with column partner[a] of j)
  private void merge(Edge e, int[] partner, int[] rep) {
    int i = e.i;
    int j = e.j;
    edges.remove(key(i, j));
    long[] ui = unary[i];
    long[] uj = unary[j];
    int dj = uj.length;
    for (int a = 0; a < ui.length; a++) {
      int b = partner[a];
      ui[a] = b < 0 ? HARD : add(ui[a], add(e.cost[a * dj + b], uj[b]));
    }
    Arrays.fill(uj, 0);
    for (Edge g : new ArrayList<>(edges.values())) {
      if (g.i != j && g.j != j) {
        continue;
      }
      edges.remove(key(g.i, g.j));
      int k = g.i == j ? g.j : g.i;
      int dk = values[k].length;
      long[] h = new long[ui.length * dk];
      for (int a = 0; a < ui.length; a++) {
        int b = partner[a];
        for (int c = 0; c < dk; c++) {
          if (b < 0) {
            h[a * dk + c] = HARD;
          } else {
            h[a * dk + c] = g.i == j ? g.cost[b * dk + c] : g.cost[c * dj + b];
          }
        }
      }
      addBinary(i, k, h);
    }
    for (int v = 0; v < rep.length; v++) {
      if (rep[v] == j) {
        rep[v] = i;
      }
    }
  }
}
