/*
 * NetworkFlowExplanation.java
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

package org.jacop.constraints.netflow;

import java.util.Arrays;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Explanations of the cost reasoning of {@link NetworkFlow} for lazy clause generation, from the
 * duals of a minimum cost flow. With node potentials p and reduced costs {@code rc(a) = c(a) +
 * p(tail) - p(head)}, every flow meeting the balances b costs {@code sum_a rc(a) x(a) - sum_v p(v)
 * b(v)}, so it costs at least {@code K = sum_a min(rc(a) l(a), rc(a) u(a)) - sum_v p(v) b(v)} when
 * each arc's flow lies in [l(a), u(a)]. That holds for any potentials; those of a minimum cost flow
 * over the bounds just before the explained entry make K the minimum cost. A reason cites the lower
 * bounds of the arcs with a positive reduced cost and the upper bounds of those with a negative
 * one, weakened as far as K stays above what the atom needs. A bound of an arc's flow is explained
 * by the minimum cost with the flow past that bound, against the upper bound of the cost. Pruning
 * that comes from the balances alone (no flow at all) is left to the generic reason.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class NetworkFlowExplanation {

  /** Networks with more node-arc products than this are not explained. */
  private static final long MAX_WORK = 1_000_000;

  private final int n;
  private final int m;
  private final int[] tail;
  private final int[] head;
  private final long[] cost;
  private final int[] structuralLower;
  private final int[] structuralUpper;
  private final IntVar[] flows;
  private final long[] balance;
  private final IntVar costVariable;

  // per solve
  private final long[] lower;
  private final long[] upper;
  private final long[] flow;
  private final long[] potential;
  private final long[] excess;
  private final long[] distance;
  private final int[] previousArc;
  private final boolean[] done;

  private NetworkFlowExplanation(
      int[] balances, int[][] arcs, IntVar[] flows, long[] cost, IntVar costVariable) {
    this.n = balances.length;
    this.m = arcs.length;
    this.tail = new int[m];
    this.head = new int[m];
    this.cost = cost;
    this.structuralLower = new int[m];
    this.structuralUpper = new int[m];
    for (int a = 0; a < m; a++) {
      tail[a] = arcs[a][0];
      head[a] = arcs[a][1];
      structuralLower[a] = arcs[a][3];
      structuralUpper[a] = arcs[a][4];
    }
    this.flows = flows;
    this.balance = new long[n];
    for (int v = 0; v < n; v++) {
      balance[v] = balances[v];
    }
    this.costVariable = costVariable;
    lower = new long[m];
    upper = new long[m];
    flow = new long[m];
    potential = new long[n];
    excess = new long[n];
    distance = new long[n];
    previousArc = new int[n];
    done = new boolean[n];
  }

  /**
   * Returns the explanations of a network with constant arc costs, or null when the network has
   * variable weights or structure handlers.
   */
  static NetworkFlowExplanation of(
      int[] balances,
      int[][] arcs,
      IntVar[] flows,
      IntVar[] weights,
      boolean structures,
      IntVar costVariable) {
    if (structures || (long) balances.length * arcs.length > MAX_WORK) {
      return null;
    }
    long[] cost = new long[arcs.length];
    for (int a = 0; a < arcs.length; a++) {
      if (weights[a] == null) {
        cost[a] = arcs[a][2];
      } else if (weights[a].singleton()) {
        cost[a] = weights[a].value();
      } else {
        return null;
      }
    }
    return new NetworkFlowExplanation(balances, arcs, flows, cost, costVariable);
  }

  /** Adds the reason of an entry of the cost or of an arc's flow; false when there is none. */
  boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar x = trail.variable(entry);
    int kind = trail.kind(entry);
    if (kind == AtomicTrail.NE) {
      return false;
    }
    int bound = trail.skippedBound(entry);
    int mark = out.size();
    if (x == costVariable) {
      if (!boundsBefore(trail, entry, null, 0, 0)) {
        return false;
      }
      if (kind == AtomicTrail.LE) {
        return explainCostMax(trail, entry, bound, out);
      }
      boolean feasible = solve();
      if (feasible
          ? citeArcs(trail, entry, bound, null, false, out) != Long.MIN_VALUE
          : citeCut(trail, entry, null, false, out)) {
        trail.addSkippedHoles(entry, bound, out);
        return true;
      }
      out.truncate(mark);
      return false;
    }
    if (!isFlow(x)) {
      return false;
    }
    boolean ge = kind == AtomicTrail.GE;
    // the flow past the bound: at most bound - 1, or at least bound + 1
    if (!boundsBefore(trail, entry, x, ge ? Long.MIN_VALUE : bound + 1L, ge ? bound - 1L : 0)) {
      return false;
    }
    boolean feasible = solve();
    if (feasible
        ? citeAgainstCost(trail, entry, x, !ge, out)
        : citeCut(trail, entry, x, !ge, out)) {
      trail.addSkippedHoles(entry, bound, out);
      return true;
    }
    out.truncate(mark);
    return false;
  }

  // once every flow variable is fixed, the cost is at most the minimum cost of the rest
  private boolean explainCostMax(AtomicTrail trail, int entry, int bound, EntryList out) {
    if (!allFixed() || !solve() || costBound() > bound) {
      return false;
    }
    citeFixed(trail, entry, out);
    trail.addSkippedHoles(entry, bound, out);
    return true;
  }

  private boolean allFixed() {
    for (int a = 0; a < m; a++) {
      if (flows[a] != null && lower[a] != upper[a]) {
        return false;
      }
    }
    return true;
  }

  private void citeFixed(AtomicTrail trail, int position, EntryList out) {
    for (int a = 0; a < m; a++) {
      IntVar f = flows[a];
      if (f != null) {
        trail.addBoundReaching(f, position, true, lower[a], out);
        trail.addBoundReaching(f, position, false, upper[a], out);
      }
    }
  }

  /**
   * Adds the reason of a failure: the minimum cost above the upper bound of the cost, no flow at
   * all, or every flow fixed at a cost below the lower bound of the cost.
   */
  boolean explainFailure(AtomicTrail trail, EntryList out) {
    int now = trail.size();
    int mark = out.size();
    if (!boundsBefore(trail, now, null, 0, 0)) {
      return false;
    }
    if (solve()
        ? citeAgainstCost(trail, now, null, false, out)
        : citeCut(trail, now, null, false, out)) {
      return true;
    }
    out.truncate(mark);
    // every flow fixed and the cost below the minimum of the cost variable
    if (allFixed() && solve() && costBound() < trail.minBefore(costVariable, now)) {
      citeFixed(trail, now, out);
      trail.addBoundReaching(costVariable, now, true, costBound() + 1, out);
      return true;
    }
    return false;
  }

  // the arc bounds just before the position; the arcs of variable x get the hypothesis instead (a
  // lower bound when atLeast is not Long.MIN_VALUE, else the upper bound atMost); false when some
  // arc's bounds are empty
  private boolean boundsBefore(
      AtomicTrail trail, int position, IntVar x, long atLeast, long atMost) {
    for (int a = 0; a < m; a++) {
      long lo = structuralLower[a];
      long hi = structuralUpper[a];
      IntVar f = flows[a];
      if (f != null) {
        lo = Math.max(lo, trail.minBefore(f, position));
        hi = Math.min(hi, trail.maxBefore(f, position));
        if (f == x) {
          if (atLeast != Long.MIN_VALUE) {
            lo = Math.max(lo, atLeast);
          } else {
            hi = Math.min(hi, atMost);
          }
        }
      }
      if (lo > hi) {
        return false;
      }
      lower[a] = lo;
      upper[a] = hi;
    }
    return true;
  }

  // the minimum cost flow within [lower, upper] by successive shortest paths; false when there is
  // no flow meeting the balances, and then cut tells whether the nodes reachable from the excess
  // (finite distance) are a cut: every arc out of them full, every arc into them at its lower bound
  private boolean solve() {
    cut = false;
    Arrays.fill(potential, 0);
    System.arraycopy(balance, 0, excess, 0, n);
    for (int a = 0; a < m; a++) {
      // arcs of negative cost start full, so no residual arc has a negative cost
      flow[a] = cost[a] < 0 ? upper[a] : lower[a];
      excess[tail[a]] -= flow[a];
      excess[head[a]] += flow[a];
    }
    while (true) {
      boolean any = false;
      for (int v = 0; v < n; v++) {
        if (excess[v] > 0) {
          any = true;
          break;
        }
      }
      if (!any) {
        for (int v = 0; v < n; v++) {
          if (excess[v] != 0) {
            return false;
          }
        }
        return true;
      }
      int t = shortestPaths();
      if (t < 0) {
        cut = true;
        return false;
      }
      // the path back to a node with excess, and how much it carries
      long delta = -excess[t];
      int v = t;
      while (previousArc[v] != -1) {
        int code = previousArc[v];
        int a = code >> 1;
        delta = Math.min(delta, (code & 1) == 0 ? upper[a] - flow[a] : flow[a] - lower[a]);
        v = (code & 1) == 0 ? tail[a] : head[a];
      }
      delta = Math.min(delta, excess[v]);
      int s = v;
      v = t;
      while (previousArc[v] != -1) {
        int code = previousArc[v];
        int a = code >> 1;
        if ((code & 1) == 0) {
          flow[a] += delta;
          v = tail[a];
        } else {
          flow[a] -= delta;
          v = head[a];
        }
      }
      excess[s] -= delta;
      excess[t] += delta;
      // potentials stay valid for every residual arc when capped at the target's distance
      long dt = distance[t];
      for (int w = 0; w < n; w++) {
        potential[w] += Math.min(distance[w], dt);
      }
    }
  }

  // Dijkstra over the residual arcs with reduced costs, from every node with excess; the nearest
  // node with a deficit, or -1
  private int shortestPaths() {
    Arrays.fill(distance, Long.MAX_VALUE);
    Arrays.fill(done, false);
    Arrays.fill(previousArc, -1);
    for (int v = 0; v < n; v++) {
      if (excess[v] > 0) {
        distance[v] = 0;
      }
    }
    while (true) {
      int u = -1;
      for (int v = 0; v < n; v++) {
        if (!done[v] && distance[v] != Long.MAX_VALUE && (u < 0 || distance[v] < distance[u])) {
          u = v;
        }
      }
      if (u < 0) {
        return -1;
      }
      if (excess[u] < 0) {
        return u;
      }
      done[u] = true;
      for (int a = 0; a < m; a++) {
        if (tail[a] == u && flow[a] < upper[a]) {
          relax(u, head[a], cost[a] + potential[u] - potential[head[a]], a << 1);
        } else if (head[a] == u && flow[a] > lower[a]) {
          relax(u, tail[a], -cost[a] + potential[u] - potential[tail[a]], (a << 1) | 1);
        }
      }
    }
  }

  private void relax(int u, int v, long reducedCost, int code) {
    long d = distance[u] + reducedCost;
    if (!done[v] && d < distance[v]) {
      distance[v] = d;
      previousArc[v] = code;
    }
  }

  private long reducedCost(int a) {
    return cost[a] + potential[tail[a]] - potential[head[a]];
  }

  // the bound K the potentials give over [lower, upper]
  private long costBound() {
    long k = 0;
    for (int a = 0; a < m; a++) {
      long rc = reducedCost(a);
      k += rc >= 0 ? rc * lower[a] : rc * upper[a];
    }
    for (int v = 0; v < n; v++) {
      k -= potential[v] * balance[v];
    }
    return k;
  }

  // whether the last failed solve left a cut
  private boolean cut;

  // cites why the nodes reached by the last search cannot send out their net supply: the upper
  // bounds of the arcs leaving them and the lower bounds of those entering, weakened within the
  // excess left over; the bound of skip on the side of the hypothesis is not cited
  private boolean citeCut(
      AtomicTrail trail, int position, IntVar skip, boolean skipLower, EntryList out) {
    if (!cut) {
      return false;
    }
    long left = 0;
    for (int v = 0; v < n; v++) {
      if (distance[v] != Long.MAX_VALUE) {
        left += excess[v];
      }
    }
    // the current flow sends all it can out of the reached nodes and still lacks left > 0
    long room = left - 1;
    if (room < 0) {
      return false;
    }
    for (int a = 0; a < m; a++) {
      boolean inTail = distance[tail[a]] != Long.MAX_VALUE;
      boolean inHead = distance[head[a]] != Long.MAX_VALUE;
      IntVar f = flows[a];
      if (inTail == inHead || f == null) {
        continue;
      }
      // leaving: its upper bound; entering: its lower bound
      boolean low = inHead;
      if (f == skip && low == skipLower) {
        continue;
      }
      long structural = low ? structuralLower[a] : structuralUpper[a];
      long before = low ? trail.minBefore(f, position) : trail.maxBefore(f, position);
      if (low ? before <= structural : before >= structural) {
        continue;
      }
      long slack = Math.min(room, Math.abs(before - structural));
      long weaker = trail.addBoundWithin(f, position, low, slack, out);
      room -= Math.min(weaker, Math.abs(before - structural));
    }
    return true;
  }

  private boolean isFlow(IntVar x) {
    for (IntVar f : flows) {
      if (f == x) {
        return true;
      }
    }
    return false;
  }

  // cites the arc bounds that keep the cost bound at need or more, lifted within the slack; the
  // bound of skip on the side of the hypothesis (lower when skipLower) is not cited; the bound kept
  private long citeArcs(
      AtomicTrail trail, int position, long need, IntVar skip, boolean skipLower, EntryList out) {
    long k = costBound();
    if (k < need) {
      return Long.MIN_VALUE;
    }
    long room = k - need;
    for (int a = 0; a < m; a++) {
      IntVar f = flows[a];
      long rc = reducedCost(a);
      boolean low = rc > 0;
      if (f == null || rc == 0 || f == skip && low == skipLower) {
        continue;
      }
      long structural = low ? structuralLower[a] : structuralUpper[a];
      long before = low ? trail.minBefore(f, position) : trail.maxBefore(f, position);
      if (low ? before <= structural : before >= structural) {
        continue;
      }
      long magnitude = Math.abs(rc);
      // the structural bound serves as well as any atom
      long slack = Math.min(room / magnitude, Math.abs(before - structural));
      long weaker = trail.addBoundWithin(f, position, low, slack, out);
      room -= Math.min(weaker, Math.abs(before - structural)) * magnitude;
    }
    return need + room;
  }

  // the minimum cost exceeds the upper bound of the cost
  private boolean citeAgainstCost(
      AtomicTrail trail, int position, IntVar skip, boolean skipLower, EntryList out) {
    long most = trail.maxBefore(costVariable, position);
    long kept = citeArcs(trail, position, most + 1, skip, skipLower, out);
    if (kept == Long.MIN_VALUE) {
      return false;
    }
    if (kept - 1 < IntDomain.MAX_INT) {
      trail.addBoundReaching(costVariable, position, false, kept - 1, out);
    }
    return true;
  }
}
