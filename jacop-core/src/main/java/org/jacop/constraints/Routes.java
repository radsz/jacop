/*
 * Routes.java
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

package org.jacop.constraints;

import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.FailException;
import org.jacop.core.InitOnce;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TrailedInts;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Routes: vehicle routes from a depot over a graph whose arcs are 0/1 literals, the
 * multiple-circuit constraint of vehicle routing (CP-SAT's {@code routes}).
 *
 * <p>The nodes are 0..n-1 and node 0 is the depot. The arcs whose literal is 1 must form circuits
 * that all pass through the depot, each once: every other node has exactly one incoming and one
 * outgoing arc, or, when it has a self loop among the arcs, may take its self loop instead and stay
 * out of every route. The depot may start any number of routes. With demands and a capacity, the
 * demands of the nodes of each route add up to at most the capacity.
 *
 * <p>Propagation keeps the degrees (one arc out and one in of each node), follows the paths of arcs
 * fixed to 1 and removes every arc that would close a path into a circuit without the depot or join
 * two paths whose demands together exceed the capacity. Under lazy clause generation each pruning
 * is explained by the arcs it rests on: the other arc at a node, or the arcs of the paths.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class Routes extends Constraint implements SatisfiedPresent, Copyable<Routes>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The tail of each arc. */
  public final int[] tails;

  /** The head of each arc. */
  public final int[] heads;

  /** The literal of each arc: 1 when the arc is used. */
  public final IntVar[] literals;

  /** The demand of each node, or null without a capacity. */
  public final int[] demands;

  /** The capacity of each route. */
  public final int capacity;

  private final int n;

  // arcs out of and into each node other than its self loop: outArc[outStart[v]..outStart[v+1]-1]
  private final int[] outStart;
  private final int[] outArc;
  private final int[] inStart;
  private final int[] inArc;
  // the self loop of each node, or -1
  private final int[] selfLoop;

  private final Map<IntVar, Integer> arcOf = new IdentityHashMap<>();

  private final InitOnce init = new InitOnce();

  // whether the constraint keeps the degrees itself
  private boolean degrees = true;

  // the paths of arcs at 1, restored on backtracking (see next, prev, otherEnd and load)
  private TrailedInts state;

  // arcs whose literal was fixed and that are not yet processed
  private final boolean[] pending;
  private final int[] stack;
  private int stackSize;

  /**
   * It constructs the constraint without demands.
   *
   * @param tails the tail of each arc, a node from 0 (the depot) to n-1.
   * @param heads the head of each arc.
   * @param literals the 0/1 literal of each arc.
   */
  public Routes(int[] tails, int[] heads, IntVar[] literals) {
    this(tails, heads, literals, null, 0);
  }

  /**
   * It constructs the constraint with the demand of each node and the capacity of each route.
   *
   * @param tails the tail of each arc, a node from 0 (the depot) to n-1.
   * @param heads the head of each arc.
   * @param literals the 0/1 literal of each arc.
   * @param demands the demand of each node (non-negative), or null for no capacity.
   * @param capacity the capacity of each route, used only with demands.
   */
  public Routes(int[] tails, int[] heads, IntVar[] literals, int[] demands, int capacity) {

    if (tails == null || heads == null) {
      throw new IllegalArgumentException("Routes needs the tail and the head of each arc");
    }
    checkInputForNullness("literals", literals);
    checkInputForDuplication("literals", literals);
    if (tails.length != heads.length || tails.length != literals.length) {
      throw new IllegalArgumentException("Routes needs a tail, a head and a literal for each arc");
    }
    int max = 0;
    for (int k = 0; k < tails.length; k++) {
      if (tails[k] < 0 || heads[k] < 0) {
        throw new IllegalArgumentException("Routes has a negative node");
      }
      max = Math.max(max, Math.max(tails[k], heads[k]));
    }
    this.n = max + 1;
    if (demands != null) {
      if (demands.length < n) {
        throw new IllegalArgumentException("Routes needs a demand for each of the " + n + " nodes");
      }
      for (int d : demands) {
        if (d < 0) {
          throw new IllegalArgumentException("Routes needs non-negative demands");
        }
      }
    }

    this.numberId = idNumber.incrementAndGet();
    this.tails = Arrays.copyOf(tails, tails.length);
    this.heads = Arrays.copyOf(heads, heads.length);
    this.literals = Arrays.copyOf(literals, literals.length);
    this.demands = demands == null ? null : Arrays.copyOf(demands, n);
    this.capacity = capacity;
    this.queueIndex = 1;

    selfLoop = new int[n];
    Arrays.fill(selfLoop, -1);
    outStart = new int[n + 1];
    inStart = new int[n + 1];
    int m = tails.length;
    for (int k = 0; k < m; k++) {
      if (tails[k] == heads[k]) {
        if (selfLoop[tails[k]] >= 0) {
          throw new IllegalArgumentException("Routes has two self loops on node " + tails[k]);
        }
        selfLoop[tails[k]] = k;
      } else {
        outStart[tails[k] + 1]++;
        inStart[heads[k] + 1]++;
      }
      arcOf.put(literals[k], k);
    }
    for (int v = 0; v < n; v++) {
      outStart[v + 1] += outStart[v];
      inStart[v + 1] += inStart[v];
    }
    outArc = new int[outStart[n]];
    inArc = new int[inStart[n]];
    int[] o = Arrays.copyOf(outStart, n);
    int[] i = Arrays.copyOf(inStart, n);
    for (int k = 0; k < m; k++) {
      if (tails[k] != heads[k]) {
        outArc[o[tails[k]]++] = k;
        inArc[i[heads[k]]++] = k;
      }
    }

    pending = new boolean[m];
    stack = new int[m];

    setScope(literals);
  }

  /**
   * It tells whether the constraint keeps the degrees itself (one arc out of and one into each node
   * other than the depot). A model whose own constraints keep them can turn this off, so the
   * constraint only follows the paths.
   *
   * @param degrees false when the degrees are kept by other constraints.
   */
  public void setDegrees(boolean degrees) {
    this.degrees = degrees;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public void impose(Store store) {
    super.impose(store);
    state = new TrailedInts(store, 4 * n);
  }

  @Override
  public void queueVariable(int level, Var v) {
    Integer a = arcOf.get(v);
    if (a != null) {
      push(a);
    }
  }

  private void push(int a) {
    if (!pending[a]) {
      pending[a] = true;
      stack[stackSize++] = a;
    }
  }

  // the path state: the successor and predecessor (node + 1, 0 for none) of each node, the other
  // end of the path of each end of a path (node + 1, 0 for the node alone), and the demand of the
  // path of each end of a path
  private int next(int v) {
    return state.get(v) - 1;
  }

  private int prev(int v) {
    return state.get(n + v) - 1;
  }

  private int otherEnd(int v) {
    int o = state.get(2 * n + v);
    return o == 0 ? v : o - 1;
  }

  private int load(int v) {
    return state.get(3 * n + v);
  }

  @Override
  public void consistency(Store store) {
    if (init.begin(store)) {
      for (IntVar x : literals) {
        x.domain.in(store.level, x, 0, 1);
      }
      if (selfLoop[0] >= 0) {
        IntVar x = literals[selfLoop[0]];
        x.domain.in(store.level, x, 0, 0);
      }
      for (int v = 1; v < n; v++) {
        state.set(3 * n + v, demands == null ? 0 : demands[v]);
      }
      for (int a = 0; a < literals.length; a++) {
        push(a);
      }
      drain(store);
      if (degrees) {
        for (int v = 1; v < n; v++) {
          degree(store, outArc, outStart[v], outStart[v + 1], selfLoop[v]);
          degree(store, inArc, inStart[v], inStart[v + 1], selfLoop[v]);
        }
      }
      // pairs of paths, and nodes alone, that the paths found so far keep apart
      for (int a = 0; a < literals.length; a++) {
        if (!literals[a].singleton()) {
          pair(store, a);
        }
      }
    }
    drain(store);
  }

  private void drain(Store store) {
    try {
      while (stackSize > 0) {
        int a = stack[--stackSize];
        pending[a] = false;
        IntVar x = literals[a];
        if (x.min() == 1) {
          arcOne(store, a);
        } else if (x.max() == 0 && degrees) {
          arcZero(store, a);
        }
      }
    } catch (FailException e) {
      while (stackSize > 0) {
        pending[stack[--stackSize]] = false;
      }
      throw e;
    }
  }

  private void zero(Store store, int a) {
    IntVar x = literals[a];
    if (x.max() > 0) {
      x.domain.in(store.level, x, 0, 0);
    }
  }

  // every arc of arcs[from..to-1] and the self loop but arc a to 0
  private void zeroOthers(Store store, int a, int[] arcs, int from, int to, int self) {
    for (int q = from; q < to; q++) {
      if (arcs[q] != a) {
        zero(store, arcs[q]);
      }
    }
    if (self >= 0 && self != a) {
      zero(store, self);
    }
  }

  private void arcOne(Store store, int a) {
    int t = tails[a];
    int h = heads[a];
    if (t == h) {
      if (degrees) {
        zeroOthers(store, a, outArc, outStart[t], outStart[t + 1], -1);
        zeroOthers(store, a, inArc, inStart[t], inStart[t + 1], -1);
      }
      return;
    }
    boolean known = (t == 0 || next(t) == h) && (h == 0 || prev(h) == t);
    if (known) {
      return;
    }
    if (t != 0 && next(t) >= 0 || h != 0 && prev(h) >= 0) {
      // a second arc out of t or into h
      throw Store.failException;
    }
    if (degrees) {
      if (t != 0) {
        zeroOthers(store, a, outArc, outStart[t], outStart[t + 1], selfLoop[t]);
      }
      if (h != 0) {
        zeroOthers(store, a, inArc, inStart[h], inStart[h + 1], selfLoop[h]);
      }
    }
    if (t != 0) {
      state.set(t, h + 1);
    }
    if (h != 0) {
      state.set(n + h, t + 1);
    }
    if (t == 0 || h == 0) {
      // a depot arc puts the node in a route
      if (demands != null && load(t == 0 ? h : t) > capacity) {
        throw Store.failException;
      }
      return;
    }
    // the path s .. t and the path h .. e become s .. e
    int s = otherEnd(t);
    int e = otherEnd(h);
    if (s == h) {
      throw Store.failException;
    }
    long sum = (long) load(t) + load(h);
    if (demands != null && sum > capacity) {
      throw Store.failException;
    }
    int total = (int) Math.min(sum, Integer.MAX_VALUE);
    state.set(2 * n + s, e + 1);
    state.set(2 * n + e, s + 1);
    state.set(3 * n + s, total);
    state.set(3 * n + e, total);
    // e -> s would close the path into a circuit without the depot
    for (int q = outStart[e]; q < outStart[e + 1]; q++) {
      int b = outArc[q];
      int j = heads[b];
      if (j == s) {
        zero(store, b);
      } else if (demands != null
          && j != 0
          && !literals[b].singleton()
          && prev(j) < 0
          && (long) total + load(j) > capacity) {
        zero(store, b);
      }
    }
    if (demands != null) {
      for (int q = inStart[s]; q < inStart[s + 1]; q++) {
        int b = inArc[q];
        int i = tails[b];
        if (i != 0
            && !literals[b].singleton()
            && next(i) < 0
            && (long) load(i) + total > capacity) {
          zero(store, b);
        }
      }
    }
  }

  private void arcZero(Store store, int a) {
    int t = tails[a];
    int h = heads[a];
    if (t != 0) {
      degree(store, outArc, outStart[t], outStart[t + 1], selfLoop[t]);
    }
    if (h != 0) {
      degree(store, inArc, inStart[h], inStart[h + 1], selfLoop[h]);
    }
  }

  // exactly one of the arcs arcs[from..to-1] and the self loop is 1
  private void degree(Store store, int[] arcs, int from, int to, int self) {
    int free = -1;
    int frees = 0;
    for (int p = from; p <= to; p++) {
      int a = p < to ? arcs[p] : self;
      if (a < 0) {
        continue;
      }
      IntVar x = literals[a];
      if (x.min() == 1) {
        return;
      } else if (!x.singleton()) {
        free = a;
        frees++;
      }
    }
    if (frees == 0) {
      throw Store.failException;
    } else if (frees == 1) {
      literals[free].domain.in(store.level, literals[free], 1, 1);
    }
  }

  // arc a joins two paths: not into a circuit without the depot, not over the capacity
  private void pair(Store store, int a) {
    int t = tails[a];
    int h = heads[a];
    if (t == h) {
      return;
    }
    if (t == 0 || h == 0) {
      int v = t == 0 ? h : t;
      // a node alone may still take its self loop, but this arc puts it in a route
      if (demands != null && load(v) > capacity) {
        zero(store, a);
      }
      return;
    }
    if (next(t) >= 0 || prev(h) >= 0) {
      return;
    }
    if (otherEnd(t) == h || demands != null && (long) load(t) + load(h) > capacity) {
      zero(store, a);
    }
  }

  @Override
  public boolean satisfied() {
    for (IntVar x : literals) {
      if (!x.singleton()) {
        return false;
      }
    }
    return check(literals);
  }

  // whether fixed literals form routes
  private boolean check(IntVar[] lits) {
    int[] succ = new int[n];
    int[] in = new int[n];
    int[] out = new int[n];
    boolean[] off = new boolean[n];
    Arrays.fill(succ, -1);
    for (int a = 0; a < lits.length; a++) {
      if (lits[a].value() == 1) {
        if (tails[a] == heads[a]) {
          if (tails[a] == 0) {
            return false;
          }
          off[tails[a]] = true;
          out[tails[a]]++;
          in[tails[a]]++;
        } else {
          succ[tails[a]] = heads[a];
          out[tails[a]]++;
          in[heads[a]]++;
        }
      }
    }
    for (int v = 1; v < n; v++) {
      if (in[v] != 1 || out[v] != 1) {
        return false;
      }
    }
    boolean[] seen = new boolean[n];
    for (int a = 0; a < lits.length; a++) {
      if (lits[a].value() == 1 && tails[a] == 0 && heads[a] != 0) {
        long sum = 0;
        int w = heads[a];
        while (w != 0) {
          if (seen[w]) {
            return false;
          }
          seen[w] = true;
          sum += demands == null ? 0 : demands[w];
          w = succ[w];
        }
        if (demands != null && sum > capacity) {
          return false;
        }
      }
    }
    for (int v = 1; v < n; v++) {
      if (!off[v] && !seen[v]) {
        return false;
      }
    }
    return true;
  }

  // ---------------------------------------------------------------------------------------------
  // explanations

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    Integer index = arcOf.get(trail.variable(entry));
    if (index == null) {
      return false;
    }
    int a = index;
    int kind = trail.kind(entry);
    int value = trail.value(entry);
    // the atom of the entry: x >= 1, x <= 0, or x != 0 / x != 1
    boolean one;
    if (kind == AtomicTrail.GE && value >= 1 || kind == AtomicTrail.NE && value == 0) {
      one = true;
    } else if (kind == AtomicTrail.LE && value <= 0 || kind == AtomicTrail.NE && value == 1) {
      one = false;
    } else {
      return false;
    }
    int mark = out.size();
    boolean done = one ? explainOne(trail, entry, a, out) : explainZero(trail, entry, a, out);
    if (!done) {
      out.truncate(mark);
      return false;
    }
    out.sortUnique(mark);
    return true;
  }

  private boolean isOne(AtomicTrail trail, int a, int position) {
    return trail.minBefore(literals[a], position) >= 1;
  }

  private boolean isZero(AtomicTrail trail, int a, int position) {
    return trail.maxBefore(literals[a], position) <= 0;
  }

  // the arc is 1: every other arc out of its tail, or into its head, is 0
  private boolean explainOne(AtomicTrail trail, int p, int a, EntryList out) {
    if (!degrees) {
      // only the degrees set an arc to 1
      return false;
    }
    int t = tails[a];
    int h = heads[a];
    if (t != 0 && allOthersZero(trail, p, a, outArc, outStart[t], outStart[t + 1], selfLoop[t])) {
      addZeros(trail, p, a, outArc, outStart[t], outStart[t + 1], selfLoop[t], out);
      return true;
    }
    if (h != 0 && allOthersZero(trail, p, a, inArc, inStart[h], inStart[h + 1], selfLoop[h])) {
      addZeros(trail, p, a, inArc, inStart[h], inStart[h + 1], selfLoop[h], out);
      return true;
    }
    return false;
  }

  private boolean allOthersZero(
      AtomicTrail trail, int p, int a, int[] arcs, int from, int to, int self) {
    for (int q = from; q <= to; q++) {
      int b = q < to ? arcs[q] : self;
      if (b >= 0 && b != a && !isZero(trail, b, p)) {
        return false;
      }
    }
    return true;
  }

  private void addZeros(
      AtomicTrail trail, int p, int a, int[] arcs, int from, int to, int self, EntryList out) {
    for (int q = from; q <= to; q++) {
      int b = q < to ? arcs[q] : self;
      if (b >= 0 && b != a) {
        trail.addUpperBound(literals[b], p, out);
      }
    }
  }

  // an arc at the same node is 1
  private boolean otherOne(
      AtomicTrail trail, int p, int a, int[] arcs, int from, int to, int self, EntryList out) {
    for (int q = from; q <= to; q++) {
      int b = q < to ? arcs[q] : self;
      if (b >= 0 && b != a && isOne(trail, b, p)) {
        trail.addLowerBound(literals[b], p, out);
        return true;
      }
    }
    return false;
  }

  // the arc is 0: another arc at its tail or head is 1, or it closes a path of arcs at 1 into a
  // circuit without the depot, or joins two paths over the capacity
  private boolean explainZero(AtomicTrail trail, int p, int a, EntryList out) {
    int t = tails[a];
    int h = heads[a];
    if (t == h) {
      return t == 0 || otherOneAt(trail, p, a, out);
    }
    if (otherOneAt(trail, p, a, out)) {
      return true;
    }
    if ((t == 0 || h == 0) && demands == null) {
      return false;
    }
    // the path of arcs at 1 that ends at t and the one that starts at h
    long sum = demands == null ? 0 : (long) demands[t] + demands[h];
    int w = h;
    int steps = 0;
    while (w != 0 && steps++ < n) {
      int b = arcOut(trail, w, p);
      if (b < 0) {
        break;
      }
      trail.addLowerBound(literals[b], p, out);
      w = heads[b];
      if (w == t) {
        // h .. t closes into a circuit without the depot
        return true;
      }
      if (w == 0) {
        break;
      }
      sum += demands == null ? 0 : demands[w];
    }
    if (demands == null) {
      return false;
    }
    w = t;
    steps = 0;
    while (w != 0 && steps++ < n && sum <= capacity) {
      int b = arcIn(trail, w, p);
      if (b < 0) {
        break;
      }
      trail.addLowerBound(literals[b], p, out);
      w = tails[b];
      if (w == 0 || w == h) {
        break;
      }
      sum += demands[w];
    }
    return sum > capacity;
  }

  // another arc out of the tail or into the head of arc a is 1 (for a self loop, any arc at its
  // node); without its degrees the constraint removes no arc for that reason
  private boolean otherOneAt(AtomicTrail trail, int p, int a, EntryList out) {
    if (!degrees) {
      return false;
    }
    int t = tails[a];
    int h = heads[a];
    if (t == h) {
      return otherOne(trail, p, a, outArc, outStart[t], outStart[t + 1], -1, out)
          || otherOne(trail, p, a, inArc, inStart[t], inStart[t + 1], -1, out);
    }
    return t != 0 && otherOne(trail, p, a, outArc, outStart[t], outStart[t + 1], selfLoop[t], out)
        || h != 0 && otherOne(trail, p, a, inArc, inStart[h], inStart[h + 1], selfLoop[h], out);
  }

  // the arc at 1 out of node w (not its self loop) just before the position, or -1
  private int arcOut(AtomicTrail trail, int w, int p) {
    for (int q = outStart[w]; q < outStart[w + 1]; q++) {
      if (isOne(trail, outArc[q], p)) {
        return outArc[q];
      }
    }
    return -1;
  }

  private int arcIn(AtomicTrail trail, int w, int p) {
    for (int q = inStart[w]; q < inStart[w + 1]; q++) {
      if (isOne(trail, inArc[q], p)) {
        return inArc[q];
      }
    }
    return -1;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    int p = trail.size();
    int mark = out.size();
    if (failure(trail, p, out)) {
      out.sortUnique(mark);
      return true;
    }
    out.truncate(mark);
    return false;
  }

  private boolean failure(AtomicTrail trail, int p, EntryList out) {
    return degreeFailure(trail, p, out) || pathFailure(trail, p, out);
  }

  // a node with two arcs at 1, or with every arc out or in at 0
  private boolean degreeFailure(AtomicTrail trail, int p, EntryList out) {
    for (int v = 1; v < n; v++) {
      // without its degrees a self loop at 1 does not exclude the other arcs here
      int self = degrees ? selfLoop[v] : -1;
      if (twoOnes(trail, p, outArc, outStart[v], outStart[v + 1], self, out)
          || twoOnes(trail, p, inArc, inStart[v], inStart[v + 1], self, out)) {
        return true;
      }
      if (!degrees) {
        // a node without an arc out or in is left to the constraints that keep the degrees
        continue;
      }
      if (allOthersZero(trail, p, -1, outArc, outStart[v], outStart[v + 1], selfLoop[v])) {
        addZeros(trail, p, -1, outArc, outStart[v], outStart[v + 1], selfLoop[v], out);
        return true;
      }
      if (allOthersZero(trail, p, -1, inArc, inStart[v], inStart[v + 1], selfLoop[v])) {
        addZeros(trail, p, -1, inArc, inStart[v], inStart[v + 1], selfLoop[v], out);
        return true;
      }
    }
    return false;
  }

  // a circuit of arcs at 1 without the depot, or a path over the capacity
  private boolean pathFailure(AtomicTrail trail, int p, EntryList out) {
    int[] succ = new int[n];
    int[] pred = new int[n];
    Arrays.fill(succ, -1);
    Arrays.fill(pred, -1);
    for (int a = 0; a < literals.length; a++) {
      if (tails[a] != heads[a] && isOne(trail, a, p)) {
        succ[tails[a]] = a;
        pred[heads[a]] = a;
      }
    }
    boolean[] seen = new boolean[n];
    for (int v = 1; v < n; v++) {
      if (seen[v]) {
        continue;
      }
      // the start of v's path, or v itself on a circuit
      int s = v;
      int steps = 0;
      while (pred[s] >= 0 && tails[pred[s]] != 0 && tails[pred[s]] != v && steps++ < n) {
        s = tails[pred[s]];
      }
      boolean circuit = pred[s] >= 0 && tails[pred[s]] == v;
      if (circuit) {
        s = v;
      }
      long sum = 0;
      int w = s;
      int mark = out.size();
      steps = 0;
      while (w > 0 && steps++ < n) {
        seen[w] = true;
        sum += demands == null ? 0 : demands[w];
        int b = succ[w];
        if (b < 0) {
          break;
        }
        trail.addLowerBound(literals[b], p, out);
        w = heads[b];
        if (w == s) {
          return true;
        }
      }
      if (demands != null && sum > capacity) {
        if (w == s && selfLoop[s] >= 0) {
          // a node on its own is in a route only when its self loop is 0
          if (!isZero(trail, selfLoop[s], p)) {
            out.truncate(mark);
            continue;
          }
          trail.addUpperBound(literals[selfLoop[s]], p, out);
        }
        // the nodes of the path are in one route
        return true;
      }
      out.truncate(mark);
    }
    return false;
  }

  private boolean twoOnes(
      AtomicTrail trail, int p, int[] arcs, int from, int to, int self, EntryList out) {
    int first = -1;
    for (int q = from; q <= to; q++) {
      int b = q < to ? arcs[q] : self;
      if (b >= 0 && isOne(trail, b, p)) {
        if (first >= 0) {
          trail.addLowerBound(literals[first], p, out);
          trail.addLowerBound(literals[b], p, out);
          return true;
        }
        first = b;
      }
    }
    return false;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : Routes(").append(Arrays.toString(tails)).append(", ");
    result.append(Arrays.toString(heads)).append(", [");
    appendArrayToString(result, literals);
    result.append(']');
    if (demands != null) {
      result.append(", ").append(Arrays.toString(demands)).append(", ").append(capacity);
    }
    result.append(')');
    return result.toString();
  }

  @Override
  public Routes copy(VarMap map) {
    Routes c = new Routes(tails, heads, map.get(literals), demands, capacity);
    c.degrees = degrees;
    return c;
  }
}
