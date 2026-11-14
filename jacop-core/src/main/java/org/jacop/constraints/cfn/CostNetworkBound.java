/*
 * CostNetworkBound.java
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
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * A lower bound of the objective from a cost function network that the objective is at least: the
 * unary and binary cost functions a model's objective sums, as in weighted constraint satisfaction
 * (radio link frequency assignment, satellite photograph selection, protein design), with the hard
 * binary constraints between their variables.
 *
 * <p>At the first propagation the network is reparametrised over the domains of then ({@link
 * CostNetwork#solve}): the result is a constant c<sub>0</sub>, unary costs u<sub>i</sub> and binary
 * costs f<sub>ij</sub> &ge; 0 with the same cost as the network for every assignment. During search
 * each variable x<sub>j</sub> contributes the least, over its domain, of u<sub>j</sub> plus the
 * binary costs towards its fixed neighbours (an edge between two fixed variables counts once), and
 * the objective is kept at least c<sub>0</sub> plus the contributions: node consistency of the
 * reparametrised network with forward checking of its binary costs (M. C. Cooper, S. de Givry, M.
 * Sanchez, T. Schiex, M. Zytnicki and T. Werner, Soft arc consistency revisited, Artificial
 * Intelligence 174 (2010) 449-478; T. Schiex, Arc consistency for soft constraints, CP 2000). A
 * value whose cost lifts the bound past the objective's other bound is removed. Virtual arc
 * consistency maintained during search, as toulbar2 does, is the subject of H. Montalbano, S. de
 * Givry and G. Katsirelos (arXiv 2509.17706, 2025). The costs are scaled integers, so the bound is
 * exact.
 *
 * <p>The reason of a bound is the objective's other bound, for a removal, and for each variable
 * whose contribution it needs the removals of its values that cost less, with the values of the
 * fixed neighbours when their binary costs are needed, lifted: a variable whose contribution the
 * slack covers is left out.
 *
 * <p>The sweeps of the reparametrisation stop after {@code org.jacop.cfn.rootMs} milliseconds
 * (2,000) or {@code org.jacop.cfn.sweeps} sweeps (1,000), or when they stop raising the bound.
 * {@code org.jacop.cfn.dump=file} writes the network before the sweeps in the wcsp format of
 * toulbar2.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class CostNetworkBound extends Constraint
    implements Explainable, Copyable<CostNetworkBound> {

  static final long ROOT_MS = Long.getLong("org.jacop.cfn.rootMs", 2000L);

  static final boolean PRUNE =
      Boolean.parseBoolean(System.getProperty("org.jacop.cfn.prune", "true"));

  static final int SWEEPS = Integer.getInteger("org.jacop.cfn.sweeps", 1000);

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private static final long HARD = CostNetwork.HARD;

  private final IntVar objective;

  private final boolean maximize;

  private final IntVar[] x;

  private final int[][] values;

  // the network, until it is reparametrised
  private CostNetwork network;

  /** The reparametrised network, shared by copies. */
  private static final class Reparam {
    long scale;
    long c0;
    long[][] u;
    // value indexes of each variable by increasing unary cost
    int[][] order;
    // the binary functions left: ends and residual costs, and the functions of each variable
    int[] ei;
    int[] ej;
    long[][] ef;
    int[][] adj;
    // the variables with costs: not all unary costs equal, or a binary function
    int[] relevant;
    // values removed before the reparametrisation, which it assumes absent: variable, value
    int[][] assumed;
  }

  private Reparam r;

  /** The bound of the reparametrised network over the root domains, or Long.MIN_VALUE. */
  public long rootBound = Long.MIN_VALUE;

  /** The bound before the sweeps (after the functional merge), or Long.MIN_VALUE. */
  public long startBound = Long.MIN_VALUE;

  /** The sweeps made at the root. */
  public int sweeps;

  /** The variables merged into others at the root. */
  public int merged;

  /** The time of the reparametrisation, in seconds. */
  public double seconds;

  /** The values removed by the bound. */
  public long prunings;

  private final EntryList scratch = new EntryList();

  /**
   * Creates the bound.
   *
   * @param objective the objective
   * @param maximize whether the objective is maximised; the network is then a lower bound of minus
   *     the objective
   * @param x the variables of the network, distinct
   * @param network the network over the values of x, a lower bound of the objective (or of minus
   *     the objective when maximised) for every solution
   */
  public CostNetworkBound(IntVar objective, boolean maximize, IntVar[] x, CostNetwork network) {
    if (x.length != network.size()) {
      throw new IllegalArgumentException("a network of another size");
    }
    this.numberId = idNumber.incrementAndGet();
    this.objective = objective;
    this.maximize = maximize;
    this.x = x.clone();
    this.values = network.values;
    this.network = network;
    this.queueIndex = 3;
    IntVar[] scope = Arrays.copyOf(this.x, this.x.length + 1);
    scope[this.x.length] = objective;
    setScope(scope);
  }

  // a copy that shares the reparametrisation
  private CostNetworkBound(CostNetworkBound o, IntVar objective, IntVar[] x) {
    this.numberId = idNumber.incrementAndGet();
    this.objective = objective;
    this.maximize = o.maximize;
    this.x = x;
    this.values = o.values;
    this.r = o.r;
    this.rootBound = o.rootBound;
    this.startBound = o.startBound;
    this.sweeps = o.sweeps;
    this.merged = o.merged;
    this.queueIndex = 3;
    IntVar[] scope = Arrays.copyOf(this.x, this.x.length + 1);
    scope[this.x.length] = objective;
    setScope(scope);
  }

  /**
   * Tells whether the objective is maximised.
   *
   * @return true when the network bounds minus the objective
   */
  public boolean maximize() {
    return maximize;
  }

  /**
   * Returns the objective.
   *
   * @return the objective the network bounds
   */
  public IntVar objective() {
    return objective;
  }

  /**
   * Reparametrises the network over the current domains, as the first propagation does, so that
   * {@link #rootBound} can be read before the constraint is imposed.
   *
   * @param store the store of the variables
   */
  public void prepare(Store store) {
    if (r == null) {
      reparametrise();
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  /**
   * Returns the bound the network gives over the current domains, in units of the objective.
   *
   * @return the lower bound of the objective (of minus the objective when maximised), or
   *     Long.MIN_VALUE before the first propagation
   */
  public long currentBound() {
    if (r == null) {
      return Long.MIN_VALUE;
    }
    long s = r.c0;
    for (int j : r.relevant) {
      s = CostNetwork.add(s, contribution(now, j, null));
    }
    return s == HARD ? Long.MAX_VALUE : Math.ceilDiv(s, r.scale);
  }

  private synchronized void reparametrise() {
    if (r != null) {
      return;
    }
    long start = System.nanoTime();
    CostNetwork net = network;
    List<int[]> removed = new ArrayList<>();
    for (int i = 0; i < x.length; i++) {
      for (int a = 0; a < values[i].length; a++) {
        if (!x[i].domain.contains(values[i][a])) {
          net.unary[i][a] = HARD;
          removed.add(new int[] {i, values[i][a]});
        }
      }
    }
    String dump = System.getProperty("org.jacop.cfn.dump");
    if (dump != null) {
      try (java.io.PrintWriter w =
          new java.io.PrintWriter(dump, java.nio.charset.StandardCharsets.UTF_8)) {
        net.writeWcsp(w);
      } catch (java.io.IOException e) {
        throw new java.io.UncheckedIOException(e);
      }
    }
    Reparam p = new Reparam();
    CostNetwork.Solution s;
    try {
      s = net.solve(start + ROOT_MS * 1_000_000L, SWEEPS);
    } catch (ArithmeticException e) {
      // costs too large to scale: no bound
      s = null;
    }
    network = null;
    if (s == null) {
      p.scale = 1;
      p.c0 = Long.MIN_VALUE / 4;
      p.u = new long[x.length][];
      for (int i = 0; i < x.length; i++) {
        p.u[i] = new long[values[i].length];
      }
      p.ei = new int[0];
      p.ej = new int[0];
      p.ef = new long[0][];
    } else {
      p.scale = s.scale;
      p.c0 = s.constant;
      p.u = s.unary;
      p.ei = s.edgeFirst;
      p.ej = s.edgeSecond;
      p.ef = s.edgeCost;
      sweeps = s.sweeps;
      merged = s.mergedCount();
      startBound = s.trace[0] == HARD ? Long.MAX_VALUE : Math.ceilDiv(s.trace[0], p.scale);
    }
    p.assumed = removed.toArray(new int[0][]);
    int[] degree = new int[x.length];
    for (int e = 0; e < p.ei.length; e++) {
      degree[p.ei[e]]++;
      degree[p.ej[e]]++;
    }
    p.adj = new int[x.length][];
    for (int i = 0; i < x.length; i++) {
      p.adj[i] = new int[degree[i]];
      degree[i] = 0;
    }
    for (int e = 0; e < p.ei.length; e++) {
      p.adj[p.ei[e]][degree[p.ei[e]]++] = e;
      p.adj[p.ej[e]][degree[p.ej[e]]++] = e;
    }
    p.order = new int[x.length][];
    List<Integer> rel = new ArrayList<>();
    for (int i = 0; i < x.length; i++) {
      long[] ui = p.u[i];
      Integer[] o = new Integer[ui.length];
      for (int a = 0; a < o.length; a++) {
        o[a] = a;
      }
      Arrays.sort(o, (a, b) -> Long.compare(ui[a], ui[b]));
      p.order[i] = new int[o.length];
      for (int a = 0; a < o.length; a++) {
        p.order[i][a] = o[a];
      }
      boolean constant = o.length > 0 && ui[o[0]] == ui[o[o.length - 1]] && ui[o[0]] != HARD;
      if (constant) {
        // the same cost for every value: part of c0
        p.c0 = CostNetwork.add(p.c0, ui[o[0]]);
        Arrays.fill(ui, 0);
      }
      if (!constant || p.adj[i].length > 0) {
        rel.add(i);
      }
    }
    p.relevant = rel.stream().mapToInt(Integer::intValue).toArray();
    r = p;
    seconds = (System.nanoTime() - start) / 1e9;
    rootBound = currentBound();
  }

  // ---- the domains the bound is computed over: the store's now, or the trail's before a position

  private interface View {
    boolean fixed(int i);

    int value(int i);

    boolean allowed(int i, int v);
  }

  private final View now =
      new View() {
        @Override
        public boolean fixed(int i) {
          return x[i].singleton();
        }

        @Override
        public int value(int i) {
          return x[i].value();
        }

        @Override
        public boolean allowed(int i, int v) {
          return x[i].domain.contains(v);
        }
      };

  private final class Before implements View {
    final AtomicTrail trail;
    final int position;

    Before(AtomicTrail trail, int position) {
      this.trail = trail;
      this.position = position;
    }

    @Override
    public boolean fixed(int i) {
      return trail.minBefore(x[i], position) == trail.maxBefore(x[i], position);
    }

    @Override
    public int value(int i) {
      return trail.minBefore(x[i], position);
    }

    @Override
    public boolean allowed(int i, int v) {
      if (!trail.rootDomain(x[i]).contains(v)) {
        return false;
      }
      int mark = scratch.size();
      boolean out = trail.excludedBefore(x[i], v, position, scratch);
      scratch.truncate(mark);
      return !out;
    }
  }

  // whether edge e counts towards variable j: its other end is fixed, and j is not, or comes after
  private boolean receives(View view, int j, int e) {
    int k = r.ei[e] == j ? r.ej[e] : r.ei[e];
    return view.fixed(k) && (!view.fixed(j) || k < j);
  }

  // the cost of value a of j with the binary costs towards the edges it receives
  private long cost(View view, int j, int a) {
    long c = r.u[j][a];
    if (c == HARD) {
      return HARD;
    }
    for (int e : r.adj[j]) {
      if (receives(view, j, e)) {
        boolean first = r.ei[e] == j;
        int k = first ? r.ej[e] : r.ei[e];
        int b = Arrays.binarySearch(values[k], view.value(k));
        if (b < 0) {
          // a value outside the network: no assignment of it has a cost
          return HARD;
        }
        int dk = values[k].length;
        int dj = values[j].length;
        long f = first ? r.ef[e][a * dk + b] : r.ef[e][b * dj + a];
        c = CostNetwork.add(c, f);
        if (c == HARD) {
          return HARD;
        }
      }
    }
    return c;
  }

  // the least cost of j over the allowed values; with unaryOnly[0] set, without binary costs
  private long contribution(View view, int j, boolean[] unaryOnly) {
    boolean plain = unaryOnly != null && unaryOnly[0];
    boolean edges = false;
    if (!plain) {
      for (int e : r.adj[j]) {
        if (receives(view, j, e)) {
          edges = true;
          break;
        }
      }
    }
    long best = HARD;
    int[] vs = values[j];
    for (int a : r.order[j]) {
      long ua = r.u[j][a];
      if (ua == HARD || ua >= best) {
        break;
      }
      if (view.allowed(j, vs[a])) {
        long c = edges ? cost(view, j, a) : ua;
        best = Math.min(best, c);
        if (!edges) {
          break;
        }
      }
    }
    return best;
  }

  // the contributions of the last propagation, valid while the domain of the variable (its object
  // and size: a domain object only shrinks at its level) and the values of its fixed neighbours are
  // the same
  private IntDomain[] cacheDomain;
  private int[] cacheSize;
  private int[][] cacheNeighbours;
  private long[] cacheLeast;
  private long[] cacheMost;

  private static final int NOT_FIXED = Integer.MIN_VALUE;

  // whether the cached contribution of j is still valid; updates the neighbour values if not
  private boolean cached(int j) {
    IntVar xj = x[j];
    boolean valid = cacheDomain[j] == xj.domain && cacheSize[j] == xj.domain.getSize();
    int[] adj = r.adj[j];
    int[] nb = cacheNeighbours[j];
    for (int q = 0; q < adj.length; q++) {
      int e = adj[q];
      IntVar k = x[r.ei[e] == j ? r.ej[e] : r.ei[e]];
      int sig = k.singleton() ? k.value() : NOT_FIXED;
      if (nb[q] != sig) {
        nb[q] = sig;
        valid = false;
      }
    }
    if (!valid) {
      cacheDomain[j] = xj.domain;
      cacheSize[j] = xj.domain.getSize();
    }
    return valid;
  }

  // the least and the most finite cost of the values of j in its domain
  private void evaluate(int j) {
    IntVar xj = x[j];
    long least = HARD;
    long most = Long.MIN_VALUE;
    long[] uj = r.u[j];
    int[] vs = values[j];
    boolean edges = r.adj[j].length > 0;
    for (int a : r.order[j]) {
      if (uj[a] == HARD) {
        break;
      }
      if (xj.domain.contains(vs[a])) {
        long c = edges ? cost(now, j, a) : uj[a];
        least = Math.min(least, c);
        if (c != HARD) {
          most = Math.max(most, c);
        }
      }
    }
    cacheLeast[j] = least;
    cacheMost[j] = most;
  }

  @Override
  public void consistency(Store store) {
    if (r == null) {
      reparametrise();
    }
    if (cacheDomain == null) {
      cacheDomain = new IntDomain[x.length];
      cacheSize = new int[x.length];
      cacheLeast = new long[x.length];
      cacheMost = new long[x.length];
      cacheNeighbours = new int[x.length][];
      for (int j = 0; j < x.length; j++) {
        cacheNeighbours[j] = new int[r.adj[j].length];
        Arrays.fill(cacheNeighbours[j], NOT_FIXED + 1);
      }
    }
    // fixing a variable with binary costs changes the costs of its neighbours: again until none is
    while (bound(store)) {
      // again
    }
  }

  // one pass of the bound and its removals; true when a variable with binary costs got fixed
  private boolean bound(Store store) {
    int[] rel = r.relevant;
    long s = r.c0;
    for (int j : rel) {
      if (!cached(j)) {
        evaluate(j);
      }
      s = CostNetwork.add(s, cacheLeast[j]);
    }
    if (s == HARD) {
      throw Store.failException;
    }
    long scale = r.scale;
    long lb = Math.ceilDiv(s, scale);
    if (maximize) {
      if (lb > -(long) objective.min()) {
        throw Store.failException;
      }
      if (-lb > Integer.MIN_VALUE) {
        objective.domain.inMax(store.level, objective, (int) Math.max(-lb, Integer.MIN_VALUE));
      }
    } else {
      if (lb > objective.max()) {
        throw Store.failException;
      }
      if (lb > Integer.MIN_VALUE) {
        objective.domain.inMin(store.level, objective, (int) Math.min(lb, Integer.MAX_VALUE));
      }
    }
    long top = maximize ? -(long) objective.min() : objective.max();
    long slack = top * scale - s;
    boolean again = false;
    for (int j : rel) {
      IntVar xj = x[j];
      if (!PRUNE || xj.singleton() || cacheMost[j] - cacheLeast[j] <= slack) {
        continue;
      }
      // a value costing more than the least by the slack lifts the bound past the objective
      long over = cacheLeast[j] + slack;
      long[] uj = r.u[j];
      int[] o = r.order[j];
      int[] vs = values[j];
      boolean edges = r.adj[j].length > 0;
      for (int p = o.length - 1; p >= 0; p--) {
        int a = o[p];
        if (uj[a] == HARD || !xj.domain.contains(vs[a])) {
          continue;
        }
        long ca = edges ? cost(now, j, a) : uj[a];
        if (ca != HARD && ca > over) {
          prunings++;
          xj.domain.inComplement(store.level, xj, vs[a]);
        } else if (!edges && uj[a] <= over) {
          // without binary costs the values are sorted by cost: the cheaper ones stay
          break;
        }
      }
      again |= edges && xj.singleton();
    }
    return again;
  }

  // ---- explanations

  // the least unary cost of j over its root domain
  private long leastRoot(AtomicTrail trail, int j) {
    IntDomain root = trail.rootDomain(x[j]);
    for (int a : r.order[j]) {
      if (r.u[j][a] == HARD || root.contains(values[j][a])) {
        return r.u[j][a];
      }
    }
    return HARD;
  }

  // the values of the fixed neighbours whose binary costs j receives
  private void addNeighbours(Before view, int j, EntryList out) {
    for (int e : r.adj[j]) {
      if (receives(view, j, e)) {
        IntVar k = x[r.ei[e] == j ? r.ej[e] : r.ei[e]];
        view.trail.addLowerBound(k, view.position, out);
        view.trail.addUpperBound(k, view.position, out);
      }
    }
  }

  // the removals of the values of j cheaper than level, by unary cost alone or with edges
  private boolean addCheaper(Before view, int j, long level, boolean edges, EntryList out) {
    IntDomain root = view.trail.rootDomain(x[j]);
    int[] vs = values[j];
    for (int a : r.order[j]) {
      long ua = r.u[j][a];
      if (ua >= level) {
        break;
      }
      if (!root.contains(vs[a])) {
        continue;
      }
      if ((!edges || cost(view, j, a) < level)
          && !view.trail.excludedBefore(x[j], vs[a], view.position, out)) {
        return false;
      }
    }
    return true;
  }

  // the exclusions of the values the reparametrisation assumed absent
  private boolean addAssumed(Before view, EntryList out) {
    for (int[] a : r.assumed) {
      IntVar v = x[a[0]];
      if (view.trail.rootDomain(v).contains(a[1])
          && !view.trail.excludedBefore(v, a[1], view.position, out)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Adds the atoms that make c0 + the contributions of the variables other than skip at least need
   * just before the view's position, lifted.
   */
  private boolean reason(Before view, long need, int skip, EntryList out) {
    int start = out.size();
    int[] rel = r.relevant;
    int n = rel.length;
    long[] full = new long[n];
    long[] plain = new long[n];
    long[] base = new long[n];
    boolean[] unaryOnly = {true};
    long s = r.c0;
    for (int k = 0; k < n; k++) {
      int j = rel[k];
      if (j == skip) {
        continue;
      }
      full[k] = contribution(view, j, null);
      plain[k] = contribution(view, j, unaryOnly);
      base[k] = leastRoot(view.trail, j);
      if (base[k] == HARD) {
        return false;
      }
      if (full[k] == HARD) {
        // no value of j is left with its fixed neighbours: that alone exceeds any need
        out.truncate(start);
        addNeighbours(view, j, out);
        return addCheaper(view, j, HARD, true, out) && addAssumed(view, out);
      }
      s += full[k];
    }
    long slack = s - need;
    if (slack < 0) {
      return false;
    }
    if (!addAssumed(view, out)) {
      return false;
    }
    // the variables that gained least first: they are left out while the slack covers them
    Integer[] by = new Integer[n];
    for (int k = 0; k < n; k++) {
      by[k] = k;
    }
    Arrays.sort(by, (p, q) -> Long.compare(full[p] - base[p], full[q] - base[q]));
    for (int k : by) {
      int j = rel[k];
      if (j == skip) {
        continue;
      }
      long gain = full[k] - base[k];
      if (gain <= slack) {
        slack -= gain;
        continue;
      }
      long level = full[k] - slack;
      slack = 0;
      if (level <= plain[k]) {
        if (!addCheaper(view, j, level, false, out)) {
          return false;
        }
      } else {
        addNeighbours(view, j, out);
        if (!addCheaper(view, j, level, true, out)) {
          return false;
        }
      }
    }
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (r == null) {
      return false;
    }
    IntVar v = trail.variable(entry);
    int kind = trail.kind(entry);
    Before view = new Before(trail, entry);
    long scale = r.scale;
    if (v == objective) {
      if (maximize ? kind != AtomicTrail.LE : kind != AtomicTrail.GE) {
        return false;
      }
      long bound = maximize ? -(long) trail.value(entry) : trail.value(entry);
      return reason(view, (bound - 1) * scale + 1, -1, out);
    }
    int j = -1;
    for (int k = 0; k < x.length; k++) {
      if (x[k] == v) {
        j = k;
        break;
      }
    }
    if (j < 0) {
      return false;
    }
    // the values the atom removes that were in the domain before it: each passes the bound
    int lo = trail.removedMin(entry);
    int hi = trail.removedMax(entry);
    if ((long) hi - lo >= 100_000) {
      return false;
    }
    IntDomain root = trail.rootDomain(v);
    int start = out.size();
    long cheapPlain = HARD;
    long cheapFull = HARD;
    for (int w = lo; w <= hi; w++) {
      if (!root.contains(w)) {
        continue;
      }
      int a = Arrays.binarySearch(values[j], w);
      if (trail.excludedBefore(v, w, entry, out)) {
        continue;
      }
      if (a < 0 || r.u[j][a] == HARD) {
        // a value this constraint did not remove
        return false;
      }
      cheapPlain = Math.min(cheapPlain, r.u[j][a]);
      cheapFull = Math.min(cheapFull, cost(view, j, a));
    }
    if (cheapPlain == HARD) {
      return true;
    }
    long top =
        maximize ? -(long) trail.minBefore(objective, entry) : trail.maxBefore(objective, entry);
    addObjectiveBound(trail, entry, top, out);
    int mark = out.size();
    if (reason(view, top * scale + 1 - cheapPlain, j, out)) {
      return true;
    }
    out.truncate(mark);
    if (cheapFull == HARD) {
      out.truncate(start);
      return false;
    }
    addNeighbours(view, j, out);
    return reason(view, top * scale + 1 - cheapFull, j, out);
  }

  private void addObjectiveBound(AtomicTrail trail, int position, long top, EntryList out) {
    if (maximize) {
      if (trail.rootDomain(objective).min() < -top) {
        trail.addBoundReaching(objective, position, true, -top, out);
      }
    } else if (trail.rootDomain(objective).max() > top) {
      trail.addBoundReaching(objective, position, false, top, out);
    }
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (r == null) {
      return false;
    }
    int position = trail.size();
    long top =
        maximize
            ? -(long) trail.minBefore(objective, position)
            : trail.maxBefore(objective, position);
    addObjectiveBound(trail, position, top, out);
    return reason(new Before(trail, position), top * r.scale + 1, -1, out);
  }

  @Override
  public CostNetworkBound copy(VarMap map) {
    if (r == null) {
      reparametrise();
    }
    return new CostNetworkBound(this, map.get(objective), map.get(x));
  }

  @Override
  public String toString() {
    return id()
        + " : CostNetworkBound("
        + objective
        + (maximize ? ", max" : ", min")
        + ", variables "
        + x.length
        + ")";
  }
}
