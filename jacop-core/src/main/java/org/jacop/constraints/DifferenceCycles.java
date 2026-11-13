/*
 * DifferenceCycles.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * It fails as soon as the difference constraints that hold make a cycle of negative weight. Each
 * difference constraint {@code x[i] - y[i] <= c[i]} holds always ({@code b[i] == null}) or when its
 * 0/1 variable has a given value ({@code b[i] == v[i]}), as the half-reified and reified
 * precedences of disjunctive scheduling models do. The constraint is redundant: the difference
 * constraints are posted on their own as well. It does not prune; it only fails earlier.
 *
 * <p>Bounds propagation on a cycle of negative weight moves the bounds by the weight of the cycle
 * each time round it, so it fails only after about (domain width) / |weight| rounds, and the reason
 * it gives for the failure under lazy clause generation is a long chain of bound literals. This
 * constraint fails when the last literal of the cycle becomes true, and the reason is the literals
 * of the cycle alone.
 *
 * <p>The graph has a node for each variable and an arc {@code y[i] -> x[i]} of weight {@code c[i]}
 * for each difference constraint. The constraint keeps a potential function {@code pi} that is
 * feasible for the arcs that hold, {@code pi(x) <= pi(y) + c}. When an arc becomes active and
 * violates it, the potential is repaired by a Dijkstra-like search over reduced costs that starts
 * at the head of the new arc; the arcs hold a cycle of negative weight exactly when the search
 * reaches the tail of the new arc. This is the incremental negative-cycle detection of Ramalingam,
 * Song, Joskowicz and Miller, as used for difference logic in DPLL(T) by Cotton and Maler. A
 * potential that is feasible for some arcs stays feasible for fewer arcs, so backtracking does not
 * touch it. The first potential is computed for the arcs that always hold by Bellman-Ford with a
 * queue, with a cycle check of the parent pointers in the manner of Tarjan.
 *
 * <p>An arc may also have an offset variable {@code o}: {@code x - y <= c - s * o} with {@code s =
 * 1} or {@code -1}, as in {@code y >= x + d} with a variable duration d or a variable travel time.
 * Its weight is then {@code c - min(o)} or {@code c + max(o)} at the current bounds, and a bound of
 * o that moves re-inserts the arc. Such weights only decrease down a branch, so the potential stays
 * feasible on backtracking, and the bound of o joins the reason of a cycle. A literal may also be
 * any variable: the arc holds when the literal is fixed to its value, as the arcs {@code z = a[j]}
 * of an element {@code z = a[k]} hold for {@code k = j}. Such a literal is explained by both of its
 * bounds. These are the precedences with variable offsets of CP-SAT (Perron, Didier and Gay) and
 * the global difference constraint propagation of Feydy, Schutt and Stuckey, here used for cycle
 * detection only.
 *
 * <p>Only the arcs inside a strongly connected component of the graph of all arcs can be on a
 * cycle, so the others are dropped when the constraint is built, as are the arcs of fixed variables
 * ({@link #conditionalArcs()} tells how many conditional arcs remain).
 *
 * <p>References:
 *
 * <ul>
 *   <li>S. Cotton and O. Maler, Fast and Flexible Difference Constraint Propagation for DPLL(T), in
 *       Theory and Applications of Satisfiability Testing (SAT 2006), LNCS 4121, Springer, 2006,
 *       pp. 170-183.
 *   <li>T. Feydy, A. Schutt and P. J. Stuckey, Global Difference Constraint Propagation for Finite
 *       Domain Solvers, in Principles and Practice of Declarative Programming (PPDP 2008), ACM,
 *       2008, pp. 226-235.
 *   <li>L. Perron, F. Didier and S. Gay, The CP-SAT-LP Solver, invited talk, in Principles and
 *       Practice of Constraint Programming (CP 2023), LIPIcs 280, 2023, pp. 3:1-3:2.
 *   <li>G. Ramalingam, J. Song, L. Joskowicz and R. E. Miller, Solving Systems of Difference
 *       Constraints Incrementally, Algorithmica 23(3), 1999, pp. 261-275.
 *   <li>R. E. Tarjan, Shortest Paths, AT&amp;T Bell Laboratories technical memorandum, 1981; see
 *       also B. V. Cherkassky and A. V. Goldberg, Negative-Cycle Detection Algorithms, Mathematical
 *       Programming 85(2), 1999, pp. 277-311.
 * </ul>
 *
 * <p>The same scheme extends to constraints with two variables per inequality ({@code a x + b y <=
 * c}, TVPI), for which Hochbaum and Naor give the closure, and to the unit case {@code +-x +-y <=
 * c} (UTVPI), for which Schutt and Stuckey give incremental satisfiability and implication; this
 * class covers the difference case only:
 *
 * <ul>
 *   <li>D. S. Hochbaum and J. Naor, Simple and Fast Algorithms for Linear and Integer Programs with
 *       Two Variables per Inequality, SIAM Journal on Computing 23(6), 1994, pp. 1179-1192.
 *   <li>A. Schutt and P. J. Stuckey, Incremental Satisfiability and Implication for UTVPI
 *       Constraints, INFORMS Journal on Computing 22(4), 2010, pp. 514-527.
 * </ul>
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class DifferenceCycles extends Constraint
    implements UsesQueueVariable, Stateful, Explainable, Copyable<DifferenceCycles> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * The most arc relaxations of the first Bellman-Ford pass (property
   * jacop.differenceCycles.budget).
   */
  static final long BUDGET = Long.getLong("jacop.differenceCycles.budget", 50_000_000L);

  // the arguments, for copy and toString
  private final IntVar[] xs;
  private final IntVar[] ys;
  private final int[] cs;
  private final IntVar[] bs;
  private final int[] vs;
  private final IntVar[] os;
  private final int[] ss;

  // nodes
  private final IntVar[] node;

  // arc k: node[head[k]] - node[tail[k]] <= weight[k] when lit[k] < 0 or literal[lit[k]] ==
  // value[k]
  private final int[] tail;
  private final int[] head;
  private final long[] weight;
  private final int[] lit;
  private final int[] value;
  private final int[] off;
  private final int[] offSign;

  // the arcs leaving each node: out[start[n] .. start[n + 1])
  private final int[] start;
  private final int[] out;

  // the distinct 0/1 variables and their arcs: arcsOf[litStart[l] .. litStart[l + 1])
  private final IntVar[] literal;
  private final int[] litStart;
  private final int[] arcsOf;
  private final Map<Var, Integer> literalIndex = new IdentityHashMap<>();

  private final IntVar[] offset;
  private final int[] offStart;
  private final int[] arcsOfOffset;
  private final Map<Var, Integer> offsetIndex = new IdentityHashMap<>();

  // BOUND events when an arc has an offset or a literal that is not 0/1, else GROUND
  private final boolean boundEvents;

  private final int conditional;

  // the potential, feasible for the arcs that hold and are not pending
  private long[] pi;
  private boolean infeasible;
  private boolean disabled;
  private boolean first = true;

  // arcs that hold but are not in the potential yet
  private boolean[] pending;

  // the search of insert: gamma[n] < 0 is the change of pi[n]; heap of the nodes with gamma < 0
  private long[] gamma;
  private int[] parentArc;
  private boolean[] done;
  private int[] heap;
  private int[] heapPos;
  private int heapSize;
  private int[] touched;
  private int touchedSize;

  // the arcs of the last cycle found, for the explanation of the failure
  private int[] cycle = new int[0];
  private int cycleSize;

  // 0/1 variables fixed since the last consistency call
  private final List<Var> queue = new ArrayList<>();

  private long cyclesFound;

  /**
   * It creates the constraint over difference constraints {@code x[i] - y[i] <= c[i]}, each of
   * which holds always ({@code b[i] == null}) or when {@code b[i] == v[i]}.
   *
   * @param x the variables with coefficient 1.
   * @param y the variables with coefficient -1.
   * @param c the constants.
   * @param b the 0/1 variables of the conditional difference constraints, or null entries.
   * @param v the values of b under which the difference constraints hold.
   */
  public DifferenceCycles(IntVar[] x, IntVar[] y, int[] c, IntVar[] b, int[] v) {
    this(x, y, c, b, v, new IntVar[x.length], new int[x.length]);
  }

  /**
   * It creates the constraint over difference constraints {@code x[i] - y[i] <= c[i] - s[i] *
   * o[i]}, each of which holds always ({@code b[i] == null}) or when {@code b[i] == v[i]}. An
   * offset variable {@code o[i]} (null for none) makes the weight of the arc depend on its bound:
   * {@code c[i] - min(o[i])} for {@code s[i] = 1} and {@code c[i] + max(o[i])} for {@code s[i] =
   * -1}, as in {@code y = x + d} with a variable duration d. A literal {@code b[i]} may be any
   * variable: the arc holds once it is fixed to {@code v[i]}, as the arcs {@code z = a[j]} of an
   * element {@code z = a[k]} hold for {@code k = j}.
   *
   * @param x the variables with coefficient 1.
   * @param y the variables with coefficient -1.
   * @param c the constants.
   * @param b the variables of the conditional difference constraints, or null entries.
   * @param v the values of b under which the difference constraints hold.
   * @param o the offset variables, or null entries.
   * @param s the signs of the offsets, 1 or -1 (ignored for a null offset).
   */
  public DifferenceCycles(
      IntVar[] x, IntVar[] y, int[] c, IntVar[] b, int[] v, IntVar[] o, int[] s) {
    checkInputForNullness(new String[] {"x", "y"}, new Object[][] {x, y});
    checkInputForNullness(new String[] {"c", "b", "v", "o", "s"}, new Object[] {c, b, v, o, s});
    int m = x.length;
    if (y.length != m
        || c.length != m
        || b.length != m
        || v.length != m
        || o.length != m
        || s.length != m) {
      throw new IllegalArgumentException("DifferenceCycles: the arrays have different lengths");
    }
    for (int i = 0; i < m; i++) {
      if (o[i] != null && s[i] != 1 && s[i] != -1) {
        throw new IllegalArgumentException(
            "DifferenceCycles: the sign " + s[i] + " is not 1 or -1");
      }
    }
    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 0;
    this.xs = x;
    this.ys = y;
    this.cs = c;
    this.bs = b;
    this.vs = v;
    this.os = o;
    this.ss = s;

    // nodes and all arcs
    Map<IntVar, Integer> nodeIndex = new IdentityHashMap<>();
    List<IntVar> nodes = new ArrayList<>();
    int[] t = new int[m];
    int[] h = new int[m];
    for (int i = 0; i < m; i++) {
      t[i] = nodeIndex.computeIfAbsent(y[i], k -> addNode(nodes, k));
      h[i] = nodeIndex.computeIfAbsent(x[i], k -> addNode(nodes, k));
    }
    int n = nodes.size();
    // a cycle through a fixed variable is bounds reasoning, which propagation does in one pass
    // along it; dropping its arcs only loses failures that come early anyway
    for (int i = 0; i < m; i++) {
      if (x[i].singleton() || y[i].singleton()) {
        h[i] = t[i];
      }
    }
    int[] component = components(n, t, h);

    // the arcs inside a strongly connected component, without loops
    int kept = 0;
    int cond = 0;
    for (int i = 0; i < m; i++) {
      if (t[i] != h[i] && component[t[i]] == component[h[i]]) {
        kept++;
        if (b[i] != null) {
          cond++;
        }
      }
    }
    this.conditional = cond;
    tail = new int[kept];
    head = new int[kept];
    weight = new long[kept];
    lit = new int[kept];
    value = new int[kept];
    off = new int[kept];
    offSign = new int[kept];
    List<IntVar> literals = new ArrayList<>();
    List<IntVar> offsets = new ArrayList<>();
    boolean bounds = false;
    int k = 0;
    for (int i = 0; i < m; i++) {
      if (t[i] != h[i] && component[t[i]] == component[h[i]]) {
        tail[k] = t[i];
        head[k] = h[i];
        weight[k] = c[i];
        value[k] = v[i];
        if (o[i] == null) {
          off[k] = -1;
        } else {
          bounds = true;
          offSign[k] = s[i];
          Integer l = offsetIndex.get(o[i]);
          if (l == null) {
            l = offsets.size();
            offsetIndex.put(o[i], l);
            offsets.add(o[i]);
          }
          off[k] = l;
        }
        bounds |= b[i] != null && (b[i].min() < 0 || b[i].max() > 1);
        if (b[i] == null) {
          lit[k] = -1;
        } else {
          Integer l = literalIndex.get(b[i]);
          if (l == null) {
            l = literals.size();
            literalIndex.put(b[i], l);
            literals.add(b[i]);
          }
          lit[k] = l;
        }
        k++;
      }
    }
    node = nodes.toArray(new IntVar[0]);
    literal = literals.toArray(new IntVar[0]);
    offset = offsets.toArray(new IntVar[0]);
    boundEvents = bounds;

    start = new int[n + 1];
    out = new int[kept];
    for (int a = 0; a < kept; a++) {
      start[tail[a] + 1]++;
    }
    for (int i = 0; i < n; i++) {
      start[i + 1] += start[i];
    }
    int[] fill = Arrays.copyOf(start, n);
    for (int a = 0; a < kept; a++) {
      out[fill[tail[a]]++] = a;
    }

    int nl = literal.length;
    litStart = new int[nl + 1];
    arcsOf = new int[cond];
    for (int a = 0; a < kept; a++) {
      if (lit[a] >= 0) {
        litStart[lit[a] + 1]++;
      }
    }
    for (int l = 0; l < nl; l++) {
      litStart[l + 1] += litStart[l];
    }
    int[] lfill = Arrays.copyOf(litStart, nl);
    for (int a = 0; a < kept; a++) {
      if (lit[a] >= 0) {
        arcsOf[lfill[lit[a]]++] = a;
      }
    }

    int no = offset.length;
    offStart = new int[no + 1];
    int withOffset = 0;
    for (int a = 0; a < kept; a++) {
      if (off[a] >= 0) {
        offStart[off[a] + 1]++;
        withOffset++;
      }
    }
    for (int l = 0; l < no; l++) {
      offStart[l + 1] += offStart[l];
    }
    arcsOfOffset = new int[withOffset];
    int[] ofill = Arrays.copyOf(offStart, no);
    for (int a = 0; a < kept; a++) {
      if (off[a] >= 0) {
        arcsOfOffset[ofill[off[a]]++] = a;
      }
    }

    List<IntVar> scope = new ArrayList<>(literals);
    for (IntVar ov : offset) {
      if (!literalIndex.containsKey(ov)) {
        scope.add(ov);
      }
    }
    setScope(scope.toArray(new IntVar[0]));
  }

  // the weight of arc a now: its constant less the bound of its offset
  private long weightOf(int a) {
    if (off[a] < 0) {
      return weight[a];
    }
    IntVar o = offset[off[a]];
    return offSign[a] > 0 ? weight[a] - o.min() : weight[a] + o.max();
  }

  private static int addNode(List<IntVar> nodes, IntVar v) {
    nodes.add(v);
    return nodes.size() - 1;
  }

  /**
   * It tells how many conditional difference constraints can be on a cycle. With none, the
   * constraint never fails and need not be imposed.
   *
   * @return the number of conditional arcs inside strongly connected components.
   */
  public int conditionalArcs() {
    return conditional;
  }

  /**
   * It tells how many arcs with an offset variable can be on a cycle.
   *
   * @return the number of arcs with offsets inside strongly connected components.
   */
  public int offsetArcs() {
    return arcsOfOffset.length;
  }

  /**
   * It tells how many cycles of negative weight it has found.
   *
   * @return the number of failures of this constraint.
   */
  public long cyclesFound() {
    return cyclesFound;
  }

  // the strongly connected components of the graph of all arcs (Tarjan, iterative)
  static int[] components(int n, int[] t, int[] h) {
    int m = t.length;
    int[] st = new int[n + 1];
    for (int a = 0; a < m; a++) {
      st[t[a] + 1]++;
    }
    for (int i = 0; i < n; i++) {
      st[i + 1] += st[i];
    }
    int[] adj = new int[m];
    int[] fill = Arrays.copyOf(st, n);
    for (int a = 0; a < m; a++) {
      adj[fill[t[a]]++] = h[a];
    }
    int[] index = new int[n];
    Arrays.fill(index, -1);
    int[] low = new int[n];
    int[] comp = new int[n];
    boolean[] onStack = new boolean[n];
    int[] stack = new int[n];
    int sp = 0;
    int[] call = new int[n];
    int[] edge = new int[n];
    int counter = 0;
    int components = 0;
    for (int r = 0; r < n; r++) {
      if (index[r] >= 0) {
        continue;
      }
      int depth = 0;
      call[0] = r;
      edge[0] = st[r];
      index[r] = low[r] = counter++;
      stack[sp++] = r;
      onStack[r] = true;
      while (depth >= 0) {
        int u = call[depth];
        if (edge[depth] < st[u + 1]) {
          int w = adj[edge[depth]++];
          if (index[w] < 0) {
            index[w] = low[w] = counter++;
            stack[sp++] = w;
            onStack[w] = true;
            depth++;
            call[depth] = w;
            edge[depth] = st[w];
          } else if (onStack[w]) {
            low[u] = Math.min(low[u], index[w]);
          }
        } else {
          if (low[u] == index[u]) {
            int w;
            do {
              w = stack[--sp];
              onStack[w] = false;
              comp[w] = components;
            } while (w != u);
            components++;
          }
          depth--;
          if (depth >= 0) {
            int p = call[depth];
            low[p] = Math.min(low[p], low[u]);
          }
        }
      }
    }
    return comp;
  }

  @Override
  public void impose(Store store) {
    int n = node.length;
    pi = new long[n];
    gamma = new long[n];
    parentArc = new int[n];
    done = new boolean[n];
    heap = new int[n];
    heapPos = new int[n];
    Arrays.fill(heapPos, -1);
    touched = new int[n];
    pending = new boolean[tail.length];
    initialPotential();
    super.impose(store);
  }

  // Bellman-Ford with a queue over the arcs that always hold, from pi = 0
  private void initialPotential() {
    int n = node.length;
    int[] parent = new int[n];
    Arrays.fill(parent, -1);
    int[] length = new int[n];
    boolean[] queued = new boolean[n];
    int[] q = new int[n];
    int qh = 0;
    int qs = n;
    for (int i = 0; i < n; i++) {
      q[i] = i;
      queued[i] = true;
    }
    long work = 0;
    int polls = 0;
    while (qs > 0) {
      int u = q[qh];
      qh = (qh + 1) % n;
      qs--;
      queued[u] = false;
      for (int e = start[u]; e < start[u + 1]; e++) {
        int a = out[e];
        // an arc with an offset is left to the first consistency, so that a cycle found here
        // needs no reason and does not depend on the bounds of the offsets when it is imposed
        if (lit[a] >= 0 || off[a] >= 0) {
          continue;
        }
        int w = head[a];
        long d = pi[u] + weight[a];
        if (d < pi[w]) {
          pi[w] = d;
          parent[w] = u;
          length[w] = length[u] + 1;
          if (length[w] > n) {
            infeasible = true;
            return;
          }
          if (!queued[w]) {
            queued[w] = true;
            q[(qh + qs) % n] = w;
            qs++;
          }
        }
      }
      work += start[u + 1] - start[u];
      if (++polls % n == 0 && hasCycle(parent)) {
        infeasible = true;
        return;
      }
      if (work > BUDGET) {
        disabled = true;
        return;
      }
    }
  }

  // whether the parent pointers make a cycle, in O(n)
  private static boolean hasCycle(int[] parent) {
    int n = parent.length;
    byte[] state = new byte[n];
    for (int i = 0; i < n; i++) {
      int v = i;
      while (v >= 0 && state[v] == 0) {
        state[v] = 1;
        v = parent[v];
      }
      if (v >= 0 && state[v] == 1) {
        return true;
      }
      for (v = i; v >= 0 && state[v] == 1; v = parent[v]) {
        state[v] = 2;
      }
    }
    return false;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return boundEvents ? IntDomain.BOUND : IntDomain.GROUND;
  }

  @Override
  public void queueVariable(int level, Var v) {
    queue.add(v);
  }

  @Override
  public void removeLevel(int level) {
    queue.clear();
  }

  @Override
  public void cleanAfterFailure() {
    queue.clear();
  }

  private boolean holds(int a) {
    if (lit[a] < 0) {
      return true;
    }
    IntVar b = literal[lit[a]];
    return b.singleton() && b.value() == value[a];
  }

  @Override
  public void consistency(Store store) {
    if (disabled) {
      queue.clear();
      return;
    }
    cycleSize = 0;
    if (infeasible) {
      throw Store.failException;
    }
    if (first) {
      first = false;
      queue.clear();
      queue.addAll(Arrays.asList(literal));
      queue.addAll(Arrays.asList(offset));
    }
    // the arcs that hold now and may not be in the potential yet
    int[] arcs = new int[8];
    int na = 0;
    for (Var v : queue) {
      Integer l = literalIndex.get(v);
      if (l != null) {
        for (int i = litStart[l]; i < litStart[l + 1]; i++) {
          int a = arcsOf[i];
          if (!pending[a] && holds(a)) {
            pending[a] = true;
            if (na == arcs.length) {
              arcs = Arrays.copyOf(arcs, 2 * na);
            }
            arcs[na++] = a;
          }
        }
      }
      // an offset that moved tightens its arcs
      Integer k = offsetIndex.get(v);
      if (k != null) {
        for (int i = offStart[k]; i < offStart[k + 1]; i++) {
          int a = arcsOfOffset[i];
          if (!pending[a] && holds(a)) {
            pending[a] = true;
            if (na == arcs.length) {
              arcs = Arrays.copyOf(arcs, 2 * na);
            }
            arcs[na++] = a;
          }
        }
      }
    }
    queue.clear();
    int next = 0;
    try {
      for (; next < na; next++) {
        int a = arcs[next];
        pending[a] = false;
        insert(a);
      }
    } finally {
      for (; next < na; next++) {
        pending[arcs[next]] = false;
      }
    }
  }

  // adds arc a, which holds, to the potential, or fails with the cycle it closes
  private void insert(int a) {
    int u = tail[a];
    int v = head[a];
    long g = pi[u] + weightOf(a) - pi[v];
    if (g >= 0) {
      return;
    }
    try {
      touch(v);
      gamma[v] = g;
      parentArc[v] = a;
      push(v);
      while (heapSize > 0) {
        int s = pop();
        done[s] = true;
        long ps = pi[s] + gamma[s];
        for (int e = start[s]; e < start[s + 1]; e++) {
          int arc = out[e];
          int w = head[arc];
          if (done[w] || pending[arc] || !holds(arc)) {
            continue;
          }
          long ng = ps + weightOf(arc) - pi[w];
          if (ng < gamma[w]) {
            if (w == u) {
              recordCycle(arc, a);
              cyclesFound++;
              throw Store.failException;
            }
            touch(w);
            gamma[w] = ng;
            parentArc[w] = arc;
            push(w);
          }
        }
      }
      for (int i = 0; i < touchedSize; i++) {
        int s = touched[i];
        pi[s] += gamma[s];
      }
    } finally {
      for (int i = 0; i < touchedSize; i++) {
        int s = touched[i];
        gamma[s] = 0;
        done[s] = false;
        heapPos[s] = -1;
      }
      touchedSize = 0;
      heapSize = 0;
    }
  }

  // the cycle: arc a into v, the parent arcs from v to the tail of last, and last into tail of a
  private void recordCycle(int last, int a) {
    cycleSize = 0;
    addCycleArc(last);
    int x = tail[last];
    int v = head[a];
    while (x != v) {
      int p = parentArc[x];
      addCycleArc(p);
      x = tail[p];
    }
    addCycleArc(a);
  }

  private void addCycleArc(int a) {
    if (cycleSize == cycle.length) {
      cycle = Arrays.copyOf(cycle, Math.max(8, 2 * cycleSize));
    }
    cycle[cycleSize++] = a;
  }

  private void touch(int s) {
    if (heapPos[s] == -1 && !done[s] && gamma[s] == 0) {
      // first time in this search
      heapPos[s] = -2;
      touched[touchedSize++] = s;
    }
  }

  // binary heap of nodes by gamma; heapPos is -2 for touched nodes not in the heap
  private void push(int s) {
    int i = heapPos[s];
    if (i < 0) {
      i = heapSize++;
      heap[i] = s;
      heapPos[s] = i;
    }
    while (i > 0) {
      int p = (i - 1) >> 1;
      if (gamma[heap[p]] <= gamma[s]) {
        break;
      }
      heap[i] = heap[p];
      heapPos[heap[i]] = i;
      i = p;
    }
    heap[i] = s;
    heapPos[s] = i;
  }

  private int pop() {
    int top = heap[0];
    heapPos[top] = -2;
    int last = heap[--heapSize];
    if (heapSize > 0) {
      int i = 0;
      while (true) {
        int l = 2 * i + 1;
        if (l >= heapSize) {
          break;
        }
        int r = l + 1;
        int c = r < heapSize && gamma[heap[r]] < gamma[heap[l]] ? r : l;
        if (gamma[heap[c]] >= gamma[last]) {
          break;
        }
        heap[i] = heap[c];
        heapPos[heap[i]] = i;
        i = c;
      }
      heap[i] = last;
      heapPos[last] = i;
    }
    return top;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    // it prunes nothing
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (infeasible) {
      // the arcs that always hold have a cycle of negative weight
      return true;
    }
    if (cycleSize == 0) {
      return false;
    }
    int now = trail.size();
    for (int i = 0; i < cycleSize; i++) {
      int a = cycle[i];
      if (lit[a] >= 0) {
        IntVar b = literal[lit[a]];
        // whether one bound fixes the literal depends on its root domain, not on the current one
        boolean zeroOne = trail.minBefore(b, 0) >= 0 && trail.maxBefore(b, 0) <= 1;
        if (!zeroOne || value[a] == 1) {
          trail.addLowerBound(b, now, out);
        }
        if (!zeroOne || value[a] != 1) {
          trail.addUpperBound(b, now, out);
        }
      }
      if (off[a] >= 0) {
        IntVar o = offset[off[a]];
        if (offSign[a] > 0) {
          trail.addLowerBound(o, now, out);
        } else {
          trail.addUpperBound(o, now, out);
        }
      }
    }
    return true;
  }

  @Override
  public DifferenceCycles copy(VarMap map) {
    // only the literals are in the scope, so presolve may fix or eliminate a variable of a
    // difference constraint and give it no counterpart: such an arc is left out, which only loses
    // cycles, as for an arc of a fixed variable
    List<IntVar> x = new ArrayList<>();
    List<IntVar> y = new ArrayList<>();
    List<Integer> c = new ArrayList<>();
    List<IntVar> b = new ArrayList<>();
    List<Integer> v = new ArrayList<>();
    List<IntVar> o = new ArrayList<>();
    List<Integer> sign = new ArrayList<>();
    for (int i = 0; i < xs.length; i++) {
      IntVar xi = map.get(xs[i]);
      IntVar yi = map.get(ys[i]);
      IntVar bi = bs[i] == null ? null : map.get(bs[i]);
      IntVar oi = os[i] == null ? null : map.get(os[i]);
      if (xi == null || yi == null) {
        continue;
      }
      // a literal without a counterpart holds always only when it is fixed to its value
      if (bs[i] != null && bi == null && (!bs[i].singleton() || bs[i].value() != vs[i])) {
        continue;
      }
      long ci = cs[i];
      if (os[i] != null && oi == null) {
        // an offset without a counterpart must be fixed, and its value joins the constant
        if (!os[i].singleton()) {
          continue;
        }
        ci -= (long) ss[i] * os[i].value();
        if (ci < Integer.MIN_VALUE || ci > Integer.MAX_VALUE) {
          continue;
        }
      }
      x.add(xi);
      y.add(yi);
      c.add((int) ci);
      b.add(bi);
      v.add(vs[i]);
      o.add(oi);
      sign.add(ss[i]);
    }
    return new DifferenceCycles(
        x.toArray(new IntVar[0]),
        y.toArray(new IntVar[0]),
        c.stream().mapToInt(Integer::intValue).toArray(),
        b.toArray(new IntVar[0]),
        v.stream().mapToInt(Integer::intValue).toArray(),
        o.toArray(new IntVar[0]),
        sign.stream().mapToInt(Integer::intValue).toArray());
  }

  @Override
  public String toString() {
    return id()
        + " : DifferenceCycles("
        + node.length
        + " nodes, "
        + tail.length
        + " arcs, "
        + conditional
        + " conditional)";
  }
}
