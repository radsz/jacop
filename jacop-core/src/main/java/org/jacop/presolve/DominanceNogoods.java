/*
 * DominanceNogoods.java
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

package org.jacop.presolve;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.LongUnaryOperator;
import org.jacop.api.Monotone;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.AbstractReifiedConstraint;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.Reified;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.ValueIndicator;

/**
 * Automatic dominance breaking nogoods for constraint optimisation problems, after Lee and Zhong:
 * <em>Automatic dominance breaking for a class of constraint optimization problems</em>, IJCAI
 * 2020, pp. 1192-1200; <em>Exploiting functional constraints in automatic dominance breaking for
 * constraint optimization</em>, CP 2022 (LIPIcs 235, 31:1-31:17) and JAIR 78, 2023.
 *
 * <p>A partial assignment {@code theta} of a set {@code S} of at most two variables is a dominance
 * breaking nogood when another assignment {@code theta'} of {@code S} exists such that every
 * solution that extends {@code theta} stays a solution when {@code S} takes {@code theta'} instead,
 * with a strictly better objective. No optimal solution then extends {@code theta}, so the nogood
 * can be imposed; since every nogood only removes solutions that are not optimal, all of them can
 * be imposed together, with the constraints the store already has (for example symmetry breaking)
 * and without an order of the variables.
 *
 * <p>The changed solution is checked constraint by constraint without knowing the rest of the
 * solution, as in the papers' generation CSPs:
 *
 * <ul>
 *   <li>a linear relation {@code sum w * v <= c} holds again when {@code sum w * delta(v) <= 0}, an
 *       equality when {@code sum w * delta(v) = 0};
 *   <li>a {@link Monotone} constraint holds again when every variable moves in a direction the
 *       constraint leaves free;
 *   <li>{@code b -> c} with linear {@code c}: when {@code c} holds again and {@code b} does not
 *       rise; {@code b <-> c}: when the left-hand side of {@code c} is unchanged and {@code b}
 *       stays;
 *   <li>any other constraint: when none of its variables changes.
 * </ul>
 *
 * <p>Functional constraints (the CP 2022 paper) are linear equalities {@code z = sum w * v} with
 * unit weight on {@code z}, whose domain is an interval covering every value of the sum: when an
 * input changes, {@code z} follows it, and the constraints of {@code z} are checked with its
 * change. The objective follows its own definition the same way; its domain needs to cover only the
 * improving side. The objective change must be strictly improving.
 *
 * <p>Nogoods on one variable remove values; nogoods on two 0/1 variables are imposed as clauses,
 * those on two other variables as one table of the allowed pairs. Pairs are taken from the
 * constraints, shortest first, with at least one variable the objective depends on, and the search
 * stops after a budget of work (the system property {@code jacop.dominance.budget}).
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class DominanceNogoods {

  /**
   * What the rule found.
   *
   * @param removed values removed by nogoods on one variable.
   * @param pairs pairs of variables with at least one nogood.
   * @param nogoods nogoods on two variables.
   * @param imposed constraints imposed for them.
   * @param checked pairs of variables checked.
   * @param complete true if the budget sufficed for all pairs.
   * @param skipped why the rule did not run, or null.
   */
  public record Outcome(
      int removed,
      int pairs,
      long nogoods,
      int imposed,
      long checked,
      boolean complete,
      String skipped) {}

  private static final long BUDGET = Long.getLong("jacop.dominance.budget", 50_000_000L);
  private static final long TIME = Long.getLong("jacop.dominance.time", 1000L) * 1_000_000L;
  private static final int MAX_DOMAIN = Integer.getInteger("jacop.dominance.domain", 16);
  private static final int MAX_FOLLOWERS = 64;
  private static final long UNDEFINED = Long.MIN_VALUE;
  private static final long MAX_NOGOODS = Long.getLong("jacop.dominance.nogoods", 200_000L);

  // the constraints: a linear part (relation, variables, weights) and the variables outside it
  // with the directions in which each may move
  private static final int NONE = 0;
  private static final int LE = 1;
  private static final int EQ = 2;

  private final Store store;
  private final IntVar objective;
  private final boolean minimize;

  private final List<IntVar> vars = new ArrayList<>();
  private final Map<Var, Integer> index = new IdentityHashMap<>();
  private int[] relation;
  private int[][] linVars;
  private long[][] linWeights;
  private int[][] freeVars;
  private int[][] freeDirs;
  private int[][] varCons;
  // the defining equality of a variable and its weight there, or -1
  private long[] constants;
  private int[] definition;
  // functional constraints read by value, per row; the one defining a variable; inputs of any
  private LongUnaryOperator[] valueOf;
  private int[] valIn;
  private int[] valOut;
  private int[] valueDefinition;
  private boolean[] valueInput;
  private long[] definitionWeight;
  private int obj = -1;

  // per move scratch
  private long[] delta;
  private int[] state;
  private final List<Integer> touched = new ArrayList<>();
  private boolean[] known;
  private long[] oldValue;
  private long[] newValue;
  private int movedX;
  private int[] rank;
  private final java.util.PriorityQueue<Long> queue = new java.util.PriorityQueue<>();
  private int movedY;
  private long work;

  /**
   * Prepares the rule.
   *
   * @param store the store, at a fixpoint.
   * @param objective the objective variable.
   * @param minimize true if the objective is minimised.
   */
  public DominanceNogoods(Store store, IntVar objective, boolean minimize) {
    this.store = store;
    this.objective = objective;
    this.minimize = minimize;
  }

  /**
   * Finds the nogoods and imposes them.
   *
   * @return what was found.
   */
  public Outcome run() {
    return run(List.of());
  }

  /**
   * Finds the nogoods and imposes them.
   *
   * @param clauses clauses of the model kept outside the store, each as its positive and its
   *     negative variables.
   * @return what was found.
   */
  public Outcome run(List<IntVar[][]> clauses) {
    if (objective == null || objective.singleton()) {
      return new Outcome(0, 0, 0, 0, 0, true, "no objective");
    }
    long deadline = System.nanoTime() + TIME;
    List<Var> all = Derivation.variables(store);
    List<Constraint> live = new ArrayList<>();
    for (Constraint c : Derivation.constraints(store, all)) {
      if (!(c instanceof SatisfiedPresent s && s.satisfied())) {
        live.add(c);
      }
    }
    read(live, clauses);
    Integer o = index.get(objective);
    if (o == null) {
      return new Outcome(0, 0, 0, 0, 0, true, "objective in no constraint");
    }
    obj = o;
    definitions();
    ranks();
    if (definition[obj] < 0) {
      return new Outcome(0, 0, 0, 0, 0, true, "objective not defined by a linear equality");
    }
    boolean[] reaches = reachesObjective();
    boolean[] candidate = new boolean[vars.size()];
    for (int v = 0; v < vars.size(); v++) {
      IntVar x = vars.get(v);
      candidate[v] = v != obj && !x.singleton() && x.getSize() <= MAX_DOMAIN && movable(v);
    }
    delta = new long[vars.size()];
    state = new int[vars.size()];
    known = new boolean[vars.size()];
    oldValue = new long[vars.size()];
    newValue = new long[vars.size()];
    if (DEBUG) {
      debug(reaches, candidate);
    }

    // nogoods on one variable
    List<int[]> removals = new ArrayList<>();
    boolean[][] dominated = new boolean[vars.size()][];
    boolean complete = true;
    for (int v = 0; v < vars.size(); v++) {
      if (!candidate[v] || !reaches[v]) {
        continue;
      }
      if ((v & 63) == 0 && System.nanoTime() > deadline) {
        complete = false;
        break;
      }
      int[] d = values(vars.get(v));
      for (int i = 0; i < d.length; i++) {
        for (int j = 0; j < d.length; j++) {
          if (i != j && valid(v, d[i], d[j], -1, 0, 0)) {
            if (dominated[v] == null) {
              dominated[v] = new boolean[d.length];
            }
            dominated[v][i] = true;
            removals.add(new int[] {v, d[i]});
            break;
          }
        }
      }
    }

    // nogoods on two variables, from the shortest constraints first
    Integer[] order = new Integer[relation.length];
    for (int c = 0; c < order.length; c++) {
      order[c] = c;
    }
    Arrays.sort(order, (a, b) -> Integer.compare(scope(a).length, scope(b).length));
    Set<Long> seen = new HashSet<>();
    long checked = 0;
    long nogoods = 0;
    int pairs = 0;
    int imposed = 0;
    List<Constraint> posted = new ArrayList<>();
    outer:
    for (int c : complete ? order : new Integer[0]) {
      int[] scope = scope(c);
      for (int i = 0; i < scope.length; i++) {
        int x = scope[i];
        if (!candidate[x]) {
          continue;
        }
        for (int j = i + 1; j < scope.length; j++) {
          int y = scope[j];
          if (!candidate[y] || x == y || !(reaches[x] || reaches[y])) {
            continue;
          }
          long key = Math.min(x, y) * (long) vars.size() + Math.max(x, y);
          if (!seen.add(key)) {
            continue;
          }
          if (work > BUDGET
              || nogoods >= MAX_NOGOODS
              || (checked & 63) == 0 && System.nanoTime() > deadline) {
            complete = false;
            break outer;
          }
          checked++;
          List<int[]> found = pair(x, y, dominated);
          if (!found.isEmpty()) {
            pairs++;
            nogoods += found.size();
            posted.addAll(constraints(vars.get(x), vars.get(y), found));
          }
        }
      }
    }
    for (int[] r : removals) {
      IntVar x = vars.get(r[0]);
      x.domain.inComplement(store.level, x, r[1]);
    }
    for (Constraint c : posted) {
      store.impose(c);
      imposed++;
    }
    return new Outcome(removals.size(), pairs, nogoods, imposed, checked, complete, null);
  }

  /** The nogoods on x and y that are not implied by those on one variable. */
  private List<int[]> pair(int x, int y, boolean[][] dominated) {
    int[] dx = values(vars.get(x));
    int[] dy = values(vars.get(y));
    // without functional constraints read by value, whether a move is valid depends only on the
    // changes, so it is computed once for each pair of changes
    boolean byChange = !valueInput[x] && !valueInput[y];
    Map<Long, Boolean> moves = new HashMap<>();
    List<int[]> found = new ArrayList<>();
    for (int i = 0; i < dx.length; i++) {
      if (dominated[x] != null && dominated[x][i]) {
        continue;
      }
      for (int j = 0; j < dy.length; j++) {
        if (dominated[y] != null && dominated[y][j]) {
          continue;
        }
        search:
        for (int a = 0; a < dx.length; a++) {
          if (a == i) {
            continue;
          }
          for (int b = 0; b < dy.length; b++) {
            if (b == j) {
              continue;
            }
            boolean ok;
            if (byChange) {
              long key = ((long) (dx[a] - dx[i]) << 32) ^ ((dy[b] - dy[j]) & 0xffffffffL);
              Boolean known = moves.get(key);
              if (known == null) {
                known = valid(x, dx[i], dx[a], y, dy[j], dy[b]);
                moves.put(key, known);
              }
              ok = known;
            } else {
              ok = valid(x, dx[i], dx[a], y, dy[j], dy[b]);
            }
            if (ok) {
              found.add(new int[] {dx[i], dy[j]});
              break search;
            }
          }
        }
      }
    }
    return found;
  }

  private static List<Constraint> constraints(IntVar x, IntVar y, List<int[]> nogoods) {
    List<Constraint> result = new ArrayList<>();
    if (x.min() >= 0 && x.max() <= 1 && y.min() >= 0 && y.max() <= 1) {
      for (int[] n : nogoods) {
        // not (x = a and y = b): x != a or y != b
        List<IntVar> pos = new ArrayList<>();
        List<IntVar> neg = new ArrayList<>();
        (n[0] == 1 ? neg : pos).add(x);
        (n[1] == 1 ? neg : pos).add(y);
        result.add(new BoolClause(pos, neg));
      }
      return result;
    }
    Set<Long> forbidden = new HashSet<>();
    for (int[] n : nogoods) {
      forbidden.add(((long) n[0] << 32) ^ (n[1] & 0xffffffffL));
    }
    List<int[]> allowed = new ArrayList<>();
    for (int a : values(x)) {
      for (int b : values(y)) {
        if (!forbidden.contains(((long) a << 32) ^ (b & 0xffffffffL))) {
          allowed.add(new int[] {a, b});
        }
      }
    }
    result.add(new HybridTable(new IntVar[] {x, y}, allowed.toArray(new int[0][])));
    return result;
  }

  /**
   * True if moving x from xa to xb, and y from ya to yb (y may be -1), keeps every solution a
   * solution with a strictly better objective.
   */
  private boolean valid(int x, int xa, int xb, int y, int ya, int yb) {
    for (int v : touched) {
      delta[v] = 0;
      state[v] = 0;
      known[v] = false;
    }
    touched.clear();
    movedX = x;
    movedY = y;
    set(x, xa, xb);
    if (y >= 0) {
      set(y, ya, yb);
    }
    // the followers reached from the changed variables, by rank, so that the changed inputs of a
    // follower are computed before it
    queue.clear();
    discover(x);
    if (y >= 0) {
      discover(y);
    }
    int followers = 0;
    while (!queue.isEmpty()) {
      int z = (int) (queue.poll() & 0xffffffffL);
      if (!compute(z)) {
        return false;
      }
      if (delta[z] != 0) {
        if (++followers > MAX_FOLLOWERS) {
          return false;
        }
        discover(z);
      }
    }
    long d = delta[obj];
    if (minimize ? d >= 0 : d <= 0) {
      return false;
    }
    // every constraint of a changed variable holds again
    for (int v : touched) {
      if (delta[v] == 0) {
        continue;
      }
      for (int c : varCons[v]) {
        work++;
        if (!holds(c)) {
          return false;
        }
      }
    }
    return true;
  }

  private void set(int v, long from, long to) {
    delta[v] = to - from;
    oldValue[v] = from;
    newValue[v] = to;
    known[v] = true;
    state[v] = 2;
    touched.add(v);
  }

  /** Queues the followers defined from v. */
  private void discover(int v) {
    for (int c : varCons[v]) {
      work++;
      int z = -1;
      if (relation[c] == EQ) {
        z = definedBy(c);
      } else if (valueOf[c] != null && valIn[c] == v && valueDefinition[valOut[c]] == c) {
        z = valOut[c];
      }
      if (z >= 0 && state[z] == 0) {
        state[z] = 1;
        touched.add(z);
        queue.add(((long) rank[z] << 32) | z);
      }
    }
  }

  /** Computes the change of the follower u from its definition, whose inputs are final. */
  private boolean compute(int u) {
    work++;
    if (valueDefinition[u] >= 0) {
      int c = valueDefinition[u];
      int in = valIn[c];
      if (delta[in] != 0) {
        if (!known[in]) {
          return false;
        }
        long from = valueOf[c].applyAsLong(oldValue[in]);
        long to = valueOf[c].applyAsLong(newValue[in]);
        if (from == UNDEFINED || to == UNDEFINED || !vars.get(u).dom().contains((int) to)) {
          return false;
        }
        delta[u] = to - from;
        oldValue[u] = from;
        newValue[u] = to;
        known[u] = true;
      }
    } else {
      int c = definition[u];
      long sum = 0;
      for (int k = 0; k < linVars[c].length; k++) {
        int w = linVars[c][k];
        if (w != u) {
          sum += linWeights[c][k] * delta[w];
        }
      }
      // w * u + sum = const
      delta[u] = -sum * definitionWeight[u];
    }
    state[u] = 2;
    return true;
  }

  /**
   * Ranks the defined variables: one more than the largest rank of their inputs, 0 for others. A
   * definition on a cycle of definitions is dropped.
   */
  private void ranks() {
    rank = new int[vars.size()];
    int[] mark = new int[vars.size()];
    for (int v = 0; v < vars.size(); v++) {
      rank(v, mark, 0);
    }
  }

  private int rank(int v, int[] mark, int depth) {
    if (mark[v] == 2) {
      return rank[v];
    }
    if (mark[v] == 1 || depth > 2000) {
      return -1;
    }
    int[] inputs = inputs(v);
    if (inputs.length == 0) {
      mark[v] = 2;
      rank[v] = 0;
      return 0;
    }
    mark[v] = 1;
    int r = 0;
    for (int u : inputs) {
      int ru = rank(u, mark, depth + 1);
      if (ru < 0) {
        // v closes a cycle, or the chain is too long: v is no longer defined
        definition[v] = -1;
        valueDefinition[v] = -1;
        r = -1;
        break;
      }
      r = Math.max(r, ru + 1);
    }
    mark[v] = 2;
    rank[v] = Math.max(r, 0);
    return rank[v];
  }

  private int[] inputs(int v) {
    if (valueDefinition[v] >= 0) {
      return new int[] {valIn[valueDefinition[v]]};
    }
    if (definition[v] >= 0) {
      int c = definition[v];
      return Arrays.stream(linVars[c]).filter(u -> u != v).toArray();
    }
    return new int[0];
  }

  private int definedBy(int c) {
    for (int v : linVars[c]) {
      if (definition[v] == c) {
        return v;
      }
    }
    return -1;
  }

  private boolean holds(int c) {
    if (valueOf[c] != null) {
      int in = valIn[c];
      int out = valOut[c];
      if (valueDefinition[out] == c && !moved(out)) {
        // a follower, computed from this constraint
        return true;
      }
      if (delta[in] == 0 && delta[out] == 0) {
        return true;
      }
      return known[in] && known[out] && valueOf[c].applyAsLong(newValue[in]) == newValue[out];
    }
    if (relation[c] != NONE) {
      long s = 0;
      for (int k = 0; k < linVars[c].length; k++) {
        s += linWeights[c][k] * delta[linVars[c][k]];
      }
      if (relation[c] == LE ? s > 0 : s != 0) {
        return false;
      }
    }
    for (int k = 0; k < freeVars[c].length; k++) {
      long d = delta[freeVars[c][k]];
      if (d > 0 && (freeDirs[c][k] & Monotone.INCREASE) == 0) {
        return false;
      }
      if (d < 0 && (freeDirs[c][k] & Monotone.DECREASE) == 0) {
        return false;
      }
    }
    return true;
  }

  private boolean moved(int v) {
    return v == movedX || v == movedY;
  }

  private boolean movable(int v) {
    for (int c : varCons[v]) {
      for (int k = 0; k < freeVars[c].length; k++) {
        if (freeVars[c][k] == v && freeDirs[c][k] == 0) {
          return false;
        }
      }
    }
    return true;
  }

  private int[] scope(int c) {
    int[] a = linVars[c];
    int[] b = freeVars[c];
    int[] r = Arrays.copyOf(a, a.length + b.length);
    System.arraycopy(b, 0, r, a.length, b.length);
    return r;
  }

  private static int[] values(IntVar x) {
    int[] r = new int[x.getSize()];
    int i = 0;
    for (ValueEnumeration e = x.dom().valueEnumeration(); e.hasMoreElements(); ) {
      r[i++] = e.nextElement();
    }
    return r;
  }

  /** The variables whose change can reach the objective through definitions. */
  private boolean[] reachesObjective() {
    boolean[] r = new boolean[vars.size()];
    List<Integer> queue = new ArrayList<>();
    r[obj] = true;
    queue.add(obj);
    for (int k = 0; k < queue.size(); k++) {
      int z = queue.get(k);
      int vd = valueDefinition[z];
      if (vd >= 0 && !r[valIn[vd]]) {
        r[valIn[vd]] = true;
        queue.add(valIn[vd]);
      }
      int c = definition[z];
      if (c < 0) {
        continue;
      }
      for (int u : linVars[c]) {
        if (!r[u]) {
          r[u] = true;
          queue.add(u);
        }
      }
    }
    return r;
  }

  private void debug(boolean[] reaches, boolean[] candidate) {
    Map<String, Integer> blocking = new java.util.TreeMap<>();
    int inputs = 0;
    int cands = 0;
    for (int v = 0; v < vars.size(); v++) {
      if (!reaches[v] || v == obj) {
        continue;
      }
      inputs++;
      if (candidate[v]) {
        cands++;
      }
      for (int c : varCons[v]) {
        for (int k = 0; k < freeVars[c].length; k++) {
          if (freeVars[c][k] == v && freeDirs[c][k] == 0) {
            blocking.merge(origins[c], 1, Integer::sum);
          }
        }
      }
    }
    System.out.println(
        "%% dominance debug: objective inputs "
            + inputs
            + ", candidates "
            + cands
            + ", locked by "
            + blocking
            + ", objective definition "
            + origins[definition[obj]]
            + " of "
            + linVars[definition[obj]].length);
  }

  // ---- reading the constraints

  private int id(Var v) {
    Integer i = index.get(v);
    if (i == null) {
      i = vars.size();
      index.put(v, i);
      vars.add((IntVar) v);
    }
    return i;
  }

  /** One row: a linear part and the variables outside it with the directions each may move. */
  private static final class Row {
    int relation = NONE;
    long constant;
    int[] linVars = new int[0];
    long[] linWeights = new long[0];
    int[] freeVars = new int[0];
    int[] freeDirs = new int[0];
    String origin = "clause";
    // a functional constraint read by value: out = valueOf(in)
    LongUnaryOperator valueOf;
    int valIn = -1;
    int valOut = -1;
  }

  private final List<Row> rows = new ArrayList<>();
  private String[] origins;
  private static final boolean DEBUG = Boolean.getBoolean("jacop.dominance.debug");

  private void read(List<Constraint> live, List<IntVar[][]> clauses) {
    for (Constraint c : live) {
      read(c);
    }
    for (IntVar[][] c : clauses) {
      clause(c);
    }
    int n = rows.size();
    constants = new long[n];
    relation = new int[n];
    linVars = new int[n][];
    linWeights = new long[n][];
    freeVars = new int[n][];
    freeDirs = new int[n][];
    for (int c = 0; c < n; c++) {
      Row r = rows.get(c);
      constants[c] = r.constant;
      relation[c] = r.relation;
      linVars[c] = r.linVars;
      linWeights[c] = r.linWeights;
      freeVars[c] = r.freeVars;
      freeDirs[c] = r.freeDirs;
    }
    origins = new String[n];
    valueOf = new LongUnaryOperator[n];
    valIn = new int[n];
    valOut = new int[n];
    for (int c = 0; c < n; c++) {
      Row r = rows.get(c);
      origins[c] = r.origin;
      valueOf[c] = r.valueOf;
      valIn[c] = r.valIn;
      valOut[c] = r.valOut;
    }
    rows.clear();
    List<List<Integer>> byVar = new ArrayList<>();
    for (int v = 0; v < vars.size(); v++) {
      byVar.add(new ArrayList<>());
    }
    for (int c = 0; c < n; c++) {
      for (int v : linVars[c]) {
        addOnce(byVar.get(v), c);
      }
      for (int v : freeVars[c]) {
        addOnce(byVar.get(v), c);
      }
      if (valueOf[c] != null) {
        addOnce(byVar.get(valIn[c]), c);
        addOnce(byVar.get(valOut[c]), c);
      }
    }
    valueDefinition = new int[vars.size()];
    Arrays.fill(valueDefinition, -1);
    valueInput = new boolean[vars.size()];
    for (int c = 0; c < n; c++) {
      if (valueOf[c] != null) {
        valueInput[valIn[c]] = true;
        if (valueDefinition[valOut[c]] < 0) {
          valueDefinition[valOut[c]] = c;
        }
      }
    }
    varCons = new int[vars.size()][];
    for (int v = 0; v < vars.size(); v++) {
      varCons[v] = byVar.get(v).stream().mapToInt(Integer::intValue).toArray();
    }
  }

  private static void addOnce(List<Integer> list, int c) {
    if (list.isEmpty() || list.getLast() != c) {
      list.add(c);
    }
  }

  /** The linear relations a constraint is exactly, or null. */
  private static LinearForm[] exact(Constraint con) {
    if (con instanceof Knapsack k) {
      return k.rows();
    }
    LinearForm form = LinearForms.of(con);
    if (form == null) {
      form = Locks.form(con);
    }
    return form == null || form.relation() == LinearForm.NE ? null : new LinearForm[] {form};
  }

  private void read(Constraint con) {
    if (functional(con)) {
      return;
    }
    LinearForm[] forms = exact(con);
    Map<Var, Integer> free = new IdentityHashMap<>();
    if (forms != null) {
      Set<Var> in = Collections.newSetFromMap(new IdentityHashMap<>());
      for (LinearForm form : forms) {
        Row row = new Row();
        row.origin = con.getClass().getSimpleName();
        linear(row, form, form.relation() == LinearForm.EQ ? EQ : LE);
        rows.add(row);
        in.addAll(Arrays.asList(form.vars()));
      }
      for (Var v : con.arguments()) {
        if (!in.contains(v)) {
          free.put(v, 0);
        }
      }
      if (!free.isEmpty()) {
        Row row = new Row();
        row.origin = con.getClass().getSimpleName() + "-extra";
        freeVars(row, free);
        rows.add(row);
      }
      return;
    }
    Row row = new Row();
    row.origin = con.getClass().getSimpleName();
    if (con instanceof AbstractReifiedConstraint r
        && (r instanceof Implies || r instanceof Reified)
        && exact(r.c) instanceof LinearForm[] fs
        && fs.length == 1
        && !r.c.arguments().contains(r.b)) {
      boolean implies = r instanceof Implies;
      LinearForm f = fs[0];
      linear(row, f, implies && f.relation() != LinearForm.EQ ? LE : EQ);
      Set<Var> in = Collections.newSetFromMap(new IdentityHashMap<>());
      in.addAll(Arrays.asList(f.vars()));
      for (Var v : r.c.arguments()) {
        if (!in.contains(v)) {
          free.put(v, 0);
        }
      }
      free.put(r.b, implies ? Monotone.DECREASE : 0);
    } else {
      Monotone m = con instanceof Monotone mm ? mm : null;
      for (Var v : con.arguments()) {
        free.put(v, m == null ? 0 : m.freeDirections(v));
      }
    }
    freeVars(row, free);
    rows.add(row);
  }

  /**
   * Reads a constraint that makes one variable a function of one other: {@code b <-> x = c} (a
   * {@link ValueIndicator}), {@code b <-> c(x)} for a linear {@code c} over one variable, and
   * {@code z = list[x]}. Such a constraint is checked by value (CP 2022's functional constraints).
   */
  private boolean functional(Constraint con) {
    IntVar in = null;
    IntVar out = null;
    LongUnaryOperator f = null;
    if (con instanceof ValueIndicator vi && vi.indicator() != null) {
      in = vi.variable();
      out = vi.indicator();
      int value = vi.value();
      f = v -> v == value ? 1 : 0;
    } else if (con instanceof Reified r && Locks.form(r.c) instanceof LinearForm form) {
      Map<IntVar, Long> weights = Locks.merged(form);
      long fixed = 0;
      for (Map.Entry<IntVar, Long> e : weights.entrySet()) {
        if (e.getKey().singleton()) {
          fixed += e.getValue() * e.getKey().value();
        } else if (e.getValue() != 0) {
          if (in != null) {
            return false;
          }
          in = e.getKey();
        }
      }
      if (in == null) {
        return false;
      }
      long w = weights.get(in);
      long k = form.c() - fixed;
      int rel = form.relation();
      out = r.b;
      f =
          v -> {
            long lhs = w * v;
            boolean holds =
                switch (rel) {
                  case LinearForm.LE -> lhs <= k;
                  case LinearForm.GE -> lhs >= k;
                  case LinearForm.EQ -> lhs == k;
                  default -> lhs != k;
                };
            return holds ? 1 : 0;
          };
    } else if (con instanceof ElementInteger e) {
      in = e.index();
      out = e.value();
      f = element(e.values(), e.indexOffset());
    } else if (con instanceof ElementIntegerFast e) {
      in = e.index();
      out = e.value();
      f = element(e.values(), e.indexOffset());
    }
    if (f == null || in == out || in.singleton() || out.singleton()) {
      return false;
    }
    Row row = new Row();
    row.origin = con.getClass().getSimpleName();
    row.valueOf = f;
    row.valIn = id(in);
    row.valOut = id(out);
    rows.add(row);
    return true;
  }

  private static LongUnaryOperator element(int[] list, int offset) {
    return v -> {
      long i = v - 1 - offset;
      return i < 0 || i >= list.length ? UNDEFINED : list[(int) i];
    };
  }

  /**
   * A clause holds again when its positive variables do not fall and its negative ones not rise.
   */
  private void clause(IntVar[][] clause) {
    Map<Var, Integer> free = new IdentityHashMap<>();
    for (IntVar v : clause[0]) {
      free.merge(v, Monotone.INCREASE, (a, b) -> a & b);
    }
    for (IntVar v : clause[1]) {
      free.merge(v, Monotone.DECREASE, (a, b) -> a & b);
    }
    Row row = new Row();
    freeVars(row, free);
    rows.add(row);
  }

  private void freeVars(Row row, Map<Var, Integer> free) {
    List<Integer> fv = new ArrayList<>();
    List<Integer> fd = new ArrayList<>();
    for (Map.Entry<Var, Integer> e : free.entrySet()) {
      if (e.getKey() instanceof IntVar && !e.getKey().singleton()) {
        fv.add(id(e.getKey()));
        fd.add(e.getValue());
      }
    }
    row.freeVars = fv.stream().mapToInt(Integer::intValue).toArray();
    row.freeDirs = fd.stream().mapToInt(Integer::intValue).toArray();
  }

  private void linear(Row row, LinearForm form, int rel) {
    Map<IntVar, Long> weights = Locks.merged(form);
    long sign = form.relation() == LinearForm.GE ? -1 : 1;
    List<Integer> vs = new ArrayList<>();
    List<Long> ws = new ArrayList<>();
    long fixed = 0;
    for (Map.Entry<IntVar, Long> e : weights.entrySet()) {
      if (e.getKey().singleton()) {
        fixed += e.getValue() * e.getKey().value();
      } else if (e.getValue() != 0) {
        vs.add(id(e.getKey()));
        ws.add(sign * e.getValue());
      }
    }
    row.relation = rel;
    row.constant = sign * (form.c() - fixed);
    row.linVars = vs.stream().mapToInt(Integer::intValue).toArray();
    row.linWeights = ws.stream().mapToLong(Long::longValue).toArray();
  }

  /**
   * Picks the defining equalities: the objective's first, then for each other equality the variable
   * with unit weight and an interval domain covering its sum, the largest such.
   */
  private void definitions() {
    definition = new int[vars.size()];
    definitionWeight = new long[vars.size()];
    Arrays.fill(definition, -1);
    boolean[] used = new boolean[relation.length];
    for (int c : varCons[obj]) {
      if (relation[c] == EQ && freeVars[c].length == 0 && covers(c, obj, true)) {
        definition[obj] = c;
        definitionWeight[obj] = weight(c, obj);
        used[c] = true;
        break;
      }
    }
    for (int c = 0; c < relation.length; c++) {
      if (used[c] || relation[c] != EQ || freeVars[c].length > 0 || linVars[c].length < 2) {
        continue;
      }
      int best = -1;
      for (int v : linVars[c]) {
        if (v != obj
            && definition[v] < 0
            && valueDefinition[v] < 0
            && covers(c, v, false)
            && (best < 0 || vars.get(v).getSize() > vars.get(best).getSize())) {
          best = v;
        }
      }
      if (best >= 0) {
        definition[best] = c;
        definitionWeight[best] = weight(c, best);
        used[c] = true;
      }
    }
  }

  private long weight(int c, int v) {
    for (int k = 0; k < linVars[c].length; k++) {
      if (linVars[c][k] == v) {
        return linWeights[c][k];
      }
    }
    return 0;
  }

  /**
   * True if v has unit weight in the equality c and an interval domain that holds every value the
   * rest of c gives it (for the objective, every value on the improving side).
   */
  private boolean covers(int c, int v, boolean objectiveSide) {
    long w = weight(c, v);
    if (Math.abs(w) != 1) {
      return false;
    }
    IntDomain d = vars.get(v).dom();
    if (d.getSize() != (long) d.max() - d.min() + 1) {
      return false;
    }
    long low = 0;
    long high = 0;
    for (int k = 0; k < linVars[c].length; k++) {
      int u = linVars[c][k];
      if (u == v) {
        continue;
      }
      long a = -w * linWeights[c][k];
      IntVar x = vars.get(u);
      low += Math.min(a * x.min(), a * x.max());
      high += Math.max(a * x.min(), a * x.max());
    }
    // w * v + rest = k, so v = w * k - w * rest
    long k = w * constants[c];
    if (objectiveSide) {
      return minimize ? d.min() <= k + low : d.max() >= k + high;
    }
    return d.min() <= k + low && d.max() >= k + high;
  }
}
