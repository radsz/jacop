/*
 * SatPresolve.java
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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.AndBoolVector;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.OrBoolSimple;
import org.jacop.constraints.OrBoolVector;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XgteqY;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqY;
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * SAT preprocessing of the clauses of a store (presolve rule 9): the constraints that are clauses
 * over 0/1 variables ({@link BoolClause}, and implications, equalities, disjunctions and negated
 * conjunctions of two or more 0/1 variables) and clauses kept outside the store, for the SAT solver
 * of {@code -sat} or lazy clause generation, form one clause set, which is simplified as in SAT
 * solvers (Biere, Järvisalo and Kiesl, <i>Preprocessing in SAT solving</i>, 2021):
 *
 * <ul>
 *   <li>unit propagation, subsumption and self-subsuming resolution (strengthening);
 *   <li>equivalent literals, the strongly connected components of the binary implication graph;
 *   <li>failed literal probing with lifting (a literal implied by both values of a variable);
 *   <li>vivification, which shortens a clause when the negation of some of its literals implies
 *       another of them or a conflict;
 *   <li>bounded variable elimination (Eén and Biere 2005), pure literals and blocked clause
 *       elimination (Järvisalo, Biere and Heule 2010) of variables that occur only in clauses.
 * </ul>
 *
 * <p>The first group keeps every solution: it fixes literals the clauses imply and replaces clauses
 * by equivalent shorter ones. A variable equivalent to another literal is removed when nothing else
 * needs it, and postsolve gives it the value of that literal, so solutions stay in one to one
 * correspondence. The last group keeps satisfiability and the values of every other variable, but
 * several solutions of the clauses can become one, so it only runs when the caller allows that
 * ({@code merge}). Removed clauses go to a reconstruction stack; {@link Reconstruction} gives the
 * removed variables values that satisfy them once the rest of a solution is known.
 *
 * <p>Every rule is bounded by a budget of steps proportional to the size of the clause set.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class SatPresolve {

  /** Steps allowed besides those proportional to the size of the clause set. */
  private static final long BASE_BUDGET = 2_000_000L;

  /** Steps allowed per literal of the clause set. */
  private static final long BUDGET_PER_LITERAL = 200L;

  /** Longest clause that is used to subsume others. */
  private static final int MAX_SUBSUMING = 100;

  /** Longest resolvent variable elimination may add (CaDiCaL's elimclslim). */
  private static final int MAX_RESOLVENT = 100;

  /** A variable with more occurrences of both of its literals is not eliminated. */
  private static final int MAX_OCCURRENCES = 16;

  /** Rounds of variable elimination over all candidates. */
  private static final int ELIMINATION_ROUNDS = 3;

  /** Variables of the clause set, by index. */
  private final List<IntVar> vars = new ArrayList<>();

  private final Map<IntVar, Integer> indexOf = new IdentityHashMap<>();

  /** Constraints taken into the clause set. */
  private final Set<Constraint> absorbed = Collections.newSetFromMap(new IdentityHashMap<>());

  private final List<Constraint> collected;
  private final List<IntVar[][]> external;
  private final Predicate<Var> protect;
  private final boolean merge;

  // variable elimination by resolution; switched off (jacop.presolve.resolution=false) to test
  // the rules it would otherwise leave nothing to
  private final boolean resolution =
      Boolean.parseBoolean(System.getProperty("jacop.presolve.resolution", "true"));

  // per variable: value (-1 unknown), frozen (needed outside the clause set), eliminated
  private int[] value;
  private boolean[] frozen;
  private boolean[] eliminated;

  // per literal 2*var + sign (sign 1 is the negation): ids of the clauses it occurs in
  private IntList[] occurs;

  // clauses by id, null once removed; each sorted when added, without fixed literals
  private final List<int[]> clauses = new ArrayList<>();
  private long[] signature = new long[64];

  // literals fixed since the start, in order; the queue of those not yet propagated
  private final IntList units = new IntList();
  private int propagated;

  // a variable replaced by an equivalent literal and still needed: var, literal
  private final IntList links = new IntList();

  // the reconstruction stack: pivot literal first, then the clause
  private final List<int[]> stack = new ArrayList<>();

  private int[] mark;
  private int stamp;

  private long budget;
  private long steps;

  private boolean infeasible;
  private boolean changed;

  private int clausesBefore;
  private int equivalent;
  private int eliminatedCount;
  private int subsumed;
  private int strengthened;
  private int blocked;

  /**
   * Prepares preprocessing.
   *
   * @param collected the constraints of the store; those that are clauses are taken.
   * @param external clauses kept outside the store, as positive and negative variables, or null.
   * @param protect the variables that must keep their meaning besides those of other constraints,
   *     or null if no variable may be removed at all.
   * @param merge true if rules that can merge solutions may run.
   */
  SatPresolve(
      List<Constraint> collected,
      List<IntVar[][]> external,
      Predicate<Var> protect,
      boolean merge) {
    this.collected = collected;
    this.external = external;
    this.protect = protect;
    this.merge = merge && protect != null;
  }

  /** Runs the rules. */
  void run() {
    List<int[]> loaded = load();
    int n = vars.size();
    value = new int[n];
    frozen = new boolean[n];
    eliminated = new boolean[n];
    occurs = new IntList[2 * n];
    mark = new int[2 * n];
    for (int i = 0; i < 2 * n; i++) {
      occurs[i] = new IntList();
    }
    long literals = 0;
    for (int v = 0; v < n; v++) {
      IntVar x = vars.get(v);
      value[v] = x.singleton() ? x.value() : -1;
    }
    freeze();
    for (int[] c : loaded) {
      literals += c.length;
      addClause(c);
      if (infeasible) {
        return;
      }
    }
    // clauses already satisfied by the domains are not counted
    clausesBefore = clauses.size() + units.size();
    if (!propagate()) {
      return;
    }
    budget = BASE_BUDGET + BUDGET_PER_LITERAL * literals;

    equivalences();
    if (infeasible) {
      return;
    }
    subsumeAll();
    if (infeasible) {
      return;
    }
    probeAndVivify();
    if (infeasible) {
      return;
    }
    if (merge) {
      if (resolution) {
        eliminate();
      }
      if (infeasible) {
        return;
      }
      blockedClauses();
      if (infeasible) {
        return;
      }
      subsumeAll();
      if (infeasible) {
        return;
      }
    }
    finish();
  }

  // ---------------------------------------------------------------------------------------------
  // Loading

  private List<int[]> load() {
    List<int[]> result = new ArrayList<>();
    Set<Var> others = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Constraint c : collected) {
      List<int[]> cs = clausesOf(c);
      if (cs == null) {
        others.addAll(c.arguments());
      } else {
        absorbed.add(c);
        result.addAll(cs);
      }
    }
    if (external != null) {
      for (IntVar[][] c : external) {
        result.add(clause(c[0], c[1]));
      }
    }
    otherVariables = others;
    return result;
  }

  private Set<Var> otherVariables;

  private void freeze() {
    for (int v = 0; v < vars.size(); v++) {
      IntVar x = vars.get(v);
      frozen[v] = protect == null || otherVariables.contains(x) || protect.test(x);
    }
  }

  /**
   * The clauses of a constraint, or null if it is not a conjunction of clauses on 0/1 variables.
   */
  private List<int[]> clausesOf(Constraint c) {
    Class<?> k = c.getClass();
    if (k == BoolClause.class) {
      BoolClause b = (BoolClause) c;
      return List.of(clause(b.positives(), b.negatives()));
    }
    if (k == XeqY.class || k == XneqY.class || k == XlteqY.class || k == XgteqY.class) {
      IntVar x = k == XeqY.class ? ((XeqY) c).x() : null;
      IntVar y;
      if (k == XeqY.class) {
        y = ((XeqY) c).y();
      } else if (k == XneqY.class) {
        x = ((XneqY) c).x();
        y = ((XneqY) c).y();
      } else if (k == XlteqY.class) {
        x = ((XlteqY) c).x();
        y = ((XlteqY) c).y();
      } else {
        x = ((XgteqY) c).x();
        y = ((XgteqY) c).y();
      }
      if (!bool(x) || !bool(y)) {
        return null;
      }
      int a = literal(x, true);
      int b = literal(y, true);
      if (k == XeqY.class) {
        return List.of(new int[] {a, b ^ 1}, new int[] {a ^ 1, b});
      } else if (k == XneqY.class) {
        return List.of(new int[] {a, b}, new int[] {a ^ 1, b ^ 1});
      } else if (k == XlteqY.class) {
        return List.of(new int[] {a ^ 1, b});
      } else {
        return List.of(new int[] {a, b ^ 1});
      }
    }
    if (k == OrBoolVector.class || k == OrBoolSimple.class) {
      IntVar r =
          k == OrBoolVector.class ? ((OrBoolVector) c).result() : ((OrBoolSimple) c).result();
      if (!r.singleton(1)) {
        return null;
      }
      IntVar[] list =
          k == OrBoolVector.class
              ? ((OrBoolVector) c).list()
              : new IntVar[] {((OrBoolSimple) c).a(), ((OrBoolSimple) c).b()};
      return allBool(list) ? List.of(clause(list, new IntVar[0])) : null;
    }
    if (k == AndBoolVector.class || k == AndBoolSimple.class) {
      IntVar r =
          k == AndBoolVector.class ? ((AndBoolVector) c).result() : ((AndBoolSimple) c).result();
      if (!r.singleton(0)) {
        return null;
      }
      IntVar[] list =
          k == AndBoolVector.class
              ? ((AndBoolVector) c).list()
              : new IntVar[] {((AndBoolSimple) c).a(), ((AndBoolSimple) c).b()};
      return allBool(list) ? List.of(clause(new IntVar[0], list)) : null;
    }
    return null;
  }

  private static boolean bool(IntVar x) {
    return x.min() >= 0 && x.max() <= 1;
  }

  private static boolean allBool(IntVar[] xs) {
    for (IntVar x : xs) {
      if (!bool(x)) {
        return false;
      }
    }
    return true;
  }

  private int[] clause(IntVar[] positives, IntVar[] negatives) {
    int[] c = new int[positives.length + negatives.length];
    for (int i = 0; i < positives.length; i++) {
      c[i] = literal(positives[i], true);
    }
    for (int i = 0; i < negatives.length; i++) {
      c[positives.length + i] = literal(negatives[i], false);
    }
    return c;
  }

  private int literal(IntVar x, boolean positive) {
    Integer v = indexOf.get(x);
    if (v == null) {
      v = vars.size();
      vars.add(x);
      indexOf.put(x, v);
    }
    return 2 * v + (positive ? 0 : 1);
  }

  // ---------------------------------------------------------------------------------------------
  // The clause set

  /** 1 if the literal is true, 0 if false, -1 if its variable is not fixed. */
  private int valueOf(int lit) {
    int v = value[lit >> 1];
    return v < 0 ? -1 : (v ^ (lit & 1));
  }

  /** Adds a clause: sorts it, drops repeated and false literals, ignores it if satisfied. */
  private void addClause(int[] lits) {
    int[] c = lits.clone();
    Arrays.sort(c);
    int k = 0;
    for (int l : c) {
      if (k > 0 && c[k - 1] == l) {
        continue;
      }
      if (k > 0 && c[k - 1] == (l ^ 1)) {
        return;
      }
      int val = valueOf(l);
      if (val == 1) {
        return;
      }
      if (val == 0) {
        continue;
      }
      c[k++] = l;
    }
    if (k == 0) {
      infeasible = true;
    } else if (k == 1) {
      assign(c[0]);
    } else {
      store(Arrays.copyOf(c, k));
    }
  }

  private int store(int[] c) {
    int id = clauses.size();
    clauses.add(c);
    if (id == signature.length) {
      signature = Arrays.copyOf(signature, 2 * id);
    }
    signature[id] = signatureOf(c);
    for (int l : c) {
      occurs[l].add(id);
    }
    return id;
  }

  private static long signatureOf(int[] c) {
    long s = 0;
    for (int l : c) {
      s |= 1L << ((l >> 1) & 63);
    }
    return s;
  }

  private void remove(int id) {
    // the occurrence lists drop the clause when they are next read, see occ
    clauses.set(id, null);
    changed = true;
  }

  /**
   * The clauses a literal occurs in. Removing a clause or a literal leaves its id in the lists;
   * they are cleaned here, so a removal costs nothing while reading costs the length of the list.
   */
  private IntList occ(int lit) {
    IntList list = occurs[lit];
    int j = 0;
    for (int i = 0; i < list.size(); i++) {
      int id = list.get(i);
      int[] c = clauses.get(id);
      if (c != null && Arrays.binarySearch(c, lit) >= 0) {
        list.set(j++, id);
      }
    }
    steps += list.size();
    list.truncate(j);
    return list;
  }

  /** Removes a literal from a clause; a clause left with one literal fixes it. */
  private void removeLiteral(int id, int lit) {
    int[] c = clauses.get(id);
    int[] d = new int[c.length - 1];
    int k = 0;
    for (int l : c) {
      if (l != lit) {
        d[k++] = l;
      }
    }
    changed = true;
    if (d.length == 1) {
      clauses.set(id, d);
      remove(id);
      assign(d[0]);
    } else {
      clauses.set(id, d);
      signature[id] = signatureOf(d);
    }
  }

  /** Fixes a literal to true; it is propagated by {@link #propagate()}. */
  private void assign(int lit) {
    int val = valueOf(lit);
    if (val == 1) {
      return;
    }
    if (val == 0) {
      infeasible = true;
      return;
    }
    value[lit >> 1] = 1 - (lit & 1);
    units.add(lit);
    changed = true;
  }

  /** Removes the clauses satisfied by fixed literals and the false literals from the others. */
  private boolean propagate() {
    while (!infeasible && propagated < units.size()) {
      int lit = units.get(propagated++);
      for (int id : occ(lit).toArray()) {
        if (clauses.get(id) != null) {
          remove(id);
        }
      }
      for (int id : occ(lit ^ 1).toArray()) {
        int[] c = clauses.get(id);
        if (c != null) {
          if (c.length == 2) {
            remove(id);
            assign(c[0] == (lit ^ 1) ? c[1] : c[0]);
          } else {
            removeLiteral(id, lit ^ 1);
          }
        }
      }
    }
    return !infeasible;
  }

  private boolean exhausted() {
    return steps > budget;
  }

  // ---------------------------------------------------------------------------------------------
  // Equivalent literals

  /**
   * Finds the strongly connected components of the binary implication graph (Tarjan), replaces
   * every literal by the representative of its component and removes or links the replaced
   * variables.
   */
  private void equivalences() {
    int nl = occurs.length;
    IntList[] succ = new IntList[nl];
    boolean any = false;
    for (int[] c : clauses) {
      if (c != null && c.length == 2) {
        edge(succ, c[0] ^ 1, c[1]);
        edge(succ, c[1] ^ 1, c[0]);
        any = true;
      }
    }
    if (!any) {
      return;
    }
    int[] repr = new int[nl];
    Arrays.fill(repr, -1);
    int[] index = new int[nl];
    Arrays.fill(index, -1);
    int[] low = new int[nl];
    boolean[] onStack = new boolean[nl];
    int[] sccStack = new int[nl];
    int sp = 0;
    int[] callNode = new int[nl];
    int[] callEdge = new int[nl];
    int counter = 0;
    for (int s = 0; s < nl; s++) {
      if (succ[s] == null || index[s] >= 0) {
        continue;
      }
      int csp = 0;
      index[s] = low[s] = counter++;
      sccStack[sp++] = s;
      onStack[s] = true;
      callNode[csp] = s;
      callEdge[csp++] = 0;
      while (csp > 0) {
        int u = callNode[csp - 1];
        IntList out = succ[u];
        if (out != null && callEdge[csp - 1] < out.size()) {
          int w = out.get(callEdge[csp - 1]++);
          steps++;
          if (index[w] < 0) {
            index[w] = low[w] = counter++;
            sccStack[sp++] = w;
            onStack[w] = true;
            callNode[csp] = w;
            callEdge[csp++] = 0;
          } else if (onStack[w]) {
            low[u] = Math.min(low[u], index[w]);
          }
        } else {
          csp--;
          if (csp > 0) {
            int p = callNode[csp - 1];
            low[p] = Math.min(low[p], low[u]);
          }
          if (low[u] == index[u]) {
            int start = sp;
            do {
              start--;
              onStack[sccStack[start]] = false;
            } while (sccStack[start] != u);
            component(Arrays.copyOfRange(sccStack, start, sp), repr);
            sp = start;
            if (infeasible) {
              return;
            }
          }
        }
      }
    }
    substitute(repr);
  }

  private static void edge(IntList[] succ, int from, int to) {
    if (succ[from] == null) {
      succ[from] = new IntList();
    }
    succ[from].add(to);
  }

  private void component(int[] scc, int[] repr) {
    if (scc.length < 2 || repr[scc[0]] >= 0) {
      return;
    }
    stamp++;
    for (int l : scc) {
      mark[l] = stamp;
    }
    int r = -1;
    for (int l : scc) {
      if (mark[l ^ 1] == stamp) {
        // a literal equivalent to its negation
        infeasible = true;
        return;
      }
      if (r < 0 || frozen[l >> 1] && !frozen[r >> 1] || frozen[l >> 1] == frozen[r >> 1] && l < r) {
        r = l;
      }
    }
    for (int l : scc) {
      repr[l] = r;
      repr[l ^ 1] = r ^ 1;
    }
  }

  private void substitute(int[] repr) {
    List<Integer> replaced = new ArrayList<>();
    for (int v = 0; v < vars.size(); v++) {
      int r = repr[2 * v];
      if (r >= 0 && r != 2 * v) {
        replaced.add(v);
      }
    }
    if (replaced.isEmpty()) {
      return;
    }
    IntList affected = new IntList();
    for (int v : replaced) {
      for (int id : occ(2 * v).toArray()) {
        affected.add(id);
      }
      for (int id : occ(2 * v + 1).toArray()) {
        affected.add(id);
      }
    }
    for (int i = 0; i < affected.size(); i++) {
      int id = affected.get(i);
      int[] c = clauses.get(id);
      if (c == null) {
        continue;
      }
      remove(id);
      int[] d = new int[c.length];
      for (int j = 0; j < c.length; j++) {
        d[j] = repr[c[j]] >= 0 ? repr[c[j]] : c[j];
      }
      steps += c.length;
      addClause(d);
      if (infeasible || !propagate()) {
        return;
      }
    }
    for (int v : replaced) {
      int r = repr[2 * v];
      equivalent++;
      if (frozen[v]) {
        links.add(v);
        links.add(r);
      } else {
        // v = r: (v \/ -r) and (-v \/ r)
        eliminated[v] = true;
        stack.add(new int[] {2 * v, 2 * v, r ^ 1});
        stack.add(new int[] {2 * v + 1, 2 * v + 1, r});
      }
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Subsumption and strengthening

  private void subsumeAll() {
    ArrayDeque<Integer> queue = new ArrayDeque<>();
    List<Integer> ids = new ArrayList<>();
    for (int id = 0; id < clauses.size(); id++) {
      if (clauses.get(id) != null) {
        ids.add(id);
      }
    }
    ids.sort((a, b) -> Integer.compare(clauses.get(a).length, clauses.get(b).length));
    queue.addAll(ids);
    while (!queue.isEmpty() && !exhausted() && !infeasible) {
      int id = queue.poll();
      int[] c = clauses.get(id);
      if (c == null || c.length > MAX_SUBSUMING) {
        continue;
      }
      int best = c[0];
      for (int l : c) {
        if (occurs[l].size() + occurs[l ^ 1].size()
            < occurs[best].size() + occurs[best ^ 1].size()) {
          best = l;
        }
      }
      int[] candidates = concat(occ(best).toArray(), occ(best ^ 1).toArray());
      for (int d : candidates) {
        if (clauses.get(id) != c) {
          break;
        }
        int[] dc = clauses.get(d);
        if (d == id || dc == null || dc.length < c.length) {
          continue;
        }
        if ((signature[id] & ~signature[d]) != 0) {
          continue;
        }
        steps += dc.length;
        int r = subsumes(c, dc);
        if (r == -1) {
          remove(d);
          subsumed++;
        } else if (r >= 0) {
          strengthened++;
          removeLiteral(d, r ^ 1);
          if (!propagate()) {
            return;
          }
          if (clauses.get(d) != null) {
            queue.add(d);
          }
        }
      }
    }
  }

  /**
   * -1 if clause c subsumes clause d, a literal l of c if c without l and with its negation
   * subsumes d (so d can lose the negation of l), -2 otherwise.
   */
  private int subsumes(int[] c, int[] d) {
    stamp++;
    for (int l : d) {
      mark[l] = stamp;
    }
    int flip = -1;
    for (int l : c) {
      if (mark[l] == stamp) {
        continue;
      }
      if (flip < 0 && mark[l ^ 1] == stamp) {
        flip = l;
      } else {
        return -2;
      }
    }
    return flip;
  }

  private static int[] concat(int[] a, int[] b) {
    int[] r = Arrays.copyOf(a, a.length + b.length);
    System.arraycopy(b, 0, r, a.length, b.length);
    return r;
  }

  // ---------------------------------------------------------------------------------------------
  // Probing and vivification

  private void probeAndVivify() {
    if (exhausted()) {
      return;
    }
    Probe p = new Probe();
    // failed literals and lifting, on the variables of binary clauses
    boolean[] candidate = new boolean[vars.size()];
    for (int[] c : clauses) {
      if (c != null && c.length == 2) {
        candidate[c[0] >> 1] = true;
        candidate[c[1] >> 1] = true;
      }
    }
    for (int v = 0; v < vars.size() && !exhausted() && !infeasible; v++) {
      if (candidate[v] && p.value[v] < 0) {
        p.probe(v);
      }
    }
    // vivification of clauses of three literals or more
    List<int[]> shortened = new ArrayList<>();
    for (int id = 0; id < clauses.size() && !exhausted() && !infeasible; id++) {
      int[] c = clauses.get(id);
      if (c != null && c.length >= 3) {
        int[] d = p.vivify(id, c);
        if (d != null) {
          shortened.add(new int[] {id});
          shortened.add(d);
        }
      }
    }
    if (infeasible) {
      return;
    }
    for (int i = 0; i < p.size; i++) {
      assign(p.trail[i]);
    }
    if (!propagate()) {
      return;
    }
    for (int i = 0; i < shortened.size(); i += 2) {
      int id = shortened.get(i)[0];
      if (clauses.get(id) != null) {
        remove(id);
        strengthened++;
        addClause(shortened.get(i + 1));
        if (infeasible || !propagate()) {
          return;
        }
      }
    }
  }

  /** Unit propagation with two watched literals over the clauses as they are when it starts. */
  private final class Probe {

    final int[] value = SatPresolve.this.value.clone();
    final int[][] cls = clauses.toArray(new int[0][]);
    final IntList[] watches = new IntList[occurs.length];
    final int[] trail = new int[vars.size()];
    int size;
    int head;
    int ignored = -1;

    Probe() {
      for (int i = 0; i < watches.length; i++) {
        watches[i] = new IntList();
      }
      for (int id = 0; id < cls.length; id++) {
        int[] c = cls[id];
        if (c != null) {
          // copies, so the order of the watched literals does not change the clause set
          c = c.clone();
          cls[id] = c;
          watches[c[0]].add(id);
          watches[c[1]].add(id);
        }
      }
    }

    int valueOf(int lit) {
      int v = value[lit >> 1];
      return v < 0 ? -1 : (v ^ (lit & 1));
    }

    void set(int lit) {
      value[lit >> 1] = 1 - (lit & 1);
      trail[size++] = lit;
    }

    void backtrack(int to) {
      while (size > to) {
        value[trail[--size] >> 1] = -1;
      }
      head = Math.min(head, to);
    }

    /** Propagates the trail; false on a conflict. */
    boolean propagate() {
      while (head < size) {
        int falseLit = trail[head++] ^ 1;
        IntList ws = watches[falseLit];
        int i = 0;
        int j = 0;
        int n = ws.size();
        boolean conflict = false;
        while (i < n) {
          int id = ws.get(i++);
          steps++;
          if (conflict || id == ignored) {
            ws.set(j++, id);
            continue;
          }
          int[] c = cls[id];
          if (c[0] == falseLit) {
            c[0] = c[1];
            c[1] = falseLit;
          }
          if (valueOf(c[0]) == 1) {
            ws.set(j++, id);
            continue;
          }
          boolean moved = false;
          for (int k = 2; k < c.length; k++) {
            if (valueOf(c[k]) != 0) {
              c[1] = c[k];
              c[k] = falseLit;
              watches[c[1]].add(id);
              moved = true;
              break;
            }
          }
          if (moved) {
            continue;
          }
          ws.set(j++, id);
          if (valueOf(c[0]) == 0) {
            conflict = true;
          } else {
            set(c[0]);
          }
        }
        ws.truncate(j);
        if (conflict) {
          return false;
        }
      }
      return true;
    }

    /** Fixes a literal implied at the root; marks the problem infeasible on a conflict. */
    void root(int lit) {
      int val = valueOf(lit);
      if (val == 1) {
        return;
      }
      if (val == 0) {
        infeasible = true;
        return;
      }
      set(lit);
      if (!propagate()) {
        infeasible = true;
      }
    }

    void probe(int v) {
      int start = size;
      set(2 * v);
      if (!propagate()) {
        backtrack(start);
        root(2 * v + 1);
        return;
      }
      stamp++;
      for (int i = start + 1; i < size; i++) {
        mark[trail[i]] = stamp;
      }
      backtrack(start);
      set(2 * v + 1);
      if (!propagate()) {
        backtrack(start);
        root(2 * v);
        return;
      }
      IntList both = new IntList();
      for (int i = start + 1; i < size; i++) {
        if (mark[trail[i]] == stamp) {
          both.add(trail[i]);
        }
      }
      backtrack(start);
      for (int i = 0; i < both.size() && !infeasible; i++) {
        root(both.get(i));
      }
    }

    /** A shorter clause implied by the others that replaces clause id, or null. */
    int[] vivify(int id, int[] c) {
      int start = size;
      ignored = id;
      IntList kept = new IntList();
      boolean shorter = false;
      for (int l : c) {
        int val = valueOf(l);
        if (val == 1) {
          // the negation of the literals before implies l
          kept.add(l);
          shorter = kept.size() < c.length;
          break;
        }
        if (val == 0) {
          // the negation of the literals before implies the negation of l
          shorter = true;
          continue;
        }
        kept.add(l);
        set(l ^ 1);
        if (!propagate()) {
          shorter = kept.size() < c.length;
          break;
        }
      }
      backtrack(start);
      ignored = -1;
      return shorter ? kept.toArray() : null;
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Variable elimination and blocked clauses

  private boolean eliminable(int v) {
    return !frozen[v] && !eliminated[v] && value[v] < 0;
  }

  private void eliminate() {
    for (int round = 0; round < ELIMINATION_ROUNDS; round++) {
      List<Integer> candidates = new ArrayList<>();
      int[] count = new int[vars.size()];
      for (int v = 0; v < vars.size(); v++) {
        if (eliminable(v)) {
          count[v] = occurrences(v);
          if (count[v] > 0) {
            candidates.add(v);
          }
        }
      }
      candidates.sort((a, b) -> Integer.compare(count[a], count[b]));
      boolean any = false;
      for (int v : candidates) {
        if (exhausted() || infeasible) {
          return;
        }
        if (eliminable(v) && tryEliminate(v)) {
          any = true;
        }
      }
      if (!any) {
        return;
      }
    }
  }

  private int occurrences(int v) {
    return occ(2 * v).size() + occ(2 * v + 1).size();
  }

  private boolean tryEliminate(int v) {
    int[] pos = occ(2 * v).toArray();
    int[] neg = occ(2 * v + 1).toArray();
    if (pos.length + neg.length == 0) {
      return false;
    }
    if (pos.length > MAX_OCCURRENCES && neg.length > MAX_OCCURRENCES) {
      return false;
    }
    List<int[]> resolvents = new ArrayList<>();
    if (pos.length > 0 && neg.length > 0) {
      int limit = pos.length + neg.length;
      for (int p : pos) {
        for (int q : neg) {
          if (exhausted()) {
            return false;
          }
          int[] r = resolve(clauses.get(p), clauses.get(q), v);
          if (r == null) {
            continue;
          }
          if (r.length > MAX_RESOLVENT || resolvents.size() == limit) {
            return false;
          }
          resolvents.add(r);
        }
      }
    }
    for (int p : pos) {
      stack.add(withPivot(2 * v, clauses.get(p)));
      remove(p);
    }
    for (int q : neg) {
      stack.add(withPivot(2 * v + 1, clauses.get(q)));
      remove(q);
    }
    eliminated[v] = true;
    eliminatedCount++;
    for (int[] r : resolvents) {
      addClause(r);
      if (infeasible || !propagate()) {
        return true;
      }
    }
    return true;
  }

  /** The resolvent of c (with v) and d (with not v), or null if it is a tautology. */
  private int[] resolve(int[] c, int[] d, int v) {
    steps += c.length + d.length;
    stamp++;
    IntList r = new IntList();
    for (int l : c) {
      if (l >> 1 != v) {
        mark[l] = stamp;
        r.add(l);
      }
    }
    for (int l : d) {
      if (l >> 1 == v || mark[l] == stamp) {
        continue;
      }
      if (mark[l ^ 1] == stamp) {
        return null;
      }
      r.add(l);
    }
    return r.toArray();
  }

  private static int[] withPivot(int pivot, int[] c) {
    int[] e = new int[c.length + 1];
    e[0] = pivot;
    System.arraycopy(c, 0, e, 1, c.length);
    return e;
  }

  private void blockedClauses() {
    for (int v = 0; v < vars.size() && !exhausted(); v++) {
      if (!eliminable(v)) {
        continue;
      }
      for (int lit = 2 * v; lit <= 2 * v + 1; lit++) {
        for (int id : occ(lit).toArray()) {
          int[] c = clauses.get(id);
          if (c != null && blocked(c, lit)) {
            stack.add(withPivot(lit, c));
            remove(id);
            blocked++;
          }
        }
      }
    }
  }

  /** True if every resolvent of c on lit is a tautology. */
  private boolean blocked(int[] c, int lit) {
    stamp++;
    for (int l : c) {
      mark[l] = stamp;
    }
    for (int id : occ(lit ^ 1).toArray()) {
      int[] d = clauses.get(id);
      steps += d.length;
      boolean tautology = false;
      for (int l : d) {
        if (l != (lit ^ 1) && mark[l ^ 1] == stamp) {
          tautology = true;
          break;
        }
      }
      if (!tautology) {
        return false;
      }
    }
    return true;
  }

  // ---------------------------------------------------------------------------------------------
  // Result

  /**
   * Fixes the linked variables whose representative is fixed and, when solutions may merge, removes
   * the variables that no longer occur in a clause but in a clause of the stack, which gives them
   * values (a representative left in no clause would otherwise stay free in the child, where it
   * keeps its two values, so it is kept when solutions must stay apart).
   */
  private void finish() {
    for (int i = 0; i < links.size(); i += 2) {
      int v = links.get(i);
      int val = valueOf(links.get(i + 1));
      if (val >= 0 && value[v] < 0) {
        assign(val == 1 ? 2 * v : 2 * v + 1);
      }
    }
    boolean[] onStack = new boolean[vars.size()];
    for (int[] e : stack) {
      for (int j = 1; j < e.length; j++) {
        onStack[e[j] >> 1] = true;
      }
    }
    for (int v = 0; v < vars.size(); v++) {
      if (merge && onStack[v] && eliminable(v) && occurrences(v) == 0) {
        eliminated[v] = true;
      }
    }
  }

  /** True if the clauses have no solution. */
  boolean infeasible() {
    return infeasible;
  }

  /** True if the clause set has changed. */
  boolean changed() {
    return changed;
  }

  /** The constraints taken into the clause set. */
  Set<Constraint> absorbed() {
    return absorbed;
  }

  /**
   * The fixed literals implied by the clauses, as variable and value pairs, in the order found.
   *
   * @return the implied values.
   */
  Map<IntVar, Integer> implied() {
    Map<IntVar, Integer> result = new IdentityHashMap<>();
    for (int i = 0; i < units.size(); i++) {
      int lit = units.get(i);
      if (!vars.get(lit >> 1).singleton()) {
        result.put(vars.get(lit >> 1), 1 - (lit & 1));
      }
    }
    return result;
  }

  /**
   * The clauses after preprocessing, with the links of replaced variables that are still needed, as
   * positive and negative variables. Literals fixed by {@link #implied()} are left out.
   *
   * @return the clauses.
   */
  List<IntVar[][]> clauses() {
    List<IntVar[][]> result = new ArrayList<>();
    for (int[] c : clauses) {
      if (c != null) {
        result.add(variables(c));
      }
    }
    for (int i = 0; i < links.size(); i += 2) {
      int v = 2 * links.get(i);
      int r = links.get(i + 1);
      if (value[v >> 1] < 0) {
        result.add(variables(new int[] {v, r ^ 1}));
        result.add(variables(new int[] {v ^ 1, r}));
      }
    }
    return result;
  }

  private IntVar[][] variables(int[] c) {
    List<IntVar> pos = new ArrayList<>();
    List<IntVar> neg = new ArrayList<>();
    for (int l : c) {
      if (valueOf(l) < 0) {
        ((l & 1) == 0 ? pos : neg).add(vars.get(l >> 1));
      }
    }
    return new IntVar[][] {pos.toArray(new IntVar[0]), neg.toArray(new IntVar[0])};
  }

  /** The variables removed: they occur in no clause and postsolve gives them values. */
  Collection<IntVar> eliminated() {
    List<IntVar> result = new ArrayList<>();
    for (int v = 0; v < vars.size(); v++) {
      if (eliminated[v]) {
        result.add(vars.get(v));
      }
    }
    return result;
  }

  /** The reconstruction of removed variables, or null if no clause was removed with a pivot. */
  Reconstruction reconstruction() {
    return stack.isEmpty() ? null : new Reconstruction(vars, eliminated, stack);
  }

  /** What the rules did. */
  Derivation.ClauseStatistics statistics() {
    int after = 0;
    for (int[] c : clauses) {
      if (c != null) {
        after++;
      }
    }
    return new Derivation.ClauseStatistics(
        clausesBefore,
        after + links.size(),
        implied().size(),
        equivalent,
        eliminatedCount,
        subsumed,
        strengthened,
        blocked);
  }

  /**
   * Gives values to the variables removed with clauses: the clauses of the stack, last removed
   * first, are made true by setting the pivot literal when they are false (Järvisalo, Heule and
   * Biere, <i>Inprocessing rules</i>, 2012).
   */
  static final class Reconstruction {

    private final IntVar[] vars;
    private final boolean[] eliminated;
    private final int[][] stack;

    Reconstruction(List<IntVar> vars, boolean[] eliminated, List<int[]> stack) {
      this.vars = vars.toArray(new IntVar[0]);
      this.eliminated = eliminated.clone();
      this.stack = stack.toArray(new int[0][]);
    }

    /**
     * Returns the variables the removed clauses read that are not removed themselves; postsolve
     * needs their values in the solution.
     *
     * @return the variables.
     */
    List<IntVar> read() {
      boolean[] seen = new boolean[vars.length];
      List<IntVar> result = new ArrayList<>();
      for (int[] e : stack) {
        for (int j = 1; j < e.length; j++) {
          int v = e[j] >> 1;
          if (!seen[v] && !eliminated[v]) {
            seen[v] = true;
            result.add(vars[v]);
          }
        }
      }
      return result;
    }

    /**
     * Computes the values of the variables the stack decides.
     *
     * @param current the value of a variable that is not removed, from the solution.
     * @return the values of the removed variables, and of the others the stack changes.
     */
    Map<IntVar, Integer> values(java.util.function.ToIntFunction<IntVar> current) {
      int[] val = new int[vars.length];
      boolean[] used = new boolean[vars.length];
      for (int[] e : stack) {
        for (int j = 1; j < e.length; j++) {
          used[e[j] >> 1] = true;
        }
      }
      for (int v = 0; v < vars.length; v++) {
        if (used[v]) {
          val[v] = eliminated[v] && !vars[v].singleton() ? 0 : current.applyAsInt(vars[v]);
        }
      }
      int[] before = val.clone();
      for (int i = stack.length - 1; i >= 0; i--) {
        int[] e = stack[i];
        boolean satisfied = false;
        for (int j = 1; j < e.length && !satisfied; j++) {
          satisfied = (val[e[j] >> 1] ^ (e[j] & 1)) == 1;
        }
        if (!satisfied) {
          val[e[0] >> 1] = 1 - (e[0] & 1);
        }
      }
      Map<IntVar, Integer> result = new IdentityHashMap<>();
      for (int v = 0; v < vars.length; v++) {
        if (used[v] && (eliminated[v] || val[v] != before[v])) {
          result.put(vars[v], val[v]);
        }
      }
      return result;
    }
  }

  /** A growable list of ints. */
  private static final class IntList {
    private int[] a = new int[4];
    private int n;

    void add(int x) {
      if (n == a.length) {
        a = Arrays.copyOf(a, 2 * n);
      }
      a[n++] = x;
    }

    int get(int i) {
      return a[i];
    }

    void set(int i, int x) {
      a[i] = x;
    }

    int size() {
      return n;
    }

    void truncate(int size) {
      n = size;
    }

    int[] toArray() {
      return Arrays.copyOf(a, n);
    }
  }
}
