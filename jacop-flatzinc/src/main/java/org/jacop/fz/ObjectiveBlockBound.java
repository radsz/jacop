/*
 * ObjectiveBlockBound.java
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

package org.jacop.fz;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.DifferenceCycles;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.lp.LinearRelaxation;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.jasat.lcg.LcgSolver;
import org.jacop.lcg.LinearForm;

/**
 * Lower bounds on the parts of a linear objective that belong to loosely coupled blocks of the
 * model, posted as redundant constraints before search.
 *
 * <p>The objective is a sum of terms. The constraints are taken in the order of their scope size
 * and join the variables they share into fragments, as in the connected-components detection of
 * decomposable programs (G. Gamrath and M. E. Lübbecke, Experiments with a generic Dantzig-Wolfe
 * decomposition for integer programs, SEA 2010, LNCS 6049, 239-252), except that a constraint is
 * left out, as a linking constraint, when the fragment it would make holds more than half of the
 * objective's terms. The fragments that hold several terms are the blocks: a team's tour in a
 * travelling tournament, a machine's sequence, a person's roster.
 *
 * <p>Dropping the linking constraints relaxes the model, so the least cost of a block's terms
 * subject to the constraints inside the block bounds that part of the objective in every solution:
 * the Lagrangian relaxation with zero multipliers (A. M. Geoffrion, Lagrangean relaxation for
 * integer programming, Mathematical Programming Study 2 (1974) 82-114), known for the travelling
 * tournament problem as its independent lower bound (K. Easton, G. Nemhauser and M. Trick, The
 * traveling tournament problem: description and benchmarks, CP 2001, LNCS 2239, 580-584). The least
 * cost is found by lazy clause generation branch and bound in a copy of the block: its own
 * constraints and the clauses over its variables, over the root domains. A block whose constraints
 * cannot be copied is skipped; one that is not solved within its time gives the lower bound proved
 * so far.
 *
 * <p>For each block a variable {@code c_b} equal to the block's part of the objective is posted
 * with {@code c_b >= least_b}, and the objective is posted again as the sum of the {@code c_b} and
 * the remaining terms. During search the objective's lower bound is then the cost of the blocks
 * already decided plus the least costs of the others, which the sum over the single terms does not
 * see. The search is not changed, so this also holds under a fixed search annotation.
 *
 * <p>On by default; {@code -Dorg.jacop.fz.blockBound=false} turns it off. It may take {@code
 * org.jacop.fz.blockBound.share} (0.02) of the time limit, at most {@code
 * org.jacop.fz.blockBound.ms} (5000) milliseconds, and each block {@code
 * org.jacop.fz.blockBound.blockMs} (1000); after four blocks without a gain the others are left
 * out. The bounds are posted only when they raise the objective's lower bound by at least {@code
 * org.jacop.fz.blockBound.gain} (0.05) of the distance to its upper bound, since the extra
 * variables and the second objective equation cost time at every node.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class ObjectiveBlockBound {

  private ObjectiveBlockBound() {}

  /**
   * Returns whether the bounds are computed, {@code org.jacop.fz.blockBound}.
   *
   * @return false when the property is set to false.
   */
  static boolean on() {
    return !"false".equals(System.getProperty("org.jacop.fz.blockBound"));
  }

  private static final boolean TRACE = Boolean.getBoolean("org.jacop.fz.blockBound.trace");

  private static final double SHARE =
      Double.parseDouble(System.getProperty("org.jacop.fz.blockBound.share", "0.02"));

  private static final long MILLIS = Long.getLong("org.jacop.fz.blockBound.ms", 5000L);

  private static final long BLOCK_MILLIS = Long.getLong("org.jacop.fz.blockBound.blockMs", 1000L);

  // the terms of an objective at least, and the variables of a block at most
  private static final int MIN_TERMS = 4;

  private static final int MAX_BLOCK_VARS = 2000;

  // the blocks tried without a gain before the others are left out
  private static final int PATIENCE = 4;

  // a block's terms, the bounds of their sum and its least cost
  private record Pending(List<IntVar> xs, List<Long> ws, long lo, long hi, long least) {}

  // the share of the objective's range at the root the bound must close at least
  private static final double MIN_GAIN =
      Double.parseDouble(System.getProperty("org.jacop.fz.blockBound.gain", "0.05"));

  /** What was done, for the statistics. */
  record Outcome(int blocks, int bounded, int uncopied, long raised, long millis) {}

  /**
   * Finds the blocks of the objective, computes their least costs and posts the bounds.
   *
   * @param store the store, at a fixpoint at the root.
   * @param clauses clauses kept outside the store, each {positive, negative}; may be empty.
   * @param objective the objective variable.
   * @param maximize whether the objective is maximized.
   * @param order variables to branch on first in a block's search, such as the annotated ones.
   * @param timeLimitMillis the time limit of the run, or 0 for none.
   * @return what was done, or null when the objective has no blocks.
   */
  static Outcome run(
      Store store,
      List<IntVar[][]> clauses,
      IntVar objective,
      boolean maximize,
      List<Var> order,
      long timeLimitMillis) {
    long start = System.currentTimeMillis();
    if (objective == null || objective.singleton()) {
      return null;
    }
    long budget = timeLimitMillis > 0 ? Math.min(MILLIS, (long) (SHARE * timeLimitMillis)) : MILLIS;
    long deadline = start + budget;

    List<Constraint> all = new ArrayList<>();
    for (Constraint c : Components.constraints(store)) {
      if (c instanceof SatisfiedPresent s && s.satisfied()
          || c instanceof LinearRelaxation
          || c instanceof DifferenceCycles) {
        continue;
      }
      all.add(c);
    }
    // the equations: a variable that only its equation and one other constraint use, such as a
    // part of a long sum split for lazy clause generation, is replaced by its definition
    Map<Var, Integer> uses = new IdentityHashMap<>();
    for (Constraint c : all) {
      for (Var v : c.arguments()) {
        uses.merge(v, 1, Integer::sum);
      }
    }
    Map<Constraint, LinearForm> equations = new IdentityHashMap<>();
    Map<IntVar, List<Constraint>> defining = new IdentityHashMap<>();
    Constraint definition = null;
    for (Constraint c : all) {
      LinearForm f = c instanceof BoolClause ? null : LinearForms.of(c);
      if (f == null || f.relation() != LinearForm.EQ) {
        continue;
      }
      equations.put(c, f);
      int i = indexOf(f.vars(), objective);
      if (i >= 0
          && Math.abs(f.weights()[i]) == 1
          && (definition == null || f.vars().length > equations.get(definition).vars().length)) {
        definition = c;
      }
      for (int j = 0; j < f.vars().length; j++) {
        IntVar v = f.vars()[j];
        if (v != objective && !v.singleton() && Math.abs(f.weights()[j]) == 1 && uses.get(v) == 2) {
          defining.computeIfAbsent(v, k -> new ArrayList<>(2)).add(c);
        }
      }
    }
    if (definition == null) {
      if (TRACE) {
        System.err.println("% block bound: no definition of " + objective);
      }
      return null;
    }
    defining.put(objective, List.of(definition));
    // cost = sign * objective = sum of terms + constant
    long sign = maximize ? -1 : 1;
    Map<IntVar, Long> terms = new LinkedHashMap<>();
    terms.put(objective, sign);
    long[] constantHolder = {0};
    Set<Constraint> used = Collections.newSetFromMap(new IdentityHashMap<>());
    expand(terms, constantHolder, equations, defining, used);
    long constant = constantHolder[0];
    if (terms.containsKey(objective)) {
      return null;
    }
    terms.values().removeIf(w -> w == 0);
    if (terms.size() < MIN_TERMS) {
      return null;
    }
    int half = terms.size() / 2;

    // the fragments, joined by the constraints in the order of their scope size
    Map<Var, Var> parent = new IdentityHashMap<>();
    Map<Var, Integer> termCount = new IdentityHashMap<>();
    for (IntVar x : terms.keySet()) {
      parent.put(x, x);
      termCount.put(x, 1);
    }
    List<Constraint> sorted = new ArrayList<>();
    Map<Constraint, List<Var>> scopes = new IdentityHashMap<>();
    for (Constraint c : all) {
      if (used.contains(c)) {
        continue;
      }
      List<Var> scope = new ArrayList<>();
      Set<Var> seen = Collections.newSetFromMap(new IdentityHashMap<>());
      for (Var v : c.arguments()) {
        if (!v.singleton() && v != objective && seen.add(v)) {
          scope.add(v);
        }
      }
      if (scope.size() >= 2) {
        scopes.put(c, scope);
        sorted.add(c);
      }
    }
    List<List<Var>> ordered = new ArrayList<>();
    for (Constraint c : sorted) {
      ordered.add(scopes.get(c));
    }
    for (IntVar[][] clause : clauses) {
      List<Var> scope = new ArrayList<>();
      Set<Var> seen = Collections.newSetFromMap(new IdentityHashMap<>());
      for (IntVar[] side : clause) {
        for (IntVar v : side) {
          if (!v.singleton() && seen.add(v)) {
            scope.add(v);
          }
        }
      }
      if (scope.size() >= 2) {
        ordered.add(scope);
      }
    }
    ordered.sort((a, b) -> Integer.compare(a.size(), b.size()));
    int linking = 0;
    for (List<Var> scope : ordered) {
      Set<Var> roots = Collections.newSetFromMap(new IdentityHashMap<>());
      int count = 0;
      for (Var v : scope) {
        Var r = find(parent, v);
        if (roots.add(r)) {
          count += termCount.getOrDefault(r, 0);
        }
      }
      if (roots.size() < 2) {
        continue;
      }
      if (count > half) {
        linking++;
        continue;
      }
      Var first = null;
      for (Var r : roots) {
        if (first == null) {
          first = r;
        } else {
          parent.put(r, first);
          termCount.merge(first, termCount.getOrDefault(r, 0), Integer::sum);
          termCount.remove(r);
        }
      }
    }
    if (TRACE) {
      System.err.println("% block bound: " + linking + " linking, fragments " + termCount.values());
    }
    if (linking == 0) {
      // the objective's terms do not share a linking constraint: nothing to gain over the sum
      return null;
    }
    // the blocks: fragments with several terms
    Map<Var, List<IntVar>> blockVars = new LinkedHashMap<>();
    for (Map.Entry<Var, Integer> e : termCount.entrySet()) {
      if (e.getValue() >= 2) {
        blockVars.put(e.getKey(), new ArrayList<>());
      }
    }
    if (blockVars.size() < 2) {
      return null;
    }
    for (Var v : parent.keySet()) {
      if (v instanceof IntVar x && !x.singleton()) {
        List<IntVar> list = blockVars.get(find(parent, v));
        if (list != null) {
          list.add(x);
        }
      }
    }
    if (TRACE) {
      List<Integer> sizes = new ArrayList<>();
      for (List<IntVar> l : blockVars.values()) {
        sizes.add(l.size());
      }
      System.err.println(
          "% block bound: "
              + terms.size()
              + " terms, "
              + blockVars.size()
              + " blocks of "
              + sizes
              + " variables, "
              + linking
              + " linking constraints");
    }
    // the constraints and clauses inside each block
    Map<Var, List<Constraint>> inside = new IdentityHashMap<>();
    for (Constraint c : all) {
      if (!used.contains(c)) {
        Var root = blockOf(c.arguments(), parent, objective);
        if (root != null && blockVars.containsKey(root)) {
          inside.computeIfAbsent(root, k -> new ArrayList<>()).add(c);
        }
      }
    }
    Map<Var, List<IntVar[][]>> insideClauses = new IdentityHashMap<>();
    for (IntVar[][] clause : clauses) {
      List<Var> vs = new ArrayList<>(List.of(clause[0]));
      vs.addAll(List.of(clause[1]));
      Var root = blockOf(vs, parent, objective);
      if (root != null && blockVars.containsKey(root)) {
        insideClauses.computeIfAbsent(root, k -> new ArrayList<>()).add(clause);
      }
    }

    List<IntVar> sums = new ArrayList<>();
    List<Pending> pending = new ArrayList<>();
    Set<IntVar> covered = Collections.newSetFromMap(new IdentityHashMap<>());
    int bounded = 0;
    int uncopied = 0;
    long raised = 0;
    int left = blockVars.size();
    int tried = 0;
    for (Map.Entry<Var, List<IntVar>> e : blockVars.entrySet()) {
      List<IntVar> vars = e.getValue();
      long now = System.currentTimeMillis();
      if (pending.isEmpty() && tried >= PATIENCE) {
        // the first blocks gain nothing: the others, often alike, are not worth the time
        break;
      }
      if (now >= deadline || vars.size() > MAX_BLOCK_VARS) {
        left--;
        continue;
      }
      long slice = Math.max(1, Math.min(BLOCK_MILLIS, (deadline - now) / left--));
      List<IntVar> xs = new ArrayList<>();
      List<Long> ws = new ArrayList<>();
      long lo = 0;
      long hi = 0;
      for (IntVar x : vars) {
        Long w = terms.get(x);
        if (w != null) {
          xs.add(x);
          ws.add(w);
          lo += w > 0 ? w * x.min() : w * x.max();
          hi += w > 0 ? w * x.max() : w * x.min();
        }
      }
      if (lo < Integer.MIN_VALUE / 2 || hi > Integer.MAX_VALUE / 2) {
        continue;
      }
      tried++;
      long least =
          leastInCopy(
              inside.getOrDefault(e.getKey(), List.of()),
              insideClauses.getOrDefault(e.getKey(), List.of()),
              vars,
              xs,
              ws,
              slice);
      if (TRACE) {
        System.err.println(
            "% block bound: block of "
                + vars.size()
                + " variables, "
                + xs.size()
                + " terms, least "
                + (least == Long.MIN_VALUE ? "not copied" : least)
                + " vs "
                + lo
                + " in "
                + (System.currentTimeMillis() - now)
                + " ms");
      }
      if (least == Long.MIN_VALUE) {
        uncopied++;
        continue;
      }
      if (least <= lo) {
        continue;
      }
      // the block has no solution (Long.MAX_VALUE) or its least cost is above the sum's bound
      pending.add(new Pending(xs, ws, lo, hi, Math.min(least, hi + 1L)));
      raised += Math.min(least, hi + 1L) - lo;
    }
    if (pending.isEmpty()) {
      return new Outcome(blockVars.size(), 0, uncopied, 0, elapsed(start));
    }
    // the bound of cost = sign * objective that the blocks give, against the one it has: posted
    // only
    // when it closes enough of the objective's range to pay for the constraints it adds
    long termsLo = constant;
    for (Map.Entry<IntVar, Long> t : terms.entrySet()) {
      long w = t.getValue();
      termsLo += w > 0 ? w * t.getKey().min() : w * t.getKey().max();
    }
    long current = sign > 0 ? objective.min() : -(long) objective.max();
    long top = sign > 0 ? objective.max() : -(long) objective.min();
    long gain = termsLo + raised - current;
    if (TRACE) {
      System.err.println(
          "% block bound: bound "
              + (termsLo + raised)
              + " vs "
              + current
              + " of range up to "
              + top);
    }
    if (gain <= 0 || gain < MIN_GAIN * (top - current)) {
      return new Outcome(blockVars.size(), 0, uncopied, 0, elapsed(start));
    }
    for (Pending b : pending) {
      IntVar cost = new IntVar(store, "blockCost" + sums.size(), (int) b.lo, (int) b.hi);
      IntVar[] lv = new IntVar[b.xs.size() + 1];
      int[] lw = new int[b.xs.size() + 1];
      for (int i = 0; i < b.xs.size(); i++) {
        lv[i] = b.xs.get(i);
        lw[i] = (int) (long) b.ws.get(i);
      }
      lv[b.xs.size()] = cost;
      lw[b.xs.size()] = -1;
      store.impose(new LinearInt(lv, lw, "==", 0));
      store.impose(new XgteqC(cost, (int) b.least));
      sums.add(cost);
      covered.addAll(b.xs);
      bounded++;
      if (!store.consistency()) {
        return new Outcome(blockVars.size(), bounded, uncopied, raised, elapsed(start));
      }
    }
    // cost = constant + sum of block costs + other terms, cost = sign * objective
    List<IntVar> lv = new ArrayList<>(sums);
    List<Long> lw = new ArrayList<>();
    for (int i = 0; i < sums.size(); i++) {
      lw.add(1L);
    }
    for (Map.Entry<IntVar, Long> t : terms.entrySet()) {
      if (!covered.contains(t.getKey())) {
        lv.add(t.getKey());
        lw.add(t.getValue());
      }
    }
    lv.add(objective);
    lw.add(-sign);
    int[] w = new int[lw.size()];
    for (int i = 0; i < w.length; i++) {
      long x = lw.get(i);
      if (x < Integer.MIN_VALUE || x > Integer.MAX_VALUE) {
        return new Outcome(blockVars.size(), bounded, uncopied, raised, elapsed(start));
      }
      w[i] = (int) x;
    }
    if (constant < Integer.MIN_VALUE || constant > Integer.MAX_VALUE) {
      return new Outcome(blockVars.size(), bounded, uncopied, raised, elapsed(start));
    }
    store.impose(new LinearInt(lv.toArray(new IntVar[0]), w, "==", (int) -constant));
    store.consistency();
    return new Outcome(blockVars.size(), bounded, uncopied, raised, elapsed(start));
  }

  // the block of all non-singleton variables, or null when they are in several or none
  private static Var blockOf(Iterable<? extends Var> vars, Map<Var, Var> parent, IntVar objective) {
    Var root = null;
    for (Var v : vars) {
      if (v.singleton()) {
        continue;
      }
      if (v == objective || !parent.containsKey(v)) {
        return null;
      }
      Var r = find(parent, v);
      if (root != null && r != root) {
        return null;
      }
      root = r;
    }
    return root;
  }

  /**
   * The least cost of a block by lazy clause generation in a copy of the block: its own constraints
   * and clauses only. Returns a proved lower bound when it runs out of time, Long.MAX_VALUE when
   * the block has no solution, and Long.MIN_VALUE + 1 when the block cannot be copied.
   */
  private static long leastInCopy(
      List<Constraint> own,
      List<IntVar[][]> clauses,
      List<IntVar> vars,
      List<IntVar> xs,
      List<Long> ws,
      long millis) {
    Store copy = new Store();
    Map<Var, Var> copies = new IdentityHashMap<>();
    VarMap map =
        new VarMap() {
          @Override
          public Store target() {
            return copy;
          }

          @Override
          @SuppressWarnings("unchecked")
          public <V extends Var> V get(V v) {
            Var c = copies.get(v);
            if (c == null) {
              c = copyOf(copy, v);
              copies.put(v, c);
            }
            return (V) c;
          }
        };
    IntVar cost;
    try {
      for (Constraint c : own) {
        if (!Copyable.canCopy(c)) {
          throw new IllegalArgumentException(c + " cannot be copied");
        }
        copy.impose(((Copyable<?>) c).copy(map));
      }
      for (IntVar x : vars) {
        map.get(x);
      }
      for (IntVar[][] clause : clauses) {
        map.get(clause[0]);
        map.get(clause[1]);
      }
      IntVar[] lv = new IntVar[xs.size() + 1];
      int[] lw = new int[xs.size() + 1];
      long lo = 0;
      long hi = 0;
      for (int i = 0; i < xs.size(); i++) {
        lv[i] = map.get(xs.get(i));
        long w = ws.get(i);
        lw[i] = Math.toIntExact(w);
        lo += Math.min(w * lv[i].min(), w * lv[i].max());
        hi += Math.max(w * lv[i].min(), w * lv[i].max());
      }
      cost = new IntVar(copy, Math.toIntExact(lo), Math.toIntExact(hi));
      lv[xs.size()] = cost;
      lw[xs.size()] = -1;
      copy.impose(new LinearInt(lv, lw, "==", 0));
    } catch (IllegalArgumentException | ArithmeticException e) {
      if (TRACE) {
        System.err.println("% block bound: not copied: " + e.getMessage());
      }
      return Long.MIN_VALUE;
    }
    LcgSolver solver = new LcgSolver(copy);
    for (IntVar[][] clause : clauses) {
      solver.addClause(map.get(clause[0]), map.get(clause[1]));
    }
    long left = Math.max(1, millis);
    solver.sat().setDeadline(System.nanoTime() + left * 1_000_000L);
    solver.setTimeLimit(left);
    long[] lower = {cost.min()};
    solver.onBound(v -> lower[0] = Math.max(lower[0], v));
    int status = solver.minimize(cost);
    if (TRACE) {
      System.err.println(
          "%   copy: status "
              + status
              + " lower "
              + lower[0]
              + " constraints "
              + own.size()
              + " clauses "
              + clauses.size());
    }
    if (status == CdclSolver.UNSAT) {
      return Long.MAX_VALUE;
    }
    if (status == CdclSolver.SAT) {
      return solver.value(cost);
    }
    return lower[0];
  }

  // a copy of a variable in another store: an integer or a Boolean variable with its domain
  private static Var copyOf(Store target, Var v) {
    if (v.getClass() == IntVar.class) {
      IntVar x = (IntVar) v;
      return new IntVar(target, x.id(), x.dom().cloneLight());
    }
    if (v.getClass() == BooleanVar.class) {
      IntVar x = (IntVar) v;
      return new BooleanVar(target, x.id(), x.min(), x.max());
    }
    throw new IllegalArgumentException(v + " cannot be copied");
  }

  private static long elapsed(long start) {
    return System.currentTimeMillis() - start;
  }

  // replaces each term defined by an equation by the equation's other terms
  private static void expand(
      Map<IntVar, Long> terms,
      long[] constant,
      Map<Constraint, LinearForm> equations,
      Map<IntVar, List<Constraint>> defining,
      Set<Constraint> used) {
    ArrayDeque<IntVar> work = new ArrayDeque<>(terms.keySet());
    while (!work.isEmpty()) {
      IntVar v = work.poll();
      Long a = terms.get(v);
      Constraint d = null;
      for (Constraint e : defining.getOrDefault(v, List.of())) {
        if (!used.contains(e)) {
          d = e;
          break;
        }
      }
      if (a == null || a == 0 || d == null) {
        continue;
      }
      LinearForm f = equations.get(d);
      long wv = f.weights()[indexOf(f.vars(), v)];
      used.add(d);
      terms.remove(v);
      // wv v + sum w_u u = c, wv = +-1: v = wv (c - sum w_u u)
      constant[0] += a * wv * f.c();
      for (int i = 0; i < f.vars().length; i++) {
        IntVar u = f.vars()[i];
        if (u == v) {
          continue;
        }
        long coefficient = -a * wv * f.weights()[i];
        if (u.singleton()) {
          constant[0] += coefficient * u.value();
        } else {
          terms.merge(u, coefficient, Long::sum);
          work.add(u);
        }
      }
    }
  }

  private static int indexOf(IntVar[] vars, IntVar v) {
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] == v) {
        return i;
      }
    }
    return -1;
  }

  private static Var find(Map<Var, Var> parent, Var x) {
    Var r = x;
    Var p = parent.putIfAbsent(r, r);
    while (p != null && p != r) {
      r = p;
      p = parent.get(r);
    }
    while (parent.get(x) != r) {
      Var next = parent.get(x);
      parent.put(x, r);
      x = next;
    }
    return r;
  }
}
