/*
 * DecompositionBound.java
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
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.ToIntFunction;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.CountValuesBounds;
import org.jacop.constraints.DifferenceCycles;
import org.jacop.constraints.LexChain;
import org.jacop.constraints.LexOrder;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SeqPrecedeChain;
import org.jacop.constraints.ValuePrecede;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.lp.LinearRelaxation;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.jalp.RevisedDualSimplex;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.jasat.lcg.LcgSolver;
import org.jacop.lcg.LinearForm;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMiddle;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.SmallestDomain;
import org.jacop.search.SplitSelect;

/**
 * A root bound on the objective from a Dantzig-Wolfe decomposition of the model into blocks that
 * share only counting and linear constraints.
 *
 * <p>The blocks are found as in the connected-components detection of decomposable mixed integer
 * programs (G. Gamrath and M. E. Lübbecke, Experiments with a generic Dantzig-Wolfe decomposition
 * for integer programs, SEA 2010, LNCS 6049, 239-252): the linear and counting constraints
 * (CountValuesBounds) are taken out, the other constraints and the clauses of lazy clause
 * generation split the variables into components, and a removed constraint is put back while it
 * joins fragments of which at most one is large. The removed constraints that still span several
 * components are the linking rows; the components they or the objective touch are the blocks (a
 * worker's shift sequence, a person's roster, a generator).
 *
 * <p>The bound is that of the Lagrangian relaxation of the linking rows, whose dual is the
 * Dantzig-Wolfe master over the blocks' solutions (A. M. Geoffrion, Lagrangean relaxation for
 * integer programming, Mathematical Programming Study 2 (1974) 82-114). Column generation gives the
 * multipliers: a JaLP master over the columns found so far, and for each block a pricing problem,
 * the block's own constraints with the reduced cost as objective, solved by branch and bound in the
 * store at the root or, when that runs out of time, by lazy clause generation in a copy of the
 * block. As for CP models built from knapsack and regular constraints in M. H. Hà, C.-G. Quimper
 * and L.-M. Rousseau, General bounding mechanism for constraint programs, CP 2015, LNCS 9255,
 * 158-172, a block is solved with the solver's own propagation, so any block the solver handles can
 * be one. The pricing problems get the master's duals smoothed towards the best multipliers so far
 * (P. Wentges, Weighted Dantzig-Wolfe decomposition for linear mixed-integer programming,
 * International Transactions in Operational Research 4 (1997) 151-162).
 *
 * <p>The bound is certified exactly: the duals of each master solve are rounded to multiples of
 * 1/K, and when every pricing problem has been solved to optimality with these rounded multipliers,
 * or has a proved lower bound (the root bound of lazy clause generation, the least cost over the
 * domains), the bound K &middot; L = &Sigma; Y<sub>r</sub> side<sub>r</sub> + &Sigma;<sub>b</sub>
 * min<sub>b</sub> (K cost - Y &middot; A<sub>b</sub>) is computed in integer arithmetic; it holds
 * whatever the simplex's accuracy. A pricing problem is solved in the store, where the linking
 * constraints also propagate: that only removes assignments of a block that no solution extends, so
 * the bound stays valid.
 *
 * <p>It runs once, before search, within a share of the time limit ({@code
 * org.jacop.fz.decomposition.share}, 0.2, of the time limit, or {@code
 * org.jacop.fz.decomposition.ms} when there is none), and the objective is bounded at the root by
 * the best certified bound. Off by default; {@code -Dorg.jacop.fz.decomposition=true} turns it on.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class DecompositionBound {

  /**
   * Returns whether the bound is computed, {@code org.jacop.fz.decomposition}.
   *
   * @return true when the property is set.
   */
  static boolean on() {
    return Boolean.getBoolean("org.jacop.fz.decomposition");
  }

  // prints the progress of column generation to the standard error
  private static final boolean TRACE = Boolean.getBoolean("org.jacop.fz.decomposition.trace");

  // the share of the time limit the bound may take
  private static final double SHARE =
      Double.parseDouble(System.getProperty("org.jacop.fz.decomposition.share", "0.2"));

  // the time the bound may take when there is no time limit, in milliseconds
  private static final long MILLIS = Long.getLong("org.jacop.fz.decomposition.ms", 60_000L);

  // the time of a pricing search in the store at most, for a block that can be copied
  private static long storeMillis() {
    return Long.getLong("org.jacop.fz.decomposition.storeMs", 300L);
  }

  // the time of one pricing search at most, in milliseconds
  private static final long PRICE_MS = Long.getLong("org.jacop.fz.decomposition.priceMs", 2000L);

  // the pivots of one master solve at most, for each of the dual and the primal simplex
  private static final int PIVOTS = Integer.getInteger("org.jacop.fz.decomposition.pivots", 20_000);

  // the variables of a large block at least, and the large blocks at least
  private static int large() {
    return Integer.getInteger("org.jacop.fz.decomposition.large", 10);
  }

  private static final int MIN_BLOCKS = 2;

  // the blocks and the linking rows at most
  private static final int MAX_BLOCKS = 2000;

  private static final int MAX_ROWS = 20_000;

  // the time, in milliseconds, the bound may take at least before it gives up for lack of progress
  private static final long PATIENCE_MS = 5000;

  // the weight of the best multipliers in the duals that the pricing problems get
  private static final double SMOOTHING =
      Double.parseDouble(System.getProperty("org.jacop.fz.decomposition.smoothing", "0.5"));

  // the multipliers are rounded to multiples of 2^-SCALE at most
  private static final int SCALE = 20;

  /** Whether an assignment of the blocks is built from the columns, as a hint for search. */
  private static final boolean PRIMAL =
      !"false".equals(System.getProperty("org.jacop.fz.decomposition.primal"));

  /** The milliseconds of the search for an integer solution of the restricted master. */
  private static final long PRIMAL_MS = Long.getLong("org.jacop.fz.decomposition.primalMs", 1000L);

  /** What the bound did. */
  record Outcome(
      int blocks,
      int rows,
      int iterations,
      int columns,
      boolean certified,
      long bound,
      long millis,
      int pricingTimeOuts,
      Primal primal) {}

  /**
   * An assignment of the blocks' variables from the columns: those of an integer solution of the
   * restricted master when one was found, else the column of largest weight in the master's last
   * solution of each block; its cost is that of the columns when they satisfy the linking rows. The
   * blocks' variables and, for each block, how far its heaviest column is from 1 in the master
   * (plus 0.1) guide the {@code BLOCKS} neighbourhood of large neighbourhood search.
   */
  record Primal(
      IntVar[] vars,
      int[] values,
      boolean feasible,
      long cost,
      long millis,
      IntVar[][] blocks,
      double[] fractionality) {}

  /** A linking row: lo &le; &Sigma; terms &le; hi, its terms by block. */
  static final class Row {
    long lo;
    long hi;
    final boolean hasLo;
    final boolean hasHi;
    // per block: the variables, weights; the counted variables and their values
    final Map<Integer, List<Object[]>> terms = new HashMap<>();

    Row(long lo, boolean hasLo, long hi, boolean hasHi) {
      this.lo = lo;
      this.hasLo = hasLo;
      this.hi = hi;
      this.hasHi = hasHi;
    }
  }

  /** A block: its variables, its objective terms, its rows. */
  static final class Block {
    final List<IntVar> vars = new ArrayList<>();
    final Map<IntVar, Long> objective = new IdentityHashMap<>();
    // linear terms: row index, variable, weight; counted terms: row index, variable, value
    final List<long[]> linear = new ArrayList<>();
    final List<IntVar> linearVars = new ArrayList<>();
    final List<long[]> counted = new ArrayList<>();
    final List<IntVar> countedVars = new ArrayList<>();
    final List<IntVar[][]> clauses = new ArrayList<>();
    // the constraints over the block's variables alone
    final List<Constraint> own = new ArrayList<>();
    // whether its pricing problems are solved in a copy with lazy clause generation, after a
    // search in the store ran out of time; false when the block cannot be copied
    boolean copy;
    boolean copyable = true;
    // whether the huge bounds of its objective variables were searched for
    boolean probed;
  }

  /** A column: its block, its cost, its row activities (row index to value). */
  record Column(int block, long cost, Map<Integer, Long> activity, int[] values) {}

  private final Store store;
  private final List<Row> rows;
  private final List<Block> blocks;
  private final long constant;
  private final List<Var> order;

  private DecompositionBound(
      Store store, List<Row> rows, List<Block> blocks, long constant, List<Var> order) {
    this.store = store;
    this.rows = rows;
    this.blocks = blocks;
    this.constant = constant;
    this.order = order;
  }

  /**
   * Finds the blocks and computes the bound.
   *
   * @param store the store, at a fixpoint at the root.
   * @param clauses clauses kept outside the store, each {positive, negative}; may be empty.
   * @param objective the objective variable.
   * @param maximize whether the objective is maximized.
   * @param order variables to branch on first in a pricing search, such as the annotated ones.
   * @param timeLimitMillis the time limit of the run, or 0 for none.
   * @return what was done, or null when the model has no blocks; the bound is in the objective's
   *     units, a lower bound when minimizing and an upper bound when maximizing.
   */
  static Outcome run(
      Store store,
      List<IntVar[][]> clauses,
      IntVar objective,
      boolean maximize,
      List<Var> order,
      long timeLimitMillis) {
    long start = System.currentTimeMillis();
    long budget = timeLimitMillis > 0 ? (long) (SHARE * timeLimitMillis) : MILLIS;
    DecompositionBound d = detect(store, clauses, objective, maximize, order);
    if (TRACE) {
      System.err.println(
          "% decomposition: "
              + (d == null ? "no blocks" : d.blocks.size() + " blocks, " + d.rows.size() + " rows")
              + " in "
              + (System.currentTimeMillis() - start)
              + " ms");
    }
    if (d == null) {
      return null;
    }
    d.objectiveLo = objective.min();
    d.objectiveHi = objective.max();
    return d.generate(start, start + budget, maximize);
  }

  // ---------------------------------------------------------------- detection

  static DecompositionBound detect(
      Store store, List<IntVar[][]> clauses, IntVar objective, boolean maximize, List<Var> order) {
    if (objective == null || objective.singleton()) {
      return null;
    }
    List<Constraint> all = new ArrayList<>();
    for (Constraint c : Components.constraints(store)) {
      // a relaxation of the whole model, such as the linear relaxation, and a redundant constraint
      // over many blocks, such as the negative cycle check of difference constraints, are not
      // needed in the relaxation
      if (c instanceof SatisfiedPresent s && s.satisfied()
          || c instanceof LinearRelaxation
          || c instanceof DifferenceCycles) {
        continue;
      }
      all.add(c);
    }
    // the equations: a variable that only its equation and one other constraint use, such as a
    // part of a long sum split for lazy clause generation or a cost term, is replaced by its
    // definition in the objective and in the linear rows
    Map<Var, Integer> uses = new IdentityHashMap<>();
    for (Constraint c : all) {
      for (Var v : c.arguments()) {
        uses.merge(v, 1, Integer::sum);
      }
    }
    Map<Constraint, LinearForm> equations = new IdentityHashMap<>();
    Map<IntVar, Constraint> defining = new IdentityHashMap<>();
    Constraint definition = null;
    for (Constraint c : all) {
      LinearForm f = c instanceof BoolClause ? null : LinearForms.of(c);
      if (f == null || f.relation() != LinearForm.EQ) {
        continue;
      }
      equations.put(c, f);
      int at = indexOf(f.vars(), objective);
      if (at >= 0
          && Math.abs(f.weights()[at]) == 1
          && (definition == null || f.vars().length > equations.get(definition).vars().length)) {
        definition = c;
      }
      for (int i = 0; i < f.vars().length; i++) {
        IntVar v = f.vars()[i];
        if (v != objective && !v.singleton() && Math.abs(f.weights()[i]) == 1 && uses.get(v) == 2) {
          defining.putIfAbsent(v, c);
        }
      }
    }
    if (definition != null) {
      defining.put(objective, definition);
    }
    Set<Constraint> used = Collections.newSetFromMap(new IdentityHashMap<>());
    // the objective as a linear sum: cost = constant + sum of terms, cost = obj (or -obj)
    Map<IntVar, Long> terms = new IdentityHashMap<>();
    terms.put(objective, maximize ? -1L : 1L);
    long[] constant = {0};
    expand(terms, constant, null, equations, defining, used);
    // the candidate linking constraints, with their equations expanded
    Set<Constraint> definitions = Collections.newSetFromMap(new IdentityHashMap<>());
    definitions.addAll(defining.values());
    Map<Constraint, LinearForm> forms = new IdentityHashMap<>();
    List<Constraint> linear = new ArrayList<>();
    for (Constraint c : all) {
      if (!(c instanceof BoolClause) && !definitions.contains(c)) {
        LinearForm f = LinearForms.of(c);
        if (f != null && f.relation() != LinearForm.NE) {
          forms.put(c, f);
          linear.add(c);
        }
      }
    }
    for (Constraint c : definitions) {
      if (!used.contains(c)) {
        forms.put(c, equations.get(c));
        linear.add(c);
      }
    }
    for (Constraint c : linear) {
      if (used.contains(c)) {
        continue;
      }
      LinearForm f = forms.get(c);
      Map<IntVar, Long> row = new IdentityHashMap<>();
      long[] rc = {0};
      for (int i = 0; i < f.vars().length; i++) {
        IntVar v = f.vars()[i];
        if (v.singleton()) {
          rc[0] += f.weights()[i] * v.value();
        } else {
          row.merge(v, f.weights()[i], Long::sum);
        }
      }
      expand(row, rc, c, equations, defining, used);
      row.values().removeIf(w -> w == 0);
      IntVar[] vs = row.keySet().toArray(new IntVar[0]);
      long[] ws = new long[vs.length];
      for (int i = 0; i < vs.length; i++) {
        ws[i] = row.get(vs[i]);
      }
      forms.put(c, new LinearForm(vs, ws, f.c() - rc[0], f.relation()));
    }
    terms.values().removeIf(w -> w == 0);
    List<Constraint> candidates = new ArrayList<>();
    List<Constraint> structural = new ArrayList<>();
    for (Constraint c : all) {
      if (used.contains(c)) {
        continue;
      }
      // symmetry breaking constraints between blocks are left out of the relaxation, which stays
      // a relaxation of the model with one optimal solution of each symmetry class
      if (c instanceof CountValuesBounds
          || c instanceof LexChain
          || c instanceof LexOrder
          || c instanceof ValuePrecede
          || c instanceof SeqPrecedeChain
          || forms.containsKey(c) && forms.get(c).vars().length >= 3) {
        candidates.add(c);
      } else {
        structural.add(c);
        forms.remove(c);
      }
    }
    Map<Var, Var> parent = new IdentityHashMap<>();
    for (Constraint c : structural) {
      join(parent, c.arguments());
    }
    for (IntVar[][] clause : clauses) {
      List<Var> vars = new ArrayList<>(List.of(clause[0]));
      vars.addAll(List.of(clause[1]));
      join(parent, vars);
    }
    for (Constraint c : candidates) {
      for (Var v : scope(c, forms)) {
        if (!v.singleton()) {
          parent.putIfAbsent(v, v);
        }
      }
    }
    for (IntVar v : terms.keySet()) {
      parent.putIfAbsent(v, v);
    }
    // put back a candidate that joins fragments of which at most one is large
    for (int round = 0; round < 20; round++) {
      Map<Var, Integer> size = sizes(parent);
      List<Integer> top = new ArrayList<>(size.values());
      top.sort(Collections.reverseOrder());
      int second = 0;
      if (top.size() > 1) {
        second = top.get(1);
      } else if (!top.isEmpty()) {
        second = top.get(0);
      }
      int threshold = Math.max(large(), second / 4);
      boolean changed = false;
      for (Constraint c : candidates) {
        Set<Var> roots = roots(parent, scope(c, forms));
        if (roots.size() < 2) {
          continue;
        }
        int large = 0;
        for (Var r : roots) {
          if (size.get(r) >= threshold) {
            large++;
          }
        }
        if (large <= 1) {
          join(parent, scope(c, forms));
          changed = true;
          size = sizes(parent);
        }
      }
      if (!changed) {
        break;
      }
    }
    if (TRACE) {
      Map<String, Integer> kinds = new TreeMap<>();
      for (Constraint c : all) {
        String key = c.getClass().getSimpleName() + (candidates.contains(c) ? "*" : "");
        kinds.merge(key, 1, Integer::sum);
      }
      List<Integer> top = new ArrayList<>(sizes(parent).values());
      top.sort(Collections.reverseOrder());
      System.err.println(
          "% decomposition: "
              + kinds
              + " components "
              + top.subList(0, Math.min(20, top.size()))
              + " of "
              + top.size());
    }
    List<Constraint> linking = new ArrayList<>();
    for (Constraint c : candidates) {
      if (roots(parent, scope(c, forms)).size() >= 2) {
        linking.add(c);
      }
    }
    if (linking.isEmpty()) {
      return null;
    }
    // the blocks: components touched by the linking rows or the objective
    Map<Var, Integer> blockOf = new IdentityHashMap<>();
    List<Block> blocks = new ArrayList<>();
    for (Constraint c : linking) {
      for (Var v : scope(c, forms)) {
        if (!v.singleton()) {
          blockIndex(find(parent, v), blockOf, blocks);
        }
      }
    }
    for (IntVar v : terms.keySet()) {
      blockIndex(find(parent, v), blockOf, blocks);
    }
    if (blocks.size() > MAX_BLOCKS) {
      return null;
    }
    // the variables of the blocks, in the store's order
    for (int i = 0; i < store.size(); i++) {
      addToBlock(store.vars[i], parent, blockOf, blocks);
    }
    for (Var v : store.variablesHashMap.values()) {
      if (v.index() < 0) {
        addToBlock(v, parent, blockOf, blocks);
      }
    }
    int large = 0;
    for (Block b : blocks) {
      if (b.vars.size() >= large()) {
        large++;
      }
    }
    if (large < MIN_BLOCKS) {
      return null;
    }
    for (Map.Entry<IntVar, Long> e : terms.entrySet()) {
      blocks
          .get(blockOf.get(find(parent, e.getKey())))
          .objective
          .merge(e.getKey(), e.getValue(), Long::sum);
    }
    for (IntVar[][] clause : clauses) {
      Integer b = null;
      for (IntVar[] side : clause) {
        for (IntVar v : side) {
          if (b == null && !v.singleton()) {
            b = blockOf.get(find(parent, v));
          }
        }
      }
      if (b != null) {
        blocks.get(b).clauses.add(clause);
      }
    }
    Set<Constraint> linked = Collections.newSetFromMap(new IdentityHashMap<>());
    linked.addAll(linking);
    for (Constraint c : all) {
      if (used.contains(c) || linked.contains(c)) {
        continue;
      }
      Integer b = null;
      boolean inside = true;
      for (Var v : c.arguments()) {
        if (!v.singleton()) {
          Integer vb = parent.containsKey(v) ? blockOf.get(find(parent, v)) : null;
          if (vb == null || b != null && !b.equals(vb)) {
            inside = false;
            break;
          }
          b = vb;
        }
      }
      if (inside && b != null) {
        blocks.get(b).own.add(c);
      }
    }
    // the rows
    List<Row> rows = new ArrayList<>();
    for (Constraint c : linking) {
      if (c instanceof CountValuesBounds cv) {
        IntVar[] list = cv.countedList();
        for (int[] vlu : cv.countBounds()) {
          Row r = new Row(vlu[1], true, vlu[2], true);
          for (IntVar x : list) {
            if (x.singleton()) {
              if (x.value() == vlu[0]) {
                r.lo--;
                r.hi--;
              }
            } else if (x.domain.contains(vlu[0])) {
              int b = blockOf.get(find(parent, x));
              r.terms
                  .computeIfAbsent(b, k -> new ArrayList<>())
                  .add(new Object[] {x, (long) vlu[0], true});
            }
          }
          if (!r.terms.isEmpty()) {
            rows.add(r);
          }
        }
      } else if (forms.containsKey(c)) {
        LinearForm f = forms.get(c);
        boolean lo = f.relation() != LinearForm.LE;
        boolean hi = f.relation() != LinearForm.GE;
        Row r = new Row(f.c(), lo, f.c(), hi);
        for (int i = 0; i < f.vars().length; i++) {
          IntVar x = f.vars()[i];
          long w = f.weights()[i];
          if (x.singleton()) {
            r.lo -= w * x.value();
            r.hi -= w * x.value();
          } else {
            int b = blockOf.get(find(parent, x));
            r.terms.computeIfAbsent(b, k -> new ArrayList<>()).add(new Object[] {x, w, false});
          }
        }
        rows.add(r);
      }
      if (rows.size() > MAX_ROWS) {
        return null;
      }
    }
    for (int ri = 0; ri < rows.size(); ri++) {
      for (Map.Entry<Integer, List<Object[]>> e : rows.get(ri).terms.entrySet()) {
        Block b = blocks.get(e.getKey());
        for (Object[] t : e.getValue()) {
          if (Boolean.TRUE.equals(t[2])) {
            b.counted.add(new long[] {ri, (Long) t[1]});
            b.countedVars.add((IntVar) t[0]);
          } else {
            b.linear.add(new long[] {ri, (Long) t[1]});
            b.linearVars.add((IntVar) t[0]);
          }
        }
      }
    }
    return new DecompositionBound(store, rows, blocks, constant[0], order);
  }

  // the variables of a candidate: those of its expanded linear form, or its arguments
  private static Collection<? extends Var> scope(Constraint c, Map<Constraint, LinearForm> forms) {
    LinearForm f = forms.get(c);
    return f == null ? c.arguments() : List.of(f.vars());
  }

  /**
   * Replaces in terms + constant each variable that an unused equation defines (other than self) by
   * its definition, marking the equation used.
   */
  private static void expand(
      Map<IntVar, Long> terms,
      long[] constant,
      Constraint self,
      Map<Constraint, LinearForm> equations,
      Map<IntVar, Constraint> defining,
      Set<Constraint> used) {
    ArrayDeque<IntVar> work = new ArrayDeque<>(terms.keySet());
    while (!work.isEmpty()) {
      IntVar v = work.poll();
      Long a = terms.get(v);
      Constraint d = defining.get(v);
      if (a == null || a == 0 || d == null || d == self || used.contains(d)) {
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

  private static int blockIndex(Var root, Map<Var, Integer> blockOf, List<Block> blocks) {
    Integer b = blockOf.get(root);
    if (b == null) {
      b = blocks.size();
      blockOf.put(root, b);
      blocks.add(new Block());
    }
    return b;
  }

  private static void addToBlock(
      Var v, Map<Var, Var> parent, Map<Var, Integer> blockOf, List<Block> blocks) {
    if (!(v instanceof IntVar x) || x.singleton() || !parent.containsKey(v)) {
      return;
    }
    Integer b = blockOf.get(find(parent, v));
    if (b != null) {
      List<IntVar> vars = blocks.get(b).vars;
      vars.add(x);
    }
  }

  private static Map<Var, Integer> sizes(Map<Var, Var> parent) {
    Map<Var, Integer> size = new IdentityHashMap<>();
    for (Var v : new ArrayList<>(parent.keySet())) {
      size.merge(find(parent, v), 1, Integer::sum);
    }
    return size;
  }

  private static Set<Var> roots(Map<Var, Var> parent, Iterable<? extends Var> vars) {
    Set<Var> r = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Var v : vars) {
      if (!v.singleton() && parent.containsKey(v)) {
        r.add(find(parent, v));
      }
    }
    return r;
  }

  private static void join(Map<Var, Var> parent, Iterable<? extends Var> vars) {
    Var first = null;
    for (Var v : vars) {
      if (v.singleton()) {
        continue;
      }
      parent.putIfAbsent(v, v);
      if (first == null) {
        first = v;
      } else {
        Var a = find(parent, first);
        Var b = find(parent, v);
        if (a != b) {
          parent.put(a, b);
        }
      }
    }
  }

  private static Var find(Map<Var, Var> parent, Var x) {
    Var r = x;
    while (parent.get(r) != r) {
      r = parent.get(r);
    }
    while (parent.get(x) != r) {
      Var next = parent.get(x);
      parent.put(x, r);
      x = next;
    }
    return r;
  }

  int blockCount() {
    return blocks.size();
  }

  int rowCount() {
    return rows.size();
  }

  // ---------------------------------------------------------------- column generation

  private Outcome generate(long start, long deadline, boolean maximize) {
    int m = rows.size();
    int nb = blocks.size();
    List<Column> columns = pool;
    Set<String> seen = new LinkedHashSet<>();
    long best = Long.MIN_VALUE;
    boolean certified = false;
    int iterations = 0;
    int timeOuts = 0;
    double[] y = new double[m];
    double[] mu = new double[nb];
    // the multipliers of the best bound, the centre of the smoothing of the duals (P. Wentges,
    // Weighted Dantzig-Wolfe decomposition for linear mixed-integer programming, International
    // Transactions in Operational Research 4 (1997) 151-162): the pricing problems get a convex
    // combination of the centre and the master's duals, which damps their oscillation
    double[] centre = null;
    double alpha = SMOOTHING;
    // the bound of the objective at the root, in the minimized cost
    long root = maximize ? -objectiveHi : objectiveLo;
    long budget = deadline - start;
    long improved = start;
    while (System.currentTimeMillis() < deadline) {
      long now = System.currentTimeMillis();
      // a bound that has not risen for a quarter of the time, or that is no better than the
      // root's after half of it, is not worth the rest of the time
      long quarter = Math.max(PATIENCE_MS, budget / 4);
      if (iterations > 0
          && (now - improved > quarter || now - start > 2 * quarter && best <= root)) {
        break;
      }
      iterations++;
      double[] price = y;
      if (iterations > 1) {
        // the cost of the artificial columns, which bounds the duals: above any column's cost
        double big = 1;
        for (Column c : columns) {
          big = Math.max(big, 1 + 2 * Math.abs((double) c.cost()));
        }
        double[][] duals = master(columns, big);
        if (duals.length == 0) {
          break;
        }
        y = duals[0];
        mu = duals[1];
        weights = duals[2];
        price = y;
        if (centre != null && alpha > 0) {
          price = new double[m];
          for (int r = 0; r < m; r++) {
            price[r] = alpha * centre[r] + (1 - alpha) * y[r];
          }
        }
      }
      // the multipliers, projected to the signs the rows allow, rounded to multiples of 1/K
      long k = scale(price);
      long[] yk = new long[m];
      for (int r = 0; r < m; r++) {
        Row row = rows.get(r);
        double v = price[r];
        if (!row.hasLo && v > 0 || !row.hasHi && v < 0) {
          v = 0;
        }
        yk[r] = Math.round(v * k);
      }
      // the Lagrangian bound K L = sum_r Y_r side_r + K constant + sum_b min_b
      long lk;
      boolean exact = true;
      try {
        lk = Math.multiplyExact(k, constant);
        for (int r = 0; r < m; r++) {
          Row row = rows.get(r);
          long side = yk[r] > 0 ? row.lo : row.hi;
          if (yk[r] != 0) {
            lk = Math.addExact(lk, Math.multiplyExact(yk[r], side));
          }
        }
      } catch (ArithmeticException _) {
        break;
      }
      int added = 0;
      int priced = 0;
      for (int b = 0; b < nb && System.currentTimeMillis() < deadline; b++) {
        priced++;
        Pricing p = price(b, k, yk, deadline);
        if (p == null) {
          // no solution of the block at all: the model has none
          exact = false;
          break;
        }
        if (!p.complete) {
          timeOuts++;
          if (TRACE) {
            System.err.println(
                "% decomposition: block "
                    + b
                    + " ("
                    + blocks.get(b).vars.size()
                    + " variables) timed out "
                    + (blocks.get(b).copy && blocks.get(b).copyable ? "in a copy" : "in the store")
                    + ", lower bound "
                    + p.lower);
          }
        }
        // the minimum of the block, or a lower bound of it when the search ran out of time
        long least = p.complete ? p.value : p.lower;
        if (least == Long.MIN_VALUE) {
          exact = false;
        } else {
          try {
            lk = Math.addExact(lk, least);
          } catch (ArithmeticException _) {
            exact = false;
          }
        }
        for (Column c : p.columns) {
          String key = c.block() + ":" + c.cost() + ":" + c.activity();
          // reduced cost below the block's convexity dual: improves the master
          double reduced = (double) c.cost();
          for (Map.Entry<Integer, Long> e : c.activity().entrySet()) {
            reduced -= y[e.getKey()] * e.getValue();
          }
          if ((iterations == 1 || reduced < mu[b] - 1e-7) && seen.add(key)) {
            columns.add(c);
            added++;
          }
        }
      }
      // the bound needs the minimum of every block
      if (priced < nb) {
        exact = false;
      }
      if (exact) {
        long bound = Math.floorDiv(lk, k) + (Math.floorMod(lk, k) == 0 ? 0 : 1);
        if (bound > best) {
          best = bound;
          certified = true;
          centre = price;
          improved = System.currentTimeMillis();
          if (maximize ? -best <= objectiveLo : best >= objectiveHi) {
            break;
          }
        }
      }
      if (TRACE) {
        System.err.println(
            "% decomposition: iteration "
                + iterations
                + " columns "
                + columns.size()
                + " added "
                + added
                + (exact ? " bound " + Math.floorDiv(lk, k) : " no bound")
                + " best "
                + best
                + " time "
                + (System.currentTimeMillis() - start));
      }
      if (added == 0 && iterations > 1) {
        if (price == y) {
          break;
        }
        // the smoothed duals priced no column of the master's: the master's own next
        alpha = 0;
      } else if (alpha == 0 && price == y) {
        alpha = SMOOTHING;
      }
    }
    long bound = 0;
    if (certified) {
      bound = maximize ? -best : best;
    }
    long millis = System.currentTimeMillis() - start;
    Primal primal = PRIMAL ? primal(maximize) : null;
    return new Outcome(
        nb, m, iterations, columns.size(), certified, bound, millis, timeOuts, primal);
  }

  // the columns of column generation and their weights in the last solution of the master
  private final List<Column> pool = new ArrayList<>();
  private double[] weights = new double[0];

  // the bounds of the objective at the root, set by the caller
  long objectiveLo = Long.MIN_VALUE;
  long objectiveHi = Long.MAX_VALUE;

  /**
   * Builds an assignment of the blocks' variables from the columns: an integer solution of the
   * restricted master (one column per block, the linking rows, the least cost) found by lazy clause
   * generation within {@link #PRIMAL_MS}, starting from the column of largest weight in the
   * master's last solution; that column of each block when there is none. This is the restricted
   * master heuristic of column generation (price and branch), as in C. Joncour, S. Michel, R.
   * Sadykov, D. Sverdlov and F. Vanderbeck, Column generation based primal heuristics, Electronic
   * Notes in Discrete Mathematics 36 (2010) 695-702.
   */
  private Primal primal(boolean maximize) {
    long start = System.currentTimeMillis();
    int nb = blocks.size();
    int m = rows.size();
    if (pool.isEmpty()) {
      return null;
    }
    double big = 1;
    for (Column c : pool) {
      big = Math.max(big, 1 + 2 * Math.abs((double) c.cost()));
    }
    double[][] last = master(pool, big);
    if (last.length == 3) {
      weights = last[2];
    }
    // the column of largest weight of each block
    int[] heaviest = new int[nb];
    Arrays.fill(heaviest, -1);
    List<List<Integer>> byBlock = new ArrayList<>();
    for (int b = 0; b < nb; b++) {
      byBlock.add(new ArrayList<>());
    }
    for (int j = 0; j < pool.size(); j++) {
      int b = pool.get(j).block();
      byBlock.get(b).add(j);
      double wj = j < weights.length ? weights[j] : 0;
      if (heaviest[b] < 0 || wj > (heaviest[b] < weights.length ? weights[heaviest[b]] : 0)) {
        heaviest[b] = j;
      }
    }
    for (int b = 0; b < nb; b++) {
      if (heaviest[b] < 0) {
        return null;
      }
    }
    if (TRACE) {
      double lpCost = constant;
      int integral = 0;
      for (int j = 0; j < pool.size() && j < weights.length; j++) {
        lpCost += weights[j] * pool.get(j).cost();
      }
      for (int b = 0; b < nb; b++) {
        if (heaviest[b] < weights.length && weights[heaviest[b]] > 0.99) {
          integral++;
        }
      }
      System.err.println(
          "% decomposition: master cost "
              + lpCost
              + ", blocks with a column at 1: "
              + integral
              + " of "
              + nb);
    }
    int[] chosen = heaviest.clone();
    boolean feasible = false;
    long cost = 0;
    try {
      Store s = new Store();
      BooleanVar[] z = new BooleanVar[pool.size()];
      for (int j = 0; j < z.length; j++) {
        z[j] = new BooleanVar(s);
      }
      for (int b = 0; b < nb; b++) {
        List<Integer> js = byBlock.get(b);
        IntVar[] xs = new IntVar[js.size()];
        int[] ones = new int[js.size()];
        for (int i = 0; i < xs.length; i++) {
          xs[i] = z[js.get(i)];
          ones[i] = 1;
        }
        s.impose(new LinearInt(xs, ones, "==", 1));
      }
      List<List<IntVar>> rowVars = new ArrayList<>();
      List<List<Integer>> rowWeights = new ArrayList<>();
      for (int r = 0; r < m; r++) {
        rowVars.add(new ArrayList<>());
        rowWeights.add(new ArrayList<>());
      }
      for (int j = 0; j < z.length; j++) {
        for (Map.Entry<Integer, Long> e : pool.get(j).activity().entrySet()) {
          rowVars.get(e.getKey()).add(z[j]);
          rowWeights.get(e.getKey()).add(Math.toIntExact(e.getValue()));
        }
      }
      for (int r = 0; r < m; r++) {
        Row row = rows.get(r);
        IntVar[] xs = rowVars.get(r).toArray(new IntVar[0]);
        int[] ws = rowWeights.get(r).stream().mapToInt(Integer::intValue).toArray();
        if (xs.length == 0) {
          // no column touches the row
          if (row.hasLo && row.lo > 0 || row.hasHi && row.hi < 0) {
            throw new ArithmeticException("an empty row of the restricted master is violated");
          }
          continue;
        }
        if (row.hasLo && row.hasHi && row.lo == row.hi) {
          s.impose(new LinearInt(xs, ws, "==", Math.toIntExact(row.lo)));
        } else {
          if (row.hasLo) {
            s.impose(new LinearInt(xs, ws, ">=", Math.toIntExact(row.lo)));
          }
          if (row.hasHi) {
            s.impose(new LinearInt(xs, ws, "<=", Math.toIntExact(row.hi)));
          }
        }
      }
      long lo = 0;
      long hi = 0;
      for (int b = 0; b < nb; b++) {
        long bl = Long.MAX_VALUE;
        long bh = Long.MIN_VALUE;
        for (int j : byBlock.get(b)) {
          bl = Math.min(bl, pool.get(j).cost());
          bh = Math.max(bh, pool.get(j).cost());
        }
        lo += bl;
        hi += bh;
      }
      IntVar total = new IntVar(s, Math.toIntExact(lo), Math.toIntExact(hi));
      IntVar[] xs = new IntVar[z.length + 1];
      int[] ws = new int[z.length + 1];
      for (int j = 0; j < z.length; j++) {
        xs[j] = z[j];
        ws[j] = Math.toIntExact(pool.get(j).cost());
      }
      xs[z.length] = total;
      ws[z.length] = -1;
      s.impose(new LinearInt(xs, ws, "==", 0));
      if (!s.consistency()) {
        throw new ArithmeticException("the restricted master has no solution");
      }
      LcgSolver solver = new LcgSolver(s);
      int[] phase = new int[z.length];
      for (int b = 0; b < nb; b++) {
        phase[heaviest[b]] = 1;
      }
      solver.setPhase(z, phase);
      long left = PRIMAL_MS;
      solver.sat().setDeadline(System.nanoTime() + left * 1_000_000L);
      solver.setTimeLimit(left);
      int[] found = new int[nb];
      boolean[] any = {false};
      long[] best = {Long.MAX_VALUE};
      solver.onSolution(
          () -> {
            any[0] = true;
            best[0] = total.value();
            for (int j = 0; j < z.length; j++) {
              if (z[j].value() == 1) {
                found[pool.get(j).block()] = j;
              }
            }
          });
      solver.minimize(total);
      if (any[0]) {
        System.arraycopy(found, 0, chosen, 0, nb);
        feasible = true;
        cost = best[0] + constant;
      }
    } catch (ArithmeticException | IllegalArgumentException e) {
      if (TRACE) {
        System.err.println("% decomposition: no restricted master: " + e.getMessage());
      }
    }
    List<IntVar> vars = new ArrayList<>();
    List<Integer> values = new ArrayList<>();
    IntVar[][] blockVars = new IntVar[nb][];
    double[] fractionality = new double[nb];
    for (int b = 0; b < nb; b++) {
      blockVars[b] = blocks.get(b).vars.toArray(new IntVar[0]);
      double w = heaviest[b] < weights.length ? weights[heaviest[b]] : 0;
      fractionality[b] = Math.max(0, 1 - w) + 0.1;
    }
    for (int b = 0; b < nb; b++) {
      Column c = pool.get(chosen[b]);
      Block block = blocks.get(b);
      for (int i = 0; i < block.vars.size(); i++) {
        vars.add(block.vars.get(i));
        values.add(c.values()[i]);
      }
    }
    if (TRACE) {
      System.err.println(
          "% decomposition: primal "
              + (feasible ? "restricted master cost " + cost : "heaviest columns")
              + " over "
              + vars.size()
              + " variables in "
              + (System.currentTimeMillis() - start)
              + " ms");
    }
    return new Primal(
        vars.toArray(new IntVar[0]),
        values.stream().mapToInt(Integer::intValue).toArray(),
        feasible,
        maximize ? -cost : cost,
        System.currentTimeMillis() - start,
        blockVars,
        fractionality);
  }

  // the scale K = 2^s of the multipliers: as fine as the magnitudes allow
  private long scale(double[] y) {
    double maxY = 1;
    for (double v : y) {
      maxY = Math.max(maxY, Math.abs(v));
    }
    // the least reduced cost of a block stays above -2^30, so that a copy of the block can hold it
    // in an integer variable, and the bound and the reduced costs within 2^60
    double maxLeast = 1;
    double maxBlock = 1;
    for (Block b : blocks) {
      double a = 0;
      for (int i = 0; i < b.linear.size(); i++) {
        a += Math.abs((double) b.linear.get(i)[1]) * magnitude(b.linearVars.get(i));
      }
      a += b.counted.size();
      a *= maxY + 1;
      double least = a;
      double full = a;
      for (Map.Entry<IntVar, Long> e : b.objective.entrySet()) {
        IntVar x = e.getKey();
        double weight = e.getValue();
        least +=
            Math.abs(Math.min(0, weight > 0 ? weight * x.min() : weight * x.max()))
                + Math.abs(weight);
        full += Math.abs(weight) * magnitude(x);
      }
      maxLeast = Math.max(maxLeast, least);
      maxBlock = Math.max(maxBlock, full);
    }
    double room =
        Math.min(
            Math.pow(2, 30) / maxLeast,
            Math.pow(2, 60) / (maxBlock * Math.max(1, rows.size() + blocks.size())));
    int s = SCALE;
    while (s > 0 && Math.pow(2, s) > room) {
      s--;
    }
    return 1L << s;
  }

  private static double magnitude(IntVar x) {
    return Math.max(Math.abs((double) x.min()), Math.abs((double) x.max()));
  }

  /**
   * The master LP over the columns, with artificial columns of cost {@code big} for every row; an
   * empty array if JaLP gives no duals.
   */
  private double[][] master(List<Column> columns, double big) {
    int m = rows.size();
    int nb = blocks.size();
    int nr = m + nb;
    List<List<int[]>> idx = new ArrayList<>();
    List<List<Double>> val = new ArrayList<>();
    for (int r = 0; r < nr; r++) {
      idx.add(new ArrayList<>());
      val.add(new ArrayList<>());
    }
    List<Double> cost = new ArrayList<>();
    int j = 0;
    for (Column c : columns) {
      for (Map.Entry<Integer, Long> e : c.activity().entrySet()) {
        idx.get(e.getKey()).add(new int[] {j});
        val.get(e.getKey()).add((double) e.getValue());
      }
      idx.get(m + c.block()).add(new int[] {j});
      val.get(m + c.block()).add(1.0);
      cost.add((double) c.cost());
      j++;
    }
    for (int r = 0; r < nr; r++) {
      boolean lo = r >= m || rows.get(r).hasLo;
      boolean hi = r >= m || rows.get(r).hasHi;
      if (lo) {
        idx.get(r).add(new int[] {j});
        val.get(r).add(1.0);
        cost.add(big);
        j++;
      }
      if (hi) {
        idx.get(r).add(new int[] {j});
        val.get(r).add(-1.0);
        cost.add(big);
        j++;
      }
    }
    int[][] cols = new int[nr][];
    double[][] wts = new double[nr][];
    double[] rowLo = new double[nr];
    double[] rowHi = new double[nr];
    for (int r = 0; r < nr; r++) {
      List<int[]> ix = idx.get(r);
      cols[r] = new int[ix.size()];
      wts[r] = new double[ix.size()];
      for (int i = 0; i < ix.size(); i++) {
        cols[r][i] = ix.get(i)[0];
        wts[r][i] = val.get(r).get(i);
      }
      if (r < m) {
        Row row = rows.get(r);
        rowLo[r] = row.hasLo ? row.lo : Double.NEGATIVE_INFINITY;
        rowHi[r] = row.hasHi ? row.hi : Double.POSITIVE_INFINITY;
      } else {
        rowLo[r] = 1;
        rowHi[r] = 1;
      }
    }
    double[] c = new double[cost.size()];
    for (int i = 0; i < c.length; i++) {
      c[i] = cost.get(i);
    }
    // JaLP's dual simplex cycles on some of these degenerate masters and its primal simplex
    // stalls on others: each gets a pivot limit, and the duals of the last basis are taken in
    // any case, since the Lagrangian bound holds for any multipliers
    RevisedDualSimplex lp = new RevisedDualSimplex(cols, wts, rowLo, rowHi, c, false);
    int status = lp.solve(PIVOTS);
    if (status != RevisedDualSimplex.OPTIMAL && status != RevisedDualSimplex.INFEASIBLE) {
      RevisedDualSimplex primal = new RevisedDualSimplex(cols, wts, rowLo, rowHi, c, false);
      int s2 = primal.solvePrimal(PIVOTS);
      if (s2 == RevisedDualSimplex.OPTIMAL) {
        lp = primal;
        status = s2;
      }
    }
    if (status == RevisedDualSimplex.INFEASIBLE || status == RevisedDualSimplex.UNBOUNDED) {
      return new double[0][];
    }
    double[] d = lp.duals();
    double[] y = Arrays.copyOf(d, m);
    double[] mu = Arrays.copyOfRange(d, m, nr);
    for (double v : d) {
      if (!Double.isFinite(v)) {
        return new double[0][];
      }
    }
    double[] x = new double[columns.size()];
    for (int i = 0; i < x.length; i++) {
      x[i] = lp.value(i);
    }
    return new double[][] {y, mu, x};
  }

  private static final class Pricing {
    boolean complete;
    long value = Long.MAX_VALUE;
    // a lower bound of the minimum when it is not known, or Long.MIN_VALUE
    long lower = Long.MIN_VALUE;
    final List<Column> columns = new ArrayList<>();
  }

  /**
   * Minimizes K cost - Y &middot; A over the solutions of block b by branch and bound in the store;
   * null if the block has no solution.
   */
  private Pricing price(int b, long k, long[] yk, long deadline) {
    Block block = blocks.get(b);
    // the reduced cost of each variable: a weight on its value and a cost on some values
    Map<IntVar, long[]> linear = new IdentityHashMap<>();
    Map<IntVar, Map<Integer, Long>> valued = new IdentityHashMap<>();
    for (Map.Entry<IntVar, Long> e : block.objective.entrySet()) {
      linear.computeIfAbsent(e.getKey(), x -> new long[1])[0] += k * e.getValue();
    }
    for (int i = 0; i < block.linear.size(); i++) {
      long[] t = block.linear.get(i);
      linear.computeIfAbsent(block.linearVars.get(i), x -> new long[1])[0] -= yk[(int) t[0]] * t[1];
    }
    for (int i = 0; i < block.counted.size(); i++) {
      long[] t = block.counted.get(i);
      if (yk[(int) t[0]] != 0) {
        valued
            .computeIfAbsent(block.countedVars.get(i), x -> new HashMap<>())
            .merge((int) t[1], -yk[(int) t[0]], Long::sum);
      }
    }
    for (IntVar x : block.countedVars) {
      valued.computeIfAbsent(x, z -> new HashMap<>());
    }
    List<IntVar> costVars = new ArrayList<>();
    Set<IntVar> cv = Collections.newSetFromMap(new IdentityHashMap<>());
    for (IntVar x : linear.keySet()) {
      if (cv.add(x)) {
        costVars.add(x);
      }
    }
    for (IntVar x : valued.keySet()) {
      if (cv.add(x)) {
        costVars.add(x);
      }
    }
    for (IntVar x : block.linearVars) {
      if (cv.add(x)) {
        costVars.add(x);
      }
    }
    IntVar[] cvars = costVars.toArray(new IntVar[0]);
    long[] w = new long[cvars.length];
    @SuppressWarnings("unchecked")
    Map<Integer, Long>[] vc = new Map[cvars.length];
    for (int i = 0; i < cvars.length; i++) {
      long[] lw = linear.get(cvars[i]);
      w[i] = lw == null ? 0 : lw[0];
      vc[i] = valued.get(cvars[i]);
    }
    if (block.copy && block.copyable) {
      Pricing p = priceCopy(b, block, cvars, w, vc, deadline);
      if (block.copyable) {
        return p;
      }
    }
    Pricing result = priceInStore(b, block, cvars, w, vc, deadline);
    if (result != null
        && !result.complete
        && block.copyable
        && System.currentTimeMillis() < deadline) {
      // the search in the store ran out of time: the block's pricing problems go to a copy with
      // lazy clause generation from now on
      block.copy = true;
      Pricing p = priceCopy(b, block, cvars, w, vc, deadline);
      if (block.copyable) {
        p.columns.addAll(result.columns);
        return p;
      }
    }
    return result;
  }

  /** Minimizes the reduced cost of block b by branch and bound in the store. */
  private Pricing priceInStore(
      int b, Block block, IntVar[] cvars, long[] w, Map<Integer, Long>[] vc, long deadline) {
    List<IntVar> branch = branchOrder(block);
    Pricing result = new Pricing();
    ReducedCost rc = new ReducedCost(cvars, w, vc);
    List<Constraint> posted = new ArrayList<>();
    for (IntVar[][] clause : block.clauses) {
      Constraint c = new BoolClause(clause[0], clause[1]);
      store.impose(c);
      posted.add(c);
    }
    store.impose(rc);
    // the least reduced cost over the domains at the root, a lower bound of the minimum
    result.lower = rc.least();
    posted.add(rc);
    IntVar[] array = branch.toArray(new IntVar[0]);
    DepthFirstSearch<IntVar> label = new DepthFirstSearch<>();
    label.setPrintInfo(false);
    label.setAssignSolution(false);
    long left =
        Math.min(block.copyable ? storeMillis() : PRICE_MS, deadline - System.currentTimeMillis());
    if (left <= 0) {
      for (Constraint c : posted) {
        c.removeConstraint();
      }
      result.complete = false;
      return result;
    }
    label.setTimeOutMilliseconds(left);
    Map<String, Column> found = new LinkedHashMap<>();
    SimpleSolutionListener<IntVar> listener =
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(
              Search<IntVar> search, SelectChoicePoint<IntVar> select) {
            long value = rc.value();
            if (value < rc.best) {
              rc.best = value;
              Column c = column(b, block, IntVar::value);
              found.put(c.cost() + ":" + c.activity() + ":" + Arrays.toString(c.values()), c);
            }
            return false;
          }
        };
    listener.searchAll(true);
    label.setSolutionListener(listener);
    try {
      // a large domain is split, so that the depth of the search stays its logarithm
      boolean large = false;
      for (IntVar x : array) {
        large |= x.getSize() > 64;
      }
      SelectChoicePoint<IntVar> select =
          large
              ? new SplitSelect<>(array, new SmallestDomain<>(), new IndomainMiddle<>())
              : new SimpleSelect<>(array, new SmallestDomain<>(), new IndomainMin<>());
      label.labeling(store, select);
    } finally {
      for (Constraint c : posted) {
        c.removeConstraint();
      }
    }
    result.complete = !label.timeOutOccured;
    if (found.isEmpty()) {
      return result.complete ? null : result;
    }
    result.value = rc.best;
    // the last columns found are the best ones
    List<Column> cs = new ArrayList<>(found.values());
    int from = Math.max(0, cs.size() - 3);
    result.columns.addAll(cs.subList(from, cs.size()));
    return result;
  }

  /** A copy of a block in a store of its own, with the map from the block's variables. */
  private record Copy(Store store, VarMap map) {}

  // the bound beyond which a variable of the objective is first bounded by a search in a copy
  private static final long HUGE = 1L << 24;

  // the reduced cost of a block in a copy is held in an integer variable within these bounds
  private static final long COST_RANGE = 1L << 30;

  /**
   * Copies the block's variables and constraints into a store of its own; marks the block as not
   * copyable, and returns null, when a constraint or variable cannot be copied.
   */
  private Copy copy(Block block) {
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
    try {
      for (Constraint c : block.own) {
        if (!Copyable.canCopy(c)) {
          throw new IllegalArgumentException(c + " cannot be copied");
        }
        copy.impose(((Copyable<?>) c).copy(map));
      }
      for (IntVar x : block.vars) {
        map.get(x);
      }
      // the variables of the clauses, which the solver of the copy knows when it is built
      for (IntVar[][] clause : block.clauses) {
        map.get(clause[0]);
        map.get(clause[1]);
      }
    } catch (IllegalArgumentException e) {
      if (TRACE) {
        System.err.println("% decomposition: a block is not copied: " + e.getMessage());
      }
      block.copyable = false;
      return null;
    }
    return new Copy(copy, map);
  }

  /**
   * Bounds each variable of the block's objective whose bound on the side its weight minimizes is
   * huge, such as a cost that the model sets by reified equalities, by minimizing it in a copy of
   * the block, and imposes the bound found in the store: it holds in every solution, so it is a
   * root fact. Marks the block as not copyable when a bound is not found in time.
   */
  private void probe(Block block, long deadline) {
    block.probed = true;
    for (Map.Entry<IntVar, Long> e : block.objective.entrySet()) {
      IntVar x = e.getKey();
      boolean up = e.getValue() < 0;
      if (x.singleton() || (up ? x.max() < HUGE : x.min() > -HUGE)) {
        continue;
      }
      Copy c = copy(block);
      if (c == null) {
        return;
      }
      IntVar y = c.map().get(x);
      IntVar target = y;
      if (up) {
        target = new IntVar(c.store(), -y.max(), -y.min());
        c.store().impose(new XplusYeqC(y, target, 0));
      }
      LcgSolver solver = new LcgSolver(c.store());
      for (IntVar[][] clause : block.clauses) {
        solver.addClause(c.map().get(clause[0]), c.map().get(clause[1]));
      }
      long left = Math.min(PRICE_MS, deadline - System.currentTimeMillis());
      if (left <= 0) {
        block.copyable = false;
        return;
      }
      solver.sat().setDeadline(System.nanoTime() + left * 1_000_000L);
      solver.setTimeLimit(left);
      int status = solver.minimize(target);
      if (status == CdclSolver.UNSAT) {
        // the block has no solution: neither has the model, which the search finds
        return;
      }
      if (status != CdclSolver.SAT) {
        block.copyable = false;
        return;
      }
      int v = solver.value(target);
      store.impose(up ? new XlteqC(x, -v) : new XgteqC(x, v));
      if (!store.consistency()) {
        return;
      }
    }
  }

  /**
   * Minimizes the reduced cost of block b with lazy clause generation in a store of its own, which
   * holds copies of the block's variables, of its constraints and of its clauses; marks the block
   * as not copyable, and returns null, when one of its constraints or variables cannot be copied.
   */
  private Pricing priceCopy(
      int b, Block block, IntVar[] cvars, long[] w, Map<Integer, Long>[] vc, long deadline) {
    if (!block.probed) {
      probe(block, deadline);
      if (!block.copyable) {
        return null;
      }
    }
    Copy c = copy(block);
    if (c == null) {
      return null;
    }
    Store copy = c.store();
    VarMap map = c.map();
    IntVar cost;
    // whether the reduced cost may be above its variable's upper bound
    boolean clipped;
    try {
      // the reduced cost: cost = sum w_i x_i + sum over the costed values of c_iv [x_i = v]
      List<IntVar> terms = new ArrayList<>();
      List<Integer> weights = new ArrayList<>();
      long lo = 0;
      long hi = 0;
      for (int i = 0; i < cvars.length; i++) {
        IntVar x = map.get(cvars[i]);
        if (w[i] != 0) {
          terms.add(x);
          weights.add(Math.toIntExact(w[i]));
          lo += Math.min(w[i] * x.min(), w[i] * x.max());
          hi += Math.max(w[i] * x.min(), w[i] * x.max());
        }
        if (vc[i] != null) {
          for (Map.Entry<Integer, Long> e : vc[i].entrySet()) {
            if (e.getValue() != 0 && x.domain.contains(e.getKey())) {
              BooleanVar is = new BooleanVar(copy);
              copy.impose(new Reified(new XeqC(x, e.getKey()), is));
              terms.add(is);
              weights.add(Math.toIntExact(e.getValue()));
              lo += Math.min(0, e.getValue());
              hi += Math.max(0, e.getValue());
            }
          }
        }
      }
      if (lo < -COST_RANGE) {
        throw new ArithmeticException("the reduced cost has no lower bound");
      }
      clipped = hi > COST_RANGE;
      cost = new IntVar(copy, (int) lo, (int) Math.min(hi, COST_RANGE));
      terms.add(cost);
      weights.add(-1);
      copy.impose(
          new LinearInt(
              terms.toArray(new IntVar[0]),
              weights.stream().mapToInt(Integer::intValue).toArray(),
              "==",
              0));
    } catch (IllegalArgumentException | ArithmeticException e) {
      block.copyable = false;
      if (TRACE) {
        System.err.println("% decomposition: block " + b + " is not copied: " + e.getMessage());
      }
      return null;
    }
    LcgSolver solver = new LcgSolver(copy);
    for (IntVar[][] clause : block.clauses) {
      solver.addClause(map.get(clause[0]), map.get(clause[1]));
    }
    Pricing result = new Pricing();
    long left = Math.min(PRICE_MS, deadline - System.currentTimeMillis());
    if (left <= 0) {
      return result;
    }
    solver.sat().setDeadline(System.nanoTime() + left * 1_000_000L);
    solver.setTimeLimit(left);
    List<Column> found = new ArrayList<>();
    solver.onSolution(() -> found.add(column(b, block, x -> map.get(x).value())));
    // the bounds that the search proves at the root
    long[] lower = {cost.min()};
    solver.onBound(v -> lower[0] = Math.max(lower[0], v));
    int status = solver.minimize(cost);
    if (status == CdclSolver.UNSAT) {
      // no solution at all, or, when the cost is clipped, none of a cost up to the clip
      if (!clipped) {
        return null;
      }
      result.lower = COST_RANGE + 1;
      return result;
    }
    result.complete = status == CdclSolver.SAT;
    if (result.complete) {
      result.value = solver.value(cost);
    } else {
      // under the bound of branch and bound: no solution is below the best one and the bound
      result.lower = found.isEmpty() ? lower[0] : Math.min(lower[0], solver.value(cost));
    }
    int from = Math.max(0, found.size() - 3);
    result.columns.addAll(found.subList(from, found.size()));
    return result;
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

  private List<IntVar> branchOrder(Block block) {
    Set<IntVar> members = Collections.newSetFromMap(new IdentityHashMap<>());
    members.addAll(block.vars);
    Set<IntVar> added = Collections.newSetFromMap(new IdentityHashMap<>());
    List<IntVar> vars = new ArrayList<>();
    for (Var v : order) {
      if (v instanceof IntVar x && members.contains(x) && !x.singleton() && added.add(x)) {
        vars.add(x);
      }
    }
    for (IntVar x : block.vars) {
      if (!x.singleton() && added.add(x)) {
        vars.add(x);
      }
    }
    return vars;
  }

  // the column of a solution of block b, given by the values of its variables: its cost and its
  // row activities
  private Column column(int b, Block block, ToIntFunction<IntVar> value) {
    long cost = 0;
    for (Map.Entry<IntVar, Long> e : block.objective.entrySet()) {
      cost += e.getValue() * value.applyAsInt(e.getKey());
    }
    Map<Integer, Long> activity = new TreeMap<>();
    for (int i = 0; i < block.linear.size(); i++) {
      long[] t = block.linear.get(i);
      activity.merge((int) t[0], t[1] * value.applyAsInt(block.linearVars.get(i)), Long::sum);
    }
    for (int i = 0; i < block.counted.size(); i++) {
      long[] t = block.counted.get(i);
      if (value.applyAsInt(block.countedVars.get(i)) == t[1]) {
        activity.merge((int) t[0], 1L, Long::sum);
      }
    }
    activity.values().removeIf(v -> v == 0);
    int[] values = new int[block.vars.size()];
    for (int i = 0; i < values.length; i++) {
      values[i] = value.applyAsInt(block.vars.get(i));
    }
    return new Column(b, cost, activity, values);
  }

  /**
   * The reduced cost of a pricing problem as a propagator: &Sigma; w<sub>i</sub> x<sub>i</sub> +
   * &Sigma; c<sub>i</sub>(x<sub>i</sub>) &lt; best, where c<sub>i</sub> gives some values a cost.
   * It fails when the least cost over the domains reaches the best found, and removes the values
   * that would reach it.
   */
  static final class ReducedCost extends Constraint {

    static final AtomicInteger idNumber = new AtomicInteger(0);

    final IntVar[] x;
    final long[] w;
    final Map<Integer, Long>[] vc;
    long best = Long.MAX_VALUE;

    ReducedCost(IntVar[] x, long[] w, Map<Integer, Long>[] vc) {
      numberId = idNumber.incrementAndGet();
      this.x = x;
      this.w = w;
      this.vc = vc;
      setScope(x);
    }

    long value() {
      long s = 0;
      for (int i = 0; i < x.length; i++) {
        s += cost(i, x[i].value());
      }
      return s;
    }

    private long cost(int i, int v) {
      long c = w[i] * v;
      if (vc[i] != null) {
        Long e = vc[i].get(v);
        if (e != null) {
          c += e;
        }
      }
      return c;
    }

    // the least cost of variable i over its domain
    private long least(int i) {
      IntDomain d = x[i].dom();
      if (vc[i] == null || vc[i].isEmpty()) {
        return w[i] >= 0 ? w[i] * d.min() : w[i] * d.max();
      }
      if (d.getSize() > 4096) {
        long m = w[i] >= 0 ? w[i] * d.min() : w[i] * d.max();
        long extra = 0;
        for (long e : vc[i].values()) {
          extra = Math.min(extra, e);
        }
        return m + extra;
      }
      long m = Long.MAX_VALUE;
      for (ValueEnumeration en = d.valueEnumeration(); en.hasMoreElements(); ) {
        m = Math.min(m, cost(i, en.nextElement()));
      }
      return m;
    }

    // the least cost over the current domains
    long least() {
      double estimate = 0;
      for (int i = 0; i < x.length; i++) {
        IntDomain d = x[i].dom();
        estimate +=
            Math.abs((double) w[i])
                * Math.max(Math.abs((double) d.min()), Math.abs((double) d.max()));
      }
      if (estimate > 0x1p61) {
        return Long.MIN_VALUE;
      }
      long sum = 0;
      for (int i = 0; i < x.length; i++) {
        sum += least(i);
      }
      return sum;
    }

    @Override
    public void consistency(Store store) {
      if (best == Long.MAX_VALUE) {
        return;
      }
      long[] lo = new long[x.length];
      long sum = 0;
      for (int i = 0; i < x.length; i++) {
        lo[i] = least(i);
        sum += lo[i];
      }
      if (sum >= best) {
        throw Store.failException;
      }
      for (int i = 0; i < x.length; i++) {
        IntDomain d = x[i].dom();
        if (d.singleton()) {
          continue;
        }
        long slack = best - (sum - lo[i]);
        // a value of cost >= slack cannot be in a better solution
        if (vc[i] == null || vc[i].isEmpty()) {
          if (w[i] > 0) {
            long max = Math.floorDiv(slack - 1, w[i]);
            if (max < d.max()) {
              x[i].domain.inMax(store.level, x[i], (int) Math.max(Integer.MIN_VALUE, max));
            }
          } else if (w[i] < 0) {
            long min = -Math.floorDiv(slack - 1, -w[i]);
            if (min > d.min()) {
              x[i].domain.inMin(store.level, x[i], (int) Math.min(Integer.MAX_VALUE, min));
            }
          }
        } else if (d.getSize() <= 4096) {
          for (ValueEnumeration en = d.valueEnumeration(); en.hasMoreElements(); ) {
            int v = en.nextElement();
            if (cost(i, v) >= slack) {
              x[i].domain.inComplement(store.level, x[i], v);
            }
          }
        }
      }
    }

    @Override
    public int getDefaultConsistencyPruningEvent() {
      return IntDomain.ANY;
    }

    @Override
    public String toString() {
      return id() + " : ReducedCost(" + x.length + " variables, best " + best + ")";
    }
  }
}
