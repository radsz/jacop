/*
 * CoreSearch.java
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

package org.jacop.jasat.lcg;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.lp.LinearRelaxation;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.ValueIndicator;

/**
 * Core-guided search for an objective that is a linear sum: the OLL algorithm (Andres et al. 2012,
 * Morgado et al. 2014) over the order literals of the terms, as Gange, Berg, Demirović and Stuckey
 * (CPAIOR 2020) apply it to lazy clause generation.
 *
 * <p>Each term {@code w * x} with {@code w > 0} costs {@code w} for every value of {@code x} above
 * its lower bound, so it is a sum of soft literals {@code [x >= lb + k]}, each of weight {@code w}
 * ({@code [x <= ub - k]} for a negative weight). The search assumes the soft literals false. An
 * unsatisfiable core of these assumptions raises the lower bound by its smallest weight {@code m},
 * takes {@code m} from the weight of each of its literals, and adds a totalizer over them whose
 * outputs {@code [at least j of them]} for {@code j >= 2} become soft literals of weight {@code m}.
 * The next literal of a term, or output of a totalizer, becomes soft when the one before it is in a
 * core. A solution under all the assumptions is optimal; with weight stratification, assumptions of
 * the heavier literals come first, and a solution under them is the best so far.
 *
 * <p>The lower bound goes to the objective variable as a clause after each core, so the branch and
 * bound that follows keeps it.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class CoreSearch {

  /** A soft literal: true costs its weight. */
  private static final class Soft {
    final int lit;
    long weight;
    final int term; // for a term's literal: the term and how far above its bound; else -1
    final int level;
    final Totalizer totalizer; // for a totalizer output: the totalizer and the count; else null
    final int count;
    boolean expanded; // its successor is soft already
    boolean hard; // true in every solution better than the best one

    Soft(int lit, long weight, int term, int level, Totalizer totalizer, int count) {
      this.lit = lit;
      this.weight = weight;
      this.term = term;
      this.level = level;
      this.totalizer = totalizer;
      this.count = count;
    }
  }

  /**
   * Outputs {@code [at least j of the inputs]} for j up to a limit, true when the count reaches j.
   */
  private static final class Totalizer {
    final int[] inputs;
    final long weight;
    int[] outputs = new int[0];

    Totalizer(int[] inputs, long weight) {
      this.inputs = inputs;
      this.weight = weight;
    }
  }

  // the conflicts of one probe of a term's level
  private static final long PROBE_CONFLICTS = 100;
  // the lower bound's rate is measured once this many nanoseconds passed, and may grow this many
  // times
  private static final long RATE_WINDOW = 2_000_000_000L;
  private static final double RATE_SLACK = 3;

  private final LcgSolver lcg;
  private final CdclSolver sat;
  private final int[] termVar;
  private final long[] termWeight; // positive
  private final boolean[] termUp; // the cost grows with the variable
  private final int[] termBase; // the bound the cost is counted from
  private final int[] termSpan; // how far the variable can move from it
  private final int[] termProven; // the levels that the variable is proved to move at least
  private final long offset; // the objective at the bounds
  private final int objective;
  private final List<Soft> softs = new ArrayList<>();
  private final Map<Integer, Soft> byLiteral = new HashMap<>();

  /** Statistics: cores found. */
  public long cores;

  /** Statistics: cores of one literal that was true at the root, found without the solver. */
  public long rootCores;

  /** Statistics: calls of the solver that probe how far a term must move. */
  public long probes;

  /** Statistics: literals in the cores found. */
  public long coreLiterals;

  /** Statistics: soft literals made hard because violating one costs more than the gap. */
  public long hardened;

  /** Statistics: solutions found under the assumptions. */
  public long stratumSolutions;

  /** Statistics: groups of soft literals relaxed at once as at most one of them false. */
  public long amoGroups;

  /** Statistics: objective terms expanded into the values of a variable. */
  public long expandedTerms;

  /** Statistics: what those groups added to the lower bound. */
  public long amoBound;

  /** The objective's lower bound proved by the cores. */
  public long lowerBound;

  /** Whether the phase proved its best solution optimal, or that there is none. */
  public boolean proved;

  private long startTime; // when the first call of the solver started, and the bound then
  private long startBound;
  private long runBound; // the lower bound when the last run started
  private long runEnd; // when the last run stopped
  private boolean grouped; // the at-most-one groups were looked for
  private long threshold = -1; // soft literals of at least this weight are assumed
  private boolean exhausted; // all soft literals were assumed and a solution still cost more

  private CoreSearch(LcgSolver lcg, int objective, Map<Integer, Long> terms, long constant) {
    this.lcg = lcg;
    this.sat = lcg.solver();
    this.objective = objective;
    int n = terms.size();
    termVar = new int[n];
    termWeight = new long[n];
    termUp = new boolean[n];
    termBase = new int[n];
    termSpan = new int[n];
    termProven = new int[n];
    long sum = constant;
    int t = 0;
    for (Map.Entry<Integer, Long> e : terms.entrySet()) {
      IntVar x = lcg.variable(e.getKey());
      long w = e.getValue();
      termVar[t] = e.getKey();
      termWeight[t] = Math.abs(w);
      termUp[t] = w > 0;
      termBase[t] = w > 0 ? x.min() : x.max();
      termSpan[t] = x.max() - x.min();
      sum += w * termBase[t];
      t++;
    }
    offset = sum;
    lowerBound = sum;
  }

  /**
   * Reads the objective as a linear sum from a linear equality on it with coefficient 1 or -1,
   * following single-term definitions such as the negation of a maximised variable.
   *
   * @return the search, or null when the objective is not such a sum of the solver's variables
   */
  static CoreSearch of(LcgSolver lcg, IntVar x) {
    int objective = lcg.index(x);
    if (objective < 0) {
      return null;
    }
    // objective = constant + sum of weight * variable, over the solver's variable indices
    Map<Integer, Long> terms = new HashMap<>();
    terms.put(objective, 1L);
    Set<Constraint> used = new HashSet<>();
    long[] constant = new long[1];
    for (int round = 0; round < 4 && terms.size() == 1; round++) {
      Map.Entry<Integer, Long> only = terms.entrySet().iterator().next();
      LinearForm f = definition(lcg.variable(only.getKey()), only.getValue(), used);
      if (f == null) {
        break;
      }
      if (!substitute(lcg, terms, only.getKey(), only.getValue(), f, constant)) {
        return null;
      }
    }
    if (terms.containsKey(objective) || terms.isEmpty()) {
      return null;
    }
    Map<Integer, Long> blocks = new HashMap<>(terms);
    long blocksConstant = constant[0];
    // a term that is only a sum defined for the objective, such as a block of a long sum split for
    // shorter explanations, is replaced by its own terms
    for (int round = 0; round < 4; round++) {
      boolean changed = false;
      for (int t : new ArrayList<>(terms.keySet())) {
        IntVar y = lcg.variable(t);
        Long weight = terms.get(t);
        if (t == objective || weight == null || otherConstraints(y, used) != 1) {
          continue;
        }
        LinearForm f = definition(y, 0, used);
        if (f != null) {
          if (!substitute(lcg, terms, t, weight, f, constant)) {
            return null;
          }
          changed = true;
        }
      }
      if (!changed) {
        break;
      }
    }
    // the terms of the sums replace the sums when they have fewer levels for the cores to relax:
    // 0-1 terms (trucking, celar, spot5), not wide ones whose span is that of the sums (atsp: 405
    // terms, 151 cores on its 3 sums against 2,285 on the terms)
    if (span(lcg, terms) > span(lcg, blocks)) {
      return new CoreSearch(lcg, objective, blocks, blocksConstant);
    }
    CoreSearch search = new CoreSearch(lcg, objective, terms, constant[0]);
    if (!terms.equals(blocks)) {
      // grouped now, as before #313's rework: the probes then have the time of the whole run, not
      // the share of the phase (spot5 28: 58 groups and a proof in 7 s, against 6 groups)
      search.addTermSofts();
      search.relaxAtMostOnes();
    }
    return search;
  }

  /** The number of levels of the terms' variables, summed. */
  private static long span(LcgSolver lcg, Map<Integer, Long> terms) {
    long span = 0;
    for (int t : terms.keySet()) {
      IntVar x = lcg.variable(t);
      span += (long) x.max() - x.min();
    }
    return span;
  }

  /**
   * Replaces term y of the sum by its definition f, {@code a * y + sum of w_j * z_j = c} with a = 1
   * or -1, so {@code y = (c - sum of w_j * z_j) / a}, where y has the given weight in the sum.
   * Returns false when a z_j is not a variable of the solver.
   */
  private static boolean substitute(
      LcgSolver lcg, Map<Integer, Long> terms, int y, long weight, LinearForm f, long[] constant) {
    IntVar yv = lcg.variable(y);
    long a = 0;
    for (int k = 0; k < f.vars().length; k++) {
      if (f.vars()[k] == yv) {
        a = f.weights()[k];
      }
    }
    terms.remove(y);
    long scale = weight * a; // a is its own inverse
    for (int k = 0; k < f.vars().length; k++) {
      IntVar z = f.vars()[k];
      if (z == yv) {
        continue;
      }
      long w = -scale * f.weights()[k];
      if (z.singleton()) {
        constant[0] += w * z.value();
        continue;
      }
      int j = lcg.index(z);
      if (j < 0) {
        return false;
      }
      terms.merge(j, w, Long::sum);
    }
    constant[0] += scale * f.c();
    terms.values().removeIf(w -> w == 0);
    return true;
  }

  /**
   * The number of constraints on x that are not used yet, apart from the linear relaxation, which
   * only relaxes the others.
   */
  private static int otherConstraints(IntVar x, Set<Constraint> used) {
    IntDomain dom = x.dom();
    if (dom.modelConstraints == null) {
      return 0;
    }
    Set<Constraint> on = new HashSet<>();
    for (int e = 0; e < dom.modelConstraints.length; e++) {
      Constraint[] list = dom.modelConstraints[e];
      for (int k = 0; list != null && k < dom.modelConstraintsToEvaluate[e]; k++) {
        if (!used.contains(list[k]) && !(list[k] instanceof LinearRelaxation)) {
          on.add(list[k]);
        }
      }
    }
    return on.size();
  }

  /**
   * A linear equality on x with coefficient 1 or -1 that is not used yet, or null. With a nonzero
   * weight of x in the minimised sum, the equality whose terms bound weight * x highest at the
   * root: presolve adds the objective as a sum of cost variables, shifted by the model's
   * exactly-one sets, next to its definition when lcg-split has split the definition into blocks
   * (jp-encoding data1000: a root bound of 30,874 on the cost variables, 0 on the 0-1 terms of the
   * blocks).
   */
  private static LinearForm definition(IntVar x, long weight, Set<Constraint> used) {
    IntDomain dom = x.dom();
    if (dom.modelConstraints == null) {
      return null;
    }
    LinearForm found = null;
    Constraint foundConstraint = null;
    long foundBound = Long.MIN_VALUE;
    for (int e = 0; e < dom.modelConstraints.length; e++) {
      Constraint[] list = dom.modelConstraints[e];
      for (int k = 0; list != null && k < dom.modelConstraintsToEvaluate[e]; k++) {
        Constraint c = list[k];
        if (used.contains(c) || c == foundConstraint) {
          continue;
        }
        LinearForm f = LinearForms.of(c);
        if (f == null || f.relation() != LinearForm.EQ) {
          continue;
        }
        long a = coefficient(f, x);
        if (Math.abs(a) != 1) {
          continue;
        }
        if (weight == 0) {
          used.add(c);
          return f;
        }
        long bound = rootBound(x, weight * a, f);
        if (found == null || bound > foundBound) {
          found = f;
          foundConstraint = c;
          foundBound = bound;
        }
      }
    }
    if (foundConstraint != null) {
      used.add(foundConstraint);
    }
    return found;
  }

  /** The coefficient of x in f, or 0 when x occurs other than once. */
  private static long coefficient(LinearForm f, IntVar x) {
    int occurrences = 0;
    long a = 0;
    for (int j = 0; j < f.vars().length; j++) {
      if (f.vars()[j] == x) {
        occurrences++;
        a = f.weights()[j];
      }
    }
    return occurrences == 1 ? a : 0;
  }

  /**
   * The root lower bound of {@code scale * a * x} through {@code a * x + sum of w_j * z_j = c},
   * that is of {@code scale * (c - sum of w_j * z_j)}.
   */
  private static long rootBound(IntVar x, long scale, LinearForm f) {
    long bound = scale * f.c();
    for (int j = 0; j < f.vars().length; j++) {
      IntVar z = f.vars()[j];
      if (z != x) {
        long w = -scale * f.weights()[j];
        bound += w > 0 ? w * z.min() : w * z.max();
      }
    }
    return bound;
  }

  /** The number of terms of the objective's sum. */
  int termCount() {
    return termVar.length;
  }

  /**
   * Continues the search until it proves the best solution optimal, proves there is none, or a
   * limit stops it. Each run picks up where the last one stopped.
   *
   * @param phaseLimit the solver's conflict count at which the run stops
   * @param callLimit the conflicts one call of the solver may take before the run stops, doubled
   *     each time a call runs out of them while the lower bound still rises fast enough
   * @return {@link CdclSolver#SAT} when the best solution is optimal, {@link CdclSolver#UNSAT} when
   *     there is no solution, {@link CdclSolver#UNKNOWN} otherwise
   */
  int run(long phaseLimit, long callLimit) {
    runBound = lowerBound;
    if (startTime != 0) {
      // the rate of the lower bound counts only the phase's own time, not branch and bound between
      startTime += System.nanoTime() - runEnd;
    }
    int result = search(phaseLimit, callLimit);
    runEnd = System.nanoTime();
    if (result != CdclSolver.UNKNOWN) {
      proved = true;
    }
    return result;
  }

  private int search(long phaseLimit, long callLimit) {
    if (exhausted) {
      return CdclSolver.UNKNOWN;
    }
    if (threshold < 0) {
      if (!grouped) {
        addTermSofts();
      }
      if (!grouped && !relaxAtMostOnes()) {
        return lcg.bestObjective() == Long.MAX_VALUE ? CdclSolver.UNSAT : CdclSolver.SAT;
      }
      threshold = maxWeightBelow(Long.MAX_VALUE);
      startTime = System.nanoTime();
      startBound = lowerBound;
    }
    while (true) {
      if (!relaxTrueAtRoot()) {
        return lcg.bestObjective() == Long.MAX_VALUE ? CdclSolver.UNSAT : CdclSolver.SAT;
      }
      if (lcg.bestObjective() <= lowerBound) {
        return CdclSolver.SAT;
      }
      if (!harden()) {
        return CdclSolver.SAT; // no solution better than the best one
      }
      List<Integer> assumed = new ArrayList<>();
      for (Soft s : softs) {
        if (s.weight >= threshold && s.weight > 0) {
          assumed.add(-s.lit);
        }
      }
      long cap = sat.conflicts + callLimit;
      sat.setConflictLimit(Math.min(phaseLimit, cap < 0 ? Long.MAX_VALUE : cap));
      int result = lcg.solveUnder(assumed.stream().mapToInt(Integer::intValue).toArray());
      if (result == CdclSolver.UNKNOWN) {
        if (sat.conflicts < cap || cap >= phaseLimit || !rising()) {
          return result;
        }
        // the call ran out of its own conflicts while the bound rose fast enough so far: the
        // clauses it learnt stay, and the next call of the same assumptions may take twice as many
        callLimit = 2 * callLimit;
        continue;
      }
      if (result == CdclSolver.SAT) {
        stratumSolutions++;
        if (lcg.bestObjective() <= lcg.variable(objective).min()) {
          return CdclSolver.SAT; // the solution is at the objective's smallest value
        }
        long below = maxWeightBelow(threshold);
        if (below == 0) {
          // every soft literal false: the solution costs the lower bound
          exhausted = true;
          return lcg.bestObjective() <= lowerBound ? CdclSolver.SAT : CdclSolver.UNKNOWN;
        }
        // the next stratum takes the weights down to half of this one: a stratum per distinct
        // weight costs a solution each, about 100 ms on jp-encoding data1000, whose weights near
        // 1,000 differ by 1 to 10
        long half = maxWeightBelow(threshold / 2 + 1);
        threshold = half > 0 ? half : below;
        continue;
      }
      int[] core = sat.failedAssumptions();
      if (core.length == 0 || !relax(core, true)) {
        // no solution better than the best one, if there is one
        return lcg.bestObjective() == Long.MAX_VALUE ? CdclSolver.UNSAT : CdclSolver.SAT;
      }
      Soft unit = core.length == 1 ? byLiteral.get(-core[0]) : null;
      if (unit != null && unit.term >= 0) {
        probe(unit.term, unit.level, phaseLimit);
      }
      if (tooSlow()) {
        return CdclSolver.UNKNOWN;
      }
    }
  }

  /**
   * Makes hard each soft literal whose weight exceeds the gap between the best solution and the
   * lower bound: any assignment that violates it costs at least the lower bound plus its weight, so
   * no better solution violates it (hardening, as in RC2 and Geas). Returns false when the solver
   * becomes unsatisfiable.
   */
  private boolean harden() {
    long best = lcg.bestObjective();
    if (best == Long.MAX_VALUE) {
      return true;
    }
    long gap = best - lowerBound;
    for (Soft s : softs) {
      if (!s.hard && s.weight > gap) {
        s.hard = true;
        hardened++;
        if (!sat.addClause(-s.lit)) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * Relaxes the groups of soft literals of which at most one can be false, before any core: the
   * cores of two such literals each raise the bound by one weight, and a group of k needs k - 1 of
   * them, with a totalizer each. Probing each literal false at the root shows the soft literals it
   * makes true; a greedy cover of that graph by cliques, the heaviest literals first, gives the
   * groups. A group of k literals of smallest weight m raises the lower bound by (k - 1) m, takes m
   * from each, and adds a soft literal of weight m that is true when all k are (the at-most-one
   * relaxation of Ignatiev, Morgado and Marques-Silva 2019; CP-SAT's am1 presolve of the
   * objective).
   *
   * <p>A term {@code w * b} with {@code b <=> x = c} can also be seen through the values of x: b is
   * 0 exactly when x takes one of its k other values, so {@code w * b} is {@code w} times the
   * number of those values that x does not take, less {@code (k - 1) w}. The literals {@code [x !=
   * v]} are then soft, each of weight w, and the groups can mix values of different variables, for
   * example observations that cannot share an instrument. Both covers are computed, and the one
   * with the larger bound is kept. Returns false when the solver is unsatisfiable at the root.
   */
  private void addTermSofts() {
    for (int t = 0; t < termVar.length; t++) {
      addTermSoft(t, 1, termWeight[t]);
    }
  }

  private boolean relaxAtMostOnes() {
    grouped = true;
    // the nodes: soft literals of terms, then the value literals of the terms that expand
    List<Integer> lits = new ArrayList<>();
    List<Long> weights = new ArrayList<>();
    List<Soft> owner = new ArrayList<>(); // the term's soft literal of each node
    for (Soft s : softs) {
      if (s.term >= 0 && s.weight > 0 && sat.value(s.lit) == 0) {
        lits.add(s.lit);
        weights.add(s.weight);
        owner.add(s);
      }
    }
    int terms = lits.size();
    long expansionCost = 0; // what the expansion takes from the bound
    BitSet expanded = new BitSet();
    for (int i = 0; i < terms; i++) {
      int[] values = valueLiterals(owner.get(i));
      if (values.length == 0) {
        continue;
      }
      expanded.set(i);
      expansionCost += (values.length - 1) * weights.get(i);
      for (int v : values) {
        lits.add(-v);
        weights.add(weights.get(i));
        owner.add(owner.get(i));
      }
    }
    int n = lits.size();
    if (n > MAX_GROUP_NODES) {
      return true;
    }
    Map<Integer, Integer> position = new HashMap<>();
    for (int i = 0; i < n; i++) {
      position.put(lits.get(i), i);
    }
    BitSet[] adjacent = new BitSet[n];
    for (int i = 0; i < n; i++) {
      adjacent[i] = new BitSet();
    }
    BitSet free = new BitSet(n);
    long start = System.nanoTime();
    long deadline = sat.deadline();
    long budget =
        deadline == Long.MAX_VALUE
            ? PROBE_TIME
            : Math.min(PROBE_TIME, Math.max(0, deadline - start) / PROBE_SHARE);
    for (int i = 0; i < n && System.nanoTime() - start < budget; i++) {
      int lit = lits.get(i);
      if (sat.value(lit) != 0) {
        continue;
      }
      int[] implied = lcg.probe(-lit);
      if (implied == null) {
        // the literal is true in every solution
        if (!sat.addClause(lit)) {
          return false;
        }
        continue;
      }
      free.set(i);
      for (int l : implied) {
        Integer k = position.get(l);
        if (k != null && k != i) {
          adjacent[i].set(k);
          adjacent[k].set(i);
        }
      }
    }
    // the literals of each cover: terms only, or the values in place of the terms that expand
    BitSet plain = new BitSet(n);
    plain.set(0, terms);
    plain.and(free);
    BitSet byValues = (BitSet) free.clone();
    byValues.andNot(expanded);
    if (expanded.isEmpty()) {
      byValues = null;
    }
    List<List<Integer>> plainCover = cover(plain, adjacent, weights);
    List<List<Integer>> valueCover = byValues == null ? null : cover(byValues, adjacent, weights);
    List<List<Integer>> chosen = plainCover;
    if (valueCover != null
        && gain(valueCover, weights) - expansionCost > gain(plainCover, weights)) {
      chosen = valueCover;
      for (int i = expanded.nextSetBit(0); i >= 0; i = expanded.nextSetBit(i + 1)) {
        Soft s = owner.get(i);
        for (int k = terms; k < n; k++) {
          if (owner.get(k) == s) {
            Soft value = new Soft(lits.get(k), s.weight, -1, 0, null, 0);
            value.expanded = true; // nothing follows it
            addSoft(value);
          }
        }
        s.weight = 0;
        s.expanded = true;
        expandedTerms++;
      }
      lowerBound -= expansionCost;
    }
    for (List<Integer> clique : chosen) {
      long m = Long.MAX_VALUE;
      for (int k : clique) {
        m = Math.min(m, byLiteral.get(lits.get(k)).weight);
      }
      int[] all = new int[clique.size() + 1];
      int z = lcg.newAuxiliary();
      all[0] = z;
      for (int j = 0; j < clique.size(); j++) {
        Soft s = byLiteral.get(lits.get(clique.get(j)));
        s.weight -= m;
        if (!s.expanded) {
          // as in a core: the term's next level costs its weight once this one is relaxed, or
          // every soft literal could be false in a solution above the lower bound
          s.expanded = true;
          addTermSoft(s.term, s.level + 1, termWeight[s.term]);
        }
        all[j + 1] = -s.lit;
        if (!sat.addClause(-z, s.lit)) {
          return false;
        }
      }
      if (!sat.addClause(all)) {
        return false;
      }
      Soft group = new Soft(z, m, -1, 0, null, 0);
      group.expanded = true; // nothing follows it
      addSoft(group);
      lowerBound += m * (clique.size() - 1);
      amoGroups++;
      amoBound += m * (clique.size() - 1);
    }
    return boundObjective();
  }

  /**
   * A greedy cover of the given nodes by cliques of two or more, the heaviest nodes first. A clique
   * takes its smallest weight from each of its nodes, and a node whose weight is not used up can be
   * in further cliques, as a literal can be in several cores.
   */
  private static List<List<Integer>> cover(BitSet nodes, BitSet[] adjacent, List<Long> weights) {
    long[] left = new long[weights.size()];
    BitSet open = new BitSet();
    for (int i = nodes.nextSetBit(0); i >= 0; i = nodes.nextSetBit(i + 1)) {
      left[i] = weights.get(i);
      open.set(i);
    }
    List<List<Integer>> cliques = new ArrayList<>();
    boolean found = true;
    while (found) {
      found = false;
      List<Integer> order = new ArrayList<>();
      for (int i = open.nextSetBit(0); i >= 0; i = open.nextSetBit(i + 1)) {
        order.add(i);
      }
      order.sort((a, b) -> Long.compare(left[b], left[a]));
      for (int i : order) {
        if (left[i] == 0) {
          continue;
        }
        List<Integer> clique = new ArrayList<>();
        clique.add(i);
        BitSet candidates = (BitSet) adjacent[i].clone();
        candidates.and(open);
        while (!candidates.isEmpty()) {
          int best = -1;
          for (int k = candidates.nextSetBit(0); k >= 0; k = candidates.nextSetBit(k + 1)) {
            if (best < 0 || left[k] > left[best]) {
              best = k;
            }
          }
          clique.add(best);
          candidates.and(adjacent[best]);
        }
        if (clique.size() < 2) {
          open.clear(i); // no neighbour has weight left
          continue;
        }
        long m = Long.MAX_VALUE;
        for (int k : clique) {
          m = Math.min(m, left[k]);
        }
        for (int k : clique) {
          left[k] -= m;
          if (left[k] == 0) {
            open.clear(k);
          }
        }
        cliques.add(clique);
        found = true;
      }
    }
    return cliques;
  }

  /** What a cover adds to the lower bound. */
  private static long gain(List<List<Integer>> cover, List<Long> weights) {
    long[] left = new long[weights.size()];
    for (int i = 0; i < left.length; i++) {
      left[i] = weights.get(i);
    }
    long sum = 0;
    for (List<Integer> clique : cover) {
      long m = Long.MAX_VALUE;
      for (int k : clique) {
        m = Math.min(m, left[k]);
      }
      for (int k : clique) {
        left[k] -= m;
      }
      sum += m * (clique.size() - 1);
    }
    return sum;
  }

  // the most soft literals probed for at-most-one groups, the most time the probes may take, and
  // at most this part of the time left
  private static final int MAX_GROUP_NODES = 20_000;
  private static final long PROBE_TIME = 2_000_000_000L;
  private static final long PROBE_SHARE = 10;

  private static final int[] NO_VALUES = new int[0];

  /** The most values of a variable whose objective term is seen through its values. */
  private static final int MAX_EXPANDED_VALUES = 64;

  /**
   * The literals {@code [x = v]} for the values v of x other than c, when s is the soft literal
   * {@code [b >= 1]} of a term {@code w * b} with {@code w > 0} and {@code b <=> x = c}, and x has
   * three to {@link #MAX_EXPANDED_VALUES} values; else none.
   */
  private int[] valueLiterals(Soft s) {
    if (s.level != 1 || !termUp[s.term] || termSpan[s.term] != 1) {
      return NO_VALUES;
    }
    IntVar b = lcg.variable(termVar[s.term]);
    ValueIndicator indicator = indicatorOf(b);
    if (indicator == null || b.min() != 0) {
      return NO_VALUES;
    }
    int x = lcg.index(indicator.variable());
    if (x < 0) {
      return NO_VALUES;
    }
    IntDomain dom = lcg.rootDomain(x);
    int c = indicator.value();
    if (dom.getSize() > MAX_EXPANDED_VALUES || !dom.contains(c) || dom.getSize() < 3) {
      return NO_VALUES;
    }
    int[] values = new int[dom.getSize() - 1];
    int k = 0;
    for (var e = dom.valueEnumeration(); e.hasMoreElements(); ) {
      int v = e.nextElement();
      if (v != c) {
        values[k++] = lcg.eqLiteral(x, v);
      }
    }
    return values;
  }

  /** The constraint {@code b <=> x = c} on b, or null. */
  private static ValueIndicator indicatorOf(IntVar b) {
    IntDomain dom = b.dom();
    if (dom.modelConstraints == null) {
      return null;
    }
    for (int e = 0; e < dom.modelConstraints.length; e++) {
      Constraint[] list = dom.modelConstraints[e];
      for (int k = 0; list != null && k < dom.modelConstraintsToEvaluate[e]; k++) {
        if (list[k] instanceof ValueIndicator v && v.indicator() == b) {
          return v;
        }
      }
    }
    return null;
  }

  /**
   * Whether the lower bound rises too slowly to meet the best solution before the deadline, at
   * three times its rate since the first call of the solver, once that is two seconds ago; for
   * example when each core of two terms with large domains raises it by 1. Branch and bound then
   * gets the time. The rate is taken since the start, not over the last seconds, so that a few slow
   * cores near the optimum do not end the phase.
   */
  private boolean tooSlow() {
    // only once the phase has a solution of its own: a poor one from branch and bound before it
    // would stop the phase before its strata find better ones
    return System.nanoTime() - startTime >= RATE_WINDOW
        && stratumSolutions > 0
        && lcg.bestObjective() != Long.MAX_VALUE
        && !rising();
  }

  /**
   * Whether the lower bound, at its rate since the first call of the solver, would meet the best
   * solution before the given deadline.
   *
   * @param deadline a time of {@link System#nanoTime()}
   * @return false when there is no solution yet
   */
  boolean closing(long deadline) {
    long best = lcg.bestObjective();
    if (best == Long.MAX_VALUE || startTime == 0) {
      return false;
    }
    long now = System.nanoTime();
    double rate = (double) (lowerBound - startBound) / Math.max(1, now - startTime);
    return rate * (deadline - now) >= best - lowerBound;
  }

  /** Whether the lower bound rose in the last run. */
  boolean rose() {
    return lowerBound > runBound;
  }

  /**
   * Whether the lower bound rose in the last run at least as much as it still has to rise to meet
   * the best solution. False when there is no solution yet.
   */
  boolean halfWay() {
    long best = lcg.bestObjective();
    return best != Long.MAX_VALUE && lowerBound - runBound >= best - lowerBound;
  }

  /**
   * Whether the lower bound, at three times its rate since the first call of the solver, would meet
   * the best solution before the deadline. False when there is no solution yet. Without a deadline
   * the time left is taken as the time the phase has run: cores that cost no conflicts never reach
   * its budget of conflicts, and one per level of a term of a million values would run for hours.
   */
  private boolean rising() {
    long best = lcg.bestObjective();
    if (best == Long.MAX_VALUE) {
      return false;
    }
    long deadline = sat.deadline();
    long now = System.nanoTime();
    double rate = (double) (lowerBound - startBound) / Math.max(1, now - startTime);
    long left = deadline != Long.MAX_VALUE ? deadline - now : now - startTime;
    return RATE_SLACK * rate * left >= best - lowerBound;
  }

  /**
   * Relaxes, without calling the solver, every soft literal that is true at the root: each is a
   * core of its own. A term whose lower bound rose at the root then costs its levels below the
   * bound at once, instead of a call of the solver for each. Returns false when the solver is
   * unsatisfiable at the root.
   */
  private boolean relaxTrueAtRoot() {
    for (int k = 0; k < softs.size(); k++) {
      Soft s = softs.get(k);
      if (s.weight > 0 && trueAtRoot(s)) {
        rootCores++;
        if (s.term >= 0 && !s.expanded) {
          // the levels up to the variable's root bound cost their full weight at once
          int reached = Math.max(rootLevel(s.term), s.level);
          s.expanded = true;
          lowerBound += termWeight[s.term] * (long) (reached - s.level);
          addTermSoft(s.term, reached + 1, termWeight[s.term]);
        }
        if (!relax(new int[] {-s.lit}, false)) {
          return false;
        }
      }
    }
    return boundObjective();
  }

  private boolean trueAtRoot(Soft s) {
    if (sat.value(s.lit) > 0) {
      return true;
    }
    if (s.term < 0) {
      return false;
    }
    return s.level <= rootLevel(s.term);
  }

  /** The level that term t's variable has reached at the root, or is proved to reach. */
  private int rootLevel(int t) {
    IntVar x = lcg.variable(termVar[t]);
    return Math.max(termProven[t], termUp[t] ? x.min() - termBase[t] : termBase[t] - x.max());
  }

  /**
   * After a core of one literal of a term, proves how far the term's variable must move: levels at
   * doubling distances above it, each assumed alone with a few conflicts, until one is not refuted.
   * A term whose bound rises far at the root then needs a few calls of the solver instead of one
   * per level; the levels proved are relaxed as true at the root.
   */
  private void probe(int t, int from, long phaseLimit) {
    for (int step = 1; from + step <= termSpan[t]; step *= 2) {
      int level = from + step;
      int lit = termLiteral(t, level);
      long cap = sat.conflicts + PROBE_CONFLICTS;
      sat.setConflictLimit(Math.min(phaseLimit, cap));
      probes++;
      if (lcg.solveUnder(-lit) != CdclSolver.UNSAT || sat.failedAssumptions().length != 1) {
        return;
      }
      sat.addClause(lit);
      termProven[t] = level;
    }
  }

  /** Whether every soft literal was assumed and a solution was found under all of them. */
  boolean exhausted() {
    return exhausted;
  }

  /** The largest positive weight of a soft literal below the given one, or 0. */
  private long maxWeightBelow(long limit) {
    long max = 0;
    for (Soft s : softs) {
      if (s.weight < limit && s.weight > max) {
        max = s.weight;
      }
    }
    return max;
  }

  /** Relaxes a core of assumptions; returns false when the solver is unsatisfiable at the root. */
  private boolean relax(int[] core, boolean bound) {
    cores++;
    coreLiterals += core.length;
    long min = Long.MAX_VALUE;
    List<Soft> in = new ArrayList<>();
    for (int a : core) {
      Soft s = byLiteral.get(-a);
      in.add(s);
      min = Math.min(min, s.weight);
    }
    lowerBound += min;
    int[] lits = new int[in.size()];
    for (int k = 0; k < in.size(); k++) {
      Soft s = in.get(k);
      lits[k] = s.lit;
      s.weight -= min;
      if (!s.expanded) {
        s.expanded = true;
        if (s.term >= 0) {
          addTermSoft(s.term, s.level + 1, termWeight[s.term]);
        } else {
          addTotalizerSoft(s.totalizer, s.count + 1);
        }
      }
    }
    // one of the core's literals holds in every solution
    if (!sat.addClause(lits)) {
      return false;
    }
    if (lits.length > 1) {
      addTotalizerSoft(new Totalizer(lits, min), 2);
    }
    return !bound || boundObjective();
  }

  /** Adds the clause that the objective is at least the lower bound. */
  private boolean boundObjective() {
    IntVar x = lcg.variable(objective);
    if (lowerBound <= x.min()) {
      return true;
    }
    if (lowerBound > x.max()) {
      return false;
    }
    return sat.addClause(lcg.geLiteral(objective, (int) lowerBound));
  }

  /**
   * Adds the soft literal of term t at the given level, or at the next level its variable can take
   * at the root: the levels in a hole of the domain are the same literal, so one soft literal
   * stands for all of them and weighs as much (jp-encoding: cost variables of two values, 0 and
   * about 1,000, each needed a core per level).
   */
  private void addTermSoft(int t, int level, long weight) {
    if (level > termSpan[t]) {
      return; // the variable cannot move further
    }
    int to = nextLevel(t, level);
    int lit = termLiteral(t, to);
    addSoft(new Soft(lit, weight * (to - level + 1), t, to, null, 0));
  }

  /** The smallest level from the given one that term t's variable can take at the root. */
  private int nextLevel(int t, int level) {
    IntDomain dom = lcg.rootDomain(termVar[t]);
    int v = termUp[t] ? termBase[t] + level : termBase[t] - level;
    if (dom.contains(v)) {
      return level;
    }
    int next = termUp[t] ? dom.nextValue(v) : dom.previousValue(v);
    return termUp[t] ? next - termBase[t] : termBase[t] - next;
  }

  /** The literal that term t's variable is at least the given level above its bound. */
  private int termLiteral(int t, int level) {
    return termUp[t]
        ? lcg.geLiteral(termVar[t], termBase[t] + level)
        : -lcg.geLiteral(termVar[t], termBase[t] - level + 1);
  }

  private void addTotalizerSoft(Totalizer tot, int count) {
    if (count > tot.inputs.length) {
      return;
    }
    if (count > tot.outputs.length) {
      tot.outputs = encode(tot.inputs, Math.min(tot.inputs.length, Math.max(4, 2 * count)));
    }
    addSoft(new Soft(tot.outputs[count - 1], tot.weight, -1, 0, tot, count));
  }

  private void addSoft(Soft s) {
    Soft old = byLiteral.get(s.lit);
    if (old != null) {
      old.weight += s.weight; // the same literal from two sources
      return;
    }
    softs.add(s);
    byLiteral.put(s.lit, s);
  }

  /**
   * Encodes a totalizer (Bailleux and Boufkhad 2003) over the inputs with outputs up to a limit,
   * with only the clauses that make an output true when enough inputs are.
   */
  private int[] encode(int[] inputs, int limit) {
    return encode(inputs, 0, inputs.length, limit);
  }

  private int[] encode(int[] inputs, int from, int to, int limit) {
    if (to - from == 1) {
      return new int[] {inputs[from]};
    }
    int mid = (from + to) >>> 1;
    int[] a = encode(inputs, from, mid, limit);
    int[] b = encode(inputs, mid, to, limit);
    int n = Math.min(limit, a.length + b.length);
    int[] out = new int[n];
    for (int k = 0; k < n; k++) {
      out[k] = lcg.newAuxiliary();
    }
    for (int i = 0; i <= a.length; i++) {
      for (int j = 0; j <= b.length && i + j <= n; j++) {
        if (i + j == 0) {
          continue;
        }
        int[] clause = new int[(i > 0 ? 1 : 0) + (j > 0 ? 1 : 0) + 1];
        int k = 0;
        if (i > 0) {
          clause[k++] = -a[i - 1];
        }
        if (j > 0) {
          clause[k++] = -b[j - 1];
        }
        clause[k] = out[i + j - 1];
        sat.addClause(clause);
      }
    }
    return out;
  }
}
