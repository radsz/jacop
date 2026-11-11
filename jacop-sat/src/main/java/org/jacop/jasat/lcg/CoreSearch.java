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
import java.util.Arrays;
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
    int[] group; // for a group: the soft literals it is the conjunction of; else null
    int[]
        value; // for -[x = v] of an expanded term: the term, x, v and the indicator's c; else null

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
  // the lower bound's rate, per unit of the solver's work (CdclSolver#work, never the clock, so a
  // run repeats), is measured once this much work was done (about two seconds), and may grow this
  // many times
  private static final long RATE_WINDOW = 2_000 * LcgSolver.WORK_PER_MS;
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
  // the proof of the cores, or null without a proof
  private CoreProof proof;

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

  /**
   * Statistics: times the phase gave its time to branch and bound because it had no solution of its
   * own after a third of its time.
   */
  public long noSolutionStops;

  /** Statistics: groups of soft literals relaxed at once as at most one of them false. */
  public long amoGroups;

  /** Statistics: objective terms expanded into the values of a variable. */
  public long expandedTerms;

  /** Statistics: what those groups added to the lower bound. */
  public long amoBound;

  /** The objective's lower bound proved by the cores. */
  public long lowerBound;

  /** Statistics: linear programs over the cores solved ({@code jacop.lcg.coreLp}). */
  public long lpSolves;

  /** Statistics: times the bound of the linear program over the cores was above the lower bound. */
  public long lpRaised;

  /** The best bound of the linear program over the cores, or {@link Long#MIN_VALUE}. */
  public long lpBound = Long.MIN_VALUE;

  /**
   * The largest bound of the linear program over the cores before rounding, and the best solution's
   * objective then ({@link Long#MAX_VALUE} without one): a bound above the optimum is right only
   * when that solution is optimal.
   */
  public double lpValue = Double.NEGATIVE_INFINITY;

  /** See {@link #lpValue}. */
  public long lpIncumbent = Long.MAX_VALUE;

  /** Whether the phase proved its best solution optimal, or that there is none. */
  public boolean proved;

  // the cores as rows of a linear program with the model's rows, after each run (off by default)
  static final boolean CORE_LP = Boolean.getBoolean("jacop.lcg.coreLp");
  boolean lp = CORE_LP; // whether the cores go to a linear program (set by LcgSolver)
  // the most pivots of that linear program
  private static final int LP_PIVOTS = Integer.getInteger("jacop.lcg.coreLpPivots", 20_000);
  private final List<int[]> coreLits = new ArrayList<>(); // the cores, as soft literals
  private int lpCores; // the cores when the last linear program was solved
  private final long constant; // the objective's constant

  // the solver's work when the first call of the solver started (-1 before), and the bound then
  private long startWork = -1;
  private long startBound;
  private long runBound; // the lower bound when the last run started
  private long runEnd; // the solver's work when the last run stopped
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
    this.constant = constant;
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
    List<CoreProof.Definition> definitions = new ArrayList<>();
    for (int round = 0; round < 4 && terms.size() == 1; round++) {
      Map.Entry<Integer, Long> only = terms.entrySet().iterator().next();
      Constraint c = definition(lcg.variable(only.getKey()), only.getValue(), used);
      if (c == null) {
        break;
      }
      if (!substitute(lcg, terms, only.getKey(), only.getValue(), c, constant, definitions)) {
        return null;
      }
    }
    if (terms.containsKey(objective) || terms.isEmpty()) {
      return null;
    }
    Map<Integer, Long> blocks = new HashMap<>(terms);
    long blocksConstant = constant[0];
    List<CoreProof.Definition> blockDefinitions = new ArrayList<>(definitions);
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
        Constraint c = definition(y, 0, used);
        if (c != null) {
          if (!substitute(lcg, terms, t, weight, c, constant, definitions)) {
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
      CoreSearch search = new CoreSearch(lcg, objective, blocks, blocksConstant);
      return search.startProof(blockDefinitions) ? search : null;
    }
    CoreSearch search = new CoreSearch(lcg, objective, terms, constant[0]);
    if (!search.startProof(definitions)) {
      return null;
    }
    if (!terms.equals(blocks)) {
      // grouped now, as before #313's rework: the probes then have the time of the whole run, not
      // the share of the phase (spot5 28: 58 groups and a proof in 7 s, against 6 groups)
      search.addTermSofts();
      search.group();
    }
    return search;
  }

  /**
   * Starts the proof of the cores when the solver writes one: the line of the objective's lower
   * bound, from the definitions. Returns false when the model does not state them, so the phase
   * cannot be proved.
   */
  private boolean startProof(List<CoreProof.Definition> definitions) {
    if (!lcg.proving()) {
      return true;
    }
    proof = CoreProof.of(lcg, definitions);
    return proof != null;
  }

  /**
   * Relaxes the at-most-one groups ({@link #relaxAtMostOnes}), except under a proof, which does not
   * define the groups' literals; returns false when the solver is unsatisfiable at the root.
   */
  private boolean group() {
    if (proof != null) {
      grouped = true;
      return true;
    }
    return relaxAtMostOnes();
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
      LcgSolver lcg,
      Map<Integer, Long> terms,
      int y,
      long weight,
      Constraint c,
      long[] constant,
      List<CoreProof.Definition> definitions) {
    LinearForm f = LinearForms.of(c);
    IntVar yv = lcg.variable(y);
    long a = 0;
    for (int k = 0; k < f.vars().length; k++) {
      if (f.vars()[k] == yv) {
        a = f.weights()[k];
      }
    }
    terms.remove(y);
    long scale = weight * a; // a is its own inverse
    definitions.add(new CoreProof.Definition(c, f, scale));
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
  private static Constraint definition(IntVar x, long weight, Set<Constraint> used) {
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
          return c;
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
    return foundConstraint;
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
    if (startWork >= 0) {
      // the rate of the lower bound counts only the phase's own work, not branch and bound between
      startWork += sat.work() - runEnd;
    }
    int result = search(phaseLimit, callLimit);
    if (result == CdclSolver.UNKNOWN && lp && proof == null && coreLits.size() > lpCores) {
      result = lpBound();
    }
    runEnd = sat.work();
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
      if (!grouped && !group()) {
        return lcg.bestObjective() == Long.MAX_VALUE ? CdclSolver.UNSAT : CdclSolver.SAT;
      }
      threshold = maxWeightBelow(Long.MAX_VALUE);
      start(sat.work());
    }
    while (true) {
      if (!relaxTrueAtRoot()) {
        return lcg.bestObjective() == Long.MAX_VALUE ? CdclSolver.UNSAT : CdclSolver.SAT;
      }
      if (lcg.boundObjective() <= lowerBound) {
        // also when the best solution was found elsewhere (a portfolio): none here is better
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
      sat.setConflictLimit(
          Math.min(lcg.conflictCap(), Math.min(phaseLimit, cap < 0 ? Long.MAX_VALUE : cap)));
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
      lcg.reportBound(lowerBound);
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
    long best = lcg.boundObjective();
    if (best == Long.MAX_VALUE) {
      return true;
    }
    long gap = best - lowerBound;
    long line = -1; // the proof's line of the gap, written before the first literal hardened
    try {
      for (Soft s : softs) {
        if (!s.hard && s.weight > gap) {
          s.hard = true;
          hardened++;
          if (proof != null && line < 0) {
            line = proof.gap();
          }
          if (!lcg.addProvedClause(-s.lit)) {
            return false;
          }
        }
      }
    } finally {
      if (line > 0) {
        proof.delete(line);
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
    long start = sat.work();
    long end = lcg.workEnd();
    long budget =
        end == Long.MAX_VALUE
            ? PROBE_WORK
            : Math.min(PROBE_WORK, Math.max(0, end - start) / PROBE_SHARE);
    for (int i = 0; i < n && sat.work() - start < budget; i++) {
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
            if (lp) {
              value.value = valueOf(s.term, lits.get(k));
            }
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
      group.group = Arrays.copyOfRange(all, 1, all.length);
      for (int j = 0; j < group.group.length; j++) {
        group.group[j] = -group.group[j];
      }
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
  // the work of the probes that look for at-most-one groups (about two seconds), and the share of
  // the work left that they may take at most
  private static final long PROBE_WORK = 2_000 * LcgSolver.WORK_PER_MS;
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
   * Whether the lower bound rises too slowly to meet the best solution before the end of the run,
   * at three times its rate since the first call of the solver, once the phase has done about two
   * seconds of work (see {@link LcgSolver#WORK_PER_MS}); for example when each core of two terms
   * with large domains raises it by 1. Branch and bound then gets the time. The rate is taken since
   * the start, not over the last seconds, so that a few slow cores near the optimum do not end the
   * phase. Once a share {@link #STALL} of the run's work after the phase's start is done, the same
   * test is also made at the rate over the second half of the phase's work: a bound that rose fast
   * at first, often from a far initial bound, and then stalls does not keep the phase to the end.
   */
  private boolean tooSlow() {
    // only once the phase has a solution of its own: a poor one from branch and bound before it
    // would stop the phase before its strata find better ones
    boolean ready =
        sat.work() - startWork >= RATE_WINDOW
            && stratumSolutions > 0
            && lcg.bestObjective() != Long.MAX_VALUE;
    if (STALL > 0) {
      sample(sat.work());
    }
    if (!ready) {
      return false;
    }
    if (!rising()) {
      return true;
    }
    if (STALL > 0 && stalled(sat.work(), lcg.workEnd(), lcg.boundObjective())) {
      stallStops++;
      return true;
    }
    return false;
  }

  /** Statistics: the phases ended because the bound stalled over their second half. */
  public long stallStops;

  // the share of the run's work after the phase's start before the bound's rate over the second
  // half of the phase is tested, 0 never; 0.1: work-task-variation 2025 seed-8 proves its optimum
  // after a stall of 20 s that a test from the start would end, community-detection 2026 and
  // javarouting trip_7_2 stall for good after 12 s and 330 s
  static final double STALL = Double.parseDouble(System.getProperty("jacop.lcg.coreStall", "0.1"));

  // the solver's work and the lower bound at each test of the phase's rate, and the last sample at
  // or before the half of the phase's work (whose point only moves forward)
  private long[] sampleWork = new long[16];
  private long[] sampleBound = new long[16];
  private int samples;
  private int half;

  /** Starts the phase's rates at the given work of the solver and the lower bound now. */
  void start(long work) {
    startWork = work;
    startBound = lowerBound;
  }

  /** Records the given work of the solver and the lower bound now for {@link #stalled}. */
  void sample(long work) {
    if (samples == sampleWork.length) {
      sampleWork = Arrays.copyOf(sampleWork, 2 * samples);
      sampleBound = Arrays.copyOf(sampleBound, 2 * samples);
    }
    sampleWork[samples] = work;
    sampleBound[samples] = lowerBound;
    samples++;
  }

  /**
   * Whether the lower bound, at three times its rate over the second half of the phase's work,
   * would not meet the best solution before the end of the run; false before a share {@link #STALL}
   * of the run's work after the phase's start is done, and without an end of the run. The calls
   * come with work that never decreases.
   *
   * @param now the solver's work now
   * @param end the solver's work at the end of the run, Long.MAX_VALUE without one
   * @param best the objective of the best solution
   * @return whether the bound stalled
   */
  boolean stalled(long now, long end, long best) {
    if (end == Long.MAX_VALUE || now - startWork < STALL * (end - startWork)) {
      return false;
    }
    long from = now - (now - startWork) / 2;
    while (half + 1 < samples && sampleWork[half + 1] <= from) {
      half++;
    }
    long w = startWork;
    long b = startBound;
    if (samples > 0 && sampleWork[half] <= from) {
      w = sampleWork[half];
      b = sampleBound[half];
    }
    double rate = (double) (lowerBound - b) / Math.max(1, now - w);
    return RATE_SLACK * rate * (end - now) < best - lowerBound;
  }

  /**
   * Whether the lower bound, at its rate per unit of work since the first call of the solver, would
   * meet the best solution before the given end of the run.
   *
   * @param end the solver's work ({@link CdclSolver#work}) at the end of the run
   * @return false when there is no solution yet
   */
  boolean closing(long end) {
    long best = lcg.boundObjective();
    if (best == Long.MAX_VALUE || startWork < 0 || end == Long.MAX_VALUE) {
      return false;
    }
    long now = sat.work();
    double rate = (double) (lowerBound - startBound) / Math.max(1, now - startWork);
    return rate * (end - now) >= best - lowerBound;
  }

  // the solver's work and the lower bound at the last mark (see #mark), -1 before
  private long markWork = -1;
  private long markBound;

  /** Marks the solver's work and the lower bound now, from which {@link #canReach} measures. */
  void mark() {
    markWork = sat.work();
    markBound = lowerBound;
  }

  /**
   * Whether the lower bound could reach the given value within the given work, at {@link
   * #RATE_SLACK} times its rate per unit of work since the last {@link #mark}. True when it is
   * already there and when nothing was marked.
   *
   * @param target the value of the objective
   * @param work the solver's work the phase may still do
   * @return whether the phase may reach the value
   */
  boolean canReach(long target, long work) {
    if (lowerBound >= target || markWork < 0) {
      return true;
    }
    double rate = (double) (lowerBound - markBound) / Math.max(1, sat.work() - markWork);
    return RATE_SLACK * rate * work >= target - lowerBound;
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
   * Whether the lower bound, at three times its rate per unit of work since the first call of the
   * solver, would meet the best solution before the end of the run ({@link LcgSolver#workEnd}).
   * False when there is no solution yet. Without an end the work left is taken as the work the
   * phase has done: cores that cost no conflicts never reach its budget of conflicts, and one per
   * level of a term of a million values would run for hours.
   */
  private boolean rising() {
    long best = lcg.boundObjective();
    if (best == Long.MAX_VALUE) {
      return false;
    }
    long end = lcg.workEnd();
    long now = sat.work();
    double rate = (double) (lowerBound - startBound) / Math.max(1, now - startWork);
    long left = end != Long.MAX_VALUE ? end - now : now - startWork;
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
      sat.setConflictLimit(Math.min(lcg.conflictCap(), Math.min(phaseLimit, cap)));
      probes++;
      if (lcg.solveUnder(-lit) != CdclSolver.UNSAT || sat.failedAssumptions().length != 1) {
        return;
      }
      lcg.addProvedClause(lit);
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
    if (lp) {
      coreLits.add(lits.clone());
    }
    // one of the core's literals holds in every solution; the solver's cores are in the proof
    if (!(bound ? sat.addClause(lits) : lcg.addProvedClause(lits))) {
      return false;
    }
    if (lits.length > 1) {
      Totalizer tot = new Totalizer(lits, min);
      addTotalizerSoft(tot, 2);
      if (proof != null) {
        proof.core(tot.outputs, min);
      }
    }
    return !bound || boundObjective();
  }

  /** The key of a soft literal's column in {@link #lpBound}. */
  private record SoftColumn(int lit) {}

  /** The key of the column {@code [x = v]} in {@link #lpBound}. */
  private record ValueColumn(int variable, int value) {}

  /** The key of the objective's column in {@link #lpBound}. */
  private static final Object OBJECTIVE_COLUMN = new Object();

  /** The term, the variable x, the value v of the literal -[x = v], and the indicator's value. */
  private int[] valueOf(int t, int lit) {
    ValueIndicator indicator = indicatorOf(lcg.variable(termVar[t]));
    int x = lcg.index(indicator.variable());
    for (var e = lcg.rootDomain(x).valueEnumeration(); e.hasMoreElements(); ) {
      int v = e.nextElement();
      if (lcg.eqLiteral(x, v) == -lit) {
        return new int[] {t, x, v, indicator.value()};
      }
    }
    throw new IllegalStateException(lit + " is not a value literal of term " + t);
  }

  /**
   * Bounds the objective with a linear program over the rows of the model's relaxation and the
   * phase's cores ({@code jacop.lcg.coreLp}). The soft literals are 0/1 columns linked to the
   * variables they stand for: the levels of a term by the order encoding of its variable, the
   * outputs of a totalizer by rows that make each the count of its inputs, a group by the rows of a
   * conjunction, and a value literal by the columns {@code [x = u]} of its variable. Each core is
   * the row that one of its literals holds, and the reformulated objective of the cores (as in
   * Morgado et al., "Core-guided MaxSAT with soft cardinality constraints", CP 2014) is the row
   * {@code objective - sum of the soft literals' weights >= lower bound}. A rise of the bound
   * becomes the clause that the objective is at least it. Not under a proof, whose steps the linear
   * program does not give.
   *
   * @return {@link CdclSolver#UNKNOWN}, or as {@link #run} when the bound leaves no solution better
   *     than the best one
   */
  private int lpBound() {
    lpCores = coreLits.size();
    LinearRelaxation relaxation = lcg.relaxation();
    if (relaxation == null) {
      return CdclSolver.UNKNOWN;
    }
    IntVar objectiveVar = lcg.variable(objective);
    CoreLp lp = new CoreLp();
    int obj = lp.column(OBJECTIVE_COLUMN, objectiveVar.min(), objectiveVar.max());
    // the model's rows
    LinearRelaxation.Rows rows = relaxation.rowsNow();
    int[] col = new int[rows.columns().length];
    for (int j = 0; j < col.length; j++) {
      col[j] = lp.column(rows.columns()[j], rows.lower()[j], rows.upper()[j]);
    }
    for (int i = 0; i < rows.rowColumns().length; i++) {
      int[] cs = rows.rowColumns()[i];
      double[] ws = new double[cs.length];
      int[] js = new int[cs.length];
      for (int k = 0; k < cs.length; k++) {
        js[k] = col[cs[k]];
        ws[k] = rows.rowWeights()[i][k];
      }
      long lo = rows.rowLo()[i];
      long hi = rows.rowHi()[i];
      lp.row(
          js,
          ws,
          lo == Long.MIN_VALUE ? Double.NEGATIVE_INFINITY : lo,
          hi == Long.MAX_VALUE ? Double.POSITIVE_INFINITY : hi);
    }
    // the objective's definition: objective = constant + sum of weight * term
    int n = termVar.length;
    int[] terms = new int[n + 1];
    double[] weights = new double[n + 1];
    terms[0] = obj;
    weights[0] = 1;
    for (int t = 0; t < n; t++) {
      IntVar x = lcg.variable(termVar[t]);
      terms[t + 1] = lp.column(x, x.min(), x.max());
      weights[t + 1] = termUp[t] ? -termWeight[t] : termWeight[t];
    }
    lp.row(terms, weights, constant, constant);
    boolean root = sat.decisionLevel() == 0;
    Map<Totalizer, Map<Integer, Integer>> outputs = new HashMap<>();
    for (Soft s : softs) {
      int v = root ? sat.value(s.lit) : 0;
      lp.column(new SoftColumn(s.lit), v > 0 ? 1 : 0, v < 0 ? 0 : 1);
      if (s.totalizer != null) {
        outputs.computeIfAbsent(s.totalizer, k -> new HashMap<>()).put(s.count, s.lit);
      }
    }
    termRows(lp);
    Set<Integer> valued = new HashSet<>();
    for (Soft s : softs) {
      if (s.totalizer != null) {
        totalizerRows(lp, s, outputs.get(s.totalizer).get(s.count + 1));
      } else if (s.group != null) {
        groupRows(lp, s);
      } else if (s.value != null) {
        valueRows(lp, s, valued.add(s.value[1]));
      }
    }
    for (int[] core : coreLits) {
      int[] js = new int[core.length];
      double[] ones = new double[core.length];
      for (int k = 0; k < core.length; k++) {
        js[k] = softColumn(lp, core[k]);
        ones[k] = 1;
      }
      lp.row(js, ones, 1, Double.POSITIVE_INFINITY);
    }
    List<Integer> js = new ArrayList<>();
    List<Double> ws = new ArrayList<>();
    js.add(obj);
    ws.add(1.0);
    for (Soft s : softs) {
      if (s.weight > 0) {
        js.add(softColumn(lp, s.lit));
        ws.add((double) -s.weight);
      }
    }
    lp.row(
        js.stream().mapToInt(Integer::intValue).toArray(),
        ws.stream().mapToDouble(Double::doubleValue).toArray(),
        lowerBound,
        Double.POSITIVE_INFINITY);
    lpSolves++;
    double z = lp.minimize(obj, LP_PIVOTS);
    if (!(z > Long.MIN_VALUE && z < Long.MAX_VALUE)) {
      return CdclSolver.UNKNOWN;
    }
    if (z > lpValue) {
      lpValue = z;
      lpIncumbent = lcg.boundObjective();
    }
    long bound = (long) Math.ceil(z);
    if (bound <= Math.max(lowerBound, objectiveVar.min())) {
      return CdclSolver.UNKNOWN;
    }
    lpRaised++;
    lpBound = Math.max(lpBound, bound);
    if (bound > objectiveVar.max() || !sat.addClause(lcg.geLiteral(objective, (int) bound))) {
      // no solution better than the best one, if there is one
      return lcg.bestObjective() == Long.MAX_VALUE ? CdclSolver.UNSAT : CdclSolver.SAT;
    }
    lcg.reportBound(bound);
    return lcg.boundObjective() <= bound ? CdclSolver.SAT : CdclSolver.UNKNOWN;
  }

  private static int softColumn(CoreLp lp, int lit) {
    return lp.column(new SoftColumn(lit), 0, 1);
  }

  /**
   * The order encoding of each term's variable over its soft levels: with y the distance of the
   * variable from its bound and s_1, s_2, ... the literals [y >= l_1], [y >= l_2], ..., {@code y >=
   * sum (l_i - l_{i-1}) s_i}, {@code y <= l_1 - 1 + sum (l_{i+1} - l_i) s_i} and {@code s_i >=
   * s_{i+1}}; a level proved holds.
   */
  private void termRows(CoreLp lp) {
    Map<Integer, List<Soft>> byTerm = new HashMap<>();
    for (Soft s : softs) {
      if (s.term >= 0) {
        byTerm.computeIfAbsent(s.term, k -> new ArrayList<>()).add(s);
      }
    }
    for (Map.Entry<Integer, List<Soft>> e : byTerm.entrySet()) {
      int t = e.getKey();
      List<Soft> levels = e.getValue();
      levels.sort((a, b) -> Integer.compare(a.level, b.level));
      IntVar x = lcg.variable(termVar[t]);
      int xc = lp.column(x, x.min(), x.max());
      // y = sign * x + shift
      double sign = termUp[t] ? 1 : -1;
      double shift = termUp[t] ? -termBase[t] : termBase[t];
      int k = levels.size();
      int[] js = new int[k + 1];
      double[] up = new double[k + 1];
      double[] down = new double[k + 1];
      js[0] = xc;
      up[0] = sign;
      down[0] = sign;
      int previous = 0;
      for (int i = 0; i < k; i++) {
        Soft s = levels.get(i);
        js[i + 1] = softColumn(lp, s.lit);
        up[i + 1] = -(s.level - previous);
        previous = s.level;
        int next = i + 1 < k ? levels.get(i + 1).level : termSpan[t] + 1;
        down[i + 1] = -(next - s.level);
        if (s.level <= termProven[t]) {
          lp.column(new SoftColumn(s.lit), 1, 1);
        }
        if (i + 1 < k) {
          lp.row(
              new int[] {js[i + 1], softColumn(lp, levels.get(i + 1).lit)},
              new double[] {1, -1},
              0,
              Double.POSITIVE_INFINITY);
        }
      }
      lp.row(js, up, -shift, Double.POSITIVE_INFINITY);
      lp.row(js, down, Double.NEGATIVE_INFINITY, levels.get(0).level - 1 - shift);
    }
  }

  /** Output j of a totalizer over n inputs is their count's {@code [>= j]}. */
  private void totalizerRows(CoreLp lp, Soft s, Integer next) {
    int[] in = s.totalizer.inputs;
    int n = in.length;
    int j = s.count;
    int[] js = new int[n + 1];
    double[] at = new double[n + 1];
    double[] over = new double[n + 1];
    js[0] = softColumn(lp, s.lit);
    at[0] = j;
    over[0] = n - j + 1;
    for (int k = 0; k < n; k++) {
      js[k + 1] = softColumn(lp, in[k]);
      at[k + 1] = -1;
      over[k + 1] = -1;
    }
    lp.row(js, at, Double.NEGATIVE_INFINITY, 0); // j o_j <= count
    lp.row(js, over, 1 - j, Double.POSITIVE_INFINITY); // count >= j makes o_j true
    if (next != null) {
      lp.row(
          new int[] {js[0], softColumn(lp, next)},
          new double[] {1, -1},
          0,
          Double.POSITIVE_INFINITY);
    }
  }

  /** A group is the conjunction of its members, and at most one of them is false. */
  private void groupRows(CoreLp lp, Soft s) {
    int[] members = s.group;
    int k = members.length;
    int z = softColumn(lp, s.lit);
    int[] js = new int[k + 1];
    double[] and = new double[k + 1];
    int[] ms = new int[k];
    double[] ones = new double[k];
    js[0] = z;
    and[0] = 1;
    for (int i = 0; i < k; i++) {
      int m = softColumn(lp, members[i]);
      lp.row(new int[] {z, m}, new double[] {1, -1}, Double.NEGATIVE_INFINITY, 0);
      js[i + 1] = m;
      and[i + 1] = -1;
      ms[i] = m;
      ones[i] = 1;
    }
    lp.row(js, and, -(k - 1), Double.POSITIVE_INFINITY);
    lp.row(ms, ones, k - 1, Double.POSITIVE_INFINITY);
  }

  /**
   * The literal -[x = v] of an expanded term b = [x = c]: the columns [x = u] of the values of x
   * sum to 1 and to x when weighted by u, the literal is {@code 1 - [x = v]} and b is {@code [x =
   * c]}.
   */
  private void valueRows(CoreLp lp, Soft s, boolean first) {
    int t = s.value[0];
    int xi = s.value[1];
    IntVar x = lcg.variable(xi);
    int xc = lp.column(x, x.min(), x.max());
    if (first) {
      // the first value literal of x: its value columns
      IntDomain dom = lcg.rootDomain(xi);
      int size = dom.getSize();
      int[] js = new int[size];
      double[] ones = new double[size];
      int[] withX = new int[size + 1];
      double[] values = new double[size + 1];
      int k = 0;
      for (var e = dom.valueEnumeration(); e.hasMoreElements(); k++) {
        int u = e.nextElement();
        js[k] = lp.column(new ValueColumn(xi, u), 0, x.dom().contains(u) ? 1 : 0);
        ones[k] = 1;
        withX[k] = js[k];
        values[k] = -u;
      }
      withX[size] = xc;
      values[size] = 1;
      lp.row(js, ones, 1, 1);
      lp.row(withX, values, 0, 0);
    }
    int e = lp.column(new ValueColumn(xi, s.value[2]), 0, 1);
    lp.row(new int[] {softColumn(lp, s.lit), e}, new double[] {1, 1}, 1, 1);
    IntVar b = lcg.variable(termVar[t]);
    int bc = lp.column(b, b.min(), b.max());
    int ec = lp.column(new ValueColumn(xi, s.value[3]), 0, 1);
    lp.row(new int[] {bc, ec}, new double[] {1, -1}, 0, 0);
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
    return lcg.addProvedClause(lcg.geLiteral(objective, (int) lowerBound));
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
    if (proof != null) {
      proof.fold(termVar[t], termUp[t], termBase[t], level, to, weight);
    }
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
      // all outputs under a proof, whose definitions an encoding with more outputs would repeat
      int limit = proof != null ? tot.inputs.length : Math.max(4, 2 * count);
      tot.outputs = encode(tot.inputs, Math.min(tot.inputs.length, limit));
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
    if (proof != null) {
      proof.define(out, inputs, from, to);
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
        if (proof != null) {
          // a child of one input is a leaf, not an output with definitions
          proof.totalizerClause(
              i > 0 && mid - from > 1 ? a[i - 1] : 0,
              j > 0 && to - mid > 1 ? b[j - 1] : 0,
              clause[k]);
        }
        sat.addClause(clause);
      }
    }
    return out;
  }
}
