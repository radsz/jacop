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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.lcg.LinearForm;

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
  // the lower bound's rate is measured over this many nanoseconds, and may grow this many times
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

  /** Statistics: solutions found under the assumptions. */
  public long stratumSolutions;

  /** The objective's lower bound proved by the cores. */
  public long lowerBound;

  /** Whether the phase proved its best solution optimal, or that there is none. */
  public boolean proved;

  private long checkTime; // when the rate of the lower bound was last measured, and the bound then
  private long checkBound;
  private long startTime; // when the rate was first measured
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
    long constant = 0;
    Set<Constraint> used = new HashSet<>();
    for (int round = 0; round < 4 && terms.size() == 1; round++) {
      Map.Entry<Integer, Long> only = terms.entrySet().iterator().next();
      LinearForm f = definition(lcg.variable(only.getKey()), used);
      if (f == null) {
        break;
      }
      // a * y + sum of w_j * z_j = c, so y = (c - sum of w_j * z_j) / a with a = 1 or -1
      long a = 0;
      for (int k = 0; k < f.vars().length; k++) {
        if (f.vars()[k] == lcg.variable(only.getKey())) {
          a = f.weights()[k];
        }
      }
      long scale = only.getValue() * a; // a is its own inverse
      Map<Integer, Long> next = new HashMap<>();
      for (int k = 0; k < f.vars().length; k++) {
        IntVar z = f.vars()[k];
        if (z == lcg.variable(only.getKey())) {
          continue;
        }
        long w = -scale * f.weights()[k];
        if (z.singleton()) {
          constant += w * z.value();
          continue;
        }
        int j = lcg.index(z);
        if (j < 0) {
          return null;
        }
        next.merge(j, w, Long::sum);
      }
      constant += scale * f.c();
      next.values().removeIf(w -> w == 0);
      terms = next;
    }
    if (terms.containsKey(objective) || terms.isEmpty()) {
      return null;
    }
    return new CoreSearch(lcg, objective, terms, constant);
  }

  /** A linear equality on x with coefficient 1 or -1 that is not used yet, or null. */
  private static LinearForm definition(IntVar x, Set<Constraint> used) {
    IntDomain dom = x.dom();
    if (dom.modelConstraints == null) {
      return null;
    }
    LinearForm found = null;
    for (int e = 0; e < dom.modelConstraints.length && found == null; e++) {
      Constraint[] list = dom.modelConstraints[e];
      for (int k = 0; list != null && k < dom.modelConstraintsToEvaluate[e]; k++) {
        Constraint c = list[k];
        if (used.contains(c)) {
          continue;
        }
        LinearForm f = LinearForms.of(c);
        if (f == null || f.relation() != LinearForm.EQ) {
          continue;
        }
        int occurrences = 0;
        long a = 0;
        for (int j = 0; j < f.vars().length; j++) {
          if (f.vars()[j] == x) {
            occurrences++;
            a = f.weights()[j];
          }
        }
        if (occurrences == 1 && Math.abs(a) == 1) {
          used.add(c);
          found = f;
          break;
        }
      }
    }
    return found;
  }

  /**
   * Continues the search until it proves the best solution optimal, proves there is none, or a
   * limit stops it. Each run picks up where the last one stopped.
   *
   * @param phaseLimit the solver's conflict count at which the run stops
   * @param callLimit the conflicts one call of the solver may take before the run stops
   * @return {@link CdclSolver#SAT} when the best solution is optimal, {@link CdclSolver#UNSAT} when
   *     there is no solution, {@link CdclSolver#UNKNOWN} otherwise
   */
  int run(long phaseLimit, long callLimit) {
    int result = search(phaseLimit, callLimit);
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
      for (int t = 0; t < termVar.length; t++) {
        addTermSoft(t, 1, termWeight[t]);
      }
      threshold = maxWeightBelow(Long.MAX_VALUE);
    }
    while (true) {
      if (!relaxTrueAtRoot()) {
        return lcg.bestObjective() == Long.MAX_VALUE ? CdclSolver.UNSAT : CdclSolver.SAT;
      }
      if (lcg.bestObjective() <= lowerBound) {
        return CdclSolver.SAT;
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
        return result;
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
        threshold = below;
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
   * Whether the lower bound rises too slowly to meet the best solution before the deadline, at
   * three times its rate of the last two seconds; for example when each core of two terms with
   * large domains raises it by 1. Branch and bound then gets the time. Without a deadline the time
   * left is taken as the time the phase has run: cores that cost no conflicts never reach its
   * budget of conflicts, and one per level of a term of a million values would run for hours.
   */
  private boolean tooSlow() {
    long now = System.nanoTime();
    if (checkTime == 0) {
      checkTime = now;
      startTime = now;
      checkBound = lowerBound;
      return false;
    }
    if (now - checkTime < RATE_WINDOW) {
      return false;
    }
    long deadline = sat.deadline();
    long best = lcg.bestObjective();
    double rate = (double) (lowerBound - checkBound) / (now - checkTime);
    checkTime = now;
    checkBound = lowerBound;
    long left = deadline != Long.MAX_VALUE ? deadline - now : now - startTime;
    return best != Long.MAX_VALUE && RATE_SLACK * rate * left < best - lowerBound;
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

  private void addTermSoft(int t, int level, long weight) {
    if (level > termSpan[t]) {
      return; // the variable cannot move further
    }
    int lit = termLiteral(t, level);
    addSoft(new Soft(lit, weight, t, level, null, 0));
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
