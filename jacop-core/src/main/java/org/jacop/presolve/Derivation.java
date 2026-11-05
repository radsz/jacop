/*
 * Derivation.java
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
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.core.AffineDomain;
import org.jacop.core.AffineView;
import org.jacop.core.Domain;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.StoreState;
import org.jacop.core.Var;

/**
 * Derives a child store from a parent store at the parent's current level, and returns the child's
 * solutions to the parent. The child is a new store with fresh variables and copies of the parent's
 * constraints, simplified by the presolve rules; every solution of the child, written back by
 * {@link #returnSolution()}, is a solution of the parent's problem at that level.
 *
 * <p>Two choices fix what the parent can do afterwards. With {@link Retention#KEPT} the parent
 * keeps its constraints: it is {@link StoreState#SUSPENDED} while the child lives, and each
 * returned solution is propagated in the parent, which checks it against the whole model. With
 * {@link Retention#RELEASED} the parent's constraints are detached, so they can be garbage
 * collected, and the parent becomes a {@link StoreState#SINK} that only receives values.
 *
 * <p>If the parent is inconsistent at its level there is no child ({@link Outcome#INFEASIBLE}). If
 * one of its constraints or variables cannot be copied there is no child either ({@link
 * Outcome#LIVE}): {@link #child()} is then the parent itself, the map is the identity and returning
 * a solution does nothing, so callers need no special case.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class Derivation implements VarMap {

  /** The most rounds of presolve rules by default. */
  public static final int DEFAULT_ROUNDS = 10;

  /**
   * The share of the variables a round must change for the next round to go back to the fast rules
   * by default; a round that changes less moves on to the next timing class, and at the last class
   * it ends the rounds. SCIP's presolving/abortfac is 0.0008.
   */
  public static final double DEFAULT_ABORT_FACTOR = 0.001;

  /** What happens to the parent's constraints. */
  public enum Retention {
    /** The parent keeps its constraints and checks every returned solution. */
    KEPT,
    /** The parent's constraints are detached once the child exists. */
    RELEASED
  }

  /** The result of deriving. */
  public enum Outcome {
    /** A child store was derived. */
    DERIVED,
    /** The parent is inconsistent at its level, so there is no child. */
    INFEASIBLE,
    /** A constraint or variable cannot be copied, so the parent itself is searched. */
    LIVE
  }

  /**
   * Sizes of the parent and the child.
   *
   * @param parentVariables variables of the parent store.
   * @param parentConstraints constraints attached in the parent at the level of the derivation.
   * @param childVariables variables of the child store.
   * @param childConstraints constraints copied into the child.
   * @param fixed parent variables fixed at the level of the derivation and absent from the child.
   * @param dropped constraints not copied because the presolve rules found them entailed or a rule
   *     removed them.
   * @param simplified constraints rewritten by {@link GlobalPresolve} for the domains at the level
   *     of the derivation; those rewritten to nothing are counted here too.
   * @param aliased parent variables merged with another variable by an equation; they share its
   *     copy, and the equation is counted in {@code dropped}.
   */
  public record Statistics(
      int parentVariables,
      int parentConstraints,
      int childVariables,
      int childConstraints,
      int fixed,
      int dropped,
      int simplified,
      int aliased) {}

  /**
   * What the dual reductions did.
   *
   * @param rounds rounds run.
   * @param fixed variables fixed.
   * @param tightened domains narrowed without fixing the variable.
   * @param dominated pairs of variables where one dominates the other (dominated columns).
   * @param dominanceClauses clauses imposed for those pairs.
   */
  public record DualStatistics(
      int rounds, int fixed, int tightened, int dominated, int dominanceClauses) {}

  /**
   * What the SAT preprocessing of the clauses did (rule 9).
   *
   * @param clauses clauses in the parent: clause constraints and clauses kept outside the store.
   * @param clausesAfter clauses given to the child.
   * @param fixed variables fixed because the clauses imply their value.
   * @param equivalent variables replaced by an equivalent literal.
   * @param eliminated variables eliminated by resolution, pure literals included.
   * @param subsumed clauses removed because another clause subsumes them.
   * @param strengthened literals removed from clauses by self-subsuming resolution or vivification.
   * @param blocked blocked clauses removed.
   */
  public record ClauseStatistics(
      int clauses,
      int clausesAfter,
      int fixed,
      int equivalent,
      int eliminated,
      int subsumed,
      int strengthened,
      int blocked) {}

  private final Store parent;
  private final Retention retention;
  private final Set<Var> frozen;
  private final boolean rules;
  private final List<IntVar[][]> clauses;
  private final boolean solutionPreserving;
  private final List<Rule> ruleList;
  private final int maxRounds;
  private final Rule.Timing maxTiming;
  private final double abortFactor;
  private final long budgetNanos;
  private final int[] timingRounds = new int[Rule.Timing.values().length];
  private final boolean views;
  private final boolean affine;
  private final boolean doubletons;
  private final boolean inPlace;
  private final DualReductions dual;

  private Outcome outcome;
  private int level;
  private Store child;
  private final Map<Var, Entry> entries = new IdentityHashMap<>();
  private final Map<Var, Var> copies = new IdentityHashMap<>();
  private List<Var> variables = List.of();
  private List<Constraint> collected = List.of();
  private Statistics statistics;
  private final Map<String, Integer> reductions = new LinkedHashMap<>();
  private final Map<String, Long> timings = new LinkedHashMap<>();
  private Map<Var, Integer> relaxed = Map.of();
  private DualStatistics dualStatistics;
  private boolean solutionWritten;
  private Reconstruction eliminationReconstruction;
  private int eliminated;
  private int substitutions;
  private int affineSubstituted;
  private SatPresolve.Reconstruction reconstruction;
  private ClauseStatistics clauseStatistics;
  private int rounds;
  private final Set<Constraint> removed = Collections.newSetFromMap(new IdentityHashMap<>());

  private Derivation(Builder builder) {
    this.parent = builder.parent;
    this.retention = builder.retention;
    this.frozen = builder.frozen;
    this.rules = builder.rules;
    this.clauses = builder.clauses;
    this.solutionPreserving = builder.solutionPreserving;
    this.dual =
        builder.dual
            ? new DualReductions(
                builder.objective,
                builder.minimize,
                builder.exempt == null ? Set.of() : builder.exempt,
                builder.dominatedColumns)
            : null;
    List<Rule> list = new ArrayList<>(builder.ruleList);
    if (dual != null) {
      // after the rules that keep every solution, which may expose more one-sided variables
      list.add(dual);
    }
    this.ruleList = List.copyOf(list);
    this.maxRounds = builder.maxRounds;
    this.maxTiming = builder.maxTiming;
    this.abortFactor = builder.abortFactor;
    this.budgetNanos = builder.budgetNanos;
    this.views = builder.views;
    this.affine = builder.affine;
    this.doubletons = builder.doubletons;
    this.inPlace = builder.inPlace;
  }

  /**
   * Starts a derivation from a store at its current level.
   *
   * @param parent the store, which must be {@link StoreState#ACTIVE}.
   * @return a builder.
   */
  public static Builder of(Store parent) {
    return new Builder(parent);
  }

  /** Options of a derivation. */
  public static final class Builder {

    private final Store parent;
    private Retention retention = Retention.RELEASED;
    private Set<Var> frozen;
    private boolean rules = true;
    private List<IntVar[][]> clauses;
    private boolean solutionPreserving = true;
    private boolean dual;
    private IntVar objective;
    private boolean minimize;
    private Set<Var> exempt;
    private boolean dominatedColumns = true;
    private final List<Rule> ruleList = new ArrayList<>();
    private int maxRounds = DEFAULT_ROUNDS;
    private Rule.Timing maxTiming = Rule.Timing.EXHAUSTIVE;
    private double abortFactor = DEFAULT_ABORT_FACTOR;
    private long budgetNanos = Long.MAX_VALUE;
    private boolean views = true;
    private boolean affine = true;
    private boolean doubletons = true;
    private boolean inPlace;

    private Builder(Store parent) {
      this.parent = parent;
    }

    /**
     * Sets what happens to the parent's constraints; the default is {@link Retention#RELEASED}.
     *
     * @param retention the retention.
     * @return this builder.
     */
    public Builder retention(Retention retention) {
      this.retention = retention;
      return this;
    }

    /**
     * Sets the variables that must keep a counterpart in the child even if no constraint uses them,
     * for example output variables. By default every variable that is not fixed is kept. Once the
     * kept variables are given, the others can also be eliminated with the constraint that defines
     * them (rule 8), and postsolve computes their values.
     *
     * @param vars the variables.
     * @return this builder.
     */
    public Builder keep(Var... vars) {
      if (frozen == null) {
        frozen = Collections.newSetFromMap(new IdentityHashMap<>());
      }
      Collections.addAll(frozen, vars);
      return this;
    }

    /**
     * Switches the presolve rules on or off; with them off the child is a plain copy of the parent
     * at its level. On by default.
     *
     * @param on true to apply the rules.
     * @return this builder.
     */
    public Builder rules(boolean on) {
      this.rules = on;
      return this;
    }

    /**
     * Gives the derivation clauses kept outside the parent store, for a SAT solver that takes them
     * itself, each as its positive and its negative 0/1 variables. They are preprocessed with the
     * clauses of the store; once the child is derived the list holds the clauses for the child, in
     * its variables, and the clause constraints of the store that preprocessing changed are in the
     * list instead of the child. With {@link Retention#KEPT} the original clauses are also imposed
     * on the parent, so that it checks them.
     *
     * @param clauses the clauses, a list the derivation changes in place.
     * @return this builder.
     */
    public Builder clauses(List<IntVar[][]> clauses) {
      this.clauses = clauses;
      return this;
    }

    /**
     * Sets whether the child must have every solution of the parent, projected on the frozen
     * variables ({@link #keep(Var...)}), once each. With false, rules may also apply that keep only
     * satisfiability and optima, for example half-reification, so the child can have several
     * solutions for one solution of the parent, or a solution whose non-frozen variables postsolve
     * leaves open; use true for all-solution search and counting. These rules also need the frozen
     * variables to be given. True by default.
     *
     * <p>Once frozen variables are given, the SAT preprocessing of the clauses may remove the other
     * variables that occur only in clauses, and postsolve gives them their values: with true only a
     * variable equivalent to another literal, with false also variables eliminated by resolution or
     * freed by blocked clauses.
     *
     * @param on true to keep every solution.
     * @return this builder.
     */
    public Builder solutionPreserving(boolean on) {
      this.solutionPreserving = on;
      return this;
    }

    /**
     * Adds a presolve rule; the rules run in the order added, in rounds alternated with propagation
     * of the parent until a fixpoint, see {@link Rule}.
     *
     * @param rule the rule.
     * @return this builder.
     */
    public Builder rule(Rule rule) {
      ruleList.add(rule);
      return this;
    }

    /**
     * Switches the dual reductions on or off; off by default. They narrow domains in the parent at
     * the level of the derivation so that at least one solution, and every optimum of the
     * objective, is left, but not every solution: switch them on only for a search that wants one
     * solution or an optimum. The parent's constraints must be the whole problem, apart from those
     * on {@link #exempt(Var...)} variables.
     *
     * @param on true to apply them.
     * @return this builder.
     */
    public Builder dualReductions(boolean on) {
      this.dual = on;
      return this;
    }

    /**
     * Switches the dominated columns of the dual reductions on or off; on by default. They keep an
     * optimum but may remove the improving solutions a search would find on the way to it.
     *
     * @param on true to look for dominated columns when the dual reductions are on.
     * @return this builder.
     */
    public Builder dominatedColumns(boolean on) {
      this.dominatedColumns = on;
      return this;
    }

    /**
     * Sets the objective, for the dual reductions; without one the problem is a satisfaction
     * problem and the reductions keep one of its solutions.
     *
     * @param objective the objective variable, or null.
     * @param minimize true if it is minimised, false if maximised.
     * @return this builder.
     */
    public Builder objective(IntVar objective, boolean minimize) {
      this.objective = objective;
      this.minimize = minimize;
      return this;
    }

    /**
     * Sets variables the dual reductions must leave alone, for example those of constraints that
     * are posted after the derivation or that live outside the store.
     *
     * @param vars the variables.
     * @return this builder.
     */
    public Builder exempt(Var... vars) {
      if (exempt == null) {
        exempt = Collections.newSetFromMap(new IdentityHashMap<>());
      }
      Collections.addAll(exempt, vars);
      return this;
    }

    /**
     * Sets the most rounds of rules; the default is {@value Derivation#DEFAULT_ROUNDS}. The rounds
     * stop earlier at a fixpoint, when a round of rules and propagation changes nothing.
     *
     * @param max the most rounds, at least 1.
     * @return this builder.
     */
    public Builder rounds(int max) {
      if (max < 1) {
        throw new IllegalArgumentException("At least one round is needed; " + max + " given");
      }
      this.maxRounds = max;
      return this;
    }

    /**
     * Sets the costliest timing class of rules to run; the rules of a costlier class are left out.
     * {@link Rule.Timing#EXHAUSTIVE} by default, which runs every rule.
     *
     * @param max the costliest class.
     * @return this builder.
     */
    public Builder timing(Rule.Timing max) {
      this.maxTiming = Objects.requireNonNull(max);
      return this;
    }

    /**
     * Sets the share of the variables a round must change to count as finding much; see {@link
     * #DEFAULT_ABORT_FACTOR}. With 0 every change counts, so the rounds stop only at a fixpoint.
     *
     * @param factor the share, at least 0.
     * @return this builder.
     */
    public Builder abortFactor(double factor) {
      if (!(factor >= 0)) {
        throw new IllegalArgumentException("The abort factor must be at least 0; " + factor);
      }
      this.abortFactor = factor;
      return this;
    }

    /**
     * Sets the time the rounds of rules may take, in milliseconds; no new round starts once it is
     * spent. Unlimited by default. The steps after the rounds (SAT preprocessing, substitution, the
     * copy) are not limited.
     *
     * @param millis the time, at least 0.
     * @return this builder.
     */
    public Builder budget(long millis) {
      if (millis < 0) {
        throw new IllegalArgumentException("The budget must be at least 0; " + millis);
      }
      this.budgetNanos =
          millis > Long.MAX_VALUE / 1_000_000L ? Long.MAX_VALUE : millis * 1_000_000L;
      return this;
    }

    /**
     * Sets whether a derivation whose rules only narrowed domains and imposed constraints leaves
     * the parent to be searched, with outcome {@link Outcome#LIVE}, instead of copying it. Off by
     * default. The narrowing and the imposed constraints are in the parent already, and a copy
     * costs time and changes the order of variables and constraints, which changes the search of
     * lazy clause generation and the rows of the linear relaxation.
     *
     * @param on true to skip a copy that would not simplify the problem.
     * @return this builder.
     */
    public Builder inPlace(boolean on) {
      this.inPlace = on;
      return this;
    }

    /**
     * Switches the doubleton substitutions of rule 8 on or off; on by default. A doubleton
     * substitution replaces a variable defined by a linear equality by its definition in the one
     * other linear constraint it occurs in, so the result is longer. Lazy clause generation is
     * better off without them: the explanations of a long sum are long, while the variable that
     * stands for part of a sum lets them refer to that part with one literal. The singleton columns
     * of rule 8 are eliminated either way.
     *
     * @param on true to substitute doubletons.
     * @return this builder.
     */
    public Builder doubletons(boolean on) {
      this.doubletons = on;
      return this;
    }

    /**
     * Switches rule 2, affine equality substitution, on or off; on by default when the rules are.
     *
     * @param on true to substitute.
     * @return this builder.
     */
    public Builder affine(boolean on) {
      this.affine = on;
      return this;
    }

    /**
     * Switches affine views on or off. With them on, a variable defined as a*y + b by an equality
     * becomes an {@link AffineView} of y's counterpart in the child; with them off only variables
     * equal to another one are substituted. On by default; switch them off when the child is
     * searched by a solver that does not support views, such as the LCG solver.
     *
     * @param on true to use views.
     * @return this builder.
     */
    public Builder views(boolean on) {
      this.views = on;
      return this;
    }

    /**
     * Derives the child.
     *
     * @return the derivation; see {@link Derivation#outcome()}.
     */
    public Derivation derive() {
      Derivation d = new Derivation(this);
      d.run();
      return d;
    }
  }

  private void run() {
    if (parent.state() != StoreState.ACTIVE) {
      throw new IllegalStateException(
          "Only an active store can derive a child; it is " + parent.state());
    }
    // The parent has to be at a fixpoint, so every constraint has had its first consistency call
    // at this level or below. Propagating may itself raise the level, so the level is read after.
    if (!parent.consistency()) {
      outcome = Outcome.INFEASIBLE;
      return;
    }
    level = parent.level;
    try {
      if (rules && !ruleList.isEmpty() && !applyRules()) {
        outcome = Outcome.INFEASIBLE;
        return;
      }
    } catch (FailException e) {
      outcome = Outcome.INFEASIBLE;
      return;
    } finally {
      if (dual != null) {
        dualStatistics =
            new DualStatistics(
                dual.rounds(),
                dual.fixed(),
                dual.tightened(),
                dual.dominated(),
                dual.dominanceClauses());
      }
    }
    long t = System.nanoTime();
    variables = variables(parent);
    collected = constraints(parent, variables);
    t = time("collect", t);

    if (!copyable()) {
      live();
      return;
    }

    SatPresolve sat = null;
    List<IntVar[][]> originalClauses = clauses == null ? null : new ArrayList<>(clauses);
    if (rules) {
      sat =
          new SatPresolve(
              collected.stream().filter(c -> !removed.contains(c)).toList(),
              clauses,
              frozen == null ? null : frozen::contains,
              !solutionPreserving);
      sat.run();
      if (sat.infeasible()) {
        outcome = Outcome.INFEASIBLE;
        return;
      }
      clauseStatistics = sat.statistics();
      if (!fixImplied(sat.implied())) {
        outcome = Outcome.INFEASIBLE;
        return;
      }
      if (!sat.changed()) {
        sat = null;
      }
      t = time("satPresolve", t);
    }
    Set<Constraint> absorbed = sat == null ? Set.of() : sat.absorbed();
    List<IntVar[][]> childClauses =
        sat != null ? sat.clauses() : clauses != null ? clauses : List.of();
    // the variables of the clauses, and those postsolve reads for the removed ones: the rules on
    // the carried constraints do not see them, and the child keeps them
    Set<Var> clauseVariables = Collections.newSetFromMap(new IdentityHashMap<>());
    for (IntVar[][] c : childClauses) {
      Collections.addAll(clauseVariables, c[0]);
      Collections.addAll(clauseVariables, c[1]);
    }
    if (sat != null && sat.reconstruction() != null) {
      clauseVariables.addAll(sat.reconstruction().read());
    }

    List<Constraint> carried = new ArrayList<>();
    int dropped = 0;
    for (Constraint c : collected) {
      if (absorbed.contains(c)) {
        continue;
      }
      if (rules && (removed.contains(c) || entailed(c))) {
        dropped++;
      } else {
        carried.add(c);
      }
    }
    int simplified = 0;
    for (Rule rule : ruleList) {
      if (rule instanceof GlobalPresolveRule g) {
        simplified += g.simplified();
      }
    }
    if (rules) {
      List<Constraint> rewritten = new ArrayList<>(carried.size());
      for (Constraint c : carried) {
        Optional<List<Constraint>> r = GlobalPresolve.rewrite(c);
        if (r.isPresent()) {
          rewritten.addAll(r.get());
          simplified++;
        } else {
          rewritten.add(c);
        }
      }
      carried = rewritten;
    }
    int equations = carried.size();
    Map<Var, Var> aliases = rules && Aliases.ENABLED ? Aliases.merge(carried) : Map.of();
    dropped += equations - carried.size();
    t = time("rewrite", t);

    ReificationCleanup reifications =
        new ReificationCleanup(carried, frozenWith(clauseVariables), !solutionPreserving);
    if (rules) {
      reifications.run();
      carried.removeIf(reifications::dropped);
      reductions.put("reificationsSimplified", reifications.simplified());
      reductions.put("halfReified", reifications.halfReified());
      reductions.put("reificationsDropped", reifications.dropped());
    }

    t = time("reificationCleanup", t);
    if (rules && frozen != null) {
      carried = eliminate(carried, aliases, reifications, clauseVariables);
      t = time("elimination", t);
    }

    // rule 2: the equalities that define affine classes are replaced by substitution
    AffineSubstitution affine = null;
    if (rules && this.affine) {
      // variables the child needs as themselves: those of the clauses, which go to the SAT solver,
      // and those of the constraints the reification cleanup rewrites or relaxes
      Set<Var> pinned = Collections.newSetFromMap(new IdentityHashMap<>());
      pinned.addAll(clauseVariables);
      pinned.addAll(reifications.relaxed().keySet());
      List<Constraint> plain = new ArrayList<>(carried.size());
      for (Constraint c : carried) {
        if (reifications.rewritten(c)) {
          pinned.addAll(c.arguments());
          pinned.addAll(reifications.arguments(c));
        } else {
          plain.add(c);
        }
      }
      // a merged alias is named by the constraints but takes the copy of its class
      affine = AffineSubstitution.find(plain, views, aliases::containsKey, pinned::contains);
      if (affine.definingCount() > 0) {
        carried.removeIf(affine::defines);
        dropped += affine.definingCount();
      } else {
        affine = null;
      }
    }

    t = time("affineSubstitution", t);
    Set<Var> used = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Constraint c : carried) {
      used.addAll(reifications.arguments(c));
    }
    used.addAll(clauseVariables);
    Set<Var> eliminatedVars = Collections.newSetFromMap(new IdentityHashMap<>());
    if (sat != null) {
      eliminatedVars.addAll(sat.eliminated());
      reconstruction = sat.reconstruction();
    }
    // the variable that stays for a class is kept, so every merged variable has a copy
    used.addAll(aliases.values());

    if (inPlace
        && removed.isEmpty()
        && simplified == 0
        && sat == null
        && absorbed.isEmpty()
        && aliases.isEmpty()
        && reifications.simplified() + reifications.halfReified() + reifications.dropped() == 0
        && entries.isEmpty()
        && affine == null) {
      // the rules only narrowed domains and imposed constraints, which the parent has: it is
      // searched itself, as it was loaded, rather than a copy that would search differently
      live();
      time("copy", t);
      return;
    }

    child = new Store();
    int fixed = 0;
    try {
      for (Var v : variables) {
        if (aliases.containsKey(v) || entries.containsKey(v)) {
          // merged into another variable, or eliminated by rule 8
          continue;
        }
        if (affine != null && affine.relation(v) != null) {
          // a member of an affine class, mapped once its representative has a counterpart
          continue;
        }
        if (used.contains(v) || !rules || affine != null && affine.isRoot(v)) {
          keep(v);
        } else if (eliminatedVars.contains(v) && !v.singleton()) {
          entries.put(v, new Entry.Eliminated());
        } else if (v.singleton()) {
          entries.put(v, new Entry.Fixed());
          fixed++;
        } else if (frozen == null || frozen.contains(v)) {
          keep(v);
        } else {
          entries.put(v, new Entry.Free());
        }
      }
    } catch (UnsupportedOperationException e) {
      // a variable class without copyTo
      live();
      return;
    }
    int childConstraints = carried.size();
    if (affine != null) {
      try {
        // an equality that ties a member to its representative stands for a dropped definition
        int tied = substitute(affine, carried, aliases);
        dropped -= tied;
        childConstraints += tied;
      } catch (FailException e) {
        outcome = Outcome.INFEASIBLE;
        child = null;
        return;
      }
    }
    Set<Var> distinctCopies = Collections.newSetFromMap(new IdentityHashMap<>());
    distinctCopies.addAll(copies.values());
    int childVariables = distinctCopies.size();
    for (Map.Entry<Var, Var> e : aliases.entrySet()) {
      Var copy = copies.get(e.getValue());
      copies.put(e.getKey(), copy);
      entries.put(e.getKey(), new Entry.Kept(copy));
    }

    for (Constraint c : carried) {
      if (reifications.rewritten(c)) {
        child.impose(reifications.rewrite(c, this));
        continue;
      }
      Constraint copy = ((Copyable<?>) c).copy(this);
      if (copy.getClass() != c.getClass()) {
        throw new IllegalStateException(
            c.getClass().getName() + " was copied as " + copy.getClass().getName());
      }
      child.impose(copy);
    }
    List<IntVar[][]> mappedClauses = new ArrayList<>();
    for (IntVar[][] c : childClauses) {
      IntVar[][] m = {get(c[0]), get(c[1])};
      if (clauses != null) {
        mappedClauses.add(m);
      } else {
        child.impose(new BoolClause(m[0], m[1]));
      }
    }
    if (clauses != null) {
      clauses.clear();
      clauses.addAll(mappedClauses);
    }
    // degree-based variable selections choose in the child as in the parent, whose static degrees
    // also count the constraints entailed or dropped since; a merged variable has the degrees of
    // its class added up
    Map<Var, Integer> degrees = new IdentityHashMap<>();
    for (Map.Entry<Var, Var> e : copies.entrySet()) {
      degrees.merge(e.getValue(), e.getKey().sizeConstraintsOriginal(), Integer::sum);
    }
    degrees.forEach((copy, degree) -> copy.adjustDegree(degree - copy.sizeConstraintsOriginal()));

    t = time("copy", t);
    relaxed = reifications.relaxed();
    statistics =
        new Statistics(
            variables.size(),
            collected.size(),
            childVariables,
            childConstraints,
            fixed,
            dropped,
            simplified,
            aliases.size());

    boolean consistent = child.consistency();
    t = time("childPropagation", t);
    if (!consistent) {
      // the child holds the same problem, so the parent is infeasible at this level
      outcome = Outcome.INFEASIBLE;
      child = null;
      return;
    }

    outcome = Outcome.DERIVED;
    if (retention == Retention.KEPT && originalClauses != null) {
      for (IntVar[][] c : originalClauses) {
        parent.impose(new BoolClause(c[0], c[1]));
      }
    }
    if (retention == Retention.RELEASED) {
      release();
      parent.setState(StoreState.SINK);
    } else {
      parent.setState(StoreState.SUSPENDED);
    }
    time("release", t);
  }

  /** Returns the frozen variables and the given ones, or null if every variable is frozen. */
  /**
   * Rule 8: eliminates variables with the constraints that define them, once the kept variables are
   * known. It leaves alone the merged variables, which the constraints still name, the variables of
   * the clauses and the constraints the reification cleanup rewrites.
   */
  private List<Constraint> eliminate(
      List<Constraint> carried,
      Map<Var, Var> aliases,
      ReificationCleanup reifications,
      Set<Var> clauseVariables) {
    Set<Var> kept = Collections.newSetFromMap(new IdentityHashMap<>());
    kept.addAll(frozen);
    kept.addAll(aliases.keySet());
    kept.addAll(aliases.values());
    kept.addAll(clauseVariables);
    Map<Var, Integer> half = reifications.relaxed();
    for (Constraint c : carried) {
      if (reifications.rewritten(c) || c.arguments().stream().anyMatch(half::containsKey)) {
        kept.addAll(c.arguments());
      }
    }
    VariableElimination elimination =
        new VariableElimination(kept, solutionPreserving, aliases, doubletons);
    List<Constraint> result = elimination.apply(carried);
    for (Var v : elimination.eliminated()) {
      entries.put(v, new Entry.Eliminated());
    }
    eliminated = elimination.eliminated().size();
    substitutions = elimination.substitutions();
    eliminationReconstruction = elimination.reconstruction();
    return result;
  }

  private Set<Var> frozenWith(Set<Var> vars) {
    if (frozen == null || vars.isEmpty()) {
      return frozen;
    }
    Set<Var> result = Collections.newSetFromMap(new IdentityHashMap<>());
    result.addAll(frozen);
    result.addAll(vars);
    return result;
  }

  /**
   * Fixes in the parent the values the clauses imply and propagates them.
   *
   * @return false if the parent becomes inconsistent.
   */
  private boolean fixImplied(Map<IntVar, Integer> implied) {
    if (implied.isEmpty()) {
      return true;
    }
    try {
      for (Map.Entry<IntVar, Integer> e : implied.entrySet()) {
        IntVar x = e.getKey();
        x.domain.in(level, x, e.getValue(), e.getValue());
      }
    } catch (FailException f) {
      return false;
    }
    if (!parent.consistency()) {
      return false;
    }
    level = parent.level;
    variables = variables(parent);
    collected = constraints(parent, variables);
    return true;
  }

  /**
   * Runs the rules in rounds, each followed by propagation of the parent. A round runs the rules of
   * the current timing class and the cheaper ones. A round that changes more than the abort factor
   * of the variables sends the next round back to the fast rules; one that changes less moves the
   * next round on to the next class. The rounds end when a round of the costliest class changes
   * less, or the budget of rounds or time is spent.
   *
   * @return false if the parent is inconsistent.
   */
  private boolean applyRules() {
    Context context = new Context();
    long start = System.nanoTime();
    Rule.Timing top = Rule.Timing.FAST;
    for (Rule rule : ruleList) {
      if (rule.timing().compareTo(top) > 0 && rule.timing().compareTo(maxTiming) <= 0) {
        top = rule.timing();
      }
    }
    Rule.Timing timing = Rule.Timing.FAST;
    while (rounds < maxRounds && (rounds == 0 || System.nanoTime() - start < budgetNanos)) {
      rounds++;
      timingRounds[timing.ordinal()]++;
      List<Var> before = variables(parent);
      double[] sizes = sizes(before);
      int edits = context.edits;
      for (Rule rule : ruleList) {
        if (rule.timing().compareTo(timing) > 0) {
          continue;
        }
        context.snapshot = null;
        // a rule that propagates may have raised the level (raiseLevelBeforeConsistency), and the
        // next one narrows domains at the level the store is at
        level = parent.level;
        long t = System.nanoTime();
        rule.apply(context);
        time(ruleName(rule), t);
      }
      long t = System.nanoTime();
      boolean consistent = parent.consistency();
      time("propagation", t);
      if (!consistent) {
        return false;
      }
      // propagating may raise the level, as before the rules
      level = parent.level;
      int changes = context.edits - edits + Math.abs(variables(parent).size() - before.size());
      double[] after = sizes(before);
      for (int i = 0; i < sizes.length; i++) {
        if (after[i] != sizes[i]) {
          changes++;
        }
      }
      if (changes > 0 && changes > abortFactor * before.size()) {
        timing = Rule.Timing.FAST;
      } else if (timing.compareTo(top) < 0) {
        timing = Rule.Timing.values()[timing.ordinal() + 1];
      } else {
        break;
      }
    }
    return true;
  }

  /**
   * Returns the rounds of rules run in each timing class, indexed by {@link Rule.Timing#ordinal()}.
   *
   * @return the rounds.
   */
  public int[] timingRounds() {
    return timingRounds.clone();
  }

  /** Adds the time since a start, in nanoseconds, to a phase of {@link #timings()}. */
  private long time(String phase, long start) {
    long now = System.nanoTime();
    timings.merge(phase, now - start, Long::sum);
    return now;
  }

  private static String ruleName(Rule rule) {
    // a lambda is named after the class that defines it
    String name = rule.getClass().getName();
    name = name.substring(name.lastIndexOf('.') + 1);
    int lambda = name.indexOf("$$");
    if (lambda > 0) {
      name = name.substring(0, lambda);
    }
    // an anonymous class is named after its enclosing class too
    while (name.matches(".*\\$\\d+")) {
      name = name.substring(0, name.lastIndexOf('$'));
    }
    name = name.substring(name.lastIndexOf('$') + 1);
    return Character.toLowerCase(name.charAt(0)) + name.substring(1);
  }

  /** The domain sizes of the variables, in order, to tell whether a round changed a domain. */
  private static double[] sizes(List<Var> vars) {
    double[] sizes = new double[vars.size()];
    for (int i = 0; i < sizes.length; i++) {
      sizes[i] = vars.get(i).getSizeFloat();
    }
    return sizes;
  }

  /** The view of the derivation that the rules get. */
  private final class Context implements Rule.Context {

    private int edits;
    private List<Constraint> snapshot;

    @Override
    public Store store() {
      return parent;
    }

    @Override
    public int level() {
      return level;
    }

    @Override
    public int round() {
      return rounds;
    }

    @Override
    public List<Constraint> constraints() {
      if (snapshot == null) {
        variables = variables(parent);
        List<Constraint> live = new ArrayList<>();
        for (Constraint c : Derivation.constraints(parent, variables)) {
          if (!removed.contains(c)) {
            live.add(c);
          }
        }
        snapshot = Collections.unmodifiableList(live);
      }
      return snapshot;
    }

    @Override
    public void impose(Constraint c) {
      parent.impose(c);
      snapshot = null;
      edits++;
    }

    @Override
    public void remove(Constraint c) {
      if (removed.add(c)) {
        snapshot = null;
        edits++;
      }
    }

    @Override
    public boolean removed(Constraint c) {
      return removed.contains(c);
    }
  }

  private void keep(Var v) {
    Var copy = v.copyTo(child);
    copies.put(v, copy);
    entries.put(v, new Entry.Kept(copy));
  }

  /**
   * The variables of a store: those of the store array in store order, then the Boolean variables,
   * which the store keeps only by id.
   */
  static List<Var> variables(Store store) {
    List<Var> result = new ArrayList<>();
    for (int i = 0; i < store.size(); i++) {
      result.add(store.vars[i]);
    }
    for (Var v : store.variablesHashMap.values()) {
      if (v.index() < 0) {
        result.add(v);
      }
    }
    return result;
  }

  /**
   * The constraints attached in a store, walking the variables in store order and each variable's
   * constraints in attachment order, so a derivation is deterministic. Besides the constraints of a
   * variable's domain, this takes the constraints that only watch the variable: for a value ({@link
   * Store#watchValue}, for example a long 0-1 linear constraint) or as a watched literal ({@link
   * Store#registerWatchedLiteralConstraint}).
   */
  static List<Constraint> constraints(Store store, List<Var> variables) {
    Map<Constraint, Boolean> seen = new IdentityHashMap<>();
    List<Constraint> result = new ArrayList<>();
    for (Var v : variables) {
      List<Constraint> attached = new ArrayList<>(v.dom().constraints());
      attached.addAll(store.valueWatchers(v));
      attached.addAll(store.watchedLiteralConstraints(v));
      for (Constraint c : attached) {
        if (c != null && !c.isEntailed() && seen.put(c, Boolean.TRUE) == null) {
          result.add(c);
        }
      }
    }
    return result;
  }

  private boolean copyable() {
    for (Constraint c : collected) {
      if (!Copyable.canCopy(c)) {
        return false;
      }
    }
    return true;
  }

  /**
   * Narrows the counterpart of every representative to the values all members of its class allow,
   * and maps each member to that counterpart (an alias) or to a view of it. A propagator does not
   * expect two of its variables to change together, so a member that shares a constraint with
   * another variable of its class gets a copy of its own instead, tied to the representative's
   * counterpart by an equality.
   *
   * @return the number of equalities imposed.
   */
  private int substitute(
      AffineSubstitution affine, List<Constraint> carried, Map<Var, Var> aliases) {
    for (Var v : variables) {
      if (!affine.isRoot(v)) {
        continue;
      }
      IntVar r = (IntVar) copies.get(v);
      for (IntVar m : affine.members(v)) {
        AffineSubstitution.Relation rel = affine.relation(m);
        if (rel != null) {
          r.domain.in(child.level, r, AffineDomain.preimage(m.dom(), 0, rel.a(), rel.b()));
        }
      }
    }
    Set<Var> shared = Collections.newSetFromMap(new IdentityHashMap<>());
    Map<Var, Var> seen = new IdentityHashMap<>();
    int tied = 0;
    for (Constraint c : carried) {
      seen.clear();
      for (Var x : c.arguments()) {
        Var y = aliases.getOrDefault(x, x);
        Var other = seen.put(affine.root(y), y);
        if (other != null && other != y) {
          shared.add(y);
          shared.add(other);
        }
      }
    }
    for (Var v : variables) {
      AffineSubstitution.Relation rel = affine.relation(v);
      if (rel == null) {
        continue;
      }
      IntVar r = (IntVar) copies.get(rel.root());
      Var copy;
      if (shared.contains(v)) {
        IntVar own = (IntVar) v.copyTo(child);
        child.impose(equality(own, rel.a(), r, rel.b()));
        tied++;
        copy = own;
      } else if (rel.identity()) {
        copy = r;
        affineSubstituted++;
      } else {
        copy = new AffineView(child, v.id(), r, rel.a(), rel.b());
        affineSubstituted++;
      }
      copies.put(v, copy);
      entries.put(v, new Entry.Kept(copy));
    }
    return tied;
  }

  /** The constraint x = a*y + b. */
  private static Constraint equality(IntVar x, int a, IntVar y, int b) {
    if (a == 1 && b == 0) {
      return new XeqY(y, x);
    }
    if (a == 1) {
      return new XplusCeqZ(y, b, x);
    }
    if (b == 0) {
      return new XmulCeqZ(y, a, x);
    }
    return new LinearInt(new IntVar[] {x, y}, new int[] {1, -a}, "==", b);
  }

  private void live() {
    outcome = Outcome.LIVE;
    child = parent;
    entries.clear();
    copies.clear();
    reconstruction = null;
    eliminationReconstruction = null;
    eliminated = 0;
    substitutions = 0;
    affineSubstituted = 0;
    statistics =
        new Statistics(
            variables.size(), collected.size(), variables.size(), collected.size(), 0, 0, 0, 0);
  }

  /**
   * Rule 1: at a fixpoint a constraint whose variables are all fixed is satisfied, and so is one
   * whose satisfaction check says so.
   */
  private static boolean entailed(Constraint c) {
    boolean allFixed = true;
    for (Var v : c.arguments()) {
      if (!v.singleton()) {
        allFixed = false;
        break;
      }
    }
    return allFixed || c instanceof SatisfiedPresent s && s.satisfied();
  }

  private void release() {
    if (level > 0) {
      for (Constraint c : collected) {
        parent.markEntailed(c);
      }
      return;
    }
    // Nothing restores level 0, so each variable drops its constraint lists at once; removing the
    // constraints one by one costs time quadratic in the number of constraints of a variable.
    for (Var v : variables) {
      Domain d = v.dom();
      if (d.modelConstraints != null) {
        d.modelConstraints = new Constraint[d.modelConstraints.length][];
        d.modelConstraintsToEvaluate = new int[d.modelConstraintsToEvaluate.length];
      }
      d.searchConstraints = new ArrayList<>();
      d.searchConstraintsToEvaluate = 0;
      d.searchConstraintsCloned = false;
      parent.clearValueWatches(v);
    }
    parent.clearWatchedConstraint();
  }

  /**
   * Returns the result of deriving.
   *
   * @return the outcome.
   */
  public Outcome outcome() {
    return outcome;
  }

  /**
   * Returns the store to search: the child, or the parent itself when the outcome is {@link
   * Outcome#LIVE}.
   *
   * @return the store to search.
   * @throws IllegalStateException if the parent is infeasible.
   */
  public Store child() {
    if (outcome == Outcome.INFEASIBLE) {
      throw new IllegalStateException("The parent is infeasible; there is no child");
    }
    return child;
  }

  /**
   * Returns the parent store.
   *
   * @return the parent.
   */
  public Store parent() {
    return parent;
  }

  /**
   * Returns the parent's level at which the child was derived.
   *
   * @return the level.
   */
  public int level() {
    return level;
  }

  /**
   * Returns the presolve rules of this derivation, in the order they run.
   *
   * @return the rules.
   */
  public List<Rule> rules() {
    return Collections.unmodifiableList(ruleList);
  }

  /**
   * Returns the rounds of presolve rules run, 0 when there are no rules.
   *
   * @return the rounds.
   */
  public int rounds() {
    return rounds;
  }

  /**
   * Returns the sizes of the parent and the child.
   *
   * @return the statistics, or null if the parent is infeasible at its level.
   */
  public Statistics statistics() {
    return statistics;
  }

  /**
   * Returns the number of variables eliminated with their defining constraint (rule 8).
   *
   * @return the number of eliminated variables.
   */
  public int eliminated() {
    return eliminated;
  }

  /**
   * Returns the number of constraints into which rule 8 substituted an eliminated variable.
   *
   * @return the number of substituted constraints.
   */
  public int substitutions() {
    return substitutions;
  }

  /**
   * Returns the number of parent variables that rule 2 replaced by their class representative or by
   * a view of it.
   *
   * @return the number of substituted variables.
   */
  public int affineSubstituted() {
    return affineSubstituted;
  }

  /**
   * Returns what the SAT preprocessing of the clauses did.
   *
   * @return the statistics, or null if it did not run.
   */
  public ClauseStatistics clauseStatistics() {
    return clauseStatistics;
  }

  /**
   * Returns how much each presolve rule reduced, by name, in the order the rules ran.
   *
   * @return the reductions; empty if no child was derived.
   */
  public Map<String, Integer> reductions() {
    return Collections.unmodifiableMap(reductions);
  }

  /**
   * Returns the time each phase of the derivation took, in nanoseconds of wall-clock time, in the
   * order the phases first ran: each rule under its class name, the propagation after the rounds of
   * rules ("propagation"), and the steps that build the child ("collect", "satPresolve", "rewrite",
   * "reificationCleanup", "elimination", "affineSubstitution", "copy", "childPropagation",
   * "release").
   *
   * @return the times.
   */
  public Map<String, Long> timings() {
    return Collections.unmodifiableMap(timings);
  }

  /**
   * Returns the parent variables that the child half-reifies: Booleans that are not frozen. Once
   * the other variables of the child are fixed, propagation leaves each of them either fixed or
   * free to take the value that satisfies every constraint on it, so a search of the child can
   * leave them out; postsolve gives them their value in the parent.
   *
   * @return the relaxed variables.
   */
  public Set<Var> relaxed() {
    return Collections.unmodifiableSet(relaxed.keySet());
  }

  /**
   * Returns what the dual reductions did.
   *
   * @return the statistics, or null if they were not run.
   */
  public DualStatistics dualStatistics() {
    return dualStatistics;
  }

  /**
   * Returns what the derivation did with a parent variable.
   *
   * @param v a variable of the parent.
   * @return the entry, or {@code Kept(v)} itself when the outcome is {@link Outcome#LIVE}.
   */
  public Entry entry(Var v) {
    if (outcome == Outcome.LIVE) {
      return new Entry.Kept(v);
    }
    Entry e = entries.get(v);
    if (e == null) {
      throw new IllegalArgumentException("Variable " + v.id() + " is not a variable of the parent");
    }
    return e;
  }

  @Override
  public Store target() {
    return child();
  }

  /**
   * Returns the child's counterpart of a parent variable.
   *
   * @param v a variable of the parent.
   * @return the counterpart, or null if the child has none (the variable is fixed, free or
   *     eliminated).
   */
  @Override
  @SuppressWarnings("unchecked")
  public <V extends Var> V get(V v) {
    if (outcome == Outcome.LIVE) {
      return v;
    }
    Var copy = copies.get(v);
    if (copy == null && !entries.containsKey(v)) {
      throw new IllegalArgumentException("Variable " + v.id() + " is not a variable of the parent");
    }
    return (V) copy;
  }

  /**
   * Maps variables to their counterparts and leaves out those without one, for example to turn
   * decision variables of the parent into decision variables of the child.
   *
   * @param <V> the type of the variables.
   * @param vars variables of the parent.
   * @return the counterparts, in order, in an array of the same runtime type.
   */
  public <V extends Var> V[] counterparts(V[] vars) {
    V[] mapped = get(vars);
    int n = 0;
    for (V v : mapped) {
      if (v != null) {
        mapped[n++] = v;
      }
    }
    return java.util.Arrays.copyOf(mapped, n);
  }

  /**
   * Writes the child's current solution into the parent, at the level above the derivation level,
   * replacing a solution written before. With {@link Retention#KEPT} the parent then propagates its
   * whole model, which checks the solution.
   *
   * @return true if the parent accepts the solution.
   * @throws IllegalStateException with {@link Retention#KEPT} if the solution violates the parent's
   *     model, which means the derivation is wrong.
   */
  public boolean returnSolution() {
    if (outcome == Outcome.LIVE) {
      return true;
    }
    child();
    boolean[] accepted = {true};
    parent.runReturning(
        () -> {
          clearSolution();
          parent.setLevel(level + 1);
          solutionWritten = true;
          try {
            Map<IntVar, Integer> reconstructed =
                reconstruction == null ? Map.of() : reconstruction.values(this::solutionValue);
            for (Map.Entry<Var, Var> e : copies.entrySet()) {
              Var v = e.getKey();
              if (reconstructed.containsKey(v)) {
                continue;
              }
              Integer enforcing = relaxed.get(v);
              if (enforcing != null && !((IntDomain) e.getValue().dom()).singleton(enforcing)) {
                // a half-reified Boolean: the parent's reification gives it its value
                continue;
              }
              v.dom().in(parent.level, v, e.getValue().dom());
            }
            // the variables the clause preprocessing removed, from the values of the child; none
            // is half-reified, since the variables of the clauses are frozen for that rule
            for (Map.Entry<IntVar, Integer> e : reconstructed.entrySet()) {
              IntVar x = e.getKey();
              x.domain.in(parent.level, x, e.getValue(), e.getValue());
            }
            // then the variables rule 8 eliminated, from the parent's values of the others; their
            // definitions name no variable of the clauses
            accepted[0] =
                (eliminationReconstruction == null || eliminationReconstruction.apply(parent))
                    && parent.consistency();
          } catch (FailException f) {
            accepted[0] = false;
          }
        });
    if (!accepted[0] && retention == Retention.KEPT) {
      throw new IllegalStateException(
          "A solution of the derived store violates the model of the parent store");
    }
    return accepted[0];
  }

  /** The value of a variable in the child's solution, its smallest value if it is not fixed. */
  private int solutionValue(IntVar x) {
    Var copy = copies.get(x);
    IntVar v = copy instanceof IntVar c ? c : x;
    return v.singleton() ? v.value() : v.min();
  }

  /**
   * Ends the derivation: removes a written solution with {@link Retention#KEPT}, which makes the
   * parent active again at the derivation level; a released parent keeps its last solution and is
   * closed.
   */
  public void discard() {
    if (outcome != Outcome.DERIVED) {
      return;
    }
    if (retention == Retention.KEPT) {
      parent.runReturning(this::clearSolution);
      parent.setState(StoreState.ACTIVE);
    } else {
      parent.setState(StoreState.CLOSED);
    }
    child = null;
    copies.clear();
  }

  private void clearSolution() {
    if (solutionWritten) {
      // propagating the solution may have raised the level further (raiseLevelBeforeConsistency)
      while (parent.level > level) {
        parent.removeLevel(parent.level);
        parent.setLevel(parent.level - 1);
      }
      solutionWritten = false;
    }
  }

  @Override
  public String toString() {
    Map<String, Object> shown = new LinkedHashMap<>();
    shown.put("outcome", outcome);
    shown.put("level", level);
    shown.put("retention", retention);
    shown.put("rounds", rounds);
    shown.put("statistics", statistics);
    return "Derivation" + shown;
  }
}
