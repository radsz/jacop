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
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.Domain;
import org.jacop.core.FailException;
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
   */
  public record Statistics(
      int parentVariables,
      int parentConstraints,
      int childVariables,
      int childConstraints,
      int fixed,
      int dropped) {}

  private final Store parent;
  private final Retention retention;
  private final Set<Var> frozen;
  private final boolean rules;
  private final List<Rule> ruleList;
  private final int maxRounds;

  private Outcome outcome;
  private int level;
  private Store child;
  private final Map<Var, Entry> entries = new IdentityHashMap<>();
  private final Map<Var, Var> copies = new IdentityHashMap<>();
  private List<Var> variables = List.of();
  private List<Constraint> collected = List.of();
  private Statistics statistics;
  private boolean solutionWritten;
  private Reconstruction reconstruction;
  private int eliminated;
  private int substitutions;
  private int rounds;
  private final Set<Constraint> removed = Collections.newSetFromMap(new IdentityHashMap<>());

  private Derivation(Builder builder) {
    this.parent = builder.parent;
    this.retention = builder.retention;
    this.frozen = builder.frozen;
    this.rules = builder.rules;
    this.ruleList = List.copyOf(builder.ruleList);
    this.maxRounds = builder.maxRounds;
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
    private final List<Rule> ruleList = new ArrayList<>();
    private int maxRounds = DEFAULT_ROUNDS;

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
    }
    variables = allVariables();
    collected = collectConstraints();

    if (!copyable()) {
      live();
      return;
    }

    List<Constraint> carried = new ArrayList<>();
    int dropped = 0;
    for (Constraint c : collected) {
      if (rules && (removed.contains(c) || entailed(c))) {
        dropped++;
      } else {
        carried.add(c);
      }
    }

    // rule 8 needs to know which variables must be kept
    if (rules && frozen != null) {
      VariableElimination elimination = new VariableElimination(frozen);
      carried = elimination.apply(carried);
      for (Var v : elimination.eliminated()) {
        entries.put(v, new Entry.Eliminated());
      }
      eliminated = elimination.eliminated().size();
      substitutions = elimination.substitutions();
      reconstruction = elimination.reconstruction();
    }

    Set<Var> used = Collections.newSetFromMap(new IdentityHashMap<>());
    for (Constraint c : carried) {
      used.addAll(c.arguments());
    }

    child = new Store();
    int fixed = 0;
    try {
      for (Var v : variables) {
        if (entries.containsKey(v)) {
          // eliminated
          continue;
        }
        if (used.contains(v) || !rules) {
          keep(v);
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

    for (Constraint c : carried) {
      Constraint copy = ((Copyable<?>) c).copy(this);
      if (copy.getClass() != c.getClass()) {
        throw new IllegalStateException(
            c.getClass().getName() + " was copied as " + copy.getClass().getName());
      }
      child.impose(copy);
    }
    // degree-based variable selections choose in the child as in the parent, whose static degrees
    // also count the constraints entailed or dropped since
    for (Map.Entry<Var, Var> e : copies.entrySet()) {
      e.getValue()
          .adjustDegree(
              e.getKey().sizeConstraintsOriginal() - e.getValue().sizeConstraintsOriginal());
    }

    statistics =
        new Statistics(
            variables.size(), collected.size(), copies.size(), carried.size(), fixed, dropped);

    if (!child.consistency()) {
      // the child holds the same problem, so the parent is infeasible at this level
      outcome = Outcome.INFEASIBLE;
      child = null;
      return;
    }

    outcome = Outcome.DERIVED;
    if (retention == Retention.RELEASED) {
      release();
      parent.setState(StoreState.SINK);
    } else {
      parent.setState(StoreState.SUSPENDED);
    }
  }

  /**
   * Runs the rules in rounds, each followed by propagation of the parent, until a round changes
   * nothing or the budget of rounds is spent.
   *
   * @return false if the parent is inconsistent.
   */
  private boolean applyRules() {
    Context context = new Context();
    while (rounds < maxRounds) {
      rounds++;
      List<Var> before = allVariables();
      double[] sizes = sizes(before);
      int edits = context.edits;
      for (Rule rule : ruleList) {
        context.snapshot = null;
        rule.apply(context);
      }
      if (!parent.consistency()) {
        return false;
      }
      // propagating may raise the level, as before the rules
      level = parent.level;
      if (context.edits == edits
          && allVariables().size() == before.size()
          && Arrays.equals(sizes, sizes(before))) {
        break;
      }
    }
    return true;
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
        variables = allVariables();
        List<Constraint> live = new ArrayList<>();
        for (Constraint c : collectConstraints()) {
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
   * The variables of the parent: those of the store array in store order, then the Boolean
   * variables, which the store keeps only by id.
   */
  private List<Var> allVariables() {
    List<Var> result = new ArrayList<>();
    for (int i = 0; i < parent.size(); i++) {
      result.add(parent.vars[i]);
    }
    for (Var v : parent.variablesHashMap.values()) {
      if (v.index() < 0) {
        result.add(v);
      }
    }
    return result;
  }

  /**
   * The constraints attached in the parent, walking the variables in store order and each
   * variable's constraints in attachment order, so a derivation is deterministic. Besides the
   * constraints of a variable's domain, this takes the constraints that only watch the variable:
   * for a value ({@link Store#watchValue}, for example a long 0-1 linear constraint) or as a
   * watched literal ({@link Store#registerWatchedLiteralConstraint}).
   */
  private List<Constraint> collectConstraints() {
    Map<Constraint, Boolean> seen = new IdentityHashMap<>();
    List<Constraint> result = new ArrayList<>();
    for (Var v : variables) {
      List<Constraint> attached = new ArrayList<>(v.dom().constraints());
      attached.addAll(parent.valueWatchers(v));
      if (parent.watchedConstraints != null) {
        attached.addAll(parent.watchedConstraints.getOrDefault(v, Set.of()));
      }
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

  private void live() {
    outcome = Outcome.LIVE;
    child = parent;
    entries.clear();
    copies.clear();
    reconstruction = null;
    eliminated = 0;
    substitutions = 0;
    statistics =
        new Statistics(
            variables.size(), collected.size(), variables.size(), collected.size(), 0, 0);
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
    if (parent.watchedConstraints != null) {
      parent.watchedConstraints.clear();
    }
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
            for (Map.Entry<Var, Var> e : copies.entrySet()) {
              Var v = e.getKey();
              v.dom().in(parent.level, v, e.getValue().dom());
            }
            accepted[0] =
                (reconstruction == null || reconstruction.apply(parent)) && parent.consistency();
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
