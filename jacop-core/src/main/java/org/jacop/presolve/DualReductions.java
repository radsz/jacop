/*
 * DualReductions.java
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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.api.Monotone;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.LinearForm;

/**
 * Dual reductions before a derivation: dual fixing and dual bound strengthening (Achterberg et al.,
 * Presolve reductions in mixed integer programming, 2020; CP-SAT's {@code var_domination.h}).
 *
 * <p>A variable that every constraint lets decrease is fixed to its minimum, since any solution
 * stays a solution, with the same objective, when the variable takes its minimum instead; likewise
 * for increasing and the maximum. A variable whose decrease only constraints that hold once it is
 * at least {@code t} forbid loses its values above the smallest value at least {@code t}, and
 * likewise upwards. The objective variable also counts the objective as a constraint that forbids
 * moving it the wrong way.
 *
 * <p>When the objective is defined by one linear equality and occurs in no other constraint, the
 * equality is read as the inequality towards the objective (for minimisation {@code obj >= expr}):
 * moving a variable so that {@code expr} improves keeps a solution once the objective follows it.
 * This needs the objective's domain to be an interval that does not cut {@code expr} on the
 * improving side, and the objective itself is then left alone.
 *
 * <p>The reductions keep at least one solution and every optimum, but not every solution, so they
 * are only for searches that want one solution or an optimum. Each round reduces each variable at
 * most once, which keeps every reduction of a round valid with the others applied; the derivation
 * propagates between rounds. Unlike the other rules, the reductions remove solutions, so a
 * derivation runs this rule, after the others, only when asked for (see {@link
 * Derivation.Builder#dualReductions(boolean)}).
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class DualReductions implements Rule {

  /** The locks on one variable in a round. */
  private static final class Info {
    // constraints that forbid a decrease or an increase, and of them those with no threshold
    int downLocks;
    int upLocks;
    int downOpen;
    int upOpen;
    // the largest threshold above which a constraint forbidding a decrease holds, and likewise
    long above = Long.MIN_VALUE;
    long below = Long.MAX_VALUE;
    boolean constrained;

    /** Adds the locks of one constraint. */
    void lock(int free, long above, long below) {
      constrained = true;
      if ((free & Monotone.DECREASE) == 0) {
        downLocks++;
        if (above == Locks.NONE_ABOVE) {
          downOpen++;
        } else {
          this.above = Math.max(this.above, above);
        }
      }
      if ((free & Monotone.INCREASE) == 0) {
        upLocks++;
        if (below == Locks.NONE_BELOW) {
          upOpen++;
        } else {
          this.below = Math.min(this.below, below);
        }
      }
    }

    /** Takes back a lock without a threshold. */
    void unlock(int direction) {
      if (direction == Monotone.DECREASE) {
        downLocks--;
        downOpen--;
      } else {
        upLocks--;
        upOpen--;
      }
    }
  }

  /** The locks of one constraint, merged over the reports for each variable. */
  private static final class Report {
    int free = Monotone.DECREASE | Monotone.INCREASE;
    long above = Long.MIN_VALUE;
    long below = Long.MAX_VALUE;
  }

  private final IntVar objective;
  private final boolean minimize;
  private final Set<Var> exempt;

  private int rounds;
  private int fixed;
  private int tightened;

  /**
   * Prepares dual reductions.
   *
   * @param objective the objective variable, or null for a satisfaction problem.
   * @param minimize true if the objective is minimised.
   * @param exempt variables to leave alone, for example those of constraints posted later.
   */
  DualReductions(IntVar objective, boolean minimize, Set<Var> exempt) {
    this.objective = objective;
    this.minimize = minimize;
    this.exempt = exempt;
  }

  /**
   * Returns the number of rounds run.
   *
   * @return the number.
   */
  int rounds() {
    return rounds;
  }

  /**
   * Returns the number of variables the reductions fixed.
   *
   * @return the number.
   */
  int fixed() {
    return fixed;
  }

  /**
   * Returns the number of times the reductions removed values without fixing a variable.
   *
   * @return the number.
   */
  int tightened() {
    return tightened;
  }

  @Override
  public void apply(Context context) {
    rounds++;
    apply(context.store(), context.level(), context.constraints());
  }

  /**
   * Runs one round: computes the locks of the constraints and reduces each variable at most once.
   *
   * @param store the store, at a fixpoint.
   * @param level the level at which domains are narrowed.
   * @param constraints the constraints of the problem that are not entailed.
   * @return true if a domain changed.
   * @throws org.jacop.core.FailException if a domain becomes empty, which means the problem has no
   *     solution.
   */
  boolean apply(Store store, int level, List<Constraint> constraints) {
    Map<Var, Info> infos = new IdentityHashMap<>();
    for (Var v : Derivation.variables(store)) {
      if (v instanceof IntVar iv && !iv.singleton() && !exempt.contains(v)) {
        infos.put(iv, new Info());
      }
    }
    if (infos.isEmpty()) {
      return false;
    }
    List<Constraint> live = new ArrayList<>(constraints.size());
    for (Constraint c : constraints) {
      if (!(c instanceof SatisfiedPresent s && s.satisfied())) {
        live.add(c);
      }
    }

    Constraint definition = objectiveDefinition(live);
    if (definition != null) {
      infos.remove(objective);
    } else if (objective != null && infos.get(objective) instanceof Info info) {
      info.lock(
          minimize ? Monotone.DECREASE : Monotone.INCREASE, Locks.NONE_ABOVE, Locks.NONE_BELOW);
    }

    // a constraint that defines a variable locks all its variables here, and below lets an input
    // move where the defined variable can follow it
    List<Locks.Definition> definitions = new ArrayList<>();
    for (Constraint c : live) {
      Locks.Definition d = c == definition ? null : Locks.definition(c);
      if (d != null) {
        definitions.add(d);
        lock(infos, c, null, true);
      } else {
        lock(infos, c, c == definition ? relaxed(Locks.form(c)) : null, false);
      }
    }
    relax(infos, definitions);

    boolean changed = false;
    for (Map.Entry<Var, Info> e : infos.entrySet()) {
      // a variable of no constraint is not part of the problem; search gives it any value
      if (e.getValue().constrained) {
        changed |= reduce(level, (IntVar) e.getKey(), e.getValue());
      }
    }
    return changed;
  }

  /**
   * Adds the locks of a constraint: on all its variables in both directions, or read through a
   * linear form if one is given, or else those the constraint has.
   */
  private static void lock(Map<Var, Info> infos, Constraint c, LinearForm form, boolean all) {
    Map<Var, Report> reports = new IdentityHashMap<>();
    Locks.Sink sink =
        (v, free, above, below) -> {
          if (infos.containsKey(v)) {
            Report r = reports.computeIfAbsent(v, x -> new Report());
            r.free &= free;
            if ((free & Monotone.DECREASE) == 0) {
              r.above = Math.max(r.above, above);
            }
            if ((free & Monotone.INCREASE) == 0) {
              r.below = Math.min(r.below, below);
            }
          }
        };
    if (form != null) {
      Locks.collect(form, c.arguments(), sink);
    } else if (all) {
      for (Var v : c.arguments()) {
        sink.lock(v, 0, Locks.NONE_ABOVE, Locks.NONE_BELOW);
      }
    } else {
      Locks.collect(c, sink);
    }
    for (Map.Entry<Var, Report> e : reports.entrySet()) {
      Report r = e.getValue();
      infos.get(e.getKey()).lock(r.free, r.above, r.below);
    }
  }

  /**
   * Takes back the locks of definitions on their inputs in the directions the defined variable can
   * follow: those in which no other constraint locks it. Which directions it can follow is decided
   * before any lock is taken back, so a defined variable that is the input of another definition
   * stays locked by it.
   */
  private static void relax(Map<Var, Info> infos, List<Locks.Definition> definitions) {
    int n = definitions.size();
    boolean[] up = new boolean[n];
    boolean[] down = new boolean[n];
    for (int i = 0; i < n; i++) {
      Info f = infos.get(definitions.get(i).defined());
      // the definition itself is one lock in each direction
      up[i] = f != null && f.upLocks == 1;
      down[i] = f != null && f.downLocks == 1;
    }
    for (int i = 0; i < n; i++) {
      for (Map.Entry<Var, Integer> e : definitions.get(i).inputs().entrySet()) {
        Info x = infos.get(e.getKey());
        if (x == null) {
          continue;
        }
        int m = e.getValue();
        boolean increase = m == Locks.INDEPENDENT || m == 1 && up[i] || m == -1 && down[i];
        boolean decrease = m == Locks.INDEPENDENT || m == 1 && down[i] || m == -1 && up[i];
        if (increase) {
          x.unlock(Monotone.INCREASE);
        }
        if (decrease) {
          x.unlock(Monotone.DECREASE);
        }
      }
    }
  }

  private boolean reduce(int level, IntVar v, Info info) {
    IntDomain d = v.dom();
    int min = d.min();
    int max = d.max();
    if (info.downLocks == 0) {
      return restrict(level, v, min, min);
    }
    if (info.upLocks == 0) {
      return restrict(level, v, max, max);
    }
    if (info.downOpen == 0 && info.above < max) {
      int t = (int) Math.max(info.above, min);
      return restrict(level, v, min, d.contains(t) ? t : d.nextValue(t));
    }
    if (info.upOpen == 0 && info.below > min) {
      int t = (int) Math.min(info.below, max);
      return restrict(level, v, d.contains(t) ? t : d.previousValue(t), max);
    }
    return false;
  }

  private boolean restrict(int level, IntVar v, int min, int max) {
    v.domain.in(level, v, min, max);
    if (v.singleton()) {
      fixed++;
    } else {
      tightened++;
    }
    return true;
  }

  /**
   * The linear equality that defines the objective, if it is its only constraint and the domain of
   * the objective lets it follow the expression on the improving side.
   */
  private Constraint objectiveDefinition(List<Constraint> live) {
    if (objective == null || objective.singleton()) {
      return null;
    }
    Constraint definition = null;
    for (Constraint c : live) {
      if (c.arguments().contains(objective)) {
        if (definition != null) {
          return null;
        }
        definition = c;
      }
    }
    if (definition == null) {
      return null;
    }
    LinearForm form = Locks.form(definition);
    if (form == null || form.relation() != LinearForm.EQ) {
      return null;
    }
    Map<IntVar, Long> weights = Locks.merged(form);
    Long w = weights.get(objective);
    if (w == null || Math.abs(w) != 1) {
      return null;
    }
    IntDomain d = objective.dom();
    if (d.getSize() != (long) d.max() - d.min() + 1) {
      return null;
    }
    // objective = w * (c - rest), where rest is the sum of the other terms
    long low = 0;
    long high = 0;
    for (Map.Entry<IntVar, Long> e : weights.entrySet()) {
      if (e.getKey() != objective) {
        long a = -w * e.getValue();
        IntVar x = e.getKey();
        low += Math.min(a * x.min(), a * x.max());
        high += Math.max(a * x.min(), a * x.max());
      }
    }
    long constant = w * form.c();
    boolean followed = minimize ? d.min() <= constant + low : d.max() >= constant + high;
    return followed ? definition : null;
  }

  /**
   * The objective's defining equality as the inequality towards the objective: for minimisation the
   * objective is at least the expression, for maximisation at most.
   */
  private LinearForm relaxed(LinearForm form) {
    long w = Locks.merged(form).get(objective);
    // with w = 1, objective = c - rest, and objective >= c - rest is sum >= c
    boolean atLeast = minimize == (w > 0);
    return new LinearForm(
        form.vars(), form.weights(), form.c(), atLeast ? LinearForm.GE : LinearForm.LE);
  }
}
