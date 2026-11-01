/*
 * DominatedColumns.java
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
import java.util.Comparator;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.api.Monotone;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.lcg.LinearForm;

/**
 * Dominated columns (SCIP's {@code presol_domcol}; CP-SAT's {@code var_domination.h}), run by the
 * dual reductions once they reach a fixpoint.
 *
 * <p>A variable {@code x} dominates a variable {@code y} when moving {@code x} one value up and
 * {@code y} one value down keeps every solution a solution, with an objective at least as good. In
 * a linear relation {@code sum w * v <= c} this holds when {@code w(x) <= w(y)} (a missing variable
 * has weight 0), in an equality when {@code w(x) = w(y)}, and in a {@link Monotone} constraint when
 * {@code x} may increase and {@code y} may decrease; any other constraint on {@code x} or {@code y}
 * rules the pair out. Repeating the move from any solution while {@code x} is below its maximum and
 * {@code y} above its minimum reaches a solution, as good, with {@code x = max(x)} or {@code y =
 * min(y)}, so that clause is imposed: {@code y <= x} for two 0/1 variables.
 *
 * <p>Clauses of several pairs are imposed together only along one order of the variables, a pair
 * {@code (x, y)} only when {@code x} comes after {@code y}. Each move on a pair whose clause is
 * false then raises {@code sum pos(v) * v}, which is bounded, so the moves stop at a solution that
 * satisfies every clause. Both variables need domains without holes, so that each move stays in
 * them.
 *
 * <p>The objective's defining equality is read as the inequality towards the objective, as by the
 * dual reductions; the objective variable itself is left alone. The search for pairs takes the
 * candidates {@code y} of {@code x} from the shortest constraint that forbids {@code x} to
 * increase, and stops after a budget of comparisons (the system property {@code
 * jacop.presolve.domcol.budget}).
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class DominatedColumns {

  /** Whether the dual reductions look for dominated columns (jacop.presolve.domcol). */
  static final boolean ENABLED =
      Boolean.parseBoolean(System.getProperty("jacop.presolve.domcol", "true"));

  private static final long BUDGET = Long.getLong("jacop.presolve.domcol.budget", 20_000_000L);

  private static final int LE = 0;
  private static final int EQ = 1;
  private static final int MONOTONE = 2;

  /**
   * How a constraint reads a variable: a weight as in {@code sum w * v <= c}, or free directions.
   */
  private record Term(int constraint, int kind, long weight, int free) {

    /** True if the constraint forbids the variable to increase. */
    boolean locksUp() {
      return switch (kind) {
        case LE -> weight > 0;
        case EQ -> true;
        default -> (free & Monotone.INCREASE) == 0;
      };
    }
  }

  // the candidates in the order given, and how each constraint reads them
  private final List<IntVar> vars = new ArrayList<>();
  private final Map<IntVar, Map<Integer, Term>> terms = new IdentityHashMap<>();
  private final Set<Var> blocked = Collections.newSetFromMap(new IdentityHashMap<>());
  private final List<Constraint> live;
  private long work;

  private int pairs;
  private int imposed;

  /**
   * Reads the constraints.
   *
   * @param live the constraints that are not entailed.
   * @param definition the objective's defining equality, or null.
   * @param relaxed that equality as the inequality towards the objective, or null.
   * @param candidates the variables that may be moved.
   */
  DominatedColumns(
      List<Constraint> live, Constraint definition, LinearForm relaxed, List<IntVar> candidates) {
    this.live = live;
    for (IntVar v : candidates) {
      if (holeless(v)) {
        terms.put(v, new HashMap<>());
      }
    }
    for (int i = 0; i < live.size(); i++) {
      Constraint c = live.get(i);
      read(i, c, c == definition ? relaxed : Locks.form(c));
    }
    terms.keySet().removeIf(v -> blocked.contains(v) || terms.get(v).isEmpty());
    for (IntVar v : candidates) {
      if (terms.containsKey(v)) {
        vars.add(v);
      }
    }
  }

  private static boolean holeless(IntVar v) {
    IntDomain d = v.dom();
    return !d.singleton() && d.getSize() == (long) d.max() - d.min() + 1;
  }

  private void read(int index, Constraint c, LinearForm form) {
    if (form != null && form.relation() != LinearForm.NE) {
      Map<IntVar, Long> weights = Locks.merged(form);
      for (Var v : c.arguments()) {
        if (!(v instanceof IntVar iv) || !weights.containsKey(iv)) {
          blocked.add(v);
        }
      }
      int kind = form.relation() == LinearForm.EQ ? EQ : LE;
      long sign = form.relation() == LinearForm.GE ? -1 : 1;
      for (Map.Entry<IntVar, Long> e : weights.entrySet()) {
        if (e.getValue() != 0) {
          add(e.getKey(), new Term(index, kind, sign * e.getValue(), 0));
        }
      }
    } else if (form == null && c instanceof Monotone m) {
      for (Var v : c.arguments()) {
        if (v instanceof IntVar iv) {
          add(iv, new Term(index, MONOTONE, 0, m.freeDirections(v)));
        } else {
          blocked.add(v);
        }
      }
    } else {
      blocked.addAll(c.arguments());
    }
  }

  private void add(IntVar v, Term t) {
    Map<Integer, Term> m = terms.get(v);
    if (m != null) {
      // a variable a constraint reads twice is ruled out rather than merged
      if (m.put(t.constraint(), t) != null) {
        blocked.add(v);
      }
    }
  }

  /**
   * Finds the dominated pairs and imposes their clauses.
   *
   * @param context the derivation.
   * @param limit the most clauses to impose.
   */
  void apply(Rule.Context context, int limit) {
    List<IntVar[]> found = new ArrayList<>();
    Map<IntVar, Integer> dominating = new IdentityHashMap<>();
    search:
    for (IntVar x : vars) {
      // x dominates only variables of every constraint that forbids x to increase
      Constraint shortest = null;
      for (Term t : terms.get(x).values()) {
        if (t.kind() == MONOTONE && t.locksUp()) {
          continue search;
        }
        Constraint c = live.get(t.constraint());
        if (t.locksUp()
            && (shortest == null || c.arguments().size() < shortest.arguments().size())) {
          shortest = c;
        }
      }
      if (shortest == null) {
        // the dual reductions fix a variable nothing locks upwards
        continue;
      }
      for (Var v : shortest.arguments()) {
        if (v != x && v instanceof IntVar y && terms.containsKey(y) && dominates(x, y)) {
          found.add(new IntVar[] {x, y});
          dominating.merge(x, 1, Integer::sum);
        }
        if (work > BUDGET) {
          break search;
        }
      }
    }
    pairs = found.size();
    // a variable that dominates more comes later, so more of its pairs are kept
    List<IntVar> sorted = new ArrayList<>(vars);
    sorted.sort(Comparator.comparingInt(v -> dominating.getOrDefault(v, 0)));
    Map<IntVar, Integer> pos = new IdentityHashMap<>();
    for (IntVar v : sorted) {
      pos.put(v, pos.size());
    }
    for (IntVar[] p : found) {
      if (imposed >= limit) {
        break;
      }
      IntVar x = p[0];
      IntVar y = p[1];
      if (pos.get(x) > pos.get(y)) {
        context.impose(clause(x, y));
        imposed++;
      }
    }
  }

  private static Constraint clause(IntVar x, IntVar y) {
    if (x.min() == 0 && x.max() == 1 && y.min() == 0 && y.max() == 1) {
      return new XlteqY(y, x);
    }
    return new Or(new PrimitiveConstraint[] {new XgteqC(x, x.max()), new XlteqC(y, y.min())});
  }

  /** True if x moving up and y moving down keeps every constraint, read as in the class comment. */
  private boolean dominates(IntVar x, IntVar y) {
    Map<Integer, Term> tx = terms.get(x);
    Map<Integer, Term> ty = terms.get(y);
    work += tx.size() + ty.size();
    for (Term a : tx.values()) {
      Term b = ty.get(a.constraint());
      if (!fits(a, b)) {
        return false;
      }
    }
    for (Term b : ty.values()) {
      if (!tx.containsKey(b.constraint()) && !fits(null, b)) {
        return false;
      }
    }
    return true;
  }

  /** Whether a constraint keeps its solutions when x (term a) goes up and y (term b) down. */
  private static boolean fits(Term a, Term b) {
    Term t = a != null ? a : b;
    return switch (t.kind()) {
      case LE -> (a == null ? 0 : a.weight()) <= (b == null ? 0 : b.weight());
      case EQ -> a != null && b != null && a.weight() == b.weight();
      default ->
          (a == null || (a.free() & Monotone.INCREASE) != 0)
              && (b == null || (b.free() & Monotone.DECREASE) != 0);
    };
  }

  /**
   * Returns the number of dominated pairs found.
   *
   * @return the number.
   */
  int pairs() {
    return pairs;
  }

  /**
   * Returns the number of clauses imposed.
   *
   * @return the number.
   */
  int imposed() {
    return imposed;
  }
}
