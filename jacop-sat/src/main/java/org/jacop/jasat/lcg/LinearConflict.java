/*
 * LinearConflict.java
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

import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.function.IntFunction;
import java.util.function.IntUnaryOperator;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearBool;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Linearizations;
import org.jacop.constraints.SumWeight;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.ConflictRows;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.LinearReasons;

/**
 * Cut-based conflict analysis over the atomic trail (IntSat, Pumpkin's lazy linear generation): a
 * failure of a linear constraint is combined with the linear constraints that propagated the bounds
 * it fails on, latest first, each time eliminating the variable of that bound, until the sum is
 * asserting: it fails on the current bounds but not without the latest bound it uses, and that
 * bound is the only one it uses from the current level. The result is a linear inequality implied
 * by the model, which may propagate more than the learnt clause.
 *
 * <p>Combinations are exact (the eliminated coefficients are made opposite by integer multipliers)
 * and each result is divided by the gcd of its coefficients, rounding the right-hand side down. A
 * reason that is stronger than its linear relation on the bounds (rounding, holes, domain
 * propagation) can give a combination that no longer fails, and then the analysis gives up.
 */
final class LinearConflict {

  // magnitudes kept below 2^40, so that a coefficient times a 32-bit bound fits in a long
  private static final long LIMIT = 1L << 40;

  private final AtomicTrail trail;

  // the current sum: sum coef[id] * x[id] <= rhs over the ids in terms[0..size)
  private long[] coef = new long[0];
  private IntVar[] var = new IntVar[0];
  private int[] terms = new int[16];
  private int size;
  private long rhs;

  // the reason being added
  private long[] rCoef = new long[0];
  private int[] rTerms = new int[16];
  private int rSize;
  private long rRhs;

  private final int maxSteps = Integer.getInteger("jacop.lcg.linearSteps", 64);
  private final int maxTerms = Integer.getInteger("jacop.lcg.linearTerms", 200);

  /** Outcomes of the analyses, by name. */
  final Map<String, Long> outcomes = new TreeMap<>();

  /** Sizes of the learnt sums and steps taken, summed over asserting analyses. */
  long learntTerms;

  long learntSteps;

  private static final String[] SOURCES = {
    "decision", "unit", "binary", "learnt", "clause", "external", "none"
  };

  // for an entry recorded outside propagation: how the solver literal applied got its value
  private final IntUnaryOperator source;

  // for an entry recorded outside propagation: the constraint that explained its solver literal
  // earlier, or null
  private final IntFunction<Constraint> origin;

  // the rows of the constraints that formOf does not read: clauses and fixed and/or as linear
  // relations (LinearForms), big-M rows of reified sums, and/or, max/min, |x|, products
  // (Linearizations), made once on the root bounds, where they hold for the whole search
  private final Map<Constraint, List<LinearForm>> relaxations = new IdentityHashMap<>();

  // the saved sum, while a reason is tried
  private int[] savedTerms = new int[16];
  private long[] savedCoef = new long[16];
  private int savedSize;
  private long savedRhs;

  LinearConflict(
      AtomicTrail trail, Store store, IntUnaryOperator source, IntFunction<Constraint> origin) {
    this.trail = trail;
    this.source = source;
    this.origin = origin;
    if (store != null && !"false".equals(System.getProperty("jacop.lcg.linearRows"))) {
      for (Constraint c : store.getConstraints()) {
        if (formOf(c) == null && !(c instanceof LinearReasons)) {
          LinearForm f = LinearForms.of(c);
          List<LinearForm> rows;
          if (f != null && f.relation() != LinearForm.NE) {
            rows = List.of(f);
          } else if (c instanceof ConflictRows r) {
            rows = r.conflictRows();
          } else {
            rows = Linearizations.of(c);
          }
          if (!rows.isEmpty()) {
            relaxations.put(c, rows);
          }
        }
      }
    }
  }

  /**
   * Returns the inequalities a constraint gives for an analysis: its linear relation, the rows made
   * at the root for a constraint that is not one, or for an LP relaxation the form that failed (x
   * null) or the forms that pruned x.
   */
  private List<LinearForm> candidates(Constraint c, IntVar x) {
    if (c instanceof LinearReasons lr) {
      if (x == null) {
        LinearForm f = lr.failureForm();
        return f == null ? List.of() : List.of(f);
      }
      return lr.reasonForms(x);
    }
    LinearForm f = formOf(c);
    if (f != null) {
      return f.relation() == LinearForm.NE ? List.of() : List.of(f);
    }
    List<LinearForm> rows = relaxations.get(c);
    return rows == null ? List.of() : rows;
  }

  private void save() {
    if (savedTerms.length < size) {
      savedTerms = new int[2 * size];
      savedCoef = new long[2 * size];
    }
    for (int k = 0; k < size; k++) {
      savedTerms[k] = terms[k];
      savedCoef[k] = coef[terms[k]];
    }
    savedSize = size;
    savedRhs = rhs;
  }

  private void restore() {
    clear();
    if (terms.length < savedSize) {
      terms = Arrays.copyOf(terms, savedTerms.length);
    }
    for (int k = 0; k < savedSize; k++) {
      terms[k] = savedTerms[k];
      coef[savedTerms[k]] = savedCoef[k];
    }
    size = savedSize;
    rhs = savedRhs;
  }

  private void count(String outcome) {
    outcomes.merge(outcome, 1L, Long::sum);
  }

  /**
   * Returns whether a constraint may have a linear relation ({@link #formOf}).
   *
   * @param c the constraint, or null
   * @return true for the classes formOf reads
   */
  static boolean isLinear(Constraint c) {
    return c instanceof LinearInt
        || c instanceof LinearExplainable
        || c instanceof LinearBool
        || c instanceof SumWeight;
  }

  /**
   * Returns whether an analysis can use a constraint as a reason.
   *
   * @param c the constraint, or null
   * @return true when it has a linear relation, root rows or LP forms
   */
  boolean usable(Constraint c) {
    return isLinear(c) || c instanceof LinearReasons || c != null && relaxations.containsKey(c);
  }

  /**
   * Returns the linear relation of a constraint, or null.
   *
   * @param c the constraint
   * @return its linear form
   */
  static LinearForm formOf(Constraint c) {
    if (c instanceof LinearInt li) {
      return li.linearForm();
    }
    if (c instanceof LinearExplainable le) {
      return le.linearForm();
    }
    if (c instanceof LinearBool lb) {
      return lb.linearForm();
    }
    if (c instanceof SumWeight sw) {
      return sw.linearForm();
    }
    return null;
  }

  /**
   * Analyses the failure of a constraint at the current store level.
   *
   * @param failed the constraint that failed
   * @param level the store level of the failure
   * @return the learnt sum, as {@code sum <= c}, or null when the analysis gave up
   */
  LinearForm analyse(Constraint failed, int level) {
    count("calls");
    try {
      return analyseFailure(failed, level);
    } catch (ArithmeticException overflow) {
      count("overflow");
      return null;
    }
  }

  private LinearForm analyseFailure(Constraint failed, int level) {
    List<LinearForm> starts = failed == null ? List.of() : candidates(failed, null);
    if (starts.isEmpty()) {
      count("start-nonlinear:" + (failed == null ? "none" : failed.getClass().getSimpleName()));
      return null;
    }
    int now = trail.size();
    // the first relation, and side of it, that fails on the current bounds
    boolean started = false;
    for (LinearForm f : starts) {
      clear();
      if (f.relation() != LinearForm.GE && load(f, false) && slack(now) < 0) {
        started = true;
        break;
      }
      clear();
      if (f.relation() != LinearForm.LE && load(f, true) && slack(now) < 0) {
        started = true;
        break;
      }
    }
    if (!started) {
      clear();
      count("start-not-failing");
      return null;
    }
    boolean modelStart = formOf(failed) != null;
    if (!modelStart && !(failed instanceof LinearReasons)) {
      count("start-row");
    }
    for (int step = 0; ; step++) {
      // the latest entry giving a bound the sum uses, and the level of the latest other one
      int latest = -1;
      int otherLevel = -1;
      for (int k = 0; k < size; k++) {
        int e = boundEntry(terms[k], now);
        if (e > latest) {
          if (latest >= 0) {
            otherLevel = Math.max(otherLevel, trail.level(latest));
          }
          latest = e;
        } else if (e >= 0) {
          otherLevel = Math.max(otherLevel, trail.level(e));
        }
      }
      if (latest < 0) {
        count("root-failure");
        return null;
      }
      if (trail.level(latest) < level
          || (otherLevel < level && trail.level(latest) == level && slack(latest) >= 0)) {
        if (step == 0 && (modelStart || size > maxTerms)) {
          // the failing constraint itself, already in the model, or a row or LP form too long
          count(modelStart ? "asserting-at-start" : "too-many-terms:start");
          return null;
        }
        count(step == 0 ? "asserting-row" : "asserting");
        learntTerms += size;
        learntSteps += step;
        return result();
      }
      if (step == maxSteps) {
        count("too-many-steps");
        return null;
      }
      Constraint r = trail.reason(latest);
      boolean guessed = false;
      if (r == null && origin != null) {
        // a solver literal applied: the constraint whose explanation of that literal the solver
        // keeps as a clause, if any. Any constraint of the model gives a valid combination; one
        // that does not imply the bound gives up below, as the combination then does not fail
        r = origin.apply(latest);
        guessed = r != null;
      }
      if (r == null) {
        count(
            "stop-"
                + (trail.level(latest) == level ? "current-" : "earlier-")
                + SOURCES[source.applyAsInt(latest)]);
        return null;
      }
      List<LinearForm> reasons = candidates(r, trail.variable(latest));
      if (reasons.isEmpty()) {
        count("stop-nonlinear:" + r.getClass().getSimpleName());
        return null;
      }
      int x = trail.id(trail.variable(latest));
      long a = coef[x];
      // the first relation whose side bounding x in the direction the sum uses gives a sum that
      // still fails on the bounds before the entry: the trail is undone up to it
      String why = "stop-wrong-side:";
      boolean combined = false;
      save();
      for (LinearForm rf : reasons) {
        if (!loadReason(rf, x, a)) {
          continue;
        }
        if (!combine(x, a)) {
          why = "overflow:";
        } else if (size > maxTerms) {
          why = "too-many-terms:";
        } else if (size == 0) {
          why = "cancelled:";
        } else if (slack(latest) >= 0) {
          why = guessed ? "not-failing-kept:" : "not-failing:";
        } else {
          combined = true;
          break;
        }
        restore();
      }
      if (!combined) {
        restore();
        count(why + r.getClass().getSimpleName());
        return null;
      }
      now = latest;
      if (guessed) {
        count("kept-origin");
      }
      if (formOf(r) == null && !(r instanceof LinearReasons)) {
        count("row-reason");
      } else if (r instanceof LinearReasons) {
        count("lp-reason");
      }
    }
  }

  // the entry giving the bound of the variable the sum uses (its lower bound for a positive
  // coefficient), the earliest one that gives that bound; -1 when the root domain gives it
  private int boundEntry(int id, int position) {
    IntVar x = var[id];
    if (coef[id] > 0) {
      return trail.earliestLowerBound(x, trail.minBefore(x, position), position);
    }
    return trail.earliestUpperBound(x, trail.maxBefore(x, position), position);
  }

  // rhs minus the smallest value of the sum on the bounds just before a trail position
  private long slack(int position) {
    long s = rhs;
    for (int k = 0; k < size; k++) {
      int id = terms[k];
      IntVar x = var[id];
      long a = coef[id];
      s =
          Math.subtractExact(
              s,
              Math.multiplyExact(
                  a, a > 0 ? trail.minBefore(x, position) : trail.maxBefore(x, position)));
    }
    return s;
  }

  private void clear() {
    for (int k = 0; k < size; k++) {
      coef[terms[k]] = 0;
    }
    size = 0;
    rhs = 0;
  }

  private void grow(int id) {
    if (id >= coef.length) {
      int n = Math.max(id + 1, 2 * coef.length);
      coef = Arrays.copyOf(coef, n);
      var = Arrays.copyOf(var, n);
      rCoef = Arrays.copyOf(rCoef, n);
    }
  }

  // the form as sum <= c (negated when ge, the >= side): false on a magnitude over LIMIT
  private boolean load(LinearForm f, boolean ge) {
    long sign = ge ? -1 : 1;
    IntVar[] xs = f.vars();
    long[] ws = f.weights();
    if (Math.abs(f.c()) >= LIMIT) {
      return false;
    }
    rhs = sign * f.c();
    for (int i = 0; i < xs.length; i++) {
      if (ws[i] == 0) {
        continue;
      }
      if (Math.abs(ws[i]) >= LIMIT) {
        clear();
        return false;
      }
      int id = trail.id(xs[i]);
      grow(id);
      var[id] = xs[i];
      if (coef[id] == 0) {
        if (size == terms.length) {
          terms = Arrays.copyOf(terms, 2 * size);
        }
        terms[size++] = id;
      }
      coef[id] += sign * ws[i];
    }
    compact();
    return true;
  }

  // drops the terms whose coefficients cancelled
  private void compact() {
    int n = 0;
    for (int k = 0; k < size; k++) {
      if (coef[terms[k]] != 0) {
        terms[n++] = terms[k];
      }
    }
    size = n;
  }

  // the side of rf, as sum <= c, whose coefficient of x has the sign opposite to a
  private boolean loadReason(LinearForm rf, int x, long a) {
    for (int k = 0; k < rSize; k++) {
      rCoef[rTerms[k]] = 0;
    }
    rSize = 0;
    long w = 0;
    IntVar[] xs = rf.vars();
    long[] ws = rf.weights();
    for (int i = 0; i < xs.length; i++) {
      if (trail.id(xs[i]) == x) {
        w += ws[i];
      }
    }
    if (w == 0) {
      return false;
    }
    // as sum <= c the coefficient is w; as the >= side, negated, -w
    boolean ge;
    if (Long.signum(w) != Long.signum(a)) {
      ge = false;
      if (rf.relation() == LinearForm.GE) {
        return false;
      }
    } else {
      ge = true;
      if (rf.relation() == LinearForm.LE) {
        return false;
      }
    }
    long sign = ge ? -1 : 1;
    if (Math.abs(rf.c()) >= LIMIT) {
      return false;
    }
    rRhs = sign * rf.c();
    for (int i = 0; i < xs.length; i++) {
      if (ws[i] == 0) {
        continue;
      }
      if (Math.abs(ws[i]) >= LIMIT) {
        return false;
      }
      int id = trail.id(xs[i]);
      grow(id);
      var[id] = xs[i];
      if (rCoef[id] == 0) {
        if (rSize == rTerms.length) {
          rTerms = Arrays.copyOf(rTerms, 2 * rSize);
        }
        rTerms[rSize++] = id;
      }
      rCoef[id] += sign * ws[i];
    }
    return true;
  }

  // sum := m * sum + n * reason with x cancelled, divided by the gcd of the coefficients
  private boolean combine(int x, long a) {
    long b = rCoef[x];
    long g = gcd(Math.abs(a), Math.abs(b));
    long m = Math.abs(b) / g;
    long n = Math.abs(a) / g;
    try {
      for (int k = 0; k < size; k++) {
        int id = terms[k];
        coef[id] = Math.multiplyExact(coef[id], m);
      }
      rhs = Math.addExact(Math.multiplyExact(rhs, m), Math.multiplyExact(rRhs, n));
      for (int k = 0; k < rSize; k++) {
        int id = rTerms[k];
        if (rCoef[id] == 0) {
          continue;
        }
        if (coef[id] == 0) {
          if (size == terms.length) {
            terms = Arrays.copyOf(terms, 2 * size);
          }
          terms[size++] = id;
        }
        coef[id] = Math.addExact(coef[id], Math.multiplyExact(rCoef[id], n));
      }
    } catch (ArithmeticException overflow) {
      clear();
      return false;
    }
    coef[x] = 0;
    compact();
    long d = 0;
    for (int k = 0; k < size; k++) {
      d = gcd(d, Math.abs(coef[terms[k]]));
    }
    if (d > 1) {
      for (int k = 0; k < size; k++) {
        coef[terms[k]] /= d;
      }
      rhs = Math.floorDiv(rhs, d);
    }
    if (Math.abs(rhs) >= LIMIT) {
      clear();
      return false;
    }
    for (int k = 0; k < size; k++) {
      if (Math.abs(coef[terms[k]]) >= LIMIT) {
        clear();
        return false;
      }
    }
    return true;
  }

  private static long gcd(long p, long q) {
    while (q != 0) {
      long t = p % q;
      p = q;
      q = t;
    }
    return p;
  }

  private LinearForm result() {
    IntVar[] xs = new IntVar[size];
    long[] ws = new long[size];
    for (int k = 0; k < size; k++) {
      xs[k] = var[terms[k]];
      ws[k] = coef[terms[k]];
    }
    return new LinearForm(xs, ws, rhs, LinearForm.LE);
  }
}
