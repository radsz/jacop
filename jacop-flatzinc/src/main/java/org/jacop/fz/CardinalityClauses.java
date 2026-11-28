/*
 * CardinalityClauses.java
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

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.LinearForm;

/**
 * A cardinality row over 0/1 variables, sum of literals at most, at least or equal to a constant,
 * as clauses of the sequential counter of C. Sinz, "Towards an optimal CNF encoding of Boolean
 * cardinality constraints", CP 2005: the auxiliary variable s(i, j) says that at least j of the
 * first i + 1 literals are true. A model of clauses and such rows goes to JaSAT whole: the
 * peaceable armies of queens of the Pseudo-Boolean Competition 2016 (army10, army13: clauses and
 * two rows "at least 24 of 169") had no solution in 120 s under lazy clause generation; with the
 * counters JaSAT finds one in 3 s.
 */
final class CardinalityClauses {

  /**
   * The most auxiliary variables of the counters of a model, system property
   * org.jacop.fz.cardinalityClauses (default 100,000; 0 takes no cardinality row as clauses).
   */
  static final long MAX_AUXILIARIES = Long.getLong("org.jacop.fz.cardinalityClauses", 100_000);

  // the variables of the literals, and whether each literal is the variable or its negation
  private final IntVar[] vars;
  private final boolean[] positive;
  // the bounds of the sum of the literals and of the sum of their negations, -1 when none
  private final int atMost;
  private final int atMostNegated;

  private CardinalityClauses(IntVar[] vars, boolean[] positive, int atMost, int atMostNegated) {
    this.vars = vars;
    this.positive = positive;
    this.atMost = atMost;
    this.atMostNegated = atMostNegated;
  }

  /**
   * Returns the row of c as a cardinality row, or null when c is no linear constraint over distinct
   * 0/1 variables with weights 1 and -1 (and fixed variables), or its bound is out of reach (then
   * it fails, which the solver finds without the clauses). A row that every assignment meets has no
   * clauses.
   *
   * @param c the constraint
   * @return the cardinality row, or null
   */
  static CardinalityClauses of(Constraint c) {
    return MAX_AUXILIARIES <= 0 ? null : of(LinearForms.of(c));
  }

  /**
   * Returns the linear relation f as a cardinality row, or null, as {@link #of(Constraint)}.
   *
   * @param f the linear relation, or null
   * @return the cardinality row, or null
   */
  static CardinalityClauses of(LinearForm f) {
    if (MAX_AUXILIARIES <= 0 || f == null || f.relation() == LinearForm.NE) {
      return null;
    }
    List<IntVar> vars = new ArrayList<>();
    List<Boolean> signs = new ArrayList<>();
    // sum w x REL rest, as the sum of the literals (x for w = 1, 1 - x for w = -1) REL bound
    long bound = f.c();
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    IntVar[] xs = f.vars();
    long[] ws = f.weights();
    for (int i = 0; i < xs.length; i++) {
      if (xs[i].singleton()) {
        bound -= ws[i] * xs[i].value();
      } else if (Math.abs(ws[i]) != 1 || xs[i].min() != 0 || xs[i].max() != 1 || !seen.add(xs[i])) {
        return null;
      } else {
        vars.add(xs[i]);
        signs.add(ws[i] == 1);
        bound += ws[i] == 1 ? 0 : 1;
      }
    }
    int n = vars.size();
    boolean[] positive = new boolean[n];
    for (int i = 0; i < n; i++) {
      positive[i] = signs.get(i);
    }
    // LE: literals <= bound; GE: literals >= bound, negated literals <= n - bound; EQ: both
    int le = f.relation() == LinearForm.GE ? -1 : clamp(bound, n);
    int ge = f.relation() == LinearForm.LE ? -1 : clamp(n - bound, n);
    if (le == -2 || ge == -2) {
      return null;
    }
    return new CardinalityClauses(vars.toArray(new IntVar[0]), positive, le, ge);
  }

  // k as a bound of a sum of n literals: -2 when no assignment meets it, n when every one does
  private static int clamp(long k, int n) {
    if (k < 0) {
      return -2;
    }
    return (int) Math.min(k, n);
  }

  /**
   * Returns the auxiliary variables of the counters.
   *
   * @return the number of auxiliary variables
   */
  long auxiliaries() {
    return counterSize(atMost) + counterSize(atMostNegated);
  }

  private long counterSize(int k) {
    return k <= 0 || k >= vars.length ? 0 : (long) (vars.length - 1) * k;
  }

  /**
   * Adds the clauses of the counters, each as its positive and its negative variables, with new 0/1
   * variables of the store.
   *
   * @param store the store of the new variables
   * @param out the clauses
   */
  void encode(Store store, List<IntVar[][]> out) {
    counter(store, atMost, false, out);
    counter(store, atMostNegated, true, out);
  }

  // sum of the literals (negated when negated) <= k; k -1 is no form, k >= n holds always
  private void counter(Store store, int k, boolean negated, List<IntVar[][]> out) {
    int n = vars.length;
    if (k < 0 || k >= n) {
      return;
    }
    if (k == 0) {
      for (int i = 0; i < n; i++) {
        out.add(clause(i, negated, null, null));
      }
      return;
    }
    // s[i][j]: at least j + 1 of the literals 0..i are true, for i < n - 1
    IntVar[][] s = new IntVar[n - 1][k];
    for (int i = 0; i < n - 1; i++) {
      for (int j = 0; j < k; j++) {
        s[i][j] = new IntVar(store, 0, 1);
      }
    }
    out.add(clause(0, negated, s[0][0], null));
    for (int j = 1; j < k; j++) {
      out.add(new IntVar[][] {{}, {s[0][j]}});
    }
    for (int i = 1; i < n - 1; i++) {
      out.add(clause(i, negated, s[i][0], null));
      out.add(new IntVar[][] {{s[i][0]}, {s[i - 1][0]}});
      for (int j = 1; j < k; j++) {
        out.add(clause(i, negated, s[i][j], s[i - 1][j - 1]));
        out.add(new IntVar[][] {{s[i][j]}, {s[i - 1][j]}});
      }
      out.add(clause(i, negated, null, s[i - 1][k - 1]));
    }
    out.add(clause(n - 1, negated, null, s[n - 2][k - 1]));
  }

  // the clause: not literal i, or then, or not not (then and not may be null)
  private IntVar[][] clause(int i, boolean negated, IntVar then, IntVar not) {
    // not literal i: the literal is x when positive[i] differs from negated, and 1 - x otherwise
    boolean literalIsVariable = positive[i] != negated;
    List<IntVar> pos = new ArrayList<>(2);
    List<IntVar> neg = new ArrayList<>(2);
    if (literalIsVariable) {
      neg.add(vars[i]);
    } else {
      pos.add(vars[i]);
    }
    if (then != null) {
      pos.add(then);
    }
    if (not != null) {
      neg.add(not);
    }
    return new IntVar[][] {pos.toArray(new IntVar[0]), neg.toArray(new IntVar[0])};
  }
}
