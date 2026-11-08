/*
 * ClauseEncoder.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * Notwithstanding any other provisions of this License, the copyright
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

package org.jacop.jasat.lcg;

import java.util.ArrayList;
import java.util.List;
import java.util.function.BooleanSupplier;
import org.jacop.constraints.AbstractReifiedConstraint;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Implies;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;

/**
 * Writes small constraints as clauses of the LCG solver, in place of their propagators. It reads
 * the pseudo-Boolean encoding each constraint gives for proofs ({@link PbEncodable}, linear forms,
 * reifications), and turns its lines into clauses: a clause stays a clause, a linear relation over
 * few terms becomes its order encoding (Tamura et al., "Compiling finite linear CSP into SAT",
 * Constraints 14(2), 2009) with the direct encoding of two-variable equalities and of
 * disequalities, and a sum of 0/1 terms with unit weights a sequential counter (Sinz, "Towards an
 * optimal CNF encoding of Boolean cardinality constraints", CP 2005). Unit propagation over the
 * clauses prunes at least the bounds the propagator prunes. A constraint whose encoding needs a
 * line it cannot write, or more clauses than the limit, keeps its propagator.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class ClauseEncoder implements PbModel {

  /** Thrown when a line cannot become clauses within the limit. */
  private static final class Rejected extends RuntimeException {
    private static final long serialVersionUID = 1L;

    Rejected() {
      super(null, null, false, false);
    }
  }

  private static final Rejected REJECTED = new Rejected();

  /** What the encoder needs of the solver. */
  interface Literals {
    /** [x >= v] for v in (root min, root max]. */
    int atLeast(IntVar x, int v);

    /** [x = v] for v in the root domain of a variable with more than two values. */
    int equal(IntVar x, int v);

    /** A new solver variable that is no atom. */
    int auxiliary();

    /** The root domain of x. */
    IntDomain root(IntVar x);
  }

  private final Literals lits;
  private final int limit;
  private final List<int[]> clauses = new ArrayList<>();
  private final List<String> guard = new ArrayList<>();

  /**
   * @param lits the literals of the solver
   * @param limit the most clauses of one constraint
   */
  ClauseEncoder(Literals lits, int limit) {
    this.lits = lits;
    this.limit = limit;
  }

  /**
   * Encodes a constraint.
   *
   * @param c the constraint
   * @return its clauses, or null when it keeps its propagator
   */
  List<int[]> encode(Constraint c) {
    clauses.clear();
    guard.clear();
    try {
      if (!dispatch(c)) {
        return null;
      }
    } catch (Rejected | IllegalStateException | IllegalArgumentException _) {
      return null;
    }
    return new ArrayList<>(clauses);
  }

  private boolean dispatch(Constraint c) {
    if (c instanceof PbEncodable p && p.encode(this)) {
      return true;
    }
    LinearForm f = OpbEncoder.form(c);
    if (f != null) {
      linear(f);
      return true;
    }
    if (c instanceof AbstractReifiedConstraint r
        && (r.getClass() == Reified.class || r.getClass() == Implies.class)) {
      IntDomain d = lits.root(r.b);
      if (d.min() < 0 || d.max() > 1) {
        return false;
      }
      LinearForm inner = OpbEncoder.form(r.c);
      if (inner != null) {
        reified(r.b, inner, r instanceof Reified);
        return true;
      }
      String lit = equalTo(r.b, 1);
      return implied(lit, r.c, false)
          && (!(r instanceof Reified) || implied(PbModel.not(lit), r.c, true));
    }
    if (c instanceof Not n && n.getClass() == Not.class) {
      return implied("1", n.negatedConstraint(), true);
    }
    return false;
  }

  private boolean implied(String lit, PrimitiveConstraint c, boolean negated) {
    if (c instanceof Not n && n.getClass() == Not.class) {
      return implied(lit, n.negatedConstraint(), !negated);
    }
    LinearForm f = OpbEncoder.form(c);
    if (f != null) {
      guarded(lit, negated ? f.negated() : f);
      return true;
    }
    return c instanceof PbEncodable p && p.encodeImplied(this, lit, negated);
  }

  // ---------------------------------------------------------------- literals

  private static String name(int lit) {
    return lit > 0 ? "x" + lit : "~x" + -lit;
  }

  private static int parse(String name) {
    return name.charAt(0) == '~'
        ? -Integer.parseInt(name, 2, name.length(), 10)
        : Integer.parseInt(name, 1, name.length(), 10);
  }

  private static boolean binary(IntDomain d) {
    return d.getSize() <= 2;
  }

  @Override
  public IntDomain domain(IntVar x) {
    return lits.root(x);
  }

  @Override
  public String equalTo(IntVar x, int v) {
    IntDomain d = lits.root(x);
    if (!d.contains(v)) {
      return "0";
    }
    if (d.singleton()) {
      return "1";
    }
    if (binary(d)) {
      // a variable of two values: [x = max] is [x >= max]
      String ge = name(lits.atLeast(x, d.max()));
      return v == d.max() ? ge : PbModel.not(ge);
    }
    return name(lits.equal(x, v));
  }

  @Override
  public String atLeast(IntVar x, int v) {
    IntDomain d = lits.root(x);
    if (v <= d.min()) {
      return "1";
    }
    if (v > d.max()) {
      return "0";
    }
    return name(lits.atLeast(x, v));
  }

  @Override
  public String auxiliary() {
    return name(lits.auxiliary());
  }

  // ---------------------------------------------------------------- clauses

  @Override
  public void clause(String... literals) {
    int[] c = new int[literals.length + guard.size()];
    int n = 0;
    for (String g : guard) {
      if ("1".equals(g)) {
        continue;
      }
      if ("0".equals(g)) {
        return;
      }
      c[n++] = -parse(g);
    }
    for (String l : literals) {
      if ("1".equals(l)) {
        return;
      }
      if (!"0".equals(l)) {
        c[n++] = parse(l);
      }
    }
    if (clauses.size() >= limit) {
      throw REJECTED;
    }
    clauses.add(java.util.Arrays.copyOf(c, n));
  }

  @Override
  public void clause(IntVar[] positive, IntVar[] negative) {
    String[] c = new String[positive.length + negative.length];
    int k = 0;
    for (IntVar x : positive) {
      c[k++] = equalTo(x, 1);
    }
    for (IntVar x : negative) {
      c[k++] = PbModel.not(equalTo(x, 1));
    }
    clause(c);
  }

  @Override
  public boolean implied(String literal, BooleanSupplier encoding) {
    if ("0".equals(literal)) {
      return true;
    }
    if ("1".equals(literal)) {
      return encoding.getAsBoolean();
    }
    guard.add(literal);
    try {
      return encoding.getAsBoolean();
    } finally {
      guard.remove(guard.size() - 1);
    }
  }

  @Override
  public void guarded(String literal, LinearForm form) {
    if ("0".equals(literal)) {
      return;
    }
    guard.add(literal);
    try {
      linear(form);
    } finally {
      guard.remove(guard.size() - 1);
    }
  }

  @Override
  public void reified(IntVar b, LinearForm form, boolean equivalence) {
    String lit = equalTo(b, 1);
    guarded(lit, form);
    if (equivalence) {
      guarded(PbModel.not(lit), form.negated());
    }
  }

  // ---------------------------------------------------------------- linear relations

  /** A term of a linear relation: an integer variable or a literal, with its values. */
  private final class Term {
    final IntVar x; // null for a literal
    final String lit;
    final int[] values;

    Term(IntVar x) {
      this.x = x;
      this.lit = null;
      IntDomain d = lits.root(x);
      values = new int[d.getSize()];
      int k = 0;
      for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
        values[k++] = e.nextElement();
      }
    }

    Term(String lit) {
      this.x = null;
      this.lit = lit;
      values = new int[] {0, 1};
    }

    int min() {
      return values[0];
    }

    int max() {
      return values[values.length - 1];
    }

    String ge(long v) {
      if (v <= min()) {
        return "1";
      }
      if (v > max()) {
        return "0";
      }
      return x == null ? lit : atLeast(x, (int) v);
    }

    String eq(long v) {
      if (v < min() || v > max()) {
        return "0";
      }
      if (x == null) {
        return v == 1 ? lit : PbModel.not(lit);
      }
      return equalTo(x, (int) v);
    }
  }

  @Override
  public void linear(LinearForm f) {
    List<Term> t = new ArrayList<>();
    List<Long> w = new ArrayList<>();
    long c = f.c();
    for (int i = 0; i < f.vars().length; i++) {
      IntDomain d = lits.root(f.vars()[i]);
      if (f.weights()[i] == 0) {
        continue;
      }
      if (d.singleton()) {
        c -= f.weights()[i] * d.min();
      } else {
        t.add(new Term(f.vars()[i]));
        w.add(f.weights()[i]);
      }
    }
    relation(t, w, f.relation(), c);
  }

  @Override
  public void sum(String[] literals, long[] a, IntVar[] x, long[] wx, int relation, long c) {
    List<Term> t = new ArrayList<>();
    List<Long> w = new ArrayList<>();
    for (int k = 0; k < literals.length; k++) {
      if (a[k] == 0 || "0".equals(literals[k])) {
        continue;
      }
      if ("1".equals(literals[k])) {
        c -= a[k];
      } else {
        t.add(new Term(literals[k]));
        w.add(a[k]);
      }
    }
    for (int k = 0; k < x.length; k++) {
      IntDomain d = lits.root(x[k]);
      if (wx[k] == 0) {
        continue;
      }
      if (d.singleton()) {
        c -= wx[k] * d.min();
      } else {
        t.add(new Term(x[k]));
        w.add(wx[k]);
      }
    }
    relation(t, w, relation, c);
  }

  private void relation(List<Term> t, List<Long> w, int relation, long c) {
    Term[] terms = t.toArray(new Term[0]);
    long[] ws = new long[w.size()];
    for (int i = 0; i < ws.length; i++) {
      ws[i] = w.get(i);
    }
    switch (relation) {
      case LinearForm.LE -> le(terms, ws, c);
      case LinearForm.GE -> le(terms, negate(ws), -c);
      case LinearForm.EQ -> {
        le(terms, ws, c);
        le(terms, negate(ws), -c);
        if (terms.length == 2) {
          direct(terms, ws, c);
        }
      }
      case LinearForm.NE -> ne(terms, ws, c);
      default -> throw REJECTED;
    }
  }

  private static long[] negate(long[] w) {
    long[] n = new long[w.length];
    for (int i = 0; i < w.length; i++) {
      n[i] = -w[i];
    }
    return n;
  }

  /** The order encoding of sum w[i] * t[i] <= c, or a sequential counter for 0/1 unit sums. */
  private void le(Term[] t, long[] w, long c) {
    int n = t.length;
    if (n == 0) {
      if (c < 0) {
        clause();
      }
      return;
    }
    // the last term is the one with the most values; the clauses enumerate the values of the others
    int last = 0;
    for (int i = 1; i < n; i++) {
      if (t[i].values.length > t[last].values.length) {
        last = i;
      }
    }
    double combos = 1;
    for (int i = 0; i < n; i++) {
      if (i != last) {
        combos *= t[i].values.length;
      }
    }
    if (combos > limit) {
      if (unitBinary(t, w)) {
        counter(t, w, c);
        return;
      }
      throw REJECTED;
    }
    Term[] order = new Term[n];
    long[] ow = new long[n];
    int k = 0;
    for (int i = 0; i < n; i++) {
      if (i != last) {
        order[k] = t[i];
        ow[k++] = w[i];
      }
    }
    order[n - 1] = t[last];
    ow[n - 1] = w[last];
    String[] assumed = new String[n];
    enumerate(order, ow, c, 0, 0, assumed);
  }

  // clauses: the first terms at their assumed bounds force the last one
  private void enumerate(Term[] t, long[] w, long c, int i, long s, String[] assumed) {
    int n = t.length;
    if (i == n - 1) {
      Term l = t[i];
      long rest = c - s;
      String force;
      if (w[i] > 0) {
        long r = Math.floorDiv(rest, w[i]);
        if (r >= l.max()) {
          return; // nothing forced
        }
        force = PbModel.not(l.ge(r + 1));
      } else {
        long r = -Math.floorDiv(rest, -w[i]); // ceil(rest / w), w < 0
        if (r <= l.min()) {
          return;
        }
        force = l.ge(r);
      }
      String[] cl = new String[n];
      for (int k = 0; k < i; k++) {
        cl[k] = PbModel.not(assumed[k]);
      }
      cl[i] = force;
      clause(cl);
      return;
    }
    Term x = t[i];
    // the least contribution of the remaining terms after this one, to skip values that force
    // nothing: with this term at value u, the clause needs s + w u + min rest > c - w_last max_last
    for (int u : x.values) {
      String a;
      long contribution;
      if (w[i] > 0) {
        a = x.ge(u); // x >= u
        contribution = w[i] * u;
      } else {
        a = PbModel.not(x.ge(u + 1L)); // x <= u
        contribution = w[i] * u;
      }
      assumed[i] = a;
      enumerate(t, w, c, i + 1, s + contribution, assumed);
    }
  }

  private static boolean unitBinary(Term[] t, long[] w) {
    for (int i = 0; i < t.length; i++) {
      if (Math.abs(w[i]) != 1 || t[i].min() != 0 || t[i].max() != 1) {
        return false;
      }
    }
    return true;
  }

  /** Sinz's sequential counter of sum w[i] * t[i] <= c over 0/1 terms with weights +-1. */
  private void counter(Term[] t, long[] w, long c) {
    int n = t.length;
    String[] l = new String[n];
    long k = c;
    for (int i = 0; i < n; i++) {
      if (w[i] > 0) {
        l[i] = t[i].ge(1);
      } else {
        // -t = (1 - t) - 1
        l[i] = PbModel.not(t[i].ge(1));
        k += 1;
      }
    }
    if (k >= n) {
      return;
    }
    if (k < 0) {
      clause();
      return;
    }
    if (k == 0) {
      for (String x : l) {
        clause(PbModel.not(x));
      }
      return;
    }
    if ((double) n * k * 2 > limit) {
      throw REJECTED;
    }
    int kk = (int) k;
    String[][] s = new String[n][kk + 1];
    for (int i = 0; i < n - 1; i++) {
      for (int j = 1; j <= kk; j++) {
        s[i][j] = auxiliary();
      }
    }
    clause(PbModel.not(l[0]), s[0][1]);
    for (int j = 2; j <= kk; j++) {
      clause(PbModel.not(s[0][j]));
    }
    for (int i = 1; i < n - 1; i++) {
      clause(PbModel.not(l[i]), s[i][1]);
      clause(PbModel.not(s[i - 1][1]), s[i][1]);
      for (int j = 2; j <= kk; j++) {
        clause(PbModel.not(l[i]), PbModel.not(s[i - 1][j - 1]), s[i][j]);
        clause(PbModel.not(s[i - 1][j]), s[i][j]);
      }
      clause(PbModel.not(l[i]), PbModel.not(s[i - 1][kk]));
    }
    clause(PbModel.not(l[n - 1]), PbModel.not(s[n - 2][kk]));
  }

  /** The direct encoding of w0 t0 + w1 t1 = c: each value of one term forces the other's. */
  private void direct(Term[] t, long[] w, long c) {
    for (int a = 0; a < 2; a++) {
      int b = 1 - a;
      if (t[a].values.length > limit) {
        throw REJECTED;
      }
      for (int u : t[a].values) {
        long rest = c - w[a] * u;
        String other = rest % w[b] == 0 ? t[b].eq(rest / w[b]) : "0";
        clause(PbModel.not(t[a].eq(u)), other);
      }
    }
  }

  /** sum w[i] t[i] != c: each assignment of all but the last term rules out one value of it. */
  private void ne(Term[] t, long[] w, long c) {
    int n = t.length;
    if (n == 0) {
      if (c == 0) {
        clause();
      }
      return;
    }
    double combos = 1;
    for (int i = 0; i < n - 1; i++) {
      combos *= t[i].values.length;
    }
    if (combos > limit) {
      throw REJECTED;
    }
    neEnumerate(t, w, c, 0, 0, new String[n]);
  }

  private void neEnumerate(Term[] t, long[] w, long c, int i, long s, String[] assumed) {
    int n = t.length;
    if (i == n - 1) {
      long rest = c - s;
      if (rest % w[i] != 0) {
        return;
      }
      String last = t[i].eq(rest / w[i]);
      if ("0".equals(last)) {
        return;
      }
      String[] cl = new String[n];
      for (int k = 0; k < i; k++) {
        cl[k] = PbModel.not(assumed[k]);
      }
      cl[i] = PbModel.not(last);
      clause(cl);
      return;
    }
    for (int u : t[i].values) {
      assumed[i] = t[i].eq(u);
      neEnumerate(t, w, c, i + 1, s + w[i] * u, assumed);
    }
  }

  // ---------------------------------------------------------------- not as clauses

  @Override
  public void allDifferent(IntVar[] x) {
    throw REJECTED;
  }

  @Override
  public void circuit(IntVar[] x, int offset) {
    throw REJECTED;
  }

  @Override
  public void cardinality(
      IntVar[] x,
      int[] values,
      IntVar[] counters,
      int[] low,
      int[] up,
      boolean closed,
      IntVar rest) {
    throw REJECTED;
  }

  @Override
  public void timetable(IntVar[] starts, int[] durations, int[] uses, IntVar limit) {
    throw REJECTED;
  }
}
