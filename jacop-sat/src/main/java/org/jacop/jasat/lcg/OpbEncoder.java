/*
 * OpbEncoder.java
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

import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.ToIntFunction;
import org.jacop.constraints.AbstractReifiedConstraint;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;

/**
 * Writes the OPB model of a store for a VeriPB proof of its LCG search ({@link VeriPbProof}). An
 * integer variable x with root domain D, min m and max M, has the order literals {@code [x >= v]}
 * for v in (m, M], named {@code x<id>g<v>}, chained by {@code [x >= v + 1] -> [x >= v]}, with
 * {@code [x >= h] -> [x >= h + 1]} for each hole h, and the value literals {@code [x = v]} for v in
 * D, named {@code x<id>e<v>}, each defined as {@code [x >= v] and not [x >= v + 1]}. These are the
 * literals of the LCG solver, which then uses the model's names. A term a x is a m plus a times
 * each order literal of x, so a linear constraint is one pseudo-Boolean constraint over them, and
 * unit propagation on it derives the bounds that its propagator and explanations derive. A
 * disequality has one more literal, telling which side of the constant the sum is on.
 *
 * <p>The constraints written are those with a {@link LinearForm} (linear ones, {@link LinearInt}
 * and its subclasses included), {@link PbEncodable} ones, and {@link Reified} and {@link Implies}
 * of a constraint with a linear form; the others are listed by {@link #unsupported}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class OpbEncoder implements PbModel {

  private final IntVar[] vars;
  private final IntDomain[] root;
  private final ToIntFunction<IntVar> id;
  private final StringBuilder constraints = new StringBuilder();
  private long numConstraints;
  private long numVariables;
  private int numAuxiliaries;
  private long numTerms;
  private final long maxTerms;
  private final Set<String> unsupported = new TreeSet<>();
  // the guard literals of the constraints being written, for reifications
  private final List<String> guard = new ArrayList<>();

  /**
   * Creates the encoder.
   *
   * @param vars the variables, by id
   * @param root their root domains
   * @param id the id of a variable
   * @param maxTerms the most terms the model may have, which bounds its size
   */
  OpbEncoder(IntVar[] vars, IntDomain[] root, ToIntFunction<IntVar> id, long maxTerms) {
    this.vars = vars;
    this.root = root;
    this.id = id;
    this.maxTerms = maxTerms;
  }

  static String ge(int i, int v) {
    return "x" + i + "g" + v;
  }

  static String eq(int i, int v) {
    return "x" + i + "e" + v;
  }

  /** Writes the literals of every variable and the constraints that define them. */
  void variables() {
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] == null || root[i].singleton()) {
        continue;
      }
      IntDomain d = root[i];
      int m = d.min();
      int max = d.max();
      grow((long) max - m);
      numVariables += 2L * (max - m) + 1;
      for (int v = m + 1; v < max; v++) {
        line("1 " + ge(i, v) + " 1 ~" + ge(i, v + 1) + " >= 1");
      }
      for (int v = m + 1; v < max; v++) {
        if (!d.contains(v)) {
          line("1 ~" + ge(i, v) + " 1 " + ge(i, v + 1) + " >= 1");
        }
      }
      for (int v = m; v <= max; v++) {
        if (!d.contains(v)) {
          numVariables--;
          continue;
        }
        String e = eq(i, v);
        if (v == m) {
          line("1 ~" + e + " 1 ~" + ge(i, v + 1) + " >= 1");
          line("1 " + e + " 1 " + ge(i, v + 1) + " >= 1");
        } else if (v == max) {
          line("1 ~" + e + " 1 " + ge(i, v) + " >= 1");
          line("1 " + e + " 1 ~" + ge(i, v) + " >= 1");
        } else {
          line("2 ~" + e + " 1 " + ge(i, v) + " 1 ~" + ge(i, v + 1) + " >= 2");
          line("1 " + e + " 1 ~" + ge(i, v) + " 1 " + ge(i, v + 1) + " >= 1");
        }
      }
    }
  }

  /**
   * Writes a constraint, or lists its class as unsupported.
   *
   * @param c the constraint
   */
  void constraint(Constraint c) {
    if (!encode(c)) {
      unsupported.add(c.getClass().getSimpleName());
    }
  }

  private boolean encode(Constraint c) {
    if (c instanceof PbEncodable p && p.encode(this)) {
      return true;
    }
    LinearForm f = form(c);
    if (f != null) {
      linear(f);
      return true;
    }
    if (c instanceof AbstractReifiedConstraint r
        && (r.getClass() == Reified.class || r.getClass() == Implies.class)) {
      LinearForm inner = form(r.c);
      if (inner == null || !isBoolean(r.b)) {
        return false;
      }
      reified(r.b, inner, r instanceof Reified);
      return true;
    }
    return false;
  }

  @Override
  public void reified(IntVar b, LinearForm f, boolean equivalence) {
    String lit = literal(b, true);
    String value = valueLiteral(f);
    if (value != null) {
      // b -> [x = v] (or its negation) on the value literal, which the bounds do not give
      implication(lit, value);
      if (equivalence) {
        implication(negate(lit), negate(value));
      }
      return;
    }
    guarded(lit, f);
    if (equivalence) {
      guarded(negate(lit), f.negated());
    }
  }

  private static LinearForm form(Constraint c) {
    if (c instanceof LinearInt l) {
      return l.linearRelation();
    }
    if (c instanceof LinearExplainable l) {
      return l.linearForm();
    }
    return null;
  }

  private void guarded(String lit, LinearForm f) {
    if ("0".equals(lit)) {
      return; // the guard is false: nothing to state
    }
    if (!"1".equals(lit)) {
      guard.add(lit);
    }
    linear(f);
    guard.clear();
  }

  /**
   * Returns the classes of the constraints that could not be written.
   *
   * @return their simple names
   */
  Set<String> unsupported() {
    return unsupported;
  }

  @Override
  public void linear(LinearForm f) {
    switch (f.relation()) {
      case LinearForm.LE -> atLeast(f, -1, -f.c());
      case LinearForm.GE -> atLeast(f, 1, f.c());
      case LinearForm.EQ -> {
        atLeast(f, 1, f.c());
        atLeast(f, -1, -f.c());
        channel(f);
      }
      default -> {
        // the sum is below c, or (the new literal false) above it
        String side = "ne" + ++numAuxiliaries;
        guard.add(side);
        atLeast(f, -1, -(f.c() - 1));
        guard.set(guard.size() - 1, negate(side));
        atLeast(f, 1, f.c() + 1);
        guard.remove(guard.size() - 1);
      }
    }
  }

  /**
   * Links the order literals of x and y by clauses when the relation is x = y + c or x = c - y:
   * unit propagation on the sum alone derives bounds, but not the values x loses with y, which the
   * equality's propagator removes.
   */
  private void channel(LinearForm f) {
    if (f.vars().length != 2
        || Math.abs(f.weights()[0]) != 1
        || Math.abs(f.weights()[1]) != 1
        || f.vars()[0] == f.vars()[1]) {
      return;
    }
    long sign = f.weights()[0];
    long c = sign * f.c();
    // x + (b y) = c, so [x >= v] is [y >= v - c] for b = -1 and not [y >= c - v + 1] for b = 1
    boolean opposite = sign * f.weights()[1] > 0;
    int x = id.applyAsInt(f.vars()[0]);
    int y = id.applyAsInt(f.vars()[1]);
    IntDomain dx = root[x];
    IntDomain dy = root[y];
    if (dx.singleton() || dy.singleton()) {
      return;
    }
    grow(2L * (dx.max() - dx.min()));
    for (int v = dx.min() + 1; v <= dx.max(); v++) {
      long u = opposite ? c - v + 1 : v - c;
      // the literal of y that [x >= v] equals: a name, or "1" or "0" outside y's root domain
      String other;
      if (u <= dy.min()) {
        other = opposite ? "0" : "1";
      } else if (u > dy.max()) {
        other = opposite ? "1" : "0";
      } else {
        other = (opposite ? "~" : "") + ge(y, (int) u);
      }
      equivalent(ge(x, v), other);
    }
  }

  // the value literal of x = v or x != v, or null for another relation
  private String valueLiteral(LinearForm f) {
    if (f.vars().length != 1
        || Math.abs(f.weights()[0]) != 1
        || (f.relation() != LinearForm.EQ && f.relation() != LinearForm.NE)) {
      return null;
    }
    long v = f.weights()[0] * f.c();
    int i = id.applyAsInt(f.vars()[0]);
    IntDomain d = root[i];
    String eqLit;
    if (v < d.min() || v > d.max() || !d.contains((int) v)) {
      eqLit = "0";
    } else {
      eqLit = d.singleton() ? "1" : eq(i, (int) v);
    }
    return f.relation() == LinearForm.EQ ? eqLit : negate(eqLit);
  }

  // the clause a -> b, under the guard
  private void implication(String a, String b) {
    if ("0".equals(a) || "1".equals(b)) {
      return;
    }
    if ("1".equals(a)) {
      line(guardPrefix() + ("0".equals(b) ? "" : "1 " + b + " ") + ">= 1");
    } else if ("0".equals(b)) {
      line(guardPrefix() + "1 " + negate(a) + " >= 1");
    } else {
      line(guardPrefix() + "1 " + negate(a) + " 1 " + b + " >= 1");
    }
  }

  // two clauses, a <-> b, under the guard
  private void equivalent(String a, String b) {
    switch (b) {
      case "1" -> line(guardPrefix() + "1 " + a + " >= 1");
      case "0" -> line(guardPrefix() + "1 " + negate(a) + " >= 1");
      default -> {
        line(guardPrefix() + "1 " + negate(a) + " 1 " + b + " >= 1");
        line(guardPrefix() + "1 " + a + " 1 " + negate(b) + " >= 1");
      }
    }
  }

  // sign * sum >= rhs, under the guard
  private void atLeast(LinearForm f, long sign, long rhs) {
    StringBuilder s = new StringBuilder();
    long constant = 0;
    for (int k = 0; k < f.vars().length; k++) {
      IntVar x = f.vars()[k];
      long a = Math.multiplyExact(sign, f.weights()[k]);
      int i = id.applyAsInt(x);
      IntDomain d = root[i];
      constant = Math.addExact(constant, Math.multiplyExact(a, d.min()));
      if (a == 0 || d.singleton()) {
        continue;
      }
      grow((long) d.max() - d.min());
      for (int v = d.min() + 1; v <= d.max(); v++) {
        s.append(a).append(' ').append(ge(i, v)).append(' ');
      }
    }
    line(guardPrefix() + s + ">= " + Math.subtractExact(rhs, constant));
  }

  @Override
  public void clause(IntVar[] positive, IntVar[] negative) {
    StringBuilder s = new StringBuilder();
    for (int sign = 1; sign >= -1; sign -= 2) {
      for (IntVar x : sign > 0 ? positive : negative) {
        String l = literal(x, sign > 0);
        if ("1".equals(l)) {
          return;
        }
        if (!"0".equals(l)) {
          s.append("1 ").append(l).append(' ');
        }
      }
    }
    line(guardPrefix() + s + ">= 1");
  }

  /**
   * The literal that a 0/1 variable is 1 (or 0 when not positive): a name, or "1" or "0" for a
   * constant.
   */
  String literal(IntVar x, boolean positive) {
    int i = id.applyAsInt(x);
    IntDomain d = root[i];
    if (d.min() < 0 || d.max() > 1) {
      throw new IllegalArgumentException(x + " is not a 0/1 variable");
    }
    if (d.singleton()) {
      return (d.min() == 1) == positive ? "1" : "0";
    }
    return positive ? ge(i, 1) : "~" + ge(i, 1);
  }

  private boolean isBoolean(IntVar x) {
    IntDomain d = root[id.applyAsInt(x)];
    return d.min() >= 0 && d.max() <= 1;
  }

  @Override
  public IntDomain domain(IntVar x) {
    return root[id.applyAsInt(x)];
  }

  @Override
  public String equal(IntVar x, int v) {
    int i = id.applyAsInt(x);
    IntDomain d = root[i];
    if (!d.contains(v)) {
      return "0";
    }
    return d.singleton() ? "1" : eq(i, v);
  }

  @Override
  public String atLeast(IntVar x, int v) {
    int i = id.applyAsInt(x);
    IntDomain d = root[i];
    if (v <= d.min()) {
      return "1";
    }
    if (v > d.max()) {
      return "0";
    }
    return ge(i, v);
  }

  @Override
  public void sum(String[] literals, long[] a, IntVar[] x, long[] w, int relation, long c) {
    // positive literal -> coefficient, and the constant the negated and fixed ones give
    Map<String, Long> terms = new LinkedHashMap<>();
    long constant = 0;
    for (int k = 0; k < literals.length; k++) {
      String l = literals[k];
      switch (l) {
        case "1" -> constant = Math.addExact(constant, a[k]);
        case "0" -> {}
        default -> {
          if (l.startsWith("~")) {
            constant = Math.addExact(constant, a[k]);
            terms.merge(l.substring(1), -a[k], Math::addExact);
          } else {
            terms.merge(l, a[k], Math::addExact);
          }
        }
      }
    }
    for (int j = 0; j < x.length; j++) {
      IntDomain d = root[id.applyAsInt(x[j])];
      constant = Math.addExact(constant, Math.multiplyExact(w[j], d.min()));
      if (w[j] == 0 || d.singleton()) {
        continue;
      }
      grow((long) d.max() - d.min());
      for (int v = d.min() + 1; v <= d.max(); v++) {
        terms.merge(ge(id.applyAsInt(x[j]), v), w[j], Math::addExact);
      }
    }
    if (relation != LinearForm.LE) {
      sumLine(terms, 1, Math.subtractExact(c, constant));
    }
    if (relation != LinearForm.GE) {
      sumLine(terms, -1, Math.subtractExact(constant, c));
    }
  }

  // sign * sum of terms >= rhs, under the guard
  private void sumLine(Map<String, Long> terms, long sign, long rhs) {
    StringBuilder s = new StringBuilder(guardPrefix());
    terms.forEach(
        (l, a) -> {
          if (a != 0) {
            s.append(Math.multiplyExact(sign, a)).append(' ').append(l).append(' ');
          }
        });
    line(s.append(">= ").append(rhs).toString());
  }

  @Override
  public void clause(String... literals) {
    StringBuilder s = new StringBuilder(guardPrefix());
    for (String l : literals) {
      if ("1".equals(l)) {
        return;
      }
      if (!"0".equals(l)) {
        s.append("1 ").append(l).append(' ');
      }
    }
    line(s.append(">= 1").toString());
  }

  private static String negate(String lit) {
    return switch (lit) {
      case "0" -> "1";
      case "1" -> "0";
      default -> lit.startsWith("~") ? lit.substring(1) : "~" + lit;
    };
  }

  private String guardPrefix() {
    return guard.isEmpty() ? "" : String.join(" ", guard) + " ==> ";
  }

  /**
   * Returns the objective to minimise, the order literals of a variable and its root minimum.
   *
   * @param x the variable minimised
   * @return the objective line
   */
  String objective(IntVar x) {
    int i = id.applyAsInt(x);
    IntDomain d = root[i];
    StringBuilder s = new StringBuilder("min:");
    for (int v = d.min() + 1; v <= d.max() && !d.singleton(); v++) {
      s.append(" 1 ").append(ge(i, v));
    }
    return s.append(' ').append(d.min()).append(" ;\n").toString();
  }

  private void line(String constraint) {
    constraints.append(constraint).append(" ;\n");
    numConstraints++;
    if (constraints.length() > MAX_CHARS) {
      // the order and channelling lines cost several lines per value, more than their term count
      throw new UnsupportedOperationException("the OPB model is over " + MAX_CHARS + " characters");
    }
  }

  // the longest model text, well below the largest array a StringBuilder can hold
  private static final int MAX_CHARS = 400_000_000;

  private void grow(long terms) {
    numTerms += terms;
    if (numTerms > maxTerms) {
      throw new UnsupportedOperationException(
          "the OPB model is over " + maxTerms + " terms (system property jacop.lcg.proofTerms)");
    }
  }

  /**
   * Writes the model: its header, the objective (or null), the comments and the constraints.
   *
   * @param out where the model goes
   * @param objective the objective line, or null
   * @param comments lines of comments, each starting with "* "
   * @throws IOException if out fails
   */
  void write(OutputStream out, String objective, CharSequence comments) throws IOException {
    String head =
        "* #variable= "
            + (numVariables + numAuxiliaries)
            + " #constraint= "
            + numConstraints
            + "\n"
            + (objective == null ? "" : objective)
            + comments;
    out.write(head.getBytes(StandardCharsets.US_ASCII));
    byte[] chunk = new byte[1 << 16];
    for (int from = 0; from < constraints.length(); from += chunk.length) {
      int to = Math.min(constraints.length(), from + chunk.length);
      for (int k = from; k < to; k++) {
        chunk[k - from] = (byte) constraints.charAt(k);
      }
      out.write(chunk, 0, to - from);
    }
  }

  /**
   * Returns the number of constraints VeriPB loads.
   *
   * @return the count, an equality counted twice
   */
  long numConstraints() {
    return numConstraints;
  }
}
