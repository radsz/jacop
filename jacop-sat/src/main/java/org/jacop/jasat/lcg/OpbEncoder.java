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
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.BooleanSupplier;
import java.util.function.ToIntFunction;
import org.jacop.constraints.AbstractReifiedConstraint;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
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
   * The lines of a cardinality constraint (all different or global cardinality), by which the
   * solver derives its flow reasons: for each counted value the upper line {@code sum [x_j = v] -
   * count <= 0} and the lower line {@code sum [x_j = v] - count >= 0}, and for each variable the
   * line that it takes at most one value. A line not written is 0.
   */
  static final class CardinalityLines {
    final int[] variables;
    final Map<Integer, Integer> position;
    final int[] values;
    final int[] counters;
    final int[] low;
    final int[] up;
    final boolean closed;
    final Map<Integer, Integer> counterPosition;
    final long[] upper;
    final long[] lower;
    final long[] atMostOne;

    /**
     * Collects the lines.
     *
     * @param variables the indexes of the counted variables
     * @param position the position of each index in variables
     * @param values the counted values, increasing
     * @param counters the index of the counter of each value, or -1 for constant bounds
     * @param low the lower bound of each value without a counter
     * @param up the upper bound of each value without a counter
     * @param closed whether the variables take counted values only; otherwise the other values are
     *     free
     * @param counterPosition the position of each counter index in counters
     * @param upper the upper line of each value
     * @param lower the lower line of each value
     * @param atMostOne the at-most-one line of each variable
     */
    CardinalityLines(
        int[] variables,
        Map<Integer, Integer> position,
        int[] values,
        int[] counters,
        int[] low,
        int[] up,
        boolean closed,
        Map<Integer, Integer> counterPosition,
        long[] upper,
        long[] lower,
        long[] atMostOne) {
      this.variables = variables;
      this.position = position;
      this.values = values;
      this.counters = counters;
      this.low = low;
      this.up = up;
      this.closed = closed;
      this.counterPosition = counterPosition;
      this.upper = upper;
      this.lower = lower;
      this.atMostOne = atMostOne;
    }
  }

  private final Map<Constraint, CardinalityLines> cardinality = new IdentityHashMap<>();

  /**
   * The first line of an equality, {@code sum >= c}, which the next line, {@code -sum >= -c},
   * follows: the lines a proof sums to state the objective through its definitions.
   */
  record EqualityLine(LinearForm form, long id) {}

  private final Map<Constraint, EqualityLine> equalities = new IdentityHashMap<>();

  // the id of each variable's first order line, [x >= v] or not [x >= v + 1], for v = min + 1
  private long[] chainStart;

  // the constraint being written
  private Constraint current;

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
    chainStart = new long[vars.length];
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] == null || root[i].singleton()) {
        continue;
      }
      IntDomain d = root[i];
      int m = d.min();
      int max = d.max();
      grow((long) max - m);
      numVariables += 2L * (max - m) + 1;
      chainStart[i] = numConstraints + 1;
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
    current = c;
    if (!encode(c)) {
      String name = c.getClass().getSimpleName();
      if (c instanceof AbstractReifiedConstraint r) {
        name += " of " + r.c.getClass().getSimpleName();
      } else if (c instanceof Not n) {
        name += " of " + n.negatedConstraint().getClass().getSimpleName();
      }
      unsupported.add(name);
    }
  }

  /**
   * Returns whether the model can state a constraint, encoding it into this model.
   *
   * @param c the constraint
   * @return true if it is encoded
   */
  boolean encodes(Constraint c) {
    current = c;
    return encode(c);
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
      if (!isBoolean(r.b)) {
        return false;
      }
      LinearForm inner = form(r.c);
      if (inner != null) {
        reified(r.b, inner, r instanceof Reified);
        return true;
      }
      String lit = literal(r.b, true);
      return implied(lit, r.c, false)
          && (!(r instanceof Reified) || implied(negate(lit), r.c, true));
    }
    if (c instanceof Not n && n.getClass() == Not.class) {
      return implied("1", n.negatedConstraint(), true);
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

  static LinearForm form(Constraint c) {
    if (c instanceof LinearInt l) {
      return l.linearRelation();
    }
    if (c instanceof LinearExplainable l) {
      return l.linearForm();
    }
    return null;
  }

  @Override
  public void guarded(String lit, LinearForm f) {
    if ("0".equals(lit)) {
      return; // the guard is false: nothing to state
    }
    if (!"1".equals(lit)) {
      guard.add(lit);
    }
    linear(f);
    if (!"1".equals(lit)) {
      guard.remove(guard.size() - 1);
    }
  }

  @Override
  public boolean implied(String lit, BooleanSupplier encoding) {
    if ("0".equals(lit)) {
      return true; // the guard is false: nothing to state
    }
    if ("1".equals(lit)) {
      return encoding.getAsBoolean();
    }
    guard.add(lit);
    try {
      return encoding.getAsBoolean();
    } catch (IllegalStateException e) {
      // an encoding the proof derives lines from: the constraint is listed as unsupported, which
      // stops the proof, so the lines it wrote under the guard do no harm
      return false;
    } finally {
      guard.remove(guard.size() - 1);
    }
  }

  // writes that lit implies c, or its negation
  private boolean implied(String lit, PrimitiveConstraint c, boolean negated) {
    if (c instanceof Not n && n.getClass() == Not.class) {
      return implied(lit, n.negatedConstraint(), !negated);
    }
    LinearForm f = form(c);
    if (f != null) {
      guarded(lit, negated ? f.negated() : f);
      return true;
    }
    return c instanceof PbEncodable p && p.encodeImplied(this, lit, negated);
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
        if (guard.isEmpty() && current != null) {
          equalities.putIfAbsent(current, new EqualityLine(f, numConstraints + 1));
        }
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
  public void allDifferent(IntVar[] x) {
    if (!guard.isEmpty()) {
      throw new IllegalStateException("an all different constraint under a guard");
    }
    int[] variables = new int[x.length];
    Map<Integer, Integer> position = new HashMap<>();
    Map<Integer, StringBuilder> terms = new TreeMap<>();
    Map<Integer, Integer> count = new HashMap<>();
    for (int j = 0; j < x.length; j++) {
      int i = id.applyAsInt(x[j]);
      variables[j] = i;
      position.put(i, j);
      IntDomain d = root[i];
      grow(d.getSize());
      for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        count.merge(v, 1, Integer::sum);
        StringBuilder t = terms.computeIfAbsent(v, k -> new StringBuilder());
        if (!d.singleton()) {
          // a fixed variable's term is 0, and the degree still counts it
          t.append("1 ~").append(eq(i, v)).append(' ');
        }
      }
    }
    int[] values = new int[terms.size()];
    long[] upper = new long[values.length];
    int k = 0;
    for (Map.Entry<Integer, StringBuilder> t : terms.entrySet()) {
      values[k] = t.getKey();
      int c = count.getOrDefault(t.getKey(), 0);
      if (c >= 2) {
        line(t.getValue() + ">= " + (c - 1));
        upper[k] = numConstraints;
      }
      k++;
    }
    int[] counters = new int[values.length];
    Arrays.fill(counters, -1);
    int[] up = new int[values.length];
    Arrays.fill(up, 1);
    cardinality.put(
        current,
        new CardinalityLines(
            variables,
            position,
            values,
            counters,
            new int[values.length],
            up,
            true,
            Map.of(),
            upper,
            new long[values.length],
            new long[x.length]));
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
    if (!guard.isEmpty()) {
      throw new IllegalStateException("a cardinality constraint under a guard");
    }
    int[] variables = new int[x.length];
    Map<Integer, Integer> position = new HashMap<>();
    Set<Integer> counted = new HashSet<>();
    for (int v : values) {
      counted.add(v);
    }
    long[] atMostOne = new long[x.length];
    for (int j = 0; j < x.length; j++) {
      int i = id.applyAsInt(x[j]);
      variables[j] = i;
      position.put(i, j);
      IntDomain d = root[i];
      grow(d.getSize());
      List<String> literals = new ArrayList<>();
      for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        if (counted.contains(v) || !closed) {
          literals.add(equalTo(x[j], v));
        } else {
          // the variables take counted values only
          clause(PbModel.not(equalTo(x[j], v)));
        }
      }
      if (literals.size() >= 2) {
        // implied by the definitions of the value literals; a lower bound reason needs it
        long[] ones = new long[literals.size()];
        Arrays.fill(ones, 1);
        sum(literals.toArray(String[]::new), ones, new IntVar[0], new long[0], LinearForm.LE, 1);
        atMostOne[j] = numConstraints;
      }
    }
    int[] counterIds = new int[values.length];
    Map<Integer, Integer> counterPosition = new HashMap<>();
    long[] upper = new long[values.length];
    long[] lower = new long[values.length];
    for (int k = 0; k < values.length; k++) {
      if (counters[k] == null) {
        counterIds[k] = -1;
        PbModel.count(this, x, values[k], new IntVar[0], LinearForm.GE, low[k]);
        lower[k] = numConstraints;
        PbModel.count(this, x, values[k], new IntVar[0], LinearForm.LE, up[k]);
        upper[k] = numConstraints;
        continue;
      }
      counterIds[k] = id.applyAsInt(counters[k]);
      if (!root[counterIds[k]].singleton()) {
        counterPosition.put(counterIds[k], k);
      }
      // sum [x_j = v] - count >= 0, then <= 0
      PbModel.count(this, x, values[k], new IntVar[] {counters[k]}, LinearForm.EQ, 0);
      lower[k] = numConstraints - 1;
      upper[k] = numConstraints;
    }
    if (rest != null) {
      // the variables taking no counted value: rest + sum counters = n
      IntVar[] all = Arrays.copyOf(counters, counters.length + 1);
      all[counters.length] = rest;
      long[] ones = new long[all.length];
      Arrays.fill(ones, 1);
      sum(new String[0], new long[0], all, ones, LinearForm.EQ, x.length);
    }
    cardinality.put(
        current,
        new CardinalityLines(
            variables,
            position,
            values,
            counterIds,
            low,
            up,
            closed,
            counterPosition,
            upper,
            lower,
            atMostOne));
  }

  /**
   * Returns the lines of the cardinality constraints written.
   *
   * @return the lines of each constraint
   */
  Map<Constraint, CardinalityLines> cardinalityLines() {
    return cardinality;
  }

  /**
   * Returns the first line of each equality written unguarded, by its constraint.
   *
   * @return the lines
   */
  Map<Constraint, EqualityLine> equalityLines() {
    return equalities;
  }

  /**
   * Returns the id of each variable's first order line, {@code [x >= m + 1] or not [x >= m + 2]}
   * for its root min m, which the lines of the next values follow; 0 for a variable without them.
   *
   * @return the ids, by variable
   */
  long[] chainLines() {
    return chainStart;
  }

  /**
   * The literals of a circuit's positions, by which the solver derives its cut reasons:
   * forward[i][k] that node i is k arcs after node 0 along the circuit, reverse[i][k] that it is k
   * arcs before it, for k from 1 to n - 1, as names or "0" and "1"; node 0 and position n have none
   * ("0").
   */
  record CircuitLines(int[] variables, int offset, String[][] forward, String[][] reverse) {}

  private final Map<Constraint, CircuitLines> circuits = new IdentityHashMap<>();

  /**
   * The lines of a time-indexed cumulative over fixed durations and uses: the trail index of each
   * task's start, its duration and use, the trail index of the limit, the id of the load line at
   * each time point, and of each task the id of the line {@code c - [s >= t - d + 1] + [s >= t + 1]
   * >= 0} that defines its covering literal at a time point, where it has one (elsewhere that
   * literal is an order literal).
   */
  record TimetableLines(
      int[] starts,
      int[] durations,
      int[] uses,
      int limit,
      Map<Long, Long> load,
      List<Map<Long, Long>> covers) {}

  private final Map<Constraint, TimetableLines> timetables = new IdentityHashMap<>();

  /**
   * Returns the position literals of each circuit.
   *
   * @return the literals, by constraint
   */
  Map<Constraint, CircuitLines> circuitLines() {
    return circuits;
  }

  @Override
  public void timetable(IntVar[] starts, int[] durations, int[] uses, IntVar limit) {
    if (!guard.isEmpty()) {
      throw new IllegalStateException("a time table under a guard");
    }
    if (current == null) {
      return;
    }
    int n = starts.length;
    int[] ids = new int[n];
    List<Map<Long, Long>> covers = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      ids[i] = id.applyAsInt(starts[i]);
      covers.add(new HashMap<>());
    }
    timetables.put(
        current,
        new TimetableLines(
            ids, durations.clone(), uses.clone(), id.applyAsInt(limit), new HashMap<>(), covers));
  }

  @Override
  public void timetableLine(int task, long t) {
    TimetableLines lines = current == null ? null : timetables.get(current);
    if (lines != null) {
      (task < 0 ? lines.load() : lines.covers().get(task)).put(t, numConstraints + 1);
    }
  }

  /** The lines of each time-indexed cumulative over fixed durations and uses. */
  Map<Constraint, TimetableLines> timetableLines() {
    return timetables;
  }

  /**
   * Writes a circuit: all different successors in the range of the nodes, no node its own
   * successor, each node some node's successor, and two position encodings. Node 0 is at position
   * 0; an arc i to j with j not 0 puts j one after i, and an arc into 0 puts its tail at n - 1.
   * Backwards, an arc into 0 puts its tail at 1, an arc i to j with i not 0 puts i one after j, and
   * the arc out of 0 puts its head at n - 1. Each position is a value of a node, by order literals,
   * and each arc a clause per position. A set of nodes that no arc leaves, without node 0, then has
   * no position for its nodes, which steps derive from the last position down; the nodes outside
   * such a set with node 0 have no backward position.
   */
  @Override
  public void circuit(IntVar[] x, int offset) {
    if (!guard.isEmpty()) {
      throw new IllegalStateException("a circuit under a guard");
    }
    int n = x.length;
    int[] variables = new int[n];
    for (int i = 0; i < n; i++) {
      variables[i] = id.applyAsInt(x[i]);
    }
    allDifferent(x);
    long arcs = 0;
    for (int i = 0; i < n; i++) {
      arcs += root[variables[i]].getSize();
      clause(atLeast(x[i], offset));
      clause(PbModel.not(atLeast(x[i], offset + n)));
      clause(PbModel.not(equalTo(x[i], offset + i)));
    }
    grow(6 * arcs * n + 8L * n * n);
    String[][] forward = positions(n);
    String[][] reverse = positions(n);
    for (int j = 0; j < n; j++) {
      String[] column = new String[n];
      for (int i = 0; i < n; i++) {
        column[i] = i == j ? "0" : equalTo(x[i], offset + j);
      }
      clause(column);
    }
    for (int i = 0; i < n; i++) {
      IntDomain d = root[variables[i]];
      for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
        int w = e.nextElement();
        long j = (long) w - offset;
        if (j < 0 || j >= n || j == i) {
          continue;
        }
        String arc = PbModel.not(equalTo(x[i], w));
        arc(arc, forward, i, (int) j, n);
        arc(arc, reverse, (int) j, i, n);
      }
    }
    circuits.put(current, new CircuitLines(variables, offset, forward, reverse));
  }

  // the clauses of an arc that puts node b one after node a (node 0 at 0, and n - 1 before it)
  private void arc(String notArc, String[][] p, int a, int b, int n) {
    if (a == 0) {
      clause(notArc, p[b][1]);
    } else if (b == 0) {
      clause(notArc, p[a][n - 1]);
    } else {
      for (int k = 1; k < n; k++) {
        clause(notArc, negate(p[a][k]), p[b][k + 1]);
      }
    }
  }

  // the literals that node i (not 0) is at position k, for k in 1..n - 1, defined by order literals
  private String[][] positions(int n) {
    String[][] p = new String[n][n + 1];
    for (String[] row : p) {
      Arrays.fill(row, "0");
    }
    for (int i = 1; i < n; i++) {
      // at[k] that the position is at least k: 1 for k = 1, 0 for k = n
      String[] at = new String[n + 1];
      at[1] = "1";
      at[n] = "0";
      for (int k = 2; k < n; k++) {
        at[k] = auxiliary();
        if (k > 2) {
          clause(negate(at[k]), at[k - 1]);
        }
      }
      for (int k = 1; k < n; k++) {
        String e = n == 2 ? "1" : auxiliary();
        p[i][k] = e;
        if (!"1".equals(e)) {
          clause(negate(e), at[k]);
          clause(negate(e), negate(at[k + 1]));
          clause(e, negate(at[k]), at[k + 1]);
        }
      }
    }
    return p;
  }

  @Override
  public String auxiliary() {
    return "aux" + ++numAuxiliaries;
  }

  @Override
  public IntDomain domain(IntVar x) {
    return root[id.applyAsInt(x)];
  }

  @Override
  public String equalTo(IntVar x, int v) {
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
        case "0" -> {
          // a false literal adds nothing
        }
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
      throw new TooLarge("the OPB model is over " + MAX_CHARS + " characters");
    }
  }

  // the longest model text, well below the largest array a StringBuilder can hold
  private static final int MAX_CHARS = 400_000_000;

  private void grow(long terms) {
    numTerms += terms;
    if (numTerms > maxTerms) {
      throw new TooLarge(
          "the OPB model is over " + maxTerms + " terms (system property jacop.lcg.proofTerms)");
    }
  }

  /** The model is larger than the encoder writes. */
  static final class TooLarge extends UnsupportedOperationException {
    private static final long serialVersionUID = 1L;

    TooLarge(String message) {
      super(message);
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
