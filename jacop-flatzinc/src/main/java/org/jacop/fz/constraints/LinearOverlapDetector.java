/*
 * LinearOverlapDetector.java
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

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Linear overlap factoring: a sub-sum {@code sum(b_i * x_i)} that several linear constraints of the
 * model contain, each a multiple {@code k * sum(b_i * x_i)} of it, becomes a new variable {@code z}
 * with {@code z = sum(b_i * x_i)}, and every one of these constraints gets {@code k * z} in place
 * of its terms. The factoring is exact. The bounds of {@code z} carry what one constraint learns
 * about the sub-sum to the others, and the constraints have fewer terms.
 *
 * <p>Greedy, as the horizontal overlap rule of the CP-SAT presolve ({@code
 * FindBigHorizontalLinearOverlap} in OR-Tools {@code cp_model_presolve.cc}): every row in turn
 * takes the largest common proportional sub-sum it shares with another row, and the factoring
 * repeats while it finds one. The sub-sum must have at least {@code
 * org.jacop.fz.linearOverlap.minSize} (4) terms. Rows {@code int_lin_eq}, {@code int_lin_le},
 * {@code int_lin_ne} take part, and their reified and half-reified forms with {@code
 * -Dorg.jacop.fz.linearOverlap.reified=true}. Off by default, {@code
 * -Dorg.jacop.fz.linearOverlap=true} turns it on.
 *
 * <p>Reference: L. Perron, F. Didier, CP-SAT, Google OR-Tools 9.15 ({@code
 * CpModelPresolver::FindBigHorizontalLinearOverlap}); the rule has no separate publication.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LinearOverlapDetector implements ParserTreeConstants {

  static final int MIN_SIZE = Integer.getInteger("org.jacop.fz.linearOverlap.minSize", 4);

  /** Variables in more rows than this are not used to find the partner rows (as CP-SAT). */
  static final int MAX_OCCURRENCES = Integer.getInteger("org.jacop.fz.linearOverlap.maxOcc", 200);

  /** At most this many terms visited while looking for partners, so large models stay cheap. */
  static final long WORK_LIMIT = Long.getLong("org.jacop.fz.linearOverlap.work", 50_000_000L);

  /**
   * Whether reified and half-reified rows take part too ({@code
   * org.jacop.fz.linearOverlap.reified}, false): their sums are mostly not propagated until the
   * literal is fixed, and the bounds of the new variables cost propagation at every node
   * (pattern-set-mining-k1 and bnn-planner, same trees, 3 to 4 times slower).
   */
  private static final Set<String> PLAIN = Set.of("int_lin_eq", "int_lin_le", "int_lin_ne");

  private static final Set<String> HALF_OR_REIFIED =
      Set.of(
          "int_lin_eq_reif",
          "int_lin_le_reif",
          "int_lin_ne_reif",
          "int_lin_eq_imp",
          "int_lin_le_imp",
          "int_lin_ne_imp");

  /**
   * The terms of a rewritten constraint.
   *
   * @param coefficients the coefficients
   * @param vars the variables
   */
  public record Rewrite(int[] coefficients, IntVar[] vars) {
    @Override
    public boolean equals(Object o) {
      return this == o;
    }

    @Override
    public int hashCode() {
      return System.identityHashCode(this);
    }

    @Override
    public String toString() {
      return "Rewrite[" + coefficients.length + " terms]";
    }
  }

  private final Support support;

  private final List<SimpleNode> nodes = new ArrayList<>();

  /**
   * Terms of each row, in the order of the row; a duplicated variable has its coefficients summed.
   */
  private final List<LinkedHashMap<IntVar, Long>> rows = new ArrayList<>();

  private final Map<IntVar, LinkedHashSet<Integer>> occurrences = new IdentityHashMap<>();

  private boolean[] changed;

  private int factored;

  private long work;

  /**
   * It creates the detector.
   *
   * @param support the support of the FlatZinc front end.
   */
  public LinearOverlapDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the factoring is on.
   *
   * @return true if the system property org.jacop.fz.linearOverlap is true.
   */
  public static boolean enabled() {
    return Boolean.parseBoolean(System.getProperty("org.jacop.fz.linearOverlap", "false"));
  }

  /**
   * It scans the linear constraints of the model, factors their common sub-sums, posts the
   * definitions of the new variables and records the rewritten constraints in the support.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    // reified and half-reified sums are mostly not propagated until their literal is fixed, while
    // the bounds of the new variables cost propagation at every node: pattern-set-mining-k1 and
    // bnn-planner make the same trees 3 to 4 times slower with them
    boolean reified = Boolean.getBoolean("org.jacop.fz.linearOverlap.reified");
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM
              && (PLAIN.contains(((ASTConstElem) item).getName())
                  || reified && HALF_OR_REIFIED.contains(((ASTConstElem) item).getName()))) {
            collect(item);
          }
        }
      }
    }
    if (rows.size() < 2) {
      return;
    }
    changed = new boolean[rows.size()];
    factor(new LinearConstraints(support));
    if (support.options.debug() && factored > 0) {
      int rewritten = 0;
      for (boolean c : changed) {
        rewritten += c ? 1 : 0;
      }
      FzConsole.println(
          "% linear overlap: "
              + factored
              + " sub-sums factored into new variables, "
              + rewritten
              + " of "
              + rows.size()
              + " linear constraints rewritten");
    }
  }

  private void collect(SimpleNode node) {
    int[] coefficients = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] vars = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (coefficients.length != vars.length) {
      return;
    }
    LinkedHashMap<IntVar, Long> row = new LinkedHashMap<>();
    for (int i = 0; i < vars.length; i++) {
      row.merge(vars[i], (long) coefficients[i], Long::sum);
    }
    row.values().removeIf(c -> c == 0);
    int free = 0;
    for (IntVar x : row.keySet()) {
      free += x.singleton() ? 0 : 1;
    }
    if (free < MIN_SIZE) {
      return;
    }
    int id = rows.size();
    nodes.add(node);
    rows.add(row);
    for (Map.Entry<IntVar, Long> t : row.entrySet()) {
      if (!t.getKey().singleton()) {
        occurrences.computeIfAbsent(t.getKey(), k -> new LinkedHashSet<>()).add(id);
      }
    }
  }

  private void factor(LinearConstraints linear) {
    int n = rows.size();
    int[] count = new int[n];
    for (int i = 0; i < n && work < WORK_LIMIT; i++) {
      while (work < WORK_LIMIT && factorRow(i, count, linear)) {
        // the row may share another sub-sum
      }
    }
    for (int i = 0; i < n; i++) {
      if (changed[i]) {
        LinkedHashMap<IntVar, Long> row = rows.get(i);
        List<IntVar> vars = new ArrayList<>(row.size());
        List<Integer> coefficients = new ArrayList<>(row.size());
        for (Map.Entry<IntVar, Long> t : row.entrySet()) {
          if (t.getValue() != 0) {
            vars.add(t.getKey());
            coefficients.add(t.getValue().intValue());
          }
        }
        support.linearRewrites.put(
            nodes.get(i),
            new Rewrite(
                coefficients.stream().mapToInt(Integer::intValue).toArray(),
                vars.toArray(new IntVar[0])));
      }
    }
  }

  /** The best partner of row i; false if there is none or the factoring cannot be done. */
  private boolean factorRow(int i, int[] count, LinearConstraints linear) {
    LinkedHashMap<IntVar, Long> row = rows.get(i);
    List<Integer> touched = new ArrayList<>();
    for (Map.Entry<IntVar, Long> t : row.entrySet()) {
      LinkedHashSet<Integer> occ = occurrences.get(t.getKey());
      if (occ == null || occ.size() > MAX_OCCURRENCES) {
        continue;
      }
      work += occ.size();
      for (int j : occ) {
        if (j != i && count[j]++ == 0) {
          touched.add(j);
        }
      }
    }
    List<IntVar> best = null;
    for (int j : touched) {
      if (count[j] >= MIN_SIZE && (best == null || count[j] > best.size())) {
        List<IntVar> group = largestProportionalGroup(row, rows.get(j));
        if (group.size() >= MIN_SIZE && (best == null || group.size() > best.size())) {
          best = group;
        }
      }
      count[j] = 0;
    }
    return best != null && substitute(i, best, linear);
  }

  /** The largest set of common variables whose coefficients have the same ratio in both rows. */
  private List<IntVar> largestProportionalGroup(
      LinkedHashMap<IntVar, Long> a, LinkedHashMap<IntVar, Long> b) {
    Map<List<Long>, List<IntVar>> groups = new HashMap<>();
    List<IntVar> best = List.of();
    for (Map.Entry<IntVar, Long> t : a.entrySet()) {
      Long other = b.get(t.getKey());
      if (other == null || t.getKey().singleton() || occurrences.get(t.getKey()) == null) {
        continue;
      }
      work++;
      long p = other;
      long q = t.getValue();
      long g = gcd(Math.abs(p), Math.abs(q));
      p /= g;
      q /= g;
      if (q < 0) {
        p = -p;
        q = -q;
      }
      List<IntVar> group = groups.computeIfAbsent(List.of(p, q), k -> new ArrayList<>());
      group.add(t.getKey());
      if (group.size() > best.size()) {
        best = group;
      }
    }
    return best;
  }

  private boolean substitute(int i, List<IntVar> sub, LinearConstraints linear) {
    LinkedHashMap<IntVar, Long> row = rows.get(i);
    long g = 0;
    for (IntVar x : sub) {
      g = gcd(g, Math.abs(row.get(x)));
    }
    if (row.get(sub.get(0)) < 0) {
      g = -g;
    }
    long[] base = new long[sub.size()];
    for (int t = 0; t < base.length; t++) {
      base[t] = row.get(sub.get(t)) / g;
    }

    // the rows that contain the whole sub-sum as a multiple of base
    IntVar rarest = sub.get(0);
    for (IntVar x : sub) {
      if (occurrences.get(x).size() < occurrences.get(rarest).size()) {
        rarest = x;
      }
    }
    List<Integer> members = new ArrayList<>();
    List<Long> multipliers = new ArrayList<>();
    for (int j : occurrences.get(rarest)) {
      LinkedHashMap<IntVar, Long> r = rows.get(j);
      Long c0 = r.get(sub.get(0));
      work += sub.size();
      if (c0 == null || c0 % base[0] != 0) {
        continue;
      }
      long k = c0 / base[0];
      boolean all = true;
      for (int t = 1; t < base.length && all; t++) {
        Long c = r.get(sub.get(t));
        all = c != null && c == k * base[t];
      }
      if (all) {
        members.add(j);
        multipliers.add(k);
      }
    }
    if (members.size() < 2) {
      return false;
    }

    long lo = 0;
    long hi = 0;
    for (int t = 0; t < base.length; t++) {
      IntVar x = sub.get(t);
      long a = base[t] * x.min();
      long b = base[t] * x.max();
      lo += Math.min(a, b);
      hi += Math.max(a, b);
    }
    if (lo < IntDomain.MIN_INT || hi > IntDomain.MAX_INT) {
      return false;
    }
    for (long k : multipliers) {
      if (Math.abs(k) * Math.max(Math.abs(lo), Math.abs(hi)) > IntDomain.MAX_INT
          || Math.abs(k) > Integer.MAX_VALUE) {
        return false;
      }
    }

    IntVar z = new IntVar(support.store, (int) lo, (int) hi);
    int[] coefficients = new int[base.length + 1];
    IntVar[] vars = new IntVar[base.length + 1];
    for (int t = 0; t < base.length; t++) {
      coefficients[t] = (int) base[t];
      vars[t] = sub.get(t);
    }
    coefficients[base.length] = -1;
    vars[base.length] = z;
    linear.poseLinearEquality(coefficients, vars, 0);
    // as a block sum of a split linear constraint: the linear relaxation substitutes z back, so it
    // keeps the rows of the model, and z is a defined variable, not searched
    support.dictionary.addSplitSum(z);

    LinkedHashSet<Integer> zOcc = new LinkedHashSet<>();
    for (int m = 0; m < members.size(); m++) {
      int j = members.get(m);
      LinkedHashMap<IntVar, Long> r = rows.get(j);
      for (IntVar x : sub) {
        r.remove(x);
        occurrences.get(x).remove(j);
      }
      r.put(z, multipliers.get(m));
      zOcc.add(j);
      changed[j] = true;
    }
    occurrences.put(z, zOcc);
    factored++;
    return true;
  }

  private static long gcd(long a, long b) {
    while (b != 0) {
      long t = a % b;
      a = b;
      b = t;
    }
    return a;
  }
}
