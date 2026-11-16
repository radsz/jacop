/*
 * LinearEqualityPairs.java
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
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds equalities written as two opposite inequalities, {@code a*x <= c} and {@code -a*x <=
 * -c}, and turns each pair into one {@code int_lin_eq}, which every later reader of the parse tree
 * then sees. The normalised pseudo-Boolean format writes every equality this way (the instances of
 * the PB competitions have {@code #equal= 0}), and some MiniZinc models state both bounds of a sum
 * separately, while the detectors that read equalities ({@link LinearSystemDetector}, {@link
 * KnapsackDetector}, {@link ExactCoverDetector}, {@link SymmetricGCCDetector}, {@link
 * RoutesDetector}, {@link CardinalityDetector}) read {@code int_lin_eq} only. One equality is also
 * one propagator where the pair was two.
 *
 * <p>The rows are compared after their terms are merged by variable and divided by the greatest
 * common divisor of their coefficients (the bound rounded down), as parallel rows are found by the
 * presolve of MIP solvers (R. E. Bixby and D. K. Wagner, A note on detecting simple redundancies in
 * linear systems, Operations Research Letters 6(1), 1987, pp. 15-17; T. Achterberg, R. E. Bixby, Z.
 * Gu, E. Rothberg and D. Weninger, Presolve reductions in mixed integer programming, INFORMS
 * Journal on Computing 32(2), 2020, pp. 473-506). When the tightest bounds of a row and of its
 * opposite meet, the tightest row becomes the equality and the other rows over the same terms,
 * implied by it, are not posted. Bounds that do not meet are left as they are.
 *
 * <p>Off under {@code --proof}, which encodes the model as given; the system property {@code
 * org.jacop.fz.equalityPairs} set to false turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LinearEqualityPairs implements ParserTreeConstants {

  private static final String LIN_LE = "int_lin_le";

  private final Support support;

  private final Set<SimpleNode> replaced = new HashSet<>();

  private int equalities;

  /**
   * A row a*x <= c by its constraint node: its terms over unfixed variables divided by their gcd
   * have the bound {@code bound}, and its fixed variables add up to {@code fixed}.
   */
  private record Row(ASTConstElem node, long gcd, long bound, long fixed) {}

  /**
   * It creates the detector.
   *
   * @param support the support of the FlatZinc front end.
   */
  public LinearEqualityPairs(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.equalityPairs is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.equalityPairs"));
  }

  /**
   * The inequalities implied by the equalities, which are not posted.
   *
   * @return their constraint nodes.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  /**
   * The number of equalities found.
   *
   * @return the number of pairs turned into int_lin_eq.
   */
  public int equalities() {
    return equalities;
  }

  /**
   * It turns the pairs of opposite inequalities of the model into equalities.
   *
   * @param astTree the root of the parsed model.
   * @param skipped constraint nodes that are not posted.
   */
  public void detect(SimpleNode astTree, Set<SimpleNode> skipped) {
    // variables are numbered in the order they are met, so that the keys do not depend on hashes
    Map<IntVar, Integer> ids = new IdentityHashMap<>();
    Map<List<Long>, List<Row>> rows = new HashMap<>();
    List<List<Long>> order = new ArrayList<>();
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() != JJTCONSTRAINTITEMS) {
        continue;
      }
      for (int j = 0; j < node.jjtGetNumChildren(); j++) {
        SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
        if (item.getId() == JJTCONSTELEM
            && !skipped.contains(item)
            && LIN_LE.equals(((ASTConstElem) item).getName())) {
          ASTConstElem c = (ASTConstElem) item;
          List<Long> key = new ArrayList<>();
          Row r = row(c, ids, key);
          if (r != null) {
            rows.computeIfAbsent(
                    key,
                    k -> {
                      order.add(k);
                      return new ArrayList<>();
                    })
                .add(r);
          }
        }
      }
    }
    for (List<Long> key : order) {
      List<Long> opposite = negated(key);
      List<Row> up = rows.get(key);
      List<Row> down = rows.get(opposite);
      // each pair once: from the key whose first coefficient is positive
      if (down == null || key.get(1) < 0) {
        continue;
      }
      Row tight = tightest(up);
      Row other = tightest(down);
      // a*x <= u and -a*x <= d, so -d <= a*x <= u
      if (tight.bound() != -other.bound()) {
        continue;
      }
      ASTConstElem eq = tight.node();
      eq.setName("int_lin_eq");
      // the equality of the terms as written: the unfixed ones add up to gcd * bound
      long rhs = tight.gcd() * tight.bound() + tight.fixed();
      if (rhs != support.getInt((ASTScalarFlatExpr) eq.jjtGetChild(2))) {
        ASTScalarFlatExpr e = new ASTScalarFlatExpr(JJTSCALARFLATEXPR);
        e.setType(0);
        e.setInt((int) rhs);
        e.jjtSetParent(eq);
        eq.jjtAddChild(e, 2);
      }
      for (Row r : up) {
        if (r != tight) {
          replaced.add(r.node());
        }
      }
      for (Row r : down) {
        replaced.add(r.node());
      }
      equalities++;
    }
    if (support.options.debug() && equalities > 0) {
      FzConsole.println(
          "% equality pairs: "
              + equalities
              + " equalities from opposite inequalities, "
              + (replaced.size() - equalities)
              + " implied duplicates");
    }
  }

  // the row with the least bound, the first one on ties
  private static Row tightest(List<Row> rows) {
    Row best = rows.get(0);
    for (Row r : rows) {
      if (r.bound() < best.bound()) {
        best = r;
      }
    }
    return best;
  }

  private static List<Long> negated(List<Long> key) {
    List<Long> n = new ArrayList<>(key.size());
    for (int i = 0; i < key.size(); i += 2) {
      n.add(key.get(i));
      n.add(-key.get(i + 1));
    }
    return n;
  }

  // the key (variable id, coefficient, ...) by increasing id after merging and dividing by the
  // gcd, or null for a row without variable terms or with a bound beyond int after rounding
  private Row row(ASTConstElem c, Map<IntVar, Integer> ids, List<Long> key) {
    int[] a = support.getIntArray((SimpleNode) c.jjtGetChild(0));
    IntVar[] v = support.getVarArray((SimpleNode) c.jjtGetChild(1));
    if (a == null || v == null || a.length != v.length) {
      return null;
    }
    long bound = support.getInt((ASTScalarFlatExpr) c.jjtGetChild(2));
    long fixed = 0;
    TreeMap<Integer, Long> terms = new TreeMap<>();
    for (int i = 0; i < v.length; i++) {
      if (v[i].singleton()) {
        fixed += (long) a[i] * v[i].value();
      } else if (a[i] != 0) {
        Integer id = ids.computeIfAbsent(v[i], x -> ids.size());
        terms.merge(id, (long) a[i], Long::sum);
      }
    }
    terms.values().removeIf(t -> t == 0);
    if (terms.isEmpty()) {
      return null;
    }
    long g = 0;
    for (long t : terms.values()) {
      g = gcd(g, Math.abs(t));
    }
    for (Map.Entry<Integer, Long> t : terms.entrySet()) {
      key.add((long) t.getKey());
      key.add(t.getValue() / g);
    }
    long b = Math.floorDiv(bound - fixed, g);
    if (g * b + fixed < Integer.MIN_VALUE || g * b + fixed > Integer.MAX_VALUE) {
      return null;
    }
    return new Row(c, g, b, fixed);
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
