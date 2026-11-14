/*
 * ObjectiveScaling.java
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

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ASTSolveExpr;
import org.jacop.fz.ASTSolveKind;
import org.jacop.fz.Node;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import org.jacop.fz.Tables;

/**
 * Divides an objective whose declared domain reaches beyond JaCoP's integer range by the greatest
 * common divisor its defining equation forces on it, so that it fits the range instead of being
 * narrowed to it.
 *
 * <p>MiniZinc declares an objective with the bounds it computes, such as 0..2147483646 for a sum of
 * costs, and JaCoP narrows such a domain to {@link IntDomain#MIN_INT}..{@link IntDomain#MAX_INT}.
 * Narrowing the worse side of the objective cuts off the solutions worse than the end of the range,
 * which are often all the solutions a fixed search finds (2023 unit-commitment L12 and L15: none in
 * 1200 s). When the objective {@code z} occurs in an equation {@code c*z + sum(a_i*x_i) = b}, every
 * value of {@code c*z} is a multiple of {@code G = gcd(a_i, b)}, so {@code z} is a multiple of
 * {@code g = G / gcd(G, c)}. The objective is then represented by {@code z' = z / g}: its domain
 * becomes {@code ceil(low/g)..floor(high/g)} and its coefficient in every linear row is multiplied
 * by {@code g}, which keeps every row exact. The solutions are those of the model, the order of the
 * objective's values is kept, and the output multiplies the value back by {@code g}. This is the
 * objective scaling of the CP-SAT presolve, which divides the objective by the greatest common
 * divisor of its coefficients (L. Perron, F. Didier, CP-SAT, Google OR-Tools,
 * https://developers.google.com/optimization, cp_model_presolve.cc).
 *
 * <p>The objective is scaled only when it, and every variable a declaration makes equal to it,
 * occurs in no constraint but the variable list of linear rows (int_lin_eq, int_lin_le, int_lin_ne,
 * also reified or implied), in no output array, and when the scaled domain fits JaCoP's range. The
 * model tree may be shared by the threads of a portfolio: its rows are rewritten once, under a
 * lock, and every thread scales its own variables.
 */
public final class ObjectiveScaling {

  // the scale found for a model tree, so that the rows of a shared tree are rewritten once
  // guards the rewriting of a model tree, which the threads of a portfolio may share
  private static final Object LOCK = new Object();

  private static final Map<SimpleNode, Long> SCALES =
      Collections.synchronizedMap(new WeakHashMap<>());

  private static final Set<String> LINEAR =
      Set.of(
          "int_lin_eq",
          "int_lin_le",
          "int_lin_ne",
          "int_lin_eq_reif",
          "int_lin_le_reif",
          "int_lin_ne_reif",
          "int_lin_eq_imp",
          "int_lin_le_imp",
          "int_lin_ne_imp");

  private final Support support;
  private final Tables dictionary;
  private final SimpleNode model;

  // the objective and the variables declared equal to it
  private final Map<IntVar, Boolean> family = new IdentityHashMap<>();

  private ObjectiveScaling(Support support, SimpleNode model) {
    this.support = support;
    this.dictionary = support.dictionary;
    this.model = model;
  }

  /**
   * Scales the objective of the model when its declared domain was narrowed to JaCoP's range and a
   * defining equation makes it a multiple of a number greater than one.
   *
   * @param support the support of the FlatZinc front end, with the variables of the model
   * @param model the root of the model tree
   * @return the scale of the objective, 1 when it is not scaled
   */
  public static long apply(Support support, SimpleNode model) {
    if (!support.dictionary.domainsClamped()
        || support.options != null && support.options.proof() != null) {
      // a proof derives the model as the FlatZinc file states it
      return 1;
    }
    synchronized (LOCK) {
      return new ObjectiveScaling(support, model).scale();
    }
  }

  private long scale() {
    IntVar objective = objective();
    if (objective == null || objective.singleton()) {
      return 1;
    }
    collectFamily(objective);
    boolean clamped = false;
    for (IntVar v : family.keySet()) {
      clamped |= dictionary.clampedDeclaredBounds(v) != null;
    }
    if (!clamped) {
      return 1;
    }
    Long known = SCALES.get(model);
    long g;
    if (known != null) {
      g = known;
    } else {
      List<ASTConstElem> rows = rows();
      g = rows == null ? 1 : divisor(rows);
      if (g > 1 && (scaledBounds(g) == null || !rewrite(rows, g))) {
        g = 1;
      }
      SCALES.put(model, g);
    }
    long[] scaled = g > 1 ? scaledBounds(g) : null;
    if (scaled == null) {
      return 1;
    }
    // the members are equal: each takes the scaled bounds common to all; the declarations equating
    // them stay satisfied
    for (IntVar v : family.keySet()) {
      v.setDomain((int) scaled[0], (int) scaled[1]);
      dictionary.scale(v, g);
    }
    return g;
  }

  // the variable of the objective, or null without one
  private IntVar objective() {
    for (int i = 0; i < model.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) model.jjtGetChild(i);
      if (node.getId() != ParserTreeConstants.JJTMODELEND) {
        continue;
      }
      SimpleNode solve = (SimpleNode) node.jjtGetChild(0);
      Node last = solve.jjtGetChild(solve.jjtGetNumChildren() - 1);
      if (!(last instanceof ASTSolveKind kind)
          || "satisfy".equals(kind.getKind())
          || !(kind.jjtGetChild(0) instanceof ASTSolveExpr e)) {
        return null;
      }
      if (e.getType() == 0) {
        return dictionary.getVariable(e.getIdent());
      }
      IntVar[] a = dictionary.getVariableArray(e.getIdent());
      return a == null ? null : a[e.getIndex()];
    }
    return null;
  }

  // the objective and, transitively, every variable a declaration equates with it
  private void collectFamily(IntVar objective) {
    family.put(objective, true);
    boolean grown = true;
    while (grown) {
      grown = false;
      for (IntVar[] pair : dictionary.declaredEqualities()) {
        if (family.containsKey(pair[0]) != family.containsKey(pair[1])) {
          family.put(pair[0], true);
          family.put(pair[1], true);
          grown = true;
        }
      }
    }
  }

  // the bounds of the scaled family, the tightest of its members' declared bounds divided by g;
  // null when a member has holes or the bounds do not fit JaCoP's range
  private long[] scaledBounds(long g) {
    long low = Long.MIN_VALUE;
    long high = Long.MAX_VALUE;
    for (IntVar v : family.keySet()) {
      if (v.getSize() != (long) v.max() - v.min() + 1) {
        return null;
      }
      long[] b = dictionary.declaredMemberBounds(v);
      low = Math.max(low, Math.ceilDiv(b[0], g));
      high = Math.min(high, Math.floorDiv(b[1], g));
    }
    if (low > high || low < IntDomain.MIN_INT || high > IntDomain.MAX_INT) {
      return null;
    }
    return new long[] {low, high};
  }

  // the linear rows the family occurs in, or null when it occurs anywhere else
  private List<ASTConstElem> rows() {
    for (var a : dictionary.outputArrays()) {
      for (var x : a) {
        if (x instanceof IntVar v && family.containsKey(v)) {
          return null;
        }
      }
    }
    List<ASTConstElem> rows = new ArrayList<>();
    boolean[] other = new boolean[1];
    support.forEachConstraint(
        model,
        node -> {
          for (int k = 0; k < node.jjtGetNumChildren(); k++) {
            List<IntVar> occurring = new ArrayList<>();
            occurrences(node.jjtGetChild(k), occurring);
            if (occurring.stream().anyMatch(family::containsKey)) {
              if (k == 1 && LINEAR.contains(node.getName())) {
                if (rows.isEmpty() || rows.getLast() != node) {
                  rows.add(node);
                }
              } else {
                other[0] = true;
              }
            }
          }
        });
    return other[0] ? null : rows;
  }

  private void occurrences(Node node, List<IntVar> out) {
    if (node instanceof ASTScalarFlatExpr e && (e.getType() == 2 || e.getType() == 3)) {
      IntVar[] array = dictionary.getVariableArray(e.getIdent());
      if (array != null) {
        out.addAll(List.of(array));
      } else {
        IntVar v = dictionary.getVariable(e.getIdent());
        if (v != null) {
          out.add(v);
        }
      }
    }
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      occurrences(node.jjtGetChild(i), out);
    }
  }

  // the number every value of the objective is a multiple of, by its equations; 1 for none
  private long divisor(List<ASTConstElem> rows) {
    long g = 1;
    for (ASTConstElem row : rows) {
      if (!"int_lin_eq".equals(row.getName())) {
        continue;
      }
      int[] a = support.getIntArray((SimpleNode) row.jjtGetChild(0));
      IntVar[] x = support.getVarArray((SimpleNode) row.jjtGetChild(1));
      if (a == null || a.length != x.length) {
        return 1;
      }
      long c = 0;
      long common = Math.abs((long) support.getInt((ASTScalarFlatExpr) row.jjtGetChild(2)));
      for (int i = 0; i < a.length; i++) {
        if (family.containsKey(x[i])) {
          c += a[i];
        } else {
          common = gcd(common, Math.abs((long) a[i]));
        }
      }
      if (c == 0 || common == 0) {
        continue;
      }
      long rowDivisor = common / gcd(common, Math.abs(c));
      g = g / gcd(g, rowDivisor) * rowDivisor;
      if (g > IntDomain.MAX_INT) {
        return 1;
      }
    }
    return g;
  }

  private static long gcd(long a, long b) {
    while (b != 0) {
      long t = a % b;
      a = b;
      b = t;
    }
    return a;
  }

  // multiplies the family's coefficients in the rows by g; false, changing nothing, on overflow
  private boolean rewrite(List<ASTConstElem> rows, long g) {
    List<int[]> scaled = new ArrayList<>();
    for (ASTConstElem row : rows) {
      int[] a = support.getIntArray((SimpleNode) row.jjtGetChild(0));
      IntVar[] x = support.getVarArray((SimpleNode) row.jjtGetChild(1));
      if (a == null || a.length != x.length) {
        return false;
      }
      int[] s = a.clone();
      for (int i = 0; i < a.length; i++) {
        if (family.containsKey(x[i])) {
          long v = a[i] * g;
          if (Math.abs(v) > IntDomain.MAX_INT) {
            return false;
          }
          s[i] = (int) v;
        }
      }
      scaled.add(s);
    }
    for (int r = 0; r < rows.size(); r++) {
      ASTConstElem row = rows.get(r);
      SimpleNode literal = new SimpleNode(ParserTreeConstants.JJTARRAYLITERAL);
      int[] s = scaled.get(r);
      for (int i = 0; i < s.length; i++) {
        ASTScalarFlatExpr e = new ASTScalarFlatExpr(ParserTreeConstants.JJTSCALARFLATEXPR);
        e.setType(0);
        e.setInt(s[i]);
        e.jjtSetParent(literal);
        literal.jjtAddChild(e, i);
      }
      literal.jjtSetParent(row);
      row.jjtAddChild(literal, 0);
    }
    return true;
  }
}
