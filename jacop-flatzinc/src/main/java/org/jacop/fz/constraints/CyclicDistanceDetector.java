/*
 * CyclicDistanceDetector.java
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
import java.util.Arrays;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It adds the wrapped difference of a cyclic distance. A distance on a cycle of c positions, m =
 * min(a, c - a) with a = |e| and -c < e < c (FlatZinc: int_abs(e, a), int_lin_eq([-1, -1], [a, b],
 * -c), int_min(a, b, m)), is also m = |f| with f = e + c * k, k in -1..1 and -c/2 <= f <= c/2: the
 * difference e taken modulo c into the interval around zero. The minimum prunes nothing on e until
 * a or b is decided, so a bound on m (the cyclic bandwidth of XCSP CyclicBandwidth, max of such
 * distances over the edges of a graph) does not narrow the positions of the nodes; once k is fixed,
 * the linear equation does, by bounds. Free search labels k and f. When a and b occur in nothing
 * else (no other constraint, the objective, an annotation or the output), the three constraints are
 * replaced and a and b dropped, and a difference e defined by a linear equation and used only there
 * is substituted by its definition (x - y + c * k = f); otherwise the new constraints are added
 * next to them. On XCSP 2022 CyclicBandwidth at 600 s free search reaches 29 instead of 105 on
 * caterpillar35, 24 instead of 64 on caterpillar29 and 34 instead of 112 on mesh2D25x26, but the
 * lower bounds of lazy clause generation grow more slowly than over the minimum, so caterpillar13,
 * 16 and 19, proved in 21 to 336 s without it, are not proved in 600 s.
 *
 * <p>It is off by default; setting the system property {@code org.jacop.fz.cyclicDistance} to true
 * turns it on.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class CyclicDistanceDetector implements ParserTreeConstants {

  private final Support support;

  // a = |e|, by a
  private record Absolute(IntVar e, SimpleNode node) {}

  private final Map<IntVar, Absolute> absolutes = new IdentityHashMap<>();

  // the complement of a on the cycle of c positions, keyed by the complement
  private record Complement(IntVar a, int c, SimpleNode node) {}

  // the linear equation that defines e: sign * e + sum weights * others = rhs, keyed by e
  private static final class Definition {
    private final IntVar[] others;
    private final int[] weights;
    private final int sign;
    private final int rhs;
    private final SimpleNode node;

    Definition(IntVar[] others, int[] weights, int sign, int rhs, SimpleNode node) {
      this.others = others;
      this.weights = weights;
      this.sign = sign;
      this.rhs = rhs;
      this.node = node;
    }

    IntVar[] others() {
      return others;
    }

    int[] weights() {
      return weights;
    }

    int sign() {
      return sign;
    }

    int rhs() {
      return rhs;
    }

    SimpleNode node() {
      return node;
    }
  }

  private final Map<IntVar, Definition> definitions = new IdentityHashMap<>();

  private final Map<IntVar, Integer> occurrences = new IdentityHashMap<>();

  private final Set<SimpleNode> replaced = new HashSet<>();

  private final Set<Var> removed = new HashSet<>();

  private final Map<IntVar, List<Complement>> complements = new IdentityHashMap<>();

  private final List<ASTConstElem> minimums = new ArrayList<>();

  private int added;

  private int replacedDistances;

  /**
   * It creates a detector posting through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public CyclicDistanceDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return true if the system property org.jacop.fz.cyclicDistance is true.
   */
  public static boolean enabled() {
    return Boolean.getBoolean("org.jacop.fz.cyclicDistance");
  }

  /**
   * It posts f = e + c * k and m = |f| for each cyclic distance m of the model.
   *
   * @param astTree the root of the parsed model.
   * @return the constraint nodes it replaces, which must not be posted.
   */
  public Set<SimpleNode> detect(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          support.checkTimeOut();
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            collect((ASTConstElem) item);
          }
        }
      } else if (node.getId() == JJTSOLVEITEM || node.getId() == JJTMODELEND) {
        // variables of the search annotations and the objective stay
        countAll(node);
      }
    }
    if (absolutes.isEmpty() || complements.isEmpty()) {
      return replaced;
    }
    for (ASTConstElem node : minimums) {
      IntVar p = variable(node, 0);
      IntVar q = variable(node, 1);
      IntVar m = variable(node, 2);
      if (!post(p, q, m, node)) {
        post(q, p, m, node);
      }
    }
    if (support.options.debug()) {
      FzConsole.println("% cyclic distances: " + added + ", replaced " + replacedDistances);
    }
    return replaced;
  }

  /**
   * It returns the variables a and b of the replaced distances, left without constraints.
   *
   * @return the removed variables.
   */
  public Set<Var> removed() {
    return removed;
  }

  // m = min(a, b) with a = |e| and b = c - a
  private boolean post(IntVar a, IntVar b, IntVar m, SimpleNode min) {
    Absolute abs = absolutes.get(a);
    List<Complement> cs = complements.get(b);
    if (abs == null || cs == null || abs.e() == m || a == m || b == m) {
      return false;
    }
    IntVar e = abs.e();
    for (Complement cm : cs) {
      int c = cm.c();
      if (cm.a() != a || c < 2 || e.min() <= -c || e.max() >= c) {
        continue;
      }
      int h = c / 2;
      IntVar k = new IntVar(support.store, -1, 1);
      IntVar f = new IntVar(support.store, -h, h);
      boolean replace =
          occurrences.getOrDefault(a, 0) == 3
              && occurrences.getOrDefault(b, 0) == 2
              && abs.node() != null
              && cm.node() != null
              && free(a)
              && free(b);
      Definition d =
          replace && occurrences.getOrDefault(e, 0) == 2 && free(e) ? definitions.get(e) : null;
      if (d != null && d.node() != null && !replaced.contains(d.node())) {
        // e = w_e (r - sum w_i v_i) substituted: sum (-w_e w_i) v_i + c k - f = -w_e r
        IntVar[] v = Arrays.copyOf(d.others(), d.others().length + 2);
        int[] w = new int[v.length];
        for (int i = 0; i < d.others().length; i++) {
          w[i] = -d.sign() * d.weights()[i];
        }
        v[v.length - 2] = k;
        w[v.length - 2] = c;
        v[v.length - 1] = f;
        w[v.length - 1] = -1;
        support.pose(new LinearInt(v, w, "==", -d.sign() * d.rhs()));
        replaced.add(d.node());
        removed.add(e);
      } else {
        support.pose(new LinearInt(new IntVar[] {e, k, f}, new int[] {1, c, -1}, "==", 0));
      }
      support.pose(new AbsXeqY(f, m));
      // free search labels k and f, as it labels the variables of a model that states them
      support.dictionary.addSearchVar(k);
      support.dictionary.addSearchVar(f);
      added++;
      if (replace) {
        replaced.add(min);
        replaced.add(abs.node());
        replaced.add(cm.node());
        removed.add(a);
        removed.add(b);
        replacedDistances++;
      }
      return true;
    }
    return false;
  }

  // in no alias and not output
  private boolean free(IntVar x) {
    return !support.dictionary.aliasTable.containsKey(x)
        && !support.dictionary.aliasTable.containsValue(x)
        && !support.dictionary.isOutput(x);
  }

  private void collect(ASTConstElem node) {
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      PartialCopyDetector.countVariables(support, (SimpleNode) node.jjtGetChild(i), occurrences);
    }
    switch (node.getName()) {
      case "int_abs" -> absolute(node);
      case "int_lin_eq" -> {
        complement(node);
        definition(node);
      }
      case "int_min" -> minimums.add(node);
      default -> {
        // none of the parts
      }
    }
  }

  private void absolute(ASTConstElem node) {
    IntVar a = variable(node, 1);
    IntVar e = variable(node, 0);
    // a domain of a narrower than |e| is a constraint the replacement would drop
    Absolute old = absolutes.putIfAbsent(a, new Absolute(e, holdsAbsolute(a, e) ? node : null));
    if (old != null) {
      // two definitions: neither is replaced
      absolutes.put(a, new Absolute(old.e(), null));
    }
  }

  private void countAll(SimpleNode node) {
    PartialCopyDetector.countVariables(support, node, occurrences);
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      countAll((SimpleNode) node.jjtGetChild(i));
    }
  }

  // sum w_i v_i + sign * e = rhs, by e, for each e of coefficient 1 or -1 that occurs once
  private void definition(ASTConstElem node) {
    int[] w = support.getIntArray(child(node, 0));
    IntVar[] v = support.getVarArray(child(node, 1));
    int rhs = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    for (int j = 0; j < v.length; j++) {
      if (Math.abs(w[j]) != 1) {
        continue;
      }
      IntVar[] others = new IntVar[v.length - 1];
      int[] ow = new int[v.length - 1];
      boolean once = true;
      int n = 0;
      for (int i = 0; i < v.length; i++) {
        if (i != j) {
          once &= v[i] != v[j];
          others[n] = v[i];
          ow[n] = w[i];
          n++;
        }
      }
      if (once) {
        // a domain of e narrower than its definition is a constraint the substitution would drop
        SimpleNode where = holdsDefinition(v[j], others, ow, w[j], rhs) ? node : null;
        Definition old = definitions.put(v[j], new Definition(others, ow, w[j], rhs, where));
        if (old != null) {
          // two definitions: neither is substituted
          definitions.put(v[j], new Definition(others, ow, w[j], rhs, null));
        }
      }
    }
  }

  // b = c - a written as [s, s] * [a, b] = s * c, s = 1 or -1, in either order
  private void complement(ASTConstElem node) {
    int[] w = support.getIntArray(child(node, 0));
    IntVar[] v = support.getVarArray(child(node, 1));
    if (w.length != 2 || w[0] != w[1] || Math.abs(w[0]) != 1 || v[0] == v[1]) {
      return;
    }
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)) * w[0];
    // keyed by b = c - a; a domain of b narrower than c - a is a constraint the replacement would
    // drop
    complements
        .computeIfAbsent(v[1], z -> new ArrayList<>())
        .add(new Complement(v[0], c, holdsComplement(v[1], v[0], c) ? node : null));
    complements
        .computeIfAbsent(v[0], z -> new ArrayList<>())
        .add(new Complement(v[1], c, holdsComplement(v[0], v[1], c) ? node : null));
  }

  // the domain of a contains |v| for every v of the domain of e
  private static boolean holdsAbsolute(IntVar a, IntVar e) {
    IntDomain d = e.dom();
    for (int i = 0; i < d.noIntervals(); i++) {
      int lo = d.leftElement(i);
      int hi = d.rightElement(i);
      boolean holds =
          lo >= 0
              ? a.dom().contains(lo, hi)
              : hi <= 0 ? a.dom().contains(-hi, -lo) : a.dom().contains(0, Math.max(-lo, hi));
      if (!holds) {
        return false;
      }
    }
    return true;
  }

  // the domain of b contains c - v for every v of the domain of a
  private static boolean holdsComplement(IntVar b, IntVar a, int c) {
    IntDomain d = a.dom();
    for (int i = 0; i < d.noIntervals(); i++) {
      long lo = (long) c - d.rightElement(i);
      long hi = (long) c - d.leftElement(i);
      if (lo < b.min() || hi > b.max() || !b.dom().contains((int) lo, (int) hi)) {
        return false;
      }
    }
    return true;
  }

  // the domain of e contains every value of sign * (rhs - sum w_i v_i) over the bounds of the v_i
  private static boolean holdsDefinition(IntVar e, IntVar[] v, int[] w, int sign, int rhs) {
    long lo = 0;
    long hi = 0;
    for (int i = 0; i < v.length; i++) {
      long p = (long) w[i] * v[i].min();
      long q = (long) w[i] * v[i].max();
      lo += Math.min(p, q);
      hi += Math.max(p, q);
    }
    long min = sign > 0 ? rhs - hi : lo - rhs;
    long max = sign > 0 ? rhs - lo : hi - rhs;
    return min >= e.min() && max <= e.max() && e.dom().contains((int) min, (int) max);
  }

  private IntVar variable(SimpleNode node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }
}
