/*
 * AbsoluteDifferenceDetector.java
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
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusCneqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It replaces an absolute difference used only to exclude a few values, {@code t = x - y} and
 * {@code a = |t|} where t and a occur nowhere else, by the constraints on x - y that the domains of
 * t and a state: {@code x - y != d} for each value d of the range of x - y that they exclude inside
 * it, and bounds on x - y for the values they exclude at its ends. MiniZinc flattens {@code
 * abs(q[i] - q[j]) != j - i} of the n-queens model this way: a = |t| gets the hole at j - i, and
 * the model keeps 2 auxiliary variables and 2 constraints per pair (n = 100: 9,900 variables and
 * 9,900 constraints besides the 100 queens, over 3,000 propagations per search node). The
 * disequalities {@code x - y != d} are those of the diagonals, which {@link AlldifferentDetector}
 * then finds as all-different cliques with offsets; up to {@link #maxHoles()} values cut off at
 * each end of the range are given to it as well, though the bounds already exclude them, since the
 * corner pairs of the diagonals exclude only their largest difference.
 *
 * <p>The rewrite is exact: x - y takes, within the bounds of x and y, exactly the values w for
 * which t has a value with {@code a = |t|} in the domain of a. It is considered only when x - y
 * ranges over at most {@link #MAX_RANGE} values and at most {@link #maxHoles()} values inside the
 * range are excluded, and made only when every disequality inside the range becomes part of an
 * all-different constraint (or there is none): a few disequalities per pair alone propagate no
 * better than |t| and explain worse under lazy clause generation. Not with {@code --proof}. Setting
 * the system property {@code org.jacop.fz.absoluteDifference} to false turns it off, and to all
 * makes every rewrite found.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class AbsoluteDifferenceDetector implements ParserTreeConstants {

  private static final Set<String> GATE_KINDS = Set.of("int_abs");

  private static final String PROPERTY = "org.jacop.fz.absoluteDifference";

  /** The most values of x - y that are read. */
  static final int MAX_RANGE = 1 << 16;

  private final Support support;

  // a = |t|, by t
  private record Absolute(IntVar a, SimpleNode node) {}

  // q * t + p * x - p * y = c with |p| = |q|, by t; node is null for two definitions
  private record Definition(IntVar x, IntVar y, int p, int q, int c, SimpleNode node) {}

  /**
   * A disequality x - y != d of a rewrite, with the node that stands for it in clique detection.
   */
  private record Disequality(IntVar x, IntVar y, int d, SimpleNode token) {}

  // in the order of the model, so that the cliques found from the disequalities do not depend on
  // identity hash codes
  private final Map<IntVar, Absolute> absolutes = new LinkedHashMap<>();

  private final Map<IntVar, Definition> definitions = new IdentityHashMap<>();

  private final Map<IntVar, Integer> occurrences = new IdentityHashMap<>();

  private final Set<SimpleNode> replaced = Collections.newSetFromMap(new IdentityHashMap<>());

  private final Set<Var> removed = new LinkedHashSet<>();

  private final List<Disequality> disequalities = new ArrayList<>();

  // a rewrite found: the two constraints, the variables, the bounds on x - y that cut values off
  // (null when none) and the disequalities inside the range
  private record Rewrite(
      SimpleNode abs,
      SimpleNode definition,
      IntVar t,
      IntVar a,
      IntVar x,
      IntVar y,
      Integer first,
      Integer last,
      List<Disequality> holes) {}

  private final List<Rewrite> rewrites = new ArrayList<>();

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public AbsoluteDifferenceDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.absoluteDifference is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty(PROPERTY));
  }

  /**
   * It tells if every rewrite found is made, also when its disequalities are in no all-different
   * constraint: the system property org.jacop.fz.absoluteDifference is all.
   *
   * @return true if the system property org.jacop.fz.absoluteDifference is all.
   */
  public static boolean all() {
    return "all".equalsIgnoreCase(System.getProperty(PROPERTY));
  }

  /**
   * It returns the most values inside the range of x - y that a rewrite excludes by disequalities:
   * the system property org.jacop.fz.absoluteDifference.maxHoles, 8 by default.
   *
   * @return the most disequalities of one rewrite.
   */
  public static int maxHoles() {
    return Integer.getInteger(PROPERTY + ".maxHoles", 8);
  }

  /**
   * It finds the absolute differences that can be rewritten. Nothing is posted or replaced yet:
   * {@link #feed(AlldifferentDetector)} gives their disequalities to the all-different detection,
   * and {@link #apply(Set)} then makes the rewrites whose disequalities all became part of an
   * all-different constraint, or that have none.
   *
   * @param astTree the root of the parsed model.
   * @param skipped the constraint nodes already replaced by other detectors.
   */
  public void detect(SimpleNode astTree, Set<SimpleNode> skipped) {
    // the differences it rewrites are int_abs constraints: a model without them is not read
    if (!support.hasConstraint(astTree, GATE_KINDS)) {
      return;
    }
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          support.checkTimeOut();
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            collect((ASTConstElem) item, skipped);
          }
        }
      } else if (node.getId() == JJTSOLVEITEM || node.getId() == JJTMODELEND) {
        // variables of the search annotations and the objective stay
        countAll(node);
      }
    }
    for (Map.Entry<IntVar, Absolute> e : absolutes.entrySet()) {
      rewrite(e.getKey(), e.getValue());
    }
  }

  /**
   * It returns the variables t and a of the rewritten differences, left without constraints.
   *
   * @return the removed variables.
   */
  public Set<Var> removed() {
    return removed;
  }

  /**
   * It gives the disequalities of the rewrites to the all-different detection as stated
   * disequalities, so that cliques may replace them.
   *
   * @param alldifferent the all-different detection, before it runs.
   */
  public void feed(AlldifferentDetector alldifferent) {
    for (Disequality d : disequalities) {
      alldifferent.statedDisequality(d.x(), d.y(), d.d(), d.token());
    }
  }

  /**
   * It makes the rewrites whose disequalities inside the range of x - y are all replaced by
   * all-different constraints, or that have none: it posts their bounds on x - y and returns their
   * constraints, which must not be posted. The others keep their constraints and variables, since a
   * few disequalities per pair propagate no better than |t| and explain worse under lazy clause
   * generation (Rlfap-graph-01, XCSP 2022: about 5 per pair, no clique, the optimum proved in 13 s
   * without the rewrite and not in 240 s with it).
   *
   * @param inCliques the replaced constraint nodes of the all-different detection.
   * @return the constraint nodes it replaces.
   */
  public Set<SimpleNode> apply(Set<SimpleNode> inCliques) {
    int bounds = 0;
    int holes = 0;
    for (Rewrite r : rewrites) {
      if (!all() && !r.holes().stream().allMatch(d -> inCliques.contains(d.token()))) {
        continue;
      }
      if (r.first() != null) {
        // x - y >= first, that is y + first <= x
        support.pose(new XplusClteqZ(r.y(), r.first(), r.x()));
        bounds++;
      }
      if (r.last() != null) {
        // x - y <= last, that is x - last <= y
        support.pose(new XplusClteqZ(r.x(), -r.last(), r.y()));
        bounds++;
      }
      holes += r.holes().size();
      for (Disequality d : r.holes()) {
        if (!inCliques.contains(d.token())) {
          // x - y != d, that is y + d != x
          support.pose(new XplusCneqZ(d.y(), d.d(), d.x()));
        }
      }
      replaced.add(r.abs());
      replaced.add(r.definition());
      removed.add(r.t());
      removed.add(r.a());
    }
    if (support.options.debug() && !rewrites.isEmpty()) {
      FzConsole.println(
          "% absolute differences rewritten: "
              + replaced.size() / 2
              + " of "
              + rewrites.size()
              + ", "
              + holes
              + " disequalities in cliques, "
              + bounds
              + " bounds");
    }
    rewrites.clear();
    disequalities.clear();
    return replaced;
  }

  private void rewrite(IntVar t, Absolute abs) {
    IntVar a = abs.a();
    Definition def = definitions.get(t);
    if (abs.node() == null
        || def == null
        || def.node() == null
        || a == t
        || occurrences.getOrDefault(t, 0) != 2
        || occurrences.getOrDefault(a, 0) != 1
        || !free(t)
        || !free(a)) {
      return;
    }
    IntVar x = def.x();
    IntVar y = def.y();
    if (x == y || x == t || y == t || x == a || y == a || def.c() % def.q() != 0) {
      return;
    }
    long lo = (long) x.min() - y.max();
    long hi = (long) x.max() - y.min();
    if (hi - lo + 1 > MAX_RANGE) {
      return;
    }
    // t = k - s * (x - y)
    long k = def.c() / def.q();
    long s = def.p() / def.q();
    int first = Integer.MAX_VALUE;
    int last = Integer.MIN_VALUE;
    List<Integer> holes = new ArrayList<>();
    for (long w = lo; w <= hi; w++) {
      long v = k - s * w;
      boolean allowed =
          v >= t.min()
              && v <= t.max()
              && t.domain.contains((int) v)
              && Math.abs(v) <= a.max()
              && a.domain.contains((int) Math.abs(v));
      if (allowed) {
        if (first == Integer.MAX_VALUE) {
          first = (int) w;
        } else {
          for (int h = last + 1; h < w; h++) {
            holes.add(h);
          }
          if (holes.size() > maxHoles()) {
            return;
          }
        }
        last = (int) w;
      }
    }
    if (first == Integer.MAX_VALUE) {
      // no value of x - y is allowed: the constraints are posted and fail
      return;
    }
    List<Disequality> inside = new ArrayList<>();
    for (int h : holes) {
      inside.add(new Disequality(x, y, h, new SimpleNode(JJTCONSTELEM)));
    }
    disequalities.addAll(inside);
    // the values cut off at the ends are disequalities too, which may complete a clique: the
    // corner pair of a queens diagonal has its only excluded difference at the end of the range
    for (long w = lo; w < first && w < lo + maxHoles(); w++) {
      disequalities.add(new Disequality(x, y, (int) w, new SimpleNode(JJTCONSTELEM)));
    }
    for (long w = hi; w > last && w > hi - maxHoles(); w--) {
      disequalities.add(new Disequality(x, y, (int) w, new SimpleNode(JJTCONSTELEM)));
    }
    rewrites.add(
        new Rewrite(
            abs.node(),
            def.node(),
            t,
            a,
            x,
            y,
            first > lo ? first : null,
            last < hi ? last : null,
            inside));
  }

  // in no alias, no declared equality and not output
  private boolean free(IntVar x) {
    return !support.dictionary.aliasTable.containsKey(x)
        && !support.dictionary.aliasTable.containsValue(x)
        && !support.dictionary.isDeclaredEqual(x)
        && !support.dictionary.isOutput(x);
  }

  private void collect(ASTConstElem node, Set<SimpleNode> skipped) {
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      PartialCopyDetector.countVariables(support, (SimpleNode) node.jjtGetChild(i), occurrences);
    }
    if (skipped.contains(node)) {
      return;
    }
    switch (node.getName()) {
      case "int_abs" -> absolute(node);
      case "int_lin_eq" -> definition(node);
      default -> {
        // not a part
      }
    }
  }

  private void absolute(ASTConstElem node) {
    ASTScalarFlatExpr p0 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    if (p0.getType() == 0 || p1.getType() == 0) {
      return;
    }
    IntVar t = support.getVariable(p0);
    IntVar a = support.getVariable(p1);
    if (t.singleton() || a.singleton()) {
      return;
    }
    Absolute old = absolutes.putIfAbsent(t, new Absolute(a, node));
    if (old != null) {
      absolutes.put(t, new Absolute(old.a(), null));
    }
  }

  // q * t + p * x - p * y = c with |p| = |q|, by t, for each of the three terms
  private void definition(ASTConstElem node) {
    int[] w = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    if (w == null || w.length != 3) {
      return;
    }
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (v == null || v.length != 3 || v[0] == v[1] || v[1] == v[2] || v[0] == v[2]) {
      return;
    }
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    for (int r = 0; r < 3; r++) {
      int i = (r + 1) % 3;
      int j = (r + 2) % 3;
      int q = w[r];
      int p = w[i];
      if (q != 0 && p != 0 && w[j] == -p && (p == q || p == -q) && q != Integer.MIN_VALUE) {
        Definition old = definitions.put(v[r], new Definition(v[i], v[j], p, q, c, node));
        if (old != null) {
          definitions.put(v[r], new Definition(v[i], v[j], p, q, c, null));
        }
      }
    }
  }

  private void countAll(SimpleNode node) {
    PartialCopyDetector.countVariables(support, node, occurrences);
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      countAll((SimpleNode) node.jjtGetChild(i));
    }
  }
}
