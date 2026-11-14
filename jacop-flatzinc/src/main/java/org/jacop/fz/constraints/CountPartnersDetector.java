/*
 * CountPartnersDetector.java
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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.OrBool;
import org.jacop.constraints.XeqY;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * It finds variables whose every value is counted with a count that cannot be one, and posts that
 * each such variable equals one of its few possible partners. A model states {@code count(x, v) !=
 * 1}, or more generally {@code count(x, v)} in {0} or at least k, for each value v, so that a value
 * taken by one variable of x is taken by at least k of them: the groups of the XCSP3 problem
 * ButtonsScissors (2025 competition), where the buttons cut at one time are a cut of at least two
 * buttons. When the model also states {@code x[i] != x[j]} for most pairs (two buttons that no cut
 * joins), the variables x[i] may equal are few, its partners P(i), and the implied constraint
 * {@code sum(j in P(i)) (x[i] = x[j]) >= k - 1} (a clause for k = 2) holds. Under lazy clause
 * generation the counts explain each pruning with the values of all the other variables of x, 50 to
 * 70 literals there, while the implied clause is over the few partners only; with it JaCoP finds
 * the best known solutions of ButtonsScissors in seconds, where before it found none in 600 s.
 *
 * <p>The counts are {@code jacop_among(x, {v}, n)} and {@code jacop_count(x, v, n)}, with 1 (and
 * all values from 1 to k - 1) left out of the domain of n or stated out by {@code int_ne(n, c)} or
 * {@code int_lin_ne([a], [n], a * c)}. The disequalities are {@code int_ne(x, y)}, {@code
 * int_lin_ne([a, -a], [x, y], 0)} and the pairs of all-different constraints. A variable gets the
 * implied constraint only when every value of its domain is counted over the same list, and when
 * its partners are at most half of the other variables of the list: with more, the counts reason
 * about as well. The equalities x[i] = x[j] are reified, one Boolean per pair. All these
 * constraints are redundant (implied constraints in the sense of B. M. Smith, Modelling, in F.
 * Rossi, P. van Beek and T. Walsh (eds.), Handbook of Constraint Programming, Elsevier, 2006,
 * chapter 11).
 *
 * <p>Setting the system property {@code org.jacop.fz.countPartners} to false turns the detection
 * off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class CountPartnersDetector {

  // the most reified equalities the detector posts
  static final int MAX_PAIRS = 100_000;

  // the shortest list of counted variables
  static final int MIN_LIST = 3;

  private final Support support;

  // the counted lists: the variables, in the order of the first count over them, and the values
  // counted, each with the least count above zero that it may take (k)
  private static final class Group {
    final IntVar[] x;
    final Map<Integer, Integer> least = new HashMap<>();

    Group(IntVar[] x) {
      this.x = x;
    }
  }

  private final Map<Set<IntVar>, Group> groups = new LinkedHashMap<>();

  // a count (list, value, counter), read after the whole model is scanned
  private record Count(IntVar[] x, int v, IntVar n) {}

  private final List<Count> counts = new ArrayList<>();

  // values stated out of a variable's domain by int_ne(n, c) or int_lin_ne([a], [n], a * c)
  private final Map<IntVar, Set<Integer>> excluded = new IdentityHashMap<>();

  // the disequalities x != y
  private final Map<IntVar, Set<IntVar>> different = new IdentityHashMap<>();

  private final List<IntVar[]> alldifferent = new ArrayList<>();

  // the reified equality of each pair already posted
  private final Map<IntVar, Map<IntVar, IntVar>> equal = new IdentityHashMap<>();

  private int pairs;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public CountPartnersDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.countPartners is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.countPartners"));
  }

  /**
   * It scans the constraint items of the model and posts the partner constraints. It is called
   * after the constraints of the model are posted.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    if (counts.isEmpty()) {
      return;
    }
    for (Count c : counts) {
      count(c);
    }
    if (groups.isEmpty()) {
      return;
    }
    for (IntVar[] list : alldifferent) {
      for (int i = 0; i < list.length; i++) {
        for (int j = i + 1; j < list.length; j++) {
          different(list[i], list[j]);
        }
      }
    }
    int posted = 0;
    for (Group g : groups.values()) {
      posted += post(g);
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% count partners: "
              + groups.size()
              + " counted lists, "
              + posted
              + " variables with partners, "
              + pairs
              + " equalities");
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_among" -> {
        IntDomain s = support.getSetLiteral(node, 1);
        if (s.getSize() == 1) {
          counts.add(
              new Count(
                  support.getVarArray((SimpleNode) node.jjtGetChild(0)),
                  s.min(),
                  support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2))));
        }
      }
      case "jacop_count" ->
          counts.add(
              new Count(
                  support.getVarArray((SimpleNode) node.jjtGetChild(0)),
                  support.getInt((ASTScalarFlatExpr) node.jjtGetChild(1)),
                  support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2))));
      case "int_ne" -> {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        boolean c1 = p1.getType() == 0;
        boolean c2 = p2.getType() == 0;
        if (c1 && !c2) {
          exclude(support.getVariable(p2), support.getInt(p1));
        } else if (c2 && !c1) {
          exclude(support.getVariable(p1), support.getInt(p2));
        } else if (!c1) {
          different(support.getVariable(p1), support.getVariable(p2));
        }
      }
      case "int_lin_ne" -> {
        int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        if (a == null || a.length != v.length) {
          return;
        }
        if (a.length == 1 && a[0] != 0 && c % a[0] == 0) {
          exclude(v[0], c / a[0]);
        } else if (a.length == 2 && c == 0 && a[0] == -a[1] && a[0] != 0) {
          different(v[0], v[1]);
        }
      }
      case "jacop_alldiff", "jacop_alldistinct" ->
          alldifferent.add(support.getVarArray((SimpleNode) node.jjtGetChild(0)));
      default -> {
        // not read
      }
    }
  }

  private void exclude(IntVar n, int c) {
    excluded.computeIfAbsent(n, k -> new HashSet<>()).add(c);
  }

  private void different(IntVar x, IntVar y) {
    if (x != y) {
      different.computeIfAbsent(x, k -> Collections.newSetFromMap(new IdentityHashMap<>())).add(y);
      different.computeIfAbsent(y, k -> Collections.newSetFromMap(new IdentityHashMap<>())).add(x);
    }
  }

  // the least count above zero n may take, or 0 when 1 is possible (or n is not a count)
  private int least(IntVar n, int length) {
    Set<Integer> out = excluded.getOrDefault(n, Set.of());
    for (int k = 1; k <= Math.min(n.max(), length); k++) {
      if (n.domain.contains(k) && !out.contains(k)) {
        return k == 1 ? 0 : k;
      }
    }
    // no positive count possible: the value is not taken at all; partners are not needed
    return Integer.MAX_VALUE;
  }

  private void count(Count c) {
    if (c.x.length < MIN_LIST) {
      return;
    }
    Set<IntVar> key = new HashSet<>();
    for (IntVar v : c.x) {
      if (!key.add(v)) {
        // a variable twice: the counts are not over distinct variables
        return;
      }
    }
    int k = least(c.n, c.x.length);
    if (k == 0) {
      return;
    }
    Group g = groups.computeIfAbsent(key, s -> new Group(c.x));
    g.least.merge(c.v, k, Math::min);
  }

  // the variables of x posted with partners
  private int post(Group g) {
    IntVar[] x = g.x;
    int posted = 0;
    for (int i = 0; i < x.length; i++) {
      IntVar xi = x[i];
      if (xi.singleton()) {
        continue;
      }
      // every value of x[i] counted; k the least count of them
      int k = Integer.MAX_VALUE;
      boolean covered = true;
      for (ValueEnumeration e = xi.domain.valueEnumeration(); e.hasMoreElements(); ) {
        Integer least = g.least.get(e.nextElement());
        if (least == null) {
          covered = false;
          break;
        }
        k = Math.min(k, least);
      }
      if (!covered || k == Integer.MAX_VALUE) {
        continue;
      }
      Set<IntVar> ne = different.getOrDefault(xi, Set.of());
      List<IntVar> partners = new ArrayList<>();
      for (int j = 0; j < x.length; j++) {
        if (j != i && !ne.contains(x[j]) && xi.domain.isIntersecting(x[j].domain)) {
          partners.add(x[j]);
        }
      }
      if (partners.size() < k - 1) {
        // fewer partners than the count needs: other constraints fail it, nothing to add
        continue;
      }
      if (2 * partners.size() > x.length - 1 || pairs + partners.size() > MAX_PAIRS) {
        continue;
      }
      posted++;
      if (partners.size() == 1 && k == 2) {
        support.pose(new XeqY(xi, partners.getFirst()));
        continue;
      }
      IntVar[] b = new IntVar[partners.size()];
      for (int j = 0; j < b.length; j++) {
        b[j] = equality(xi, partners.get(j));
      }
      if (k == 2) {
        support.pose(
            new OrBool(b, support.dictionary.getConstant(1)).decompose(support.store).getFirst());
      } else {
        int[] w = new int[b.length];
        Arrays.fill(w, 1);
        support.pose(new LinearInt(b, w, ">=", k - 1));
      }
    }
    return posted;
  }

  // b <-> x = y, one per pair
  private IntVar equality(IntVar x, IntVar y) {
    IntVar b = equal.getOrDefault(x, Map.of()).get(y);
    if (b != null) {
      return b;
    }
    b = new IntVar(support.store, 0, 1);
    support.pose(support.fzXeqYreified(x, y, b));
    equal.computeIfAbsent(x, k -> new IdentityHashMap<>()).put(y, b);
    equal.computeIfAbsent(y, k -> new IdentityHashMap<>()).put(x, b);
    pairs++;
    return b;
  }
}
