/*
 * AffineSubstitution.java
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

package org.jacop.presolve;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;

/**
 * Rule 2 of the presolve design: affine equality substitution. Equalities between two variables
 * that define one of them as an affine function of the other, {@code x = p*y + q} with integer p
 * and q (for example x = y, x + c = z, c*x = z, x + y = c, or a longer linear equality whose other
 * variables are fixed), are collected in a union-find structure with offsets, so every variable of
 * a class is {@code a*r + b} for the class representative r. The derivation then gives the child
 * one variable per class: the representative's counterpart, whose domain is narrowed to the values
 * every member allows, and each member becomes that counterpart itself (an alias, a = 1 and b = 0)
 * or an {@link org.jacop.core.AffineView} of it. The equalities that defined the classes are not
 * copied.
 *
 * <p>Boolean variables only join classes of aliases with a Boolean representative, since a
 * constraint over Boolean variables needs a Boolean counterpart; with views switched off only
 * aliases are substituted. A pinned variable, which the child needs as a variable of its own, only
 * joins a class as its representative or as an alias.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class AffineSubstitution {

  /** Largest absolute factor or offset kept in a relation, so composing them cannot overflow. */
  private static final long LIMIT = 1L << 30;

  /**
   * The relation of a member to its representative.
   *
   * @param root the representative.
   * @param a the factor.
   * @param b the offset.
   */
  record Relation(IntVar root, int a, int b) {

    boolean identity() {
      return a == 1 && b == 0;
    }
  }

  /** A node of the union-find structure: var = a*parent + b. */
  private static final class Node {
    final IntVar var;
    final int order;
    Node parent;
    long a = 1;
    long b;
    // for a representative: Boolean variables in the class, and whether every relation is x = r
    int booleans;
    boolean aliasesOnly = true;
    // whether var is pinned, and for a representative the pinned variables in the class
    final boolean pinnedVar;
    int pinned;
    List<Node> members;

    Node(IntVar var, int order, boolean pinnedVar) {
      this.var = var;
      this.order = order;
      this.pinnedVar = pinnedVar;
      this.pinned = pinnedVar ? 1 : 0;
      this.booleans = var instanceof BooleanVar ? 1 : 0;
      this.members = new ArrayList<>(List.of(this));
    }
  }

  private final boolean views;
  private final Predicate<Var> excluded;
  private final Predicate<Var> pinned;
  private final Map<Var, Node> nodes = new IdentityHashMap<>();
  private final Set<Constraint> defining = Collections.newSetFromMap(new IdentityHashMap<>());

  private AffineSubstitution(boolean views, Predicate<Var> excluded, Predicate<Var> pinned) {
    this.views = views;
    this.excluded = excluded;
    this.pinned = pinned;
  }

  /**
   * Finds the affine classes of the equalities among constraints.
   *
   * @param constraints the constraints, in a deterministic order.
   * @param views true if members may become views; false for aliases only.
   * @param excluded variables that join no class.
   * @param pinned variables that join a class only as its representative or as an alias.
   * @return the classes.
   */
  static AffineSubstitution find(
      List<Constraint> constraints, boolean views, Predicate<Var> excluded, Predicate<Var> pinned) {
    AffineSubstitution s = new AffineSubstitution(views, excluded, pinned);
    for (Constraint c : constraints) {
      s.add(c);
    }
    return s;
  }

  /**
   * Tells whether a constraint is one of the equalities the classes replace.
   *
   * @param c a constraint.
   * @return true if the child does not need it.
   */
  boolean defines(Constraint c) {
    return defining.contains(c);
  }

  /**
   * Returns the number of equalities the classes replace.
   *
   * @return the number of defining constraints.
   */
  int definingCount() {
    return defining.size();
  }

  /**
   * Returns the relation of a variable to its representative.
   *
   * @param v a variable.
   * @return the relation, or null if the variable is a representative or in no class.
   */
  Relation relation(Var v) {
    Node n = nodes.get(v);
    if (n == null) {
      return null;
    }
    Node r = find(n);
    if (r == n) {
      return null;
    }
    return new Relation(r.var, (int) n.a, (int) n.b);
  }

  /**
   * Tells whether a variable represents a class with other members.
   *
   * @param v a variable.
   * @return true if it is a representative.
   */
  boolean isRoot(Var v) {
    Node n = nodes.get(v);
    return n != null && n.parent == null && n.members.size() > 1;
  }

  /**
   * Returns the representative of a variable's class.
   *
   * @param v a variable.
   * @return the representative, or the variable itself if it is in no class.
   */
  Var root(Var v) {
    Node n = nodes.get(v);
    return n == null ? v : find(n).var;
  }

  /**
   * Returns the members of a class, the representative first.
   *
   * @param root a representative.
   * @return the variables of its class.
   */
  List<IntVar> members(Var root) {
    Node n = nodes.get(root);
    List<IntVar> result = new ArrayList<>();
    for (Node m : n.members) {
      result.add(m.var);
    }
    return result;
  }

  private Node node(IntVar v) {
    return nodes.computeIfAbsent(v, k -> new Node(v, nodes.size(), pinned.test(v)));
  }

  private static Node find(Node n) {
    if (n.parent == null) {
      return n;
    }
    Node r = find(n.parent);
    if (n.parent != r) {
      // n = a*p + b and p = a'*r + b' give n = a*a'*r + a*b' + b; the limits keep this exact
      Node p = n.parent;
      n.b = n.a * p.b + n.b;
      n.a = n.a * p.a;
      n.parent = r;
    }
    return r;
  }

  private void add(Constraint c) {
    LinearForm f;
    if (c instanceof LinearInt li) {
      // a subclass other than LinearIntDom may enforce more than its linear relation
      boolean plain = li.getClass() == LinearInt.class || li.getClass() == LinearIntDom.class;
      f = plain ? li.linearRelation() : null;
    } else {
      f = c instanceof LinearExplainable le ? le.linearForm() : null;
    }
    if (f == null || f.relation() != LinearForm.EQ) {
      return;
    }
    // sum of w*x = c over the variables not fixed, with repeated variables merged
    IntVar[] xs = new IntVar[2];
    long[] ws = new long[2];
    int n = 0;
    long rhs = f.c();
    IntVar[] vars = f.vars();
    long[] weights = f.weights();
    for (int i = 0; i < vars.length; i++) {
      IntVar x = vars[i];
      if (x.singleton()) {
        rhs -= weights[i] * x.value();
        continue;
      }
      int k = 0;
      while (k < n && xs[k] != x) {
        k++;
      }
      if (k == n) {
        if (n == 2) {
          return;
        }
        xs[n] = x;
        n++;
      }
      ws[k] += weights[i];
    }
    if (n != 2 || ws[0] == 0 || ws[1] == 0 || !substitutable(xs[0]) || !substitutable(xs[1])) {
      return;
    }
    // w0*x0 + w1*x1 = rhs: x0 = p*x1 + q when w0 divides w1 and rhs, or the other way round
    if (ws[1] % ws[0] == 0 && rhs % ws[0] == 0) {
      if (union(xs[0], -ws[1] / ws[0], xs[1], rhs / ws[0])) {
        defining.add(c);
      }
    } else if (ws[0] % ws[1] == 0 && rhs % ws[1] == 0) {
      if (union(xs[1], -ws[0] / ws[1], xs[0], rhs / ws[1])) {
        defining.add(c);
      }
    }
  }

  private boolean substitutable(IntVar x) {
    return (x.getClass() == IntVar.class || x.getClass() == BooleanVar.class) && !excluded.test(x);
  }

  private static boolean small(long v) {
    return -LIMIT < v && v < LIMIT;
  }

  /**
   * Records x = p*y + q.
   *
   * @return true if the relation is now implied by the classes, so its constraint can go.
   */
  private boolean union(IntVar x, long p, IntVar y, long q) {
    if (!small(p) || !small(q)) {
      return false;
    }
    Node nx = node(x);
    Node ny = node(y);
    Node rx = find(nx);
    Node ry = find(ny);
    // x = a1*rx + b1 and y = a2*ry + b2, so a1*rx + b1 = p*a2*ry + p*b2 + q
    long a1 = nx.a;
    long b1 = nx.b;
    long pa2 = p * ny.a;
    long rest = p * ny.b + q - b1;
    if (!small(pa2) || !small(rest)) {
      return false;
    }
    if (rx == ry) {
      // a cycle: the relation is implied only if it holds for every value of the representative
      return a1 == pa2 && rest == 0;
    }
    // rx = (pa2*ry + rest) / a1, or ry = (a1*rx - rest) / pa2
    boolean rxUnder = pa2 % a1 == 0 && rest % a1 == 0;
    boolean ryUnder = a1 % pa2 == 0 && rest % pa2 == 0;
    if (rxUnder && ryUnder && prefer(rx, ry)) {
      rxUnder = false;
    }
    if (rxUnder && attach(rx, pa2 / a1, rest / a1, ry)) {
      return true;
    }
    return ryUnder && attach(ry, a1 / pa2, -rest / pa2, rx);
  }

  /** Tells whether r should stay the representative rather than s. */
  private static boolean prefer(Node r, Node s) {
    boolean rb = r.var instanceof BooleanVar;
    boolean sb = s.var instanceof BooleanVar;
    if (rb != sb) {
      return rb;
    }
    if (r.pinned != s.pinned) {
      return r.pinned > s.pinned;
    }
    int rd = r.var.sizeConstraints();
    int sd = s.var.sizeConstraints();
    if (rd != sd) {
      return rd > sd;
    }
    return r.order < s.order;
  }

  /** Makes child = a*root + b, when the merged class stays one the derivation can substitute. */
  private boolean attach(Node child, long a, long b, Node root) {
    if (!small(a) || !small(b)) {
      return false;
    }
    boolean alias = a == 1 && b == 0;
    boolean aliasesOnly = root.aliasesOnly && child.aliasesOnly && alias;
    int booleans = root.booleans + child.booleans;
    if (booleans > 0 && (!aliasesOnly || !(root.var instanceof BooleanVar))) {
      return false;
    }
    int pinnedCount = root.pinned + child.pinned;
    if (!aliasesOnly && (pinnedCount > 1 || pinnedCount == 1 && !root.pinnedVar)) {
      return false;
    }
    if (!aliasesOnly && !views) {
      return false;
    }
    for (Node m : child.members) {
      long ma = m.a * a;
      long mb = m.a * b + m.b;
      if (m != child && (!small(ma) || !small(mb))) {
        return false;
      }
    }
    // the members of child keep child as parent until find compresses them
    child.parent = root;
    child.a = a;
    child.b = b;
    root.members.addAll(child.members);
    child.members = null;
    root.booleans = booleans;
    root.pinned = pinnedCount;
    root.aliasesOnly = aliasesOnly;
    return true;
  }
}
