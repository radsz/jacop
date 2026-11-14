/*
 * EnforcementInliner.java
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
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Eliminates the 0/1 controls of half-reified constraints whose every other occurrence is a
 * positive literal of a clause: the enforcement-literal reductions of CP-SAT's presolve (Perron,
 * Didier and Gay, "The CP-SAT-LP solver", CP 2023, and the OR-Tools sources), which are bounded
 * variable elimination of the control (Een and Biere, "Effective preprocessing in SAT through
 * variable and clause elimination", SAT 2005). Such a control {@code b} of {@code b -> C} can
 * always be as large as C allows, so it is replaced:
 *
 * <ul>
 *   <li>by the literal {@code L} when C is a literal of a 0/1 variable ({@code int_eq_imp(x, 1,
 *       b)}, {@code int_ne_imp(x, 1, b)}, {@code bool_eq_imp(x, true, b)}): its clauses get L in
 *       place of b and {@code b -> C} goes;
 *   <li>when its only clause is binary, {@code l \/ b}: the clause goes and C is posted as {@code
 *       not l -> C}, with the control negated ({@link org.jacop.constraints.ImpliesNot}) when l is
 *       a positive literal.
 * </ul>
 *
 * <p>MiniZinc writes a disjunction of two constraints, as the precedences of job shop and RCPSP/max
 * models, as {@code b1 -> C1, b2 -> C2, b1 \/ b2}; it becomes {@code b1 -> C1, not b1 -> C2}. The
 * literals of a time-expanded model (ma-path-finding: {@code int_ne_imp(B, 1, b1), b2 -> C, b1 \/
 * b2}) become {@code B -> C}. Each removes a variable, a clause and a propagation step, and no
 * reasoning: unlike half-reification nothing is weakened.
 *
 * <p>Variables of the solve item, output variables and variables of other constraints are kept. The
 * reduction keeps every solution projected on the other variables but not the values of the
 * controls, so it is off for all-solution search; it is also off under {@code --proof}, and with
 * {@code -Dorg.jacop.fz.enforcementInlining=false}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class EnforcementInliner implements ParserTreeConstants {

  private final Support support;

  private final Set<SimpleNode> frozenNodes;

  private final Set<IntVar> kept;

  /** A clause: its node and its current literals. */
  private static final class Clause {
    final SimpleNode node;
    final List<IntVar> pos;
    final List<IntVar> neg;
    boolean dead;
    boolean changed;

    Clause(SimpleNode node, List<IntVar> pos, List<IntVar> neg) {
      this.node = node;
      this.pos = pos;
      this.neg = neg;
    }

    int size() {
      return pos.size() + neg.size();
    }
  }

  /** A half-reified constraint: its node, its control and the variables of its body. */
  private record Imp(ASTConstElem node, IntVar control, Set<IntVar> body) {}

  /** The occurrences of a variable. */
  private static final class Info {
    int other;
    int neg;
    int controls;
    Imp control;
    final List<Clause> clauses = new ArrayList<>(2);
  }

  private final Map<IntVar, Info> infos = new IdentityHashMap<>();

  // the variables in the order of their first occurrence, so the result does not depend on hashes
  private final List<IntVar> order = new ArrayList<>();

  private final List<Clause> clauses = new ArrayList<>();

  private final Set<SimpleNode> replaced = new HashSet<>();

  private final Set<IntVar> eliminated = new LinkedHashSet<>();

  private int literalBodies;

  private int binaryClauses;

  private int negatedControls;

  /**
   * It creates the reduction.
   *
   * @param support the support of the FlatZinc front end.
   * @param frozenNodes constraint nodes that earlier detectors replaced or merged; their variables
   *     count as used elsewhere.
   * @param kept variables that must stay: those of the solve item and the output variables.
   */
  public EnforcementInliner(Support support, Set<SimpleNode> frozenNodes, Set<IntVar> kept) {
    this.support = support;
    this.frozenNodes = frozenNodes;
    this.kept = kept;
  }

  /**
   * It tells if the reduction is on.
   *
   * @return false if the system property org.jacop.fz.enforcementInlining is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.enforcementInlining"));
  }

  /**
   * The constraint nodes that are not posted: the removed clauses and implications, and the clauses
   * posted with new literals.
   *
   * @return the replaced constraint nodes.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  /**
   * The eliminated controls.
   *
   * @return the eliminated variables.
   */
  public Set<IntVar> eliminated() {
    return Collections.unmodifiableSet(eliminated);
  }

  /**
   * It scans the constraint items, eliminates what it can, registers the controls replaced at
   * posting with the support and posts the clauses whose literals changed.
   *
   * @param astTree the root of the parsed model.
   * @param fncs the constraint functions that post the changed clauses.
   */
  public void detect(SimpleNode astTree, ConstraintFncs fncs) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          support.checkTimeOut();
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            scan((ASTConstElem) item);
          }
        }
      }
    }
    for (IntVar b : order) {
      literalBody(b);
    }
    for (IntVar b : order) {
      binaryClause(b);
    }
    for (Clause c : clauses) {
      if (c.dead || c.changed) {
        replaced.add(c.node);
      }
    }
    for (Clause c : clauses) {
      if (!c.dead && c.changed) {
        fncs.poseClause(c.pos.toArray(new IntVar[0]), c.neg.toArray(new IntVar[0]));
      }
    }
    if (support.options.debug() && !eliminated.isEmpty()) {
      FzConsole.println(
          "% enforcement inlining: "
              + eliminated.size()
              + " controls eliminated ("
              + literalBodies
              + " literal bodies, "
              + binaryClauses
              + " binary clauses, "
              + negatedControls
              + " of them negated)");
    }
  }

  private Info info(IntVar v) {
    Info i = infos.get(v);
    if (i == null) {
      i = new Info();
      infos.put(v, i);
      order.add(v);
    }
    return i;
  }

  private void scan(ASTConstElem node) {
    String name = node.getName();
    int n = node.jjtGetNumChildren();
    if (frozenNodes.contains(node)) {
      others(node, 0, n);
      return;
    }
    if (name.equals("bool_clause") && n == 2) {
      IntVar[] p = support.getVarArray((SimpleNode) node.jjtGetChild(0));
      IntVar[] q = support.getVarArray((SimpleNode) node.jjtGetChild(1));
      List<IntVar> pos = new ArrayList<>(p.length);
      List<IntVar> neg = new ArrayList<>(q.length);
      Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
      boolean plain = true;
      for (IntVar v : p) {
        plain &= v.singleton() || seen.add(v);
        if (!v.singleton()) {
          pos.add(v);
        }
      }
      for (IntVar v : q) {
        plain &= v.singleton() || seen.add(v);
        if (!v.singleton()) {
          neg.add(v);
        }
      }
      if (!plain) {
        // repeated variables: the clause is left as it is
        others(node, 0, n);
        return;
      }
      Clause c = new Clause(node, pos, neg);
      clauses.add(c);
      for (IntVar v : pos) {
        info(v).clauses.add(c);
      }
      for (IntVar v : neg) {
        info(v).neg++;
      }
      return;
    }
    if (name.endsWith("_imp")
        && n >= 2
        && node.jjtGetChild(n - 1) instanceof ASTScalarFlatExpr e
        && (e.getType() == 2 || e.getType() == 3)) {
      IntVar b = support.getVariable(e);
      if (!b.singleton()) {
        Set<IntVar> body = Collections.newSetFromMap(new IdentityHashMap<>());
        for (int k = 0; k < n - 1; k++) {
          variables((SimpleNode) node.jjtGetChild(k), body);
        }
        for (IntVar v : body) {
          info(v).other++;
        }
        Info i = info(b);
        i.controls++;
        i.control = new Imp(node, b, body);
        return;
      }
    }
    others(node, 0, n);
  }

  private void others(SimpleNode node, int from, int to) {
    Set<IntVar> vars = Collections.newSetFromMap(new IdentityHashMap<>());
    for (int k = from; k < to; k++) {
      variables((SimpleNode) node.jjtGetChild(k), vars);
    }
    for (IntVar v : vars) {
      info(v).other++;
    }
  }

  // the integer variables of an argument, constants left out
  private void variables(SimpleNode arg, Set<IntVar> out) {
    if (arg.getId() == JJTARRAYLITERAL) {
      for (int i = 0; i < arg.jjtGetNumChildren(); i++) {
        variables((SimpleNode) arg.jjtGetChild(i), out);
      }
      return;
    }
    if (arg.getId() != JJTSCALARFLATEXPR) {
      return;
    }
    ASTScalarFlatExpr e = (ASTScalarFlatExpr) arg;
    if (e.getType() == 2) {
      IntVar[] array = support.dictionary.getVariableArray(e.getIdent());
      if (array != null) {
        for (IntVar v : array) {
          add(v, out);
        }
        return;
      }
      add(support.dictionary.getVariable(e.getIdent()), out);
    } else if (e.getType() == 3 && support.dictionary.getVariableArray(e.getIdent()) != null) {
      add(support.getVariable(e), out);
    }
  }

  private static void add(IntVar v, Set<IntVar> out) {
    if (v != null && !v.singleton()) {
      out.add(v);
    }
  }

  /** Whether b is a control that only its implication keeps from 1. */
  private boolean candidate(IntVar b) {
    Info i = infos.get(b);
    return i != null
        && i.other == 0
        && i.neg == 0
        && i.controls == 1
        && !eliminated.contains(b)
        && !kept.contains(b)
        && !b.singleton()
        && b.min() == 0
        && b.max() == 1
        && !i.control.body().contains(b)
        && support.imply.variablesOf(b).isEmpty()
        && support.reif.variablesOf(b).isEmpty()
        && live(i) > 0;
  }

  private static int live(Info i) {
    i.clauses.removeIf(c -> c.dead);
    return i.clauses.size();
  }

  // b -> x = t over a 0/1 variable x: b becomes the literal x = t in its clauses
  private void literalBody(IntVar b) {
    if (!candidate(b)) {
      return;
    }
    Info info = infos.get(b);
    ASTConstElem node = info.control.node();
    String name = node.getName();
    boolean equal = name.equals("int_eq_imp") || name.equals("bool_eq_imp");
    if (!equal && !name.equals("int_ne_imp") && !name.equals("bool_ne_imp")
        || node.jjtGetNumChildren() != 3) {
      return;
    }
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);
    IntVar x;
    int k;
    if (v2.singleton() && !v1.singleton()) {
      x = v1;
      k = v2.value();
    } else if (v1.singleton() && !v2.singleton()) {
      x = v2;
      k = v1.value();
    } else {
      return;
    }
    if (x.min() != 0 || x.max() != 1 || k < 0 || k > 1 || x == b) {
      return;
    }
    boolean positive = equal ? k == 1 : k == 0;
    for (Clause c : new ArrayList<>(info.clauses)) {
      c.pos.remove(b);
      c.changed = true;
      List<IntVar> same = positive ? c.pos : c.neg;
      List<IntVar> opposite = positive ? c.neg : c.pos;
      if (opposite.contains(x)) {
        kill(c);
      } else if (!same.contains(x)) {
        same.add(x);
        if (positive) {
          info(x).clauses.add(c);
        } else {
          info(x).neg++;
        }
      }
    }
    info.clauses.clear();
    info(x).other--;
    replaced.add(node);
    eliminated.add(b);
    literalBodies++;
  }

  // b -> C with the only clause l \/ b: not l -> C
  private void binaryClause(IntVar b) {
    if (!candidate(b)) {
      return;
    }
    Info info = infos.get(b);
    if (info.clauses.size() != 1) {
      return;
    }
    Clause c = info.clauses.getFirst();
    if (c.size() != 2) {
      return;
    }
    IntVar w;
    boolean negated;
    if (c.pos.size() == 2) {
      w = c.pos.get(0) == b ? c.pos.get(1) : c.pos.get(0);
      negated = true;
    } else {
      w = c.neg.getFirst();
      negated = false;
    }
    if (w == b || info.control.body().contains(w) || w.min() != 0 || w.max() != 1) {
      return;
    }
    kill(c);
    Info wi = info(w);
    // w now controls C as well; it stays
    wi.other++;
    Support.ControlSubstitution s = new Support.ControlSubstitution(b, w, negated);
    support.controlSubstitutions.put(info.control.node(), s);
    support.substitutedControls.put(b, s);
    eliminated.add(b);
    binaryClauses++;
    if (negated) {
      negatedControls++;
    }
  }

  private void kill(Clause c) {
    c.dead = true;
    for (IntVar v : c.neg) {
      Info i = infos.get(v);
      if (i != null) {
        i.neg--;
      }
    }
  }

  /**
   * After posting: the eliminated controls that no constraint took again leave the search and get
   * no literals.
   *
   * @return the controls that are no longer in any constraint.
   */
  public Set<Var> unconstrained() {
    Set<Var> free = new LinkedHashSet<>();
    for (IntVar b : eliminated) {
      if (b.sizeConstraints() == 0) {
        free.add(b);
      }
    }
    return free;
  }
}
