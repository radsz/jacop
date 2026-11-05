/*
 * SetUnionDetector.java
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.OrBool;
import org.jacop.constraints.XeqY;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;
import org.jacop.set.constraints.ChannelBoolSet;
import org.jacop.set.core.SetVar;

/**
 * A union of singleton sets becomes one membership clause per element.
 *
 * <p>MiniZinc flattens a set comprehension over variable elements, {@code {e(i) | i in I}}, into
 * one singleton set {@code S_i} per element ({@code set_card(S_i, 1)} and {@code set_in(e_i, S_i)})
 * and a chain of {@code set_union} constraints that adds them up one at a time (gt-sort: 3,657
 * unions for 11 sets of at most 32 elements). Every intermediate union is a set variable of its
 * own, so under LCG the model carries one membership literal per element of each of them, and a
 * change of one element travels down the chain one union at a time, each step explained by the
 * previous union's literals.
 *
 * <p>The detector replaces the chain by what it means: an element {@code v} is in the union {@code
 * U} exactly when one of the {@code e_i} equals {@code v}, {@code [v in U] <-> OR_i [e_i = v]},
 * with the {@code [e_i = v]} literals of the integer variables, and a constant set among the
 * operands fixing its elements in. The singletons and the intermediate unions then have no
 * constraint left, and the set variables without constraints get no membership literals.
 *
 * <p>Only chains whose intermediate sets appear nowhere else (not in other constraints, the search,
 * the objective or the output) are replaced. The system property {@code
 * org.jacop.fz.setUnion=false} turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class SetUnionDetector implements ParserTreeConstants {

  /**
   * At least this many singletons in a replaced chain. A short chain has few inner unions to save,
   * and its membership clauses only add variables (harmony, four voices per chord: proofs 10 %
   * slower). The system property {@code org.jacop.fz.setUnion.min} changes it.
   */
  static final int MIN_SINGLETONS = 8;

  /** At most this many elements in the upper bound of a replaced union. */
  static final int MAX_ELEMENTS = 1 << 12;

  private final Support support;

  private final Set<SimpleNode> replaced = new HashSet<>();

  // the singletons and inner unions of the replaced chains, which have no constraint left
  private final Set<Var> unconstrained = new HashSet<>();

  private final Map<SetVar, Integer> occurrences = new IdentityHashMap<>();

  // S -> its set_card(S, 1) node
  private final Map<SetVar, SimpleNode> cardOne = new IdentityHashMap<>();

  // S -> its set_in(e, S) nodes
  private final Map<SetVar, List<ASTConstElem>> members = new IdentityHashMap<>();

  // C -> the set_union(A, B, C) node that defines it
  private final Map<SetVar, ASTConstElem> unions = new LinkedHashMap<>();

  // how often a set variable is an operand of a set_union
  private final Map<SetVar, Integer> operands = new IdentityHashMap<>();

  // a leaf of a union chain: the singleton {element}, or a constant set
  private record Leaf(IntVar element, IntDomain constant, IntDomain lub) {}

  private int rewritten;

  private final int minSingletons = Integer.getInteger("org.jacop.fz.setUnion.min", MIN_SINGLETONS);

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public SetUnionDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.setUnion is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.setUnion"));
  }

  /**
   * The constraints a membership clause replaced; they are not posted.
   *
   * @return the set_union, set_card and set_in nodes of the replaced chains.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  /**
   * The singleton sets and inner unions of the replaced chains. No constraint is left on them, so
   * they are not searched and get no membership literals.
   *
   * @return the set variables.
   */
  public Set<Var> unconstrained() {
    return unconstrained;
  }

  /**
   * It scans the constraint items of the model and replaces each chain of unions over singleton
   * sets by membership clauses.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          support.checkTimeOut();
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          countAll(item);
          if (item.getId() == JJTCONSTELEM) {
            collect((ASTConstElem) item);
          }
        }
      } else if (node.getId() == JJTSOLVEITEM || node.getId() == JJTMODELEND) {
        // the sets of the search annotations, the objective and the output stay
        countAll(node);
      }
    }
    if (unions.isEmpty() || cardOne.isEmpty()) {
      return;
    }
    for (Map.Entry<SetVar, ASTConstElem> e : unions.entrySet()) {
      if (!inner(e.getKey())) {
        replace(e.getKey(), e.getValue());
      }
    }
    if (support.options.debug() && rewritten > 0) {
      FzConsole.println(
          "% set union detector: "
              + rewritten
              + " unions of singletons as membership clauses, "
              + replaced.size()
              + " constraints replaced");
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "set_card" -> {
        SetVar s = setVariable(node, 0);
        ASTScalarFlatExpr c = (ASTScalarFlatExpr) node.jjtGetChild(1);
        if (s != null && (c.getType() == 0 || c.getType() == 1) && support.getInt(c) == 1) {
          cardOne.put(s, node);
        }
      }
      case "set_in" -> {
        SetVar s = setVariable(node, 1);
        if (s != null) {
          members.computeIfAbsent(s, k -> new ArrayList<>()).add(node);
        }
      }
      case "set_union" -> {
        SetVar c = setVariable(node, 2);
        if (c != null && !unions.containsKey(c)) {
          unions.put(c, node);
          for (int k = 0; k < 2; k++) {
            SetVar a = setVariable(node, k);
            if (a != null) {
              operands.merge(a, 1, Integer::sum);
            }
          }
        }
      }
      default -> {
        // other constraints only count their sets
      }
    }
  }

  /** The set variable of argument k, or null when it is a literal or a parameter. */
  private SetVar setVariable(SimpleNode node, int k) {
    SimpleNode child = (SimpleNode) node.jjtGetChild(k);
    if (child.getId() != JJTSCALARFLATEXPR) {
      return null;
    }
    ASTScalarFlatExpr e = (ASTScalarFlatExpr) child;
    if (e.getType() == 2) {
      return support.dictionary.getSetVariable(e.getIdent());
    }
    if (e.getType() == 3) {
      SetVar[] a = support.dictionary.getSetVariableArrayOrNull(e.getIdent());
      return a == null ? null : a[e.getInt()];
    }
    return null;
  }

  /** A union result that only feeds one other union. */
  private boolean inner(SetVar c) {
    return occurrences.getOrDefault(c, 0) == 2
        && operands.getOrDefault(c, 0) == 1
        && c.domain.glb().isEmpty()
        && !support.dictionary.isOutput(c);
  }

  /** A singleton set {e} that only feeds one union. */
  private boolean singleton(SetVar s) {
    List<ASTConstElem> in = members.get(s);
    return cardOne.containsKey(s)
        && in != null
        && in.size() == 1
        && occurrences.getOrDefault(s, 0) == 3
        && operands.getOrDefault(s, 0) == 1
        && !unions.containsKey(s)
        && s.domain.glb().isEmpty()
        && !support.dictionary.isOutput(s);
  }

  private void replace(SetVar root, ASTConstElem node) {
    if (root.domain.lub().getSize() > MAX_ELEMENTS) {
      return;
    }
    List<Leaf> leaves = new ArrayList<>();
    List<SimpleNode> chain = new ArrayList<>();
    List<SetVar> sets = new ArrayList<>();
    if (!leaves(node, root.domain.lub(), leaves, chain, sets)) {
      return;
    }
    int singletons = 0;
    for (Leaf l : leaves) {
      if (l.element() != null) {
        singletons++;
      }
    }
    if (singletons < minSingletons) {
      return;
    }
    Store store = support.store;
    // an element is in its singleton, so in every set on the way to the root
    for (Leaf l : leaves) {
      if (l.element() != null) {
        l.element().domain.in(store.level, l.element(), l.lub());
      } else if (!l.constant().subtract(l.lub()).isEmpty()) {
        // a constant element outside a set on the way: the constraints posted as they are fail
        return;
      }
    }
    IntDomain lub = root.domain.lub();
    int min = lub.min();
    IntVar[] member = new IntVar[lub.max() - min + 1];
    Map<IntVar, Map<Integer, IntVar>> equal = new IdentityHashMap<>();
    for (int k = 0; k < member.length; k++) {
      int v = min + k;
      if (!lub.contains(v)) {
        member[k] = support.dictionary.getConstant(0);
        continue;
      }
      List<IntVar> or = new ArrayList<>();
      boolean in = false;
      for (Leaf l : leaves) {
        if (l.element() == null) {
          in |= l.constant().contains(v);
        } else if (l.element().domain.contains(v)) {
          or.add(valueLiteral(l.element(), v, equal));
        }
      }
      if (in) {
        member[k] = support.dictionary.getConstant(1);
      } else if (or.isEmpty()) {
        member[k] = support.dictionary.getConstant(0);
      } else if (or.size() == 1) {
        member[k] = or.get(0);
      } else {
        member[k] = new IntVar(store, 0, 1);
        IntVar[] list = or.toArray(new IntVar[0]);
        if (support.options.useSat()) {
          support.sat.generateOr(list, member[k]);
        } else {
          support.poseDc(new OrBool(list, member[k]));
        }
      }
    }
    support.pose(new ChannelBoolSet(distinct(member), root, min));
    replaced.addAll(chain);
    unconstrained.addAll(sets);
    rewritten++;
  }

  /** The literal [x = v], one 0/1 variable per pair. */
  private IntVar valueLiteral(IntVar x, int v, Map<IntVar, Map<Integer, IntVar>> equal) {
    Map<Integer, IntVar> byValue = equal.computeIfAbsent(x, k -> new HashMap<>());
    IntVar b = byValue.get(v);
    if (b == null) {
      if (x.singleton(v)) {
        b = support.dictionary.getConstant(1);
      } else if (x.min() >= 0 && x.max() <= 1) {
        b = v == 1 ? x : negation(x, equal);
      } else {
        b = new IntVar(support.store, 0, 1);
        support.pose(support.fzXeqCreified(x, v, b));
      }
      byValue.put(v, b);
    }
    return b;
  }

  private IntVar negation(IntVar x, Map<IntVar, Map<Integer, IntVar>> equal) {
    IntVar b = new IntVar(support.store, 0, 1);
    support.pose(support.fzXeqCreified(x, 0, b));
    equal.computeIfAbsent(x, k -> new HashMap<>()).put(0, b);
    return b;
  }

  /** ChannelBoolSet takes each variable once; a repeated one gets a copy equal to it. */
  private IntVar[] distinct(IntVar[] member) {
    Set<Var> seen = new HashSet<>();
    IntVar[] bs = member.clone();
    for (int i = 0; i < bs.length; i++) {
      if (!bs[i].singleton() && !seen.add(bs[i])) {
        IntVar copy = new IntVar(support.store, 0, 1);
        support.pose(new XeqY(bs[i], copy));
        bs[i] = copy;
      }
    }
    return bs;
  }

  /**
   * Collects the leaves under a union, each with the intersection of the upper bounds of the sets
   * on its way to the root, and the nodes of the chain; false when an operand is neither a
   * singleton, a constant set nor an inner union.
   */
  private boolean leaves(
      ASTConstElem union,
      IntDomain lub,
      List<Leaf> out,
      List<SimpleNode> chain,
      List<SetVar> sets) {
    chain.add(union);
    for (int k = 0; k < 2; k++) {
      SetVar a = setVariable(union, k);
      if (a == null) {
        IntDomain c = support.getSetLiteral(union, k);
        out.add(new Leaf(null, c, lub));
      } else if (a.singleton()) {
        out.add(new Leaf(null, a.domain.glb(), lub));
      } else if (unions.containsKey(a) && inner(a)) {
        sets.add(a);
        if (!leaves(unions.get(a), lub.intersect(a.domain.lub()), out, chain, sets)) {
          return false;
        }
      } else if (singleton(a)) {
        ASTConstElem in = members.get(a).get(0);
        IntVar e = support.getVariable((ASTScalarFlatExpr) in.jjtGetChild(0));
        out.add(new Leaf(e, null, lub.intersect(a.domain.lub())));
        sets.add(a);
        chain.add(cardOne.get(a));
        chain.add(in);
      } else {
        return false;
      }
    }
    return true;
  }

  private void countAll(SimpleNode node) {
    count(node);
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      countAll((SimpleNode) node.jjtGetChild(i));
    }
  }

  private void count(SimpleNode arg) {
    if (arg.getId() != JJTSCALARFLATEXPR) {
      return;
    }
    ASTScalarFlatExpr e = (ASTScalarFlatExpr) arg;
    if (e.getType() == 2) {
      SetVar[] array = support.dictionary.getSetVariableArrayOrNull(e.getIdent());
      if (array != null) {
        for (SetVar v : array) {
          occurrences.merge(v, 1, Integer::sum);
        }
        return;
      }
      SetVar v = support.dictionary.getSetVariable(e.getIdent());
      if (v != null) {
        occurrences.merge(v, 1, Integer::sum);
      }
    } else if (e.getType() == 3) {
      SetVar[] array = support.dictionary.getSetVariableArrayOrNull(e.getIdent());
      if (array != null) {
        occurrences.merge(array[e.getInt()], 1, Integer::sum);
      }
    }
  }
}
