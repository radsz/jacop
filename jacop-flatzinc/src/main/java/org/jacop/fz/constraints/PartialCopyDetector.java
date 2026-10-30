/*
 * PartialCopyDetector.java
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
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It merges the copies MiniZinc makes of the result of a partial function. A partial function used
 * in a reified context, for example {@code to_enum(E, x)} or an array access with a variable index
 * that may be out of range, gets a fresh variable z at every call site:
 *
 * <pre>
 * int_eq_imp(z, x, b)       b -&gt; z = x   (b: the call is defined)
 * int_eq_imp(z, k, c)       c -&gt; z = k   (k: a default value)
 * bool_clause([c, b], [])   not b -&gt; c
 * </pre>
 *
 * <p>z is b ? x : k, so all copies with the same x, b and k are one variable. MiniZinc does not
 * merge them, and a model that calls the function once per item gets one copy per item, each with
 * its three constraints to wake. The copies become aliases of the first one and their three
 * constraints are skipped. A copy is merged only when c occurs in no other constraint and neither z
 * nor c is an output variable.
 *
 * <p>Setting the system property {@code org.jacop.fz.partialCopies} to false turns the merging off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class PartialCopyDetector implements ParserTreeConstants {

  private final Support support;

  // the implications b -> z = x between two variables, by z
  private record VarImp(IntVar x, IntVar b, SimpleNode node) {}

  // the implications c -> z = k, by z
  private record ConstImp(int k, IntVar c, SimpleNode node) {}

  // what makes copies equal
  private record Key(IntVar x, IntVar b, int k) {}

  private final Map<IntVar, List<VarImp>> varImps = new IdentityHashMap<>();
  private final Map<IntVar, List<ConstImp>> constImps = new IdentityHashMap<>();
  private final Map<IntVar, List<SimpleNode>> binaryClauses = new IdentityHashMap<>();
  private final Map<IntVar, Integer> occurrences = new IdentityHashMap<>();

  private int merged;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public PartialCopyDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the merging is on.
   *
   * @return false if the system property org.jacop.fz.partialCopies is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.partialCopies"));
  }

  /**
   * It merges the copies of the model into aliases of one variable.
   *
   * @param astTree the root of the parsed model.
   * @return the constraint nodes of the merged copies, which must not be posted.
   */
  public Set<SimpleNode> detect(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            collect((ASTConstElem) item);
          }
        }
      }
    }

    Set<IntVar> aliased = new HashSet<>(support.dictionary.aliasTable.keySet());
    aliased.addAll(support.dictionary.aliasTable.values());
    Map<Key, IntVar> first = new HashMap<>();
    Set<SimpleNode> skipped = new HashSet<>();
    for (Map.Entry<IntVar, List<ConstImp>> e : constImps.entrySet()) {
      IntVar z = e.getKey();
      List<VarImp> vi = varImps.get(z);
      if (e.getValue().size() != 1 || vi == null || vi.size() != 1 || aliased.contains(z)) {
        continue;
      }
      ConstImp ci = e.getValue().getFirst();
      VarImp v = vi.getFirst();
      SimpleNode clause = clauseOf(ci.c(), v.b());
      if (clause == null
          || occurrences.get(ci.c()) != 2
          || z.singleton()
          || support.dictionary.isOutput(z)
          || support.dictionary.isOutput(ci.c())) {
        continue;
      }
      Key key = new Key(v.x(), v.b(), ci.k());
      IntVar rep = first.putIfAbsent(key, z);
      if (rep == null) {
        continue;
      }
      rep.domain.in(support.store.level, rep, z.domain);
      support.dictionary.addAlias(rep, z);
      skipped.add(v.node());
      skipped.add(ci.node());
      skipped.add(clause);
      merged++;
    }
    if (support.options.debug()) {
      FzConsole.println("% partial function copies merged: " + merged);
    }
    return skipped;
  }

  /**
   * It returns the number of copies merged into another variable.
   *
   * @return the number of merged copies.
   */
  public int merged() {
    return merged;
  }

  private void collect(ASTConstElem node) {
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      count((SimpleNode) node.jjtGetChild(i));
    }
    switch (node.getName()) {
      case "int_eq_imp" -> implication(node);
      case "bool_clause" -> {
        IntVar[] pos = support.getVarArray(child(node, 0));
        if (pos.length == 2 && support.getVarArray(child(node, 1)).length == 0) {
          binaryClauses.computeIfAbsent(pos[0], k -> new ArrayList<>()).add(node);
          binaryClauses.computeIfAbsent(pos[1], k -> new ArrayList<>()).add(node);
        }
      }
      default -> {
        // not part of a copy
      }
    }
  }

  private void implication(ASTConstElem node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (p1.getType() == 0 || p2.getType() == 0) {
      IntVar z = support.getVariable(p1.getType() == 0 ? p2 : p1);
      int k = support.getInt(p1.getType() == 0 ? p1 : p2);
      constImps.computeIfAbsent(z, x -> new ArrayList<>()).add(new ConstImp(k, b, node));
      return;
    }
    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);
    varImps.computeIfAbsent(v1, x -> new ArrayList<>()).add(new VarImp(v2, b, node));
    varImps.computeIfAbsent(v2, x -> new ArrayList<>()).add(new VarImp(v1, b, node));
  }

  /** The clause [c, b] with no negative literals, or null. */
  private SimpleNode clauseOf(IntVar c, IntVar b) {
    for (SimpleNode node : binaryClauses.getOrDefault(c, List.of())) {
      IntVar[] pos = support.getVarArray(child(node, 0));
      if (pos[0] == b || pos[1] == b) {
        return node;
      }
    }
    return null;
  }

  /** It counts the variables of an argument, array elements included. */
  private void count(SimpleNode arg) {
    if (arg.getId() == JJTARRAYLITERAL) {
      for (int i = 0; i < arg.jjtGetNumChildren(); i++) {
        count((SimpleNode) arg.jjtGetChild(i));
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
          occurrences.merge(v, 1, Integer::sum);
        }
        return;
      }
      IntVar v = support.dictionary.getVariable(e.getIdent());
      if (v != null) {
        occurrences.merge(v, 1, Integer::sum);
      }
    } else if (e.getType() == 3 && support.dictionary.getVariableArray(e.getIdent()) != null) {
      // an element of an array of variables; other arrays hold parameters
      occurrences.merge(support.getVariable(e), 1, Integer::sum);
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }
}
