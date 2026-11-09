/*
 * AlldiffChannels.java
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

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Set;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * The variables that an element constraint uses as its index, or that a table constrains: the
 * variables whose domains get holes inside their bounds from these constraints.
 *
 * <p>An all_different over such variables keeps domain consistency ({@code Alldistinct}, Régin,
 * AAAI 1994) above the size limits of the FlatZinc posting rule, since bounds consistency ({@code
 * Alldiff}, after Puget, AAAI 1998) sees only the bounds and cannot use the holes. A bound on a
 * cost read through elements, cost[i][x[i]] &lt;= z, as in a bottleneck assignment, removes values
 * from the middle of the domains of x; the matching of Alldistinct then fixes or fails far earlier.
 *
 * <p>Hall sets that are not intervals matter when the all_different is close to a permutation, with
 * few more values than variables, as in an assignment. With many spare values (a choice of words
 * from a dictionary, of origins from a large set) the matching rarely prunes, and on the Challenge
 * instances of that kind Alldistinct lost more than it gained.
 *
 * <p>The system property {@code org.jacop.fz.alldiffChannel} selects the rule: {@code true} (the
 * default) posts Alldistinct above the limits when at least half of the not fixed variables are
 * channelled and there are at most a quarter more values than variables, {@code loose} drops the
 * condition on the values, {@code all} posts it above the limits whatever the channelling and the
 * values, and {@code false} keeps the limits.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class AlldiffChannels implements ParserTreeConstants {

  /** The largest number of variable-value pairs of an all_different that the rule changes. */
  static final long MAX_PAIRS = 1L << 20;

  private AlldiffChannels() {}

  /**
   * The rule of the system property {@code org.jacop.fz.alldiffChannel}.
   *
   * @return "true", "loose", "all" or "false".
   */
  public static String rule() {
    String rule = System.getProperty("org.jacop.fz.alldiffChannel", "true").toLowerCase();
    return switch (rule) {
      case "all", "loose", "false" -> rule;
      default -> "true";
    };
  }

  /**
   * It collects the index variables of the element constraints and the variables of the tables of
   * the model.
   *
   * @param support the support of the FlatZinc front end.
   * @param astTree the root of the parsed model.
   * @return the variables, compared by identity.
   */
  public static Set<IntVar> collect(Support support, SimpleNode astTree) {
    Set<IntVar> channelled = Collections.newSetFromMap(new IdentityHashMap<>());
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() != JJTCONSTRAINTITEMS) {
        continue;
      }
      for (int j = 0; j < node.jjtGetNumChildren(); j++) {
        SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
        if (item.getId() == JJTCONSTELEM) {
          collect(support, (ASTConstElem) item, channelled);
        }
      }
    }
    return channelled;
  }

  private static void collect(Support support, ASTConstElem node, Set<IntVar> channelled) {
    switch (node.getName()) {
      case "array_int_element", "array_var_int_element", "jacop_array_var_int_element_nonshifted" ->
          add(support, (SimpleNode) node.jjtGetChild(0), channelled);
      case "jacop_table_int", "jacop_short_table_int" -> {
        SimpleNode x = (SimpleNode) node.jjtGetChild(0);
        if (x.getId() == JJTARRAYLITERAL) {
          for (int k = 0; k < x.jjtGetNumChildren(); k++) {
            add(support, (SimpleNode) x.jjtGetChild(k), channelled);
          }
        } else if (x.getId() == JJTSCALARFLATEXPR && ((ASTScalarFlatExpr) x).getType() == 2) {
          IntVar[] v = support.dictionary.getVariableArray(((ASTScalarFlatExpr) x).getIdent());
          if (v != null) {
            Collections.addAll(channelled, v);
          }
        }
      }
      default -> {
        // other constraints are not channels
      }
    }
  }

  // only variables the model declares: looking up a constant would create it before the model does
  private static void add(Support support, SimpleNode node, Set<IntVar> channelled) {
    if (node.getId() != JJTSCALARFLATEXPR) {
      return;
    }
    ASTScalarFlatExpr e = (ASTScalarFlatExpr) node;
    IntVar v = null;
    if (e.getType() == 2) {
      v = support.dictionary.getVariable(e.getIdent());
    } else if (e.getType() == 3) {
      IntVar[] a = support.dictionary.getVariableArray(e.getIdent());
      if (a != null && e.getInt() >= 0 && e.getInt() < a.length) {
        v = a[e.getInt()];
      }
    }
    if (v != null) {
      channelled.add(v);
    }
  }

  /**
   * It tells if an all_different that the size limits give bounds consistency gets domain
   * consistency instead.
   *
   * @param v the variables of the all_different.
   * @param channelled the variables from {@link #collect(Support, SimpleNode)}, or null.
   * @param values the number of values of the variables together.
   * @param rule the rule from {@link #rule()}.
   * @return true for Alldistinct.
   */
  static boolean domainConsistent(IntVar[] v, Set<IntVar> channelled, int values, String rule) {
    if ("false".equals(rule)) {
      return false;
    }
    long pairs = 0;
    int open = 0;
    int linked = 0;
    for (IntVar x : v) {
      pairs += x.getSize();
      if (!x.singleton()) {
        open++;
        if (channelled != null && channelled.contains(x)) {
          linked++;
        }
      }
    }
    if (pairs > MAX_PAIRS) {
      return false;
    }
    if ("all".equals(rule)) {
      return true;
    }
    boolean tight = "loose".equals(rule) || 4L * values <= 5L * v.length;
    return tight && linked > 0 && 2 * linked >= open;
  }
}
