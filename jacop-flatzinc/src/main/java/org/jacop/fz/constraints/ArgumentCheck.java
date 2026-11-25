/*
 * ArgumentCheck.java
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

import java.util.HashMap;
import java.util.Map;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Checks the sizes of the arguments of the built-ins before any constraint is read: the lengths of
 * arrays that must agree, and the numbers of rows, columns, vectors or states that a flattened
 * array must fit. A model that breaks them is an error of the model (an IllegalArgumentException,
 * printed as %% Error:), as MiniZinc reports it with its assertions; the generators and the
 * detectors that read the constraints before them assume the sizes agree.
 */
public final class ArgumentCheck implements ParserTreeConstants {

  private interface Rule {
    void check(Arguments a);
  }

  private static final Map<String, Rule> RULES = new HashMap<>();

  static {
    // the weights and the variables of a linear row
    Rule linear = a -> a.sameLength("the coefficients and the variables", 0, 1);
    for (String type : new String[] {"int", "bool", "float"}) {
      for (String relation : new String[] {"eq", "ne", "le", "lt", "ge", "gt"}) {
        for (String suffix : new String[] {"", "_reif", "_imp"}) {
          rule(linear, type + "_lin_" + relation + suffix);
        }
      }
    }
  }

  private ArgumentCheck() {}

  /**
   * Checks the arguments of every constraint of the model.
   *
   * @param support the support of the model, with its parameters and arrays declared
   * @param astTree the model
   * @throws IllegalArgumentException when the sizes of the arguments of a constraint do not agree
   */
  public static void check(Support support, SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() != JJTCONSTRAINTITEMS) {
        continue;
      }
      for (int j = 0; j < node.jjtGetNumChildren(); j++) {
        SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
        if (item.getId() == JJTCONSTELEM) {
          String name = ((ASTConstElem) item).getName();
          Rule rule = RULES.get(name);
          if (rule != null) {
            rule.check(new Arguments(support, name, item));
          }
        }
      }
    }
  }

  private static void rule(Rule rule, String... names) {
    for (String name : names) {
      RULES.put(name, rule);
    }
  }

  /** The arguments of one constraint. */
  private static final class Arguments {
    private final Support support;
    private final String name;
    private final SimpleNode node;

    Arguments(Support support, String name, SimpleNode node) {
      this.support = support;
      this.name = name;
      this.node = node;
    }

    int count() {
      return node.jjtGetNumChildren();
    }

    SimpleNode arg(int i) {
      return (SimpleNode) node.jjtGetChild(i);
    }

    // the length of an array argument, -1 when it is not an array this check knows
    int length(int i) {
      SimpleNode a = arg(i);
      if (a.getId() == JJTARRAYLITERAL) {
        return a.jjtGetNumChildren();
      }
      if (a.getId() != JJTSCALARFLATEXPR || ((ASTScalarFlatExpr) a).getType() != 2) {
        return -1;
      }
      return support.dictionary.arrayLength(((ASTScalarFlatExpr) a).getIdent());
    }

    int intArg(int i) {
      return support.getInt((ASTScalarFlatExpr) arg(i));
    }

    // the integers of an array argument, null when it is not an array of integers
    int[] ints(int i) {
      try {
        return support.getIntArray(arg(i));
      } catch (IllegalArgumentException _) {
        return null;
      }
    }

    void fail(String what) {
      throw new IllegalArgumentException(name + ": " + what);
    }

    void sameLength(String what, int... args) {
      int first = -1;
      for (int i : args) {
        int n = length(i);
        if (n < 0) {
          continue;
        }
        if (first < 0) {
          first = n;
        } else if (n != first) {
          fail(what + " have different lengths");
        }
      }
    }
  }
}
