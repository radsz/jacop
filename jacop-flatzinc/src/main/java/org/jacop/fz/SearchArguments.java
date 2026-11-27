/*
 * SearchArguments.java
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

package org.jacop.fz;

import java.lang.reflect.Array;
import java.util.List;
import java.util.Map;

/**
 * Checks the variables of the search annotations of the solve item before the model is solved, in
 * every mode: an identifier the model does not declare, or one of another type than the search (a
 * set variable in int_search, an integer in float_search or set_search), is an error of the model.
 * A thread that followed the annotation threw a NullPointerException, while -f and the other
 * threads of a portfolio, which do not read the annotation, solved the model.
 */
final class SearchArguments {

  private SearchArguments() {}

  private enum Kind {
    INT,
    FLOAT,
    SET
  }

  private static final String END = "; execution aborted";

  /**
   * Checks the search annotations of the model.
   *
   * @param astTree the root of the parsed model
   * @param table the symbols of the model
   * @throws IllegalArgumentException when a search names an undeclared symbol or one of another
   *     type
   */
  static void check(SimpleNode astTree, Tables table) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node == null || node.getId() != ParserTreeConstants.JJTMODELEND) {
        continue;
      }
      SimpleNode item = (SimpleNode) node.jjtGetChild(0);
      // the annotations come before the kind of the solve item
      for (int a = 0; a < item.jjtGetNumChildren() - 1; a++) {
        if (item.jjtGetChild(a) instanceof ASTAnnotation ann) {
          search(ann, table);
        }
      }
    }
  }

  private static void search(ASTAnnotation ann, Tables table) {
    String id = ann.getAnnId();
    if (id == null || ann.jjtGetNumChildren() == 0) {
      return;
    }
    switch (id) {
      case "int_search", "bool_search", "relax_and_reconstruct" ->
          variables((SimpleNode) ann.jjtGetChild(0), Kind.INT, id, table);
      case "set_search" -> variables((SimpleNode) ann.jjtGetChild(0), Kind.SET, id, table);
      case "float_search" -> variables((SimpleNode) ann.jjtGetChild(0), Kind.FLOAT, id, table);
      case "priority_search" -> {
        variables((SimpleNode) ann.jjtGetChild(0), Kind.INT, id, table);
        if (ann.jjtGetNumChildren() > 1) {
          searches((SimpleNode) ann.jjtGetChild(1), table);
        }
      }
      case "seq_search" -> searches((SimpleNode) ann.jjtGetChild(0), table);
      default -> {
        // warm starts, restarts and annotations JaCoP ignores have no variables to search
      }
    }
  }

  private static void searches(SimpleNode body, Tables table) {
    for (int i = 0; i < body.jjtGetNumChildren(); i++) {
      if (body.jjtGetChild(i) instanceof ASTAnnotation ann) {
        search(ann, table);
      }
    }
  }

  // every element of the array of variables of a search is a symbol or literal of its kind
  private static void variables(SimpleNode node, Kind kind, String search, Tables table) {
    if (node instanceof ASTSetLiteral) {
      if (kind != Kind.SET) {
        throw new IllegalArgumentException("A set in " + search + " is not of its type" + END);
      }
      return;
    }
    if (node instanceof ASTScalarFlatExpr e) {
      boolean fits =
          switch (e.getType()) {
            case 0, 1 -> kind == Kind.INT;
            case 5 -> kind == Kind.FLOAT;
            case 2, 3 -> symbol(e.getIdent(), e.getType() == 3, kind, table);
            default -> false;
          };
      if (!fits) {
        String what = e.getType() == 2 || e.getType() == 3 ? "\"" + e.getIdent() + "\"" : "" + e;
        throw new IllegalArgumentException(
            "Symbol " + what + " in " + search + " is not of its type" + END);
      }
      if (e.getType() == 3) {
        index(e, table);
      }
      return;
    }
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      variables((SimpleNode) node.jjtGetChild(i), kind, search, table);
    }
  }

  private static boolean symbol(String ident, boolean element, Kind kind, Tables table) {
    if (!table.isIdentifier(ident)) {
      throw new IllegalArgumentException(
          "Symbol \"" + ident + "\" does not have assigned value when refered" + END);
    }
    boolean scalar =
        switch (kind) {
          case INT -> table.intTable.containsKey(ident) || table.variableTable.containsKey(ident);
          case FLOAT ->
              table.floatTable.containsKey(ident) || table.variableFloatTable.containsKey(ident);
          case SET ->
              table.setTable.containsKey(ident) || table.setVariableTable.containsKey(ident);
        };
    boolean array =
        switch (kind) {
          case INT ->
              table.intArrayTable.containsKey(ident) || table.variableArrayTable.containsKey(ident);
          case FLOAT ->
              table.floatArrayTable.containsKey(ident)
                  || table.variableFloatArrayTable.containsKey(ident);
          case SET ->
              table.setArrayTable.containsKey(ident)
                  || table.setVariableArrayTable.containsKey(ident);
        };
    // an identifier stands for a whole array or for one element; a[i] is an element of an array
    return element ? array : scalar || array;
  }

  private static void index(ASTScalarFlatExpr e, Tables table) {
    String ident = e.getIdent();
    int length = -1;
    for (Map<String, ?> m :
        List.<Map<String, ?>>of(
            table.intArrayTable,
            table.variableArrayTable,
            table.floatArrayTable,
            table.variableFloatArrayTable,
            table.setArrayTable,
            table.setVariableArrayTable)) {
      Object a = m.get(ident);
      if (a != null) {
        length = Array.getLength(a);
        break;
      }
    }
    if (e.getInt() < 0 || e.getInt() >= length) {
      throw new IllegalArgumentException(
          "Index out of bound for " + ident + "[" + (e.getInt() + 1) + "]");
    }
  }
}
