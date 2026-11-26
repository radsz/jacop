/*
 * FzItems.java
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
import java.util.List;
import java.util.Optional;
import java.util.Set;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Reading helpers shared by the detectors that rewrite constraint items of the parsed model.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class FzItems implements ParserTreeConstants {

  private static final IntVar[] NONE = new IntVar[0];

  private FzItems() {}

  /**
   * The constraint items of the model, in their order, without the skipped ones.
   *
   * @param astTree the root of the parsed model.
   * @param skipped constraint nodes that are not posted.
   * @return the constraint nodes.
   */
  static List<ASTConstElem> constraints(SimpleNode astTree, Set<SimpleNode> skipped) {
    List<ASTConstElem> all = new ArrayList<>();
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() != JJTCONSTRAINTITEMS) {
        continue;
      }
      for (int j = 0; j < node.jjtGetNumChildren(); j++) {
        SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
        if (item.getId() == JJTCONSTELEM && !skipped.contains(item)) {
          all.add((ASTConstElem) item);
        }
      }
    }
    return all;
  }

  /**
   * The integer variables an argument names, read as the constraints read their arguments, so that
   * aliases resolve the same way: a variable, an array of variables or an element of one. Float and
   * set arrays, constants and array literals give none.
   *
   * @param support the support of the FlatZinc front end.
   * @param e the argument.
   * @return the variables, possibly empty.
   */
  static IntVar[] variables(Support support, ASTScalarFlatExpr e) {
    if (e.getType() == 2) {
      if (support.dictionary.getDeclaredVariableArray(e.getIdent()) != null) {
        return support.getVarArray(e);
      }
      if (support.dictionary.getVariable(e) != null) {
        return new IntVar[] {support.getVariable(e)};
      }
    } else if (e.getType() == 3
        && support.dictionary.getDeclaredVariableArray(e.getIdent()) != null) {
      return new IntVar[] {support.getVariable(e)};
    }
    return NONE;
  }

  /**
   * The values of an array argument whose variables are all fixed.
   *
   * @param support the support of the FlatZinc front end.
   * @param arg the array argument.
   * @return the values, or empty when some variable is not fixed.
   */
  static Optional<int[]> fixedValues(Support support, SimpleNode arg) {
    IntVar[] vars = support.getVarArray(arg);
    int[] array = new int[vars.length];
    for (int k = 0; k < vars.length; k++) {
      if (!vars[k].singleton()) {
        return Optional.empty();
      }
      array[k] = vars[k].value();
    }
    return Optional.of(array);
  }
}
