/*
 * SaturatedProducts.java
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

package org.jacop.fz.constraints;

import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.Node;
import org.jacop.fz.SimpleNode;
import org.jacop.fz.Tables;

/**
 * Finds the products whose declared domain reaches beyond JaCoP's integer range but whose value
 * matters only through comparisons with values inside the range, so that they can be posted as
 * {@link org.jacop.constraints.XmulYeqZSaturated} instead of {@link org.jacop.constraints.XmulYeqZ}
 * over the narrowed domain.
 *
 * <p>Narrowing the domain of z in {@code int_times(x, y, z)} to the range removes every pair of
 * factors whose product does not fit, which can be a solution: MiniZinc compiles {@code tree[i] ==
 * Mul -> val[i] = val[l] * val[r]} (2022 arithmetic-target) to a product of two values up to 68,720
 * declared 0..4,722,438,400 and used only in {@code int_eq_imp(val[i], z, b)}; a node that adds two
 * large values still has the product of the pair. The completed search then proves nothing. The
 * saturated product keeps every pair of factors: z takes the end of the range for any product at or
 * beyond it. A comparison of z with a value strictly inside the range has the same truth value for
 * the product and for the end of the range, so every solution of the model as declared maps to a
 * solution of the posted model with z saturated, and back with z the product. This is the
 * representation of values beyond a type by a saturated sentinel, as in the interval arithmetic of
 * bound propagation (Moore, Interval Analysis, Prentice-Hall, 1966).
 *
 * <p>A product z qualifies when
 *
 * <ul>
 *   <li>its declared domain was narrowed and contains every product of the declared domains of its
 *       factors, so that the int_times constraint itself restricts nothing;
 *   <li>it is defined by exactly one int_times over two variables other than z, neither narrowed;
 *   <li>every other constraint that names it, also through an array, is int_eq, int_ne, int_le or
 *       int_lt, or their _reif or _imp forms, with z as one argument and as the other a constant or
 *       a variable declared strictly inside JaCoP's range;
 *   <li>it is not printed, not the objective, and no declaration makes it equal to another
 *       variable.
 * </ul>
 */
public final class SaturatedProducts {

  private static final Set<String> COMPARISONS =
      Set.of(
          "int_eq",
          "int_ne",
          "int_le",
          "int_lt",
          "int_eq_reif",
          "int_ne_reif",
          "int_le_reif",
          "int_lt_reif",
          "int_eq_imp",
          "int_ne_imp",
          "int_le_imp",
          "int_lt_imp");

  private final Support support;
  // candidates -> {defining products, other occurrences that are comparisons, other occurrences}
  private final Map<IntVar, int[]> uses = new IdentityHashMap<>();

  private SaturatedProducts(Support support) {
    this.support = support;
  }

  /**
   * The products of the model that may be posted saturated.
   *
   * @param support the support of the FlatZinc front end, after the declared domains are recorded
   * @param astTree the root of the parsed model
   * @param objective the variable of the objective, or null
   * @return the products, as the declarations name them
   */
  public static Set<IntVar> find(Support support, SimpleNode astTree, IntVar objective) {
    Tables dictionary = support.dictionary;
    if (!dictionary.boundedDomainsClamped()
        || support.options != null && support.options.proof() != null) {
      return Set.of();
    }
    SaturatedProducts products = new SaturatedProducts(support);
    for (IntVar v : dictionary.narrowedVariables()) {
      if (v != objective
          && dictionary.clampedDeclaredBounds(v) != null
          && !dictionary.isOutput(v)
          && !declaredEqual(dictionary, v)) {
        products.uses.put(v, new int[3]);
      }
    }
    if (products.uses.isEmpty()) {
      return Set.of();
    }
    support.forEachConstraint(astTree, products::visit);
    Set<IntVar> found = Collections.newSetFromMap(new IdentityHashMap<>());
    products.uses.forEach(
        (v, count) -> {
          if (count[0] == 1 && count[2] == 0) {
            found.add(v);
          }
        });
    return found;
  }

  private static boolean declaredEqual(Tables dictionary, IntVar v) {
    for (IntVar[] pair : dictionary.declaredEqualities()) {
      if (pair[0] == v || pair[1] == v) {
        return true;
      }
    }
    return false;
  }

  private void visit(ASTConstElem node) {
    Map<IntVar, Boolean> named = new IdentityHashMap<>();
    occurrences(node, named);
    if (named.isEmpty()) {
      return;
    }
    String name = node.getName();
    for (IntVar v : named.keySet()) {
      int[] count = uses.get(v);
      if ("int_times".equals(name) && definingProduct(node, v)) {
        count[0]++;
      } else if (COMPARISONS.contains(name) && insensitiveComparison(node, v)) {
        count[1]++;
      } else {
        count[2]++;
      }
    }
  }

  // int_times(x, y, v) over variables x, y other than v, not narrowed, whose products v contains
  private boolean definingProduct(ASTConstElem node, IntVar v) {
    try {
      ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
      ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
      ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);
      if (p1.getType() != 2 || p2.getType() != 2 || p3.getType() != 2) {
        return false;
      }
      IntVar x = support.dictionary.getVariable(p1.getIdent());
      IntVar y = support.dictionary.getVariable(p2.getIdent());
      if (support.dictionary.getVariable(p3.getIdent()) != v || x == null || y == null) {
        return false;
      }
      if (x == v || y == v || uses.containsKey(x) || uses.containsKey(y)) {
        return false;
      }
      if (support.dictionary.clampedDeclaredBounds(x) != null
          || support.dictionary.clampedDeclaredBounds(y) != null) {
        return false;
      }
      long[] declared = support.dictionary.clampedDeclaredBounds(v);
      long[] dx = support.dictionary.declaredBounds(x);
      long[] dy = support.dictionary.declaredBounds(y);
      long[] corners = {dx[0] * dy[0], dx[0] * dy[1], dx[1] * dy[0], dx[1] * dy[1]};
      for (long p : corners) {
        if (p < declared[0] || p > declared[1]) {
          return false;
        }
      }
      // x * x reaches 0 inside a domain around 0, which is no corner
      return x != y || dx[0] > 0 || dx[1] < 0 || declared[0] <= 0 && declared[1] >= 0;
    } catch (RuntimeException _) {
      return false;
    }
  }

  // a comparison of v, as one argument, with a constant or a variable strictly inside the range
  private boolean insensitiveComparison(ASTConstElem node, IntVar v) {
    try {
      ASTScalarFlatExpr a = (ASTScalarFlatExpr) node.jjtGetChild(0);
      ASTScalarFlatExpr b = (ASTScalarFlatExpr) node.jjtGetChild(1);
      boolean first = names(a, v);
      boolean second = names(b, v);
      if (first == second) {
        return false;
      }
      if (node.jjtGetNumChildren() > 2 && names((ASTScalarFlatExpr) node.jjtGetChild(2), v)) {
        return false;
      }
      ASTScalarFlatExpr other = first ? b : a;
      long low;
      long high;
      if (other.getType() == 0) {
        low = support.getInt(other);
        high = low;
      } else if (other.getType() == 2) {
        IntVar w = support.dictionary.getVariable(other);
        if (w == null || uses.containsKey(w)) {
          return false;
        }
        long[] declared = support.dictionary.declaredBounds(w);
        low = declared[0];
        high = declared[1];
      } else {
        return false;
      }
      return low > IntDomain.MIN_INT && high < IntDomain.MAX_INT;
    } catch (RuntimeException _) {
      return false;
    }
  }

  private boolean names(ASTScalarFlatExpr e, IntVar v) {
    return e.getType() == 2 && support.dictionary.getVariable(e) == v;
  }

  // the candidates a constraint names, also through arrays
  private void occurrences(Node node, Map<IntVar, Boolean> out) {
    if (node instanceof ASTScalarFlatExpr e && (e.getType() == 2 || e.getType() == 3)) {
      IntVar[] array = support.dictionary.getVariableArray(e.getIdent());
      if (array != null) {
        for (IntVar v : array) {
          if (uses.containsKey(v)) {
            out.put(v, true);
          }
        }
      } else {
        IntVar v = support.dictionary.getVariable(e);
        if (v != null && uses.containsKey(v)) {
          out.put(v, true);
        }
      }
    }
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      occurrences(node.jjtGetChild(i), out);
    }
  }
}
