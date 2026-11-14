/*
 * ConjunctionSumDetector.java
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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.ConjunctionSum;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ASTSolveExpr;
import org.jacop.fz.ASTSolveKind;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It finds a minimized objective that is a weighted sum of indicators of conjunctions of value
 * literals, {@code z = sum(t) w[t] * bool2int(l[t][1] /\ ... /\ l[t][k])} with {@code w[t] > 0},
 * and posts {@link ConjunctionSum} on it as a redundant constraint. A literal is a Boolean variable
 * or its negation, or {@code x = a} or {@code x != a} through {@code int_eq_reif} and {@code
 * int_ne_reif}, also of the {@code bool2int} of a Boolean variable. Models of soft constraints
 * written term by term, as XCSP sums of {@code and(eq(y[i], a), eq(y[j], b), x[a][b])}, flatten to
 * this form. The linear objective is still posted; the constraint adds the lower bound of the terms
 * that wait for one variable only.
 *
 * <p>Setting the system property {@code org.jacop.fz.conjunctionSum} to false turns the detection
 * off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ConjunctionSumDetector implements ParserTreeConstants {

  // the most literals the redundant constraint scans
  private static final int MAX_LITERALS = 4_000_000;

  // the widest domain of a variable in a literal
  private static final int MAX_SPAN = 64;

  private final Support support;

  private final Map<IntVar, IntVar> bool2int = new IdentityHashMap<>();
  private final Map<IntVar, IntVar[]> and = new IdentityHashMap<>();
  private final Map<IntVar, Object[]> reif = new IdentityHashMap<>();
  private final Map<IntVar, IntVar> not = new IdentityHashMap<>();
  private final List<ASTConstElem> linears = new ArrayList<>();

  private IntVar objective;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public ConjunctionSumDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.conjunctionSum is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.conjunctionSum"));
  }

  /**
   * It scans the model and posts the bound on a minimized sum of conjunctions.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    objective(astTree);
    if (objective == null) {
      return;
    }
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
    for (ASTConstElem node : linears) {
      if (sum(node)) {
        return;
      }
    }
  }

  private static SimpleNode child(SimpleNode node, int i) {
    return (SimpleNode) node.jjtGetChild(i);
  }

  private IntVar variable(ASTConstElem node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "bool2int" -> {
        IntVar b = variable(node, 0);
        IntVar i = variable(node, 1);
        if (b != i) {
          bool2int.put(i, b);
        }
      }
      case "array_bool_and" -> and.put(variable(node, 1), support.getVarArray(child(node, 0)));
      case "int_eq_reif", "int_ne_reif" -> {
        IntVar x = variable(node, 0);
        IntVar c = variable(node, 1);
        if (c.singleton() && !x.singleton()) {
          reif.put(variable(node, 2), new Object[] {x, c.value(), node.getName().equals("int_eq_reif")});
        }
      }
      case "bool_not" -> {
        IntVar a = variable(node, 0);
        IntVar b = variable(node, 1);
        not.put(b, a);
        not.put(a, b);
      }
      case "int_lin_eq" -> linears.add(node);
      default -> {
        // not part of a sum of conjunctions
      }
    }
  }

  // the variable of minimize, null otherwise
  private void objective(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() != JJTMODELEND || node.jjtGetNumChildren() == 0) {
        continue;
      }
      SimpleNode item = child(node, 0);
      SimpleNode last = child(item, item.jjtGetNumChildren() - 1);
      if (last instanceof ASTSolveKind kind
          && "minimize".equals(kind.getKind())
          && last.jjtGetNumChildren() > 0
          && child(kind, 0) instanceof ASTSolveExpr expr) {
        if (expr.getType() == 0) {
          objective = support.dictionary.getVariable(expr.getIdent());
        } else if (expr.getType() == 1) {
          IntVar[] array = support.dictionary.getVariableArray(expr.getIdent());
          objective =
              array != null && expr.getIndex() >= 0 && expr.getIndex() < array.length
                  ? array[expr.getIndex()]
                  : null;
        }
      }
    }
  }

  // one literal: its variable, value and kind
  private record Literal(IntVar x, int value, boolean eq) {}

  /** The literals whose conjunction is b = 1, or null when b is not such a conjunction. */
  private List<Literal> conjunction(IntVar b, int depth) {
    List<Literal> out = new ArrayList<>();
    IntVar[] parts = and.get(b);
    if (parts != null && depth < 4) {
      for (IntVar p : parts) {
        List<Literal> sub = conjunction(p, depth + 1);
        if (sub == null) {
          return null;
        }
        out.addAll(sub);
      }
      return out;
    }
    Literal l = literal(b, depth);
    if (l == null) {
      return null;
    }
    out.add(l);
    return out;
  }

  /** The literal b = 1 stands for. */
  private Literal literal(IntVar b, int depth) {
    if (b.min() < 0 || b.max() > 1) {
      return null;
    }
    IntVar source = bool2int.get(b);
    if (source != null && depth < 8) {
      return literal(source, depth + 1);
    }
    Object[] r = reif.get(b);
    if (r != null && depth < 8) {
      IntVar x = (IntVar) r[0];
      int value = (Integer) r[1];
      boolean eq = (Boolean) r[2];
      IntVar y = bool2int.get(x);
      if (y != null) {
        x = y;
      }
      return new Literal(x, value, eq);
    }
    IntVar a = not.get(b);
    if (a != null && depth < 8 && !reif.containsKey(a) && !bool2int.containsKey(a)) {
      return new Literal(a, 0, true);
    }
    return new Literal(b, 1, true);
  }

  // z = sum(k) w[k] * t[k] for the objective z, every t[k] a conjunction and w[k] > 0
  private boolean sum(ASTConstElem node) {
    int[] a = support.getIntArray(child(node, 0));
    IntVar[] x = support.getVarArray(child(node, 1));
    int c = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (a == null || a.length != x.length || x.length < 3) {
      return false;
    }
    int zAt = -1;
    for (int k = 0; k < x.length; k++) {
      if (x[k] == objective) {
        if (zAt >= 0) {
          return false;
        }
        zAt = k;
      }
    }
    // z * a[zAt] + sum = c with z = sum(w * t): a[zAt] = -1, other a > 0, c = 0 (or all negated)
    if (zAt < 0 || Math.abs(a[zAt]) != 1 || c != 0) {
      return false;
    }
    int sign = -a[zAt];
    int m = x.length - 1;
    IntVar[][] vars = new IntVar[m][];
    int[][] values = new int[m][];
    boolean[][] eqs = new boolean[m][];
    int[] w = new int[m];
    Set<IntVar> distinct = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
    long literals = 0;
    int t = 0;
    boolean joint = false;
    for (int k = 0; k < x.length; k++) {
      if (k == zAt) {
        continue;
      }
      int weight = sign * a[k];
      if (weight <= 0 || x[k].min() < 0 || x[k].max() > 1) {
        return false;
      }
      List<Literal> lits = conjunction(x[k], 0);
      if (lits == null) {
        lits = List.of(new Literal(x[k], 1, true));
      }
      vars[t] = new IntVar[lits.size()];
      values[t] = new int[lits.size()];
      eqs[t] = new boolean[lits.size()];
      IntVar first = null;
      for (int l = 0; l < lits.size(); l++) {
        Literal lit = lits.get(l);
        if (lit.x() == objective || (long) lit.x().max() - lit.x().min() + 1 > MAX_SPAN) {
          return false;
        }
        vars[t][l] = lit.x();
        values[t][l] = lit.value();
        eqs[t][l] = lit.eq();
        distinct.add(lit.x());
        if (first == null) {
          first = lit.x();
        } else if (first != lit.x()) {
          joint = true;
        }
      }
      literals += lits.size();
      w[t++] = weight;
    }
    // the bound adds nothing when every term has the literals of one variable only
    if (!joint || literals > MAX_LITERALS || distinct.size() >= m) {
      return false;
    }
    ConjunctionSum bound = new ConjunctionSum(vars, values, eqs, w, objective);
    bound.setDegreeWeight(0);
    if (support.options.debug() || support.options.searchStatistics()) {
      FzConsole.println(
          "%%%mzn-stat: conjunctionSumTerms="
              + m
              + "\n%%%mzn-stat: conjunctionSumVariables="
              + distinct.size());
    }
    support.delayedConstraints.add(bound);
    return true;
  }
}
