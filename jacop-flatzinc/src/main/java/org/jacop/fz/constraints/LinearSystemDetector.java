/*
 * LinearIntDomSumsetTest.java
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
import org.jacop.constraints.LinearEqualities;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * It collects the int_lin_eq constraints of a model and gives them to {@link LinearEqualities}:
 * each equality divided by its GCD, and the components of the equalities that do not merely define
 * a variable reduced to their Hermite normal form, which proves them infeasible over the integers
 * or removes from each variable the values outside the residue class the lattice of solutions
 * leaves it. The equalities themselves are posted as before.
 *
 * <p>With the linear relaxation on, a component that looks like a market split problem (at least
 * two equalities of at least five variables each, a coefficient of at least 10 and domains of at
 * most 100 values) is also reformulated as Aardal, Hurkens and Lenstra do (Math. of OR 25(3),
 * 2000): new variables λ over a reduced basis of the lattice, x = x0 + Σ λ_k q_k, which the
 * relaxation takes in as rows, and which are searched first ({@link #lattice()}).
 *
 * <p>System properties: {@code org.jacop.fz.lattice=false} turns it off; {@code
 * org.jacop.fz.latticeReformulate} is {@code auto} (default), {@code on} (every component) or
 * {@code off}; {@code jacop.fz.latticeVars} and {@code jacop.fz.latticeRows} (default 300 each)
 * bound the components given a normal form.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LinearSystemDetector {

  static final int MAX_VARS = Integer.getInteger("jacop.fz.latticeVars", 300);

  static final int MAX_ROWS = Integer.getInteger("jacop.fz.latticeRows", 300);

  private static final String REFORMULATE =
      System.getProperty("org.jacop.fz.latticeReformulate", "auto");

  private final Support support;

  private final List<LinearEqualities.Row> rows = new ArrayList<>();

  private final List<IntVar> lattice = new ArrayList<>();

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public LinearSystemDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.lattice is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.lattice"));
  }

  /**
   * It reads the equalities of the model and prunes the domains by their lattices.
   *
   * @param astTree the root of the parsed model.
   * @param relaxation whether the linear relaxation will be imposed, which the reformulation needs.
   * @throws org.jacop.core.FailException when the equalities have no integer solution.
   */
  public void detect(SimpleNode astTree, boolean relaxation) {
    support.forEachConstraint(astTree, this::collect);
    if (rows.isEmpty()) {
      return;
    }
    LinearEqualities le = new LinearEqualities(support.store);
    le.setLimits(MAX_VARS, MAX_ROWS);
    if (relaxation && "on".equals(REFORMULATE)) {
      le.setReformulate(true);
    } else if (relaxation && "auto".equals(REFORMULATE)) {
      le.setReformulate(this::marketSplit);
    }
    le.apply(rows);
    lattice.addAll(le.lattice);
    if (support.options.debug() || support.options.searchStatistics()) {
      FzConsole.println(
          "%%%mzn-stat: latticeComponents="
              + le.components
              + "\n%%%mzn-stat: latticeRows="
              + le.componentRows
              + "\n%%%mzn-stat: latticeDefinitions="
              + le.definitions
              + "\n%%%mzn-stat: latticePrunedVars="
              + le.prunedVariables
              + "\n%%%mzn-stat: latticePrunedValues="
              + le.prunedValues
              + "\n%%%mzn-stat: latticeVars="
              + le.lattice.size()
              + "\n%%%mzn-stat-end");
    }
  }

  /**
   * The variables λ of the reformulated components, to be searched first.
   *
   * @return the variables, empty when nothing was reformulated.
   */
  public List<IntVar> lattice() {
    return lattice;
  }

  // a component like a market split problem
  private boolean marketSplit(List<LinearEqualities.Row> component) {
    if (component.size() < 2) {
      return false;
    }
    long largest = 0;
    for (LinearEqualities.Row r : component) {
      if (r.x().length < 5) {
        return false;
      }
      for (int i = 0; i < r.x().length; i++) {
        largest = Math.max(largest, Math.abs((long) r.a()[i]));
        if (r.x()[i].getSize() > 100) {
          return false;
        }
      }
    }
    return largest >= 10;
  }

  private void collect(ASTConstElem node) {
    if (!"int_lin_eq".equals(node.getName()) || node.jjtGetNumChildren() != 3) {
      return;
    }
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] x = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int b = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (a != null && x != null && a.length == x.length) {
      rows.add(new LinearEqualities.Row(x, a, b));
    }
  }
}
