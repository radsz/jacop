/*
 * XorSystemDetector.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.XorSystem;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * It collects the parity constraints of a model (array_bool_xor, bool_xor, bool_not, bool_eq,
 * bool_eq_reif and bool_ne_reif, each one row {@code x_1 xor ... xor x_k = p} over GF(2)), splits
 * them into connected components by shared variables, and posts a redundant {@link XorSystem},
 * which propagates by Gauss-Jordan elimination, for each component of at least two rows with a row
 * of at least three variables. The constraints themselves are still posted as before (in LCG as
 * clauses), as CryptoMiniSat keeps the clauses of the XORs it gives its Gauss-Jordan elimination
 * (Soos, Nohl and Castelluccia, SAT 2009; Soos, Gocht and Meel, CAV 2020; see {@link XorSystem}).
 *
 * <p>Setting the system property {@code org.jacop.fz.xorSystem} to false turns it off. A component
 * with more than {@code jacop.fz.xorSystemCells} (default 50 million) row-column cells is left out,
 * as is a component of more than {@code jacop.fz.xorSystemRows} rows (default 20,000).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class XorSystemDetector implements ParserTreeConstants {

  static final long MAX_CELLS = Long.getLong("jacop.fz.xorSystemCells", 50_000_000L);

  static final int MAX_ROWS = Integer.getInteger("jacop.fz.xorSystemRows", 20_000);

  private final Support support;

  private final Map<IntVar, Integer> index = new IdentityHashMap<>();
  private final List<IntVar> vars = new ArrayList<>();
  private final List<int[]> rows = new ArrayList<>();
  private final List<Integer> parities = new ArrayList<>();

  // union-find over the variables
  private int[] parent = new int[16];

  /** Statistics: the systems posted. */
  int systems;

  /** Statistics: the rows of the systems posted. */
  int systemRows;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public XorSystemDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.xorSystem is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.xorSystem"));
  }

  /**
   * It reads the parity constraints of the model and posts their systems.
   *
   * @param astTree the root of the parsed model.
   * @throws FailException when a system fails as it is posted.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    if (rows.size() < 2) {
      return;
    }
    // the rows of each component, by its root variable
    Map<Integer, List<Integer>> components = new LinkedHashMap<>();
    for (int r = 0; r < rows.size(); r++) {
      components.computeIfAbsent(find(rows.get(r)[0]), k -> new ArrayList<>()).add(r);
    }
    Map<Integer, Integer> columns = new HashMap<>();
    for (int i = 0; i < vars.size(); i++) {
      columns.merge(find(i), 1, Integer::sum);
    }
    for (Map.Entry<Integer, List<Integer>> e : components.entrySet()) {
      List<Integer> members = e.getValue();
      int n = columns.get(e.getKey());
      if (members.size() < 2
          || members.size() > MAX_ROWS
          || (long) members.size() * n > MAX_CELLS
          || members.stream().allMatch(r -> rows.get(r).length < 3)) {
        continue;
      }
      IntVar[][] x = new IntVar[members.size()][];
      int[] p = new int[members.size()];
      for (int k = 0; k < members.size(); k++) {
        int[] row = rows.get(members.get(k));
        x[k] = new IntVar[row.length];
        for (int j = 0; j < row.length; j++) {
          x[k][j] = vars.get(row[j]);
        }
        p[k] = parities.get(members.get(k));
      }
      XorSystem system = new XorSystem(x, p);
      system.setRedundant(true);
      support.pose(system);
      systems++;
      systemRows += members.size();
    }
    if (support.options.debug() && systems > 0) {
      FzConsole.println("% XorSystem: " + systems + " systems, " + systemRows + " rows");
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "array_bool_xor" -> {
        if (node.jjtGetNumChildren() == 1) {
          row(support.getVarArray((SimpleNode) node.jjtGetChild(0)), 1);
        }
      }
      // c = a xor b
      case "bool_xor" -> {
        if (node.jjtGetNumChildren() == 3) {
          row(new IntVar[] {var(node, 0), var(node, 1), var(node, 2)}, 0);
        }
      }
      case "bool_not" -> row(new IntVar[] {var(node, 0), var(node, 1)}, 1);
      case "bool_eq" -> row(new IntVar[] {var(node, 0), var(node, 1)}, 0);
      // r = (a == b): a xor b xor r = 1
      case "bool_eq_reif" -> row(new IntVar[] {var(node, 0), var(node, 1), var(node, 2)}, 1);
      // r = (a != b): a xor b xor r = 0
      case "bool_ne_reif" -> row(new IntVar[] {var(node, 0), var(node, 1), var(node, 2)}, 0);
      default -> {
        // not a parity constraint
      }
    }
  }

  private IntVar var(ASTConstElem node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }

  // xor(x) = parity, with the fixed variables moved to the parity
  private void row(IntVar[] x, int parity) {
    int[] cols = new int[x.length];
    int size = 0;
    for (IntVar v : x) {
      if (v.min() < 0 || v.max() > 1) {
        return;
      }
      if (v.singleton()) {
        parity ^= v.value();
      } else {
        cols[size++] = node(v);
      }
    }
    if (size == 0) {
      // fixed rows are checked by the constraints themselves
      return;
    }
    int[] row = Arrays.copyOf(cols, size);
    for (int j = 1; j < size; j++) {
      union(row[0], row[j]);
    }
    rows.add(row);
    parities.add(parity);
  }

  private int node(IntVar x) {
    return index.computeIfAbsent(
        x,
        v -> {
          vars.add(v);
          int i = vars.size() - 1;
          if (i >= parent.length) {
            parent = Arrays.copyOf(parent, 2 * parent.length);
          }
          parent[i] = i;
          return i;
        });
  }

  private int find(int i) {
    while (parent[i] != i) {
      parent[i] = parent[parent[i]];
      i = parent[i];
    }
    return i;
  }

  private void union(int a, int b) {
    int ra = find(a);
    int rb = find(b);
    if (ra != rb) {
      parent[ra] = rb;
    }
  }
}
