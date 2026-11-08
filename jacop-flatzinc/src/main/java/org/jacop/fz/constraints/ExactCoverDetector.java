/*
 * ExactCoverDetector.java
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.ExactCover;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * It collects the equalities {@code x_1 + ... + x_k = 1} over 0/1 variables of a model ({@code
 * int_lin_eq} and {@code bool_lin_eq} with all coefficients 1), splits them into connected
 * components by shared variables, and posts a redundant {@link ExactCover} for each component in
 * which a variable is in two equalities: each equality is an element, each variable an option
 * covering the equalities it is in. The equalities themselves are still posted as before. The cover
 * adds the DL+ rule of Chabert and Solnon (JAIR 2020), which the equalities do not propagate.
 *
 * <p>A component needs at least {@code org.jacop.fz.exactCoverRows} equalities (default 4). The
 * detection is opt-in, with {@code -Dorg.jacop.fz.exactCover=true}: on the models it reaches
 * (MiniZinc Challenge is and solbat, XCSP3 Cryptanalysis and Slant) it changed nothing at 240 s.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ExactCoverDetector {

  static final int MIN_ROWS = Integer.getInteger("org.jacop.fz.exactCoverRows", 4);

  private final Support support;

  private final Map<IntVar, Integer> index = new IdentityHashMap<>();
  private final List<IntVar> vars = new ArrayList<>();
  private final List<int[]> rows = new ArrayList<>();

  // union-find over the variables
  private int[] parent = new int[16];

  /** Statistics: the covers posted. */
  int covers;

  /** Statistics: the elements of the covers posted. */
  int elements;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public ExactCoverDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return true if the system property org.jacop.fz.exactCover is true.
   */
  public static boolean enabled() {
    return Boolean.getBoolean("org.jacop.fz.exactCover");
  }

  /**
   * It reads the equalities of the model and posts their covers.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    if (rows.size() < MIN_ROWS) {
      return;
    }
    Map<Integer, List<Integer>> components = new LinkedHashMap<>();
    for (int r = 0; r < rows.size(); r++) {
      components.computeIfAbsent(find(rows.get(r)[0]), k -> new ArrayList<>()).add(r);
    }
    for (List<Integer> members : components.values()) {
      if (members.size() < MIN_ROWS) {
        continue;
      }
      post(members);
    }
    if (support.options.debug() && covers > 0) {
      FzConsole.println("% ExactCover: " + covers + " covers, " + elements + " elements");
    }
  }

  private void post(List<Integer> members) {
    Map<Integer, Integer> option = new LinkedHashMap<>();
    List<List<Integer>> sets = new ArrayList<>();
    boolean shared = false;
    for (int e = 0; e < members.size(); e++) {
      for (int c : rows.get(members.get(e))) {
        Integer o = option.get(c);
        if (o == null) {
          o = sets.size();
          option.put(c, o);
          sets.add(new ArrayList<>());
        } else {
          shared = true;
        }
        sets.get(o).add(e);
      }
    }
    if (!shared) {
      return;
    }
    IntVar[] x = new IntVar[sets.size()];
    int[][] s = new int[sets.size()][];
    for (Map.Entry<Integer, Integer> entry : option.entrySet()) {
      int o = entry.getValue();
      x[o] = vars.get(entry.getKey());
      s[o] = sets.get(o).stream().mapToInt(Integer::intValue).toArray();
    }
    ExactCover cover = new ExactCover(x, s, members.size());
    support.implied(() -> support.pose(cover));
    covers++;
    elements += members.size();
  }

  private void collect(ASTConstElem node) {
    String name = node.getName();
    if (!"int_lin_eq".equals(name) && !"bool_lin_eq".equals(name)
        || node.jjtGetNumChildren() != 3) {
      return;
    }
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    if (a == null) {
      return;
    }
    for (int c : a) {
      if (c != 1) {
        return;
      }
    }
    if (!(node.jjtGetChild(2) instanceof ASTScalarFlatExpr rhs)) {
      return;
    }
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (v == null || v.length != a.length || v.length < 2) {
      return;
    }
    int b;
    try {
      b = support.getInt(rhs);
    } catch (IllegalArgumentException | ClassCastException e) {
      return;
    }
    if (b != 1) {
      return;
    }
    int[] cols = new int[v.length];
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    for (int j = 0; j < v.length; j++) {
      IntVar x = v[j];
      if (x.min() < 0 || x.max() > 1 || seen.put(x, Boolean.TRUE) != null) {
        return;
      }
      cols[j] = node(x);
    }
    int[] row = Arrays.copyOf(cols, cols.length);
    for (int j = 1; j < row.length; j++) {
      union(row[0], row[j]);
    }
    rows.add(row);
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
