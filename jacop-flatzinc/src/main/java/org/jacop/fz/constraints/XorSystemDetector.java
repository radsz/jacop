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

  /** Statistics: the parity rows implied by tables. */
  int tableRows;

  // the 0/1 columns of a table read, at most, for its implied parities
  static final int MAX_TABLE_COLUMNS = 63;

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
      FzConsole.println(
          "% XorSystem: "
              + systems
              + " systems, "
              + systemRows
              + " rows, "
              + tableRows
              + " rows from tables");
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
          row(new IntVar[] {aVar(node, 0), aVar(node, 1), aVar(node, 2)}, 0);
        }
      }
      case "bool_not" -> row(new IntVar[] {aVar(node, 0), aVar(node, 1)}, 1);
      case "bool_eq" -> row(new IntVar[] {aVar(node, 0), aVar(node, 1)}, 0);
      // r = (a == b): a xor b xor r = 1
      case "bool_eq_reif" -> row(new IntVar[] {aVar(node, 0), aVar(node, 1), aVar(node, 2)}, 1);
      // r = (a != b): a xor b xor r = 0
      case "bool_ne_reif" -> row(new IntVar[] {aVar(node, 0), aVar(node, 1), aVar(node, 2)}, 0);
      case "jacop_table_int", "jacop_table_bool" -> {
        if (node.jjtGetNumChildren() == 2) {
          table(node, false);
        }
      }
      case "jacop_short_table_int" -> {
        if (node.jjtGetNumChildren() == 3) {
          table(node, true);
        }
      }
      default -> {
        // not a parity constraint
      }
    }
  }

  /**
   * It adds the parity constraints that a table implies on its 0/1 variables: the equations of the
   * affine hull over GF(2) of its tuples allowed by the domains, projected on those variables. A
   * table that is an XOR gives its row; a table whose tuples span the whole space gives nothing.
   */
  private void table(ASTConstElem node, boolean hasStar) {
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int k = v.length;
    int zeroOne = 0;
    for (IntVar x : v) {
      if (x.min() >= 0 && x.max() <= 1) {
        zeroOne++;
      }
    }
    // the tuples are read only for a table with at least two 0/1 variables
    if (zeroOne < 2) {
      return;
    }
    int[] tuples = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    int star = hasStar ? support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)) : 0;
    if (tuples.length == 0 || tuples.length % k != 0) {
      return;
    }
    // the 0/1 columns, one per distinct variable
    Map<IntVar, Integer> local = new IdentityHashMap<>();
    int[] bit = new int[k];
    List<IntVar> columns = new ArrayList<>();
    for (int j = 0; j < k; j++) {
      bit[j] = -1;
      if (v[j].min() >= 0 && v[j].max() <= 1) {
        Integer c = local.get(v[j]);
        if (c == null) {
          if (columns.size() == MAX_TABLE_COLUMNS) {
            continue;
          }
          c = columns.size();
          local.put(v[j], c);
          columns.add(v[j]);
        }
        bit[j] = c;
      }
    }
    int width = columns.size();
    if (width < 2) {
      return;
    }
    long first = -1;
    long[] basis = new long[width];
    int dim = 0;
    for (int t = 0; t < tuples.length / k && dim < width; t++) {
      long point = 0;
      long free = 0;
      long assigned = 0;
      boolean allowed = true;
      for (int j = 0; j < k && allowed; j++) {
        int value = tuples[t * k + j];
        if (hasStar && value == star) {
          if (bit[j] >= 0) {
            free |= 1L << bit[j];
          }
          continue;
        }
        if (!v[j].domain.contains(value)) {
          allowed = false;
        } else if (bit[j] >= 0) {
          long b = 1L << bit[j];
          // a variable listed twice takes one value
          if ((assigned & b) != 0 && ((point & b) != 0) != (value == 1)) {
            allowed = false;
          }
          assigned |= b;
          if (value == 1) {
            point |= b;
          }
        }
      }
      if (!allowed) {
        continue;
      }
      // a star on a variable listed elsewhere in the tuple is that value
      free &= ~assigned;
      if (first < 0) {
        first = point;
      } else {
        dim = insert(basis, dim, point ^ first);
      }
      while (free != 0) {
        long b = free & -free;
        free &= free - 1;
        dim = insert(basis, dim, b);
      }
    }
    if (first < 0 || dim == width) {
      return;
    }
    // reduced row echelon form of the span, then one equation per column without a pivot
    long pivots = 0;
    long[] pivot = new long[dim];
    for (int i = 0; i < dim; i++) {
      long p = Long.lowestOneBit(basis[i]);
      pivot[i] = p;
      pivots |= p;
      for (int r = 0; r < dim; r++) {
        if (r != i && (basis[r] & p) != 0) {
          basis[r] ^= basis[i];
        }
      }
    }
    for (int f = 0; f < width; f++) {
      if ((pivots & (1L << f)) != 0) {
        continue;
      }
      long a = 1L << f;
      for (int i = 0; i < dim; i++) {
        if ((basis[i] & (1L << f)) != 0) {
          a |= pivot[i];
        }
      }
      IntVar[] x = new IntVar[Long.bitCount(a)];
      int size = 0;
      for (long bits = a; bits != 0; bits &= bits - 1) {
        x[size++] = columns.get(Long.numberOfTrailingZeros(bits));
      }
      tableRows++;
      row(x, Long.bitCount(a & first) & 1);
    }
  }

  // reduces vector by the basis and adds it when it is independent
  private static int insert(long[] basis, int dim, long vector) {
    for (int i = 0; i < dim && vector != 0; i++) {
      long top = Long.highestOneBit(basis[i]);
      if ((vector & top) != 0) {
        vector ^= basis[i];
      }
    }
    if (vector == 0) {
      return dim;
    }
    // keep the basis ordered by leading bit, decreasing
    int at = dim;
    while (at > 0 && Long.highestOneBit(basis[at - 1]) < Long.highestOneBit(vector)) {
      basis[at] = basis[at - 1];
      at--;
    }
    basis[at] = vector;
    return dim + 1;
  }

  private IntVar aVar(ASTConstElem node, int i) {
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
