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
 * <p>Linear equations whose odd-coefficient variables are 0/1 (or of one parity) give rows too,
 * also when written as two opposite inequalities; {@code org.jacop.fz.xorZeroOne=false} leaves out
 * the equations over 0/1 variables only.
 *
 * <p>Clauses that encode parities give rows too (see {@link #clauseRows()}). A component of plain
 * rows read from clauses only is left out when its rows and variables form a tree (a Berge-acyclic
 * system): unit propagation on the clauses is then as strong as Gauss-Jordan elimination, since arc
 * consistency on each row of a Berge-acyclic network is global consistency (Beeri, Fagin, Maier and
 * Yannakakis, J. ACM 30(3), 1983), and the XORs of circuits (adders, multipliers) form such trees,
 * where the system would only slow the search.
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

  // equations over 0/1 variables enter the system (see linear(int[], IntVar[], int))
  static final boolean ZERO_ONE_EQUALITIES =
      !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.xorZeroOne"));

  // the longest inequality matched with its opposite into an equation
  static final int MAX_PAIRED_LENGTH = 64;

  // the inequalities over 0/1 variables not yet matched, by their terms
  private final Map<Map<IntVar, Integer>, Integer> lessEquals = new HashMap<>();

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

  int linearRows;

  /** Statistics: the rows from equations over 0/1 variables only. */
  int zeroOneRows;

  /** Statistics: the equations read as two opposite inequalities. */
  int pairedRows;

  /** Statistics: the parity rows recovered from clauses. */
  int clauseRows;

  /** Statistics: the systems of clause rows left out because their rows form no cycle. */
  int acyclicSystems;

  // the rows that are parities read from clauses, whose clauses the model keeps
  private final java.util.BitSet fromClauses = new java.util.BitSet();

  // the parities encoded as clauses enter the system (see clause(IntVar[], IntVar[]))
  static final boolean CLAUSES =
      !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.xorClauses"));

  // the longest parity recovered from clauses: one of k variables takes 2^(k-1) clauses
  static final int MAX_CLAUSE_XOR = Integer.getInteger("jacop.fz.xorClauseLength", 8);

  // the clauses of at most MAX_CLAUSE_XOR variables by their variables (sorted columns), each
  // with the points it excludes: bit i is the value of the i-th column at which the clause is false
  private final Map<Columns, long[]> clauses = new HashMap<>();

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
    lessEquals.clear();
    clauseRows();
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
      if (members.stream().allMatch(fromClauses::get) && acyclic(members, n)) {
        // unit propagation on the clauses of a Berge-acyclic system already reaches the
        // fixpoint of Gauss-Jordan elimination; the system would only slow the search
        acyclicSystems++;
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
    if (support.options.searchStatistics() && systems + acyclicSystems > 0) {
      FzConsole.println(
          "%%%mzn-stat: xorSystems="
              + systems
              + "\n%%%mzn-stat: xorSystemRows="
              + systemRows
              + "\n%%%mzn-stat: xorZeroOneRows="
              + zeroOneRows
              + "\n%%%mzn-stat: xorPairedRows="
              + pairedRows
              + "\n%%%mzn-stat: xorClauseRows="
              + clauseRows
              + "\n%%%mzn-stat: xorAcyclicSystems="
              + acyclicSystems
              + "\n%%%mzn-stat: xorQuadraticRows="
              + quadraticRows
              + "\n%%%mzn-stat: xorProducts="
              + products
              + "\n%%%mzn-stat-end");
    }
    if (support.options.debug() && systems > 0) {
      FzConsole.println(
          "% XorSystem: "
              + systems
              + " systems, "
              + systemRows
              + " rows, "
              + tableRows
              + " rows from tables, "
              + linearRows
              + " rows from linear equations, "
              + clauseRows
              + " rows from clauses");
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
      case "bool_clause" -> {
        if (CLAUSES && node.jjtGetNumChildren() == 2) {
          clause(
              support.getVarArray((SimpleNode) node.jjtGetChild(0)),
              support.getVarArray((SimpleNode) node.jjtGetChild(1)));
        }
      }
      case "bool_not" -> row(new IntVar[] {aVar(node, 0), aVar(node, 1)}, 1);
      case "bool_eq" -> row(new IntVar[] {aVar(node, 0), aVar(node, 1)}, 0);
      // r = (a == b): a xor b xor r = 1
      case "bool_eq_reif" -> row(new IntVar[] {aVar(node, 0), aVar(node, 1), aVar(node, 2)}, 1);
      // r = (a != b): a xor b xor r = 0
      case "bool_ne_reif" -> row(new IntVar[] {aVar(node, 0), aVar(node, 1), aVar(node, 2)}, 0);
      case "int_lin_eq" -> {
        if (node.jjtGetNumChildren() == 3) {
          linear(node);
        }
      }
      case "int_lin_le" -> {
        if (node.jjtGetNumChildren() == 3 && ZERO_ONE_EQUALITIES) {
          lessEqual(node);
        }
      }
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

  /**
   * It records a clause {@code pos_1 or ... or not neg_1 or ...} over at most {@link
   * #MAX_CLAUSE_XOR} variables. A clause with a variable fixed to the value that satisfies it holds
   * and is left out; a variable fixed to the other value is dropped from it.
   */
  private void clause(IntVar[] pos, IntVar[] neg) {
    if (pos.length + neg.length > MAX_CLAUSE_XOR || pos.length + neg.length < 2) {
      return;
    }
    int[] cols = new int[pos.length + neg.length];
    boolean[] negated = new boolean[cols.length];
    int size = 0;
    for (int s = 0; s < 2; s++) {
      IntVar[] lits = s == 0 ? pos : neg;
      for (IntVar v : lits) {
        if (v.min() < 0 || v.max() > 1) {
          return;
        }
        if (v.singleton()) {
          if ((v.value() == 1) == (s == 0)) {
            // the literal is true, the clause holds
            return;
          }
          continue;
        }
        int c = node(v);
        for (int j = 0; j < size; j++) {
          if (cols[j] == c) {
            if (negated[j] != (s == 1)) {
              // x or not x
              return;
            }
            c = -1;
            break;
          }
        }
        if (c >= 0) {
          cols[size] = c;
          negated[size] = s == 1;
          size++;
        }
      }
    }
    if (size < 2) {
      return;
    }
    // sorted columns; the excluded point has the negated variables at 1
    int[] sorted = Arrays.copyOf(cols, size);
    Arrays.sort(sorted);
    int point = 0;
    for (int j = 0; j < size; j++) {
      if (negated[j]) {
        point |= 1 << Arrays.binarySearch(sorted, cols[j]);
      }
    }
    long[] points = clauses.computeIfAbsent(new Columns(sorted), k -> new long[4]);
    points[point >>> 6] |= 1L << (point & 63);
  }

  /**
   * It adds a parity row for each set of k variables whose clauses exclude all 2^(k-1) points of
   * one parity, the CNF encoding of {@code x_1 xor ... xor x_k = p}, as CryptoMiniSat finds the
   * XORs of a CNF (Soos, Nohl and Castelluccia, SAT 2009). The clauses over a subset of the
   * variables count too: each excludes all points that agree with it on the subset, so an XOR whose
   * clauses were partly subsumed by shorter ones is found as well. The clauses stay posted; the
   * rows let Gauss-Jordan elimination combine the XORs, which clause learning does only with
   * exponentially long proofs on Tseitin formulas (Urquhart, J. ACM 34(1), 1987).
   *
   * <p>The sets read are the variables of each clause and, for a clause of at least three
   * variables, those variables with the one more variable of each clause that shares all but that
   * one with it, up to {@link #MAX_CLAUSE_XOR} variables. On a set whose clauses exclude exactly
   * half of the points, the clauses are equivalent to one equation over GF(2), the algebraic normal
   * form of the excluded points (a polynomial whose value is 1 exactly at them) equal to 0. When it
   * has degree 2 its products {@code a b} become 0/1 variables {@code m = a and b}, so the equation
   * is a parity row over variables and products, the linearisation of Bosphorus (Choo, Soos, Chai
   * and Meel, ICTAI 2019). That reads an XOR of disjunctions, {@code (a or b) xor (c or d) xor
   * ...}, since {@code a or b = a + b + a b} (CNFs lifted by substitution, as in the SAT
   * Competition random-graph-xorsat and or_randxor families). Products are kept only when another
   * row has them too; with the product in one row only, Gauss-Jordan elimination learns nothing
   * from the row that its clauses do not say.
   */
  private void clauseRows() {
    if (clauses.isEmpty()) {
      return;
    }
    java.util.Set<Columns> candidates = new java.util.LinkedHashSet<>(clauses.keySet());
    if (QUADRATIC) {
      candidates.addAll(extendedSets());
    }
    java.util.Set<String> seenRows = new java.util.HashSet<>();
    List<int[]> quadratic = new ArrayList<>();
    for (Columns c : candidates) {
      support.checkTimeOut();
      int[] cols = c.cols;
      int k = cols.length;
      long[] excluded = excludedPoints(cols);
      if (excluded == null) {
        continue;
      }
      int[] count = {0, 0};
      countPoints(excluded, k, count);
      boolean linear = false;
      for (int q = 0; q < 2; q++) {
        if (count[q] == 1 << (k - 1)) {
          // every point of parity q is excluded: the xor of the variables is 1 - q
          linear = true;
          if (seenRows.add(Arrays.toString(cols) + q)) {
            IntVar[] x = new IntVar[k];
            for (int j = 0; j < k; j++) {
              x[j] = vars.get(cols[j]);
            }
            clauseRows++;
            int before = rows.size();
            row(x, 1 - q);
            if (rows.size() > before) {
              fromClauses.set(before);
            }
          }
        }
      }
      if (!linear && QUADRATIC && k >= 3) {
        int[] equation = quadraticForm(cols, excluded);
        if (equation != null && seenRows.add(Arrays.toString(equation))) {
          quadratic.add(equation);
        }
      }
    }
    clauses.clear();
    if (!quadratic.isEmpty()) {
      quadraticRows(quadratic);
    }
  }

  // the products a b are read from the clauses over few variables (see clauseRows)
  static final boolean QUADRATIC =
      !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.xorQuadratic"));

  // the clauses read, at most, from the occurrences of a variable to extend a set
  static final int MAX_EXTENSION_OCCURRENCES = 256;

  // -Djacop.fz.xorExtensionWork: the most clause literals that extending the sets reads (about 0.3
  // s); the sets found within it are kept. Without it MiniZinc Challenge 2024 aircraft-disassembly
  // B737NG-600-06 (109k clauses, no parity) read 83 million in 0.7 s and found nothing
  static final long EXTENSION_WORK = Long.getLong("jacop.fz.xorExtensionWork", 40_000_000L);

  // the literals of clauses read to extend the sets of clause columns
  private long extensionWork;

  /**
   * The sets of variables of a clause of at least three variables, with the one more variable of
   * each clause that has all but one of its variables in it, of at most {@link #MAX_CLAUSE_XOR}
   * variables and with at least two such clauses.
   */
  private List<Columns> extendedSets() {
    Map<Integer, List<int[]>> occurrences = new HashMap<>();
    for (Columns c : clauses.keySet()) {
      for (int v : c.cols) {
        occurrences.computeIfAbsent(v, x -> new ArrayList<>()).add(c.cols);
      }
    }
    List<Columns> result = new ArrayList<>();
    for (Columns c : clauses.keySet()) {
      if (extensionWork > EXTENSION_WORK) {
        break;
      }
      int[] set =
          c.cols.length < 3 || c.cols.length >= MAX_CLAUSE_XOR
              ? null
              : extendedSet(c.cols, occurrences);
      if (set != null) {
        result.add(new Columns(set));
      }
    }
    return result;
  }

  // the columns of a clause with the one more variable of each clause that has all but one of its
  // variables in it, or null when fewer than two clauses do so or the set would outgrow
  // MAX_CLAUSE_XOR; such a set is dropped as soon as it does, without reading the rest of the
  // occurrences
  private int[] extendedSet(int[] cols, Map<Integer, List<int[]>> occurrences) {
    support.checkTimeOut();
    int room = MAX_CLAUSE_XOR - cols.length;
    int[] extra = new int[room + 1];
    // the extra variables so far, and the clauses that gave one
    int[] counts = {0, 0};
    for (int v : cols) {
      List<int[]> occ = occurrences.get(v);
      if (counts[0] <= room && occ.size() <= MAX_EXTENSION_OCCURRENCES) {
        extensionWork += occ.size();
        addExtras(cols, v, occ, extra, counts);
      }
    }
    int extras = counts[0];
    if (counts[1] < 2 || extras == 0 || extras > room) {
      return null;
    }
    int[] set = Arrays.copyOf(cols, cols.length + extras);
    System.arraycopy(extra, 0, set, cols.length, extras);
    Arrays.sort(set);
    return set;
  }

  // adds the one more variable of each clause of occ seen from v (see outside) to extra, until it
  // has one more than it can hold
  private void addExtras(int[] cols, int v, List<int[]> occ, int[] extra, int[] counts) {
    for (int[] d : occ) {
      extensionWork += d.length;
      int outside = outside(cols, v, d);
      if (outside >= 0) {
        counts[1]++;
        if (indexOf(extra, counts[0], outside) < 0) {
          extra[counts[0]++] = outside;
          if (counts[0] == extra.length) {
            return;
          }
        }
      }
    }
  }

  // the one variable of clause d outside the sorted columns, when d has at least two variables in
  // them and v is the first of those (each clause is seen from one variable only); -1 otherwise
  private static int outside(int[] cols, int v, int[] d) {
    int outside = -1;
    int inside = 0;
    int firstInside = -1;
    for (int w : d) {
      if (Arrays.binarySearch(cols, w) >= 0) {
        inside++;
        if (firstInside < 0) {
          firstInside = w;
        }
      } else if (outside < 0) {
        outside = w;
      } else {
        outside = Integer.MIN_VALUE;
      }
    }
    return firstInside == v && inside >= 2 && outside >= 0 ? outside : -1;
  }

  // the position of a value among the first n of an array, or -1
  private static int indexOf(int[] a, int n, int value) {
    for (int i = 0; i < n; i++) {
      if (a[i] == value) {
        return i;
      }
    }
    return -1;
  }

  /**
   * The points of the 2^k values of the columns that the clauses over them or over a subset of them
   * exclude, or null when fewer than a quarter of the points of a parity are excluded by the
   * clauses over exactly these columns and no clause has exactly these columns.
   */
  private long[] excludedPoints(int[] cols) {
    int k = cols.length;
    long[] own = clauses.get(new Columns(cols));
    long[] excluded = own == null ? new long[4] : own.clone();
    if (own != null) {
      int[] count = {0, 0};
      countPoints(excluded, k, count);
      // an XOR of k variables has 2^(k-1) clauses; at least half of them over all k variables
      if (Math.max(count[0], count[1]) * 2 < 1 << (k - 1) && !QUADRATIC) {
        return null;
      }
    }
    // the clauses over proper subsets of the columns, by the mask of the columns they use
    for (int mask = (1 << k) - 2; mask > 0; mask--) {
      if (Integer.bitCount(mask) < 2) {
        continue;
      }
      int[] sub = new int[Integer.bitCount(mask)];
      int n = 0;
      for (int j = 0; j < k; j++) {
        if ((mask >>> j & 1) != 0) {
          sub[n++] = cols[j];
        }
      }
      long[] subPoints = clauses.get(new Columns(sub));
      if (subPoints == null) {
        continue;
      }
      int free = ((1 << k) - 1) & ~mask;
      for (int q = 0; q < 1 << sub.length; q++) {
        if ((subPoints[q >>> 6] >>> (q & 63) & 1) != 0) {
          // every point of the k columns that agrees with q on the mask
          int fixedBits = deposit(q, mask);
          for (int f = free; ; f = (f - 1) & free) {
            int point = fixedBits | f;
            excluded[point >>> 6] |= 1L << (point & 63);
            if (f == 0) {
              break;
            }
          }
        }
      }
    }
    return excluded;
  }

  /**
   * The equation over GF(2) that the excluded points of the columns give when their algebraic
   * normal form has degree 2 and at least one product: {constant, number of variables, the
   * variables, then the products as pairs of columns}; null otherwise.
   */
  private static int[] quadraticForm(int[] cols, long[] excluded) {
    int k = cols.length;
    int[] anf = new int[1 << k];
    for (int point = 0; point < 1 << k; point++) {
      anf[point] = (int) (excluded[point >>> 6] >>> (point & 63) & 1);
    }
    // the Moebius transform gives the coefficients of the monomials
    for (int i = 0; i < k; i++) {
      for (int point = 0; point < 1 << k; point++) {
        if ((point >>> i & 1) != 0) {
          anf[point] ^= anf[point ^ (1 << i)];
        }
      }
    }
    int linear = 0;
    int products = 0;
    for (int m = 1; m < 1 << k; m++) {
      if (anf[m] != 0) {
        int degree = Integer.bitCount(m);
        if (degree > 2) {
          return null;
        }
        if (degree == 1) {
          linear++;
        } else {
          products++;
        }
      }
    }
    if (products == 0) {
      return null;
    }
    int[] equation = new int[2 + linear + 2 * products];
    equation[0] = anf[0];
    equation[1] = linear;
    int n = 2;
    for (int i = 0; i < k; i++) {
      if (anf[1 << i] != 0) {
        equation[n++] = cols[i];
      }
    }
    for (int m = 1; m < 1 << k; m++) {
      if (anf[m] != 0 && Integer.bitCount(m) == 2) {
        equation[n++] = cols[Integer.numberOfTrailingZeros(m)];
        equation[n++] = cols[31 - Integer.numberOfLeadingZeros(m)];
      }
    }
    return equation;
  }

  /** Statistics: the parity rows over products recovered from clauses, and their products. */
  int quadraticRows;

  int products;

  /**
   * It adds the quadratic equations as parity rows over variables and products. An equation {@code
   * x + a b = c} defines the product as x (an AND gate, with c = 0) and gives no row; a product of
   * no gate becomes a new 0/1 variable {@code m = a and b}. Equations with a product that no other
   * equation has are left out, repeatedly.
   */
  private void quadraticRows(List<int[]> equations) {
    Map<Long, Integer> gate = new HashMap<>();
    Map<Long, Integer> gateParity = new HashMap<>();
    List<int[]> rest = new ArrayList<>();
    for (int[] e : equations) {
      if (e[1] == 1 && e.length == 5) {
        long key = pair(e[3], e[4]);
        if (!gate.containsKey(key)) {
          gate.put(key, e[2]);
          gateParity.put(key, e[0]);
          continue;
        }
      }
      rest.add(e);
    }
    // the equations whose products are all gates or shared with another equation
    boolean changed = true;
    while (changed) {
      changed = false;
      Map<Long, Integer> uses = new HashMap<>();
      for (int[] e : rest) {
        for (int i = 2 + e[1]; i < e.length; i += 2) {
          uses.merge(pair(e[i], e[i + 1]), 1, Integer::sum);
        }
      }
      List<int[]> kept = new ArrayList<>();
      for (int[] e : rest) {
        boolean keep = e[1] + (e.length - 2 - e[1]) / 2 >= 2;
        for (int i = 2 + e[1]; i < e.length && keep; i += 2) {
          long key = pair(e[i], e[i + 1]);
          keep = gate.containsKey(key) || uses.get(key) >= 2;
        }
        if (keep) {
          kept.add(e);
        } else {
          changed = true;
        }
      }
      rest = kept;
    }
    if (rest.isEmpty()) {
      return;
    }
    Map<Long, IntVar> product = new HashMap<>();
    for (int[] e : rest) {
      List<IntVar> x = new ArrayList<>();
      int parity = e[0];
      for (int i = 2; i < 2 + e[1]; i++) {
        x.add(vars.get(e[i]));
      }
      for (int i = 2 + e[1]; i < e.length; i += 2) {
        long key = pair(e[i], e[i + 1]);
        Integer g = gate.get(key);
        if (g != null) {
          // a b = x + c
          x.add(vars.get(g));
          parity ^= gateParity.get(key);
          continue;
        }
        IntVar m = product.get(key);
        if (m == null) {
          IntVar a = vars.get(e[i]);
          IntVar b = vars.get(e[i + 1]);
          m = new org.jacop.core.BooleanVar(a.getStore(), "xor_and_" + product.size());
          support.pose(new org.jacop.constraints.AndBoolSimple(a, b, m));
          product.put(key, m);
          products++;
        }
        x.add(m);
      }
      quadraticRows++;
      // the polynomial is 0: the xor of its terms is its constant
      row(x.toArray(new IntVar[0]), parity);
    }
  }

  private static long pair(int a, int b) {
    return ((long) Math.min(a, b) << 32) | Math.max(a, b);
  }

  // the excluded points of each parity among the 2^k points
  private static void countPoints(long[] excluded, int k, int[] count) {
    for (int point = 0; point < 1 << k; point++) {
      if ((excluded[point >>> 6] >>> (point & 63) & 1) != 0) {
        count[Integer.bitCount(point) & 1]++;
      }
    }
  }

  // the bits of q placed at the positions of the set bits of mask, lowest first
  private static int deposit(int q, int mask) {
    int result = 0;
    int i = 0;
    for (int m = mask; m != 0; m &= m - 1) {
      if ((q >>> i++ & 1) != 0) {
        result |= Integer.lowestOneBit(m);
      }
    }
    return result;
  }

  /** The sorted columns of a clause, a key of {@link #clauses}. */
  private record Columns(int[] cols) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Columns c && Arrays.equals(cols, c.cols);
    }

    @Override
    public int hashCode() {
      return Arrays.hashCode(cols);
    }

    @Override
    public String toString() {
      return Arrays.toString(cols);
    }
  }

  /**
   * It reads a_1 x_1 + ... + a_n x_n &lt;= k over 0/1 variables and, when the model also has -a_1
   * x_1 - ... - a_n x_n &lt;= -k (an equation written as two inequalities, as in OPB files), adds
   * the parity row of a_1 x_1 + ... + a_n x_n = k as {@link #linear} does.
   */
  private void lessEqual(ASTConstElem node) {
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    if (a.length != v.length || v.length < 2 || v.length > MAX_PAIRED_LENGTH) {
      return;
    }
    Map<IntVar, Integer> terms = new HashMap<>();
    for (int i = 0; i < v.length; i++) {
      if (v[i].min() < 0 || v[i].max() > 1) {
        return;
      }
      terms.merge(v[i], a[i], Integer::sum);
    }
    terms.values().removeIf(c -> c == 0);
    int k = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
    Map<IntVar, Integer> negated = new HashMap<>();
    terms.forEach((x, c) -> negated.put(x, -c));
    Integer other = lessEquals.get(negated);
    if (other != null && other == -k) {
      lessEquals.remove(negated);
      IntVar[] x = terms.keySet().toArray(new IntVar[0]);
      int[] c = new int[x.length];
      for (int i = 0; i < x.length; i++) {
        c[i] = terms.get(x[i]);
      }
      pairedRows++;
      linear(c, x, k);
    } else {
      lessEquals.putIfAbsent(terms, k);
    }
  }

  /**
   * It adds the parity row of a_1 x_1 + ... + a_n x_n = k when every variable with an odd
   * coefficient is a 0/1 variable or takes values of one parity only: taken modulo 2, the equation
   * is the xor of the 0/1 variables with odd coefficients, and the other terms move to the parity
   * (a count of lit neighbours that must be odd, as in the Lights Out puzzles).
   */
  private void linear(ASTConstElem node) {
    int[] a = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    linear(a, v, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)));
  }

  /**
   * It adds the parity row of a_1 x_1 + ... + a_n x_n = k, see {@link #linear(ASTConstElem)}. An
   * equation over 0/1 variables only enters (with {@code org.jacop.fz.xorZeroOne}, on by default)
   * unless it is a cardinality of value 1 or n - 1 over n variables: x_1 + ... + x_7 = 3 over the
   * edges of a vertex is one row of the parity argument of an even colouring (PB competition
   * evencolouring, ec_*; even colouring formulas are from K. Markstrom, "Locality and hard
   * SAT-instances", JSAT 2, 2006), which the rows of the whole graph give together, while
   * exactly-one rows, common in assignment models, are left out.
   */
  private void linear(int[] a, IntVar[] v, int rhs) {
    if (a.length != v.length || v.length < 2) {
      return;
    }
    int parity = rhs & 1;
    // odd coefficients per variable; a variable listed twice adds its coefficients
    Map<IntVar, Integer> odd = new IdentityHashMap<>();
    for (int i = 0; i < v.length; i++) {
      if ((a[i] & 1) != 0) {
        odd.merge(v[i], 1, (p, q) -> p ^ q);
      }
    }
    List<IntVar> x = new ArrayList<>();
    boolean nonBinary = false;
    for (Map.Entry<IntVar, Integer> e : odd.entrySet()) {
      IntVar y = e.getKey();
      if (e.getValue() == 0) {
        continue;
      }
      if (y.min() >= 0 && y.max() <= 1) {
        x.add(y);
      } else {
        int q = oneParity(y);
        if (q < 0) {
          return;
        }
        parity ^= q;
        nonBinary = true;
      }
    }
    if (x.size() < 2) {
      return;
    }
    // a plain 0/1 equation such as x_1 + ... + x_k = 1 is no parity information beyond itself
    if (!nonBinary && !(ZERO_ONE_EQUALITIES && zeroOneParity(a, v, rhs))) {
      return;
    }
    if (!nonBinary) {
      zeroOneRows++;
    }
    linearRows++;
    row(x.toArray(new IntVar[0]), parity);
  }

  // whether an equation over 0/1 variables enters the system: two variables (an equivalence or a
  // negation), or not a cardinality of value 1 or n - 1 over n variables (exactly one, or all
  // but one)
  private static boolean zeroOneParity(int[] a, IntVar[] v, int rhs) {
    if (v.length == 2) {
      return true;
    }
    int sign = Integer.signum(a[0]);
    for (int c : a) {
      if (c != sign) {
        return true;
      }
    }
    int k = sign * rhs;
    return k != 1 && k != v.length - 1;
  }

  // the parity of all values of the domain of y, or -1 when it has values of both parities
  private static int oneParity(IntVar y) {
    int q = y.min() & 1;
    for (var e = y.domain.valueEnumeration(); e.hasMoreElements(); ) {
      if ((e.nextElement() & 1) != q) {
        return -1;
      }
    }
    return q;
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

  // the rows and the n variables of a connected system form a tree in their incidence graph
  private boolean acyclic(List<Integer> members, int n) {
    long edges = 0;
    for (int r : members) {
      edges += rows.get(r).length;
    }
    return edges == members.size() + n - 1L;
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
