/*
 * TranslationTilingDetector.java
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

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import org.jacop.constraints.CountValues;
import org.jacop.constraints.SumBool;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * Finds tilings of the cyclic group Z_n by translation, A ⊕ B = Z_n, written as an all different
 * over the n terms (b + a) mod n, a in A, b in B, and posts the redundant exact cover over the
 * characteristic vector of B.
 *
 * <p>The model of a tiling rhythmic canon (XCSP3 TilingRythmicCanons) states the set B by its
 * ordered elements x_1 &lt; ... &lt; x_k and the tiling by an all different over the terms (x_j +
 * a) mod n, as many terms as values, so a permutation of Z_n. The all different sees each term on
 * its own: that x_j = w is the same event for all the terms of x_j is lost, and so is the
 * order-free view of B. Auricchio, Ferrarini, Gualandi, Lanzarotto and Pernazza ("A SAT Encoding to
 * Compute Aperiodic Tiling Rhythmic Canons", CPAIOR 2022; Constraints 29, 2024) state the tiling
 * over the characteristic vector instead: c_w = 1 if and only if w is in B, and for every value v
 * exactly one of c_{v - a}, a in A, is 1 (Coven and Meyerowitz's tiling condition as an exact
 * cover), which a SAT solver enumerates for n = 420 in seconds.
 *
 * <p>The detector reads the terms through the flattened definitions s = x + a (int_lin_eq) and t =
 * s mod n (int_mod); a term that is x itself has the shift 0, and a constant term is a value
 * covered by a fixed element. When every not fixed base variable has the same set of shifts A and
 * the terms are as many as the values, it posts c_w = count of w among the base variables
 * (CountValues), the exact cover of every value (SumBool, = 0 for the values the constants cover)
 * and the size of B. The system property {@code org.jacop.fz.translationTiling=false} turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class TranslationTilingDetector {

  /** At most this many values: the cover posts one sum per value. */
  static final int MAX_VALUES = 1 << 14;

  private final Support support;

  private final Map<IntVar, Integer> mods = new IdentityHashMap<>();

  private final List<IntVar[]> alldiffs = new ArrayList<>();

  private final List<BooleanVar> characteristic = new ArrayList<>();

  private int tilings;

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public TranslationTilingDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.translationTiling is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.translationTiling"));
  }

  /**
   * The characteristic vectors of the tilings found, one variable per value.
   *
   * @return the 0/1 variables the detector created.
   */
  public List<BooleanVar> characteristic() {
    return characteristic;
  }

  /**
   * It reads the model and posts the exact cover of each tiling it finds.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    for (IntVar[] terms : alldiffs) {
      tiling(terms);
    }
    if (support.options.debug()) {
      FzConsole.println("% translation tilings: " + tilings);
    }
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_alldiff", "jacop_alldistinct", "all_different_int" ->
          alldiffs.add(support.getVarArray((SimpleNode) node.jjtGetChild(0)));
      case "int_mod" -> {
        IntVar x = variable(node, 0);
        IntVar n = variable(node, 1);
        IntVar t = variable(node, 2);
        if (n.singleton() && n.value() > 0 && !x.singleton() && !t.singleton()) {
          mods.put(t, n.value());
          defined.put(t, x);
        }
      }
      case "int_lin_eq" -> {
        // p - m = rhs, as [1, -1] * [p, m] = rhs in either order: p = m + rhs and m = p - rhs
        int[] c = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        if (c == null
            || c.length != 2
            || c[0] + c[1] != 0
            || Math.abs(c[0]) != 1
            || v[0] == v[1]
            || v[0].singleton()
            || v[1].singleton()) {
          return;
        }
        long rhs = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));
        IntVar p = c[0] == 1 ? v[0] : v[1];
        IntVar m = c[0] == 1 ? v[1] : v[0];
        shifts.computeIfAbsent(p, k -> new ArrayList<>()).add(new Shift(m, rhs));
        shifts.computeIfAbsent(m, k -> new ArrayList<>()).add(new Shift(p, -rhs));
      }
      default -> {
        // not part of a tiling
      }
    }
  }

  /** s = base + shift. */
  private record Shift(IntVar base, long shift) {}

  private final Map<IntVar, List<Shift>> shifts = new IdentityHashMap<>();

  private final Map<IntVar, IntVar> defined = new IdentityHashMap<>();

  private void tiling(IntVar[] terms) {
    int n = terms.length;
    if (n < 4 || n > MAX_VALUES) {
      return;
    }
    // the modulus: every term defined by a mod uses n
    for (IntVar t : terms) {
      Integer m = mods.get(t);
      if (m != null && m != n) {
        return;
      }
    }
    TreeSet<Integer> constants = new TreeSet<>();
    Map<IntVar, TreeSet<Integer>> shiftsOf = new LinkedHashMap<>();
    for (IntVar t : terms) {
      if (t.singleton()) {
        int c = t.value();
        if (c < 0 || c >= n || !constants.add(c)) {
          return;
        }
        continue;
      }
      IntVar base;
      long a;
      IntVar s = defined.get(t);
      if (s == null) {
        base = t;
        a = 0;
      } else {
        Shift sh = baseOf(s);
        if (sh == null) {
          return;
        }
        base = sh.base();
        a = sh.shift();
      }
      if (base.min() < 0 || base.max() >= n || a < 0 || a >= n) {
        return;
      }
      if (!shiftsOf.computeIfAbsent(base, k -> new TreeSet<>()).add((int) a)) {
        return;
      }
    }
    if (shiftsOf.isEmpty()) {
      return;
    }
    TreeSet<Integer> shiftSet = null;
    for (TreeSet<Integer> as : shiftsOf.values()) {
      if (shiftSet == null) {
        shiftSet = as;
      } else if (!shiftSet.equals(as)) {
        return;
      }
    }
    int[] a = shiftSet.stream().mapToInt(Integer::intValue).toArray();
    if (a.length < 2 || (long) shiftsOf.size() * a.length + constants.size() != n) {
      return;
    }
    IntVar[] base = shiftsOf.keySet().toArray(new IntVar[0]);
    Store store = base[0].getStore();
    BooleanVar[] c = new BooleanVar[n];
    int[] values = new int[n];
    for (int w = 0; w < n; w++) {
      c[w] = new BooleanVar(store, "tiling" + tilings + "_" + w);
      values[w] = w;
      characteristic.add(c[w]);
    }
    support.pose(new CountValues(base, c, values));
    support.pose(new SumBool(c, "==", support.dictionary.getConstant(base.length)));
    IntVar zero = support.dictionary.getConstant(0);
    IntVar one = support.dictionary.getConstant(1);
    for (int v = 0; v < n; v++) {
      IntVar[] cover = new IntVar[a.length];
      for (int i = 0; i < a.length; i++) {
        cover[i] = c[Math.floorMod(v - a[i], n)];
      }
      support.pose(new SumBool(cover, "==", constants.contains(v) ? zero : one));
    }
    String search = System.getProperty("org.jacop.fz.translationTiling.search", "add");
    if ("first".equals(search)) {
      support.dictionary.searchFirst(List.of(c));
    } else if ("add".equals(search)) {
      for (BooleanVar b : c) {
        support.dictionary.addSearchVar(b);
      }
    }
    tilings++;
  }

  // the base variable and shift of s = base + shift, preferring a base that is no sum itself
  private Shift baseOf(IntVar s) {
    List<Shift> list = shifts.get(s);
    if (list == null) {
      return null;
    }
    for (Shift sh : list) {
      if (!defined.containsKey(sh.base()) && sh.base() != s) {
        return sh;
      }
    }
    return null;
  }

  private IntVar variable(ASTConstElem node, int i) {
    return support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(i));
  }
}
