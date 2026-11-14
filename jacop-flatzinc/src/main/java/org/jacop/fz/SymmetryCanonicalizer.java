/*
 * SymmetryCanonicalizer.java
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

package org.jacop.fz;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntVar;
import org.jacop.search.ls.LocalSearch;

/**
 * Maps a solution of a model without its symmetry breaking constraints onto a symmetric solution
 * that satisfies them, for local search, which then need not evaluate them. It knows the
 * constraints {@link SymmetryBreaking} posted and the symmetries behind them:
 *
 * <ul>
 *   <li>a lex chain over interchangeable columns: the columns are sorted;
 *   <li>a value precedence over interchangeable values: the values are renamed in the order of
 *       their first use (Law and Lee, "Symmetry breaking constraints for value symmetries in
 *       constraint satisfaction", Constraints 11(2-3), 2006);
 *   <li>a lex-leader constraint {@code x <=lex g(x)} of a variable symmetry g (Crawford, Ginsberg,
 *       Luks and Roy, KR 1996): a solution s that breaks it is replaced by the solution s o g,
 *       which is lexicographically smaller.
 * </ul>
 *
 * <p>Each step gives a symmetric solution of the model, and the steps are repeated until none
 * changes the assignment, at most {@link #ROUNDS} times. The constraints are lex-leader constraints
 * of one order, so a solution that is smallest in its orbit satisfies all of them; the steps
 * descend towards one, and the store checks whatever they reach.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class SymmetryCanonicalizer implements LocalSearch.Canonicalizer {

  /** The most rounds of steps over all the constraints. */
  static final int ROUNDS = 100;

  private final List<Constraint> constraints = new ArrayList<>();
  private final List<IntVar[][]> chains = new ArrayList<>();
  private final List<IntVar[]> precedenceVars = new ArrayList<>();
  private final List<int[]> precedenceValues = new ArrayList<>();
  // lex-leader constraints: x <=lex y (or y <=lex x when largest), and the symmetry, from -> to
  private final List<IntVar[]> lexX = new ArrayList<>();
  private final List<IntVar[]> lexY = new ArrayList<>();
  private final BitSet lexLargest = new BitSet();
  private final List<IntVar[]> moveFrom = new ArrayList<>();
  private final List<IntVar[]> moveTo = new ArrayList<>();
  // Schreier-Sims cuts lo <= hi and the moves of the symmetry that maps them
  private final List<IntVar> cutLo = new ArrayList<>();
  private final List<IntVar> cutHi = new ArrayList<>();
  private final List<List<IntVar[][]>> cutMoves = new ArrayList<>();
  // a constraint whose symmetry is not known, or moves values too: no canonical form
  private boolean incomplete;

  private IntVar[] indexed;
  private Map<IntVar, Integer> index;

  void chain(Constraint c, IntVar[][] columns) {
    constraints.add(c);
    chains.add(columns);
  }

  void precedence(Constraint c, IntVar[] xs, int[] chain) {
    constraints.add(c);
    precedenceVars.add(xs);
    precedenceValues.add(chain);
  }

  /**
   * Records a Schreier-Sims cut lo <= hi and the symmetry that moves the value of hi onto the
   * variable of lo, as moves applied in turn; null when the symmetry is not known.
   */
  void cut(Constraint c, IntVar lo, IntVar hi, List<IntVar[][]> moves) {
    constraints.add(c);
    if (moves == null) {
      incomplete = true;
      return;
    }
    cutLo.add(lo);
    cutHi.add(hi);
    cutMoves.add(moves);
  }

  /**
   * Records a lex-leader constraint and its symmetry; from and to are null when the symmetry also
   * moves values.
   */
  void lex(Constraint c, IntVar[] x, IntVar[] y, boolean largest, IntVar[] from, IntVar[] to) {
    constraints.add(c);
    if (from == null) {
      incomplete = true;
      return;
    }
    lexX.add(x);
    lexY.add(y);
    lexLargest.set(lexX.size() - 1, largest);
    moveFrom.add(from);
    moveTo.add(to);
  }

  /**
   * Returns the symmetry breaking constraints posted, which local search may leave out.
   *
   * @return the constraints, empty when some symmetry is not known.
   */
  List<Constraint> constraints() {
    return incomplete ? List.of() : Collections.unmodifiableList(constraints);
  }

  @Override
  public boolean canonicalize(IntVar[] vars, int[] values) {
    if (vars != indexed) {
      indexed = vars;
      index = new IdentityHashMap<>();
      for (int i = 0; i < vars.length; i++) {
        index.put(vars[i], i);
      }
    }
    try {
      for (int round = 0; round < ROUNDS; round++) {
        boolean changed = false;
        for (IntVar[][] columns : chains) {
          changed |= sort(columns, values);
        }
        for (int k = 0; k < precedenceVars.size(); k++) {
          changed |= rename(precedenceVars.get(k), precedenceValues.get(k), values);
        }
        for (int k = 0; k < lexX.size(); k++) {
          changed |= descend(k, values);
        }
        for (int k = 0; k < cutLo.size(); k++) {
          if (value(cutLo.get(k), values) > value(cutHi.get(k), values)) {
            for (IntVar[][] m : cutMoves.get(k)) {
              move(m[0], m[1], values);
            }
            changed = true;
          }
        }
        if (!changed) {
          return true;
        }
      }
    } catch (MissingVariable _) {
      return false;
    }
    return false;
  }

  /** A variable of a symmetry breaking constraint that local search does not assign. */
  private static final class MissingVariable extends RuntimeException {
    private static final long serialVersionUID = 1L;

    MissingVariable() {
      super(null, null, false, false);
    }
  }

  private int at(IntVar x) {
    if (x.singleton()) {
      return -1;
    }
    Integer i = index.get(x);
    if (i == null) {
      throw new MissingVariable();
    }
    return i;
  }

  private int value(IntVar x, int[] values) {
    int i = at(x);
    return i < 0 ? x.value() : values[i];
  }

  // sorts the columns lexicographically; true if the order changed
  private boolean sort(IntVar[][] columns, int[] values) {
    int n = columns.length;
    int[][] v = new int[n][];
    for (int k = 0; k < n; k++) {
      v[k] = new int[columns[k].length];
      for (int r = 0; r < v[k].length; r++) {
        v[k][r] = value(columns[k][r], values);
      }
    }
    boolean sorted = true;
    for (int k = 1; k < n && sorted; k++) {
      sorted = Arrays.compare(v[k - 1], v[k]) <= 0;
    }
    if (sorted) {
      return false;
    }
    Arrays.sort(v, Arrays::compare);
    for (int k = 0; k < n; k++) {
      for (int r = 0; r < v[k].length; r++) {
        int i = at(columns[k][r]);
        if (i >= 0) {
          values[i] = v[k][r];
        }
      }
    }
    return true;
  }

  // renames the interchangeable values in the order of their first use; true if any changed
  private boolean rename(IntVar[] xs, int[] chain, int[] values) {
    Map<Integer, Integer> to = new java.util.HashMap<>();
    int next = 0;
    for (IntVar x : xs) {
      int v = value(x, values);
      if (Arrays.binarySearch(chain, v) >= 0 && !to.containsKey(v)) {
        to.put(v, chain[next++]);
      }
    }
    // the values not used take the rest, in order
    for (int v : chain) {
      if (!to.containsKey(v)) {
        to.put(v, chain[next++]);
      }
    }
    boolean changed = false;
    for (IntVar x : xs) {
      int i = at(x);
      if (i < 0) {
        continue;
      }
      Integer w = to.get(values[i]);
      if (w != null && w != values[i]) {
        values[i] = w;
        changed = true;
      }
    }
    return changed;
  }

  // replaces s by s o g when s breaks x <=lex g(x); true if it did
  private boolean descend(int k, int[] values) {
    IntVar[] x = lexX.get(k);
    IntVar[] y = lexY.get(k);
    int cmp = 0;
    for (int j = 0; j < x.length && cmp == 0; j++) {
      cmp = Integer.compare(value(x[j], values), value(y[j], values));
    }
    if (lexLargest.get(k) ? cmp >= 0 : cmp <= 0) {
      return false;
    }
    move(moveFrom.get(k), moveTo.get(k), values);
    return true;
  }

  // replaces s by s o g, g given by the variables it moves and their images
  private void move(IntVar[] from, IntVar[] to, int[] values) {
    int[] image = new int[from.length];
    for (int j = 0; j < from.length; j++) {
      image[j] = value(to[j], values);
    }
    for (int j = 0; j < from.length; j++) {
      int i = at(from[j]);
      if (i >= 0) {
        values[i] = image[j];
      } else if (image[j] != from[j].value()) {
        throw new MissingVariable();
      }
    }
  }
}
