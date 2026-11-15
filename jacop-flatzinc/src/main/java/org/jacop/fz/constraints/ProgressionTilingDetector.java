/*
 * ProgressionTilingDetector.java
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
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import org.jacop.constraints.Alldistinct;
import org.jacop.core.IntVar;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.SimpleNode;

/**
 * Finds tilings of an interval 0..n-1 by m arithmetic progressions of k terms each, s_i, s_i + g_i,
 * ..., s_i + (k - 1) g_i, whose starts are ordered (a strictly increasing chain s_1 &lt; ... &lt;
 * s_m) and whose gaps are all different, m k = n: Tom Johnson's perfect rhythmic tilings (XCSP3
 * PerfectRythmicTiling). Whether they exist for every m is open even for k = 3; Alon, Dębski,
 * Grytczuk and Przybyło ("Packing arithmetic progressions with pairwise distinct differences",
 * arXiv 2603.02786, 2026) cite them as the motivation of their packing bounds.
 *
 * <p>The detector does not post constraints. It finds the progressions and gives the search a
 * branching on them: the starts in the order of the chain, each at its smallest value, and after
 * each start its gap at a random value, under Luby restarts. With the starts ordered and all values
 * of the interval covered, the smallest value no progression yet covers must be the next start, so
 * the smallest value of the next start is that value once the earlier progressions are fixed, and
 * the branching is the classical search of an exact cover by its first uncovered cell (Knuth's
 * algorithm X with the leftmost column). Its search space is heavy tailed: random gaps and restarts
 * find tilings that no fixed order finds in hours (n = 80: 2.7 to 18 million nodes with 3 seeds,
 * all within 250 s).
 *
 * <p>A progression is read from the flattened model in three forms: linear equalities t = s + j g
 * (int_lin_eq over [t, s, g] with the coefficients 1, -1, -j), chains of them t' = t + g, and the
 * columns of a table (jacop_table_int, jacop_short_table_int) whose tuples all satisfy t = s + j g
 * for one j. The offsets j of a start must be 1..k-1 and the same k for all, the starts and terms
 * within 0..n-1, n = m k. The system property {@code org.jacop.fz.progressionTiling=false} turns it
 * off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ProgressionTilingDetector {

  /** At least this many progressions. */
  static final int MIN_PROGRESSIONS = 3;

  /** Tables with more cells (tuples times columns) than this are not read. */
  static final long MAX_TABLE_CELLS = 1L << 26;

  private final Support support;

  private final List<IntVar[]> chains = new ArrayList<>();

  private final List<IntVar[]> alldiffs = new ArrayList<>();

  /** t = u + c g. */
  private record Step(IntVar t, IntVar u, IntVar g, long c) {}

  private final Map<IntVar, List<Step>> steps = new IdentityHashMap<>();

  /** Tables: the variables and the tuples, row-major, star for any value. */
  private record Table(IntVar[] vars, int[] tuples, Integer star) {}

  private final List<Table> tables = new ArrayList<>();

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public ProgressionTilingDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.progressionTiling is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.progressionTiling"));
  }

  /**
   * A tiling found: the starts in their order and the gap of each.
   *
   * @param starts the starts, ascending in every solution.
   * @param gaps the gap of each start.
   * @param terms the number of terms k of each progression.
   * @param positions the start and the terms of each progression, in the order of their offsets.
   */
  public record Tiling(IntVar[] starts, IntVar[] gaps, int terms, IntVar[][] positions) {}

  /** The starts and terms of all progressions of the last tiling found. */
  private List<IntVar> positions = List.of();

  /**
   * It reads the model and returns the first tiling it finds.
   *
   * @param astTree the root of the parsed model.
   * @return the tiling, or null if there is none.
   */
  public Tiling detect(SimpleNode astTree) {
    support.forEachConstraint(astTree, this::collect);
    Tiling found = null;
    for (IntVar[] chain : chains) {
      found = tiling(chain);
      if (found != null) {
        break;
      }
    }
    if (support.options.debug()) {
      FzConsole.println(
          "% progression tiling: "
              + (found == null
                  ? "none"
                  : found.starts().length + " progressions of " + found.terms() + " terms"));
    }
    return found;
  }

  private void collect(ASTConstElem node) {
    switch (node.getName()) {
      case "jacop_strictly_increasing" ->
          chains.add(support.getVarArray((SimpleNode) node.jjtGetChild(0)));
      case "jacop_alldiff", "jacop_alldistinct", "all_different_int" ->
          alldiffs.add(support.getVarArray((SimpleNode) node.jjtGetChild(0)));
      case "int_lin_eq" -> linear(node);
      case "jacop_array_var_int_element_nonshifted", "array_var_int_element" -> element(node);
      case "jacop_table_int" -> table(node, null);
      case "jacop_short_table_int" ->
          table(node, support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)));
      default -> {
        // not part of a tiling
      }
    }
  }

  /** [1, -1, -c] * [t, u, g] = 0 in any order of u and g, or negated: t = u + c g. */
  private void linear(ASTConstElem node) {
    int[] c = support.getIntArray((SimpleNode) node.jjtGetChild(0));
    if (c == null
        || c.length != 3
        || support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2)) != 0) {
      return;
    }
    IntVar[] v = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    // a start or a term the root fixed is still one (the first start is often 0)
    if (v[0] == v[1] || v[0] == v[2] || v[1] == v[2]) {
      return;
    }
    int sign = c[0] < 0 ? -1 : 1;
    if (c[0] * sign != 1) {
      return;
    }
    // c[0] t + c[1] a + c[2] b = 0: t = -(c[1] / c[0]) a - (c[2] / c[0]) b
    long a = -(long) c[1] * sign;
    long b = -(long) c[2] * sign;
    if (a == 1 && b >= 1) {
      add(new Step(v[0], v[1], v[2], b));
    }
    if (b == 1 && a >= 1) {
      add(new Step(v[0], v[2], v[1], a));
    }
  }

  /** cover[t] = c with a constant c: the index t is one of the cells progression c covers. */
  private record Cover(IntVar[] cover, int value) {}

  private final Map<IntVar, List<Cover>> covers = new IdentityHashMap<>();

  private void element(ASTConstElem node) {
    IntVar index = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    IntVar[] cover = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    IntVar value = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    if (index != null && cover != null && value != null && value.singleton()) {
      covers.computeIfAbsent(index, k -> new ArrayList<>()).add(new Cover(cover, value.value()));
    }
  }

  private void add(Step s) {
    steps.computeIfAbsent(s.u(), k -> new ArrayList<>()).add(s);
  }

  private void table(ASTConstElem node, Integer star) {
    IntVar[] vars = support.getVarArray((SimpleNode) node.jjtGetChild(0));
    int[] tuples = support.getIntArray((SimpleNode) node.jjtGetChild(1));
    if (vars == null
        || tuples == null
        || vars.length < 3
        || tuples.length == 0
        || tuples.length % vars.length != 0
        || tuples.length > MAX_TABLE_CELLS) {
      return;
    }
    tables.add(new Table(vars, tuples, star));
  }

  private Tiling tiling(IntVar[] starts) {
    int m = starts.length;
    if (m < MIN_PROGRESSIONS) {
      return null;
    }
    Set<IntVar> gapVars = null;
    for (IntVar[] a : alldiffs) {
      if (a.length == m) {
        gapVars = Collections.newSetFromMap(new IdentityHashMap<>());
        gapVars.addAll(Arrays.asList(a));
        // the starts' gaps must all come from one all different
        IntVar[] gaps = new IntVar[m];
        int k = progressions(starts, gapVars, gaps);
        if (k > 0 && distinct(gaps, k)) {
          IntVar[][] byProgression = new IntVar[m][];
          for (int i = 0; i < m; i++) {
            byProgression[i] = positions.subList(i * k, (i + 1) * k).toArray(new IntVar[0]);
          }
          return new Tiling(starts.clone(), gaps, k, byProgression);
        }
      }
    }
    return null;
  }

  /** The number of terms k of the progressions of all starts with gaps from the given set, or 0. */
  private int progressions(IntVar[] starts, Set<IntVar> gapVars, IntVar[] gaps) {
    int k = 0;
    long maxPosition = 0;
    Set<IntVar> used = Collections.newSetFromMap(new IdentityHashMap<>());
    List<IntVar> positions = new ArrayList<>();
    for (int i = 0; i < starts.length; i++) {
      IntVar s = starts[i];
      Progression p = progression(s, gapVars);
      if (p == null || (k != 0 && p.terms.size() + 1 != k) || !used.add(p.gap)) {
        return 0;
      }
      k = p.terms.size() + 1;
      gaps[i] = p.gap;
      positions.add(s);
      positions.addAll(p.terms);
    }
    for (IntVar x : positions) {
      if (x.min() < 0) {
        return 0;
      }
      maxPosition = Math.max(maxPosition, x.max());
    }
    if (k < 2 || maxPosition + 1 != (long) k * starts.length) {
      return 0;
    }
    this.positions = positions;
    return k;
  }

  /**
   * Whether the positions are pairwise different in every solution: an all different holds them
   * all, or each position indexes the same cover array at the constant of its progression,
   * different constants for different progressions, and the gaps are at least 1. In the second case
   * it posts the all different, redundant: the next start is then at once the first value no fixed
   * progression covers (XCSP3 PerfectRythmicTiling1, 4-15: 391,800 nodes instead of no tiling in
   * 600 s).
   */
  private boolean distinct(IntVar[] gaps, int k) {
    Set<IntVar> all = Collections.newSetFromMap(new IdentityHashMap<>());
    all.addAll(positions);
    for (IntVar[] a : alldiffs) {
      if (a.length >= all.size() && Arrays.asList(a).containsAll(all)) {
        return true;
      }
    }
    for (IntVar g : gaps) {
      if (g.min() < 1) {
        return false;
      }
    }
    IntVar[] cover = null;
    Set<Integer> values = new HashSet<>();
    for (int i = 0; i < positions.size(); i += k) {
      Integer progression = null;
      for (int j = i; j < i + k; j++) {
        Integer v = null;
        for (Cover c : covers.getOrDefault(positions.get(j), List.of())) {
          if (cover == null) {
            cover = c.cover();
          }
          if (Arrays.equals(cover, c.cover())) {
            v = c.value();
            break;
          }
        }
        if (v == null || (progression != null && !progression.equals(v))) {
          return false;
        }
        progression = v;
      }
      if (!values.add(progression)) {
        return false;
      }
    }
    support.pose(new Alldistinct(positions.toArray(new IntVar[0])));
    return true;
  }

  /** A start's gap and terms s + j g, j = 1..k-1, in the order of j. */
  private record Progression(IntVar gap, List<IntVar> terms) {}

  private Progression progression(IntVar s, Set<IntVar> gapVars) {
    for (IntVar g : gapVars) {
      Map<Long, IntVar> byOffset = new TreeMap<>();
      if (!offsets(s, g, byOffset)) {
        continue;
      }
      if (byOffset.isEmpty()) {
        continue;
      }
      List<IntVar> terms = new ArrayList<>();
      long j = 1;
      for (Map.Entry<Long, IntVar> e : byOffset.entrySet()) {
        if (e.getKey() != j) {
          terms = null;
          break;
        }
        terms.add(e.getValue());
        j++;
      }
      if (terms != null) {
        return new Progression(g, terms);
      }
    }
    return null;
  }

  /**
   * The terms t = s + j g reached from s through the linear steps and the table columns, by their
   * offset j. False when one offset has two different terms or a term two offsets.
   */
  private boolean offsets(IntVar s, IntVar g, Map<Long, IntVar> byOffset) {
    Map<IntVar, Long> seen = new IdentityHashMap<>();
    seen.put(s, 0L);
    List<IntVar> queue = new ArrayList<>();
    queue.add(s);
    for (int q = 0; q < queue.size(); q++) {
      IntVar u = queue.get(q);
      long base = seen.get(u);
      for (Step st : steps.getOrDefault(u, List.of())) {
        if (st.g() != g) {
          continue;
        }
        long off = base + st.c();
        Long old = seen.get(st.t());
        if (old != null) {
          if (old != off) {
            return false;
          }
          continue;
        }
        seen.put(st.t(), off);
        queue.add(st.t());
      }
    }
    for (Table t : tables) {
      columns(t, s, g, seen);
    }
    for (Map.Entry<IntVar, Long> e : seen.entrySet()) {
      if (e.getKey() == s) {
        continue;
      }
      if (byOffset.put(e.getValue(), e.getKey()) != null) {
        return false;
      }
    }
    return true;
  }

  /** The columns c of a table over s and g with c = s + j g in every tuple, for one j &gt;= 1. */
  private void columns(Table t, IntVar s, IntVar g, Map<IntVar, Long> seen) {
    int sc = -1;
    int gc = -1;
    IntVar[] vars = t.vars();
    for (int c = 0; c < vars.length; c++) {
      if (vars[c] == s) {
        sc = c;
      } else if (vars[c] == g) {
        gc = c;
      }
    }
    if (sc < 0 || gc < 0) {
      return;
    }
    int w = vars.length;
    int[] tp = t.tuples();
    Integer star = t.star();
    for (int c = 0; c < w; c++) {
      if (c == sc || c == gc || seen.containsKey(vars[c])) {
        continue;
      }
      long j = Long.MIN_VALUE;
      boolean ok = true;
      for (int r = 0; r < tp.length && ok; r += w) {
        int sv = tp[r + sc];
        int gv = tp[r + gc];
        int cv = tp[r + c];
        if (star != null && (sv == star || gv == star || cv == star) || gv <= 0) {
          ok = false;
          break;
        }
        long d = (long) cv - sv;
        if (d % gv != 0) {
          ok = false;
          break;
        }
        long jj = d / gv;
        if (j == Long.MIN_VALUE) {
          j = jj;
        } else if (j != jj) {
          ok = false;
        }
      }
      if (ok && j >= 1) {
        seen.put(vars[c], j);
      }
    }
  }
}
