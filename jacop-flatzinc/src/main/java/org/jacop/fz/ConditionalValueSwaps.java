/*
 * ConditionalValueSwaps.java
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XltY;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.fz.SymmetryBreaking.Atom;
import org.jacop.fz.SymmetryBreaking.Item;

/**
 * Breaks the conditional symmetry of interchangeable values in a sequence whose positions are
 * ordered by precedences, as in the patience game Black Hole (I. P. Gent, C. Jefferson, T. Kelsey,
 * I. Lynce, I. Miguel, P. Nightingale, B. M. Smith and S. A. Tarim, "Search in the patience game
 * 'Black Hole'", AI Communications 20(3), 2007): two cards of the same rank can swap places in a
 * solution whenever the order of their piles allows it.
 *
 * <p>The model has a channel {@code inverse(x, y)} ({@code jacop_assignment}): {@code x[i]} is the
 * value at position {@code i} and {@code y[v]} the position of value {@code v}. Every other
 * constraint on x is a table, whose relation is the same after the values a and b are exchanged in
 * all its columns, or an all different; every other constraint on y is a precedence {@code y[u] <
 * y[v]}. Constraints on y alone that are not precedences pin their values: those never move. Two
 * values a and b are interchangeable when the tables, the domains of the x variables and the
 * domains of {@code y[a]} and {@code y[b]} do not tell them apart. Exchanging a and b in a solution
 * (a conditional symmetry, I. P. Gent, T. Kelsey, S. A. Linton, I. McDonald, I. Miguel and B. M.
 * Smith, "Conditional symmetry breaking", CP 2005) then gives a solution exactly when the
 * precedences still hold: every predecessor of the value moved forward still comes before it, and
 * every successor of the value moved back still comes after it.
 *
 * <p>With a the value that the lex-leader order prefers at a position (the smaller one, or the
 * larger one for a search that tries the largest values first) the constraint
 *
 * <pre>
 *   y[b] &lt; y[a]  -&gt;  OR(u before a) y[u] &gt; y[b]  OR  OR(s after b) y[s] &lt; y[a]
 * </pre>
 *
 * <p>is posted: when b comes first and the exchange is possible, it gives a solution that is
 * lexicographically smaller over x (Crawford, Ginsberg, Luks and Roy, KR 1996). The constraints are
 * posted only when the variables of x come first, in their order, in the order of the lex-leader
 * constraints of {@link SymmetryBreaking}, so the solution that is smallest in that order satisfies
 * both. For a search annotation {@code int_search(x, input_order, indomain_min, complete)} this is
 * the first solution the search finds without them, so the search takes the same decisions, in the
 * order of the annotation, and only fails sooner.
 *
 * <p>Setting the system property {@code org.jacop.fz.symmetrySwaps} to false turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class ConditionalValueSwaps {

  /** Whether the swaps are broken (org.jacop.fz.symmetrySwaps, default true). */
  static final boolean ENABLED = !"false".equals(System.getProperty("org.jacop.fz.symmetrySwaps"));

  /** Sequences longer than this are not handled. */
  static final int MAX_LENGTH = 2_000;

  /** The most pairs of values that get a constraint. */
  static final int MAX_PAIRS = 20_000;

  /** The most tuples read over all tables. */
  static final long MAX_WORK = 50_000_000L;

  private final Store store;

  private final Tables dictionary;

  // y[u] < y[v], by u * n + v
  private final Map<Long, IntVar> before = new HashMap<>();

  private int posted;

  // the pairs of position variables (y[a], y[b]) whose exchange got a constraint
  private final List<IntVar[]> pairs = new ArrayList<>();

  ConditionalValueSwaps(Store store, Tables dictionary) {
    this.store = store;
    this.dictionary = dictionary;
  }

  /**
   * The pairs of position variables {@code (y[a], y[b])} that got a constraint, a the preferred
   * value.
   */
  List<IntVar[]> pairs() {
    return pairs;
  }

  /**
   * Finds the channels and posts the constraints.
   *
   * @param items the constraints of the model.
   * @param ranked the order of the lex-leader constraints.
   * @param descending true if the lex-leader order keeps the largest solution.
   * @return the constraints posted.
   */
  int run(List<Item> items, List<IntVar> ranked, boolean descending) {
    for (Item item : items) {
      if (!"jacop_assignment".equals(item.name()) || item.args().length != 4) {
        continue;
      }
      Atom[][] a = item.args();
      if (a[0].length != a[1].length
          || a[0].length < 3
          || a[0].length > MAX_LENGTH
          || a[2].length != 1
          || a[3].length != 1
          || !a[2][0].isInt()
          || !a[3][0].isInt()) {
        continue;
      }
      for (int side = 0; side < 2; side++) {
        Atom[] x = a[side];
        Atom[] y = a[1 - side];
        // the values of x are the indices of y
        int yOffset = a[3 - side][0].value();
        Sequence s = sequence(x, y, yOffset);
        if (s != null && s.read(items, item) && s.leadsOrder(ranked)) {
          s.post(descending);
          return posted;
        }
      }
    }
    return posted;
  }

  /** A channel inverse(x, y) read as a sequence of values x with the positions y. */
  private final class Sequence {
    final int n;
    final Atom[] x;
    final Atom[] y;
    final int yOffset;
    final Map<IntVar, Integer> xIndex = new IdentityHashMap<>();
    final Map<IntVar, Integer> yIndex = new IdentityHashMap<>();
    // by value index (y index): values that must come before, after
    final List<List<Integer>> pred = new ArrayList<>();
    final List<List<Integer>> succ = new ArrayList<>();
    final boolean[] pinned;
    // the tables over x: each a relation over its variable columns, as x indices
    final List<int[][]> relations = new ArrayList<>();
    final List<Set<List<Integer>>> relationSets = new ArrayList<>();
    long work;

    private Sequence(Atom[] x, Atom[] y, int yOffset) {
      this.n = x.length;
      this.x = x;
      this.y = y;
      this.yOffset = yOffset;
      this.pinned = new boolean[n];
      for (int i = 0; i < n; i++) {
        pred.add(new ArrayList<>());
        succ.add(new ArrayList<>());
      }
    }

    boolean read(List<Item> items, Item channel) {
      for (int i = 0; i < n; i++) {
        if (x[i].aVar() == null) {
          pin(x[i].value() - yOffset);
        }
        if (y[i].aVar() == null) {
          pin(i);
        }
      }
      for (Item item : items) {
        if (item == channel) {
          continue;
        }
        boolean onX = false;
        boolean onY = false;
        for (Atom[] arg : item.args()) {
          for (Atom a : arg) {
            if (a.aVar() != null) {
              onX |= xIndex.containsKey(a.aVar());
              onY |= yIndex.containsKey(a.aVar());
            }
          }
        }
        if (onX && onY) {
          return false;
        }
        if (onX && !readValues(item)) {
          return false;
        }
        if (onY) {
          readPositions(item);
        }
        if (work > MAX_WORK) {
          return false;
        }
      }
      return true;
    }

    private void pin(int value) {
      if (value >= 0 && value < n) {
        pinned[value] = true;
      }
    }

    /** A constraint on x: a table or an all different over variables of x only. */
    private boolean readValues(Item item) {
      Atom[][] a = item.args();
      String name = item.name();
      if (name.equals("jacop_alldiff") || name.equals("jacop_alldistinct")) {
        for (Atom v : a[0]) {
          if (v.aVar() == null) {
            if (!v.isInt()) {
              return false;
            }
            pin(v.value() - yOffset);
          } else if (!xIndex.containsKey(v.aVar())) {
            return false;
          }
        }
        return a.length == 1;
      }
      if (!name.equals("jacop_table_int") || a.length != 2) {
        return false;
      }
      Atom[] vars = a[0];
      Atom[] tuples = a[1];
      int k = vars.length;
      if (k == 0 || tuples.length % k != 0) {
        return false;
      }
      int columns = 0;
      for (Atom v : vars) {
        if (v.aVar() != null) {
          if (!xIndex.containsKey(v.aVar())) {
            return false;
          }
          columns++;
        } else if (!v.isInt()) {
          return false;
        }
      }
      List<int[]> rows = new ArrayList<>();
      Set<List<Integer>> set = new HashSet<>();
      work += tuples.length;
      for (int t = 0; t < tuples.length; t += k) {
        int[] row = new int[columns];
        boolean matches = true;
        for (int c = 0, r = 0; c < k; c++) {
          Atom e = tuples[t + c];
          if (!e.isInt()) {
            return false;
          }
          if (vars[c].aVar() == null) {
            matches &= e.value() == vars[c].value();
          } else {
            row[r++] = e.value();
          }
        }
        if (matches && set.add(asList(row))) {
          rows.add(row);
        }
      }
      relations.add(rows.toArray(new int[0][]));
      relationSets.add(set);
      return true;
    }

    /** A constraint on y: a precedence y[u] &lt; y[v], or anything else, which pins its values. */
    private void readPositions(Item item) {
      Atom[][] a = item.args();
      int u = -1;
      int v = -1;
      switch (item.name()) {
        case "int_lt", "int_le" -> {
          if (a.length == 2 && a[0].length == 1 && a[1].length == 1) {
            u = position(a[0][0]);
            v = position(a[1][0]);
          }
        }
        case "int_lin_le" -> {
          if (a.length == 3
              && a[0].length == 2
              && a[1].length == 2
              && a[2].length == 1
              && a[0][0].isInt()
              && a[0][1].isInt()
              && a[2][0].isInt()
              && (a[2][0].value() == 0 || a[2][0].value() == -1)) {
            if (a[0][0].value() == 1 && a[0][1].value() == -1) {
              u = position(a[1][0]);
              v = position(a[1][1]);
            } else if (a[0][0].value() == -1 && a[0][1].value() == 1) {
              u = position(a[1][1]);
              v = position(a[1][0]);
            }
          }
        }
        default -> {
          // not a precedence
        }
      }
      if (u >= 0 && v >= 0 && u != v) {
        // y[u] <= y[v] of two positions of an inverse is y[u] < y[v]
        succ.get(u).add(v);
        pred.get(v).add(u);
        return;
      }
      for (Atom[] arg : a) {
        for (Atom e : arg) {
          if (e.aVar() != null && yIndex.containsKey(e.aVar())) {
            pin(yIndex.get(e.aVar()));
          }
        }
      }
    }

    private int position(Atom a) {
      Integer i = a.aVar() == null ? null : yIndex.get(a.aVar());
      return i == null ? -1 : i;
    }

    /** Whether the variables of x come first in the lex-leader order, in their order. */
    boolean leadsOrder(List<IntVar> ranked) {
      int r = 0;
      for (Atom a : x) {
        if (a.aVar() != null) {
          if (r >= ranked.size() || ranked.get(r) != a.aVar()) {
            return false;
          }
          r++;
        }
      }
      return r > 0;
    }

    /** Whether exchanging the values a and b maps every table onto itself. */
    private boolean tablesKeep(int a, int b) {
      for (int t = 0; t < relations.size(); t++) {
        Set<List<Integer>> set = relationSets.get(t);
        for (int[] row : relations.get(t)) {
          boolean moved = false;
          int[] swapped = row.clone();
          for (int c = 0; c < row.length; c++) {
            if (row[c] == a) {
              swapped[c] = b;
              moved = true;
            } else if (row[c] == b) {
              swapped[c] = a;
              moved = true;
            }
          }
          work++;
          if (moved && !set.contains(asList(swapped))) {
            return false;
          }
        }
      }
      return true;
    }

    void post(boolean descending) {
      // values that the domains do not tell apart: the domain of their position, and the
      // variables of x whose domains hold them
      Map<String, List<Integer>> classes = new LinkedHashMap<>();
      for (int j = 0; j < n; j++) {
        if (pinned[j]) {
          continue;
        }
        int value = j + yOffset;
        StringBuilder key =
            new StringBuilder(dictionary.channelDomain(y[j].aVar()).toString()).append('|');
        for (Atom a : x) {
          key.append(
              a.aVar() != null && dictionary.channelDomain(a.aVar()).contains(value) ? '1' : '0');
        }
        classes.computeIfAbsent(key.toString(), k -> new ArrayList<>()).add(j);
      }
      for (List<Integer> c : classes.values()) {
        for (int i = 0; i < c.size(); i++) {
          for (int k = i + 1; k < c.size(); k++) {
            if (posted >= MAX_PAIRS || work > MAX_WORK) {
              return;
            }
            int a = c.get(i);
            int b = c.get(k);
            if (tablesKeep(a + yOffset, b + yOffset)) {
              exchange(descending ? b : a, descending ? a : b);
            }
          }
        }
      }
    }

    /** Posts that q comes after p unless exchanging them breaks a precedence. */
    private void exchange(int p, int q) {
      if (pred.get(p).contains(q) || succ.get(p).contains(q)) {
        return;
      }
      Set<IntVar> reasons = new LinkedHashSet<>();
      for (int u : pred.get(p)) {
        reasons.add(before(q, u));
      }
      for (int s : succ.get(q)) {
        reasons.add(before(s, p));
      }
      IntVar yp = y[p].aVar();
      IntVar yq = y[q].aVar();
      if (reasons.isEmpty()) {
        store.impose(new XltY(yp, yq));
      } else {
        store.impose(new BoolClause(new ArrayList<>(reasons), List.of(before(q, p))));
      }
      pairs.add(new IntVar[] {yp, yq});
      posted++;
    }

    /** The Boolean of y[u] &lt; y[v]. */
    private IntVar before(int u, int v) {
      return before.computeIfAbsent(
          (long) u * n + v,
          key -> {
            BooleanVar b = new BooleanVar(store);
            store.impose(new Reified(new XltY(y[u].aVar(), y[v].aVar()), b));
            return b;
          });
    }
  }

  private static List<Integer> asList(int[] row) {
    return Arrays.stream(row).boxed().toList();
  }

  /** The channel as a sequence, or null when its arguments are not distinct variables. */
  private Sequence sequence(Atom[] x, Atom[] y, int yOffset) {
    Sequence s = new Sequence(x, y, yOffset);
    for (int i = 0; i < x.length; i++) {
      if (!x[i].isInt() && x[i].aVar() == null || !y[i].isInt() && y[i].aVar() == null) {
        return null;
      }
      if (x[i].aVar() != null && s.xIndex.put(x[i].aVar(), i) != null) {
        return null;
      }
    }
    for (int i = 0; i < y.length; i++) {
      if (y[i].aVar() != null
          && (s.xIndex.containsKey(y[i].aVar()) || s.yIndex.put(y[i].aVar(), i) != null)) {
        return null;
      }
    }
    return s;
  }
}
