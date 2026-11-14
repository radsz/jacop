/*
 * AllDifferentLists.java
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

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * The lists (rows) are pairwise different tuples: for every two rows some position holds different
 * values. It is the allDifferent constraint over lists of XCSP3 (F. Boussemart, C. Lecoutre, G.
 * Audemard and C. Piette, "XCSP3-core: A format for representing constraint
 * satisfaction/optimization problems", arXiv:2009.00514, 2020, section 4.1.1), whose pairwise
 * decomposition posts a disjunction of disequalities for each pair of rows: m(m-1)/2 of them for m
 * rows, 499,500 on the 1,000 tickets of XCSP 2025 LotteryDesign-32-6-6-2-1000.
 *
 * <p>Propagation is that of the decomposition's disjunctions under unit propagation, for all pairs
 * at once: the fixed rows are hashed by their tuples, the rows with one variable left by their
 * other values. Two equal fixed rows fail, and a row with one variable left loses each value that
 * would make it equal to a fixed row. A call handles only the rows whose variables were fixed since
 * the last one, in O(n) each plus the domain of a row's last variable; the tables are undone on
 * backtracking.
 *
 * <p>Explanations: a removed value is explained by the other values of its row and the values of
 * the fixed row it would equal; a failure by the values of the two equal rows.
 *
 * <p>With excepted tuples (XCSP3 allDifferent over lists with except), two rows may be equal when
 * their tuple is excepted: a fixed row whose tuple is excepted is not hashed, so it neither fails
 * nor prunes.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class AllDifferentLists extends Constraint
    implements UsesQueueVariable,
        Stateful,
        SatisfiedPresent,
        Copyable<AllDifferentLists>,
        Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The rows, all of the same length. */
  public final IntVar[][] x;

  private final int m;
  private final int n;

  /** The excepted tuples: two rows may be equal when their tuple is one of them. */
  public final int[][] except;

  private final Set<Key> excepted = new HashSet<>();

  // the positions (row * n + column) of each variable
  private final Map<IntVar, int[]> positions = new IdentityHashMap<>();

  /**
   * It creates the constraint.
   *
   * @param x the rows, all of the same length; no two may be equal tuples
   */
  public AllDifferentLists(IntVar[][] x) {
    this(x, new int[0][]);
  }

  /**
   * It creates the constraint with excepted tuples (XCSP3 allDifferent over lists with except).
   *
   * @param x the rows, all of the same length; no two may be equal tuples unless the tuple is
   *     excepted
   * @param except the excepted tuples, each of the length of the rows
   */
  public AllDifferentLists(IntVar[][] x, int[][] except) {
    checkInputForNullness("x", x);
    checkInputForNullness("except", except);
    for (int i = 0; i < x.length; i++) {
      checkInputForNullness("x[" + i + "]", x[i]);
    }
    this.m = x.length;
    this.n = m == 0 ? 0 : x[0].length;
    for (int i = 1; i < m; i++) {
      if (x[i].length != n) {
        throw new IllegalArgumentException(
            "AllDifferentLists rows must have the same length; x[0] has "
                + n
                + " elements and x["
                + i
                + "] has "
                + x[i].length);
      }
    }
    this.except = new int[except.length][];
    for (int e = 0; e < except.length; e++) {
      if (except[e] == null || except[e].length != n) {
        throw new IllegalArgumentException(
            "AllDifferentLists excepted tuple " + e + " must have the rows' length " + n);
      }
      this.except[e] = except[e].clone();
      excepted.add(new Key(this.except[e]));
    }
    this.numberId = idNumber.incrementAndGet();
    this.queueIndex = 1;
    this.x = new IntVar[m][];
    for (int i = 0; i < m; i++) {
      this.x[i] = Arrays.copyOf(x[i], n);
      for (int j = 0; j < n; j++) {
        int[] old = positions.get(x[i][j]);
        int[] now = old == null ? new int[1] : Arrays.copyOf(old, old.length + 1);
        now[now.length - 1] = i * n + j;
        positions.put(x[i][j], now);
      }
    }
    setScope(Arrays.stream(this.x).flatMap(Arrays::stream).toArray(IntVar[]::new));
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  // a row's values with one position replaced, as a hash key
  private static final class Key {
    final int[] values;
    final int hash;

    Key(int[] values) {
      this.values = values;
      this.hash = Arrays.hashCode(values);
    }

    @Override
    public boolean equals(Object o) {
      return o instanceof Key k && hash == k.hash && Arrays.equals(values, k.values);
    }

    @Override
    public int hashCode() {
      return hash;
    }
  }

  // the fixed rows by their tuples; the rows with one variable left by their other values and the
  // column of that variable (the key's last entry). Entries are undone when their level is removed.
  private final Map<Key, Integer> fixedRows = new HashMap<>();
  private final Map<Key, List<Integer>> openRows = new HashMap<>();
  private final List<Object> undoKeys = new ArrayList<>();
  private final List<Integer> undoLevels = new ArrayList<>();
  private final List<Integer> undoRows = new ArrayList<>();
  private boolean[] inFixed;
  private boolean[] inOpen;

  // the undo entry of a fixed row with an excepted tuple, which is not hashed
  private static final Object EXCEPTED = new Object();

  // the rows whose variables were fixed since the last call
  private int[] dirty;
  private int dirtyCount;
  private boolean[] isDirty;
  private boolean started;

  @Override
  public void impose(Store store) {
    inFixed = new boolean[m];
    inOpen = new boolean[m];
    dirty = new int[m];
    isDirty = new boolean[m];
    super.impose(store);
  }

  @Override
  public void queueVariable(int level, Var variable) {
    int[] cells = positions.get(variable);
    if (cells != null) {
      for (int cell : cells) {
        markDirty(cell / n);
      }
    }
  }

  private void markDirty(int i) {
    if (!isDirty[i]) {
      isDirty[i] = true;
      dirty[dirtyCount++] = i;
    }
  }

  @Override
  public void removeLevel(int level) {
    int k = undoLevels.size();
    while (k > 0 && undoLevels.get(k - 1) >= level) {
      k--;
      int i = undoRows.get(k);
      Object key = undoKeys.get(k);
      if (key == EXCEPTED) {
        inFixed[i] = false;
      } else if (key instanceof Key fixedKey) {
        fixedRows.remove(fixedKey);
        inFixed[i] = false;
      } else {
        Key openKey = (Key) ((Object[]) key)[0];
        List<Integer> rows = openRows.get(openKey);
        rows.remove(rows.size() - 1);
        if (rows.isEmpty()) {
          openRows.remove(openKey);
        }
        inOpen[i] = false;
      }
      undoKeys.remove(k);
      undoLevels.remove(k);
      undoRows.remove(k);
    }
    clearDirty();
  }

  private void clearDirty() {
    for (int q = 0; q < dirtyCount; q++) {
      isDirty[dirty[q]] = false;
    }
    dirtyCount = 0;
  }

  @Override
  public void consistency(Store store) {
    if (m < 2) {
      return;
    }
    if (n == 0) {
      throw Store.failException;
    }
    failRow = -1;
    failOther = -1;
    if (!started) {
      started = true;
      for (int i = 0; i < m; i++) {
        markDirty(i);
      }
    }
    while (dirtyCount > 0) {
      int i = dirty[--dirtyCount];
      isDirty[i] = false;
      if (inFixed[i]) {
        continue;
      }
      int free = -1;
      int unfixed = 0;
      for (int j = 0; j < n && unfixed < 2; j++) {
        if (!x[i][j].singleton()) {
          free = j;
          unfixed++;
        }
      }
      if (unfixed == 0) {
        fix(store, i);
      } else if (unfixed == 1 && !inOpen[i]) {
        open(store, i, free);
      }
    }
  }

  // row i is fixed: it differs from the fixed rows and makes the open rows it matches lose a value
  private void fix(Store store, int i) {
    Key key = new Key(values(i, -1, 0));
    if (excepted.contains(key)) {
      // an excepted tuple may repeat: the row is done
      inFixed[i] = true;
      undoKeys.add(EXCEPTED);
      undoLevels.add(store.level);
      undoRows.add(i);
      return;
    }
    Integer same = fixedRows.putIfAbsent(key, i);
    if (same != null) {
      failRow = i;
      failOther = same;
      throw Store.failException;
    }
    inFixed[i] = true;
    undoKeys.add(key);
    undoLevels.add(store.level);
    undoRows.add(i);
    for (int c = 0; c < n; c++) {
      List<Integer> rows = openRows.get(openKey(i, c));
      if (rows == null) {
        continue;
      }
      int a = x[i][c].value();
      for (int r : rows) {
        IntVar v = x[r][c];
        if (r != i && !v.singleton() && v.domain.contains(a)) {
          remove(store, v, a, r, i);
          if (v.singleton()) {
            markDirty(r);
          }
        }
      }
    }
  }

  // row i has one variable left, in column c: it loses the values that make it equal a fixed row
  private void open(Store store, int i, int c) {
    Key key = openKey(i, c);
    openRows.computeIfAbsent(key, k -> new ArrayList<>(1)).add(i);
    inOpen[i] = true;
    undoKeys.add(new Object[] {key});
    undoLevels.add(store.level);
    undoRows.add(i);
    IntVar v = x[i][c];
    int[] candidates = new int[v.getSize()];
    int k = 0;
    for (ValueEnumeration e = v.dom().valueEnumeration(); e.hasMoreElements(); ) {
      candidates[k++] = e.nextElement();
    }
    int[] t = values(i, c, 0);
    for (int a : candidates) {
      t[c] = a;
      Integer other = fixedRows.get(new Key(t.clone()));
      if (other != null) {
        remove(store, v, a, i, other);
      }
    }
    if (v.singleton()) {
      markDirty(i);
    }
  }

  // the values of row i except column c (fixed), with c as the last entry
  private Key openKey(int i, int c) {
    int[] t = new int[n + 1];
    for (int j = 0; j < n; j++) {
      t[j] = j == c || !x[i][j].singleton() ? 0 : x[i][j].value();
    }
    t[n] = c;
    return new Key(t);
  }

  // the values of row i (all fixed but maybe column skip, which gets value)
  private int[] values(int i, int skip, int value) {
    int[] t = new int[n];
    for (int j = 0; j < n; j++) {
      t[j] = j == skip ? value : x[i][j].value();
    }
    return t;
  }

  @Override
  public boolean satisfied() {
    Map<Key, Integer> seen = new HashMap<>();
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < n; j++) {
        if (!x[i][j].singleton()) {
          return false;
        }
      }
      Key key = new Key(values(i, -1, 0));
      if (!excepted.contains(key) && seen.put(key, i) != null) {
        return false;
      }
    }
    return true;
  }

  // the fixed row that removed each value: (variable, value) -> row, written at every removal, so
  // the latest record of an atom x != v on the trail is the removal that made it
  private final Map<IntVar, Map<Integer, Integer>> removedBy = new IdentityHashMap<>();

  // the two rows of the last failure: equal fixed rows, or a row whose last value a fixed row took
  private int failRow = -1;
  private int failOther = -1;

  private void remove(Store store, IntVar v, int a, int row, int other) {
    removedBy.computeIfAbsent(v, k -> new HashMap<>()).put(a, other);
    failRow = row;
    failOther = other;
    v.domain.inComplement(store.level, v, a);
    failRow = -1;
  }

  // the atoms of the variables of row i (but column skip) before a trail position
  private void addRow(AtomicTrail trail, int i, int skip, int position, EntryList out) {
    for (int j = 0; j < n; j++) {
      if (j != skip) {
        trail.atomsBefore(x[i][j], position, out);
      }
    }
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar v = trail.variable(entry);
    int[] cells = positions.get(v);
    Map<Integer, Integer> by = removedBy.get(v);
    if (cells == null || by == null) {
      return false;
    }
    // the value removed: that of x != a; for a bound atom, the bound before the entry (this
    // constraint removes one value at a time, so the values between it and the new bound are holes
    // already)
    int kind = trail.kind(entry);
    int a =
        switch (kind) {
          case AtomicTrail.GE -> trail.minBefore(v, entry);
          case AtomicTrail.LE -> trail.maxBefore(v, entry);
          default -> trail.value(entry);
        };
    Integer k = by.get(a);
    if (k == null) {
      return false;
    }
    for (int cell : cells) {
      int i = cell / n;
      int c = cell % n;
      if (i != k && matches(trail, entry, i, c, k, a)) {
        if (kind != AtomicTrail.NE) {
          trail.atomsBefore(v, entry, out);
        }
        addRow(trail, i, c, entry, out);
        addRow(trail, k, -1, entry, out);
        return true;
      }
    }
    return false;
  }

  // whether row k was fixed before a trail position and row i, with value a in column c and its
  // other variables fixed then, equals it. Fixed then means bounds equal then: a variable fixed by
  // holes only is not recognised, and the generic reason is used.
  private boolean matches(AtomicTrail trail, int position, int i, int c, int k, int a) {
    for (int j = 0; j < n; j++) {
      int u = fixedBefore(trail, x[k][j], position);
      if (u == Integer.MIN_VALUE) {
        return false;
      }
      int w = j == c ? a : fixedBefore(trail, x[i][j], position);
      if (w != u) {
        return false;
      }
    }
    return true;
  }

  // the value of x before a trail position, Integer.MIN_VALUE when its bounds differ then
  private static int fixedBefore(AtomicTrail trail, IntVar x, int position) {
    int lo = trail.minBefore(x, position);
    return lo == trail.maxBefore(x, position) ? lo : Integer.MIN_VALUE;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (failRow < 0 || failOther < 0) {
      return false;
    }
    int now = trail.size();
    addRow(trail, failRow, -1, now, out);
    addRow(trail, failOther, -1, now, out);
    return true;
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : AllDifferentLists([");
    for (int i = 0; i < m; i++) {
      result.append(Arrays.toString(x[i]));
      if (i < m - 1) {
        result.append(", ");
      }
    }
    result.append("]");
    if (except.length > 0) {
      result.append(", except ").append(Arrays.deepToString(except));
    }
    result.append(")");
    return result.toString();
  }

  @Override
  public AllDifferentLists copy(VarMap map) {
    IntVar[][] y = new IntVar[m][];
    for (int i = 0; i < m; i++) {
      y[i] = map.get(x[i]);
    }
    return new AllDifferentLists(y, except);
  }
}
