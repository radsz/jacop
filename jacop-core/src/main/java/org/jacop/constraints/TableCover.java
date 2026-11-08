/*
 * TableCover.java
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

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * A tiling as an exact cover over tables: groups of variables {@code x[i]}, each group with a table
 * of tuples, where the values of all variables are pairwise different. Every tuple of group {@code
 * i} is an option that covers the element "group i" and the elements "value v" for every value v in
 * it. Every group is covered once (its table); every value at most once (the all different), or
 * exactly once when {@code exact} is set, as in a tiling where the variables of all groups take all
 * the cells. Pentominoes in XCSP3 are modelled so: the five cells of a piece are a group, the table
 * lists its placements, and an all different over the cells of all pieces.
 *
 * <p>The table and the all different of the model already give the rules that follow from one
 * element at a time. This constraint adds the DL+ rule of Chabert and Solnon (see {@link
 * ExactCover}): when every tuple left for an element {@code a} that must be covered also covers an
 * element {@code b}, the tuples that cover {@code b} but not {@code a} are removed. Removed tuples
 * then remove the values that only they support. For example, when only placements of piece i can
 * still cover cell v, the placements of piece i that miss v are removed, and when every placement
 * left of piece i covers cell v, the placements of other pieces on v are removed.
 *
 * <p>A tuple is alive while all its values are in the domains of its variables. The numbers of
 * alive tuples of every element and of the tuples supporting every value are kept incrementally and
 * restored on backtracking from a stack of the changes, as dancing links hide and unhide rows. The
 * rule is checked for the elements whose number of alive tuples changed, and it reads only the
 * alive tuples, so a tuple it removes (kills) needs no other kill to be explained: a value removed
 * is explained, for every tuple with it, by a value of the tuple out of its domain, or, for a
 * killed tuple, by the values out of the domains of the tuples of its element {@code a} that share
 * no element with it.
 *
 * <p>References: Maxime Chabert and Christine Solnon. A Global Constraint for the Exact Cover
 * Problem: Application to Conceptual Clustering. Journal of Artificial Intelligence Research 67,
 * pages 509-547, 2020. Donald E. Knuth. The Art of Computer Programming, Volume 4B, Section 7.2.2.1
 * (primary and secondary items), Addison-Wesley, 2022.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class TableCover extends Constraint
    implements SatisfiedPresent, Stateful, UsesQueueVariable, Explainable, Copyable<TableCover> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  private final IntVar[][] groups;
  private final int[][][] given;
  private final boolean exact;

  private final IntVar[] vars;
  private final int[] groupOf;
  private final int[] columnOf;

  /** The first variable of every group in {@link #vars}. */
  private final int[] firstVar;

  /** The tuples, all groups in one list. */
  private final int[][] tuple;

  private final int[] tupleGroup;

  /** The tuples of every group. */
  private final int[][] groupTuples;

  /** The elements of every tuple, sorted: its group, then numberOfGroups + value - minValue. */
  private final int[][] elems;

  /** The tuples covering every element. */
  private final int[][] cover;

  private final boolean[] primary;
  private final int minValue;
  private final int range;

  private final boolean[] dead;
  private final boolean[] killed;
  private final int[] witness;

  /** Alive tuples of every element. */
  private final int[] aliveCount;

  /** Tuples alive and not killed with every value of every variable: var * range + value. */
  private final int[] support;

  /** Changes made, as tuple * 2 + (1 for a kill), with their levels, undone on backtracking. */
  private int[] done = new int[64];

  private int[] doneLevel = new int[64];
  private int doneSize;

  private final int[] changedVars;
  private final boolean[] isChanged;
  private int changedSize;

  private final int[] dirty;
  private final boolean[] isDirty;
  private int dirtySize;

  private final int[] mark;
  private final int[] hits;
  private final int[] seen;
  private final int[] touched;
  private int stamp;

  private boolean firstCall = true;

  private final Map<IntVar, Integer> position = new IdentityHashMap<>();

  private int failElement = -1;
  private int failVar = -1;

  /** Statistics: tuples killed by the rule. */
  public long kills;

  /** Statistics: values removed. */
  public long pruned;

  /**
   * It constructs the constraint.
   *
   * @param groups the variables of every group, all different over all groups
   * @param tuples the tuples of every group
   * @param exact true if every value of the variables is taken
   */
  public TableCover(IntVar[][] groups, int[][][] tuples, boolean exact) {
    checkInputForNullness("groups", groups);
    checkInputForNullness("tuples", tuples);
    if (groups.length != tuples.length) {
      throw new IllegalArgumentException("TableCover: groups and tuples differ in length.");
    }
    numberId = idNumber.incrementAndGet();
    queueIndex = 2;
    int k = groups.length;
    this.groups = new IntVar[k][];
    this.given = new int[k][][];
    this.exact = exact;
    List<IntVar> list = new ArrayList<>();
    List<Integer> g = new ArrayList<>();
    List<Integer> c = new ArrayList<>();
    firstVar = new int[k];
    int lo = Integer.MAX_VALUE;
    int hi = Integer.MIN_VALUE;
    for (int i = 0; i < k; i++) {
      this.groups[i] = groups[i].clone();
      this.given[i] = new int[tuples[i].length][];
      for (int r = 0; r < tuples[i].length; r++) {
        this.given[i][r] = tuples[i][r].clone();
      }
      firstVar[i] = list.size();
      for (int j = 0; j < groups[i].length; j++) {
        IntVar v = groups[i][j];
        if (position.put(v, list.size()) != null) {
          throw new IllegalArgumentException("TableCover: variable " + v + " is listed twice.");
        }
        list.add(v);
        g.add(i);
        c.add(j);
        lo = Math.min(lo, v.min());
        hi = Math.max(hi, v.max());
      }
    }
    vars = list.toArray(new IntVar[0]);
    groupOf = g.stream().mapToInt(Integer::intValue).toArray();
    columnOf = c.stream().mapToInt(Integer::intValue).toArray();
    minValue = lo;
    range = hi - lo + 1;
    int n = k + range;
    List<int[]> ts = new ArrayList<>();
    List<Integer> tg = new ArrayList<>();
    List<List<Integer>> byGroup = new ArrayList<>();
    for (int i = 0; i < k; i++) {
      byGroup.add(new ArrayList<>());
      for (int[] t : tuples[i]) {
        if (t.length != groups[i].length) {
          throw new IllegalArgumentException(
              "TableCover: a tuple of group " + i + " has a wrong size.");
        }
        // a tuple with a value twice violates the all different; one out of range is never alive
        int[] s = t.clone();
        Arrays.sort(s);
        boolean ok = true;
        for (int j = 0; j < s.length && ok; j++) {
          ok = s[j] >= lo && s[j] <= hi && (j == 0 || s[j] != s[j - 1]);
        }
        if (ok) {
          byGroup.get(i).add(ts.size());
          ts.add(t.clone());
          tg.add(i);
        }
      }
    }
    tuple = ts.toArray(new int[0][]);
    tupleGroup = tg.stream().mapToInt(Integer::intValue).toArray();
    groupTuples = new int[k][];
    for (int i = 0; i < k; i++) {
      groupTuples[i] = byGroup.get(i).stream().mapToInt(Integer::intValue).toArray();
    }
    elems = new int[tuple.length][];
    int[] size = new int[n];
    for (int r = 0; r < tuple.length; r++) {
      int[] e = new int[tuple[r].length + 1];
      e[0] = tupleGroup[r];
      for (int j = 0; j < tuple[r].length; j++) {
        e[j + 1] = k + tuple[r][j] - lo;
      }
      Arrays.sort(e);
      elems[r] = e;
      for (int x : e) {
        size[x]++;
      }
    }
    cover = new int[n][];
    for (int e = 0; e < n; e++) {
      cover[e] = new int[size[e]];
    }
    int[] fill = new int[n];
    for (int r = 0; r < tuple.length; r++) {
      for (int x : elems[r]) {
        cover[x][fill[x]++] = r;
      }
    }
    primary = new boolean[n];
    for (int e = 0; e < n; e++) {
      primary[e] = e < k || exact && cover[e].length > 0;
    }
    dead = new boolean[tuple.length];
    killed = new boolean[tuple.length];
    witness = new int[tuple.length];
    aliveCount = size.clone();
    support = new int[vars.length * range];
    for (int r = 0; r < tuple.length; r++) {
      int base = firstVar[tupleGroup[r]];
      for (int j = 0; j < tuple[r].length; j++) {
        support[(base + j) * range + tuple[r][j] - lo]++;
      }
    }
    changedVars = new int[vars.length];
    isChanged = new boolean[vars.length];
    dirty = new int[n];
    isDirty = new boolean[n];
    mark = new int[tuple.length];
    hits = new int[n];
    seen = new int[n];
    touched = new int[n];
    setScope(vars);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void queueVariable(int level, Var var) {
    Integer v = position.get(var);
    if (v != null && !isChanged[v]) {
      isChanged[v] = true;
      changedVars[changedSize++] = v;
    }
  }

  @Override
  public void removeLevel(int level) {
    while (doneSize > 0 && doneLevel[doneSize - 1] >= level) {
      int event = done[--doneSize];
      int r = event >>> 1;
      if ((event & 1) == 1) {
        killed[r] = false;
        if (!dead[r]) {
          addSupport(r, 1);
        }
      } else {
        dead[r] = false;
        for (int e : elems[r]) {
          aliveCount[e]++;
        }
        if (!killed[r]) {
          addSupport(r, 1);
        }
      }
    }
    while (changedSize > 0) {
      isChanged[changedVars[--changedSize]] = false;
    }
    while (dirtySize > 0) {
      isDirty[dirty[--dirtySize]] = false;
    }
  }

  private void addSupport(int r, int delta) {
    int base = firstVar[tupleGroup[r]];
    int[] t = tuple[r];
    for (int j = 0; j < t.length; j++) {
      support[(base + j) * range + t[j] - minValue] += delta;
    }
  }

  private void record(int event, int level) {
    if (doneSize == done.length) {
      done = Arrays.copyOf(done, 2 * doneSize);
      doneLevel = Arrays.copyOf(doneLevel, 2 * doneSize);
    }
    done[doneSize] = event;
    doneLevel[doneSize++] = level;
  }

  @Override
  public void consistency(Store store) {
    if (firstCall) {
      firstCall = false;
      for (int v = 0; v < vars.length; v++) {
        queueVariable(store.level, vars[v]);
      }
      for (int e = 0; e < cover.length; e++) {
        if (primary[e]) {
          markDirty(e);
        }
      }
      for (int e = 0; e < cover.length; e++) {
        if (primary[e] && aliveCount[e] == 0) {
          failVar = -1;
          failElement = e;
          throw Store.failException;
        }
      }
    }
    while (changedSize > 0 || dirtySize > 0) {
      while (changedSize > 0) {
        int v = changedVars[--changedSize];
        isChanged[v] = false;
        kill(store, v);
      }
      while (dirtySize > 0 && changedSize == 0) {
        int a = dirty[--dirtySize];
        isDirty[a] = false;
        if (primary[a]) {
          inclusion(store, a);
        }
      }
    }
  }

  // the tuples of the group of variable v with a value out of its domain die
  private void kill(Store store, int v) {
    int i = groupOf[v];
    int j = columnOf[v];
    IntVar x = vars[v];
    for (int r : groupTuples[i]) {
      if (dead[r] || x.domain.contains(tuple[r][j])) {
        continue;
      }
      dead[r] = true;
      record(r << 1, store.level);
      // all counts first, so that undoing the record is exact even after a failure
      for (int e : elems[r]) {
        aliveCount[e]--;
      }
      if (!killed[r]) {
        addSupport(r, -1);
      }
      for (int e : elems[r]) {
        if (primary[e]) {
          if (aliveCount[e] == 0) {
            failVar = -1;
            failElement = e;
            throw Store.failException;
          }
          markDirty(e);
        }
      }
      if (!killed[r]) {
        prune(store, r);
      }
    }
  }

  private void markDirty(int e) {
    if (!isDirty[e]) {
      isDirty[e] = true;
      dirty[dirtySize++] = e;
    }
  }

  // tuple r no longer supports its values, its supports already taken away: a value of it without
  // support is removed
  private void prune(Store store, int r) {
    int base = firstVar[tupleGroup[r]];
    int[] t = tuple[r];
    for (int j = 0; j < t.length; j++) {
      IntVar x = vars[base + j];
      if (support[(base + j) * range + t[j] - minValue] == 0 && x.domain.contains(t[j])) {
        if (x.singleton()) {
          failElement = -1;
          failVar = base + j;
          throw Store.failException;
        }
        pruned++;
        x.domain.inComplement(store.level, x, t[j]);
      }
    }
  }

  // DL+: when every alive tuple of a covers b, the tuples of b that miss a are killed
  private void inclusion(Store store, int a) {
    if (++stamp == Integer.MAX_VALUE) {
      Arrays.fill(mark, 0);
      Arrays.fill(seen, 0);
      stamp = 1;
    }
    int options = aliveCount[a];
    int size = 0;
    for (int r : cover[a]) {
      if (dead[r]) {
        continue;
      }
      mark[r] = stamp;
      for (int b : elems[r]) {
        if (seen[b] != stamp) {
          seen[b] = stamp;
          hits[b] = 0;
          touched[size++] = b;
        }
        hits[b]++;
      }
    }
    for (int t = 0; t < size; t++) {
      int b = touched[t];
      if (b == a || hits[b] != options || aliveCount[b] == options) {
        continue;
      }
      for (int r : cover[b]) {
        if (!dead[r] && !killed[r] && mark[r] != stamp) {
          killed[r] = true;
          witness[r] = a;
          kills++;
          record((r << 1) | 1, store.level);
          addSupport(r, -1);
          prune(store, r);
        }
      }
    }
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    used.clear();
    IntVar x = trail.variable(entry);
    Integer v = position.get(x);
    if (v == null) {
      return false;
    }
    if (trail.kind(entry) == AtomicTrail.NE) {
      return removed(trail, v, trail.value(entry), entry, out);
    }
    // a bound moved over the values removed at the end of the domain
    // the bound before the entry and the values between it and the new bound
    boolean lower = trail.kind(entry) == AtomicTrail.GE;
    int from = lower ? trail.minBefore(x, entry) : trail.value(entry) + 1;
    int to = lower ? trail.value(entry) - 1 : trail.maxBefore(x, entry);
    if (lower) {
      trail.addLowerBound(x, entry, out);
    } else {
      trail.addUpperBound(x, entry, out);
    }
    for (int w = from; w <= to; w++) {
      if (!trail.excludedBefore(x, w, entry, out) && !removed(trail, v, w, entry, out)) {
        return false;
      }
    }
    return true;
  }

  // the reason why no tuple supports value w of variable v before the position
  private boolean removed(AtomicTrail trail, int v, int w, int position, EntryList out) {
    if (w < minValue || w - minValue >= range) {
      return false;
    }
    int i = groupOf[v];
    int j = columnOf[v];
    for (int r : cover[groups.length + w - minValue]) {
      if (tupleGroup[r] == i && tuple[r][j] == w && !gone(trail, r, j, position, out)) {
        return false;
      }
    }
    return true;
  }

  // tuple r is dead (a value other than column skip out of its domain) or killed before the
  // position
  private boolean gone(AtomicTrail trail, int r, int skip, int position, EntryList out) {
    return deadBefore(trail, r, skip, position, out)
        || killed[r] && missing(trail, witness[r], r, position, out);
  }

  // entries in the reason being built, so that a tuple is explained by an atom already in it when
  // it can be; otherwise by its earliest atom, which more tuples share
  private final java.util.Set<Integer> used = new java.util.HashSet<>();

  private final EntryList scratch = new EntryList();

  private boolean deadBefore(AtomicTrail trail, int r, int skip, int position, EntryList out) {
    IntVar[] x = groups[tupleGroup[r]];
    int[] t = tuple[r];
    int best = -1;
    for (int j = 0; j < t.length; j++) {
      if (j == skip) {
        continue;
      }
      scratch.clear();
      if (trail.excludedBefore(x[j], t[j], position, scratch)) {
        if (scratch.size() == 0) {
          // the value was never in the domain
          return true;
        }
        int e = scratch.get(0);
        if (used.contains(e)) {
          return true;
        }
        if (best < 0 || e < best) {
          best = e;
        }
      }
    }
    if (best < 0) {
      return false;
    }
    used.add(best);
    out.add(best);
    return true;
  }

  private void truncate(EntryList out, int start) {
    for (int p = start; p < out.size(); p++) {
      used.remove(out.get(p));
    }
    out.truncate(start);
  }

  // the tuples of element a that share no element with r, all dead before the position
  private boolean missing(AtomicTrail trail, int a, int r, int position, EntryList out) {
    int start = out.size();

    for (int q : cover[a]) {
      if (q != r && !intersects(elems[q], elems[r]) && !deadBefore(trail, q, -1, position, out)) {
        truncate(out, start);
        return false;
      }
    }
    return true;
  }

  private static boolean intersects(int[] s, int[] t) {
    int i = 0;
    int j = 0;
    while (i < s.length && j < t.length) {
      if (s[i] == t[j]) {
        return true;
      }
      if (s[i] < t[j]) {
        i++;
      } else {
        j++;
      }
    }
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    used.clear();
    int e = failElement;
    int v = failVar;
    failElement = -1;
    failVar = -1;
    int now = trail.size();
    if (v >= 0) {
      // the last value of v lost its last tuple: every tuple with it is dead or killed
      return removed(trail, v, vars[v].value(), now, out) && addValue(trail, vars[v], now, out);
    }
    if (e < 0) {
      return false;
    }
    for (int r : cover[e]) {
      if (!deadBefore(trail, r, -1, now, out)) {
        return false;
      }
    }
    return true;
  }

  // the atoms that leave x with its single value
  private static boolean addValue(AtomicTrail trail, IntVar x, int position, EntryList out) {
    trail.atomsBefore(x, position, out);
    return true;
  }

  @Override
  public boolean satisfied() {
    boolean[] taken = new boolean[cover.length];
    for (int i = 0; i < groups.length; i++) {
      int[] t = new int[groups[i].length];
      for (int j = 0; j < t.length; j++) {
        if (!groups[i][j].singleton()) {
          return false;
        }
        t[j] = groups[i][j].value();
      }
      boolean found = false;
      for (int[] u : given[i]) {
        found |= Arrays.equals(u, t);
      }
      if (!found) {
        return false;
      }
      for (int w : t) {
        int e = groups.length + w - minValue;
        if (taken[e]) {
          return false;
        }
        taken[e] = true;
      }
    }
    if (exact) {
      for (int e = groups.length; e < cover.length; e++) {
        if (primary[e] && !taken[e]) {
          return false;
        }
      }
    }
    return true;
  }

  @Override
  public TableCover copy(VarMap map) {
    IntVar[][] copied = new IntVar[groups.length][];
    for (int i = 0; i < groups.length; i++) {
      copied[i] = new IntVar[groups[i].length];
      for (int j = 0; j < groups[i].length; j++) {
        copied[i][j] = map.get(groups[i][j]);
      }
    }
    return new TableCover(copied, given, exact);
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : TableCover(").append(groups.length).append(" groups, ");
    result.append(tuple.length).append(" tuples, exact ").append(exact).append(')');
    return result.toString();
  }
}
