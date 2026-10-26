/*
 * AtomicTrail.java
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

package org.jacop.lcg;

import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Map;
import org.jacop.api.RemoveLevelLate;
import org.jacop.constraints.Constraint;
import org.jacop.core.BooleanVar;
import org.jacop.core.DomainChangeRecorder;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * The atomic trail of lazy clause generation: every change of an integer variable's domain,
 * recorded in order as atoms {@code [x >= v]}, {@code [x <= v]} and {@code [x != v]}, each with the
 * store level and the constraint that was propagating ({@link Store#currentConstraint}, null
 * outside propagation). Atoms describe changes from the domains at {@link #attach}: those domains
 * are facts that need no atom.
 *
 * <p>Each variable's entries form a chain, so the atoms that held for a variable at any trail
 * position can be found ({@link #atomsBefore}). That gives the generic reason of a propagation: the
 * atoms of the propagating constraint's variables just before it.
 *
 * <p>Entries above a removed level are dropped when the store backtracks.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class AtomicTrail implements DomainChangeRecorder, RemoveLevelLate {

  /** Atom kind {@code [x >= value]}. */
  public static final int GE = 0;

  /** Atom kind {@code [x <= value]}. */
  public static final int LE = 1;

  /** Atom kind {@code [x != value]}. */
  public static final int NE = 2;

  private final Store store;

  // entries
  private IntVar[] entryVar = new IntVar[256];
  private int[] kind = new int[256];
  private int[] value = new int[256];
  private int[] level = new int[256];
  private Constraint[] reason = new Constraint[256];
  private int[] previous = new int[256]; // the variable's previous entry, or -1
  private int size;

  // per variable (by id): the domain the entries so far describe, as its bounds and, when it has
  // holes, a copy; and the last entry
  private IntDomain[] shadow = new IntDomain[0];
  private int[] shadowMin = new int[0];
  private int[] shadowMax = new int[0];
  private IntDomain[] root = new IntDomain[0]; // the domain when recording started
  private int[] last = new int[0];

  // boolean variables, which have no store index, by the order they were first seen
  private final Map<IntVar, Integer> booleanIds = new IdentityHashMap<>();

  /**
   * Creates the trail and starts recording the changes of every integer variable of the store. The
   * current domains are the facts the atoms are relative to.
   *
   * @param store the store
   */
  public AtomicTrail(Store store) {
    this.store = store;
    for (int i = 0; i < store.size(); i++) {
      Var v = store.vars[i];
      if (v instanceof IntVar x) {
        slot(x);
      }
    }
    store.variablesHashMap.values().stream()
        .filter(BooleanVar.class::isInstance)
        .map(BooleanVar.class::cast)
        .sorted((a, b) -> a.id().compareTo(b.id()))
        .forEach(this::slot);
    store.domainChangeRecorder = this;
    store.registerRemoveLevelLateListener(this);
  }

  /** Stops recording. */
  public void detach() {
    store.domainChangeRecorder = null;
    store.removeLevelLateListeners.remove(this);
  }

  /**
   * Returns the number by which this trail knows a variable: twice its store index, or for a {@link
   * BooleanVar}, which has no store index, an odd number given when the trail first sees it.
   *
   * @param x the variable
   * @return its number, at least 0
   */
  public int id(IntVar x) {
    int i = x.index();
    if (i >= 0) {
      return 2 * i;
    }
    return 2 * booleanIds.computeIfAbsent(x, b -> booleanIds.size()) + 1;
  }

  private int slot(IntVar x) {
    int i = id(x);
    if (i >= shadow.length) {
      int n = Math.max(i + 1, 2 * shadow.length);
      int old = shadow.length;
      shadow = Arrays.copyOf(shadow, n);
      shadowMin = Arrays.copyOf(shadowMin, n);
      shadowMax = Arrays.copyOf(shadowMax, n);
      root = Arrays.copyOf(root, n);
      last = Arrays.copyOf(last, n);
      Arrays.fill(last, old, n, -1);
    }
    if (root[i] == null) {
      root[i] = x.dom().cloneLight();
      setShadow(i, root[i]);
    }
    return i;
  }

  // copies a domain into the shadow; one without holes is kept as its bounds only
  private void setShadow(int i, IntDomain d) {
    int min = d.min();
    int max = d.max();
    shadowMin[i] = min;
    shadowMax[i] = max;
    shadow[i] = d.getSize() == (long) max - min + 1 ? null : d.cloneLight();
  }

  @Override
  public void domainChanged(IntVar x, int event) {
    int i = slot(x);
    IntDomain now = x.dom();
    int min = now.min();
    int max = now.max();
    if (min > shadowMin[i]) {
      add(x, i, GE, min);
    }
    if (max < shadowMax[i]) {
      add(x, i, LE, max);
    }
    if (now.getSize() < (long) max - min + 1) {
      IntDomain before = shadow[i];
      if (before == null) {
        // every value of [min, max] was in the domain: each hole is new
        for (int v = min; v < max; ) {
          int next = now.nextValue(v);
          for (int u = v + 1; u < next; u++) {
            add(x, i, NE, u);
          }
          v = next;
        }
      } else {
        IntDomain inside = before.intersect(min, max);
        if (inside.getSize() > now.getSize()) {
          IntDomain removed = inside.subtract(now);
          for (ValueEnumeration e = removed.valueEnumeration(); e.hasMoreElements(); ) {
            add(x, i, NE, e.nextElement());
          }
        }
      }
    }
    setShadow(i, now);
  }

  private void add(IntVar x, int i, int k, int v) {
    if (size == entryVar.length) {
      int n = 2 * size;
      entryVar = Arrays.copyOf(entryVar, n);
      kind = Arrays.copyOf(kind, n);
      value = Arrays.copyOf(value, n);
      level = Arrays.copyOf(level, n);
      reason = Arrays.copyOf(reason, n);
      previous = Arrays.copyOf(previous, n);
    }
    entryVar[size] = x;
    kind[size] = k;
    value[size] = v;
    level[size] = store.level;
    reason[size] = store.currentConstraint;
    previous[size] = last[i];
    last[i] = size;
    size++;
  }

  @Override
  public void removeLevelLate(int removedLevel) {
    while (size > 0 && level[size - 1] >= removedLevel) {
      size--;
      IntVar x = entryVar[size];
      int i = id(x);
      last[i] = previous[size];
      setShadow(i, x.dom());
      entryVar[size] = null;
      reason[size] = null;
    }
  }

  /**
   * Returns the number of entries.
   *
   * @return the trail size
   */
  public int size() {
    return size;
  }

  /**
   * Returns the variable of an entry.
   *
   * @param entry the entry
   * @return its variable
   */
  public IntVar variable(int entry) {
    return entryVar[entry];
  }

  /**
   * Returns the kind of an entry's atom: {@link #GE}, {@link #LE} or {@link #NE}.
   *
   * @param entry the entry
   * @return its kind
   */
  public int kind(int entry) {
    return kind[entry];
  }

  /**
   * Returns the value of an entry's atom.
   *
   * @param entry the entry
   * @return its value
   */
  public int value(int entry) {
    return value[entry];
  }

  /**
   * Returns the store level at which an entry was recorded.
   *
   * @param entry the entry
   * @return its level
   */
  public int level(int entry) {
    return level[entry];
  }

  /**
   * Returns the constraint that was propagating when an entry was recorded.
   *
   * @param entry the entry
   * @return the constraint, or null outside propagation (a decision, or a change made by search)
   */
  public Constraint reason(int entry) {
    return reason[entry];
  }

  private int lastBefore(IntVar x, int position) {
    int i = id(x);
    if (i >= last.length) {
      return -1;
    }
    int e = last[i];
    while (e >= position) {
      e = previous[e];
    }
    return e;
  }

  private int latest(IntVar x, int position, int k) {
    int e = lastBefore(x, position);
    while (e >= 0 && kind[e] != k) {
      e = previous[e];
    }
    return e;
  }

  /**
   * Returns a variable's domain when the trail started recording it: the facts its atoms are
   * relative to.
   *
   * @param x the variable
   * @return its initial domain, which must not be changed
   */
  public IntDomain rootDomain(IntVar x) {
    return root[slot(x)];
  }

  /**
   * Adds to {@code out} the entry of a variable's lower bound just before trail position {@code
   * position}, unless that bound is the initial one.
   *
   * @param x the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @param out where the entry is added
   */
  public void addLowerBound(IntVar x, int position, EntryList out) {
    int e = latest(x, position, GE);
    if (e >= 0) {
      out.add(e);
    }
  }

  /**
   * Adds to {@code out} the entry of a variable's upper bound just before trail position {@code
   * position}, unless that bound is the initial one.
   *
   * @param x the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @param out where the entry is added
   */
  public void addUpperBound(IntVar x, int position, EntryList out) {
    int e = latest(x, position, LE);
    if (e >= 0) {
      out.add(e);
    }
  }

  /**
   * Returns a variable's minimum just before a trail position.
   *
   * @param x the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @return its minimum then
   */
  public int minBefore(IntVar x, int position) {
    int e = latest(x, position, GE);
    return e >= 0 ? value[e] : root[slot(x)].min();
  }

  /**
   * Returns a variable's maximum just before a trail position.
   *
   * @param x the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @return its maximum then
   */
  public int maxBefore(IntVar x, int position) {
    int e = latest(x, position, LE);
    return e >= 0 ? value[e] : root[slot(x)].max();
  }

  /**
   * Tells whether a value was out of a variable's domain just before a trail position, and if so
   * adds to {@code out} the entry that removed it (none when the value was never in the domain
   * recording started from).
   *
   * @param x the variable
   * @param v the value
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @param out where the entry is added
   * @return true when v was not in the domain
   */
  public boolean excludedBefore(IntVar x, int v, int position, EntryList out) {
    if (!root[slot(x)].contains(v)) {
      return true;
    }
    for (int f = lastBefore(x, position); f >= 0; f = previous[f]) {
      if (removes(f, v)) {
        out.add(f);
        return true;
      }
    }
    return false;
  }

  // whether entry f removes value v from its variable's domain
  private boolean removes(int f, int v) {
    return switch (kind[f]) {
      case NE -> value[f] == v;
      case GE -> value[f] > v;
      default -> value[f] < v;
    };
  }

  /**
   * Adds to {@code out} the {@code !=} atoms that a bound entry skipped: the holes of its variable,
   * recorded before it, between the bound a propagator computed and the bound the domain moved to.
   * A propagator that prunes a bound by {@code inMin} or {@code inMax} implies only the computed
   * bound, so its explanation adds these to reach the recorded one.
   *
   * @param entry a {@link #GE} or {@link #LE} entry
   * @param bound the bound the propagator computed: at most the value of a {@link #GE} entry, at
   *     least the value of a {@link #LE} entry; when it is not known, {@link Integer#MIN_VALUE} or
   *     {@link Integer#MAX_VALUE} adds every hole recorded beyond the recorded bound
   * @param out where the entries are added
   */
  public void addSkippedHoles(int entry, int bound, EntryList out) {
    int v = value[entry];
    boolean ge = kind[entry] == GE;
    for (int f = previous[entry]; f >= 0; f = previous[f]) {
      if (kind[f] == NE
          && (ge ? value[f] >= bound && value[f] < v : value[f] <= bound && value[f] > v)) {
        out.add(f);
      }
    }
  }

  /**
   * Adds to {@code out} the entries that describe a variable's domain just before trail position
   * {@code position}: its strongest {@code >=} and {@code <=} atoms and its {@code !=} atoms inside
   * those bounds. Each such entry is the latest of its atom.
   *
   * @param x the variable
   * @param position the trail position (an entry index, or {@link #size()} for now)
   * @param out where the entries are added
   */
  public void atomsBefore(IntVar x, int position, EntryList out) {
    int ge = latest(x, position, GE);
    int le = latest(x, position, LE);
    int lo = ge >= 0 ? value[ge] : Integer.MIN_VALUE;
    int hi = le >= 0 ? value[le] : Integer.MAX_VALUE;
    if (ge >= 0) {
      out.add(ge);
    }
    if (le >= 0) {
      out.add(le);
    }
    for (int f = lastBefore(x, position); f >= 0; f = previous[f]) {
      if (kind[f] == NE && value[f] > lo && value[f] < hi) {
        out.add(f);
      }
    }
  }

  /**
   * Adds to {@code out} the reason of an entry: the constraint's own explanation when it is {@link
   * Explainable} and gives one, otherwise the generic reason.
   *
   * @param entry the entry, which must have a constraint as reason
   * @param out where the entries are added
   * @return true when the constraint explained it, false for the generic reason
   */
  public boolean explain(int entry, EntryList out) {
    int mark = out.size();
    if (reason[entry] instanceof Explainable c && c.explain(this, entry, out)) {
      return true;
    }
    out.truncate(mark);
    genericReason(entry, out);
    return false;
  }

  /**
   * Adds to {@code out} the reason of a failure of a constraint now: its own explanation when it is
   * {@link Explainable} and gives one, otherwise the atoms of all its variables.
   *
   * @param failed the constraint that failed
   * @param out where the entries are added
   * @return true when the constraint explained it, false for the generic reason
   */
  public boolean explainFailure(Constraint failed, EntryList out) {
    int mark = out.size();
    if (failed instanceof Explainable c && c.explainFailure(this, out)) {
      return true;
    }
    out.truncate(mark);
    for (Var v : failed.arguments()) {
      if (v instanceof IntVar x) {
        atomsBefore(x, size, out);
      }
    }
    return false;
  }

  /**
   * Adds to {@code out} the generic reason of an entry: the atoms of every variable of its
   * constraint just before it. It is valid for any propagator whose pruning depends only on the
   * current domains of its variables.
   *
   * @param entry the entry, which must have a constraint as reason
   * @param out where the entries are added
   */
  public void genericReason(int entry, EntryList out) {
    Constraint c = reason[entry];
    for (Var v : c.arguments()) {
      if (v instanceof IntVar x) {
        atomsBefore(x, entry, out);
      }
    }
  }

  /**
   * Returns a readable form of an entry's atom.
   *
   * @param entry the entry
   * @return for example {@code [x >= 3]}
   */
  public String atomString(int entry) {
    String op =
        switch (kind[entry]) {
          case GE -> ">=";
          case LE -> "<=";
          default -> "!=";
        };
    return "[" + entryVar[entry].id() + " " + op + " " + value[entry] + "]";
  }
}
