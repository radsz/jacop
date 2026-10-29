/*
 * RestartNoGoods.java
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

package org.jacop.search.free;

import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * The store of the nogoods that {@link FreeSearch} learns at restarts: one constraint holding all
 * of them. A nogood {@code not (x1 = a1 and ... and xk = ak)} forbids a combination of values that
 * an earlier run refuted (reduced nld-nogoods, Lecoutre et al. 2007).
 *
 * <p>Nogoods are kept in flat arrays and propagated with two watched literals per nogood. A literal
 * {@code x = a} becomes true only when {@code x} is fixed to {@code a}, so the constraint is woken
 * only when a watched variable is fixed. A watch does not move back on backtracking. When all
 * literals but one are true, the value of the last one is removed. Watch lists are kept per literal
 * {@code x = a}, so fixing {@code x} to {@code a} visits only the nogoods watching that literal.
 * Nogoods are added at the root, simplified with the root domains, and the oldest are deleted when
 * there are too many.
 *
 * <p>The constraint is not attached to the variables as a model constraint; it is woken through the
 * store's watched constraints. {@link #detach()} removes it from the store.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class RestartNoGoods extends Constraint {

  /** The default largest number of nogoods kept. */
  public static final int DEFAULT_MAX_NOGOODS = 100_000;

  /** The default largest number of literals of a nogood; longer nogoods are not kept. */
  public static final int DEFAULT_MAX_LENGTH = 200;

  private final Store store;
  private final int maxNogoods;
  private final int maxLength;

  // variables of the nogoods
  private final Map<IntVar, Integer> varIndex = new IdentityHashMap<>();
  private IntVar[] vars = new IntVar[16];
  private int varCount;

  // nogood n has literals start[n] .. start[n] + length[n] - 1
  private int[] start = new int[64];
  private int[] length = new int[64];
  // positions of the two watched literals of each nogood
  private int[] watch0 = new int[64];
  private int[] watch1 = new int[64];
  private int nogoodCount;

  private int[] litVar = new int[256];
  private int[] litValue = new int[256];
  // watch list of each literal position
  private int[] litWatch = new int[256];
  private int litCount;

  // the watch lists of each variable: values in increasing order and their watch lists
  private int[][] varValues = new int[16][];
  private int[][] varWatch = new int[16][];
  private int[] varWatchCount = new int[16];

  // watch lists, one per distinct literal x = a: entries 2 * nogood + slot
  private int[][] watches = new int[16][];
  private int[] watchSize = new int[16];
  private int watchCount;

  // variables fixed since the last propagation
  private int[] pending = new int[16];
  private int pendingSize;

  private boolean failedAtRoot;
  private long added;
  private long deleted;

  /**
   * Creates an empty nogood store.
   *
   * @param store the store.
   * @param maxNogoods the largest number of nogoods kept; the oldest are deleted beyond it.
   * @param maxLength the largest number of literals of a nogood; longer ones are not kept.
   */
  public RestartNoGoods(Store store, int maxNogoods, int maxLength) {
    if (maxNogoods < 1 || maxLength < 1) {
      throw new IllegalArgumentException("Limits of the nogood store must be positive");
    }
    this.store = store;
    this.maxNogoods = maxNogoods;
    this.maxLength = maxLength;
    this.queueIndex = 0;
    this.numberId = 0;
    setScope(new Var[0]);
  }

  @Override
  public void impose(Store store) {
    if (store.watchedConstraints == null) {
      store.watchedConstraints = Var.createEmptyPositioning();
    }
    store.countConstraint();
  }

  /** Removes the constraint from the store; it is no longer woken. */
  public void detach() {
    for (int i = 0; i < varCount; i++) {
      store.deregisterWatchedLiteralConstraint(vars[i], this);
    }
  }

  /**
   * Adds the nogood {@code not (vars[0] = values[0] and ... and vars[n-1] = values[n-1])}. It must
   * be called at the root level of the search, outside of propagation. A nogood that has become
   * unit at the root removes its value at once; one whose literals all hold at the root makes the
   * next propagation fail.
   *
   * @param nogoodVars the variables.
   * @param nogoodValues the values.
   * @param n the number of literals.
   */
  public void add(IntVar[] nogoodVars, int[] nogoodValues, int n) {
    if (failedAtRoot) {
      return;
    }
    if (n > maxLength) {
      return;
    }
    ensureLiterals(litCount + n);
    int first = litCount;
    int size = 0;
    for (int i = 0; i < n; i++) {
      IntVar x = nogoodVars[i];
      int a = nogoodValues[i];
      if (!x.domain.contains(a)) {
        // the literal is false at the root, so the nogood always holds
        litCount = first;
        return;
      }
      if (x.singleton()) {
        // the literal holds at the root and can be left out
        continue;
      }
      int xi = indexOf(x);
      boolean duplicate = false;
      for (int j = first; j < first + size; j++) {
        if (litVar[j] == xi) {
          if (litValue[j] != a) {
            litCount = first;
            return;
          }
          duplicate = true;
        }
      }
      if (!duplicate) {
        litVar[first + size] = xi;
        litValue[first + size] = a;
        litWatch[first + size] = watchOf(xi, a);
        size++;
      }
    }
    added++;
    if (size == 0) {
      failedAtRoot = true;
      store.addChanged(this);
      return;
    }
    if (size == 1) {
      IntVar x = vars[litVar[first]];
      x.domain.inComplement(store.level, x, litValue[first]);
      return;
    }
    litCount = first + size;
    if (nogoodCount == maxNogoods) {
      deleteOldest();
      // the literals of the new nogood have moved to the end of the compacted arrays
      first = litCount - size;
    }
    ensureNogoods(nogoodCount + 1);
    int k = nogoodCount++;
    start[k] = first;
    length[k] = size;
    watch0[k] = first;
    watch1[k] = first + 1;
    addWatch(litWatch[first], 2 * k);
    addWatch(litWatch[first + 1], 2 * k + 1);
  }

  /**
   * Returns the number of nogoods kept.
   *
   * @return the number of nogoods.
   */
  public int size() {
    return nogoodCount;
  }

  /**
   * Returns the number of nogoods added, including those that pruned at the root at once.
   *
   * @return the number of nogoods added.
   */
  public long getAdded() {
    return added;
  }

  /**
   * Returns the number of nogoods deleted to stay within the limit.
   *
   * @return the number of nogoods deleted.
   */
  public long getDeleted() {
    return deleted;
  }

  @Override
  public void queueVariable(int level, Var v) {
    Integer i = varIndex.get(v);
    if (i == null) {
      return;
    }
    if (pendingSize == pending.length) {
      pending = Arrays.copyOf(pending, 2 * pendingSize + 16);
    }
    pending[pendingSize++] = i;
  }

  @Override
  public void consistency(Store store) {
    if (failedAtRoot) {
      pendingSize = 0;
      throw Store.failException;
    }
    // propagation may fix more variables, which are appended to pending
    while (pendingSize > 0) {
      int xi = pending[--pendingSize];
      IntVar x = vars[xi];
      // entries left from a failed propagation may refer to variables no longer fixed
      if (x.singleton()) {
        propagateFixed(xi, x.value());
      }
    }
  }

  @Override
  public void cleanAfterFailure() {
    pendingSize = 0;
  }

  /** Visits the nogoods watching the literal xi = a, which has become true. */
  private void propagateFixed(int xi, int a) {
    int w = findWatch(xi, a);
    if (w < 0) {
      return;
    }
    int[] list = watches[w];
    int size = watchSize[w];
    int kept = 0;
    int i = 0;
    try {
      while (i < size) {
        int entry = list[i++];
        int k = entry >> 1;
        boolean first = (entry & 1) == 0;
        int own = first ? watch0[k] : watch1[k];
        int other = first ? watch1[k] : watch0[k];
        int replacement = findReplacement(k, own, other);
        if (replacement >= 0) {
          if (first) {
            watch0[k] = replacement;
          } else {
            watch1[k] = replacement;
          }
          addWatch(litWatch[replacement], entry);
          continue;
        }
        list[kept++] = entry;
        IntVar y = vars[litVar[other]];
        int b = litValue[other];
        if (y.domain.contains(b)) {
          // all other literals hold, so the last one must not
          y.domain.inComplement(store.level, y, b);
        }
      }
    } finally {
      // keep the entries not visited when the propagation failed
      while (i < size) {
        list[kept++] = list[i++];
      }
      watchSize[w] = kept;
    }
  }

  /** Returns a literal of nogood k, other than the two watched ones, that does not hold, or -1. */
  private int findReplacement(int k, int own, int other) {
    int end = start[k] + length[k];
    for (int j = start[k]; j < end; j++) {
      if (j == own || j == other) {
        continue;
      }
      IntVar z = vars[litVar[j]];
      if (!z.singleton(litValue[j])) {
        return j;
      }
    }
    return -1;
  }

  /** Deletes the older half of the nogoods and rebuilds the watch lists; called at the root. */
  private void deleteOldest() {
    int drop = nogoodCount / 2;
    int newestFirst = start[drop];
    int shift = newestFirst;
    System.arraycopy(litVar, newestFirst, litVar, 0, litCount - newestFirst);
    System.arraycopy(litValue, newestFirst, litValue, 0, litCount - newestFirst);
    System.arraycopy(litWatch, newestFirst, litWatch, 0, litCount - newestFirst);
    litCount -= shift;
    int kept = nogoodCount - drop;
    for (int k = 0; k < kept; k++) {
      start[k] = start[k + drop] - shift;
      length[k] = length[k + drop];
      watch0[k] = watch0[k + drop] - shift;
      watch1[k] = watch1[k + drop] - shift;
    }
    nogoodCount = kept;
    deleted += drop;
    Arrays.fill(watchSize, 0, watchCount, 0);
    for (int k = 0; k < nogoodCount; k++) {
      addWatch(litWatch[watch0[k]], 2 * k);
      addWatch(litWatch[watch1[k]], 2 * k + 1);
    }
  }

  private int indexOf(IntVar x) {
    Integer i = varIndex.get(x);
    if (i != null) {
      return i;
    }
    if (varCount == vars.length) {
      int n = 2 * varCount + 16;
      vars = Arrays.copyOf(vars, n);
      varValues = Arrays.copyOf(varValues, n);
      varWatch = Arrays.copyOf(varWatch, n);
      varWatchCount = Arrays.copyOf(varWatchCount, n);
    }
    vars[varCount] = x;
    varValues[varCount] = new int[2];
    varWatch[varCount] = new int[2];
    varIndex.put(x, varCount);
    store.registerWatchedLiteralConstraint(x, this);
    return varCount++;
  }

  /** Returns the watch list of the literal xi = a, or -1 if no nogood has this literal. */
  private int findWatch(int xi, int a) {
    int p = Arrays.binarySearch(varValues[xi], 0, varWatchCount[xi], a);
    return p >= 0 ? varWatch[xi][p] : -1;
  }

  /** Returns the watch list of the literal xi = a, creating it if needed. */
  private int watchOf(int xi, int a) {
    int n = varWatchCount[xi];
    int[] values = varValues[xi];
    int p = Arrays.binarySearch(values, 0, n, a);
    if (p >= 0) {
      return varWatch[xi][p];
    }
    p = -p - 1;
    if (n == values.length) {
      values = Arrays.copyOf(values, 2 * n);
      varValues[xi] = values;
      varWatch[xi] = Arrays.copyOf(varWatch[xi], 2 * n);
    }
    int[] lists = varWatch[xi];
    System.arraycopy(values, p, values, p + 1, n - p);
    System.arraycopy(lists, p, lists, p + 1, n - p);
    if (watchCount == watches.length) {
      watches = Arrays.copyOf(watches, 2 * watchCount);
      watchSize = Arrays.copyOf(watchSize, 2 * watchCount);
    }
    int w = watchCount++;
    watches[w] = new int[4];
    values[p] = a;
    lists[p] = w;
    varWatchCount[xi] = n + 1;
    return w;
  }

  private void addWatch(int w, int entry) {
    int[] list = watches[w];
    if (watchSize[w] == list.length) {
      list = Arrays.copyOf(list, 2 * list.length + 4);
      watches[w] = list;
    }
    list[watchSize[w]++] = entry;
  }

  private void ensureLiterals(int n) {
    if (n > litVar.length) {
      int size = Math.max(n, 2 * litVar.length);
      litVar = Arrays.copyOf(litVar, size);
      litValue = Arrays.copyOf(litValue, size);
      litWatch = Arrays.copyOf(litWatch, size);
    }
  }

  private void ensureNogoods(int n) {
    if (n > start.length) {
      int size = Math.max(n, 2 * start.length);
      start = Arrays.copyOf(start, size);
      length = Arrays.copyOf(length, size);
      watch0 = Arrays.copyOf(watch0, size);
      watch1 = Arrays.copyOf(watch1, size);
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public void removeConstraint() {
    // nogoods hold for the whole search
  }

  @Override
  public String toString() {
    return id() + " : RestartNoGoods(" + nogoodCount + " nogoods, " + litCount + " literals)";
  }

  @Override
  public String id() {
    return "RestartNoGoods";
  }
}
