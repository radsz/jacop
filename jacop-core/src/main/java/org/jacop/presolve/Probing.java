/*
 * Probing.java
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

package org.jacop.presolve;

import java.util.ArrayList;
import java.util.List;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.StoreState;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Root probing: tries values of the integer variables one level above the store's current level and
 * removes, at that level, every value whose assignment fails after propagation. Only values that
 * belong to no solution are removed, so probing keeps every solution of the store at its level.
 *
 * <ul>
 *   <li>{@link Mode#SHAVE} shaves the bounds of every variable: it tries the smallest value and
 *       removes it while it fails, then the same with the largest. A 0-1 variable is probed on both
 *       values (failed-literal probing); when both succeed, every other variable keeps only the
 *       bounds it can reach in one of the two branches (constructive disjunction).
 *   <li>{@link Mode#SAC} does the same, and on variables with at most {@link #sacDomainLimit(int)}
 *       values tries every value, which makes them singleton arc consistent when the budget allows.
 * </ul>
 *
 * <p>Passes over the variables repeat while one of them removes a value and the budget lasts. The
 * budget is checked between probes, so it can be passed by one probe. The store is left at its
 * level, at a fixpoint, unless probing proves it infeasible.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class Probing {

  /** What probing tries. */
  public enum Mode {
    /** No probing. */
    OFF,
    /** Bound shaving and failed-literal probing of 0-1 variables. */
    SHAVE,
    /** Shaving, and every value of variables with small domains. */
    SAC
  }

  /**
   * What probing did.
   *
   * @param feasible false if probing proved the store infeasible at its level.
   * @param probes values or literals tried.
   * @param failed probes that failed, each removing one value or a range of values.
   * @param narrowed bound reductions from constructive disjunction over 0-1 variables.
   * @param removed values removed from the domains, over all variables.
   * @param passes passes over the variables.
   * @param exhausted true if the budget ran out before a pass removed nothing.
   * @param timeNanos the time probing took.
   */
  public record Result(
      boolean feasible,
      int probes,
      int failed,
      int narrowed,
      long removed,
      int passes,
      boolean exhausted,
      long timeNanos) {

    /**
     * Tells whether probing changed the store.
     *
     * @return true if a domain was reduced or the store was found infeasible.
     */
    public boolean changed() {
      return !feasible || removed > 0;
    }
  }

  private final Store store;
  private Mode mode = Mode.SHAVE;
  private long budgetNanos = 1_000_000_000L;
  private int sacDomainLimit = 64;

  private int root;
  private long deadline;
  private List<IntVar> vars;
  private int probes;
  private int failed;
  private int narrowed;
  private boolean exhausted;
  // bounds of every variable at the end of the last successful probe, for constructive disjunction
  private int[] lastMin;
  private int[] lastMax;

  private Probing(Store store) {
    this.store = store;
  }

  /**
   * Starts probing a store at its current level.
   *
   * @param store the store, which must be {@link StoreState#ACTIVE}.
   * @return the probing.
   */
  public static Probing of(Store store) {
    return new Probing(store);
  }

  /**
   * Sets what probing tries; {@link Mode#SHAVE} by default.
   *
   * @param mode the mode.
   * @return this probing.
   */
  public Probing mode(Mode mode) {
    this.mode = mode;
    return this;
  }

  /**
   * Sets the time probing may take; one second by default.
   *
   * @param millis the budget in milliseconds.
   * @return this probing.
   */
  public Probing budget(long millis) {
    this.budgetNanos = millis * 1_000_000L;
    return this;
  }

  /**
   * Sets the largest domain whose every value is tried in {@link Mode#SAC}; 64 by default.
   *
   * @param size the number of values.
   * @return this probing.
   */
  public Probing sacDomainLimit(int size) {
    this.sacDomainLimit = size;
    return this;
  }

  /**
   * Probes.
   *
   * @return what probing did.
   */
  public Result probe() {
    long start = System.nanoTime();
    if (store.state() != StoreState.ACTIVE) {
      throw new IllegalStateException("Only an active store can be probed; it is " + store.state());
    }
    if (!store.consistency()) {
      return result(false, 0, 0, start);
    }
    root = store.level;
    deadline = start + budgetNanos;
    vars = intVariables();
    long sizeBefore = totalSize();
    lastMin = new int[vars.size()];
    lastMax = new int[vars.size()];

    int passes = 0;
    boolean feasible = true;
    if (mode != Mode.OFF) {
      try {
        boolean changed = true;
        while (changed && !outOfBudget()) {
          passes++;
          changed = pass();
        }
      } catch (FailException e) {
        feasible = false;
      }
    }
    long removed = feasible ? sizeBefore - totalSize() : 0;
    return result(feasible, removed, passes, start);
  }

  private Result result(boolean feasible, long removed, int passes, long start) {
    return new Result(
        feasible, probes, failed, narrowed, removed, passes, exhausted, System.nanoTime() - start);
  }

  /**
   * The integer variables of the store that are not fixed: those of the store array in store order,
   * then the Boolean variables, which the store keeps only by id.
   */
  private List<IntVar> intVariables() {
    List<IntVar> result = new ArrayList<>();
    for (int i = 0; i < store.size(); i++) {
      if (store.vars[i] instanceof IntVar v && !v.singleton()) {
        result.add(v);
      }
    }
    for (Var v : store.variablesHashMap.values()) {
      if (v.index() < 0 && v instanceof IntVar x && !x.singleton()) {
        result.add(x);
      }
    }
    return result;
  }

  private long totalSize() {
    long size = 0;
    for (IntVar v : vars) {
      size += v.getSize();
    }
    return size;
  }

  private boolean outOfBudget() {
    if (System.nanoTime() > deadline) {
      exhausted = true;
    }
    return exhausted;
  }

  /** One pass over the variables; returns true if it removed a value. */
  private boolean pass() {
    boolean changed = false;
    for (int i = 0; i < vars.size() && !outOfBudget(); i++) {
      IntVar x = vars.get(i);
      if (x.singleton()) {
        continue;
      }
      if (x.min() == 0 && x.max() == 1) {
        changed |= probeLiteral(i, x);
      } else if (mode == Mode.SAC && x.getSize() <= sacDomainLimit) {
        changed |= probeValues(x);
      } else {
        changed |= shave(x);
      }
    }
    return changed;
  }

  /**
   * Removes the bounds of x while their assignment fails. After a failure the next probe tries a
   * range twice as wide, x &lt;= min + step - 1 (or x &gt;= max - step + 1), so a long run of
   * values without support costs a logarithmic number of probes; after a success on a range the
   * step is halved until a single value succeeds.
   */
  private boolean shave(IntVar x) {
    boolean changed = false;
    for (int step = 1; !x.singleton() && !outOfBudget(); ) {
      int min = x.min();
      int last = (int) Math.min((long) min + step - 1, x.max() - 1L);
      if (probe(x, min, last, false)) {
        if (step == 1) {
          break;
        }
        step /= 2;
      } else {
        removeRange(x, min, last);
        changed = true;
        step = step <= Integer.MAX_VALUE / 2 ? step * 2 : step;
      }
    }
    for (int step = 1; !x.singleton() && !outOfBudget(); ) {
      int max = x.max();
      int first = (int) Math.max((long) max - step + 1, x.min() + 1L);
      if (probe(x, first, max, false)) {
        if (step == 1) {
          break;
        }
        step /= 2;
      } else {
        removeRange(x, first, max);
        changed = true;
        step = step <= Integer.MAX_VALUE / 2 ? step * 2 : step;
      }
    }
    return changed;
  }

  /** Tries every value of x and removes those that fail. */
  private boolean probeValues(IntVar x) {
    List<Integer> failing = new ArrayList<>();
    for (ValueEnumeration e = x.dom().valueEnumeration(); e.hasMoreElements(); ) {
      if (outOfBudget()) {
        break;
      }
      int value = e.nextElement();
      if (!probe(x, value, false)) {
        failing.add(value);
      }
    }
    for (int value : failing) {
      remove(x, value);
    }
    return !failing.isEmpty();
  }

  /**
   * Probes both values of a 0-1 variable. A failing value is removed; if both succeed, each other
   * variable is restricted to the hull of its bounds in the two branches.
   */
  private boolean probeLiteral(int index, IntVar x) {
    if (!probe(x, 0, true)) {
      remove(x, 0);
      return true;
    }
    int[] min0 = lastMin.clone();
    int[] max0 = lastMax.clone();
    if (outOfBudget()) {
      return false;
    }
    if (!probe(x, 1, true)) {
      remove(x, 1);
      return true;
    }
    boolean changed = false;
    for (int i = 0; i < vars.size(); i++) {
      IntVar v = vars.get(i);
      if (i == index || v.singleton()) {
        continue;
      }
      int min = Math.min(min0[i], lastMin[i]);
      int max = Math.max(max0[i], lastMax[i]);
      if (min > v.min() || max < v.max()) {
        v.domain.in(root, v, min, max);
        narrowed++;
        changed = true;
      }
    }
    if (changed) {
      propagate();
    }
    return changed;
  }

  /**
   * Tries x = value one level above the root; with record, keeps the bounds of every variable after
   * a successful probe.
   */
  private boolean probe(IntVar x, int value, boolean record) {
    return probe(x, value, value, record);
  }

  /**
   * Tries min &lt;= x &lt;= max one level above the root; with record, keeps the bounds of every
   * variable after a successful probe.
   */
  private boolean probe(IntVar x, int min, int max, boolean record) {
    probes++;
    store.setLevel(root + 1);
    boolean consistent;
    try {
      x.domain.in(store.level, x, min, max);
      consistent = store.consistency();
    } catch (FailException e) {
      consistent = false;
    }
    if (consistent && record) {
      for (int i = 0; i < vars.size(); i++) {
        IntVar v = vars.get(i);
        lastMin[i] = v.min();
        lastMax[i] = v.max();
      }
    }
    store.removeLevel(root + 1);
    store.setLevel(root);
    if (!consistent) {
      failed++;
    }
    return consistent;
  }

  /** Removes a value that belongs to no solution at the root and propagates. */
  private void remove(IntVar x, int value) {
    IntDomain d = x.domain;
    d.inComplement(root, x, value);
    propagate();
  }

  /** Removes a range of values that belong to no solution at the root and propagates. */
  private void removeRange(IntVar x, int min, int max) {
    x.domain.inComplement(root, x, min, max);
    propagate();
  }

  private void propagate() {
    if (!store.consistency()) {
      throw Store.failException;
    }
  }
}
