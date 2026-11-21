/*
 * OrBoolWatched.java
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

import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Reified disjunction of 0/1 variables with watched literals: result = (x[0] or ... or x[n-1]), or,
 * when negated, result = not (x[0] or ... or x[n-1]), which is result = (x[0] + ... + x[n-1] = 0).
 *
 * <p>It does what {@link OrBoolVector} and {@code Not(OrBoolVector)} do, but it is not woken by
 * every variable that gets fixed. Every variable is watched for value 1 ({@link Store#watchValue}),
 * which sets the result at once, and two variables that are not 0 are watched for value 0, as the
 * two watched literals of a clause in a SAT solver. A variable fixed to 0 that is not one of the
 * two does not reach the constraint at all. When one of the two gets 0, another variable that is
 * not 0 takes its place; when none is left, the disjunction is false, and when only one is left and
 * the disjunction must hold, that variable is set to 1. The result is an ordinary model variable of
 * the constraint. For the variable selections and neighbourhoods that read the constraints of a
 * variable (dom/wdeg, failure counts, static degree, LNS) the constraint counts as attached to
 * every variable of the disjunction ({@link #countsValueWatch(int, int)}), as {@code
 * Not(OrBoolVector)} is, and it uses the same queue, so that the same constraint finds a failure.
 *
 * <p>The watches are kept on backtracking, as in SAT solvers: a variable that was not 0 deeper in
 * the search is not 0 higher up either. The constraint must therefore be imposed at level 0. It has
 * no explanation for lazy clause generation; use {@link OrBoolVector} there.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class OrBoolWatched extends Constraint implements SatisfiedPresent, Copyable<OrBoolWatched> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The variables of the disjunction, without repetitions. */
  public final IntVar[] list;

  /** The variable reifying the disjunction, or its negation when {@link #negated}. */
  public final IntVar result;

  /** True if result is the negation of the disjunction. */
  public final boolean negated;

  /** Positions of the two variables watched for value 0; -1 when there is no such variable. */
  private int watch1 = -1;

  private int watch2 = -1;

  /** The variables that have a watch for value 0, which stays for good once added. */
  private boolean[] watchingZero;

  /** Position of the last variable reported fixed to 1, or -1. */
  private int one = -1;

  /** Set when the constraint has been satisfied at level 0, so that the watches are ignored. */
  private boolean rootEntailed;

  /** Where the search for a replacement watch starts, to spread the scans over the variables. */
  private int scanStart;

  /**
   * It constructs the constraint.
   *
   * @param list the variables of the disjunction, with domains within 0..1.
   * @param result the variable equal to the disjunction, or to its negation.
   * @param negated true if result is the negation of the disjunction.
   */
  public OrBoolWatched(IntVar[] list, IntVar result, boolean negated) {

    checkInputForNullness("list", list);
    checkInputForNullness("result", new Object[] {result});

    numberId = idNumber.incrementAndGet();
    this.list = unique(list);
    this.result = result;
    this.negated = negated;
    // the queue of OrBoolVector, so that failures are found, and weighted, by the same constraints
    queueIndex = this.list.length > 2 ? 1 : 0;
    for (IntVar v : this.list) {
      if (v.min() < 0 || v.max() > 1) {
        throw new IllegalArgumentException(
            "Variable " + v + " of OrBoolWatched must have a domain within 0..1.");
      }
    }
    if (result.min() < 0 || result.max() > 1) {
      throw new IllegalArgumentException(
          "Variable " + result + " of OrBoolWatched must have a domain within 0..1.");
    }
    setScope(Stream.concat(Arrays.stream(this.list), Stream.of(result)));
  }

  private static IntVar[] unique(IntVar[] list) {
    Map<IntVar, Boolean> seen = new IdentityHashMap<>();
    return Arrays.stream(list)
        .filter(v -> seen.put(v, Boolean.TRUE) == null)
        .toArray(IntVar[]::new);
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  /**
   * Imposes the constraint. Only the result is a model variable of the constraint; the variables of
   * the disjunction are watched for values. The constraint must be imposed at level 0.
   *
   * @param store the constraint store in which the constraint is imposed.
   */
  @Override
  public void impose(Store store) {
    if (store.level != 0) {
      throw new IllegalStateException("OrBoolWatched must be imposed at level 0");
    }
    watchingZero = new boolean[list.length];
    for (int i = 0; i < list.length; i++) {
      // the variable selections see the constraint on the variable as if it were attached: the
      // watch of value 1 makes it one of the variable (countsValueWatch), and the degree counts it
      list[i].adjustDegree(1);
      if (!list[i].singleton()) {
        store.watchValue(list[i], 1, this, 2 * i + 1);
      }
    }
    result.putModelConstraint(this, IntDomain.GROUND);
    store.addChanged(this);
    store.countConstraint();
  }

  @Override
  public boolean valueWatchFired(int level, Var v, int tag) {
    if (rootEntailed) {
      return false;
    }
    int i = tag >> 1;
    if ((tag & 1) == 1) {
      one = i;
      return true;
    }
    // a watch left over from an earlier choice of the two watched variables
    return i == watch1 || i == watch2;
  }

  @Override
  public boolean countsValueWatch(int value, int tag) {
    return value == 1 && !rootEntailed;
  }

  /** The value of result that makes the disjunction hold. */
  private int resultWhenTrue() {
    return negated ? 0 : 1;
  }

  @Override
  public void consistency(Store store) {

    // a variable fixed to 1 makes the disjunction true
    if (one >= 0 && list[one].min() == 1) {
      setDisjunction(store, true);
      return;
    }

    int r = result.singleton() ? (result.value() == resultWhenTrue() ? 1 : 0) : -1;
    if (r == 0) {
      for (IntVar v : list) {
        v.domain.inValue(store.level, v, 0);
      }
      entailed(store);
      return;
    }

    // A watch that got 0 without a replacement keeps its position: it got 0 at this level, since
    // the watch woke the constraint then, so it is not 0 again after backtracking below it.
    if (!alive(watch1)) {
      int w = findWatch(store, watch2);
      if (w == -2) {
        return;
      }
      if (w >= 0) {
        watch1 = w;
      }
    }
    if (!alive(watch2)) {
      int w = findWatch(store, watch1);
      if (w == -2) {
        return;
      }
      if (w >= 0) {
        watch2 = w;
      }
    }
    boolean alive1 = alive(watch1);
    boolean alive2 = alive(watch2);
    if (!alive1 && !alive2) {
      setDisjunction(store, false);
    } else if (r == 1 && alive1 != alive2) {
      IntVar last = list[alive1 ? watch1 : watch2];
      last.domain.inValue(store.level, last, 1);
      entailed(store);
    }
  }

  private boolean alive(int i) {
    return i >= 0 && list[i].max() == 1;
  }

  /**
   * Finds a variable that is not 0, other than the given one, and watches it for value 0.
   *
   * @return its position, -1 if there is none, or -2 if a variable is 1 and the disjunction has
   *     been set true.
   */
  private int findWatch(Store store, int other) {
    int n = list.length;
    for (int k = 0; k < n; k++) {
      int i = scanStart + k;
      if (i >= n) {
        i -= n;
      }
      if (i == other) {
        continue;
      }
      IntVar v = list[i];
      if (v.min() == 1) {
        setDisjunction(store, true);
        return -2;
      }
      if (v.max() == 1) {
        scanStart = i + 1 < n ? i + 1 : 0;
        if (!watchingZero[i]) {
          watchingZero[i] = true;
          store.watchValue(v, 0, this, 2 * i);
        }
        return i;
      }
    }
    return -1;
  }

  private void setDisjunction(Store store, boolean value) {
    int v = value == negated ? 0 : 1;
    result.domain.inValue(store.level, result, v);
    entailed(store);
  }

  private void entailed(Store store) {
    if (store.level == 0) {
      rootEntailed = true;
    }
    removeConstraint();
  }

  @Override
  public boolean satisfied() {
    if (!result.singleton()) {
      return false;
    }
    boolean any = false;
    for (IntVar v : list) {
      if (!v.singleton()) {
        return false;
      }
      any |= v.value() == 1;
    }
    return any == (result.value() == resultWhenTrue());
  }

  @Override
  public OrBoolWatched copy(VarMap map) {
    return new OrBoolWatched(map.get(list), map.get(result), negated);
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder(id());
    s.append(negated ? " : norBoolWatched([ " : " : orBoolWatched([ ");
    for (int i = 0; i < list.length; i++) {
      s.append(list[i]);
      if (i < list.length - 1) {
        s.append(", ");
      }
    }
    return s.append("], ").append(result).append(")").toString();
  }
}
