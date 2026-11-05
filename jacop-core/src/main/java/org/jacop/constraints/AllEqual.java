/*
 * AllEqual.java
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
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.DomainCover;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;

/**
 * Constraints forall i != j: x[i] #= x[j].
 *
 * <p>Domain consistency is used.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class AllEqual extends PrimitiveConstraint
    implements Copyable<AllEqual>, PbEncodable, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies a left hand variable in equality constraint. */
  private final IntVar[] x;

  private final int n;

  private TimeStamp<Integer> position;

  /**
   * It constructs constraint x[i] = x[j].
   *
   * @param x variables x.
   */
  public AllEqual(IntVar[] x) {

    checkInputForNullness(new String[] {"x"}, new Object[] {x});

    numberId = idNumber.incrementAndGet();

    this.x = Arrays.copyOf(x, x.length);
    this.n = x.length;

    setScope(x);
  }

  @Override
  public void consistency(final Store store) {

    // bottom up
    for (int i = 1; i < n; i++) {

      // domain consistency
      x[i - 1].domain.in(store.level, x[i - 1], x[i].domain);

      x[i].domain.in(store.level, x[i], x[i - 1].domain);
    }

    // top down
    for (int i = n - 2; i >= 0; i--) {

      // domain consistency
      x[i + 1].domain.in(store.level, x[i], x[i].domain);

      x[i].domain.in(store.level, x[i], x[i + 1].domain);
    }
  }

  /**
   * Explains an atom of one variable by the others: a removed value is out of another variable, a
   * moved bound passed only values out of other variables (one variable's bound when it covers them
   * all).
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar v = trail.variable(entry);
    int kind = trail.kind(entry);
    if (kind != AtomicTrail.NE) {
      // a single other variable whose bound already passes the new one
      int b = trail.value(entry);
      for (IntVar y : x) {
        if (y != v
            && (kind == AtomicTrail.GE
                ? trail.minBefore(y, entry) >= b
                : trail.maxBefore(y, entry) <= b)) {
          if (kind == AtomicTrail.GE) {
            trail.addLowerBound(y, entry, out);
          } else {
            trail.addUpperBound(y, entry, out);
          }
          return true;
        }
      }
    }
    return DomainCover.entry(trail, entry, (u, o) -> excludedElsewhere(trail, v, u, entry, o), out);
  }

  /**
   * Explains a failure: the bounds that leave the largest minimum above the smallest maximum, or
   * every value between them out of some variable.
   */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (n < 2) {
      return false;
    }
    int position = trail.size();
    IntVar low = x[0];
    IntVar high = x[0];
    for (IntVar y : x) {
      if (trail.minBefore(y, position) > trail.minBefore(low, position)) {
        low = y;
      }
      if (trail.maxBefore(y, position) < trail.maxBefore(high, position)) {
        high = y;
      }
    }
    int lo = trail.minBefore(low, position);
    int hi = trail.maxBefore(high, position);
    trail.addLowerBound(low, position, out);
    trail.addUpperBound(high, position, out);
    final IntVar first = low;
    return lo > hi
        || DomainCover.range(
            trail,
            low,
            position,
            lo,
            hi,
            (u, o) -> excludedElsewhere(trail, first, u, position, o),
            out);
  }

  // whether some variable other than v excludes u before the position; its entry goes to out
  private boolean excludedElsewhere(
      AtomicTrail trail, IntVar v, int u, int position, EntryList out) {
    for (IntVar y : x) {
      if (y != v && trail.excludedBefore(y, u, position, out)) {
        return true;
      }
    }
    return false;
  }

  @Override
  public void include(Store store) {
    position = new TimeStamp<>(store, 0);
  }

  @Override
  public void notConsistency(final Store store) {

    // at most one variable is always all equal, so the negation cannot hold
    if (n <= 1) {
      throw Store.failException;
    }

    int start = position.value();

    for (int i = start; i < n; i++) {
      if (x[i].singleton()) {
        if (start == 0) {
          swap(start++, i);
        } else if (x[0].value() == x[i].value()) {
          swap(start++, i);
        } else {
          removeConstraint();
          return;
        }
      }
    }

    if (start == n - 1) {
      x[start].domain.inComplement(store.level, x[start], x[0].value());
    } else if (start == n) {
      throw Store.failException;
    }

    position.update(start);
  }

  private void swap(int i, int j) {
    if (i != j) {
      IntVar tmp = x[i];
      x[i] = x[j];
      x[j] = tmp;
    }
  }

  @Override
  public boolean satisfied() {

    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (!x[i].singleton() || !x[j].singleton() || x[i].value() != x[j].value()) {
          return false;
        }
      }
    }
    return true;
  }

  @Override
  public boolean notSatisfied() {

    // not all equal as soon as the domains have no common value; pairwise intersection is not
    // enough ({1, 3}, {2, 3}, {1, 2})
    if (n < 2) {
      return false;
    }
    int lo = x[0].min();
    int hi = x[0].max();
    for (int i = 1; i < n; i++) {
      lo = Math.max(lo, x[i].min());
      hi = Math.min(hi, x[i].max());
    }
    if (lo > hi) {
      return true;
    }
    IntDomain common = x[0].dom();
    for (int i = 1; i < n; i++) {
      common = common.intersect(x[i].dom());
      if (common.isEmpty()) {
        return true;
      }
    }
    return false;
  }

  @Override
  public int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public String toString() {
    return id() + " : AllEqual(" + Arrays.asList(x) + " )";
  }

  @Override
  public AllEqual copy(VarMap map) {
    return new AllEqual(map.get(x));
  }

  @Override
  public boolean encode(PbModel model) {
    return encodeImplied(model, "1", false);
  }

  /**
   * States x[0] = x[i] for each i, or for the negation a literal per i that x[0] and x[i] differ,
   * defined by two clauses per value, and a clause that one of them does.
   */
  @Override
  public boolean encodeImplied(PbModel model, String literal, boolean negated) {
    if (getClass() != AllEqual.class) {
      return false;
    }
    if ("0".equals(literal)) {
      return true;
    }
    if (!negated) {
      for (int i = 1; i < n; i++) {
        model.guarded(
            literal,
            new LinearForm(new IntVar[] {x[0], x[i]}, new long[] {1, -1}, 0, LinearForm.EQ));
      }
      return true;
    }
    String[] some = new String[n];
    some[0] = PbModel.not(literal);
    for (int i = 1; i < n; i++) {
      String differ = model.auxiliary();
      some[i] = differ;
      IntDomain other = model.domain(x[i]);
      for (ValueEnumeration e = model.domain(x[0]).valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        String same = model.equalTo(x[i], v);
        // differ is x[0] != x[i] both ways, so that a solution fixes it
        model.clause(differ, PbModel.not(model.equalTo(x[0], v)), same);
        if (other.contains(v)) {
          model.clause(PbModel.not(differ), PbModel.not(model.equalTo(x[0], v)), PbModel.not(same));
        }
      }
    }
    model.clause(some);
    return true;
  }
}
