/*
 * Member.java
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
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;

/**
 * Member constraint implements the membership of element e on list x.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class Member extends PrimitiveConstraint implements Copyable<Member> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies a list of variables being summed. */
  final IntVar[] x;

  /** It specifies variable for the overall sum. */
  final IntVar e;

  /** It specifies the number of variables on the list. */
  final int l;

  /*
   * Defines first position of the variable that might equal e
   */
  private TimeStamp<Integer> position;

  /* Whether e is itself on the list, which makes the constraint always true; null until checked. */
  private Boolean aliased;

  /**
   * Constructs a Member constraint to check if a variable equals one in the list.
   *
   * @param list list of variables.
   * @param e variable to be checkd on the list.
   */
  public Member(IntVar[] list, IntVar e) {

    checkInputForNullness(new String[] {"list", "e"}, list, new Object[] {e});

    this.e = e;

    x = Arrays.copyOf(list, list.length);
    numberId = idNumber.incrementAndGet();

    this.l = x.length;

    queueIndex = 1;

    setScope(Stream.concat(Arrays.stream(x), Stream.of(this.e)));
  }

  /**
   * It constructs the constraint Member.
   *
   * @param list list of variables.
   * @param e variable to be checkd on the list.
   */
  public Member(List<? extends IntVar> list, IntVar e) {
    this(list.toArray(IntVar[]::new), e);
  }

  @Override
  public void consistency(Store store) {

    int start = position.value();

    if (e.singleton()) {
      consistencyGround(store, start, e.value());
      return;
    }

    IntDomain d = new IntervalDomain();
    int numberGround = 0;
    for (int i = start; i < l; i++) {

      if (!x[i].domain.isIntersecting(e.domain)) {
        swap(start, i);
        start++;
      } else {
        if (x[i].singleton()) {
          numberGround++;
        }
        d.unionAdapt(x[i].domain);
      }
    }

    if (start == l) {
      throw Store.failException;
    }

    e.domain.in(store.level, e, d);

    if (l - start == numberGround && !e.singleton()) {
      removeConstraint();
      return;
    }

    handleSingleRemainingVariable(store, start);

    position.update(start);
  }

  /** Consistency for a fixed e: the same rules as the general case without building the union. */
  private void consistencyGround(Store store, int start, int value) {
    for (int i = start; i < l; i++) {
      if (!x[i].domain.contains(value)) {
        swap(start, i);
        start++;
      } else if (x[i].singleton()) {
        removeConstraint();
        return;
      }
    }

    if (start == l) {
      throw Store.failException;
    }

    handleSingleRemainingVariable(store, start);

    position.update(start);
  }

  @Override
  public void notConsistency(Store store) {

    if (aliased()) {
      throw Store.failException;
    }

    int start = position.value();

    do {

      store.propagationHasOccurred = false;

      boolean eGround = e.singleton();
      for (int i = start; i < l; i++) {
        if (eGround) {
          x[i].domain.inComplement(store.level, x[i], e.value());
        }

        if (x[i].singleton()) {
          e.domain.inComplement(store.level, e, x[i].value());
        }

        if (!x[i].domain.isIntersecting(e.domain)) {
          swap(start, i);
          start++;
        }
      }

      if (start == l) {
        removeConstraint();
      }

      handleSingleRemainingVariableNotConsistency(store, start);

    } while (store.propagationHasOccurred);

    position.update(start);
  }

  private void handleSingleRemainingVariable(Store store, int start) {
    if (start == l - 1) {
      x[l - 1].domain.in(store.level, x[l - 1], e.domain);
      e.domain.in(store.level, e, x[l - 1].domain);
    }
  }

  private void handleSingleRemainingVariableNotConsistency(Store store, int start) {
    if (start == l - 1) {
      if (e.singleton()) {
        x[l - 1].domain.inComplement(store.level, x[l - 1], e.value());
      } else if (x[l - 1].singleton()) {
        e.domain.inComplement(store.level, e, x[l - 1].value());
      }
    }
  }

  private void swap(int i, int j) {
    if (i != j) {
      IntVar tmp = x[i];
      x[i] = x[j];
      x[j] = tmp;
    }
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void include(Store store) {
    // Wrappers include their nested constraints again whenever they are imposed, also during
    // search. Keep a stamp that still has a value, as one created at a search level loses it on
    // backtracking while the constraint may still be used below that level.
    if (position == null || position.pointer4Last < 0) {
      position = new TimeStamp<>(store, moveRepeatedVariablesToFront());
    }
  }

  /**
   * Moves repeated list variables to the front, before the first position that can still equal e,
   * so that each variable is a candidate only once and the last candidate is recognised.
   *
   * @return the number of repeated variables moved.
   */
  private int moveRepeatedVariablesToFront() {
    Set<IntVar> seen = new HashSet<>();
    int start = 0;
    for (int i = 0; i < l; i++) {
      if (!seen.add(x[i])) {
        swap(start, i);
        start++;
      }
    }
    return start;
  }

  /** Whether e is itself on the list; member is then always true. */
  private boolean aliased() {
    if (aliased == null) {
      aliased = Arrays.asList(x).contains(e);
    }
    return aliased;
  }

  @Override
  public void impose(Store store) {

    if (x == null) {
      return;
    }

    super.impose(store);
  }

  @Override
  public boolean satisfied() {

    if (aliased()) {
      return true;
    }

    if (e.singleton()) {
      for (int i = 0; i < l; i++) {
        if (x[i].singleton() && x[i].value() == e.value()) {
          return true;
        }
      }
      return false;
    }

    // Entailed also when every value of e is taken by a fixed list variable. The bounds of e are
    // checked first, as they rule out most cases cheaply.
    if (!fixedTo(e.min()) || !fixedTo(e.max())) {
      return false;
    }
    for (ValueEnumeration values = e.domain.valueEnumeration(); values.hasMoreElements(); ) {
      if (!fixedTo(values.nextElement())) {
        return false;
      }
    }
    return true;
  }

  private boolean fixedTo(int value) {
    for (int i = 0; i < l; i++) {
      if (x[i].singleton(value)) {
        return true;
      }
    }
    return false;
  }

  @Override
  public boolean notSatisfied() {
    if (aliased()) {
      return false;
    }
    for (int i = 0; i < l; i++) {
      if (x[i].domain.isIntersecting(e.domain)) {
        return false;
      }
    }
    return true;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : Member([");

    for (int i = 0; i < l; i++) {
      result.append(x[i]);
      if (i < l - 1) {
        result.append(", ");
      }
    }
    result.append("], ");

    result.append(e).append(" )");

    return result.toString();
  }

  @Override
  public Member copy(VarMap map) {
    return new Member(map.get(x), map.get(e));
  }
}
