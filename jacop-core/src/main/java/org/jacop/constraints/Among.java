/*
 * Among.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2008 Polina Maakeva and Radoslaw Szymanek
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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;

/**
 * Among constraint in its simplest form. It establishes the following relation. The given number N
 * of X`s take values from the supplied set of values Kset.
 *
 * <p>This constraint implements a simple and polynomial algorithm to establish GAC as presented in
 * different research papers. There are number of improvements (iterative execution, optimization of
 * computational load upon backtracking) to improve the constraint further.
 *
 * @author Polina Makeeva and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Among extends Constraint implements UsesQueueVariable, Stateful, SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);
  private static final boolean DEBUG_ALL = false;
  private static boolean debugAll = DEBUG_ALL;

  /** It specifies the list of variables whose values are checked. */
  private final IntVar[] list;

  /**
   * It specifies a set of values which if assigned to a variable from a list makes variable
   * counted.
   */
  private final IntervalDomain kSet;

  /** It is a idNumber variable. */
  private final IntVar n;

  final LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<>();
  // number if x that belongs to K (Kset)
  // As search progress this time stamp can only increase
  // because if X was in between lbS and ubS than
  // it can have the between (x intersects S <> empty and x doesn't belong to
  // S) values being shrinked.
  private TimeStamp<Integer> lowerBorder;
  // number of x who may still intersect K (Kset)
  private TimeStamp<Integer> upperBorder;
  private Map<IntVar, Integer> position;

  /**
   * It constructs an Among constraint.
   *
   * @param list variables which are compared to Kset
   * @param kset set of integer values against which we check if variables are equal to.
   * @param n number of possible variables equal to a value from Kset.
   */
  public Among(IntVar[] list, IntervalDomain kset, IntVar n) {

    checkInputForNullness(new String[] {"list", "kset", "n"}, new Object[][] {list, {kset}, {n}});
    checkInputForDuplication("list", list);

    this.queueIndex = 1;
    numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    this.kSet = kset.copy();
    this.n = n;

    setScope(Stream.concat(Arrays.stream(list), Stream.of(n)));
  }

  /**
   * It constructs an Among constraint.
   *
   * @param list variables which are compared to Kset
   * @param kset set of integer values against which we check if variables are equal to.
   * @param n number of possible variables equal to a value from Kset.
   */
  public Among(List<? extends IntVar> list, IntervalDomain kset, IntVar n) {
    this(list.toArray(new IntVar[0]), kset, n);
  }

  @Override
  public void removeLevel(int level) {
    variableQueue.clear();
  }

  @Override
  public void consistency(Store store) {
    // ----------------------------------------------------------
    if (debugAll) {
      log.debug("LEVEL : {}", store.level);
      log.debug("{}", this);
    }
    // ----------------------------------------------------------

    int currentLb = lowerBorder.value();
    // Refer to the algorithm where ubS = n - |{ x | dom(x) intersect S =
    // empty set } |
    int currentUb = upperBorder.value();

    // For the variable that signaled the change of domain
    // Count those that entered lbS, or ubS
    for (IntVar v : variableQueue) {

      int posVar = position.get(v);

      if (posVar < currentLb || posVar > currentUb) {
        continue;
      }

      if (kSet.contains(v.domain)) {

        if (posVar != currentLb) {
          list[posVar] = list[currentLb];
          list[currentLb] = v;
          position.put(v, currentLb);
          position.put(list[posVar], posVar);
        }
        currentLb++;

        // If variable entered lb then it would stay there
        // and we can detach the constrain from it
        v.removeConstraint(this);
      }
      if (!kSet.isIntersecting(v.domain)) {

        if (posVar != currentUb) {
          list[posVar] = list[currentUb - 1];
          list[currentUb - 1] = v;
          position.put(v, currentUb - 1);
          position.put(list[posVar], posVar);
        }
        currentUb--;

        // If the variable entered not ub then it will stay there
        // and we can detach the constrain from it
        v.removeConstraint(this);
      }
    }

    variableQueue.clear();

    // ----------------------------------------------------------
    if (debugAll) {
      log.debug("lbS = {}", currentLb);
      log.debug("ubS = {}", currentUb);
      log.debug(" domain of N {} is in [ {}, {} ]", n.domain, currentLb, currentUb);
    }
    // ----------------------------------------------------------

    if (currentLb > currentUb) {
      throw Store.failException;
    }

    n.domain.in(store.level, n, currentLb, currentUb);

    // Just in case LB or UB have changed.
    upperBorder.update(currentUb);
    lowerBorder.update(currentLb);

    if (currentLb == n.min() && n.domain.singleton()) {
      // If the number of X that belong to S is equal to N.value than we
      // have to subtract
      // the K set from the rest of x that do not belong to S
      for (int i = currentLb; i < currentUb; i++) {
        IntVar v = list[i];
        if (!kSet.contains(v.domain)) {
          if (debugAll) {
            log.debug("lb >> The value before in of {}: {}", v.id, v.domain);
            log.debug("lb >> subtrack {}", kSet);
            log.debug("lb >> equals {}", v.domain.subtract(kSet));
          }
          v.domain.in(store.level, v, v.domain.subtract(kSet));
          v.removeConstraint(this);
          if (debugAll) {
            log.debug("lb >> The value after in of {}: {}", v.id, v.domain);
          }
        }
      }

      // since the constraint is satisfied UB is equal to LB.
      upperBorder.update(currentLb);

      // The constraint became satisfied
      if (debugAll) {
        log.debug("Simple Among is satisfied");
      }
    }

    if (currentUb == n.min() && n.domain.singleton()) {
      // If the number intersecting X is equal to desired number N than we
      // have
      // to intersect the domains of X with K set.
      for (int i = currentLb; i < currentUb; i++) {
        IntVar v = list[i];
        v.domain.in(store.level, v, kSet);
        v.removeConstraint(this);
      }

      // since the constraint is satisfied LB is equal to UB.
      lowerBorder.update(currentUb);

      // The constrain became satisfied
      if (debugAll) {
        log.debug("Simple Among is satisfied");
      }
    }

    if (debugAll) {
      log.debug("{}", this);
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void impose(Store store) {

    super.impose(store);

    this.lowerBorder = new TimeStamp<>(store, 0);
    this.upperBorder = new TimeStamp<>(store, list.length);

    position = Var.positionMapping(list, false, this.getClass());
  }

  @Override
  public void queueVariable(int level, Var v) {
    if (debugAll) {
      log.debug("Var {}{}", v, ((IntVar) v).recentDomainPruning());
    }

    if (v != n) {
      variableQueue.add((IntVar) v);
    }
  }

  @Override
  public boolean satisfied() {
    return Objects.equals(lowerBorder.value(), upperBorder.value())
        && n.min() == lowerBorder.value()
        && n.singleton();
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(": Among([");

    for (IntVar v : this.list) {
      result.append(v).append(" ");
    }

    result.append("], ").append(this.kSet).append(", ");
    result.append(n).append(")\n");

    return result.toString();
  }
}
