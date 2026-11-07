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
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.DomainCover;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

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
public class Among extends Constraint
    implements UsesQueueVariable, Stateful, SatisfiedPresent, Copyable<Among>, Explainable {

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
   * @param n number of possible variables equal to a value from Kset; it must not occur in list.
   */
  public Among(IntVar[] list, IntervalDomain kset, IntVar n) {

    checkInputForNullness(
        new String[] {"list", "kset", "n"}, list, new Object[] {kset}, new Object[] {n});
    checkInputForDuplication("list", list);
    if (Arrays.asList(list).contains(n)) {
      throw new IllegalArgumentException(
          "Constraint Among has variable n " + n + " also in list; use a copy of it");
    }

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
    logLevelAndConstraintIfDebug(store);

    int currentLb = lowerBorder.value();
    int currentUb = upperBorder.value();

    int[] borders = processVariableQueue(currentLb, currentUb);
    currentLb = borders[0];
    currentUb = borders[1];

    variableQueue.clear();

    logBordersIfDebug(currentLb, currentUb);

    if (currentLb > currentUb) {
      throw Store.failException;
    }

    updateDomainAndBorders(store, currentLb, currentUb);
    pruneWhenLbEqualsN(store, currentLb, currentUb);
    pruneWhenUbEqualsN(store, currentLb, currentUb);

    if (debugAll) {
      log.debug("{}", this);
    }
  }

  private void logLevelAndConstraintIfDebug(Store store) {
    if (debugAll) {
      log.debug("LEVEL : {}", store.level);
      log.debug("{}", this);
    }
  }

  private void logBordersIfDebug(int currentLb, int currentUb) {
    if (debugAll) {
      log.debug("lbS = {}", currentLb);
      log.debug("ubS = {}", currentUb);
      log.debug(" domain of N {} is in [ {}, {} ]", n.domain, currentLb, currentUb);
    }
  }

  private void updateDomainAndBorders(Store store, int currentLb, int currentUb) {
    n.domain.in(store.level, n, currentLb, currentUb);
    upperBorder.update(currentUb);
    lowerBorder.update(currentLb);
  }

  private int[] processVariableQueue(int currentLb, int currentUb) {
    int lb = currentLb;
    int ub = currentUb;
    for (IntVar v : variableQueue) {
      int posVar = position.get(v);
      if (posVar < lb || posVar >= ub) {
        continue;
      }
      if (kSet.contains(v.domain)) {
        if (posVar != lb) {
          list[posVar] = list[lb];
          list[lb] = v;
          position.put(v, lb);
          position.put(list[posVar], posVar);
        }
        lb++;
        v.removeConstraint(this);
      }
      if (!kSet.isIntersecting(v.domain)) {
        if (posVar != ub - 1) {
          list[posVar] = list[ub - 1];
          list[ub - 1] = v;
          position.put(v, ub - 1);
          position.put(list[posVar], posVar);
        }
        ub--;
        v.removeConstraint(this);
      }
    }
    return new int[] {lb, ub};
  }

  private void pruneWhenLbEqualsN(Store store, int currentLb, int currentUb) {
    if (currentLb != n.min() || !n.domain.singleton()) {
      return;
    }
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
    upperBorder.update(currentLb);
    if (debugAll) {
      log.debug("Simple Among is satisfied");
    }
  }

  private void pruneWhenUbEqualsN(Store store, int currentLb, int currentUb) {
    if (currentUb != n.min() || !n.domain.singleton()) {
      return;
    }
    for (int i = currentLb; i < currentUb; i++) {
      IntVar v = list[i];
      v.domain.in(store.level, v, kSet);
      v.removeConstraint(this);
    }
    lowerBorder.update(currentUb);
    if (debugAll) {
      log.debug("Simple Among is satisfied");
    }
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

  // whether x's domain just before position lies inside kSet (in) or outside it (!in); its reason
  // is added to out, which is left as it was when the answer is no
  private boolean side(AtomicTrail trail, IntVar x, int position, boolean in, EntryList out) {
    int lo = trail.minBefore(x, position);
    int hi = trail.maxBefore(x, position);
    if (in ? kSet.contains(lo, hi) : !kSet.isIntersecting(lo, hi)) {
      trail.addLowerBound(x, position, out);
      trail.addUpperBound(x, position, out);
      return true;
    }
    if (in ? !kSet.contains(lo) || !kSet.contains(hi) : kSet.contains(lo) || kSet.contains(hi)) {
      return false;
    }
    int mark = out.size();
    if (DomainCover.domain(trail, x, position, (v, o) -> kSet.contains(v) == in, out)) {
      return true;
    }
    out.truncate(mark);
    return false;
  }

  // adds the reasons of `count` variables of list other than skip that are inside kSet (in) or
  // outside it (!in) just before position; false when there are fewer
  private boolean sides(
      AtomicTrail trail, int position, IntVar skip, long count, boolean in, EntryList out) {
    int mark = out.size();
    long found = 0;
    for (int i = 0; i < list.length && found < count; i++) {
      if (list[i] != skip && side(trail, list[i], position, in, out)) {
        found++;
      }
    }
    if (found < count) {
      out.truncate(mark);
      return false;
    }
    return true;
  }

  /**
   * Explains by counting: n &gt;= c by c variables inside the set, n &lt;= c by all but c outside
   * it, and a variable pushed out of (into) the set by n &lt;= c (n &gt;= c) and c other variables
   * inside (all but c outside).
   */
  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (getClass() != Among.class) {
      return false;
    }
    IntVar y = trail.variable(entry);
    int kind = trail.kind(entry);
    if (y == n) {
      if (kind == AtomicTrail.NE) {
        return false;
      }
      int bound = trail.skippedBound(entry);
      boolean ge = kind == AtomicTrail.GE;
      int mark = out.size();
      trail.addSkippedHoles(entry, bound, out);
      boolean ok =
          ge
              ? sides(trail, entry, null, bound, true, out)
              : sides(trail, entry, null, (long) list.length - bound, false, out);
      if (!ok) {
        out.truncate(mark);
      }
      return ok;
    }
    int mark = out.size();
    // pushed out of the set: n <= c and c others inside
    int c = trail.maxBefore(n, entry);
    if (sides(trail, entry, y, c, true, out)) {
      int reasons = out.size();
      if (DomainCover.entry(trail, entry, (v, o) -> kSet.contains(v), out)) {
        trail.addUpperBound(n, entry, out);
        return true;
      }
      out.truncate(reasons);
    }
    out.truncate(mark);
    // pushed into the set: n >= c and all but c others outside
    c = trail.minBefore(n, entry);
    if (sides(trail, entry, y, (long) list.length - c, false, out)) {
      if (DomainCover.entry(trail, entry, (v, o) -> !kSet.contains(v), out)) {
        trail.addLowerBound(n, entry, out);
        return true;
      }
    }
    out.truncate(mark);
    return false;
  }

  /** A failure: more variables inside the set than n allows, or fewer that may be in it. */
  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (getClass() != Among.class) {
      return false;
    }
    int now = trail.size();
    int mark = out.size();
    long most = trail.maxBefore(n, now);
    if (sides(trail, now, null, most + 1, true, out)) {
      trail.addUpperBound(n, now, out);
      return true;
    }
    long least = trail.minBefore(n, now);
    if (sides(trail, now, null, list.length - least + 1, false, out)) {
      trail.addLowerBound(n, now, out);
      return true;
    }
    out.truncate(mark);
    return false;
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

  @Override
  public Among copy(VarMap map) {
    return new Among(map.get(list), kSet, map.get(n));
  }
}
