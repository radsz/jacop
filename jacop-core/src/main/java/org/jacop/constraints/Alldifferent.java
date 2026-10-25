/*
 * Alldifferent.java
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
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.util.BipartiteGraphMatching;

/**
 * Alldifferent constraint assures that all FDVs has differnet values. It uses partial consistency
 * technique.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Alldifferent extends Constraint
    implements UsesQueueVariable, SatisfiedPresent, Copyable<Alldifferent> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies a list of variables which must take different values. */
  protected IntVar[] list;

  protected Map<IntVar, Integer> positionMapping;
  protected TimeStamp<Integer> grounded;
  LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<>();

  // Empty set swapped with variableQueue while grounded variables are processed, so no set is
  // allocated (and grown) per call.
  private LinkedHashSet<IntVar> spareVariableQueue = new LinkedHashSet<>();

  /** Values above this many per variable keep the check of the matching at fixed variables. */
  private static final int MATCHING_VALUES_PER_VARIABLE = 64;

  /*
   * A matching of the variables to distinct values, kept across calls and repaired when a matched
   * value is removed, so that the constraint fails as soon as the variables cannot all take
   * different values. matchedValue is indexed like list, owner by value - minValue. Domains only
   * grow on backtracking, so the matching stays valid without trailing; null when not kept.
   */
  private int[] matchedValue;

  private IntVar[] owner;
  private int minValue;
  private int[] visited;
  private int visitStamp;

  // variables changed since the last repair, and variables left without a value
  private IntVar[] changed = new IntVar[8];
  private int changedSize;
  private IntVar[] unmatched;
  private int unmatchedSize;

  /** Protected constructor for subclassing purposes. */
  protected Alldifferent() {}

  /**
   * It constructs the alldifferent constraint for the supplied variable.
   *
   * @param list variables which are constrained to take different values.
   */
  public Alldifferent(IntVar[] list) {

    checkInputForNullness("list", list);
    checkInputForDuplication("list", list);

    this.numberId = idNumber.incrementAndGet();
    this.list = Arrays.copyOf(list, list.length);
    setScope(this.list);
  }

  /**
   * It constructs the alldifferent constraint for the supplied variable.
   *
   * @param variables variables which are constrained to take different values.
   */
  public Alldifferent(List<? extends IntVar> variables) {
    this(variables.toArray(new IntVar[0]));
  }

  @Override
  public void consistency(Store store) {

    int groundPos = grounded.value();
    do {
      store.propagationHasOccurred = false;
      groundPos = processGroundedVariables(store, groundPos);
    } while (store.propagationHasOccurred);
    grounded.update(groundPos);

    checkMatchingExcept(store, groundPos);
  }

  /**
   * Processes grounded (singleton) variables to maintain consistency by removing their values from
   * all other variables. Variables are moved to the front of the list once grounded.
   *
   * @param store the constraint store
   * @param groundPos the current position marking the boundary between grounded and non-grounded
   *     variables
   * @return the updated position of the first non-grounded variable
   */
  protected int processGroundedVariables(Store store, int groundPos) {
    LinkedHashSet<IntVar> fdvs = variableQueue;
    variableQueue = spareVariableQueue;

    try {
      for (IntVar q : fdvs) {
        if (!q.singleton()) {
          continue;
        }
        int qPos = positionMapping.get(q);
        if (qPos > groundPos) {
          list[qPos] = list[groundPos];
          list[groundPos] = q;
          positionMapping.put(q, groundPos);
          positionMapping.put(list[qPos], qPos);
          if (matchedValue != null) {
            int value = matchedValue[qPos];
            matchedValue[qPos] = matchedValue[groundPos];
            matchedValue[groundPos] = value;
          }
          groundPos++;
        } else if (qPos == groundPos) {
          groundPos++;
        } else {
          continue;
        }
        removeValueFromOthersIfNotException(store, groundPos, q.min());
      }
    } finally {
      fdvs.clear();
      spareVariableQueue = fdvs;
    }
    return groundPos;
  }

  /**
   * Removes the given value from the domain of all variables from groundPos onward, unless it is an
   * exception value.
   */
  private void removeValueFromOthersIfNotException(Store store, int groundPos, int value) {
    if (isExceptionValue(value)) {
      return;
    }
    for (int i = groundPos; i < list.length; i++) {
      list[i].domain.inComplement(store.level, list[i], value);
    }
  }

  /**
   * Determines whether the given value is an exception value that should not be subject to the
   * alldifferent constraint. Subclasses override this to define exception sets.
   *
   * @param value the value to check
   * @return true if the value is an exception, false otherwise
   */
  protected boolean isExceptionValue(int value) {
    return false;
  }

  /**
   * Determines whether the given variable's domain intersects with the set of exception values.
   * Subclasses override this to define exception sets.
   *
   * @param v the variable to check
   * @return true if the variable may take an exception value, false otherwise
   */
  protected boolean hasExceptionValues(IntVar v) {
    return false;
  }

  /**
   * Performs a matching-based consistency check on non-exception variables. Collects all
   * non-grounded variables that cannot take exception values and verifies that a valid assignment
   * exists using bipartite matching.
   *
   * @param store the constraint store
   * @param groundPos the current position of the first non-grounded variable
   */
  protected void checkMatchingExcept(Store store, int groundPos) {
    if (matchedValue != null) {
      repairMatching();
      return;
    }
    ArrayList<IntVar> vars = new ArrayList<>();
    for (int i = groundPos; i < list.length; i++) {
      if (!hasExceptionValues(list[i])) {
        vars.add(list[i]);
      }
    }
    if (vars.size() > 2 && notSatisfiedByMatching(vars.toArray(new IntVar[0]))) {
      throw Store.failException;
    }
  }

  /**
   * Repairs the matching after domain changes: variables whose matched value was removed lose it,
   * and every variable without a value gets one by an augmenting path. Fails when one cannot.
   */
  private void repairMatching() {
    for (int k = 0; k < changedSize; k++) {
      IntVar v = changed[k];
      changed[k] = null;
      int pos = positionMapping.get(v);
      int value = matchedValue[pos];
      if (value != Integer.MIN_VALUE && !v.domain.contains(value)) {
        owner[value - minValue] = null;
        matchedValue[pos] = Integer.MIN_VALUE;
        unmatched[unmatchedSize++] = v;
      }
    }
    changedSize = 0;

    while (unmatchedSize > 0) {
      visitStamp++;
      if (!augment(unmatched[unmatchedSize - 1])) {
        throw Store.failException;
      }
      unmatched[--unmatchedSize] = null;
    }
  }

  /** Finds a value for v, moving the owners of its values along an augmenting path. */
  private boolean augment(IntVar v) {
    IntDomain dom = v.domain;
    int max = dom.max();
    // first a free value, then a path through the owners
    for (int value = dom.min(); ; value = dom.nextValue(value)) {
      if (owner[value - minValue] == null) {
        match(v, value);
        return true;
      }
      if (value == max) {
        break;
      }
    }
    for (int value = dom.min(); ; value = dom.nextValue(value)) {
      int index = value - minValue;
      if (visited[index] != visitStamp) {
        visited[index] = visitStamp;
        IntVar previous = owner[index];
        if (augment(previous)) {
          match(v, value);
          return true;
        }
      }
      if (value == max) {
        return false;
      }
    }
  }

  private void match(IntVar v, int value) {
    owner[value - minValue] = v;
    matchedValue[positionMapping.get(v)] = value;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    // a matching that is kept is checked after any change, otherwise only at fixed variables
    return matchedValue != null ? IntDomain.ANY : IntDomain.GROUND;
  }

  /**
   * Whether this constraint keeps a matching of its variables to check feasibility after every
   * domain change. Subclasses with their own matching check or propagation return false.
   *
   * @return true for the plain alldifferent constraint.
   */
  protected boolean keepsMatching() {
    return true;
  }

  @Override
  public boolean satisfied() {

    for (int i = grounded.value(); i < list.length; i++) {
      if (!list[i].singleton()) {
        return false;
      }
    }

    Set<Integer> values = new HashSet<>();

    for (IntVar aList : list) {
      int value = aList.value();
      if (!isExceptionValue(value) && !values.add(value)) {
        return false;
      }
    }

    return true;
  }

  /**
   * Performs a full consistency check to determine if the constraint is satisfied. Verifies that
   * all variable domains are pairwise non-intersecting.
   *
   * @param store the constraint store
   * @return true if all variable domains are disjoint, false otherwise
   */
  @SuppressWarnings("unused")
  private boolean satisfiedFullCheck(Store store) {

    int i = 0;

    IntervalDomain result = new IntervalDomain();

    while (i < list.length - 1) {

      if (list[i].domain.isIntersecting(result)) {
        return false;
      }

      result.addDom(list[i].domain);

      i++;
    }

    return true;
  }

  /**
   * Check whether the constraint is not satisfied based on bipartite graph matching. Variables that
   * can take an exception value are left out, as any number of them can take one.
   *
   * @return true if constraint is not satisfied
   */
  public boolean notSatisfied() {

    IntVar[] vars = Arrays.stream(list).filter(v -> !hasExceptionValues(v)).toArray(IntVar[]::new);

    Map<Integer, Integer> valueMap = new HashMap<>();
    int valueIndex = 0;

    int[][] adj = new int[vars.length + 1][];
    adj[0] = new int[0];

    for (int i = 0; i < vars.length; i++) {
      IntVar v = vars[i];

      adj[i + 1] = new int[v.dom().getSize()];
      int j = 0;
      for (ValueEnumeration e = v.dom().valueEnumeration(); e.hasMoreElements(); ) {
        int el = e.nextElement();
        Integer elIndex = valueMap.get(el);
        if (elIndex == null) {
          valueMap.put(el, valueIndex);
          adj[i + 1][j] = valueIndex + 1;
          valueIndex++;
        } else {
          adj[i + 1][j] = elIndex + 1;
        }
        j++;
      }
    }
    for (int i = 0; i < adj.length; i++) {
      log.debug("{}: {}", i, Arrays.toString(adj[i]));
    }
    // compute maximal value for count
    BipartiteGraphMatching matcher = new BipartiteGraphMatching(adj, vars.length, valueMap.size());
    int maxNumberDifferent = matcher.hopcroftKarp();

    return maxNumberDifferent < vars.length;
  }

  @Override
  public void impose(Store store) {

    positionMapping = Var.positionMapping(list, false, this.getClass());
    if (keepsMatching()) {
      initMatching();
    }
    super.impose(store);
    grounded = new TimeStamp<>(store, 0);
  }

  /** Allocates the matching when the values span a range small enough for arrays. */
  private void initMatching() {
    if (list.length == 0) {
      return;
    }
    long min = Long.MAX_VALUE;
    long max = Long.MIN_VALUE;
    for (IntVar v : list) {
      min = Math.min(min, v.min());
      max = Math.max(max, v.max());
    }
    long range = max - min + 1;
    if (range > (long) MATCHING_VALUES_PER_VARIABLE * list.length + 1024) {
      return;
    }
    minValue = (int) min;
    owner = new IntVar[(int) range];
    visited = new int[(int) range];
    matchedValue = new int[list.length];
    Arrays.fill(matchedValue, Integer.MIN_VALUE);
    unmatched = Arrays.copyOf(list, list.length);
    unmatchedSize = list.length;
  }

  @Override
  public void queueVariable(int level, Var v) {
    if (v.singleton()) {
      variableQueue.add((IntVar) v);
    }
    if (matchedValue != null) {
      if (changedSize == changed.length) {
        changed = Arrays.copyOf(changed, 2 * changedSize);
      }
      changed[changedSize++] = (IntVar) v;
    }
  }

  /**
   * Checks if the constraint is satisfied based on variable bounds. Verifies that variable domains
   * do not overlap based on their min/max values.
   *
   * @return true if all variable bounds are disjoint, false otherwise
   */
  @SuppressWarnings("unused")
  private boolean satisfiedBound() {
    boolean sat = true;
    int i = 0;
    while (sat && i < list.length) {
      IntDomain vDom = list[i].dom();
      int vMin = vDom.min();
      int vMax = vDom.max();
      int j = i + 1;
      while (sat && j < list.length) {
        IntDomain ljDom = list[j].dom();
        sat = vMin > ljDom.max() || vMax < ljDom.min();
        j++;
      }
      i++;
    }
    return sat;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : alldifferent([");
    appendArrayToString(result, list);
    result.append("])");

    return result.toString();
  }

  @Override
  public Alldifferent copy(VarMap map) {
    return new Alldifferent(map.get(list));
  }
}
