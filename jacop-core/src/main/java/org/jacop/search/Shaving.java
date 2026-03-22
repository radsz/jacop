/*
 * Shaving.java
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

package org.jacop.search;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import lombok.Setter;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XneqC;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Defines functionality of shaving. Plugin in this object to search to change your depth first
 * search to a search with shaving capabilities.
 *
 * <p>Shaving
 *
 * <p>Each search level stores the variable value pairs which were shaved at a given level.
 *
 * <p>Shaving speculation.
 *
 * <p>The right child is using all the shavable pairs from the subtree rooted at the sibling of the
 * current search node. If shaving fails then it is recorded in non shavable.
 *
 * <p>Not-shavable speculation
 *
 * <p>Every time a variable value pair is being schedule for shavability check then it is checked if
 * that pair was not already checked for shavability before with a negative results. If so, then
 * check is not performed but also entry in not-shavable is removed.
 *
 * <p>If variable value pair proofs to be not shavable then this variable value pair is recorded
 * into Not-shavable speculation.
 *
 * <p>Quick shave - upon exiting any subtree the variable value pair which was choosen at the root
 * of that subtree is recorded as shavable variable value pair.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@SuppressWarnings("unchecked")
public class Shaving<T extends IntVar> implements ExitChildListener<T>, ConsistencyListener {

  /** It specifies if only the last failed constraint is allowed to suggest shaving values. */
  public final boolean onlyFailedConstraint = false;

  /**
   * It specifies if only variables in the scope of the last failed constraint are allowed to be
   * used in shaving attempts.
   */
  public final boolean onlyIntVarsOfFailedConstraint = false;

  /** It stores the variables of the last failed constraints. */
  public final HashSet<IntVar> varsOfFailedConstraint = new HashSet<>();

  /** It contains list of constraints which suggest shaving explorations. */
  final List<Constraint> shavingConstraints = new ArrayList<>();

  final boolean leftChildShaving = true;
  final List<Map<IntVar, LinkedHashSet<Integer>>> shavable = new ArrayList<>();
  final Map<IntVar, LinkedHashSet<Integer>> notShavable = Var.createEmptyPositioning();

  /**
   * It specifies if the quickShave approach should be also used. Quickshave uses variable-value
   * pairs which lead to wrong decisions as shaving values higher in the search tree (until the
   * first time shaving attempt for this value fails).
   */
  public boolean quickShave;

  /** It stores number of successful shaving attempts. */
  public int successes;

  /** It stores number of failed shaving attempts. */
  public int failures;

  /** It specifies if the search is in the left child. */
  boolean leftChild = true;

  /**
   * It specifies current store, so shaving can obtained information about recent failed constraint.
   */
  @Setter Store store;

  Constraint recentlyFailedConstraint;
  boolean rightChild;
  boolean wrongDecisionEncountered;
  private ExitChildListener<T>[] exitChildListeners;
  private ConsistencyListener[] consistencyListeners;
  private boolean leftChildWrongDecision;
  private int depth;

  /** {@inheritDoc} */
  public boolean leftChild(IntVar v, int value, boolean status) {

    leftChild = false;
    leftChildWrongDecision = true;
    depth--;

    return true;
  }

  /** {@inheritDoc} */
  public boolean leftChild(PrimitiveConstraint choice, boolean status) {

    leftChild = false;
    leftChildWrongDecision = true;
    depth--;
    return true;
  }

  /** {@inheritDoc} */
  public void rightChild(IntVar v, int value, boolean status) {

    leftChild = false;

    if (!status && quickShave && leftChildWrongDecision) {

      int position = shavable.size() - 1;

      if (position > depth) {
        position = depth - 1;
      }

      if (position < 0) {
        position = 0;
      }

      Map<IntVar, LinkedHashSet<Integer>> current = shavable.get(position);
      LinkedHashSet<Integer> shaveVarList = current.computeIfAbsent(v, _ -> new LinkedHashSet<>());

      shaveVarList.add(value);
    }

    depth--;
    leftChildWrongDecision = false;
  }

  /** {@inheritDoc} */
  public void rightChild(PrimitiveConstraint choice, boolean status) {
    leftChild = false;
    depth--;
    leftChildWrongDecision = false;
  }

  public void setChildrenListeners(ConsistencyListener[] children) {
    consistencyListeners = children;
  }

  public void setChildrenListeners(ExitChildListener<T>[] children) {

    exitChildListeners = children;
  }

  /**
   * Sets a single consistency listener as the child listener.
   *
   * @param child the consistency listener to set.
   */
  public void setChildrenListeners(ConsistencyListener child) {
    consistencyListeners = new ConsistencyListener[1];
    consistencyListeners[0] = child;
  }

  /**
   * Sets a single exit child listener as the child listener.
   *
   * @param child the exit child listener to set.
   */
  public void setChildrenListeners(ExitChildListener<T> child) {
    exitChildListeners = new ExitChildListener[1];
    exitChildListeners[0] = child;
  }

  /**
   * Executes shaving logic after consistency check. Attempts to shave variable-value pairs.
   *
   * @param consistent whether the store is consistent after propagation.
   * @return true if the store remains consistent after shaving, false otherwise.
   */
  public boolean executeAfterConsistency(boolean consistent) {

    if (!consistent) {
      recentlyFailedConstraint = store.recentlyFailedConstraint;
      depth++;
      return false;
    }

    Map<IntVar, LinkedHashSet<Integer>> shavableCurrent = Var.createEmptyPositioning();

    if (!processShavableNeighbours(shavableCurrent)) {
      return false;
    }

    while (!shavable.isEmpty() && shavable.size() != depth) {
      shavable.removeLast();
    }

    depth++;
    shavable.add(shavableCurrent);

    if ((!leftChildShaving || leftChild) && !processShavingConstraints(shavableCurrent)) {
      return false;
    }

    leftChild = true;
    return true;
  }

  /** Returns true if store became inconsistent. */
  private boolean processShavablePair(
      Map<IntVar, LinkedHashSet<Integer>> shavableCurrent,
      Map<IntVar, LinkedHashSet<Integer>> notShavable,
      IntVar shaveVar,
      Integer shaveVal) {
    boolean shavablePair = checkIfShavable(shaveVar, shaveVal);
    if (shavablePair) {
      LinkedHashSet<Integer> shaveVarList =
          shavableCurrent.computeIfAbsent(shaveVar, _ -> new LinkedHashSet<>());
      shaveVarList.add(shaveVal);
      store.impose(new XneqC(shaveVar, shaveVal));
      return !store.consistency();
    }
    LinkedHashSet<Integer> notShaveVarList =
        notShavable.computeIfAbsent(shaveVar, _ -> new LinkedHashSet<>());
    notShaveVarList.add(shaveVal);
    return false;
  }

  /**
   * Processes shavable neighbours from previous levels. Returns false if store became inconsistent.
   */
  private boolean processShavableNeighbours(Map<IntVar, LinkedHashSet<Integer>> shavableCurrent) {
    int last = shavable.size();
    int current = depth;

    while (last > current) {
      Map<IntVar, LinkedHashSet<Integer>> shavableNeighbour = shavable.get(current);

      for (Map.Entry<IntVar, LinkedHashSet<Integer>> entry : shavableNeighbour.entrySet()) {
        IntVar shaveVar = entry.getKey();
        LinkedHashSet<Integer> list = entry.getValue();

        for (Integer shaveVal : list) {
          if (!shaveVar.domain.contains(shaveVal) || shaveVar.singleton()) {
            continue;
          }
          if (processShavablePair(shavableCurrent, notShavable, shaveVar, shaveVal)) {
            depth++;
            return false;
          }
        }
      }
      current++;
    }
    return true;
  }

  /** Returns true if store became inconsistent. */
  private boolean processShavingConstraint(
      Map<IntVar, LinkedHashSet<Integer>> shavableCurrent, IntVar shaveVar, int shaveVal) {
    LinkedHashSet<Integer> notShavableListShaveVar = notShavable.get(shaveVar);
    if (notShavableListShaveVar != null && notShavableListShaveVar.remove(shaveVal)) {
      return false;
    }
    boolean shavablePair = checkIfShavable(shaveVar, shaveVal);
    if (shavablePair) {
      LinkedHashSet<Integer> shaveVarList =
          shavableCurrent.computeIfAbsent(shaveVar, _ -> new LinkedHashSet<>());
      shaveVarList.add(shaveVal);
      store.impose(new XneqC(shaveVar, shaveVal));
      return !store.consistency();
    }
    LinkedHashSet<Integer> notShaveVarList =
        notShavable.computeIfAbsent(shaveVar, _ -> new LinkedHashSet<>());
    notShaveVarList.add(shaveVal);
    return false;
  }

  /** Processes shaving constraints. Returns false if store became inconsistent. */
  private boolean processShavingConstraints(Map<IntVar, LinkedHashSet<Integer>> shavableCurrent) {
    for (Constraint g : shavingConstraints) {
      if (onlyFailedConstraint && recentlyFailedConstraint != g) {
        continue;
      }
      IntVar shaveVar = (T) g.getGuideVariable();
      if (shaveVar == null) {
        continue;
      }
      int shaveVal = g.getGuideValue();
      if (onlyIntVarsOfFailedConstraint && !varsOfFailedConstraint.contains(shaveVar)) {
        continue;
      }
      if (processShavingConstraint(shavableCurrent, shaveVar, shaveVal)) {
        return false;
      }
    }
    return true;
  }

  boolean checkIfShavable(IntVar v, Integer val) {

    if (ASSERTS_ENABLED && (!v.domain.contains(val) || v.domain.singleton())) {
      throw new IllegalStateException(
          String.valueOf("var " + v + "val " + val + " should not be checked for shavability"));
    }

    int depth = store.level;

    store.setLevel(++depth);

    v.domain.in(store.level, v, val, val);

    boolean shavable = !store.consistency();

    store.removeLevel(depth);
    store.setLevel(--depth);

    if (shavable) {
      successes++;
    } else {
      failures++;
    }

    return shavable;
  }

  /**
   * It adds shaving constraint to the list of constraints guiding shaving.
   *
   * @param c constraint which is added to the list of guiding constraints.
   */
  public void addShavingConstraint(Constraint c) {

    shavingConstraints.add(c);
  }
}
