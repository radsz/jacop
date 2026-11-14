/*
 * FsmState.java
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

package org.jacop.util.fsm;

import java.util.HashSet;
import java.util.Set;
import lombok.EqualsAndHashCode;

/**
 * Represents a state in a finite state machine.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@EqualsAndHashCode(onlyExplicitlyIncluded = true)
public class FsmState {

  /** It specifies the list of transitions outgoing from this state. */
  public final Set<FsmTransition> transitions;

  /** Id of the state. There can be multiple copies of the same state with the same id. */
  @EqualsAndHashCode.Include public int id;

  /**
   * It constructs a Fsm state.
   *
   * @param transitions it specifies transition
   * @param id state id
   */
  public FsmState(HashSet<FsmTransition> transitions, int id) {
    this.transitions = transitions;
    this.id = id;
  }

  /** It creates a state with id equl to the number of instances FsmState created. */
  public FsmState() {
    this.id = Fsm.idNumber.incrementAndGet();
    transitions = new HashSet<>();
  }

  /**
   * It creates a state with an id as the id specified by a supplied state.
   *
   * @param a state from which id is taken while creating this state.
   */
  public FsmState(FsmState a) {
    this.id = a.id;
    transitions = new HashSet<>();
  }

  /**
   * Performing deep clone unless this state has already a state with the same id in the array of
   * states.
   *
   * @param states it contains the states which do not need to be created, only reused.
   * @return a deep clone of the current state.
   */
  public FsmState deepClone(Set<FsmState> states) {

    // replace by HashSet contains check.
    FsmState newFsm = null;
    for (FsmState s : states) {
      if (s.id == this.id) {
        newFsm = s;
      }
    }
    if (newFsm != null) {
      return newFsm;
    }

    newFsm = new FsmState(this);
    states.add(newFsm);
    for (FsmTransition t : this.transitions) {
      newFsm.transitions.add(t.deepClone(states));
    }
    return newFsm;
  }

  /**
   * It adds transition to the list of transitions from this state.
   *
   * @param transition the transition being added.
   */
  public void addTransition(FsmTransition transition) {
    transitions.add(transition);
  }

  @Override
  public String toString() {
    return "state_" + id;
  }
}
