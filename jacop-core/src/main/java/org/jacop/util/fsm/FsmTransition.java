/*
 * FsmTransition.java
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

import java.util.Set;
import org.jacop.core.IntDomain;

/**
 * Represents a transition in a finite state machine.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class FsmTransition {

  /** It specifies the domain associated with the transition. */
  public IntDomain domain;

  /** It specifies the successor state we arrive to after taking the transition. */
  public FsmState successor;

  /**
   * It constructs a finite machine state transition.
   *
   * @param domain the domain which triggers the transition.
   * @param state the successor state reached by a transition.
   */
  public FsmTransition(IntDomain domain, FsmState state) {
    this.domain = domain;
    this.successor = state;
  }

  /**
   * It performs a clone of a transition with copying the attributes too.
   *
   * @param states a list of states which have been already copied.
   * @return the transition clone.
   */
  public FsmTransition deepClone(Set<FsmState> states) {

    return new FsmTransition(domain, successor.deepClone(states));
  }

  @Override
  public int hashCode() {
    return successor.id;
  }

  @Override
  public boolean equals(Object o) {

    if (o == null) {
      return false;
    }

    if (o == this) {
      return true;
    }

    FsmTransition compareTo = (FsmTransition) o;

    return compareTo.successor.equals(successor) && compareTo.domain.eq(domain);
  }

  @Override
  public String toString() {
    return successor.toString() + "@" + domain.toString();
  }
}
