/*
 * Sequence.java
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
import java.util.List;
import java.util.Map;
import lombok.Builder;
import org.jacop.constraints.regular.Regular;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;

/**
 * It constructs a Sequence constraint. The sequence constraint establishes the following
 * relationship: For a given list of variables (list) and the length of each sequence (q) it makes
 * sure that each subsequence of consecutive variables from the list contains between min and max
 * values from the given set.
 *
 * <p>It is decomposed into the domain consistent propagator {@link AmongSeq}, or, when min = max,
 * into the period decomposition {@link #decomposeByPeriod(Sequence, Store)}. Both accept repeated
 * variables in the list. {@link #decomposeByRegular(Sequence)} is kept for reference.
 *
 * @author Radoslaw Szymanek and Polina Makeeva
 * @version 5.0
 */
public class Sequence extends DecomposedConstraint<Constraint> {

  final IntervalDomain set;
  final int min;
  final int max;
  final int q;
  final IntVar[] list;
  List<Constraint> constraints;

  /**
   * It creates a Sequence constraint.
   *
   * @param list variables which assignment is constrained by Sequence constraint.
   * @param set set of values which occurrence is counted within each sequence.
   * @param q the length of the sequence
   * @param min the minimal occurrences of values from set within a sequence.
   * @param max the maximal occurrences of values from set within a sequence.
   */
  @Builder
  public Sequence(IntVar[] list, IntervalDomain set, int q, int min, int max) {

    checkInputForNullness("list", list);
    checkInputForNullness("set", new Object[] {set});
    if (q < 1) {
      throw new IllegalArgumentException(
          "Constraint Sequence needs a subsequence length q >= 1, not " + q + ".");
    }

    this.min = min;
    this.max = max;

    this.list = Arrays.copyOf(list, list.length);
    this.set = set.copy();
    this.q = q;
  }

  /**
   * It decomposes Sequence into one Regular constraint. Its automaton has about 2^q states, and
   * Regular does not accept repeated variables.
   *
   * @param sequence sequence constraint to be decomposed by regular.
   * @return a list of constraints that are used to decompose the sequence constraints.
   */
  public static List<Constraint> decomposeByRegular(Sequence sequence) {

    IntDomain setComplement = new IntervalDomain();
    for (IntVar v : sequence.list) {
      setComplement.addDom(v.domain);
    }
    setComplement = setComplement.subtract(sequence.set);

    Fsm fsm = new Fsm();

    fsm.initState = new FsmState();
    fsm.allStates.add(fsm.initState);

    Map<FsmState, Integer> mappingQuantity = new HashMap<>();
    Map<String, FsmState> mappingString = new HashMap<>();

    mappingQuantity.put(fsm.initState, 0);
    mappingString.put("", fsm.initState);

    for (int i = 0; i < sequence.q; i++) {
      Map<String, FsmState> mappingStringNext = new HashMap<>();

      for (Map.Entry<String, FsmState> entry : mappingString.entrySet()) {
        String stateString = entry.getKey();
        FsmState state = entry.getValue();

        int count = mappingQuantity.get(state);
        // a transition is allowed if the count after it is at most max and the count can still
        // reach min in the q - i - 1 remaining positions of the first window
        if (count + 1 <= sequence.max && count + sequence.q - i >= sequence.min) {
          // transition 1 (within a set) is allowed
          FsmState nextState = new FsmState();
          state.addTransition(new FsmTransition(sequence.set, nextState));
          mappingStringNext.put(stateString + "1", nextState);
          mappingQuantity.put(nextState, count + 1);
        }

        if (count <= sequence.max && count + sequence.q - i - 1 >= sequence.min) {
          // transition 0 (outside set) is allowed
          FsmState nextState = new FsmState();
          state.addTransition(new FsmTransition(setComplement, nextState));
          mappingStringNext.put(stateString + "0", nextState);
          mappingQuantity.put(nextState, count);
        }
      }

      fsm.allStates.addAll(mappingString.values());
      mappingString = mappingStringNext;
    }

    fsm.allStates.addAll(mappingString.values());
    fsm.finalStates.addAll(mappingString.values());

    for (Map.Entry<String, FsmState> entry : mappingString.entrySet()) {
      String description = entry.getKey();
      FsmState state = entry.getValue();

      String one = description.substring(1) + "1";

      FsmState successor = mappingString.get(one);
      if (successor != null) {
        state.addTransition(new FsmTransition(sequence.set, successor));
      }

      String zero = description.substring(1) + "0";
      successor = mappingString.get(zero);
      if (successor != null) {
        state.addTransition(new FsmTransition(setComplement, successor));
      }
    }

    fsm.resize();

    List<Constraint> constraints = new ArrayList<>();
    constraints.add(new Regular(fsm, sequence.list));

    return constraints;
  }

  /**
   * It decomposes a Sequence constraint with min = max into reified memberships channelled to q
   * Boolean variables. Two consecutive windows share q - 1 variables and hold the same number of
   * values from the set, so list[i] is in the set exactly when list[i + q] is. The constraint
   * therefore holds if and only if list[i] is in the set when b[i mod q] = 1 and the sum of b
   * equals min. The decomposition has no cycles, so it is domain consistent when the list has no
   * repeated variables, and each change costs constant time instead of a pass of Regular.
   *
   * @param sequence sequence constraint with min = max, 0 &lt;= min &lt;= q and q &lt;= list
   *     length.
   * @param store the constraint store in which the Boolean variables are created.
   * @return a list of constraints that are used to decompose the sequence constraint.
   */
  public static List<Constraint> decomposeByPeriod(Sequence sequence, Store store) {

    BooleanVar[] inSet = new BooleanVar[sequence.q];
    for (int j = 0; j < inSet.length; j++) {
      inSet[j] = new BooleanVar(store);
    }

    List<Constraint> constraints = new ArrayList<>();
    for (int i = 0; i < sequence.list.length; i++) {
      constraints.add(new Reified(new In(sequence.list[i], sequence.set), inSet[i % sequence.q]));
    }
    constraints.add(new SumBool(inSet, "==", new IntVar(store, sequence.min, sequence.min)));

    return constraints;
  }

  @Override
  public void imposeDecomposition(Store store) {

    if (constraints == null) {
      constraints = decompose(store);
    }

    for (Constraint c : constraints) {
      store.impose(c, queueIndex);
    }
  }

  @Override
  public List<Constraint> decompose(Store store) {

    if (constraints == null) {
      if (q > list.length) {
        // no subsequence of length q, so nothing to constrain
        constraints = new ArrayList<>();
      } else if (min == max && min >= 0 && min <= q) {
        constraints = decomposeByPeriod(this, store);
      } else {
        // domain consistent like decomposeByRegular, but its cost does not grow as 2^q
        constraints = new ArrayList<>();
        constraints.add(new AmongSeq(list, set, q, min, max));
      }
    }

    return constraints;
  }
}
