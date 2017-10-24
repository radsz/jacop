/*
 * Sequence.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints;

import java.util.*;

import org.jacop.constraints.regular.Regular;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.util.fsm.FSM;
import org.jacop.util.fsm.FSMState;
import org.jacop.util.fsm.FSMTransition;

/**
 *
 * It constructs a Sequence constraint. The sequence constraint
 * establishes the following relationship: For a given list of 
 * variables (list) and the length of each sequence (q) it makes
 * sure that each subsequence of consecutive variables from the list
 * contains between min and max values from the given set.
 *
 * @author Radoslaw Szymanek and Polina Makeeva
 * @version 4.5
 */

public class Sequence extends DecomposedConstraint<Constraint> {

    IntervalDomain set;
    int min;
    int max;
    int q;
    IntVar[] list;
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
    public Sequence(IntVar[] list, IntervalDomain set, int q, int min, int max) {

        checkInputForNullness("list", list);
        checkInputForNullness("set", new Object[] {set});

        this.min = min;
        this.max = max;

        this.list = Arrays.copyOf(list, list.length);
        this.set = set.clone();
        this.q = q;
        
    }

    @Override public void imposeDecomposition(Store store) {

        if (constraints == null)
            constraints = decompose(store);

        for (Constraint c : constraints)
            store.impose(c, queueIndex);

    }

    /**
     * Preferred and default option of decomposing Sequence constraint.
     * @param sequence sequence constraint to be decomposed by regular.
     * @return a list of constraints that are used to decompose the sequence constraints.
     */
    public static List<Constraint> decomposeByRegular(Sequence sequence) {

        IntDomain setComplement = new IntervalDomain();
        for (IntVar var : sequence.list)
            setComplement.addDom(var.domain);
        setComplement = setComplement.subtract(sequence.set);

        FSM fsm = new FSM();

        fsm.initState = new FSMState();
        fsm.allStates.add(fsm.initState);

        Map<FSMState, Integer> mappingQuantity = new HashMap<FSMState, Integer>();
        Map<String, FSMState> mappingString = new HashMap<String, FSMState>();

        mappingQuantity.put(fsm.initState, 0);
        mappingString.put("", fsm.initState);

        for (int i = 0; i < sequence.q; i++) {
            Map<String, FSMState> mappingStringNext = new HashMap<String, FSMState>();

            for (Map.Entry<String, FSMState> entry : mappingString.entrySet()) {
                String stateString = entry.getKey();
                FSMState state = entry.getValue();

                if (mappingQuantity.get(state) < sequence.max) {
                    // transition 1 (within a set) is allowed
                    FSMState nextState = new FSMState();
                    state.addTransition(new FSMTransition(sequence.set, nextState));
                    mappingStringNext.put(stateString + "1", nextState);
                    mappingQuantity.put(nextState, mappingQuantity.get(state) + 1);
                }

                if (mappingQuantity.get(state) + (sequence.q - i) > sequence.min) {
                    // transition 0 (outside set) is allowed
                    FSMState nextState = new FSMState();
                    state.addTransition(new FSMTransition(setComplement, nextState));
                    mappingStringNext.put(stateString + "0", nextState);
                    mappingQuantity.put(nextState, mappingQuantity.get(state));
                }
            }

            fsm.allStates.addAll(mappingString.values());
            mappingString = mappingStringNext;

        }

        fsm.allStates.addAll(mappingString.values());
        fsm.finalStates.addAll(mappingString.values());

        for (Map.Entry<String, FSMState> entry : mappingString.entrySet()) {
            String description = entry.getKey();
            FSMState state = entry.getValue();

            String one = description.substring(1) + "1";

            FSMState predecessor = state;
            FSMState successor = mappingString.get(one);
            if (successor != null)
                predecessor.addTransition(new FSMTransition(sequence.set, successor));

            String zero = description.substring(1) + "0";
            successor = mappingString.get(zero);
            if (successor != null)
                predecessor.addTransition(new FSMTransition(setComplement, successor));
        }

        fsm.resize();

        List<Constraint> constraints = new ArrayList<Constraint>();
        constraints.add(new Regular(fsm, sequence.list));

        return constraints;

    }

    @Override public List<Constraint> decompose(Store store) {

        if (constraints == null) {
            constraints = decomposeByRegular(this);
        }

        return constraints;

    }


}
