/*
 * SatChangesListener.java
 * <p>
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

package org.jacop.satwrapper;

import java.util.Arrays;
import java.util.BitSet;
import java.util.HashSet;
import java.util.Set;

import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.jasat.core.Core;
import org.jacop.jasat.modules.interfaces.AssertionListener;
import org.jacop.jasat.modules.interfaces.BackjumpListener;
import org.jacop.jasat.modules.interfaces.PropagateListener;
import org.jacop.satwrapper.translation.SatCPBridge;

/*
 * TODO: many efficiency improvements!!!
 */


/**
 * this class listens to changes in literals in SAT solver, and reminds
 * what changes this implies for CP variables
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */
public final class SatChangesListener implements AssertionListener, PropagateListener, BackjumpListener {

	/*
   * invariant: upperBounds.lenght == lowerBounds.length == excludedValues.length
	 */

    // the wrapper
    private SatWrapper wrapper;

    // the core of the SAT solver
    private Core core;

    // set of forbidden values for variables
    // (not BitSet because some values could be < 0)
    @SuppressWarnings("unchecked") private Set<Integer>[] excludedValues = new HashSet[40];
    //private IntSet[] excludedValues = new IntSet[5];

    // set of (true) literals representing 'x<=v' assertions on CP vars
    private Integer[] upperBounds = new Integer[40];

    // set of literals (false) representing 'x>v' assertions
    private Integer[] lowerBounds = new Integer[40];

    // set of variables to update
    private BitSet intVarsToUpdate = new BitSet();
    private Set<BooleanVar> booleanVarsToUpdate = new HashSet<BooleanVar>();

    /**
     * clears all sets, so that elements occurring in them later result only
     * from later events
     */
    public void clear() {
        assert lowerBounds.length == upperBounds.length;

        // TODO: optimize clear(), which is often called

        Arrays.fill(upperBounds, null);
        Arrays.fill(lowerBounds, null);
        Arrays.fill(excludedValues, null);

        intVarsToUpdate.clear();
        booleanVarsToUpdate.clear();
    }


    public void onPropagate(int literal, int clauseId) {
        if (wrapper.isVarLiteral(literal))
            onAssertion(literal);
    }


    public void onAssertion(int literal, int level) {
        if (wrapper.isVarLiteral(literal))
            onAssertion(literal);
    }

    /**
     * clear on backjump
     */
    public void onBackjump(int oldLevel, int newLevel) {
        clear();
    }

    public void onRestart(int oldLevel) {
        onBackjump(oldLevel, 0);
    }

    /**
     * this should be called every time a new boolean variable representing
     * a CP proposition is asserted, but preferably only once per variable, so
     * that it can later update the CP variables domains
     *
     * @param literal the boolean literal that has been asserted
     */
    private void onAssertion(int literal) {

        // only interested in literals representing assertions on CP
        // variables domains
        assert wrapper.isVarLiteral(literal);
        assert core.trail.isSet(Math.abs(literal));
        assert core.trail.values[Math.abs(literal)] == literal;

        // this propagation asserts something about CP variables, let
        // us find what exactly

        // what variable and value does it concern
        int cpValue = wrapper.boolVarToCpValue(literal);
        IntVar cpVar = wrapper.boolVarToCpVar(literal);
        SatCPBridge range = wrapper.boolVarToDomain(literal);

        if (BooleanVar.class.isInstance(cpVar)) {
            // boolean variable, only remember something happened
            @SuppressWarnings("unchecked") BooleanVar cpBoolVar = (BooleanVar) cpVar;
            booleanVarsToUpdate.add(cpBoolVar);
        } else {
            // remember that something happened;
            int cpVarIndex = cpVar.index;
            intVarsToUpdate.set(cpVarIndex);

            // is this the negation or the affirmation of some proposition ?
            boolean isTrue = literal > 0;

            if (range.isEqualityBoolVar(literal)) {
                // simple cases, equality propositions
                if (isTrue) {
                    // 'x=v', remember this by fixing the range
                    upperBounds[cpVarIndex] = cpValue;
                    lowerBounds[cpVarIndex] = cpValue;
                } else {
                    // 'x!=v', remember that this value is excluded
                    if (excludedValues[cpVarIndex] == null)
                        excludedValues[cpVarIndex] = new HashSet<Integer>();
                    excludedValues[cpVarIndex].add(cpValue);
                }
            } else {
                // check impacts on ranges
                if (isTrue) {
                    // 'x<=v' proposition
                    if (upperBounds[cpVarIndex] == null)
                        upperBounds[cpVarIndex] = cpValue;
                    else {
                        int curBound = upperBounds[cpVarIndex];
                        if (cpValue < curBound)
                            upperBounds[cpVarIndex] = cpValue;
                    }

                } else {
                    // 'not x<=v', so 'x>v' proposition

                    cpValue++; // work on '>=' predicate, not '>'
                    if (lowerBounds[cpVarIndex] == null)
                        lowerBounds[cpVarIndex] = cpValue;
                    else {
                        int curBound = lowerBounds[cpVarIndex];
                        if (cpValue > curBound)
                            lowerBounds[cpVarIndex] = cpValue;
                    }
                }
            }
        }
    }

    /**
     * Using all data accumulated since last clear(), update the domain
     * of the given CP variable
     *
     * @param storeLevel the current level of the store
     */
    public void updateCpVariables(int storeLevel) {

        if (intVarsToUpdate.isEmpty() && booleanVarsToUpdate.isEmpty())
            return;

        assert wrapper.log(this, "update CP variables " + intVarsToUpdate + booleanVarsToUpdate);

        // first, update the IntVar
        for (int index = intVarsToUpdate.nextSetBit(0); index >= 0; index = intVarsToUpdate.nextSetBit(index + 1)) {
            IntVar variable = (IntVar) wrapper.store.vars[index];

            assert wrapper.log(this, "updating %s, with lower %s and upper %s, " + "excluded values are %s", variable, lowerBounds[index],
                upperBounds[index], excludedValues[index]);

            // update the range bounds
            Integer lower = lowerBounds[index];
            Integer upper = upperBounds[index];
            if (lower != null && upper != null) {
                variable.domain.in(storeLevel, variable, lower, upper);
            } else {
                if (lower != null)
                    variable.domain.inMin(storeLevel, variable, lower);
                if (upper != null)
                    variable.domain.inMax(storeLevel, variable, upper);
            }

            // exclude some values from the domain
            Set<Integer> excluded = excludedValues[variable.index];
            if (excluded == null)
                continue;
            for (int value : excluded)
                variable.domain.inComplement(storeLevel, variable, value);

        }

        // then, boolean variables
        for (BooleanVar variable : booleanVarsToUpdate) {
            int isOne = wrapper.cpVarToBoolVar(variable, 1, true);
            int isZero = wrapper.cpVarToBoolVar(variable, 0, true);
            int isOneValue = core.trail.values[isOne];
            int isZeroValue = core.trail.values[isZero];

            assert !(isZeroValue * isOneValue > 0); // not both true or false
            assert !(isOneValue == 0 && isZeroValue == 0); // at least one set

            if (isOneValue > 0 || isZeroValue < 0)
                variable.domain.in(storeLevel, variable, 1, 1);
            else if (isZeroValue > 0 || isOneValue < 0)
                variable.domain.in(storeLevel, variable, 0, 0);
            else
                throw new AssertionError("no changes for boolean var " + variable + "?");
        }

        assert wrapper.log(this, "updated CP variables " + intVarsToUpdate + booleanVarsToUpdate);
    }

    /**
     * gets sure we won't have a NullPointerException
     *
     * @param cpVar the CP variable we are about to access
     */
    public void ensureAccess(IntVar cpVar) {
        // only check things for true IntVar, not BooleanVar
        if (cpVar.index >= 0) {

            if (upperBounds.length <= cpVar.index) {
                int newLen = 2 * cpVar.index;
                upperBounds = Arrays.copyOf(upperBounds, newLen);
                lowerBounds = Arrays.copyOf(lowerBounds, newLen);
                excludedValues = Arrays.copyOf(excludedValues, newLen);
            }
        }

    }

    @Override public String toString() {
        // number of int vars to update
        int countPos = 0;
        countPos = intVarsToUpdate.cardinality();

        return String.format("SatChangesListener (%d IntVar and %d BoolVar) " + "vars have changes", countPos, booleanVarsToUpdate.size());
    }

    public void initialize(Core core) {
        this.core = core;

        // register
        core.assertionModules[core.numAssertionModules++] = this;
        core.propagateModules[core.numPropagateModules++] = this;
        core.backjumpModules[core.numBackjumpModules++] = this;
    }

    public void initialize(SatWrapper wrapper) {
        this.wrapper = wrapper;
    }
}
