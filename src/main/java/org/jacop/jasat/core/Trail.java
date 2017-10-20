/*
 * Trail.java
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

package org.jacop.jasat.core;

import java.util.Arrays;

import org.jacop.jasat.utils.MemoryPool;
import org.jacop.jasat.utils.Utils;
import org.jacop.jasat.utils.structures.IntStack;


/**
 * It stores the current variables status (affected or not, with which value and explanation).
 * It values of variables are packed in an int, together with the level at which 
 * they were asserted.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 *
 */

public final class Trail implements SolverComponent {

    // pool for fast int[] allocation
    public MemoryPool pool;

    // the values of variables
    public int[] values;

    // the explanations for assertions
    public int[] explanations;

    // to remember successive assertions, to backjump in an efficient way
    public IntStack assertionStack;

    // the levels at which variables are set
    private int[] levels;

    private int ASSERTED_MASK = Integer.MIN_VALUE;    // 100000....000
    private int LEVEL_MASK = Integer.MAX_VALUE >>> 1;    // 011111....111

    /**
     * It adds a variable to the trail.
     * @param var  the variable
     */
    public void addVariable(int var) {

        assert var > 0;
        ensureCapacity(var);

        values[var] = 0;
        levels[var] = 0;

    }

    /**
     * It ensures the trail can contain @param numVar variables
     * @param numVar  the number of variables the trail must be able to contain
     */
    public void ensureCapacity(int numVar) {

        assert values.length == explanations.length;
        assert values.length == levels.length;

        if (values.length <= numVar) {
            // resize (enlarge) if necessary
            int newSize = numVar * 2;
            int size = values.length;

            values = Utils.resize(values, newSize, size, pool);
            explanations = Utils.resize(explanations, newSize, size, pool);
            levels = Utils.resize(levels, newSize, size, pool);

            // do not forget to reset the new slots
            Arrays.fill(values, size, newSize - 1, 0);
        }

    }


    /**
     * Sets a literal, that is, a variable signed with its value ({@literal >} 0 for true,
     * {@literal <} 0 for false). This must be used only for asserted values,
     * not the ones propagated from unit clauses.
     * @param literal  the literal
     * @param level  the current level
     */
    public void assertLiteral(int literal, int level) {

        assert level >= 0;

        int var = Math.abs(literal);

        assert var < values.length;
        assert !isSet(var) : "variable already set !";

        assertLit(var, literal, level, true);

        assertionStack.push(var);

    }

    /**
     * Sets a literal, with an explanation clause. For unit propagation only.
     * @param literal  the literal (non nul relative number)
     * @param level    the level at which this assertion occurs
     * @param causeId  the ID of the clause that triggered this assertion
     */
    public void assertLiteral(int literal, int level, int causeId) {

        assert causeId >= 0;
        int var = Math.abs(literal);

        assertLit(var, literal, level, false);
        explanations[var] = causeId;

        assertionStack.push(var);
    }

    /**
     * real assignment of literal at level
     */
    private void assertLit(int var, int literal, int level, boolean asserted) {
        assert values.length > var;
        assert values[var] == 0;

        // remember value
        values[var] = literal;

        // pack level and some more data in an int
        int value = level;
        if (asserted)
            value |= ASSERTED_MASK;
        levels[var] = value;
    }

    /**
     * It unsets the given variable. Does not take car of assertionLevels !
     * @param var  the variable to unset. Must be positive.
     */
    public void unset(int var) {
        assert var > 0;
        assert var < values.length;
        assert isSet(var) : "var must be set";

        values[var] = 0;
    }

    /**
     * It tells the trail to return to given level. It will therefore erase all
     * assertion strictly above this level. Literals asserted at @param level will
     * be kept.
     * @param level  the level to jump to.
     */
    public void backjump(int level) {
        assert explanations.length == values.length;
        assert level >= 0;

        // remove all asserted items above level
        while (!assertionStack.isEmpty()) {
            int var = assertionStack.peek();
            assert var > 0;
            assert var < values.length;
            int currentLevel = getLevel(var);

            if (currentLevel > level) {
                // this variable must be unset, because its level is > @param level
                assertionStack.pop();
                unset(var);
            } else {
                // from now, we are under @param level
                break;
            }
            // note : something set with level=0 will never be changed
            // since curLevel > level >= 0 is mandatory for an assertion to
            // be removed
        }

    }


    /**
     * It returns the level at which @param var has been set. @param var *must*
     * be set, otherwise this will fail.
     * @param var  the literal which level we wish to know
     * @return the level
     */
    public int getLevel(int var) {

        assert var > 0;
        assert var < values.length;
        assert isSet(var);

        int level = levels[var] & LEVEL_MASK;
        return level;

    }

    /**
     * It returns the index of the clause that caused this variable to be set
     * @param var  the literal. Must be set.
     * @return an index if there was an explanation, 0 otherwise
     */
    public int getExplanation(int var) {

        assert var > 0;
        assert explanations.length == values.length;
        assert var < explanations.length;
        assert isSet(var);
        assert !isAsserted(var) : "only propagated literals have explanations";

        return explanations[var];
    }

    /**
     * It returns information if a variable was asserted or only propagated.
     * @param var  the variable
     * @return true if the variable was asserted
     */
    public boolean isAsserted(int var) {

        assert var > 0;
        assert isSet(var) : "var must be set";

        // isAsserted is encoded together with other data, for cache issues
        int value = levels[var];
        return (value & ASSERTED_MASK) != 0;

    }

    /**
     * predicate which meaning is : is this variable set or unknown ?
     * @param var  the variable, must be positive
     * @return true if the variable is set.
     */
    public boolean isSet(int var) {
        assert var > 0;
        assert var < values.length;

        int value = values[var];
        return value != 0;
    }

    /**
     * returns the number of currently set variables
     *
     * @return the number of currently set variables
     */
    public int size() {
        return assertionStack.size();
    }


    @Override public String toString() {
        StringBuilder sb = new StringBuilder("trail [");
        int n = assertionStack.size();
        for (int i = n - 1; i >= 0; --i) {
            int var = assertionStack.array[i];
            sb.append(values[var]);
            sb.append('(');
            sb.append(getLevel(var));
            sb.append(')');
            sb.append(" ");
        }
        return sb.append(']').toString();
    }



    /**
     * to be called before any use of the trail
     * @param core  the Solver instance
     */
    public void initialize(Core core) {

        int initialSize = core.config.trail_size;
        values = new int[initialSize + 1];
        explanations = new int[initialSize + 1];
        levels = new int[initialSize + 1];

        // set the solver's trail
        core.trail = this;
        this.pool = core.pool;

        assertionStack = new IntStack(pool);
    }

}
