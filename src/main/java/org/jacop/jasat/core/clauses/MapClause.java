/*
 * MapClause.java
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

package org.jacop.jasat.core.clauses;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.jacop.jasat.core.Trail;
import org.jacop.jasat.utils.MemoryPool;

/**
 * A clause used for resolution, easily modifiable several times, and that
 * can then be converted to an int[].
 *
 * This represents a *single* clause.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 *
 */

public final class MapClause implements Iterable<Integer> {

    /**
     * the literals of the clause
     */
    public Map<Integer, Boolean> literals = new HashMap<Integer, Boolean>();

    /**
     * the literal that will be asserted due to unit propagation of the conflict clause.
     */
    public int assertedLiteral;

    /**
     * the level at which backjumping should go due to the explanation clause.
     */
    public int backjumpLevel;

    /**
     * Add a literal to the clause, with resolution. If the opposite literal
     * (same variable, opposite sign) is in the clause, it returns true.
     * @param literal  the literal to be added from another clause
     * @return true if the opposite literal is in the clause, false otherwise
     */
    public boolean addLiteral(int literal) {
        assert literal != 0;

        // key, value
        int var = Math.abs(literal);
        boolean sign = var == literal ? true : false;

        // old value for this key, if any
        Boolean oldSign = literals.put(var, sign);
        return oldSign != null && (oldSign ^ sign);
    }


    /**
     * It removes the literal, if it is in the clause. It uses a HashMap to obtain constant time remove time.
     *
     * @param literal  the literal to remove (sign sensitive)
     * @return true if the literal was present (and removed), false otherwise
     */
    public boolean removeLiteral(int literal) {
        int var = Math.abs(literal);
        boolean sign = (var == literal);

        Boolean b = literals.get(var);
        if (b != null && b == sign) {
            literals.remove(var);
            return true;
        } else {
            return false;
        }
    }

    /**
     * If variable specified by the literal does not exists in this clause then
     * literal is added. If variable exists as the opposite literal then the opposite
     * literal is removed and nothing is added.
     *
     * @param literal the literal to be added
     */
    public void partialResolveWith(int literal) {

        int var = Math.abs(literal);
        boolean sign = (var == literal);

        Boolean b = literals.get(var);

        if (b == null)
            literals.put(var, sign);
        else if (b != sign)
            literals.remove(var);

    }

    /**
     * Predicate which is true iff the literal is present.
     * @param literal  a literal
     * @return true if the literal (and not its opposite) is in the clause
     */
    public boolean containsLiteral(int literal) {

        // key, value
        int var = Math.abs(literal);
        boolean sign = (var == literal);

        Boolean value = literals.get(var);
        return value != null && value == sign;
    }

    /**
     * Predicate which is true iff the variable or its opposite is present
     * @param var  a variable ({@literal >} 0)
     * @return true if the literal or its opposite is in the clause
     */
    public boolean containsVariable(int var) {

        assert var > 0;
        return literals.containsKey(var);

    }

    /**
     * @param trail the trail to check
     * @return true if all literals of the clause are false in the trail
     */
    public boolean isUnsatisfiableIn(Trail trail) {

        for (int lit : this) {
            int var = Math.abs(lit);
            int value = trail.values[var];

            // if this literal is not falsified
            if (value == 0 || lit == value)
                return false;
        }

        return true;

    }

    /**
     * @param literal  the only satisfiable literal in the clause
     * @param trail the trail for the literal
     * @return true if the clause is unit with only @param literal not set
     */
    public boolean isUnitIn(int literal, Trail trail) {

        for (int lit : this) {
            int var = Math.abs(lit);

			/*
			 * 2 failure case : the literal is not active, or
			 * one of the other literals is not set or is satisfied
			 */
            if (lit == literal) {
                if (trail.isSet(var))
                    return false;
            } else {
                if ((!trail.isSet(var)) || trail.values[var] == lit)
                    return false;
            }
        }
        return true;

    }

    public boolean isUnitIn(Trail trail) {
        // number of non set literals
        int num = 0;
        for (int var : literals.keySet()) {
            if (!trail.isSet(var))
                num++;
        }

        return num == 1;
    }

    /**
     * @return true if the clause is empty
     */
    public boolean isEmpty() {
        return literals.isEmpty();
    }

    /**
     * returns the number of literals in the clause
     * @return the number of literals in the clause
     */
    public int size() {
        return literals.size();
    }

    /**
     * converts the clause to an int[] suitable for the efficient clauses pool
     * implementations. The clause must not be empty.
     * @param pool the pool for clause implementation
     * @return an equivalent clause
     */
    public int[] toIntArray(MemoryPool pool) {
        int[] answer = pool.getNew(literals.size());
        return toIntArray(answer);
    }

    private int[] toIntArray(int[] array) {
        assert array.length == literals.size();
        int i = 0;
        for (int literal : this)
            array[i++] = literal;
        return array;
    }

    /**
     * allocates an int[] and dumps the clause in
     * @return a new int[] representing this clause
     */
    public int[] toIntArray() {
        int[] answer = new int[literals.size()];
        return toIntArray(answer);
    }

    /**
     * true iff the clause is trivial (contains a literal and its opposite).
     * Now, by construction, a MapClause cannot be trivial
     * @return true iff the clause is trivial
     */
    @Deprecated public boolean isTrivial() {
        return false;
    }

    /**
     * returns a nice representation of the clause
     */
    @Override public String toString() {
        StringBuilder sb = new StringBuilder().append('[');
        for (int literal : this) {
            if (literal > 0)
                sb.append(' ');  // to balance with the '-'
            sb.append(literal);
            sb.append(' ');
        }
        return sb.append(']').toString();
    }

    /**
     * clear the clause, ie. removes all literals
     */
    public void clear() {
        literals.clear();
        assert isEmpty();
    }

    /**
     * @TODO, FIXME
     *
     * addAll functions are used to add many literals to empty clause, better is to
     * simplify adding by using function initializeWith(Iterable<Integer> clause)
     * that assumes that clause is correctly formulated (no negative literals exist).
     */

    /**
     * adds all elements of clause to the SetClause, performing resolution.
     * @param clause the literals to add
     * @return true if the resulting SetClause is trivial (tautology), false
     * otherwise
     */
    public final boolean addAll(Iterable<Integer> clause) {
        boolean answer = false;
        for (int literal : clause)
            answer |= addLiteral(literal);
        return answer;
    }

    /**
     * same as previous
     * @param clause clause the literals to add
     * @return true if the resulting SetClause is trivial (tautology), false
     * otherwise
     */
    public final boolean addAll(int[] clause) {
        boolean answer = false;
        for (int literal : clause)
            answer |= addLiteral(literal);
        return answer;
    }

    /**
     * creates an empty clause
     */
    public MapClause() {
    }

    /**
     * initializes the SetClause with given int[] clause
     * @param clause  the clause
     */
    public MapClause(int[] clause) {
        addAll(clause);
    }

    public MapClause(Iterable<Integer> clause) {
        addAll(clause);
    }

    /**
     * (slow) iterate over literals of the clause
     */
    public Iterator<Integer> iterator() {
        return new ClauseIterator();
    }

    private final class ClauseIterator implements Iterator<Integer> {
        private Iterator<Integer> it;

        {
            it = literals.keySet().iterator();
        }

        public boolean hasNext() {
            return it.hasNext();
        }

        public Integer next() {
            int e = it.next();
            boolean value = literals.get(e);
            int curLiteral = value ? e : -e;
            return curLiteral;
        }

        public void remove() {
            it.remove();
        }
    }

}
