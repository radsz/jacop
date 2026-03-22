/*
 * MapClause.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.core.clauses;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import org.jacop.jasat.core.Trail;
import org.jacop.jasat.utils.MemoryPool;

/**
 * A clause used for resolution, easily modifiable several times, and that can then be converted to
 * an int[].
 *
 * <p>This represents a *single* clause.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class MapClause implements Iterable<Integer> {

  /** The literals of the clause. */
  public final Map<Integer, Boolean> literals = new HashMap<>();

  /** The literal that will be asserted due to unit propagation of the conflict clause. */
  public int assertedLiteral;

  /** The level at which backjumping should go due to the explanation clause. */
  public int backjumpLevel;

  /** Creates an empty clause. */
  public MapClause() {}

  /**
   * Initializes the SetClause with given int[] clause.
   *
   * @param clause the clause
   */
  public MapClause(int[] clause) {
    addAll(clause);
  }

  /**
   * Initializes the SetClause with given iterable of literals.
   *
   * @param clause the clause
   */
  public MapClause(Iterable<Integer> clause) {
    addAll(clause);
  }

  /**
   * Add a literal to the clause, with resolution. If the opposite literal (same variable, opposite
   * sign) is in the clause, it returns true.
   *
   * @param literal the literal to be added from another clause
   * @return true if the opposite literal is in the clause, false otherwise
   */
  public boolean addLiteral(int literal) {
    if (ASSERTS_ENABLED && literal == 0) {
      throw new IllegalStateException("Assertion failed");
    }

    // key, value
    int varIdx = Math.abs(literal);
    boolean sign = varIdx == literal;

    // old value for this key, if any
    Boolean oldSign = literals.put(varIdx, sign);
    return oldSign != null && (oldSign ^ sign);
  }

  /**
   * It removes the literal, if it is in the clause. It uses a HashMap to obtain constant time
   * remove time.
   *
   * @param literal the literal to remove (sign sensitive)
   * @return true if the literal was present (and removed), false otherwise
   */
  public boolean removeLiteral(int literal) {
    int varIdx = Math.abs(literal);
    boolean sign = varIdx == literal;

    Boolean b = literals.get(varIdx);
    if (b != null && b == sign) {
      literals.remove(varIdx);
      return true;
    } else {
      return false;
    }
  }

  /**
   * If variable specified by the literal does not exists in this clause then literal is added. If
   * variable exists as the opposite literal then the opposite literal is removed and nothing is
   * added.
   *
   * @param literal the literal to be added
   */
  public void partialResolveWith(int literal) {

    int varIdx = Math.abs(literal);
    boolean sign = varIdx == literal;

    Boolean b = literals.get(varIdx);

    if (b == null) {
      literals.put(varIdx, sign);
    } else if (b != sign) {
      literals.remove(varIdx);
    }
  }

  /**
   * Predicate which is true iff the literal is present.
   *
   * @param literal a literal
   * @return true if the literal (and not its opposite) is in the clause
   */
  public boolean containsLiteral(int literal) {

    // key, value
    int varIdx = Math.abs(literal);
    boolean sign = varIdx == literal;

    Boolean value = literals.get(varIdx);
    return value != null && value == sign;
  }

  /**
   * Predicate which is true iff the variable or its opposite is present.
   *
   * @param varIdx the SAT variable index ({@literal >} 0)
   * @return true if the literal or its opposite is in the clause
   */
  public boolean containsVariable(int varIdx) {

    if (ASSERTS_ENABLED && varIdx <= 0) {
      throw new IllegalStateException("Assertion failed");
    }
    return literals.containsKey(varIdx);
  }

  /**
   * Checks if the clause is unsatisfiable in the given trail.
   *
   * @param trail the trail to check
   * @return true if all literals of the clause are false in the trail
   */
  public boolean isUnsatisfiableIn(Trail trail) {

    for (int lit : this) {
      int varIdx = Math.abs(lit);
      int value = trail.values[varIdx];

      // if this literal is not falsified
      if (value == 0 || lit == value) {
        return false;
      }
    }

    return true;
  }

  /**
   * Checks if the clause is unit with the given literal in the trail.
   *
   * @param literal the only satisfiable literal in the clause
   * @param trail the trail for the literal
   * @return true if the clause is unit with only @param literal not set
   */
  public boolean isUnitIn(int literal, Trail trail) {

    for (int lit : this) {
      int varIdx = Math.abs(lit);

      /*
       * 2 failure case : the literal is not active, or
       * one of the other literals is not set or is satisfied
       */
      if (lit == literal) {
        if (trail.isSet(varIdx)) {
          return false;
        }
      } else {
        if ((!trail.isSet(varIdx)) || trail.values[varIdx] == lit) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * Checks if the clause is unit in the given trail.
   *
   * @param trail the trail to check
   * @return true if the clause is unit (only one unset literal)
   */
  public boolean isUnitIn(Trail trail) {
    // number of non set literals
    int num = 0;
    for (int varIdx : literals.keySet()) {
      if (!trail.isSet(varIdx)) {
        num++;
      }
    }

    return num == 1;
  }

  /**
   * Checks if the clause is empty.
   *
   * @return true if the clause is empty
   */
  public boolean isEmpty() {
    return literals.isEmpty();
  }

  /**
   * Returns the number of literals in the clause.
   *
   * @return the number of literals in the clause
   */
  public int size() {
    return literals.size();
  }

  /**
   * Converts the clause to an int[] suitable for the efficient clauses pool implementations. The
   * clause must not be empty.
   *
   * @param pool the pool for clause implementation
   * @return an equivalent clause
   */
  public int[] toIntArray(MemoryPool pool) {
    int[] answer = pool.getNew(literals.size());
    return toIntArray(answer);
  }

  private int[] toIntArray(int[] array) {
    if (ASSERTS_ENABLED && array.length != literals.size()) {
      throw new IllegalStateException("Assertion failed");
    }
    int i = 0;
    for (int literal : this) {
      array[i++] = literal;
    }
    return array;
  }

  /**
   * Allocates an int[] and dumps the clause in.
   *
   * @return a new int[] representing this clause
   */
  public int[] toIntArray() {
    int[] answer = new int[literals.size()];
    return toIntArray(answer);
  }

  /** Returns a nice representation of the clause. */
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder().append('[');
    for (int literal : this) {
      if (literal > 0) {
        sb.append(' '); // to balance with the '-'
      }
      sb.append(literal);
      sb.append(' ');
    }
    return sb.append(']').toString();
  }

  /** Clear the clause, ie. removes all literals */
  public void clear() {
    literals.clear();
    if (ASSERTS_ENABLED && !isEmpty()) {
      throw new IllegalStateException("Assertion failed");
    }
  }

  /**
   * Adds all elements of clause to the SetClause, performing resolution.
   *
   * @param clause the literals to add
   * @return true if the resulting SetClause is trivial (tautology), false otherwise
   */
  public boolean addAll(Iterable<Integer> clause) {
    boolean answer = false;
    for (int literal : clause) {
      answer |= addLiteral(literal);
    }
    return answer;
  }

  /**
   * Same as previous.
   *
   * @param clause clause the literals to add
   * @return true if the resulting SetClause is trivial (tautology), false otherwise
   */
  public boolean addAll(int[] clause) {
    boolean answer = false;
    for (int literal : clause) {
      answer |= addLiteral(literal);
    }
    return answer;
  }

  /** (slow) iterate over literals of the clause. */
  @Override
  public Iterator<Integer> iterator() {
    return new ClauseIterator();
  }

  private final class ClauseIterator implements Iterator<Integer> {
    private final Iterator<Integer> it;

    {
      it = literals.keySet().iterator();
    }

    @Override
    public boolean hasNext() {
      return it.hasNext();
    }

    @Override
    public Integer next() {
      int e = it.next();
      boolean value = literals.get(e);
      return value ? e : -e;
    }

    @Override
    public void remove() {
      it.remove();
    }
  }
}
