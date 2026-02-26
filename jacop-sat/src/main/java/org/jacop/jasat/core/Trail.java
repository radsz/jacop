/*
 * Trail.java
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

package org.jacop.jasat.core;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.Arrays;
import org.jacop.jasat.utils.MemoryPool;
import org.jacop.jasat.utils.Utils;
import org.jacop.jasat.utils.structures.IntStack;

/**
 * It stores the current variables status (affected or not, with which value and explanation). It
 * values of variables are packed in an int, together with the level at which they were asserted.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class Trail implements SolverComponent {

  private static final int ASSERTED_MASK = Integer.MIN_VALUE; // 100000....000
  private static final int LEVEL_MASK = Integer.MAX_VALUE >>> 1; // 011111....111
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

  /**
   * It adds a variable to the trail.
   *
   * @param varIdx the SAT variable index
   */
  public void addVariable(int varIdx) {

    if (ASSERTS_ENABLED && !(varIdx > 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    ensureCapacity(varIdx);

    values[varIdx] = 0;
    levels[varIdx] = 0;
  }

  /**
   * It ensures the trail can contain @param numVar variables.
   *
   * @param numVar the number of variables the trail must be able to contain
   */
  public void ensureCapacity(int numVar) {

    if (ASSERTS_ENABLED && !(values.length == explanations.length)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(values.length == levels.length)) {
      throw new IllegalStateException("Assertion failed");
    }

    if (values.length <= numVar) {
      // resize (enlarge) if necessary
      int newSize = numVar * 2;
      int size = values.length;

      values = Utils.resize(values, newSize, size, pool);
      explanations = Utils.resize(explanations, newSize, size, pool);
      levels = Utils.resize(levels, newSize, size, pool);

      Arrays.fill(values, size, newSize - 1, 0);
    }
  }

  /**
   * Sets a literal, that is, a variable signed with its value ({@literal >} 0 for true, {@literal
   * <} 0 for false). This must be used only for asserted values, not the ones propagated from unit
   * clauses.
   *
   * @param literal the literal
   * @param level the current level
   */
  public void assertLiteral(int literal, int level) {

    if (ASSERTS_ENABLED && !(level >= 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    int varIdx = Math.abs(literal);

    if (ASSERTS_ENABLED && !(varIdx < values.length)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(!isSet(varIdx))) {
      throw new IllegalStateException(String.valueOf("variable already set !"));
    }

    assertLit(varIdx, literal, level, true);

    assertionStack.push(varIdx);
  }

  /**
   * Sets a literal, with an explanation clause. For unit propagation only.
   *
   * @param literal the literal (non nul relative number)
   * @param level the level at which this assertion occurs
   * @param causeId the ID of the clause that triggered this assertion
   */
  public void assertLiteral(int literal, int level, int causeId) {

    if (ASSERTS_ENABLED && !(causeId >= 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    int varIdx = Math.abs(literal);

    assertLit(varIdx, literal, level, false);
    explanations[varIdx] = causeId;

    assertionStack.push(varIdx);
  }

  /** Real assignment of literal at level. */
  private void assertLit(int varIdx, int literal, int level, boolean asserted) {
    if (ASSERTS_ENABLED && !(values.length > varIdx)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(values[varIdx] == 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    // remember value
    values[varIdx] = literal;

    // pack level and some more data in an int
    int value = level;
    if (asserted) {
      value |= ASSERTED_MASK;
    }
    levels[varIdx] = value;
  }

  /**
   * It unsets the given variable. Does not take car of assertionLevels !
   *
   * @param varIdx the SAT variable index to unset. Must be positive.
   */
  public void unset(int varIdx) {
    if (ASSERTS_ENABLED && !(varIdx > 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(varIdx < values.length)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(isSet(varIdx))) {
      throw new IllegalStateException(String.valueOf("varIdx must be set"));
    }

    values[varIdx] = 0;
  }

  /**
   * It tells the trail to return to given level. It will therefore erase all assertion strictly
   * above this level. Literals asserted at @param level will be kept.
   *
   * @param level the level to jump to.
   */
  public void backjump(int level) {
    if (ASSERTS_ENABLED && !(explanations.length == values.length)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(level >= 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    // remove all asserted items above level
    while (!assertionStack.isEmpty()) {
      int varIdx = assertionStack.peek();
      if (ASSERTS_ENABLED && !(varIdx > 0)) {
        throw new IllegalStateException("Assertion failed");
      }
      if (ASSERTS_ENABLED && !(varIdx < values.length)) {
        throw new IllegalStateException("Assertion failed");
      }
      int currentLevel = getLevel(varIdx);

      if (currentLevel > level) {
        // this variable must be unset, because its level is > @param level
        assertionStack.pop();
        unset(varIdx);
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
   * It returns the level at which the given variable has been set. The variable *must* be set,
   * otherwise this will fail.
   *
   * @param varIdx the SAT variable index whose level we wish to know
   * @return the level
   */
  public int getLevel(int varIdx) {

    if (ASSERTS_ENABLED && !(varIdx > 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(varIdx < values.length)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(isSet(varIdx))) {
      throw new IllegalStateException("Assertion failed");
    }

    return levels[varIdx] & LEVEL_MASK;
  }

  /**
   * It returns the index of the clause that caused this variable to be set.
   *
   * @param varIdx the SAT variable index. Must be set.
   * @return an index if there was an explanation, 0 otherwise
   */
  public int getExplanation(int varIdx) {

    if (ASSERTS_ENABLED && !(varIdx > 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(explanations.length == values.length)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(varIdx < explanations.length)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(isSet(varIdx))) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(!isAsserted(varIdx))) {
      throw new IllegalStateException(String.valueOf("only propagated literals have explanations"));
    }

    return explanations[varIdx];
  }

  /**
   * It returns information if a variable was asserted or only propagated.
   *
   * @param varIdx the SAT variable index
   * @return true if the variable was asserted
   */
  public boolean isAsserted(int varIdx) {

    if (ASSERTS_ENABLED && !(varIdx > 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(isSet(varIdx))) {
      throw new IllegalStateException(String.valueOf("varIdx must be set"));
    }

    // isAsserted is encoded together with other data, for cache issues
    int value = levels[varIdx];
    return (value & ASSERTED_MASK) != 0;
  }

  /**
   * Checks if this variable is set or unknown.
   *
   * @param varIdx the SAT variable index, must be positive
   * @return true if the variable is set.
   */
  public boolean isSet(int varIdx) {
    if (ASSERTS_ENABLED && !(varIdx > 0)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(varIdx < values.length)) {
      throw new IllegalStateException("Assertion failed");
    }

    int value = values[varIdx];
    return value != 0;
  }

  /**
   * Returns the number of currently set variables.
   *
   * @return the number of currently set variables
   */
  public int size() {
    return assertionStack.size();
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder("trail [");
    int n = assertionStack.size();
    for (int i = n - 1; i >= 0; i--) {
      int varIdx = assertionStack.array[i];
      sb.append(values[varIdx]);
      sb.append('(');
      sb.append(getLevel(varIdx));
      sb.append(')');
      sb.append(" ");
    }
    return sb.append(']').toString();
  }

  /**
   * To be called before any use of the trail.
   *
   * @param core the Solver instance
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
