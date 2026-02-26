/*
 * SimpleCpVarDomain.java
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

package org.jacop.satwrapper.translation;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.Arrays;
import org.jacop.core.IntVar;
import org.jacop.satwrapper.SatWrapper;

/**
 * A simple representation for small domains, not lazy. It allocates boolean variables to stand for
 * propositions '[x=v]' and '[x{@literal <=}v]' for each value v of the domain of x (even
 * '[x{@literal <=}max]', which is a tautology, for simplicity)
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public class SimpleCpVarDomain extends SatCpBridge {

  private boolean translated = true;
  // first boolean variable representing this
  private int firstVar;
  // the special clauses database of the wrapper
  private DomainClausesDatabase clauseDatabase;

  /**
   * Constructs a simple CP variable domain.
   *
   * @param wrapper the SAT wrapper
   * @param variable the integer variable
   */
  public SimpleCpVarDomain(SatWrapper wrapper, IntVar variable) {
    super(variable);
    initialize(wrapper);
    setDomain(variable.min(), variable.max());
    if (translated) {
      wrapper.domainTranslator.translate(variable);
    }
  }

  /**
   * Constructs a simple CP variable domain with translation control.
   *
   * @param wrapper the SAT wrapper
   * @param variable the integer variable
   * @param translate whether to translate the variable
   */
  public SimpleCpVarDomain(SatWrapper wrapper, IntVar variable, boolean translate) {
    super(variable);
    this.translated = translate;
    initialize(wrapper);
    setDomain(variable.min(), variable.max());
    if (translated) {
      wrapper.domainTranslator.translate(variable);
    }
  }

  @Override
  public final int cpValueToBoolVar(int value, boolean isEquality) {
    if (ASSERTS_ENABLED && !(value >= getMin())) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(value <= getMax())) {
      throw new IllegalStateException("Assertion failed");
    }

    int offset = value - getMin();

    if (isEquality) {
      return firstVar + 2 * offset;
    } else {
      return firstVar + 2 * offset + 1;
    }
  }

  @Override
  public final int boolVarToCpValue(int literal) {
    int varIdx = Math.abs(literal);
    if (ASSERTS_ENABLED && !(varIdx >= firstVar)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(varIdx <= firstVar + (getMax() - getMin() + 1) * 2)) {
      throw new IllegalStateException("Assertion failed");
    }

    return getMin() + (varIdx - firstVar) / 2;
  }

  @Override
  public final boolean isEqualityBoolVar(int literal) {
    if (ASSERTS_ENABLED && !(wrapper.boolVarToCpVar(literal) == this.variable)) {
      throw new IllegalStateException("Assertion failed");
    }
    int varIdx = Math.abs(literal);

    return ((varIdx - firstVar) & 0x1) == 0; // modulo 2
  }

  @Override
  public void setDomain(int minValue, int maxValue) {

    if (hasSetDomain) {
      return;
    }

    super.setDomain(minValue, maxValue);

    // get as many fresh variables as needed
    // width of the domain (number of different values)
    int width = 2 * (maxValue - minValue + 1);
    firstVar = wrapper.core.getManyFreshVariables(width);

    // remember association literal -> range
    if (wrapper.boolVarToDomains.length <= firstVar + width) {
      int newLength = 2 * (firstVar + width);
      wrapper.boolVarToDomains = Arrays.copyOf(wrapper.boolVarToDomains, newLength);
    }
    for (int i = firstVar; i < firstVar + width; i++) {
      wrapper.boolVarToDomains[i] = this;
    }
  }

  /** Propagates other literals that should be asserted given a literal value. */
  @Override
  public void propagate(int literal) {

    if (ASSERTS_ENABLED && !(isInThisRange(literal))) {
      throw new IllegalStateException("Assertion failed");
    }

    int value = boolVarToCpValue(literal);
    boolean isEquality = isEqualityBoolVar(literal);

    if (ASSERTS_ENABLED && !(getMax() >= getMin())) {
      throw new IllegalStateException("Assertion failed");
    }

    if (getMax() == getMin()) {
      clauseDatabase.propagate(cpValueToBoolVar(getMin(), true), literal);
      return;
    }

    if (isEquality) {
      if (literal > 0) {
        propagateEqualityTrue(value, literal);
      } else {
        propagateEqualityFalse(value, literal);
      }
    } else {
      if (literal > 0) {
        propagateLeqTrue(value, literal);
      } else {
        propagateLeqFalse(value, literal);
      }
    }
  }

  private void propagateEqualityTrue(int value, int literal) {
    for (int i = getMin(); i <= getMax(); i++) {
      if (i == value) {
        continue;
      }
      clauseDatabase.propagate(-cpValueToBoolVar(i, true), literal);
    }
    for (int i = getMin(); i < value; i++) {
      clauseDatabase.propagate(-cpValueToBoolVar(i, false), literal);
    }
    for (int i = value; i <= getMax(); i++) {
      clauseDatabase.propagate(cpValueToBoolVar(i, false), literal);
    }
  }

  private void propagateEqualityFalse(int value, int literal) {
    if (value == getMin()) {
      clauseDatabase.propagate(-cpValueToBoolVar(value, false), literal);
    }
    if (value == getMax()) {
      clauseDatabase.propagate(cpValueToBoolVar(value - 1, false), literal);
    }
    if (getMax() - getMin() == 1 && value == getMax()) {
      clauseDatabase.propagate(cpValueToBoolVar(getMin(), true), literal);
    }
    if (getMax() - getMin() == 1 && value == getMin()) {
      clauseDatabase.propagate(cpValueToBoolVar(getMax(), true), literal);
    }
    if (value == getMin() + 1) {
      clauseDatabase.propagate(cpValueToBoolVar(getMin(), true), literal);
    }
  }

  private void propagateLeqTrue(int value, int literal) {
    for (int i = value + 1; i <= getMax(); i++) {
      clauseDatabase.propagate(-cpValueToBoolVar(i, true), literal);
    }
    for (int i = value + 1; i <= getMax(); i++) {
      clauseDatabase.propagate(cpValueToBoolVar(i, false), literal);
    }
  }

  private void propagateLeqFalse(int value, int literal) {
    for (int i = getMin(); i <= value; i++) {
      clauseDatabase.propagate(-cpValueToBoolVar(i, true), literal);
    }
    for (int i = getMin(); i <= value; i++) {
      clauseDatabase.propagate(-cpValueToBoolVar(i, false), literal);
    }
  }

  /** {@inheritDoc} */
  @Override
  public boolean isTranslated() {
    return translated;
  }

  /** {@inheritDoc} */
  @Override
  public void initialize(SatWrapper wrapper) {
    super.initialize(wrapper);
    if (ASSERTS_ENABLED && !(wrapper.domainDatabase != null)) {
      throw new IllegalStateException(String.valueOf("DomainClausesDatabase is needed"));
    }
    this.clauseDatabase = wrapper.domainDatabase;
  }
}
