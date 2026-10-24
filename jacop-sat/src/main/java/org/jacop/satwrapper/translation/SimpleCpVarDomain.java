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

import org.jacop.core.IntVar;
import org.jacop.satwrapper.SatWrapper;

/**
 * A simple representation for small domains, not lazy. It allocates boolean variables to stand for
 * propositions '[x=v]' and '[x{@literal <=}v]' for each value v of the domain of x (even
 * '[x{@literal <=}max]', which is a tautology, for simplicity), and links them with clauses.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public class SimpleCpVarDomain extends SatCpBridge {

  // the first boolean variable; [x=v] is firstVar + 2*(v-min), [x<=v] the next one
  private int firstVar;

  /**
   * Creates the boolean variables of a CP variable and adds the clauses linking them.
   *
   * @param wrapper the SAT wrapper
   * @param variable the CP variable
   */
  public SimpleCpVarDomain(SatWrapper wrapper, IntVar variable) {
    super(variable);
    initialize(wrapper);
    setDomain(variable.min(), variable.max());
    wrapper.domainTranslator.translate(variable);
  }

  @Override
  public final int cpValueToBoolVar(int value, boolean isEquality) {
    if (ASSERTS_ENABLED && (value < getMin() || value > getMax())) {
      throw new IllegalStateException("value " + value + " outside the domain of " + variable);
    }
    int offset = value - getMin();
    return isEquality ? firstVar + 2 * offset : firstVar + 2 * offset + 1;
  }

  @Override
  public final int boolVarToCpValue(int literal) {
    return getMin() + (Math.abs(literal) - firstVar) / 2;
  }

  @Override
  public final boolean isEqualityBoolVar(int literal) {
    return ((Math.abs(literal) - firstVar) & 0x1) == 0;
  }

  @Override
  public void setDomain(int minValue, int maxValue) {
    if (hasSetDomain) {
      return;
    }
    super.setDomain(minValue, maxValue);
    firstVar = wrapper.newBoolVars(2 * (maxValue - minValue + 1), this);
  }
}
