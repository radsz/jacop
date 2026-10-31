/*
 * OrBoolSimple.java
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

import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.ToIntFunction;
import org.jacop.api.Copyable;
import org.jacop.api.Functional;
import org.jacop.api.Monotone;
import org.jacop.api.MonotoneDefinition;
import org.jacop.api.VarMap;
import org.jacop.api.Violation;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * If at least one variable is equal 1 then result variable is equal 1 too. Otherwise, result
 * variable is equal to zero. It restricts the domain of a and b as well as result to be between 0
 * and 1.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class OrBoolSimple extends AbstractBoolSimple
    implements Functional, Violation, Copyable<OrBoolSimple>, Monotone, MonotoneDefinition {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It constructs orBool.
   *
   * @param a a parameter
   * @param b b parameter
   * @param result variable which is equal 0 if none of x is equal to zero.
   */
  public OrBoolSimple(IntVar a, IntVar b, IntVar result) {
    super(idNumber, a, b, result);
  }

  /**
   * Enforces consistency for this constraint.
   *
   * @param store the constraint store in which the constraint is imposed.
   */
  public void consistency(Store store) {
    // a OR b = result
    if (a.max() == 0 && b.max() == 0) {
      result.domain.inValue(store.level, result, 0);
    } else if (a.min() == 1 || b.min() == 1) {
      result.domain.inValue(store.level, result, 1);
      removeConstraint();
    } else if (result.max() == 0) {
      a.domain.inValue(store.level, a, 0);
      b.domain.inValue(store.level, b, 0);
    } else if (result.min() == 1) {
      if (a.max() == 0) {
        b.domain.inValue(store.level, b, 1);
      } else if (b.max() == 0) {
        a.domain.inValue(store.level, a, 1);
      }
    }
  }

  @Override
  public void notConsistency(Store store) {
    // not(a OR b) = not a and not b = result
    if (a.min() == 1 || b.min() == 1) {
      result.domain.inValue(store.level, result, 0);
      removeConstraint();
    } else if (a.max() == 0 && b.max() == 0) {
      result.domain.inValue(store.level, result, 1);
    } else if (result.min() == 1) {
      a.domain.inValue(store.level, a, 0);
      b.domain.inValue(store.level, b, 0);
    } else if (result.max() == 0) {
      if (a.max() == 0) {
        b.domain.inValue(store.level, b, 1);
      } else if (b.max() == 0) {
        a.domain.inValue(store.level, a, 1);
      }
    }
  }

  @Override
  public boolean satisfied() {
    return (result.max() == 0 && a.max() == 0 && b.max() == 0)
        || (result.min() == 1 && (a.min() == 1 || b.min() == 1));
  }

  @Override
  public boolean notSatisfied() {
    return (result.min() == 1 && a.max() == 0 && b.max() == 0)
        || (result.max() == 0 && (a.min() == 1 || b.min() == 1));
  }

  @Override
  public String toString() {

    return id() + " : orBoolSimple([ " + a + ", " + b + "], " + result + ")";
  }

  @Override
  public OrBoolSimple copy(VarMap map) {
    return new OrBoolSimple(map.get(a), map.get(b), map.get(result));
  }

  @Override
  public int freeDirections(Var v) {
    // with the result true this is a clause; otherwise both variables are tied to the result
    return v != result && result.min() == 1 ? INCREASE : 0;
  }

  @Override
  public Var defined() {
    return result.singleton() || a == result || b == result ? null : result;
  }

  @Override
  public int monotonicity(Var v) {
    return 1;
  }

  @Override
  public long violation(ToIntFunction<IntVar> value) {
    return value.applyAsInt(result) == (value.applyAsInt(a) | value.applyAsInt(b)) ? 0 : 1;
  }

  @Override
  public IntVar functionalResult() {
    return result;
  }

  @Override
  public int functionalValue(ToIntFunction<IntVar> value) {
    return value.applyAsInt(a) | value.applyAsInt(b);
  }
}
