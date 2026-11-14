/*
 * AbstractBoolSimple.java
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
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * Abstract base for two-input boolean constraints (OrBoolSimple, AndBoolSimple). Provides shared
 * fields, constructor, invariant checking, and pruning event configuration.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractBoolSimple extends PrimitiveConstraint implements Explainable {

  /** First boolean operand. */
  protected final IntVar a;

  /** Second boolean operand. */
  protected final IntVar b;

  /** Result variable storing the outcome of the boolean operation. */
  protected final IntVar result;

  /**
   * Constructs a two-input boolean constraint.
   *
   * @param idNum the id counter for the concrete subclass.
   * @param a first operand.
   * @param b second operand.
   * @param result result variable.
   */
  protected AbstractBoolSimple(AtomicInteger idNum, IntVar a, IntVar b, IntVar result) {

    checkInputForNullness(new String[] {"a", "b", "result"}, new Object[] {a, b, result});

    this.numberId = idNum.incrementAndGet();

    this.a = a;
    this.b = b;
    this.result = result;

    String error = checkInvariants();
    if (error != null) {
      throw new IllegalArgumentException(error);
    }

    queueIndex = 0;

    setScope(a, b, result);
  }

  /**
   * Checks that the operand variables have valid boolean domains (0 or 1).
   *
   * @return null if invariants hold, error message otherwise.
   */
  public String checkInvariants() {
    return checkBooleanDomains(a, b);
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  /**
   * Returns the first operand.
   *
   * @return variable a.
   */
  public IntVar a() {
    return a;
  }

  /**
   * Returns the second operand.
   *
   * @return variable b.
   */
  public IntVar b() {
    return b;
  }

  /**
   * Returns the result variable.
   *
   * @return the result variable.
   */
  public IntVar result() {
    return result;
  }

  /**
   * Returns the operand value that fixes the operation's value whatever the other operand is: 0 for
   * AND, 1 for OR; the result is then that value too.
   *
   * @return the absorbing value of the operation, or -1 when the subclass explains nothing
   */
  protected int absorbing() {
    return -1;
  }

  // the absorbing value, or -1 when the variables are not distinct or the class is not explained
  private int explained() {
    return a == b || a == result || b == result ? -1 : absorbing();
  }

  // under LCG, result = a op b (or its negation when flip is 1) is explained by atoms "x != v":
  // an operand with the absorbing value z fixes the result to z, two operands without it fix the
  // result to 1 - z, and a result other than z (1 - z) forces both operands to 1 - z (one operand
  // to z when the other is 1 - z)
  private boolean explain(AtomicTrail trail, int entry, int flip, EntryList out) {
    int z = explained();
    if (z < 0) {
      return false;
    }
    int absorbed = z ^ flip;
    int mark = out.size();
    IntVar v = trail.variable(entry);
    if (v == result) {
      if (impliedBy(trail, entry, absorbed)
          && (trail.excludedBefore(a, 1 - z, entry, out)
              || trail.excludedBefore(b, 1 - z, entry, out))) {
        return true;
      }
      out.truncate(mark);
      if (impliedBy(trail, entry, 1 - absorbed)
          && trail.excludedBefore(a, z, entry, out)
          && trail.excludedBefore(b, z, entry, out)) {
        return true;
      }
      out.truncate(mark);
      return false;
    }
    IntVar other = v == a ? b : a;
    if (impliedBy(trail, entry, 1 - z) && trail.excludedBefore(result, absorbed, entry, out)) {
      return true;
    }
    out.truncate(mark);
    if (impliedBy(trail, entry, z)
        && trail.excludedBefore(result, 1 - absorbed, entry, out)
        && trail.excludedBefore(other, z, entry, out)) {
      return true;
    }
    out.truncate(mark);
    return false;
  }

  // the entry's atom holds when its variable has value w
  private static boolean impliedBy(AtomicTrail trail, int entry, int w) {
    int value = trail.value(entry);
    return switch (trail.kind(entry)) {
      case AtomicTrail.GE -> w >= value;
      case AtomicTrail.LE -> w <= value;
      default -> w != value;
    };
  }

  // the atoms before the position that leave no assignment satisfying result = a op b (negated
  // when flip is 1)
  private boolean violated(AtomicTrail trail, int position, int flip, EntryList out) {
    int z = explained();
    if (z < 0) {
      return false;
    }
    int absorbed = z ^ flip;
    int mark = out.size();
    if (trail.excludedBefore(result, absorbed, position, out)
        && (trail.excludedBefore(a, 1 - z, position, out)
            || trail.excludedBefore(b, 1 - z, position, out))) {
      return true;
    }
    out.truncate(mark);
    if (trail.excludedBefore(result, 1 - absorbed, position, out)
        && trail.excludedBefore(a, z, position, out)
        && trail.excludedBefore(b, z, position, out)) {
      return true;
    }
    out.truncate(mark);
    if (trail.excludedBefore(result, 0, position, out)
        && trail.excludedBefore(result, 1, position, out)) {
      return true;
    }
    out.truncate(mark);
    return false;
  }

  // the bounds before the position that fix the result to w
  private boolean fixedTo(AtomicTrail trail, int position, IntVar x, int w, EntryList out) {
    if (trail.minBefore(x, position) < w || trail.maxBefore(x, position) > w) {
      return false;
    }
    trail.addLowerBound(x, position, out);
    trail.addUpperBound(x, position, out);
    return true;
  }

  // the atoms before the position under which every assignment satisfies result = a op b
  // (negated when flip is 1)
  private boolean holds(AtomicTrail trail, int position, int flip, EntryList out) {
    int z = explained();
    if (z < 0) {
      return false;
    }
    int absorbed = z ^ flip;
    int mark = out.size();
    if (fixedTo(trail, position, result, absorbed, out)
        && (trail.excludedBefore(a, 1 - z, position, out)
            || trail.excludedBefore(b, 1 - z, position, out))) {
      return true;
    }
    out.truncate(mark);
    if (fixedTo(trail, position, result, 1 - absorbed, out)
        && trail.excludedBefore(a, z, position, out)
        && trail.excludedBefore(b, z, position, out)) {
      return true;
    }
    out.truncate(mark);
    return false;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return explain(trail, entry, 0, out);
  }

  // every reason is checked against the atoms before it
  @Override
  public boolean checksReasons() {
    return explained() >= 0;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return violated(trail, trail.size(), 0, out);
  }

  @Override
  public boolean explainNegated(AtomicTrail trail, int entry, EntryList out) {
    return explain(trail, entry, 1, out);
  }

  @Override
  public boolean explainNegatedFailure(AtomicTrail trail, EntryList out) {
    return violated(trail, trail.size(), 1, out);
  }

  @Override
  public boolean explainEntailment(
      AtomicTrail trail, int position, boolean entailed, EntryList out) {
    return entailed
        ? holds(trail, position, 0, out)
        : violated(trail, position, 0, out) || holds(trail, position, 1, out);
  }
}
