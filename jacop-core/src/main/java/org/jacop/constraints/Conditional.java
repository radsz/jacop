/*
 * Conditional.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.util.QueueForward;

/**
 * Conditional constraint implements conditional constraint satisfiability. It enforces consistency
 * of constraint c[k] where b[k] = 1 (true) and all b[i] for i {@literal <} k are 0 (false).
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class Conditional extends Constraint
    implements SatisfiedPresent, UsesQueueVariable, Copyable<Conditional> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The list of 0/1 (Boolean) variables for assignment decision. */
  private final IntVar[] b;

  /** The list of constraints that are to be selected. */
  private final PrimitiveConstraint[] c;

  private final QueueForward<PrimitiveConstraint> queueForward;

  /**
   * It constructs a Conditional constraint.
   *
   * @param b 0/1 variables for selection of constraint
   * @param c constraints for selection.
   */
  public Conditional(IntVar[] b, PrimitiveConstraint[] c) {

    checkInputForNullness(new String[] {"b", "c"}, b, c);
    if (b.length != c.length) {
      throw new IllegalArgumentException(
          "The length of the two lists in Conditional constraints must be equal");
    }
    if (b.length == 0) {
      throw new IllegalArgumentException(
          "Conditional constraint: the lists of conditions and constraints must not be empty");
    }
    for (IntVar be : b) {
      if (be.min() < 0 || be.max() > 1) {
        throw new IllegalArgumentException(
            "Conditional constraint: the elements of condition list must be 0/1 variables, not "
                + be);
      }
    }
    if (b[b.length - 1].min() != 1) {
      throw new IllegalArgumentException(
          "Conditional constraint: the last element of conditions list must be 1 (true)");
    }

    this.queueIndex = 0;
    this.numberId = idNumber.incrementAndGet();

    this.b = Arrays.copyOf(b, b.length);
    this.c = Arrays.copyOf(c, c.length);

    // collect variables of all constraints
    List<Var> vs = new ArrayList<>();
    for (PrimitiveConstraint primitiveConstraint : c) {
      Set<Var> cvs = primitiveConstraint.arguments();
      vs.addAll(cvs);
    }

    setScope(Stream.concat(Arrays.stream(b), vs.stream()));
    queueForward = new QueueForward<>(this.c, arguments());
  }

  /**
   * It constructs a Conditional constraint.
   *
   * @param b 0/1 variables for selection of constraint
   * @param c constraints for selection.
   */
  public Conditional(List<? extends IntVar> b, List<? extends PrimitiveConstraint> c) {
    this(b.toArray(IntVar[]::new), c.toArray(PrimitiveConstraint[]::new));
  }

  @Override
  public void consistency(final Store store) {

    boolean prune = true;

    int i = 0;
    while (prune) {
      while (i < b.length) {
        if (b[i].max() == 0) {
          i++;
        } else {
          break;
        }
      }
      prune = false;

      if (b[i].min() == 1) {
        c[i].consistency(store);

        if (c[i].satisfied()) {
          removeConstraint();
        }
      } else if (c[i].notSatisfied()) {
        b[i].domain.inValue(store.level, b[i], 0);
        prune = true;
      }
    }
  }

  @Override
  public void queueVariable(int level, Var variable) {
    queueForward.queueForward(level, variable);
  }

  /*
   * Informs wheter the constraint is satisfied
   * @return true if constraint is satisfied
   */
  @Override
  public boolean satisfied() {

    int i = 0;
    while (i < b.length) {
      if (b[i].max() == 0) {
        i++;
      } else {
        break;
      }
    }
    return b[i].min() == 1 && c[i].satisfied();
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : Conditional(").append("[");

    for (int i = 0; i < b.length; i++) {
      result.append(b[i]);
      if (i < b.length - 1) {
        result.append(", ");
      }
    }
    result.append("], ");

    for (int i = 0; i < c.length; i++) {
      result.append(c[i]);
      if (i < c.length - 1) {
        result.append(", ");
      }
    }

    result.append("]").append(" )");

    return result.toString();
  }

  @Override
  public Conditional copy(VarMap map) {
    return new Conditional(map.get(b), Copyable.copyOf(c, map));
  }

  @Override
  public boolean canCopy() {
    return Copyable.canCopyAll((Object[]) c);
  }
}
