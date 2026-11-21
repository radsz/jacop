/*
 * LpColumn.java
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

package org.jacop.constraints.lp;

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;

/**
 * A column of the linear relaxation that is not a variable of the store: the auxiliary 0/1 column
 * {@code [x = v]} of a value encoding that the model has no Boolean for, an arc column of the flow
 * model of a layered graph (an edge of level i labelled v), which is at most {@code [x_i = v]}, or
 * a free column with fixed bounds that belongs to no variable, such as a wire of the sorting
 * network of an all-different ({@link org.jacop.constraints.Linearizations#alldifferentNetwork}).
 * It is never pruned and never searched on. In the simplex its bounds come from the domain of its
 * variable ({@link #lower}, {@link #upper}), or are those it was made with for a free column. The
 * relaxation removes it from every inequality it deduces, at the bound that keeps the inequality
 * valid, so that pruning and its explanations only use variables of the store.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LpColumn extends IntVar {

  private static final AtomicInteger NUMBER = new AtomicInteger();

  private final IntVar variable;
  private final int value;
  private final boolean arc;

  /**
   * Creates the 0/1 column {@code [variable = value]}.
   *
   * @param variable the variable whose value the column indicates
   * @param value the value
   */
  public LpColumn(IntVar variable, int value) {
    this(variable, value, false);
  }

  private LpColumn(IntVar variable, int value, boolean arc) {
    super();
    this.variable = variable;
    this.value = value;
    this.arc = arc;
    id = (arc ? "lp_arc_" : "lp_") + variable.id() + "=" + value + "#" + NUMBER.incrementAndGet();
    domain = new IntervalDomain(0, 1);
    refreshBounds();
  }

  /**
   * Creates a free column with the given bounds, which indicates no value of a variable; the bounds
   * hold for the whole search.
   *
   * @param name the name of the column
   * @param min the lower bound
   * @param max the upper bound
   */
  public LpColumn(String name, int min, int max) {
    super();
    this.variable = null;
    this.value = 0;
    this.arc = false;
    id = "lp_" + name + "#" + NUMBER.incrementAndGet();
    domain = new IntervalDomain(min, max);
    refreshBounds();
  }

  /**
   * Creates the 0/1 arc column of an edge labelled {@code value} of the level of {@code variable}
   * in the flow model of a layered graph: it is at most {@code [variable = value]}, so it is 0 once
   * the value is gone, but it is not 1 when the variable takes the value, since several edges of a
   * level may carry it.
   *
   * @param variable the variable of the level of the edge
   * @param value the label of the edge
   * @return the column
   */
  public static LpColumn arc(IntVar variable, int value) {
    return new LpColumn(variable, value, true);
  }

  /**
   * Tells whether this is an arc column ({@link #arc}) and not the indicator {@code [x = v]}.
   *
   * @return true for an arc column
   */
  public boolean isArc() {
    return arc;
  }

  /**
   * Returns the lower bound the domain of the variable gives the column: 1 for an indicator whose
   * variable is the value, 0 otherwise; for a free column its fixed lower bound.
   *
   * @return the bound
   */
  public int lower() {
    if (variable == null) {
      return min();
    }
    return !arc && variable.singleton(value) ? 1 : 0;
  }

  /**
   * Returns the upper bound the domain of the variable gives the column: 0 once the value is gone,
   * 1 otherwise; for a free column its fixed upper bound.
   *
   * @return the bound
   */
  public int upper() {
    if (variable == null) {
      return max();
    }
    return variable.domain.contains(value) ? 1 : 0;
  }

  /**
   * Tells whether this is a free column, which belongs to no variable.
   *
   * @return true for a free column
   */
  public boolean isFree() {
    return variable == null;
  }

  /**
   * Returns the variable whose value the column indicates.
   *
   * @return the variable, or null for a free column
   */
  public IntVar variable() {
    return variable;
  }

  /**
   * Returns the value the column indicates.
   *
   * @return the value
   */
  public int value() {
    return value;
  }

  /**
   * Returns the 0 or 1 the column has in a solution, given the value of its variable there; for an
   * arc column it is the bound {@code [x = v]} of the arc.
   *
   * @param of the value of the variable
   * @return 1 when it is the value of the column, 0 otherwise
   */
  public int valueIn(int of) {
    return of == value ? 1 : 0;
  }

  /**
   * Returns the column of the same value for a copy of the relaxation, over the copy of its
   * variable.
   *
   * @param copied the copy of the variable
   * @return the new column
   */
  public LpColumn copy(IntVar copied) {
    return new LpColumn(copied, value, arc);
  }

  /**
   * Returns the free column with the same bounds for a copy of the relaxation.
   *
   * @return the new column
   * @throws IllegalStateException for a value column, which {@link #copy(IntVar)} copies
   */
  public LpColumn copy() {
    if (variable != null) {
      throw new IllegalStateException("a value column is copied over the copy of its variable");
    }
    return new LpColumn(id, min(), max());
  }
}
