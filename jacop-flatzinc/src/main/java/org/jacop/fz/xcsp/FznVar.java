/*
 * FznVar.java
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
 * preservation of specified reasonable legal notices and author attributions
 * in material modified versions of this work.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.xcsp;

/**
 * A variable of the FlatZinc model the XCSP3 reader writes: an XCSP3 variable or one the reader
 * introduces. A 0/1 XCSP3 variable becomes a FlatZinc {@code var bool}, as in the MiniZinc route.
 */
final class FznVar {

  final int id;
  final String name;
  final boolean bool;

  /** The values; for a Boolean variable a subset of {0, 1}. */
  Dom dom;

  /** True for a variable the reader introduced. */
  final boolean introduced;

  /** True when a constraint defines the variable (FlatZinc {@code is_defined_var}). */
  boolean defined;

  /** The 0/1 integer variable equal to this Boolean variable, or null. */
  FznVar intView;

  /** The negation of this Boolean variable, or null. */
  FznVar notView;

  /** The Boolean variable equal to this 0/1 integer variable, or null. */
  FznVar boolView;

  FznVar(int id, String name, boolean bool, Dom dom, boolean introduced) {
    this.id = id;
    this.name = name;
    this.bool = bool;
    this.dom = dom;
    this.introduced = introduced;
  }

  long min() {
    return dom.min();
  }

  long max() {
    return dom.max();
  }

  @Override
  public String toString() {
    return name;
  }
}
