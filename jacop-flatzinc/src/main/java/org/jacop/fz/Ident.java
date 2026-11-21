/*
 * Ident.java
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

package org.jacop.fz;

import org.jacop.core.IntVar;

/**
 * An identifier of the model, shared by the nodes of the parse tree that name it, with the variable
 * it was last looked up as. The variable is kept for the store it belongs to: {@link
 * Tables#getVariable(ASTScalarFlatExpr)} reads it while the tables are over that store and looks
 * the name up again otherwise (the threads of a portfolio build their stores from copies of one
 * tree, which share the identifiers). The detectors read every constraint item, each looking its
 * variables up by name: those lookups missed the cache and were a quarter of the set-up of MaxSAT
 * 2021 relational-inference ar-2.
 */
final class Ident {

  final String name;

  // the variable the name was last looked up as, or null; a field written whole, so a thread
  // reads a variable a thread looked up or null
  IntVar variable;

  Ident(String name) {
    this.name = name;
  }

  @Override
  public String toString() {
    return name;
  }
}
