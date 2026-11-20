/*
 * ScalarName.java
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
 * in accordance with Section 7 of this License.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz;

import org.jacop.core.IntVar;

/**
 * The identifier of a scalar expression of the parse tree, shared by every expression that names
 * it, with what the tables of the model last said it denotes. The passes of the FlatZinc front end
 * read the variables of every constraint again and again (about thirty detectors, each over the
 * whole model): on ma-path-finding ins_g32_p20_a10 (MiniZinc Challenge 2022, 1.6 million
 * constraints) the look-ups of names in the tables took a quarter of the 105 s the front end took,
 * mostly cache misses in a hash table of 1.6 million names and in the table of aliases. An
 * expression whose identifier has been looked up once keeps this object instead of the string, and
 * the next look-up is two reads while the tables have not changed since.
 */
final class ScalarName {

  /** What the tables said the name denotes, with the stamp of the tables at that time. */
  record Resolved(long stamp, IntVar variable, boolean array) {}

  /** The identifier. */
  final String ident;

  // replaced as a whole, so a thread that reads it sees a stamp and a variable that belong together
  volatile Resolved resolved;

  ScalarName(String ident) {
    this.ident = ident;
  }
}
