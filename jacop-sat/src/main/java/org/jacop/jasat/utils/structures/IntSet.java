/*
 * IntSet.java
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

package org.jacop.jasat.utils.structures;

/**
 * An efficient Set for unboxed int. It is just a subclass for the IntTrie, with a more convenient
 * interface (no generics, simpler constructor). It also provides a part of the interface of BitSet.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class IntSet extends IntTrie<IntTrie.SimpleNode> {

  /** Simple initialization of a Set. */
  public IntSet() {
    super(new IntTrie.SimpleNode());
  }

  /**
   * Initializes the set with the given integers.
   *
   * @param toAdd the collection of integers to add
   */
  public IntSet(Iterable<Integer> toAdd) {
    this();
    for (int i : toAdd) {
      add(i);
    }
  }

  /**
   * Sets the bit at the specified index (alias for add).
   *
   * @param i the index to set
   */
  public void set(int i) {
    add(i);
  }

  /**
   * Gets the bit at the specified index (alias for contains).
   *
   * @param i the index to check
   * @return true if the index is in the set
   */
  public boolean get(int i) {
    return contains(i);
  }

  /**
   * Clears the bit at the specified index (alias for remove).
   *
   * @param i the index to clear
   */
  public void clear(int i) {
    remove(i);
  }
}
