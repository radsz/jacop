/*
 * PackedInts.java
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

import java.util.Arrays;

/**
 * The int literals of an array literal while it is parsed. They are kept in one int[] as long as
 * every element is an int literal, and the array literal then has them as packed children (see
 * {@link SimpleNode#packedInts()}) instead of one node each. At the first element of another kind
 * the literals read so far become nodes, and so do the later ones.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class PackedInts {

  private int[] values = new int[16];

  private int size;

  private boolean unpacked;

  /**
   * It adds an int literal element.
   *
   * @param value the value of the literal
   * @param tree the parser stack the element nodes go to once the elements are not all ints
   */
  void add(int value, JJTParserState tree) {
    if (unpacked) {
      tree.pushNode(SimpleNode.intLiteral(value));
      return;
    }
    if (size == values.length) {
      values = Arrays.copyOf(values, 2 * size);
    }
    values[size++] = value;
  }

  /**
   * It turns the int literals read so far into nodes, before an element of another kind.
   *
   * @param tree the parser stack the nodes go to
   */
  void unpack(JJTParserState tree) {
    if (unpacked) {
      return;
    }
    for (int i = 0; i < size; i++) {
      tree.pushNode(SimpleNode.intLiteral(values[i]));
    }
    unpacked = true;
    values = null;
  }

  /**
   * It gives the array literal its packed children when every element was an int literal.
   *
   * @param array the array literal node
   */
  void close(SimpleNode array) {
    if (!unpacked && size > 0) {
      array.setPackedInts(Arrays.copyOf(values, size));
    }
    values = null;
  }
}
