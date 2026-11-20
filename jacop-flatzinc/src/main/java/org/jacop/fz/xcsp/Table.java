/*
 * Table.java
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

import java.util.Arrays;

/**
 * The tuples of an XCSP3 {@code supports} or {@code conflicts} element, parsed from the text as it
 * streams in (Inglenook of XCSP 2026 has 19 million pairs on one line), or the values and ranges of
 * a unary one. A star is {@link #STAR}.
 */
final class Table {

  static final int STAR = Integer.MIN_VALUE;

  /** Cells, row after row; for a unary table the pairs lo, hi of its ranges. */
  int[] cells = new int[16];

  int size;
  int arity = -1;
  boolean starred;

  /** True when the text has no tuples, only values and ranges. */
  boolean unary;

  /** True for conflicts. */
  final boolean negative;

  /** The FlatZinc parameter holding the cells, once written; keyed by its star value. */
  String param;

  long paramStar;

  private long hash = 1;

  // the characters of the number or range being read
  private final char[] token = new char[64];
  private int tokenLength;
  private boolean inTuple;
  private int tupleStart;

  Table(boolean negative) {
    this.negative = negative;
  }

  int rows() {
    return arity <= 0 ? 0 : size / arity;
  }

  private void push(int v) {
    if (size == cells.length) {
      cells = Arrays.copyOf(cells, Math.max(16, (int) Math.min(Integer.MAX_VALUE - 8, 2L * size)));
    }
    cells[size++] = v;
    hash = 31 * hash + v;
  }

  private static int checked(long v) {
    if (v < Integer.MIN_VALUE + 1 || v > Integer.MAX_VALUE) {
      return v < 0 ? Integer.MIN_VALUE + 1 : Integer.MAX_VALUE;
    }
    return (int) v;
  }

  /** Feeds a chunk of the element's text. */
  void feed(char[] text, int start, int length) {
    for (int i = start; i < start + length; i++) {
      char c = text[i];
      if (c >= '0' && c <= '9'
          || c == '-'
          || c == '+'
          || c == '.'
          || c == 'i'
          || c == 'n'
          || c == 'f') {
        if (tokenLength == token.length) {
          throw new XcspException("number too long in table");
        }
        token[tokenLength++] = c;
        continue;
      }
      endToken();
      switch (c) {
        case '(' -> {
          inTuple = true;
          tupleStart = size;
        }
        case ')' -> {
          int a = size - tupleStart;
          if (arity < 0) {
            arity = a;
          } else if (arity != a) {
            throw new XcspException("tuples of different arities in a table");
          }
          inTuple = false;
        }
        case '*' -> {
          push(STAR);
          starred = true;
        }
        default -> {
          // ',' and whitespace separate items
        }
      }
    }
  }

  private long parse(int from, int to) {
    String t = new String(token, from, to - from);
    if (t.equals("+inf") || t.equals("inf")) {
      return Long.MAX_VALUE;
    }
    if (t.equals("-inf")) {
      return Long.MIN_VALUE;
    }
    try {
      return Long.parseLong(t.startsWith("+") ? t.substring(1) : t);
    } catch (NumberFormatException e) {
      throw new XcspException("bad integer '" + t + "' in table");
    }
  }

  private void endToken() {
    if (tokenLength == 0) {
      return;
    }
    int dots = -1;
    for (int i = 0; i + 1 < tokenLength; i++) {
      if (token[i] == '.' && token[i + 1] == '.') {
        dots = i;
        break;
      }
    }
    if (inTuple) {
      if (dots >= 0) {
        throw new XcspException("range in a tuple");
      }
      push(checked(parse(0, tokenLength)));
    } else {
      unary = true;
      long lo = dots >= 0 ? parse(0, dots) : parse(0, tokenLength);
      long hi = dots >= 0 ? parse(dots + 2, tokenLength) : lo;
      push(checked(lo));
      push(checked(hi));
    }
    tokenLength = 0;
  }

  /** Ends the text. */
  void end() {
    endToken();
    if (unary) {
      arity = 1;
    }
    if (arity < 0) {
      arity = 0;
    }
    cells = Arrays.copyOf(cells, size);
  }

  /** The values of a unary table. */
  Dom values() {
    long[] lo = new long[size / 2];
    Dom d = Dom.EMPTY;
    Dom.Builder b = new Dom.Builder();
    boolean sorted = true;
    for (int i = 0; i + 1 < size; i += 2) {
      if (i > 0 && cells[i] <= cells[i - 1]) {
        sorted = false;
      }
      lo[i / 2] = cells[i];
    }
    if (sorted) {
      for (int i = 0; i + 1 < size; i += 2) {
        b.add(cells[i], cells[i + 1]);
      }
      return b.build();
    }
    for (int i = 0; i + 1 < size; i += 2) {
      d = d.union(Dom.range(cells[i], cells[i + 1]));
    }
    return d;
  }

  /** A key of the content. */
  String key() {
    return (negative ? "N" : "P") + arity + ":" + size + ":" + hash;
  }

  boolean sameCells(Table o) {
    return o.size == size && o.arity == arity && Arrays.equals(cells, 0, size, o.cells, 0, size);
  }
}
