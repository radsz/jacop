/*
 * Restriction.java
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

package org.jacop.constraints.table;

import java.util.Arrays;

/**
 * One entry of a hybrid tuple of a {@link HybridTable}. An entry restricts the variable of its
 * column either by a unary condition (any value, a value, a comparison with a value, membership in
 * a set of values) or by a comparison with the variable of another column, possibly shifted by a
 * constant. Hybrid tables are also called smart tables.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class Restriction {

  /** The relations that can compare a column with a value or with another column. */
  public enum Relation {
    /** Less than. */
    LT,
    /** Less than or equal. */
    LE,
    /** Equal. */
    EQ,
    /** Not equal. */
    NE,
    /** Greater than or equal. */
    GE,
    /** Greater than. */
    GT
  }

  /** The kind of a restriction after normalization: LT and GT are turned into LE and GE. */
  enum Kind {
    ANY,
    EQ,
    NE,
    LE,
    GE,
    IN,
    NOT_IN,
    COLUMN
  }

  private static final Restriction ANY_VALUE = new Restriction(Kind.ANY, 0, null, null, -1, 0);

  final Kind kind;

  /** The value of EQ, NE, LE and GE. */
  final int value;

  /** The sorted values without duplicates of IN and NOT_IN. */
  final int[] values;

  /** The relation of a COLUMN restriction. */
  final Relation relation;

  /** The other column of a COLUMN restriction. */
  final int column;

  /** The constant added to the other column of a COLUMN restriction. */
  final int offset;

  private Restriction(
      Kind kind, int value, int[] values, Relation relation, int column, int offset) {
    this.kind = kind;
    this.value = value;
    this.values = values;
    this.relation = relation;
    this.column = column;
    this.offset = offset;
  }

  /**
   * It accepts any value (the wildcard {@code *} of short tables).
   *
   * @return the restriction.
   */
  public static Restriction any() {
    return ANY_VALUE;
  }

  /**
   * It accepts the given value only.
   *
   * @param value the accepted value.
   * @return the restriction.
   */
  public static Restriction eq(int value) {
    return new Restriction(Kind.EQ, value, null, null, -1, 0);
  }

  /**
   * It accepts every value except the given one.
   *
   * @param value the rejected value.
   * @return the restriction.
   */
  public static Restriction ne(int value) {
    return new Restriction(Kind.NE, value, null, null, -1, 0);
  }

  /**
   * It accepts the values smaller than the given one.
   *
   * @param value the bound.
   * @return the restriction.
   */
  public static Restriction lt(int value) {
    return value == Integer.MIN_VALUE ? in() : le(value - 1);
  }

  /**
   * It accepts the values smaller than or equal to the given one.
   *
   * @param value the bound.
   * @return the restriction.
   */
  public static Restriction le(int value) {
    return new Restriction(Kind.LE, value, null, null, -1, 0);
  }

  /**
   * It accepts the values greater than the given one.
   *
   * @param value the bound.
   * @return the restriction.
   */
  public static Restriction gt(int value) {
    return value == Integer.MAX_VALUE ? in() : ge(value + 1);
  }

  /**
   * It accepts the values greater than or equal to the given one.
   *
   * @param value the bound.
   * @return the restriction.
   */
  public static Restriction ge(int value) {
    return new Restriction(Kind.GE, value, null, null, -1, 0);
  }

  /**
   * It compares the column with a value.
   *
   * @param relation the relation.
   * @param value the value on the right-hand side.
   * @return the restriction.
   */
  public static Restriction compare(Relation relation, int value) {
    return switch (relation) {
      case LT -> lt(value);
      case LE -> le(value);
      case EQ -> eq(value);
      case NE -> ne(value);
      case GE -> ge(value);
      case GT -> gt(value);
    };
  }

  /**
   * It accepts the given values only.
   *
   * @param values the accepted values.
   * @return the restriction.
   */
  public static Restriction in(int... values) {
    int[] sorted = Arrays.stream(values).sorted().distinct().toArray();
    if (sorted.length == 1) {
      return eq(sorted[0]);
    }
    return new Restriction(Kind.IN, 0, sorted, null, -1, 0);
  }

  /**
   * It accepts every value except the given ones.
   *
   * @param values the rejected values.
   * @return the restriction.
   */
  public static Restriction notIn(int... values) {
    int[] sorted = Arrays.stream(values).sorted().distinct().toArray();
    if (sorted.length == 0) {
      return ANY_VALUE;
    }
    if (sorted.length == 1) {
      return ne(sorted[0]);
    }
    return new Restriction(Kind.NOT_IN, 0, sorted, null, -1, 0);
  }

  /**
   * It compares the column with another column of the table, x[this] relation x[column].
   *
   * @param relation the relation.
   * @param column the index of the other column.
   * @return the restriction.
   */
  public static Restriction column(Relation relation, int column) {
    return column(relation, column, 0);
  }

  /**
   * It compares the column with another column of the table shifted by a constant, x[this] relation
   * x[column] + offset.
   *
   * @param relation the relation.
   * @param column the index of the other column.
   * @param offset the constant added to the other column.
   * @return the restriction.
   */
  public static Restriction column(Relation relation, int column, int offset) {
    if (relation == null || column < 0) {
      throw new IllegalArgumentException("Restriction needs a relation and a non-negative column");
    }
    return new Restriction(Kind.COLUMN, 0, null, relation, column, offset);
  }

  /**
   * It tells whether the restriction compares its column with another column.
   *
   * @return true for a restriction between two columns.
   */
  public boolean isBinary() {
    return kind == Kind.COLUMN;
  }

  /**
   * It checks a value against a unary restriction. A restriction between two columns accepts every
   * value here.
   *
   * @param v the value.
   * @return true if the value is accepted.
   */
  boolean accepts(int v) {
    return switch (kind) {
      case ANY, COLUMN -> true;
      case EQ -> v == value;
      case NE -> v != value;
      case LE -> v <= value;
      case GE -> v >= value;
      case IN -> Arrays.binarySearch(values, v) >= 0;
      case NOT_IN -> Arrays.binarySearch(values, v) < 0;
    };
  }

  /**
   * It checks whether the values of the two columns satisfy a restriction between two columns.
   *
   * @param v the value of this column.
   * @param w the value of the other column.
   * @return true if the pair is accepted.
   */
  boolean accepts(int v, int w) {
    return holds(relation, v, (long) w + offset);
  }

  static boolean holds(Relation relation, long v, long w) {
    return switch (relation) {
      case LT -> v < w;
      case LE -> v <= w;
      case EQ -> v == w;
      case NE -> v != w;
      case GE -> v >= w;
      case GT -> v > w;
    };
  }

  @Override
  public String toString() {
    return switch (kind) {
      case ANY -> "*";
      case EQ -> Integer.toString(value);
      case NE -> "!=" + value;
      case LE -> "<=" + value;
      case GE -> ">=" + value;
      case IN -> "in" + Arrays.toString(values);
      case NOT_IN -> "notin" + Arrays.toString(values);
      case COLUMN -> {
        String op =
            switch (relation) {
              case LT -> "<";
              case LE -> "<=";
              case EQ -> "=";
              case NE -> "!=";
              case GE -> ">=";
              case GT -> ">";
            };
        String shift = offset > 0 ? "+" + offset : Integer.toString(offset);
        yield op + "c" + column + (offset == 0 ? "" : shift);
      }
    };
  }
}
