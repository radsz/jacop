/*
 * TupleUtils.java
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

package org.jacop.util;

import org.jacop.core.IntVar;

/**
 * Util functions for arrays of tuples.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public class TupleUtils {

  int tupleNumber;

  int[][] tuples;

  /**
   * It sorts tuples.
   *
   * @param ts tuples to be sorted.
   */
  public static void sortTuplesWithin(int[][] ts) {

    for (int i = 0; i < ts.length; i++) {

      boolean change = false;

      for (int j = ts.length - 1; j > i; j--) {
        if (!smallerEqualTuple(ts[j - 1], ts[j])) {
          change = true;
          int[] tmp = ts[j - 1];
          ts[j - 1] = ts[j];
          ts[j] = tmp;
        }
      }

      if (!change) {
        break;
      }
    }
  }

  /**
   * It compares tuples.
   *
   * @param left tuple to be compared to.
   * @param right tuple to compar with.
   * @return true if the left tuple is larger than right tuple.
   */
  public static boolean smallerEqualTuple(int[] left, int[] right) {

    if (right.length < left.length) {
      return false;
    }

    if (right.length > left.length) {
      return true;
    }

    for (int i = 0; i < left.length; i++) {
      if (left[i] < right[i]) {
        return true;
      }
      if (left[i] > right[i]) {
        return false;
      }
    }

    return true;
  }

  /**
   * It recordTuples to store so tuples can be reused across multiple extensional constraints. It
   * can potentially save memory.
   *
   * @param ts tuples to be recorded.
   * @return two-dimensional array with tuples.
   */
  public int[][] recordTuples(int[][] ts) {

    int[][] sortedTs = sortTuples(ts);

    if (tuples == null) {
      return recordTuplesIntoEmptyStore(sortedTs);
    }

    InsertPlan plan = buildInsertPlan(sortedTs);
    if (plan.insertNo == 0) {
      return plan.reusedTuples;
    }

    return applyInsertPlan(sortedTs, plan);
  }

  private record InsertPlan(int[] position, boolean[] insert, int insertNo, int[][] reusedTuples) {}

  private InsertPlan buildInsertPlan(int[][] sortedTs) {
    int[] position = new int[sortedTs.length];
    boolean[] insert = new boolean[sortedTs.length];
    int insertNo = 0;
    int[][] reusedTuples = new int[sortedTs.length][];

    for (int i = 0; i < sortedTs.length; i++) {
      position[i] = findPositionForInsert(sortedTs[i]);
      insert[i] =
          !smallerEqualTuple(tuples[position[i]], sortedTs[i])
              || !smallerEqualTuple(sortedTs[i], tuples[position[i]]);
      if (insert[i]) {
        insertNo++;
      } else {
        reusedTuples[i] = tuples[position[i]];
      }
    }
    return new InsertPlan(position, insert, insertNo, reusedTuples);
  }

  private int[][] applyInsertPlan(int[][] sortedTs, InsertPlan plan) {
    int[][] tuplesBeforeExtension = tuples;

    if (tupleNumber + plan.insertNo > tuples.length) {
      tuples = new int[tuples.length * 2][];
    } else {
      tuples = new int[tuples.length][];
    }

    int previousPosition = findFirstInsertIndex(plan.insert);

    System.arraycopy(tuplesBeforeExtension, 0, tuples, 0, plan.position[previousPosition]);

    tuplesBeforeExtension[plan.position[previousPosition]] =
        new int[sortedTs[previousPosition].length];

    System.arraycopy(
        sortedTs[previousPosition],
        0,
        tuplesBeforeExtension[plan.position[previousPosition]],
        0,
        sortedTs[previousPosition].length);

    plan.reusedTuples[previousPosition] = tuplesBeforeExtension[plan.position[previousPosition]];

    int performedInserts = 1;
    for (int i = previousPosition + 1; i < sortedTs.length; i++) {

      if (!plan.insert[i]) {
        continue;
      }

      System.arraycopy(
          tuplesBeforeExtension,
          plan.position[previousPosition],
          tuples,
          plan.position[previousPosition] + performedInserts,
          plan.position[i] - plan.position[previousPosition]);

      tuplesBeforeExtension[plan.position[i] + performedInserts] = new int[sortedTs[i].length];

      System.arraycopy(
          sortedTs[i],
          0,
          tuplesBeforeExtension[plan.position[i] + performedInserts],
          0,
          sortedTs[i].length);

      plan.reusedTuples[i] = tuplesBeforeExtension[plan.position[i] + performedInserts];

      performedInserts++;
      previousPosition = i;
    }

    System.arraycopy(
        tuplesBeforeExtension,
        plan.position[previousPosition],
        tuples,
        plan.position[previousPosition] + performedInserts,
        tupleNumber - plan.position[previousPosition]);

    tupleNumber += performedInserts;

    return plan.reusedTuples;
  }

  private int findFirstInsertIndex(boolean[] insert) {
    for (int i = 0; i < insert.length; i++) {
      if (insert[i]) {
        return i;
      }
    }
    return insert.length;
  }

  private int[][] recordTuplesIntoEmptyStore(int[][] sortedTs) {

    tuples = new int[sortedTs.length][];
    for (int i = 0; i < sortedTs.length; i++) {
      tuples[i] = new int[sortedTs[i].length];
      System.arraycopy(sortedTs[i], 0, tuples[i], 0, sortedTs[i].length);
    }
    tupleNumber = sortedTs.length;

    int[][] reusedTuples = new int[sortedTs.length][];
    System.arraycopy(tuples, 0, reusedTuples, 0, sortedTs.length);

    return reusedTuples;
  }

  /**
   * Searches for the position of the tuple in the tuple list.
   *
   * @param tuple to be compared to.
   * @return position at which the tuple is stored in tuple list array.
   */
  public int findPositionForInsert(int[] tuple) {

    int left = 0;
    int right = tupleNumber;

    int position = (left + right) >> 1;

    while (left + 1 < right) {

      if (smallerEqualTuple(tuples[position], tuple)) {
        left = position;
      } else {
        right = position;
      }

      position = (left + right) >> 1;
    }

    if (smallerEqualTuple(tuple, tuples[left])) {
      return left;
    }

    if (smallerEqualTuple(tuple, tuples[right])) {
      return right;
    }

    return -1;
  }

  /**
   * Sorts the given tuples.
   *
   * @param ts tuples to be sorted.
   * @return sorted tuples.
   */
  public int[][] sortTuples(int[][] ts) {

    int[][] result = new int[ts.length][];

    System.arraycopy(ts, 0, result, 0, ts.length);

    for (int i = 0; i < result.length; i++) {

      boolean change = false;

      for (int j = result.length - 1; j > i; j--) {
        if (!smallerEqualTuple(result[j - 1], result[j])) {
          change = true;
          int[] tmp = result[j - 1];
          result[j - 1] = result[j];
          result[j] = tmp;
        }
      }

      if (!change) {
        break;
      }
    }

    return result;
  }

  /**
   * Checks if tuple1 is strictly smaller than tuple2 in lexicographic order.
   *
   * @param tuple1 the first tuple to compare.
   * @param tuple2 the second tuple to compare.
   * @return true if tuple1 is strictly less than tuple2.
   */
  public static boolean tuplesSmaller(int[] tuple1, int[] tuple2) {
    int arity = tuple1.length;
    for (int i = 0; i < arity && tuple1[i] <= tuple2[i]; i++) {
      if (tuple1[i] < tuple2[i]) {
        return true;
      }
    }
    return false;
  }

  /**
   * Checks if two tuples are equal element by element.
   *
   * @param tuple1 the first tuple to compare.
   * @param tuple2 the second tuple to compare.
   * @return true if all elements of tuple1 and tuple2 are equal.
   */
  public static boolean tuplesEqual(int[] tuple1, int[] tuple2) {
    int arity = tuple1.length;
    for (int i = 0; i < arity; i++) {
      if (tuple1[i] != tuple2[i]) {
        return false;
      }
    }
    return true;
  }

  /**
   * Finds the position of a value in a sorted array using binary search.
   *
   * @param value the value to search for.
   * @param values the sorted array to search in.
   * @return the index of the value in the array, or -1 if not found.
   */
  public static int findValuePosition(int value, int[] values) {
    int left = 0;
    int right = values.length - 1;

    int position = (left + right) >> 1;

    while (left + 1 < right) {
      if (values[position] > value) {
        right = position;
      } else {
        left = position;
      }
      position = (left + right) >> 1;
    }

    if (values[left] == value) {
      return left;
    }

    if (values[right] == value) {
      return right;
    }

    return -1;
  }

  /**
   * Finds the first position where the tuple value is not contained in the corresponding variable's
   * domain.
   *
   * @param t the tuple of values to check.
   * @param list the array of variables whose domains are checked against the tuple.
   * @return the index of the first invalid position, or -1 if all values are valid.
   */
  public static int seekInvalidPosition(int[] t, IntVar[] list) {
    int noVars = list.length;
    for (int i = 0; i < noVars; i++) {
      if (!list[i].domain.contains(t[i])) {
        return i;
      }
    }
    return -1;
  }

  /**
   * Filters tuples to keep only those whose values are all contained in the corresponding variable
   * domains.
   *
   * @param tuples the tuples to filter
   * @param variables the variables whose domains are checked
   * @return array of two elements: [0] = boolean array indicating which tuples are valid, [1] =
   *     count of valid tuples
   */
  public static Object[] filterValidTuples(int[][] tuples, IntVar[] variables) {
    boolean[] valid = new boolean[tuples.length];
    int validCount = 0;

    for (int i = 0; i < tuples.length; i++) {
      int[] tuple = tuples[i];
      valid[i] = true;
      for (int j = 0; j < tuple.length && j < variables.length; j++) {
        if (!variables[j].dom().contains(tuple[j])) {
          valid[i] = false;
          break;
        }
      }
      if (valid[i]) {
        validCount++;
      }
    }

    return new Object[] {valid, validCount};
  }
}
