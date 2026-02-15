/*
 * AbstractExtensionalVa.java
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

import static org.jacop.util.TupleUtils.findValuePosition;
import static org.jacop.util.TupleUtils.tuplesEqual;
import static org.jacop.util.TupleUtils.tuplesSmaller;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.concurrent.atomic.AtomicInteger;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.util.TupleUtils;

/**
 * Abstract base class for extensional constraints (both support and conflict). Provides shared
 * fields, tuple utility methods, impose-time filtering and indexing, toString, and the core pruning
 * loop.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public abstract class AbstractExtensionalVa extends Constraint
    implements UsesQueueVariable, Stateful {

  static final boolean DEBUG_ALL = false;

  /** It stores variables within this extensional constraint, order does matter. */
  protected final IntVar[] list;

  /**
   * It represents tuples which are supports/conflicts for each of the variables. The first index
   * denotes variable index. The second index denotes value index. The third index denotes tuple.
   */
  int[][][][] tuples;

  /** It represents values which are present in tuples for a variable. */
  int[][] values;

  /** It specifies the tuples given in the constructor. */
  int[][] tuplesFromConstructor;

  /**
   * Constructs the base extensional constraint with list and tuples.
   *
   * @param idNum the atomic id counter for the concrete type
   * @param list the constraint scope
   * @param tuples the support/conflict tuples
   */
  protected AbstractExtensionalVa(AtomicInteger idNum, IntVar[] list, int[][] tuples) {
    checkInputForNullness("list", list);
    this.list = Arrays.copyOf(list, list.length);
    this.tuplesFromConstructor = tuples;
    numberId = idNum.incrementAndGet();
    setScope(list);
  }

  /**
   * Constructs the base extensional constraint with list only (tuples set later).
   *
   * @param idNum the atomic id counter for the concrete type
   * @param list the constraint scope
   */
  protected AbstractExtensionalVa(AtomicInteger idNum, IntVar[] list) {
    this.list = new IntVar[list.length];
    System.arraycopy(list, 0, this.list, 0, list.length);
    numberId = idNum.incrementAndGet();
    setScope(list);
  }

  /**
   * Filters tuplesFromConstructor to keep only those whose values are in current variable domains,
   * then builds the indexed tuples and values arrays.
   *
   * @param store the constraint store
   */
  protected void filterAndIndexTuples(Store store) {
    debugLogVariables();

    Object[] filterResult = TupleUtils.filterValidTuples(tuplesFromConstructor, list);
    @SuppressWarnings("unchecked")
    boolean[] stillValid = (boolean[]) filterResult[0];
    int noValid = (Integer) filterResult[1];

    debugLogValidTuples(stillValid, noValid);

    tuplesFromConstructor = shrinkToValidTuples(stillValid, noValid);

    this.tuples = new int[list.length][][][];
    this.values = new int[list.length][];
    int[][] supportCount = new int[list.length][];

    for (int i = 0; i < list.length; i++) {
      buildTuplesAndValuesForVariable(i, supportCount);
    }
  }

  private void debugLogVariables() {
    if (DEBUG_ALL) {
      for (Var v : list) {
        log.debug("Variable {}", v);
      }
    }
  }

  private void debugLogValidTuples(boolean[] stillValid, int noValid) {
    if (DEBUG_ALL) {
      int i = 0;
      for (int[] t : tuplesFromConstructor) {
        log.debug("tuple for analysis{}", Arrays.toString(t));
        if (!stillValid[i]) {
          log.debug("Not valid {}", Arrays.toString(t));
        }
        i++;
      }
      log.debug("No. still valid {}", noValid);
    }
  }

  private int[][] shrinkToValidTuples(boolean[] stillValid, int noValid) {
    int[][] temp4Shrinking = new int[noValid][];
    int i = 0;
    int k = 0;
    for (int[] t : tuplesFromConstructor) {
      if (stillValid[k]) {
        temp4Shrinking[i] = t;
        i++;
        if (DEBUG_ALL) {
          log.debug("Still valid {}", Arrays.toString(t));
        }
      }
      k++;
    }
    return temp4Shrinking;
  }

  private void buildTuplesAndValuesForVariable(int i, int[][] supportCount) {
    Map<Integer, Integer> val = new HashMap<>();
    for (int[] t : tuplesFromConstructor) {
      Integer value = t[i];
      val.merge(value, 1, Integer::sum);
    }
    if (DEBUG_ALL) {
      log.debug("values {}", val.keySet());
    }
    PriorityQueue<Integer> sortedVal = new PriorityQueue<>(val.keySet());
    if (DEBUG_ALL) {
      log.debug("Sorted val size {}", sortedVal.size());
    }
    values[i] = new int[sortedVal.size()];
    supportCount[i] = new int[sortedVal.size()];
    this.tuples[i] = new int[sortedVal.size()][][];
    if (DEBUG_ALL) {
      log.debug("values length {}", values[i].length);
    }
    for (int j = 0; j < values[i].length; j++) {
      if (DEBUG_ALL) {
        log.debug("sortedVal {}", sortedVal);
      }
      values[i][j] = sortedVal.poll();
      supportCount[i][j] = val.get(values[i][j]);
      this.tuples[i][j] = new int[supportCount[i][j]][];
    }
    for (int[] t : tuplesFromConstructor) {
      int value = t[i];
      int position = findPosition(value, values[i]);
      this.tuples[i][position][--supportCount[i][position]] = t;
    }
    for (int j = 0; j < tuples[i].length; j++) {
      TupleUtils.sortTuplesWithin(tuples[i][j]);
    }
  }

  /**
   * Core pruning loop: for each variable and each value, seeks support; removes values without
   * support.
   *
   * @param store the constraint store
   */
  protected void pruneUnsupported(Store store) {
    boolean pruned = true;

    while (pruned) {
      pruned = false;
      for (int varPosition = 0; varPosition < list.length; varPosition++) {
        pruned = pruneUnsupportedForVariable(store, varPosition) || pruned;
      }
    }
  }

  private boolean pruneUnsupportedForVariable(Store store, int varPosition) {
    boolean pruned = false;
    for (ValueEnumeration enumer = list[varPosition].domain.valueEnumeration();
        enumer.hasMoreElements(); ) {

      int value = enumer.nextElement();

      if (DEBUG_ALL) {
        log.debug("Seeking support for {} and value {}", list[varPosition], value);
      }
      int[] t = seekSupportVa(varPosition, value);

      if (DEBUG_ALL) {
        log.debug("Found support? {}", t != null);
      }

      if (t == null) {
        list[varPosition].domain.inComplement(store.level, list[varPosition], value);
        pruned = true;
      }
    }
    return pruned;
  }

  /**
   * Seeks a support tuple for a given variable-value pair.
   *
   * @param varPosition position of the variable
   * @param value value for which support is sought
   * @return a support tuple, or null if none exists
   */
  public abstract int[] seekSupportVa(int varPosition, int value);

  /**
   * Finds the position of a value in a sorted array of values.
   *
   * @param value the value to find
   * @param values the sorted array of values
   * @return the position of the value, or -1 if not found
   */
  protected int findPosition(int value, int[] values) {
    return findValuePosition(value, values);
  }

  /**
   * Compares two tuples lexicographically to determine if the first is smaller than the second.
   *
   * @param tuple1 the first tuple
   * @param tuple2 the second tuple
   * @return true if tuple1 is lexicographically smaller than tuple2
   */
  boolean smaller(int[] tuple1, int[] tuple2) {
    return tuplesSmaller(tuple1, tuple2);
  }

  /**
   * Checks if two tuples are equal by comparing all their elements.
   *
   * @param tuple1 the first tuple
   * @param tuple2 the second tuple
   * @return true if tuples are equal, false otherwise
   */
  boolean arraysEqual(int[] tuple1, int[] tuple2) {
    return tuplesEqual(tuple1, tuple2);
  }

  /**
   * Finds the first position in a tuple where the value is not in the corresponding variable's
   * domain.
   *
   * @param t the tuple to check
   * @return the position of the first invalid value, or -1 if all values are valid
   */
  public int seekInvalidPosition(int[] t) {
    return TupleUtils.seekInvalidPosition(t, list);
  }

  @Override
  public String toString() {

    StringBuilder tupleString = new StringBuilder();
    tupleString.append(id());
    tupleString.append("(");

    for (int i = 0; i < list.length; i++) {
      tupleString.append(list[i].toString());
      if (i + 1 < list.length) {
        tupleString.append(" ");
      }
    }

    tupleString.append(")");

    if (tuplesFromConstructor != null) {
      int[][] subset = tuplesFromConstructor;
      sortSubsetTuples(subset);
      appendTupleSubset(tupleString, subset);
      tupleString.append(")");
      return tupleString.toString();
    }

    return tupleString.toString();
  }

  private void sortSubsetTuples(int[][] subset) {
    for (int p1 = 0; p1 < subset.length; p1++) {
      for (int p2 = subset.length - 1; p2 > p1; p2--) {
        if (smaller(subset[p2], subset[p2 - 1])) {
          int[] temp = subset[p2];
          subset[p2] = subset[p2 - 1];
          subset[p2 - 1] = temp;
        }
      }
    }
  }

  private void appendTupleSubset(StringBuilder sb, int[][] subset) {
    for (int p1 = 0; p1 < subset.length; p1++) {
      for (int p2 = 0; p2 < subset[p1].length; p2++) {
        sb.append(subset[p1][p2]);
        if (p2 != subset[p1].length - 1) {
          sb.append(" ");
        }
      }

      if (p1 != subset.length - 1) {
        sb.append("|");
      }
    }
  }
}
