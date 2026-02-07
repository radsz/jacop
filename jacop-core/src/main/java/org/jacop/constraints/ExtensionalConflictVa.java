/*
 * ExtensionalConflictVa.java
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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.concurrent.atomic.AtomicInteger;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.util.TupleUtils;

/**
 * Extensional constraint assures that none of the tuples explicitly given is enforced in the
 * relation.
 *
 * <p>This implementation tries to balance the usage of memory versus time efficiency.
 *
 * @author Radoslaw Szymanek
 * @version 4.10
 */
@Slf4j
public class ExtensionalConflictVa extends Constraint implements UsesQueueVariable, Stateful {

  static final boolean debugAll = false;

  static final boolean debugPruning = false;

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It stores variables within this extensional constraint, order does matter. */
  public final IntVar[] list;

  final LinkedHashSet<Var> variableQueue = new LinkedHashSet<>();
  final int[] tuple;

  /** It specifies the tuples given in the constructor. */
  public int[][] tuplesFromConstructor;

  int numberTuples;
  Store store;

  /**
   * It represents tuples which are supports for each of the variables. The first index denotes
   * variable index. The second index denotes value index. The third index denotes tuple.
   */
  int[][][][] tuples;

  /** It represents values which are supported for a variable. */
  int[][] values;

  int[][][] lastofsequence;
  int[][][] supports;
  private boolean satisfiedAlreadyAtImposition;

  /**
   * Constructor stores reference to tuples until imposition, any changes to tuples parameter will
   * be reflected in the constraint behavior. Changes to tuples should not performed under any
   * circumstances. The tuples array is not copied to save memory and time.
   *
   * @param list list of variables for the conflict constraint
   * @param tuples list of forbidden tuples
   */
  public ExtensionalConflictVa(IntVar[] list, int[][] tuples) {

    checkInputForNullness("list", list);

    this.list = Arrays.copyOf(list, list.length);
    supports = new int[list.length][][];
    tuple = new int[list.length];
    tuplesFromConstructor = tuples;

    numberId = idNumber.incrementAndGet();
    setScope(list);
  }

  /**
   * The constructor does not create local copy of tuples array. Any changes to this array will
   * reflect on constraint behavior. Most probably incorrect as other data structures will not
   * change accordingly.
   *
   * @param variables the scope of the extensional conflict constraint.
   * @param tuples the conflict (forbidden) tuples for that constraint.
   */
  public ExtensionalConflictVa(List<? extends IntVar> variables, int[][] tuples) {
    this(variables.toArray(new IntVar[0]), tuples);
  }

  /**
   * It seeks support tuple for a given variable and its value.
   *
   * @param varPosition variable for which the support is seeked.
   * @param value value of the variable for which support is seeked.
   * @return support tuple supporting varPosition-value pair.
   */
  public int[] seekSupportVa(int varPosition, int value) {

    if (debugAll) {
      log.debug("Seeking support for {} and value {}", list[varPosition], value);
    }

    int[] t = tuple;
    int pos = findPosition(value, values[varPosition]);

    if (pos == -1) {
      return setFirstValid(varPosition, value);
    }

    try {
      if (supports[varPosition][pos] != null) {
        System.arraycopy(supports[varPosition][pos], 0, t, 0, list.length);
      } else {
        t = setFirstValid(varPosition, value);
      }
    } catch (Exception _) {
      t = setFirstValid(varPosition, value);
    }

    assert t != null : " First valid tuple can not be null ";

    int invalidPosition;

    int[][] tuplesVarValue = tuples[varPosition][pos];
    int[] lastofsequenceVarValue = lastofsequence[varPosition][pos];

    while (true) {
      // find if t is disallowed

      int position = isDisallowed(varPosition, value, t);
      if (position == -1) {
        recordSupport(varPosition, value, t);
        return t;
      }

      // finds the last of sequence of disallowed tuples from the
      // convex.

      if (lastofsequenceVarValue[position] != position) {
        System.arraycopy(tuplesVarValue[lastofsequenceVarValue[position]], 0, t, 0, list.length);
      }

      invalidPosition = seekInvalidPosition(t);

      if (invalidPosition == -1) {
        int i = list.length - 1;
        for (; i >= 0; i--) {
          if (i != varPosition) {
            if (t[i] == list[i].max()) {
              t[i] = list[i].min();
            } else {
              t[i] = list[i].domain.nextValue(t[i]);
              break;
            }
          }
        }
        if (i == -1) {
          return null;
        }
      } else {
        for (int i = invalidPosition + 1; i < list.length; i++) {
          if (i != varPosition) {
            t[i] = list[i].min();
          }
        }
        boolean cont = false;
        for (int i = invalidPosition; i >= 0; i--) {
          if (i != varPosition) {
            if (t[i] >= list[i].max()) {
              t[i] = list[i].min();
            } else {
              t[i] = list[i].domain.nextValue(t[i]);
              cont = true;
              break;
            }
          }
        }
        if (!cont) {
          return null;
        }
      }
    }
  }

  /**
   * Records a support tuple for a given variable-value pair to optimize future support searches.
   *
   * @param varPosition the position of the variable
   * @param value the value for which support is recorded
   * @param t the support tuple to record
   */
  private void recordSupport(int varPosition, int value, int[] t) {

    int pos = findPosition(value, values[varPosition]);

    int[][] supports4variable = supports[varPosition];

    if (supports4variable == null) {
      supports4variable = new int[values[varPosition].length][];
      supports4variable[pos] = new int[list.length];
      System.arraycopy(t, 0, supports4variable[pos], 0, list.length);
    } else {
      if (supports4variable[pos] == null) {
        supports4variable[pos] = new int[list.length];
      }
      System.arraycopy(t, 0, supports4variable[pos], 0, list.length);
    }
  }

  /**
   * It computes the first valid tuple given restriction that a variable will be equal to a given
   * value.
   *
   * @param varPosition the position of the variable.
   * @param value the value of the variable.
   * @return the smallest valid tuple supporting varPosition-value pair.
   */
  public int[] setFirstValid(int varPosition, int value) {

    int[] t = tuple;

    int noVars = list.length;
    for (int i = 0; i < noVars; i++) {
      t[i] = list[i].min();
    }

    t[varPosition] = value;

    return t;
  }

  /**
   * It returns the position of disallowed tuple in the array of tuples for a given variable-value
   * pair.
   *
   * @param varPosition variable for which we search for the forbidden tuple.
   * @param value value for which we search for the forbidden tuple.
   * @param t tuple which we check for forbidness.
   * @return position of the forbidden tuple, -1 if it is not forbidden.
   */
  public int isDisallowed(int varPosition, int value, int[] t) {

    if (debugAll) {
      log.debug("variable {} position {} value {}", list[varPosition], varPosition, value);
    }

    int[][] tuplesForGivenVariableValuePair =
        tuples[varPosition][findPosition(value, values[varPosition])];

    int left = 0;
    int right = tuplesForGivenVariableValuePair.length - 1;

    int position = (left + right) >> 1;

    while (!(left + 1 >= right)) {

      if (smaller(t, tuplesForGivenVariableValuePair[position])) {
        right = position;
      } else {
        left = position;
      }

      position = (left + right) >> 1;
    }

    if (left != right) {
      if (equal(t, tuplesForGivenVariableValuePair[left])) {
        return left;
      }

      if (equal(t, tuplesForGivenVariableValuePair[right])) {
        return right;
      }
    } else {

      if (equal(t, tuplesForGivenVariableValuePair[left])) {
        return left;
      }
    }

    return -1;
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

  /**
   * It puts back tuples which have lost their support status at the level which is being removed.
   */
  @Override
  public void removeLevel(int level) {

    // backtracking has occurred (removeLevel) therefore
    // restart tuples can not be reused.
    supports = new int[list.length][][];
    variableQueue.clear();
  }

  @Override
  public void consistency(Store store) {

    if (debugAll) {
      log.debug("Begin {}", this);
    }

    if (satisfiedAlreadyAtImposition) {
      return;
    }

    boolean pruned = true;

    while (pruned) {

      pruned = false;
      // For each variable
      for (int varPosition = 0; varPosition < list.length; varPosition++) {
        // for each value

        for (ValueEnumeration enumer = list[varPosition].domain.valueEnumeration();
            enumer.hasMoreElements(); ) {

          int value = enumer.nextElement();

          if (debugAll) {
            log.debug("Seeking support for {} and value {}", list[varPosition], value);
          }
          int[] t = seekSupportVa(varPosition, value);

          if (debugAll) {
            log.debug("Found support? {}", t != null);
          }

          if (t == null) {
            list[varPosition].domain.inComplement(store.level, list[varPosition], value);
            // store.inComplement(x[varPosition], value);
            pruned = true;
          }
        }
      }
    }

    if (debugAll) {
      log.debug("End {}", this);
    }
  }

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

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public void impose(Store store) {

    super.impose(store);
    this.store = store;

    if (debugAll) {
      for (Var var : list) {
        log.debug("Variable {}", var);
      }
    }

    // TO DO, adjust (even simplify) all internal data structures
    // to current domains of variables.
    // filter which ignores all tuples which already are not supports.

    boolean[] stillConflict = new boolean[tuplesFromConstructor.length];

    int noConflicts = 0;

    int i = 0;

    for (int[] t : tuplesFromConstructor) {

      stillConflict[i] = true;

      int j = 0;

      if (debugAll) {
        log.debug("conflict for analysis{}", Arrays.toString(t));
      }

      for (int val : t) {

        if (!list[j].dom().contains(val)) {
          // if (!Domain.domain.contains(x[j].dom(), val)) {
          stillConflict[i] = false;
          break;
        }

        j++;
      }

      if (stillConflict[i]) {
        noConflicts++;
      }

      if (debugAll && !stillConflict[i]) {
        log.debug("Not support {}", Arrays.toString(t));
      }

      i++;
    }

    if (debugAll) {
      log.debug("No. still conflicts {}", noConflicts);
    }

    int[][] temp4Shrinking = new int[noConflicts][];

    i = 0;
    int k = 0;

    for (int[] t : tuplesFromConstructor) {

      if (stillConflict[k]) {
        temp4Shrinking[i] = t;
        i++;

        if (debugAll) {
          log.debug("Still support {}", Arrays.toString(t));
        }
      }

      k++;
    }

    // Only still conflicts are kept.

    tuplesFromConstructor = temp4Shrinking;

    numberTuples = tuplesFromConstructor.length;

    // TO DO, just store parameters for later use in impose
    // function, move all code below to impose function.

    this.tuples = new int[list.length][][][];
    this.values = new int[list.length][];

    lastofsequence = new int[list.length][][];

    int[][] supportCount = new int[list.length][];

    for (i = 0; i < list.length; i++) {

      Map<Integer, Integer> val = new HashMap<>();

      for (int[] t : tuplesFromConstructor) {

        Integer value = t[i];

        val.merge(value, 1, Integer::sum);
      }

      if (debugAll) {
        log.debug("values {}", val.keySet());
      }

      PriorityQueue<Integer> sortedVal = new PriorityQueue<>(val.keySet());

      if (debugAll) {
        log.debug("Sorted val size {}", sortedVal.size());
      }

      values[i] = new int[sortedVal.size()];
      supportCount[i] = new int[sortedVal.size()];
      this.tuples[i] = new int[sortedVal.size()][][];

      if (debugAll) {
        log.debug("values length {}", values[i].length);
      }

      for (int j = 0; j < values[i].length; j++) {

        if (debugAll) {
          log.debug("sortedVal {}", sortedVal);
        }

        values[i][j] = sortedVal.poll();
        supportCount[i][j] = val.get(values[i][j]);
        this.tuples[i][j] = new int[supportCount[i][j]][];
      }

      //     int m = 0;
      for (int[] t : tuplesFromConstructor) {

        int value = t[i];
        int position = findPosition(value, values[i]);

        this.tuples[i][position][--supportCount[i][position]] = t;
        //       m++;

      }

      // @todo, check & improve sorting functionality (possibly reuse existing sorting
      // functionality).
      for (int j = 0; j < tuples[i].length; j++) {
        TupleUtils.sortTuplesWithin(tuples[i][j]);
      }

      lastofsequence[i] = new int[tuples[i].length][];

      // compute lastOfSequence for each i,j and tuple.
      // i - for each variable
      for (int j = 0; j < tuples[i].length; j++) { // for each value
        lastofsequence[i][j] = new int[tuples[i][j].length];
        for (int l = 0; l < tuples[i][j].length; l++) { // for each tuple
          lastofsequence[i][j][l] = computeLastOfSequence(tuples[i][j], i, l);
        }
      }
    }

    if (tuplesFromConstructor.length == 0) {
      satisfiedAlreadyAtImposition = true;
    }

    tuplesFromConstructor = null;

    store.raiseLevelBeforeConsistency = true;
  }

  /**
   * Computes the last tuple in a sequence of consecutive forbidden tuples. This optimization allows
   * skipping over sequences of forbidden tuples during support search.
   *
   * @param is the array of forbidden tuples
   * @param posVar the position of the variable being considered
   * @param l the starting position in the tuple array
   * @return the index of the last tuple in the consecutive sequence
   */
  private int computeLastOfSequence(int[][] is, int posVar, int l) {

    int[] t = tuple;

    System.arraycopy(is[l], 0, t, 0, list.length);

    while (l + 1 < is.length) {

      for (int i = list.length - 1; i >= 0; i--) {
        if (i != posVar) {
          if (t[i] >= list[i].max()) {
            t[i] = list[i].min();
          } else {
            t[i] = list[i].domain.nextValue(t[i]);
            break;
          }
        }
      }

      if (!equal(is[l + 1], t)) {
        return l;
      } else {

        System.arraycopy(is[++l], 0, t, 0, list.length);
      }
    }

    return l;
  }

  @Override
  public void queueVariable(int level, Var var) {

    if (debugAll) {
      log.debug("Var {} {}", var, ((IntVar) var).recentDomainPruning());
    }

    variableQueue.add(var);
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
  boolean equal(int[] tuple1, int[] tuple2) {
    return tuplesEqual(tuple1, tuple2);
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

      for (int p1 = 0; p1 < subset.length; p1++) {
        for (int p2 = subset.length - 1; p2 > p1; p2--) {
          if (smaller(subset[p2], subset[p2 - 1])) {
            int[] temp = subset[p2];
            subset[p2] = subset[p2 - 1];
            subset[p2 - 1] = temp;
          }
        }
      }

      for (int p1 = 0; p1 < subset.length; p1++) {
        for (int p2 = 0; p2 < subset[p1].length; p2++) {

          tupleString.append(subset[p1][p2]);

          if (p2 != subset[p1].length - 1) {
            tupleString.append(" ");
          }
        }

        if (p1 != subset.length - 1) {
          tupleString.append("|");
        }
      }

      tupleString.append(")");
      return tupleString.toString();
    }

    return tupleString.toString();
  }
}
