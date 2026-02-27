/*
 * ExtensionalSupportStr.java
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

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.Arrays;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;
import org.jacop.util.IndexDomainView;
import org.jacop.util.TupleUtils;

/**
 * Extensional constraint assures that one of the tuples is enforced in the relation.
 *
 * <p>This implementation uses technique developed/improved by Christophe Lecoutre. Paper presented
 * at CP2008. We would like to thank him for making his code available, which helped to create our
 * own version of this algorithm.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class ExtensionalSupportStr extends Constraint implements UsesQueueVariable, Stateful {

  static final boolean DEBUG_ALL = false;
  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It stores variables within this extensional constraint, order does matter. */
  private final IntVar[] list;

  /** It specifies if the tuples previously removed are re-inserted at the beginning. */
  private final boolean reinsertBefore;

  /** It specifies if the residues are moved at the beginning of the list. */
  private final boolean residuesBefore;

  final IndexDomainView[] views;

  /** It specifies the tuples. */
  private int[][] tuples;

  /**
   * Gives the position of the first tuple (in the current list) or -1 if the current list is empty.
   */
  private int first;

  /**
   * Gives the position of the last tuple (in the current list) or -1 if the current list is empty.
   */
  private int last;

  /** Gives the position of the next tuple wrt the position given in index, or -1. */
  private int[] nexts;

  /** Gives the first position of the eliminated tuple at a given level. */
  private TimeStamp<Integer> headsOfEliminatedTuples;

  /** Gives the last position of the eliminated tuple at a given level. */
  private TimeStamp<Integer> tailsOfEliminatedTuples;

  /** The number of variable-value pairs which need to have support. */
  private int nbGlobalValuesToBeSupported;

  /** The number of variable-value pairs which need to have support per variable. */
  private int[] nbValuesToBeSupported; // ID = variable position

  /** It stores the position of the first residue. */
  private int firstResidue;

  /** It stores the position of the last residue. */
  private int lastResidue;

  /**
   * It specifies the number of variables for which validity check within a tuple must be performed.
   */
  private int nbValidityVariables;

  /** The positions of the variables for which validity of any tuple must be checked. */
  private int[] validityVariablePositions;

  /**
   * It specifies the current number of variables for which it is required to check if their values
   * from the domains are supported.
   */
  private int nbSupportsVariables;

  /**
   * The positions of the variables for which GAC must be checked. It does not contain variables
   * which were singletons in previous invocation of the consistency function.
   */
  private int[] supportsVariablePositions;

  /** It specifies the mapping of the variable into its index. */
  private Map<Var, Integer> varToIndex;

  /** It specifies the position of the last assigned variable. */
  private int lastAssignedVariablePosition = -1;

  /** It specifies if there was no first consistency check yet. */
  private boolean firstConsistencyCheck = true;

  /**
   * It specifies if there was a backtrack and no yet consistency function execution after
   * backtracking.
   */
  private boolean backtrackOccured;

  Store store;
  // for each variable computes the domain as given by all tuples.
  IntervalDomain[] valuesInFocus;
  int[] domainSizeAfterConsistency;
  int firstConsistencyLevel;

  /**
   * It constructs an extensional constraint.
   *
   * @param list the variables in the scope of the constraint.
   * @param tuples the tuples which are supports.
   * @param reinsertBefore it specifies if the tuples which were removed and are reinstatiated are
   *     inserted at the beginning.
   * @param residuesBefore it specifies if the residue tuples are moved to the beginning.
   */
  public ExtensionalSupportStr(
      IntVar[] list, int[][] tuples, boolean reinsertBefore, boolean residuesBefore) {

    checkInputForNullness("list", list);
    checkInputForNullness("tuples", tuples);
    checkInputForDuplication("list", list);

    this.list = Arrays.copyOf(list, list.length);

    views = new IndexDomainView[list.length];

    this.tuples = tuples;

    numberId = idNumber.incrementAndGet();

    this.reinsertBefore = reinsertBefore;
    this.residuesBefore = residuesBefore;

    this.queueIndex = 1;

    setScope(list);
  }

  /**
   * It creates an extensional constraint.
   *
   * @param variables the variables in the scope of the constraint.
   * @param tuples the support tuples.
   */
  public ExtensionalSupportStr(IntVar[] variables, int[][] tuples) {
    this(variables, tuples, true, true);
  }

  /**
   * It removes the tuple which is no longer valid.
   *
   * @param previous the tuple pointing at removed tuple.
   * @param current the removed tuple.
   */
  public void remove(int previous, int current) {

    if (previous == -1) {
      first = nexts[current];
    } else {
      nexts[previous] = nexts[current];
    }
    if (nexts[current] == -1) {
      last = previous;
    }

    if (store.level == headsOfEliminatedTuples.stamp()) {
      nexts[current] = headsOfEliminatedTuples.value();
    } else {
      nexts[current] = -1;
    }

    headsOfEliminatedTuples.update(current);

    if (tailsOfEliminatedTuples.stamp() < store.level || tailsOfEliminatedTuples.value() == -1) {
      tailsOfEliminatedTuples.update(current);
    }
  }

  /**
   * It moves the residue to the beginning of the list.
   *
   * @param previous the tuple pointing at tuple residue.
   * @param current the residue tuple.
   */
  public void storeResidue(int previous, int current) {
    if (previous == -1) {
      first = nexts[current];
    } else {
      nexts[previous] = nexts[current];
    }
    if (nexts[current] == -1) {
      last = previous;
    }
    nexts[current] = firstResidue;
    if (firstResidue == -1) {
      lastResidue = current;
    }
    firstResidue = current;
  }

  @Override
  public void removeLevel(int level) {

    if (ASSERTS_ENABLED && level <= firstConsistencyLevel) {
      throw new IllegalStateException(
          String.valueOf(
              "Constraint has the level at which it has computed its initial state being removed."));
    }

    //   It is called upon removing level

    backtrackOccured = true;
    lastAssignedVariablePosition = -1;

    // adds tuples which were removed at current level, which is being removed.

    if (headsOfEliminatedTuples.stamp() < store.level) {
      return;
    }

    if (reinsertBefore) {

      if (tailsOfEliminatedTuples.value() == -1) {
        log.error("Error: tailsOfEliminatedTuples value is -1");
      }

      nexts[tailsOfEliminatedTuples.value()] = first;
      if (first == -1) {
        last = tailsOfEliminatedTuples.value();
      }
      first = headsOfEliminatedTuples.value();

    } else {
      if (first != -1) {
        nexts[last] = headsOfEliminatedTuples.value();
      } else {
        first = headsOfEliminatedTuples.value();
      }
      last = tailsOfEliminatedTuples.value();
    }
  }

  /** First-time setup: filter supports, shrink tuples, build views, transform to indexes. */
  private void doFirstConsistencyCheck(Store store) {
    valuesInFocus = createValuesInFocus();
    boolean[] stillSupport = new boolean[tuples.length];
    int noSupports = markSupportAndCollectValuesInFocus(stillSupport);
    logFirstConsistencySupports(noSupports);
    tuples = shrinkToSupportedTuples(stillSupport, noSupports);
    if (tuples.length == 0) {
      throw Store.failException;
    }
    initFirstAndNexts();
    restrictDomainsAndCreateViews(store);
    transformTuplesToIndexes();
    firstConsistencyCheck = false;
    firstConsistencyLevel = store.level;
  }

  private IntervalDomain[] createValuesInFocus() {
    IntervalDomain[] focus = new IntervalDomain[list.length];
    for (int j = 0; j < list.length; j++) {
      focus[j] = new IntervalDomain();
    }
    return focus;
  }

  private int markSupportAndCollectValuesInFocus(boolean[] stillSupport) {
    int noSupports = 0;
    int i = 0;
    for (int[] t : tuples) {
      stillSupport[i] = isTupleSupported(t);
      logMarkSupportDebug(t, stillSupport[i]);
      if (stillSupport[i]) {
        noSupports++;
        addTupleToValuesInFocus(t);
      }
      i++;
    }
    return noSupports;
  }

  private void logMarkSupportDebug(int[] t, boolean supported) {
    if (DEBUG_ALL) {
      log.debug("support for analysis{}", Arrays.toString(t));
      if (!supported) {
        log.debug("Not support {}", Arrays.toString(t));
      }
    }
  }

  private boolean isTupleSupported(int[] t) {
    for (int j = 0; j < t.length; j++) {
      if (!list[j].dom().contains(t[j])) {
        return false;
      }
    }
    return true;
  }

  private void addTupleToValuesInFocus(int[] t) {
    int m = 0;
    for (int val : t) {
      valuesInFocus[m].unionAdapt(val, val);
      m++;
    }
  }

  private void logFirstConsistencySupports(int noSupports) {
    if (DEBUG_ALL) {
      log.debug("No. still supports {}", noSupports);
    }
  }

  private int[][] shrinkToSupportedTuples(boolean[] stillSupport, int noSupports) {
    int[][] temp4Shrinking = new int[noSupports][];
    int i = 0;
    int k = 0;
    for (int[] t : tuples) {
      if (stillSupport[k]) {
        temp4Shrinking[i++] = t;
        if (DEBUG_ALL) {
          log.debug("Still support {}", Arrays.toString(t));
        }
      }
      k++;
    }
    return temp4Shrinking;
  }

  private void initFirstAndNexts() {
    first = 0;
    nexts = new int[tuples.length];
    for (int j = 0; j < nexts.length; j++) {
      nexts[j] = j + 1;
    }
    nexts[nexts.length - 1] = -1;
    last = nexts.length - 1;
  }

  private void restrictDomainsAndCreateViews(Store store) {
    for (int j = 0; j < views.length; j++) {
      list[j].domain.in(store.level, list[j], valuesInFocus[j]);
      views[j] = new IndexDomainView(list[j], true);
    }
  }

  private void transformTuplesToIndexes() {
    for (int l = 0; l < tuples.length; l++) {
      int[] originalTuple = tuples[l];
      int[] transformedTuple = new int[originalTuple.length];
      for (int m = 0; m < transformedTuple.length; m++) {
        transformedTuple[m] = views[m].indexOfValue(originalTuple[m]);
      }
      tuples[l] = transformedTuple;
    }
  }

  private void updateDomainSizesAfterBacktrack() {
    for (int i = 0; i < list.length; i++) {
      if (domainSizeAfterConsistency[i] != 0) {
        domainSizeAfterConsistency[i] = list[i].getSize();
      }
    }
  }

  private void fillValidityAndSupportCounts() {
    nbValidityVariables = 0;
    nbSupportsVariables = 0;
    nbGlobalValuesToBeSupported = 0;
    for (int i = 0; i < list.length; i++) {
      if (list[i].getSize() != domainSizeAfterConsistency[i]) {
        validityVariablePositions[nbValidityVariables++] = i;
      }
      if (domainSizeAfterConsistency[i] != 1) {
        supportsVariablePositions[nbSupportsVariables++] = i;
        views[i].intializeSupportSweep();
        nbGlobalValuesToBeSupported += list[i].getSize();
        nbValuesToBeSupported[i] = list[i].getSize();
      }
    }
  }

  private boolean isTupleValid(int[] checkedTuple, int lastAssignedIndex) {
    if (lastAssignedVariablePosition != -1
        && checkedTuple[lastAssignedVariablePosition] != lastAssignedIndex) {
      return false;
    }
    for (int i = 0; i < nbValidityVariables; i++) {
      int position = validityVariablePositions[i];
      if (!views[position].contains(checkedTuple[position])) {
        return false;
      }
    }
    return true;
  }

  /** Updates support for a valid tuple; returns new previous pointer. */
  private int updateSupportForTuple(int previous, int current, int[] checkedTuple) {
    int nbbefore = nbGlobalValuesToBeSupported;
    for (int i = nbSupportsVariables - 1; i >= 0; i--) {
      int position = supportsVariablePositions[i];
      if (!views[position].setSupport(checkedTuple[position])) {
        nbGlobalValuesToBeSupported--;
        nbValuesToBeSupported[position]--;
        if (nbValuesToBeSupported[position] == 0) {
          supportsVariablePositions[i] = supportsVariablePositions[--nbSupportsVariables];
        }
      }
    }
    if (residuesBefore && nbbefore > nbGlobalValuesToBeSupported) {
      storeResidue(previous, current);
      return previous;
    }
    return current;
  }

  private void applyResidues() {
    if (!residuesBefore || firstResidue == -1) {
      return;
    }
    nexts[lastResidue] = first;
    if (first == -1) {
      last = lastResidue;
    }
    first = firstResidue;
  }

  private void checkSupportFailure() {
    for (int i = 0; i < nbSupportsVariables; i++) {
      int position = supportsVariablePositions[i];
      if (nbValuesToBeSupported[position] == list[position].getSize()) {
        throw Store.failException;
      }
    }
  }

  private void removeUnsupportedAndFinalize(Store store) {
    for (int i = 0; i < nbSupportsVariables; i++) {
      views[supportsVariablePositions[i]].removeUnSupportedValues(store);
    }
    for (int i = 0; i < list.length; i++) {
      domainSizeAfterConsistency[i] = list[i].getSize();
    }
  }

  @Override
  public void consistency(Store store) {

    if (firstConsistencyCheck) {
      doFirstConsistencyCheck(store);
    }

    if (backtrackOccured) {
      updateDomainSizesAfterBacktrack();
    }

    fillValidityAndSupportCounts();

    int lastAssignedIndex = 0;
    if (lastAssignedVariablePosition != -1) {
      lastAssignedIndex =
          views[lastAssignedVariablePosition].indexOfValue(
              list[lastAssignedVariablePosition].value());
    }

    firstResidue = -1;
    int previous = -1;
    int current = first;
    while (current != -1) {
      int next = nexts[current];
      int[] checkedTuple = tuples[current];
      if (!isTupleValid(checkedTuple, lastAssignedIndex)) {
        remove(previous, current);
      } else {
        previous = updateSupportForTuple(previous, current, checkedTuple);
      }
      current = next;
    }

    applyResidues();
    checkSupportFailure();
    removeUnsupportedAndFinalize(store);
    backtrackOccured = false;
  }

  @Override
  public void impose(Store store) {

    this.store = store;

    varToIndex = Var.positionMapping(list, false, this.getClass());

    if (DEBUG_ALL) {
      for (Var v : list) {
        log.debug("Variable {}", v);
      }
    }

    headsOfEliminatedTuples = new TimeStamp<>(store, -1);
    tailsOfEliminatedTuples = new TimeStamp<>(store, -1);

    nbValuesToBeSupported = new int[list.length];
    validityVariablePositions = new int[list.length];
    supportsVariablePositions = new int[list.length];

    domainSizeAfterConsistency = new int[list.length];

    super.impose(store);
  }

  @Override
  public void queueVariable(int level, Var v) {

    if (backtrackOccured) {
      // Variables have changed after backtracking and before consistency function.
      domainSizeAfterConsistency[varToIndex.get(v)] = 0;
    }

    if (v.singleton()) {
      lastAssignedVariablePosition = varToIndex.get(v);
    }
  }

  boolean smaller(int[] tuple1, int[] tuple2) {
    return TupleUtils.tuplesSmaller(tuple1, tuple2);
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
    tupleString.append(", ");
    if (tuples != null) {
      sortTuplesForDisplay(tuples);
      appendTuplesTo(tupleString, tuples);
      tupleString.append(")");
    }
    return tupleString.toString();
  }

  private void sortTuplesForDisplay(int[][] subset) {
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

  private void appendTuplesTo(StringBuilder sb, int[][] subset) {
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
