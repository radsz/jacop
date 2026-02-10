/*
 * Alldistinct.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Alldistinct constraint assures that all FDVs have different values.
 *
 * <p>This implementation is based on Regin paper. It uses slightly modified Hopcroft-Karp algorithm
 * to compute maximum matching. The value graph is analysed and Tarjan algorithm for finding
 * strongly connected components is used. Maximum matching and Value Graph is stored as TimeStamp
 * Mutable variables to minimize recomputation. Value graph is expensive in terms of memory usage.
 * Use this constraint with care. One variable with domain 0..1000000 will make it use few MB
 * already and kill the efficiency.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class Alldistinct extends Constraint
    implements UsesQueueVariable, Stateful, SatisfiedPresent {

  /* @todo implement in alldistinct remark, that only variable
   * with domain of size smaller equal n (number
   * of variables) can contribute to any pruning. */

  static final boolean debugAll = false;

  static final boolean debugPruning = false;

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies all variables which have to have different values. */
  public final IntVar[] list;

  // Any variable which matched edge ends up deleted is added to this
  // structure to obtain a new matched edge
  final LinkedHashSet<IntVar> freeVariables = new LinkedHashSet<>();
  // each fdv has a matched value in maximal matching
  // this can change from consistency execution to consistency execution
  // any maximum matching is good for analysis.
  // However if no matched is removed then previously computed matching
  // can be directly used.
  // If a matched edge was removed then the remains of maximum matching
  // are used to compute a new maximum matching.
  final Map<IntVar, TimeStamp<Integer>> matching;
  // Until pointer stampValues it stores all values still in domain of
  // at least one variable
  final Integer[] potentialFreeValues;
  final Map<IntVar, TimeStamp<Integer>> sccStamp;
  // Variables for revisited Tarjan scc algorithm Reuse of scc
  // numbers previously computed, is only possible when matching is
  // not changed, since then any change can only split component
  // (components stay the same within the same matching). For Golomb
  // problem size 9, matching recomputed 50% of the time consistency
  // called. It is very important that this stamp is used at the
  // begining of the (re)computation of both visited and revisited
  // Tarjan algorithm.
  // stamps specify the position of the last fdv which posses given integer
  // it decrease with increase of the store level.
  final Map<Integer, TimeStamp<Integer>> stamps;
  // Stores index for values in array potentialFreeValues it speeds
  // up significantly the swap operation when a value is not free
  // anymore and needs to be moved at the end of potentialFreeValues
  // array.
  final Map<Integer, Integer> valueIndex;
  // valueMapVariable specifies which Variable posses given integer
  final Map<Integer, ArrayList<IntVar>> valueMapVariable;
  final boolean greedy = true;

  /** It counts the number of executions of the consistency function. */
  public int consistencyChecks;

  /**
   * It computes how many times did consistency execution has been re-executed due to narrowing
   * event at the end of the consistency function.
   */
  public int fullConsistencyPassesWithNarrowingEvent;

  boolean backtrackOccured = true;
  // failure (inconsistency) discovered during imposition
  boolean impositionFailure;
  boolean maximumMatchingNotRecomputed = true;
  // Important global variables for visitTarjan and revisitTarjan
  // Probably vn can be replaced by n.
  int n;
  TimeStamp<Integer> nStamp;
  boolean permutationConsistency = true;
  // Represents for each Variable a scc to which it belongs.
  // This can change from a lot from matching to matching.
  // Variable may belong to different components given different matching.
  // Only if old maximum matching is used than the old components numbers can
  // be reused.
  Map<IntVar, Integer> scc;
  // All grounded variables are not taken into account, they have
  // their consistent value and can be simply omitted in any kind of
  // analysis.
  TimeStamp<Integer> stampNotGroundedVariables;
  // Stores how many variables were reached by free values. for
  // efficiency purposes. If equal number of variables where reached
  // then previously then we can stop doing reachability analysis.
  TimeStamp<Integer> stampReachability;
  // For discovery of situation when number of values is equal
  // to number of variables, which means that there is no free
  // values
  // It also can say when to stop looking for free values since
  // it is easy to compute number of free values
  // "stampValues.value() - x.length"
  TimeStamp<Integer> stampValues;
  LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<>();
  int vn;
  IntVar guideVariable;
  int guideValue;

  /**
   * It constructs an alldistinct constraint.
   *
   * @param list an array of variables.
   */
  public Alldistinct(IntVar[] list) {

    checkInputForNullness("list", list);
    checkInputForDuplication("list", list);

    queueIndex = 2;

    numberId = idNumber.incrementAndGet();

    this.list = new IntVar[list.length];

    System.arraycopy(list, 0, this.list, 0, list.length);

    valueMapVariable = new HashMap<>();
    stamps = new HashMap<>();
    matching = Var.createEmptyPositioning();
    sccStamp = Var.createEmptyPositioning();

    IntDomain sum = new IntervalDomain(5);

    for (IntVar var : this.list) {
      sum.addDom(var.dom());
    }

    // Each value in any variable domain will appear in a value graph
    // Therefore it is enough that one variable has a domain 0..1000000 to
    // create huge value graph making this constraint very ineffective
    int value;
    ArrayList<IntVar> currentList;

    potentialFreeValues = new Integer[sum.getSize()];

    valueIndex = new HashMap<>(sum.getSize(), 0.5f);
    int m = 0;

    for (ValueEnumeration enumer = sum.valueEnumeration(); enumer.hasMoreElements(); ) {

      value = enumer.nextElement();
      Integer valueInteger = value;
      potentialFreeValues[m] = valueInteger;

      valueIndex.put(valueInteger, m);
      m++;

      currentList = new ArrayList<>();
      for (IntVar intVar : this.list) {
        if (intVar.domain.contains(value)) {
          currentList.add(intVar);
        }
      }
      valueMapVariable.put(valueInteger, currentList);
    }

    setScope(list);
  }

  /**
   * It constructs an alldistinct constraint.
   *
   * @param list arraylist of variables.
   */
  public Alldistinct(List<? extends IntVar> list) {

    this(list.toArray(new IntVar[0]));
  }

  // Right now accepts as input potential free values
  // Makes check if value is matched by variable and simply skip this case
  // It skips matched values at the begining of the path, but
  // it can not skip matched values after
  // potential freeValues, inside hopcroft algorithm, but outside it is free
  // Values

  @Override
  public void removeLevel(int level) {
    variableQueue = new LinkedHashSet<>();
    backtrackOccured = true;
  }

  @SuppressWarnings("unchecked")
  @Override
  public void consistency(Store store) {

    if (impositionFailure) {
      throw Store.failException;
    }

    if (store.currentQueue == queueIndex) {

      LinkedHashSet<IntVar> copy = (LinkedHashSet<IntVar>) variableQueue.clone();

      for (IntVar Q : copy) {
        if (Q.singleton()) {
          int qValue = Q.min();
          int lastNotGround = stampNotGroundedVariables.value();
          for (int i = 0; i <= lastNotGround; i++) {
            if (list[i] != Q) {
              list[i].domain.inComplement(store.level, list[i], qValue);
            }
          }
        }
      }

      if (queueIndex + 2 < store.queueNo) {
        store.changed[queueIndex + 2].add(this);
        return;
      }
    }

    consistencyChecks++;

    maximumMatchingNotRecomputed = true;

    permutationConsistency = stampValues.value() - 1 == stampNotGroundedVariables.value();

    // Store all changed Variable variables locally
    LinkedHashSet<IntVar> fdvs = variableQueue;

    if (debugAll) {
      log.debug("Changed Variables {}", variableQueue);
    }

    IntDomain Qdom;
    Integer zero = 0;
    ArrayList<IntVar> currentList;
    TimeStamp<Integer> stamp;

    LinkedHashSet<IntVar> singletons = new LinkedHashSet<>();

    while (!variableQueue.isEmpty()) {

      variableQueue = new LinkedHashSet<>();

      for (IntVar Q : fdvs) {
        Qdom = Q.dom();
        if (Qdom.singleton()) {

          int qValue = Q.value();

          singletons.add(Q);

          int lastNotGroundedVariable = stampNotGroundedVariables.value();
          for (int i = 0; i <= lastNotGroundedVariable; i++) {
            if (list[i] == Q) {
              list[i] = list[lastNotGroundedVariable];
              list[lastNotGroundedVariable] = Q;
              stampNotGroundedVariables.update(lastNotGroundedVariable - 1);
              break;
            }
          }

          currentList = valueMapVariable.get(qValue);

          // Timestamp variable which points to the position of
          // the last variable which still has qValue in its
          // domain
          stamp = stamps.get(qValue);

          int lastPosition = stamp.value();

          int positionV = currentList.indexOf(Q);

          // It has to set position to variable which has
          // Qvalue in its domain to value 0 since only
          // one variable will have this value.
          stamp.update(zero);

          if (positionV > 0) {

            currentList.set(positionV, currentList.getFirst());
            currentList.set(0, Q);
          }

          // All Variable which still had qValue in its domain
          // have this value removed
          for (int c = 1; c <= lastPosition; c++) {
            currentList.get(c).domain.inComplement(store.level, currentList.get(c), qValue);
          }

          // Should be seperate from above loop since failure
          // in indexicals (in) will not clear variableQueue
          for (int c = 1; c <= lastPosition; c++) {
            variableQueue.add(currentList.get(c));
          }
        }
      }
      fdvs.addAll(variableQueue);
    }

    variableQueue.clear();

    // If additional pruning has occured than re-execute consistency
    // algorithm
    Iterator<IntVar> iter = fdvs.iterator();

    if (debugAll) {
      log.debug("Before");
      log.debug("Mapping Value->Variable{}", valueMapVariable);
      log.debug("Stamps for size of Mapping Value->Variable{}", stamps);
      log.debug("Maximum Matching {}", matching);
    }

    while (iter.hasNext()) {

      IntVar V = iter.next();
      IntDomain vPrunedDomain = V.recentDomainPruning();

      if (debugAll) {
        log.debug("Variable changed {}", V);
        log.debug("Pruned Domain {}", vPrunedDomain);
      }

      if (!vPrunedDomain.isEmpty()) {

        // Check if any removed value was a edge in maximum matching
        Integer matchedValue = matching.get(V).value();

        // vPrunedDomain contains edge in maximum matching
        // this variable needs recomputation
        if (vPrunedDomain.contains(matchedValue)) {
          freeVariables.add(V);
        }

        if (debugAll) {
          log.debug(
              " V {} matchedValue {} prunedDom {}contains? {}",
              V,
              matchedValue,
              vPrunedDomain,
              vPrunedDomain.contains(matchedValue));
        }

        for (ValueEnumeration enumer = vPrunedDomain.valueEnumeration();
            enumer.hasMoreElements(); ) {

          Integer integerValue = enumer.nextElement();

          currentList = valueMapVariable.get(integerValue);

          stamp = stamps.get(integerValue);

          int lastPosition = stamp.value();

          int positionV = -1;
          for (int k = 0; k <= lastPosition; k++) {
            if (currentList.get(k) == V) {
              positionV = k;
              break;
            }
          }

          if (positionV == -1) {
            continue;
          }

          if (lastPosition > positionV) {

            stamp.update(lastPosition - 1);

            currentList.set(positionV, currentList.get(lastPosition));
            currentList.set(lastPosition, V);

            continue;
          }

          if (lastPosition == positionV) {
            stamp.update(lastPosition - 1);

            if (lastPosition == 0) {
              removeValueFromPotentialFreeValues(integerValue);
            }
          }
        }

      } else if (debugAll) {
        log.debug(
            "There was an Variable which was marked as changed but there is no difference in domain{}",
            V);
        log.debug("Most probably the result of current implementation of variableQueue signals");
      }
    }

    if (debugAll) {
      log.debug("After");
      log.debug("Mapping Value->Variable{}", valueMapVariable);
      log.debug("Stamps for size of Mapping Value->Variable{}", stamps);
    }

    if (debugAll) {
      log.debug("Looking Maximum Matching ");
    }

    // Remove singletons from changed variables as no pruning
    // can be achieved for them.
    while (!singletons.isEmpty()) {
      Iterator<IntVar> it = singletons.iterator();
      IntVar singleton = it.next();
      it.remove();
      fdvs.remove(singleton);
      freeVariables.remove(singleton);
      Integer integerValue = singleton.value();
      matching.get(singleton).update(integerValue);
      removeValueFromPotentialFreeValues(integerValue);
    }

    if (!freeVariables.isEmpty()) {

      if (!hopcroftKarpMaximumMatching()) {
        freeVariables.clear();
        variableQueue.clear();
        throw Store.failException;
      }
      freeVariables.clear();
    } else {

      // Put all matched variables in valueMapVariable on the first
      // position
      // It is required during backtracking, old matching is reused
      // no need to recompute hopcroft algorithm but there is a need
      // to fix matching data structure.

      int lastNotGroundedVariable = stampNotGroundedVariables.value();

      IntVar variable;
      Integer matchedValue;
      int positionMatched;

      for (int i = 0; i <= lastNotGroundedVariable; i++) {

        variable = list[i];

        matchedValue = matching.get(variable).value();
        currentList = valueMapVariable.get(matchedValue);

        positionMatched = currentList.indexOf(variable);
        if (positionMatched != 0) {

          currentList.set(positionMatched, currentList.getFirst());
          currentList.set(0, variable);
        }
      }
    }

    if (debugAll) {
      log.debug("Maximum Matching {}", matching);
    }

    // Revisited Tarjan

    List<IntVar> l = new ArrayList<>();
    Map<IntVar, Integer> dfsnum = Var.createEmptyPositioning();
    Map<IntVar, Integer> low = Var.createEmptyPositioning();

    n = nStamp.value();

    int lastNotGroundedVariable = stampNotGroundedVariables.value();

    if (maximumMatchingNotRecomputed || permutationConsistency) {

      while (!fdvs.isEmpty()) {

        Iterator<IntVar> it = fdvs.iterator();
        IntVar changedVariable = it.next();
        it.remove();

        if (debugAll) {
          log.debug("Tarjan start, changed variabled {}", changedVariable);
        }

        revisitTarjan(changedVariable, l, dfsnum, low, fdvs);

        if (debugAll) {
          log.debug("Tarjan end");
        }
      }

      // important to keep n as large as number of the highest current
      // component
      nStamp.update(n + 1);

    } else {
      // New maximum matching may cause different scc for variables
      scc = Var.createEmptyPositioning();

      vn = nStamp.value();

      for (int i = 0; i <= lastNotGroundedVariable; i++) {

        if (debugAll) {
          log.debug("Tarjan start, changed variabled {}", list[i]);
          log.debug("Tarjan start, value mapping {}", valueMapVariable);
        }

        if (scc.get(list[i]) == null) {
          visitTarjan(list[i], l, dfsnum, low);
        }

        if (debugAll) {
          log.debug("Tarjan end");
        }
      }

      if (debugAll) {
        log.debug("Tarjan end state {}", scc);
      }

      // Update stamps for new matching

      for (Map.Entry<IntVar, Integer> entry : scc.entrySet()) {
        IntVar key = entry.getKey();
        Integer value = entry.getValue();
        // Use the key and the value
        sccStamp.get(key).update(value);
      }

      nStamp.update(vn + 1);
    }

    // Traverses the graph starting in free values and marks each variable
    // which is reachable from a free value

    // New approach
    // Use potentialFreeValues, create ordered list of values matched
    // each potential free value check against

    LinkedHashSet<IntVar> variablesReachableFromFreeValues =
        new LinkedHashSet<>(list.length, 0.50f);

    int stampValue = stampValues.value();

    int lastNotGroundedVariablePlusOne = lastNotGroundedVariable + 1;

    if (stampValue - lastNotGroundedVariablePlusOne > 0) {

      // if values available equal to number of variables not grounded
      // (plus one is due
      // to different representation) then no free values, so no need for
      // reachability analysis.

      Set<Integer> matchedValues = new HashSet<>(list.length, 0.50f);

      int noOfReachedVariablesLastTime = stampReachability.value();

      for (int i = 0; i <= lastNotGroundedVariable; i++) {
        matchedValues.add(matching.get(list[i]).value());
      }

      for (int i = 0;
          i < stampValue
              && variablesReachableFromFreeValues.size() < noOfReachedVariablesLastTime
              && variablesReachableFromFreeValues.size() != lastNotGroundedVariablePlusOne;
          i++) {
        if (!matchedValues.contains(potentialFreeValues[i])) {
          markReachableVariables(variablesReachableFromFreeValues, potentialFreeValues[i]);
        }
      }

      stampReachability.update(variablesReachableFromFreeValues.size());
    }

    if (debugAll) {
      log.debug("All reached variables {}", variablesReachableFromFreeValues);

      log.debug(
          "Check for All NOT reached variables if there is an edge from matched variable to a different");
    }

    IntVar variable;
    Integer matched;
    int variableComponentId;
    int lastPosition;
    IntVar possibleDifferentComponentVariable;
    boolean narrowingEvent = false;

    for (int j = 0; j <= lastNotGroundedVariable; j++) {

      variable = list[j];

      if (debugAll) {
        log.debug("Variable {} is considered ", variable);
      }

      if (!variablesReachableFromFreeValues.contains(variable)) {

        if (debugPruning) {
          log.debug("Variable {} is not reached by free values ", variable);
        }

        variableComponentId = sccStamp.get(variable).value();

        matched = matching.get(variable).value();

        currentList = valueMapVariable.get(matched);

        stamp = stamps.get(matched);

        lastPosition = stamp.value();

        if (debugAll) {
          log.debug("currentList {} stamp {}", currentList, lastPosition);
        }

        // If permutation constraint
        // then above if is always true then this check can
        // reuse quite a lot of work required for other
        // pruning anyway
        // loop invariant is that variable is not singleton
        if (lastPosition == 0 && permutationConsistency) {

          if (debugPruning) {
            log.debug("Value {} has only this variable possible {}", matched, variable);
          }

          variable.domain.inValue(store.level, variable, matched); // , matched);

          // The above pruning does not require execution of
          // consistency
          // function, neither update of any local structure of
          // alldistinct
          // constraint therefore it can be removed from
          // variableQueue.
          variableQueue.remove(variable);
        }

        for (int i = 0; i <= lastPosition; i++) {
          possibleDifferentComponentVariable = currentList.get(i);
          if (variableComponentId != sccStamp.get(possibleDifferentComponentVariable).value()) {

            if (debugPruning) {
              log.debug(
                  "\n\n\n\n\nVariable {}can not take value {}\n\n\n\n",
                  possibleDifferentComponentVariable,
                  matched);
            }

            possibleDifferentComponentVariable.domain.inComplement(
                store.level, possibleDifferentComponentVariable, matched);

            narrowingEvent = true;

            // Required to keep the data structure consistent
            variableQueue.add(possibleDifferentComponentVariable);
            currentList.set(i, currentList.get(lastPosition));
            currentList.set(lastPosition, possibleDifferentComponentVariable);

            lastPosition = lastPosition - 1;
            stamp.update(lastPosition);
          }
        }
      }
    }

    if (!narrowingEvent && stampValues.value() - 1 == stampNotGroundedVariables.value()) {

      // Use Global Potential Free Values
      int sizePotentialFreeValues = stampValues.value();
      int currentlyUsedPotentialFreeValue = 0;

      Integer value;

      while (currentlyUsedPotentialFreeValue < sizePotentialFreeValues) {

        value = potentialFreeValues[currentlyUsedPotentialFreeValue];

        currentlyUsedPotentialFreeValue++;

        stamp = stamps.get(value);

        stampValue = stamp.value();

        if (stampValue == 0 && valueMapVariable.get(value).getFirst().dom().getSize() > 1) {
          log.debug("Transformation Alldistinct-Permutation and missing propagation ");

          valueMapVariable
              .get(value)
              .getFirst()
              .domain
              .inValue(store.level, valueMapVariable.get(value).getFirst(), value); // , value);

          variableQueue.add(valueMapVariable.get(value).getFirst());

          narrowingEvent = true;
        }
      }
    }

    // moved from place below, so re-execution does not do unnecessary work
    backtrackOccured = false;

    if (narrowingEvent) {
      consistencyChecks--;
      fullConsistencyPassesWithNarrowingEvent++;
      consistency(store);
    }

    if (debugAll) {
      log.debug("Consistency technique has finished execution ");
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  private boolean hopcroftKarpMaximumMatching() {

    maximumMatchingNotRecomputed = false;

    boolean maximumMatchingFound = false;

    Set<Integer> nonFreeValues = new HashSet<>();

    Integer matched;

    IntVar variable;

    int lastNotGroundedVariable = stampNotGroundedVariables.value();

    for (int i = 0; i <= lastNotGroundedVariable; i++) {
      variable = list[i];

      // variable does not belong to freeVariables
      if (!freeVariables.contains(variable)) {

        matched = matching.get(variable).value();
        nonFreeValues.add(matched);

        if (backtrackOccured) {

          ArrayList<IntVar> currentList = valueMapVariable.get(matched);

          // Correcting matching in ValueMapVariable for
          // notGroundedYetVariable.
          // This variable has not removed previously computed
          // matching
          // since last time this function was called

          int positionMatched = currentList.indexOf(variable);
          if (positionMatched != 0) {

            currentList.set(positionMatched, currentList.getFirst());
            currentList.set(0, variable);
          }
        }
      }
    }

    // Points at edge which was not yet used by Karp-Hopcroft algorithm
    Map<Integer, Integer> notYetUsedVariablePointer = new HashMap<>();

    // Use Global Potential Free Values
    int sizePotentialFreeValues = stampValues.value();
    int currentlyUsedPotentialFreeValue = 0;

    Integer value;
    TimeStamp<Integer> stamp;
    int stampValue;

    while (currentlyUsedPotentialFreeValue < sizePotentialFreeValues) {

      value = potentialFreeValues[currentlyUsedPotentialFreeValue];

      currentlyUsedPotentialFreeValue++;

      stamp = stamps.get(value);

      stampValue = stamp.value();

      notYetUsedVariablePointer.put(value, stampValue);
    }

    while (!maximumMatchingFound) {

      List<LinkedList<Object>> allpaths = new ArrayList<>();

      LinkedList<Object> path = new LinkedList<>();

      if (debugAll) {
        log.debug("Non Free Values{}", nonFreeValues);
      }

      Set<IntVar> visitedVariables = new HashSet<>(matching.size());

      // Very important since above it is also defined
      currentlyUsedPotentialFreeValue = 0;

      while (currentlyUsedPotentialFreeValue < sizePotentialFreeValues) {

        if (path.isEmpty()) {
          // If last element from path is null - no path yet
          // then look for free value to start a path from
          while (currentlyUsedPotentialFreeValue < sizePotentialFreeValues) {
            Integer potentialTop = potentialFreeValues[currentlyUsedPotentialFreeValue];

            currentlyUsedPotentialFreeValue++;

            if (!nonFreeValues.contains(potentialTop)) {
              path.addLast(potentialTop);
              break;
            }
          }
        }

        if (debugAll) {
          log.debug("First element of the path {}", path);
        }

        if (path.isEmpty()) {
          // no possibility to start new path
          if (allpaths.isEmpty()) {
            // no path was found last execution
            // failed to find maximum matching
            return false;
          } else {
            // some paths were found re run algorithm
            break;
          }
        }

        // Get last element from path
        Integer top = (Integer) path.getLast();

        // Top contains last element of constructed path

        IntVar first;

        while (true) { // Constructs the path
          // freeValue-...-freeVariable

          // Exit while loop if no addition to path can be done
          // no addition can be done if current pointer for
          // not yet used variable is larger than last possible
          // variable to be used.

          if (debugAll) {
            log.debug("Visited variables {}", visitedVariables);
          }

          if (debugAll) {
            log.debug("Free variables {}", freeVariables);
          }

          if (debugAll) {
            log.debug("Values for last path element {}", valueMapVariable.get(top));
          }

          // MAKE SURE you have increase level before worrying about
          // Null Pointer exception
          // in line below ;)).

          int notYetUsedVariable = notYetUsedVariablePointer.get(top);

          if (debugAll) {
            log.debug("notYetUsedVariable {}", notYetUsedVariable);
          }

          if (notYetUsedVariable == -1) {
            if (path.size() == 1) {
              break;
            } else {
              if (debugAll) {
                log.debug("Path to shorten {}", path);
              }
              path.removeLast();
              path.removeLast();
              if (debugAll) {
                log.debug("Shorten path{}", path);
              }
              top = (Integer) path.getLast();
              continue;
            }
          }

          // Value has still some edges pointing at variables
          first = valueMapVariable.get(top).get(notYetUsedVariable);

          // Take any edge and mark it as used.
          notYetUsedVariablePointer.put(top, notYetUsedVariable - 1);

          if (!visitedVariables.contains(first)) {

            path.addLast(first);
            visitedVariables.add(first);

            if (debugAll) {
              log.debug("Current path {}", path);
            }

            // if first is free variable then path
            // freevalue-...-freevariable found
            if (freeVariables.contains(first)) {
              break;
            }

            // variable is not free then matched value is pointed by
            // matching
            top = matching.get(first).value();
            path.addLast(top);
          }

          if (debugAll) {
            log.debug("Current path {}", path);
          }
        }

        // If path has even elements then it means that
        // freevalue-...-freevariable
        // path found
        if (path.size() % 2 == 0) {
          allpaths.add(path);
          path = new LinkedList<>();
        } else if (path.size() > 2) {
          // Value did not have any variables it could use to continue
          // path builing
          // Remove from path ....-variable-value (last variable and
          // value)
          path.removeLast();
          path.removeLast();
        } else {
          // Free Value yielded no path, try different free value
          path.removeLast();
        }

        // If number of paths is equal to number of free variables
        // this means that every free variables is visited and has its
        // path

        if (debugAll) {
          log.debug("Free variables {}", freeVariables);
        }

        if (debugAll) {
          log.debug("Allpaths {}", allpaths);
        }

        if (freeVariables.size() == allpaths.size()) {
          maximumMatchingFound = true;
          break;
        }
      }

      if (debugAll) {
        log.debug("Allpaths {}", allpaths);
      }

      if (allpaths.isEmpty()) {
        return false;
      }

      // Use all paths to create better matching
      for (LinkedList<Object> freePath : allpaths) {
        int freePathSize = freePath.size();

        for (int pos = 0; pos < freePathSize; pos = pos + 2) {
          Integer matchedValue = (Integer) freePath.get(pos);
          IntVar matchedVariable = (IntVar) freePath.get(pos + 1);

          if (!freeVariables.remove(matchedVariable)) {
            nonFreeValues.remove(matching.get(matchedVariable).value());
          }

          matching.get(matchedVariable).update(matchedValue);

          // Update valueMapVariable with new matched value

          ArrayList<IntVar> currentList = valueMapVariable.get(matchedValue);
          int positionMatched = currentList.indexOf(matchedVariable);
          if (positionMatched != 0) {

            currentList.set(positionMatched, currentList.getFirst());
            currentList.set(0, matchedVariable);
          }

          nonFreeValues.add(matchedValue);
        }
      }

      if (!maximumMatchingFound) {

        // Use Global Potential Free Values
        sizePotentialFreeValues = stampValues.value();
        currentlyUsedPotentialFreeValue = 0;

        // Points at edge which was not yet used by Karp-Hopcroft
        // algorithm
        notYetUsedVariablePointer = new HashMap<>(sizePotentialFreeValues);

        while (currentlyUsedPotentialFreeValue < sizePotentialFreeValues) {

          value = potentialFreeValues[currentlyUsedPotentialFreeValue];

          currentlyUsedPotentialFreeValue++;

          stamp = stamps.get(value);

          stampValue = stamp.value();

          notYetUsedVariablePointer.put(value, stampValue);
        }
      }
    }

    return true;
  }

  @Override
  public void impose(Store store) {

    super.impose(store);

    stampValues = new TimeStamp<>(store, valueMapVariable.size());

    stampReachability = new TimeStamp<>(store, list.length);

    nStamp = new TimeStamp<>(store, 0);

    stampNotGroundedVariables = new TimeStamp<>(store, list.length - 1);

    Integer zero = 0;

    Function<IntVar, TimeStamp<Integer>> f = _ -> new TimeStamp<>(store, zero);
    Var.addPositionMapping(matching, list, f, false, this.getClass());
    Var.addPositionMapping(sccStamp, list, f, false, this.getClass());

    for (Map.Entry<Integer, ArrayList<IntVar>> entry : valueMapVariable.entrySet()) {
      Integer key = entry.getKey();
      ArrayList<IntVar> value = entry.getValue();
      // Use the key and the value
      stamps.put(key, new TimeStamp<>(store, value.size() - 1));
    }

    // the initial maximum matching needs to be computed
    // search may return to this matching
    freeVariables.addAll(Arrays.asList(list));

    LinkedHashSet<IntVar> fdvs = new LinkedHashSet<>(freeVariables);

    // If first invocation of hocroft matching algorithm fails just set
    // variable and quit
    if (!hopcroftKarpMaximumMatching()) {
      impositionFailure = true;
      return;
    }

    n = nStamp.value();

    List<IntVar> l = new ArrayList<>();
    Map<IntVar, Integer> dfsnum = Var.createEmptyPositioning();
    Map<IntVar, Integer> low = Var.createEmptyPositioning();

    while (!fdvs.isEmpty()) {

      Iterator<IntVar> it = fdvs.iterator();
      IntVar changedVariable = it.next();
      it.remove();

      revisitTarjan(changedVariable, l, dfsnum, low, fdvs);
    }

    nStamp.update(n + 1);

    if (debugAll) {
      log.debug("Mapping Value->Variable{}", valueMapVariable);
      log.debug("Maximum Matching {}", matching);
    }

    store.raiseLevelBeforeConsistency = true;
  }

  private void markReachableVariables(
      LinkedHashSet<IntVar> variablesReachableFromFreeValues, Integer value) {

    if (debugAll) {
      log.debug("Start mark reachable variables {}", value);
    }

    ArrayList<IntVar> currentList = valueMapVariable.get(value);

    TimeStamp<Integer> stamp = stamps.get(value);

    int lastPosition = stamp.value();

    Integer matched;

    // i idNumber has to be from zero since free paths can go from matched
    // edges
    for (int i = 0; i <= lastPosition; i++) {

      IntVar reachableVariable = currentList.get(i);

      if (variablesReachableFromFreeValues.contains(reachableVariable)) {
        continue;
      }

      if (debugAll) {
        log.debug("Variable {} has been reached from value {}", reachableVariable, value);
      }

      matched = matching.get(reachableVariable).value();

      variablesReachableFromFreeValues.add(reachableVariable);

      markReachableVariables(variablesReachableFromFreeValues, matched);
    }
  }

  @Override
  public void queueVariable(int level, Var var) {

    if (debugAll) {
      log.debug("Var {}{}", var, ((IntVar) var).recentDomainPruning());
    }

    variableQueue.add((IntVar) var);
  }

  private void revisitTarjan(
      IntVar x,
      List<IntVar> l,
      Map<IntVar, Integer> dfsnum,
      Map<IntVar, Integer> low,
      LinkedHashSet<IntVar> fdvs) {

    Integer nInteger = n;

    dfsnum.put(x, nInteger);
    low.put(x, nInteger);
    n++;

    if (debugAll) {
      log.debug(
          "Tarjan invocation : \nx {}\nn {}\nl {}\ndfsnum {}\nlow {}\n", x, n, l, dfsnum, low);
    }

    l.add(x);

    Integer matchedValue = matching.get(x).value();

    if (debugAll) {
      log.debug("Matched value {} for {}", matchedValue, x);
    }

    ArrayList<IntVar> currentList = valueMapVariable.get(matchedValue);

    if (debugAll) {
      log.debug("Mapped variables to Matched value {}", currentList);
    }

    TimeStamp<Integer> stamp = stamps.get(matchedValue);

    int lastPosition = stamp.value();

    if (debugAll) {
      log.debug("Last valid position for variables {}", lastPosition);
    }

    int sccStampX = sccStamp.get(x).value();
    // first variable is matched value
    for (int i = 0; i <= lastPosition; i++) {

      IntVar v = currentList.get(i);

      if (sccStampX == sccStamp.get(v).value()) {
        if (dfsnum.get(v) == null) {

          revisitTarjan(v, l, dfsnum, low, fdvs);

          int lowv = low.get(v);

          if (low.get(x) > lowv) {
            low.put(x, lowv);
          }
        } else {

          if (debugAll) {
            log.debug("Part 2 : low {}={} dfsnum {}={}", x, low.get(x), v, dfsnum.get(v));
          }

          int dfsnumv = dfsnum.get(v);

          // If v was earlier visited and v belongs to stack then
          // update low number of x.
          if (dfsnumv < dfsnum.get(x) && l.contains(v) && low.get(x) > dfsnumv) {
            low.put(x, dfsnumv);
          }
        }
      }
    }

    if (debugAll) {
      log.debug("Invocation {} Low values for it {}", x, low);
      log.debug("Invocation {} Dfsnum values for it {}", x, dfsnum);
    }

    int lowx = low.get(x);

    if (lowx == dfsnum.get(x)) {

      if (debugAll) {
        log.debug("Component found  ");
      }

      Var component;

      do {
        component = l.removeLast();

        if (debugAll) {
          log.debug("Component part  {}id {}", component, lowx);
        }

        sccStamp.get(component).update(lowx);
        fdvs.remove(component);

      } while (component != x);
    }
  }

  @Override
  public boolean satisfied() {

    // Possible to use this check, fast but not accurate

    boolean sat = true;
    int i = 0;

    while (sat && i < list.length) {
      IntDomain vDom = list[i].dom();
      int vMin = vDom.min();
      int vMax = vDom.max();
      int j = 0;
      while (sat && j < list.length) {
        if (i != j) {
          IntDomain ljDom = list[j].dom();
          sat = vMin > ljDom.max() || vMax < ljDom.min();
        }
        j++;
      }
      i++;
    }
    return sat;
  }

  @Override
  public String toString() {

    StringBuilder buf = new StringBuilder(id());

    buf.append(" : alldistinct([");

    for (int i = 0; i < list.length; i++) {
      buf.append(list[i]);
      if (i < list.length - 1) {
        buf.append(", ");
      }
    }

    buf.append("]");
    return buf.toString();
  }

  private void visitTarjan(
      IntVar x, List<IntVar> l, Map<IntVar, Integer> dfsnum, Map<IntVar, Integer> low) {

    Integer vnInteger = vn;
    dfsnum.put(x, vnInteger);
    low.put(x, vnInteger);
    vn++;

    if (debugAll) {
      log.debug(
          "Tarjan invocation : \nx {}\nn {}\nl {}\ndfsnum {}\nlow {}\n", x, vn, l, dfsnum, low);
    }

    l.add(x);

    Integer matchedValue = matching.get(x).value();

    if (debugAll) {
      log.debug("Matched value {} for {}", matchedValue, x);
    }

    ArrayList<IntVar> currentList = valueMapVariable.get(matchedValue);

    if (debugAll) {
      log.debug("Mapped variables to Matched value {}", currentList);
    }

    TimeStamp<Integer> stamp = stamps.get(matchedValue);

    int lastPosition = stamp.value();

    if (debugAll) {
      log.debug("Last valid position for variables {}", lastPosition);
    }

    IntVar v;

    // first variable is matched value
    for (int i = 1; i <= lastPosition; i++) {

      v = currentList.get(i);

      if (dfsnum.get(v) == null) {

        visitTarjan(v, l, dfsnum, low);

        int lowv = low.get(v);

        if (low.get(x) > lowv) {
          low.put(x, lowv);
        }

      } else {

        if (debugAll) {
          log.debug("Part 2 : low {}={} dfsnum {}={}", x, low.get(x), v, dfsnum.get(v));
        }

        int dfsnumv = dfsnum.get(v);

        // If v was earlier visited and v belongs to stack then
        // update low number of x.
        if (dfsnumv < dfsnum.get(x) && l.contains(v) && low.get(x) > dfsnumv) {
          low.put(x, dfsnumv);
        }
      }
    }

    if (debugAll) {
      log.debug("Invocation {} Low values for it {}", x, low);
      log.debug("Invocation {} Dfsnum values for it {}", x, dfsnum);
    }

    int lowx = low.get(x);

    if (lowx == dfsnum.get(x)) {

      if (debugAll) {
        log.debug("Component found  ");
      }

      while (true) {
        IntVar component = l.removeLast();

        if (debugAll) {
          log.debug("Component part  {}", component);
        }

        scc.put(component, lowx);

        if (component == x) {

          break;
        }
      }
    }
  }

  @Override
  public Constraint getGuideConstraint() {
    return new XeqC(guideVariable, guideValue);
  }

  @Override
  public int getGuideValue() {
    return guideValue;
  }

  @Override
  public Var getGuideVariable() {

    int minCurrentPruning = 1;
    int maxCurrentPruning = 100000;

    // Look at all variables with domain size two, and find the one with
    // best pruning

    guideVariable = null;

    int lastNotGroundedVariable = stampNotGroundedVariables.value();

    for (int i = 0; i <= lastNotGroundedVariable; i++) {
      if (list[i].getSize() == 2) {

        Integer firstValue = list[i].min();
        Integer secondValue = list[i].max();

        // Evaluate recursively.
        int pruningFirstValue = estimatePruning(list[i], firstValue);

        if (pruningFirstValue >= minCurrentPruning) {

          int pruningSecondValue = estimatePruning(list[i], secondValue);

          if (pruningFirstValue < pruningSecondValue) {

            if (pruningFirstValue > minCurrentPruning) {

              // Lack of equal sign means greedy in propagation
              if (stamps.get(firstValue).value() < stamps.get(secondValue).value()
                  || (Objects.equals(
                          stamps.get(firstValue).value(), stamps.get(secondValue).value())
                      && !greedy)) {
                // Value with lower number of variables has a
                // higher change to have this value
                guideVariable = list[i];
                guideValue = firstValue;

              } else {
                guideVariable = list[i];
                guideValue = secondValue;
              }

              minCurrentPruning = pruningFirstValue;
              maxCurrentPruning = pruningSecondValue;
            } else if (pruningFirstValue == minCurrentPruning
                && pruningSecondValue > maxCurrentPruning) {

              // Lack of equal sign means greedy in propagation
              if (stamps.get(firstValue).value() < stamps.get(secondValue).value()
                  || (Objects.equals(
                          stamps.get(firstValue).value(), stamps.get(secondValue).value())
                      && !greedy)) {
                // Value with lower number of variables has a
                // higher change to have this value

                guideVariable = list[i];
                guideValue = firstValue;

              } else {

                guideVariable = list[i];
                guideValue = secondValue;
              }
              maxCurrentPruning = pruningSecondValue;
            }
          } else {
            // FirstValuePruning > SecondValuePruning
            if (pruningSecondValue > minCurrentPruning) {

              // Lack of equal sign means no greedy in propagation
              // Equal sign means greedy in propagation
              if (stamps.get(firstValue).value() <= stamps.get(secondValue).value()
                  || (Objects.equals(
                          stamps.get(firstValue).value(), stamps.get(secondValue).value())
                      && greedy)) {
                // Value with lower number of variables has a
                // higher change to have this value
                guideVariable = list[i];
                guideValue = firstValue;
              } else {

                guideVariable = list[i];
                guideValue = secondValue;
              }
              minCurrentPruning = pruningSecondValue;
              maxCurrentPruning = pruningFirstValue;
            } else if (pruningSecondValue == minCurrentPruning
                && pruningFirstValue > maxCurrentPruning) {

              // Equal sign means greedy in propagation
              if (stamps.get(firstValue).value() <= stamps.get(secondValue).value()
                  || (Objects.equals(
                          stamps.get(firstValue).value(), stamps.get(secondValue).value())
                      && greedy)) {
                // Value with lower number of variables has a
                // higher change to have this value
                guideVariable = list[i];
                guideValue = firstValue;
              } else {
                guideVariable = list[i];
                guideValue = secondValue;
              }
              maxCurrentPruning = pruningFirstValue;
            }
          }
        }
      }
    }

    // Permutation only at this moment

    if (stampValues.value() - stampNotGroundedVariables.value() == 1) {

      // Use Global Potential Free Values
      int sizePotentialFreeValues = stampValues.value();
      int currentlyUsedPotentialFreeValue = 0;

      Integer value;
      TimeStamp<Integer> stamp;
      int stampValue;

      ArrayList<IntVar> currentList;

      while (currentlyUsedPotentialFreeValue < sizePotentialFreeValues) {

        value = potentialFreeValues[currentlyUsedPotentialFreeValue];

        currentlyUsedPotentialFreeValue++;

        stamp = stamps.get(value);

        stampValue = stamp.value();

        // Value with two variables
        if (stampValue == 1) {

          currentList = valueMapVariable.get(value);

          int pruningFirstVariable = estimatePruning(currentList.get(0), value);

          if (pruningFirstVariable < minCurrentPruning) {
            continue;
          }

          int pruningSecondVariable = estimatePruning(currentList.get(1), value);

          if (pruningSecondVariable < minCurrentPruning) {
            continue;
          }

          if (pruningFirstVariable < pruningSecondVariable) {

            if (pruningFirstVariable > minCurrentPruning) {

              // Equals sign means no greedy in propagation
              // Lack of equal sign means greedy in propagation
              if (currentList.get(0).getSize() < currentList.get(1).getSize()
                  || (currentList.get(0).getSize() == currentList.get(1).getSize() && !greedy)) {

                guideVariable = currentList.getFirst();
                guideValue = value;

              } else {

                guideVariable = currentList.get(1);
                guideValue = value;
              }
              minCurrentPruning = pruningFirstVariable;
              maxCurrentPruning = pruningSecondVariable;
            } else if (pruningSecondVariable > maxCurrentPruning) {
              // Equals sign means no greedy in propagation in
              // case of tie break
              // Lack of equal sign means greedy in propagation
              if (currentList.get(0).getSize() < currentList.get(1).getSize()
                  || (currentList.get(0).getSize() == currentList.get(1).getSize() && !greedy)) {

                guideVariable = currentList.getFirst();
                guideValue = value;

              } else {

                guideVariable = currentList.get(1);
                guideValue = value;
              }

              maxCurrentPruning = pruningSecondVariable;
            }

          } else {
            // PruningFirstVariable > PruningSecondVariable
            if (pruningSecondVariable > minCurrentPruning) {

              // Equal sign means greedy in case of tie break
              if (currentList.get(0).getSize() <= currentList.get(1).getSize()
                  || (currentList.get(0).getSize() == currentList.get(1).getSize() && greedy)) {

                guideVariable = currentList.getFirst();
                guideValue = value;
              } else {

                guideVariable = currentList.get(1);
                guideValue = value;
              }

              minCurrentPruning = pruningSecondVariable;
              maxCurrentPruning = pruningFirstVariable;
            } else if (pruningFirstVariable > maxCurrentPruning) {

              // Equal sign means greedy in case of tie break
              if (currentList.get(0).getSize() <= currentList.get(1).getSize()
                  || (currentList.get(0).getSize() == currentList.get(1).getSize() && !greedy)) {

                guideVariable = currentList.getFirst();
                guideValue = value;

              } else {

                guideVariable = currentList.get(1);
                guideValue = value;
              }
              maxCurrentPruning = pruningFirstVariable;
            }
          }
        }
      }
    }

    // TODO: fix it, si does not return singleton variables.
    return guideVariable;
  }

  int estimatePruning(IntVar x, Integer v) {

    List<IntVar> exploredX = new ArrayList<>();
    List<Integer> exploredV = new ArrayList<>();

    int pruning = estimatePruningRecursive(x, v, exploredX, exploredV);

    ArrayList<IntVar> currentList;
    Integer value;

    for (Integer integer : exploredV) {

      value = integer;
      currentList = valueMapVariable.get(value);

      TimeStamp<Integer> stamp = stamps.get(value);

      int lastPosition = stamp.value();

      for (int j = 0; j <= lastPosition; j++) {
        // Edge between j and value was not counted yet
        if (!exploredX.contains(currentList.get(j))) {
          pruning++;
        }
      }
    }

    return pruning;
  }

  int estimatePruningRecursive(
      IntVar xvar, Integer v, List<IntVar> exploredX, List<Integer> exploredV) {

    if (exploredX.contains(xvar)) {
      return 0;
    }

    exploredX.add(xvar);
    exploredV.add(v);

    int pruning;

    IntDomain xDom = xvar.dom();
    pruning = xDom.getSize() - 1;

    TimeStamp<Integer> stamp;
    ArrayList<IntVar> currentList;
    ValueEnumeration enumer = xDom.valueEnumeration();

    // Permutation only
    if (stampValues.value() - stampNotGroundedVariables.value() == 1) {
      for (int i = enumer.nextElement(); enumer.hasMoreElements(); i = enumer.nextElement()) {
        if (!exploredV.contains(i)) {
          Integer iInteger = i;

          stamp = stamps.get(iInteger);

          int lastPosition = stamp.value();

          // lastPosition == 0 means one variable, so check if there
          // is atmost one variable for value
          if (lastPosition < exploredX.size() + 1) {

            currentList = valueMapVariable.get(iInteger);

            IntVar singleVar = null;
            boolean single = true;

            for (int m = 0; m <= lastPosition; m++) {
              if (!exploredX.contains(currentList.get(m))) {
                if (singleVar == null) {
                  singleVar = currentList.get(m);
                } else {
                  single = false;
                }
              }
            }

            if (single && singleVar == null) {
              log.debug("{}", this);
              log.debug("StampValues - 1 {}", stampValues.value() - 1);
              log.debug("Not grounded Var {}", stampNotGroundedVariables.value());

              int lastNotGroundedVariable = stampNotGroundedVariables.value();
              Var variable;

              for (int l = 0; l <= lastNotGroundedVariable; l++) {
                variable = list[l];
                log.debug("Stamp for {} {}", variable, sccStamp.get(variable).value());
                log.debug("Matching {}", matching.get(variable).value());
              }
            }

            if (single && singleVar != null) {
              pruning += estimatePruningRecursive(singleVar, iInteger, exploredX, exploredV);
            }
          }
        }
      }
    }

    stamp = stamps.get(v);
    currentList = valueMapVariable.get(v);

    int lastPosition = stamp.value();

    for (int i = 0; i <= lastPosition; i++) {
      IntVar variable = currentList.get(i);

      // checks if there is at most one value for variable
      if (!exploredX.contains(variable) && variable.dom().getSize() < exploredV.size() + 2) {

        boolean single = true;
        Integer singleVal = null;

        for (ValueEnumeration enumerX = variable.dom().valueEnumeration();
            enumerX.hasMoreElements(); ) {
          Integer next = enumerX.nextElement();

          if (!exploredV.contains(next)) {
            if (singleVal == null) {
              singleVal = next;
            } else {
              single = false;
            }
          }
        }

        if (single) {
          pruning += estimatePruningRecursive(variable, singleVal, exploredX, exploredV);
        }
      }
    }

    return pruning;
  }

  private void removeValueFromPotentialFreeValues(Integer integerValue) {
    int stampValue = stampValues.value() - 1;
    int indexDeletedValue = valueIndex.get(integerValue);

    if (indexDeletedValue < stampValue) {
      valueIndex.put(potentialFreeValues[indexDeletedValue], stampValue);
      valueIndex.put(potentialFreeValues[stampValue], indexDeletedValue);

      Integer swapValue = potentialFreeValues[indexDeletedValue];
      potentialFreeValues[indexDeletedValue] = potentialFreeValues[stampValue];
      potentialFreeValues[stampValue] = swapValue;
    }
    stampValues.update(stampValue);
  }
}
