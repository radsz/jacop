/*
 * GCC.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2008 Jocelyne Lotfi and Radoslaw Szymanek
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

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalDomainValueEnumeration;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;

/**
 * GCC constraint counts the number of occurences of given values in x variables. The counters are
 * specified by y's. The occurence of all values in the domain of xs is counted.
 *
 * <p>We would like to thank Irit Katriel for making the code of GCC in C she wrote available to us.
 *
 * @author Jocelyne Lotfi and Radoslaw Szymanek.
 * @version 5.0
 */
@Slf4j
@SuppressWarnings(
    "checkstyle:AbbreviationAsWordInName") // GCC is standard constraint programming terminology
public class GCC extends Constraint implements UsesQueueVariable, Stateful, SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);
  private static final boolean DEBUG = false;

  /** It specifies variables x whose values are counted. */
  private final IntVar[] x;

  /**
   * It species variables counters for counting occurences of each possible value from the intial
   * domain of x variables.
   */
  protected final IntVar[] counters;

  /**
   * The array which stores the first computed matching, which may not take into account the lower
   * bound of count variables.
   */
  private final int[] match1;

  /**
   * The array which stores the second computed matching, which may not take into account the upper
   * bound of count variables.
   */
  private final int[] match2;

  /**
   * The array which stores the third proper matching, constructed from the first one and second one
   * so both lower and upper bounds are respected.
   */
  private final int[] match3;

  private final int[] match1xOrder;
  private final int[] match2xOrder;
  private final int[] nbOfMatchPerY;
  private final int[] compOfY;
  private final Xdomain[] xDomain;
  private final int[][] yDomain;
  private final int xSize;
  private final int ySize;
  private final ArrayDeque<Integer> S1;
  private final ArrayDeque<Component> S2;
  private final PriorityQueue<Xdomain> pFirst;
  private final PriorityQueue<Xdomain> pSecond;
  private final PriorityQueue<Integer> pCount;
  private final Map<IntVar, Integer> xNodesHash;
  private final Comparator<Xdomain> compareLowerBound =
      (o1, o2) -> {
        if (o1.min() < o2.min()) {
          return -1;
        } else if (o1.min() > o2.min()) {
          return 1;
        }
        return 0;
      };

  /**
   * TODO An improvement to increase the incrementality even further.
   *
   * <p>1. The first matching uses minimal values. Remember which minimal value has changed which
   * removed from the domain the value which was used in the matching. Reuse from old matching 1 all
   * values smaller than the minimal which has changed.
   *
   * <p>Similar principle applies to matching 2 (skip the positions (variables) until the first
   * index for which m1 did change or for which the m2 value is no longer in the domain.
   *
   * <p>2. Use IndexDomainView instead of local solution.
   *
   * <p>3. boolean variable first - is it only once in the consistency function? Then this
   * functionality can be moved out of the while(newPropagation), if it should be executed every
   * time consistency is executed then (it should be setup to true somewhere).
   */
  boolean firstConsistencyCheck = true;

  TimeStamp<Integer> stamp;
  int firstConsistencyLevel;
  private int[] domainHash;
  private int stampValue;
  private Set<IntVar> zeroCounters;

  /**
   * Fix suggested by Radek: a set that keeps track of the variables that have changed and need to
   * be revisited in the consistency method.
   */
  private Set<IntVar> changedVariables = new HashSet<>();

  /**
   * It constructs global cardinality constraint.
   *
   * @param x variables which values are counted.
   * @param counters variables which count the values.
   */
  public GCC(IntVar[] x, IntVar[] counters) {

    checkInputForNullness(new String[] {"x", "counters"}, x, counters);
    checkInputForDuplicationSkipSingletons("x", x);

    this.queueIndex = 1;
    numberId = idNumber.incrementAndGet();

    counters = removeZeroCounters(x, counters);

    xSize = x.length;
    ySize = counters.length;

    this.x = new IntVar[xSize];
    this.counters = new IntVar[ySize];

    System.arraycopy(x, 0, this.x, 0, xSize);
    System.arraycopy(counters, 0, this.counters, 0, ySize);

    this.xDomain = new Xdomain[xSize];
    this.yDomain = new int[2][ySize];

    // rest of the init
    match1 = new int[xSize];
    match2 = new int[xSize];
    match3 = new int[xSize];
    match1xOrder = new int[xSize];
    match2xOrder = new int[xSize];

    nbOfMatchPerY = new int[ySize];
    compOfY = new int[ySize];

    S1 = new ArrayDeque<>();
    S2 = new ArrayDeque<>();
    Comparator<Xdomain> sortPriorityMinOrder =
        (o1, o2) -> {
          if (o1.max() < o2.max()) {
            return -1;
          } else if (o1.max() > o2.max()) {
            return 1;
          }

          return 0;
        };
    pFirst = new PriorityQueue<>(10, sortPriorityMinOrder);
    pSecond = new PriorityQueue<>(10, sortPriorityMinOrder);
    Comparator<Integer> sortPriorityMaxOrder = Comparator.reverseOrder();
    pCount = new PriorityQueue<>(10, sortPriorityMaxOrder);

    xNodesHash = Var.createEmptyPositioning();

    setScope(Stream.concat(Arrays.stream(x), Arrays.stream(counters)));
  }

  /**
   * It constructs global cardinality constraint.
   *
   * @param x variables which values are counted.
   * @param counters variables which count the values.
   */
  public GCC(List<? extends IntVar> x, List<? extends IntVar> counters) {

    this(x.toArray(new IntVar[0]), counters.toArray(new IntVar[0]));
  }

  private IntVar[] removeZeroCounters(IntVar[] x, IntVar[] counters) {

    // here I will put normalization
    IntervalDomain d = new IntervalDomain();

    for (IntVar aX : x) {
      d = (IntervalDomain) d.union(aX.domain);
    }

    // I check the consistency of the x and y variable
    if (d.getSize() != counters.length && (d.max() - d.min() + 1) != counters.length) {
      // if there are more y variable than x variable there is a mistake of conseption
      // as the rest of y variables are 0 in any case. The problem is to know which y variable
      // should not be here. With normalization we assume that it is the last ones in the
      // list but it is an assumption, it's better to throw an exception there and let the
      // user determine what is correct.
      throw new IllegalArgumentException(
          "GCC failure : join domain of x variables doesn't cover all count variables");
    }

    // no changes required
    if (d.getSize() == counters.length) {
      return counters;
    }

    // zero counters encountered.
    IntVar[] result = new IntVar[d.getSize()];
    zeroCounters = new HashSet<>();

    int i = 0;
    for (int k = d.min(); k <= d.max(); k++) {
      if (d.contains(k)) {
        result[i++] = counters[k - d.min()];
      } else {
        zeroCounters.add(counters[k - d.min()]);
      }
    }

    return result;
  }

  @Override
  public void removeLevel(int level) {
    if (level == firstConsistencyLevel) {
      firstConsistencyCheck = true;
    }
  }

  @Override
  public void consistency(Store store) {

    // the stamp is here to represent the number of x variable still
    // not singleton and that need to be pruned (the rest is set and
    // doesn't need to be pass though the whole calculation of matching
    // and SCC's). The same trick can not be apply to the y as the order
    // matter a lot.

    // I take out all the xNodes that are singleton and I put them
    // after the stamp value
    if (firstConsistencyCheck) {

      if (zeroCounters != null) {
        for (IntVar zeroCounter : zeroCounters) {
          zeroCounter.domain.inValue(store.level, zeroCounter, 0);
        }
      }

      int k = 0;

      stamp.update(xSize);

      while (k < stamp.value()) {
        if (x[k].singleton()) {
          if (stamp.value() > 0) {
            stamp.update(stamp.value() - 1);
            putToTheEnd(x, k);
          }
        } else {
          // no incrementation if there is a modification in the
          // xNodes table. The variable in the i position is no more
          // the same and need to be check also.
          k++;
        }
      }
      firstConsistencyCheck = false;
      firstConsistencyLevel = store.level;

      assert checkXorder() : "Inconsistent X variable order: " + Arrays.toString(this.x);
    }

    // no need to rerun the consistency function as the reduction on x domains doesn't affect
    // the matching and the y count is base on the matching and doesn't affect it. So
    // rerunning the constraint doesn't bring anything new. We can suppose that y counting
    // achieve bound consistency.

    do {

      store.propagationHasOccurred = false;

      // Fix suggested by Radek (moved from queueVariable)
      Set<IntVar> changedVariablesCopy = this.changedVariables;
      this.changedVariables = new HashSet<>();
      for (IntVar v : changedVariablesCopy) {
        // if v is singleton and is an X variable
        if (v.singleton()
            && xNodesHash.containsKey(v)
            && xNodesHash.get(v) < stamp.value()) { // changing '<=' to '<' (KK)
          if (DEBUG) {
            log.debug(" in xVariableToChange: {}", v);
          }
          if (stamp.value() > 0) {
            stamp.update(stamp.value() - 1);
            putToTheEnd(x, xNodesHash.get(v));
          }
        }
      }

      assert checkXorder() : "Inconsistent X variable order: " + Arrays.toString(this.x);

      if (DEBUG) {
        log.debug("XNodes");
        for (int i = 0; i < xSize; i++) {
          log.debug("{}", x[i]);
        }
        log.debug("stamp before {}", stamp.value());
      }

      stampValue = stamp.value();

      if (DEBUG) {
        log.debug("stamp after {}", stampValue);
        log.debug("Xdomain");
      }
      // put in the xDomain all xNodes that are not singleton

      for (int i = 0; i < stampValue; i++) {
        xDomain[i].setDomain(
            findPosition(x[i].min(), domainHash), findPosition(x[i].max(), domainHash));

        xDomain[i].twin = x[i];
        if (DEBUG) {
          log.debug("{}", xDomain[i]);
        }
      }
      if (DEBUG) {
        log.debug("YDomain");
      }

      // put all yNodes in yDomain
      for (int i = 0; i < ySize; i++) {
        yDomain[0][i] = counters[i].min();
        yDomain[1][i] = counters[i].max();

        if (DEBUG) {
          log.debug("{}", yDomain[i]);
        }
      }

      if (DEBUG) {
        log.debug("take out singleton xNodes");
      }

      // check all xNodes and if singleton change the yDomain value
      // to count down the xNode already link to this yNode
      for (int i = 0; i < xSize; i++) {
        if (x[i].singleton()) {
          // Change, check.
          int value = findPosition(x[i].value(), domainHash);
          if (yDomain[0][value] > 0) {
            yDomain[0][value]--;
          }
          yDomain[1][value]--;
          if (yDomain[1][value] < 0) {
            throw Store.failException;
          }
        }
      }

      if (DEBUG) {
        log.debug("pass in consistency");
        log.debug("YDomain");
        for (int i = 0; i < ySize; i++) {
          log.debug("{}", yDomain[i]);
        }
      }

      sortXbyDomainMin();

      findGeneralizedMatching();
      sccs();
      // I do the countConcistancy before the x pruning so the
      // change in x variable doesn't affect the pruning of y variable
      countBoundConsistency(store);

      for (int j = 0; j < stampValue; j++) {

        assert match3[j] >= 0 && match3[j] < ySize;
        assert compOfY[match3[j]] >= 0 && compOfY[match3[j]] <= ySize;

        int cutMin = xDomain[j].min();
        int cutMax = xDomain[j].max();

        if (DEBUG) {
          log.debug("cutmax {}", cutMax);
        }

        while (compOfY[match3[j]] != compOfY[cutMin]) {
          cutMin++;
        }

        while (compOfY[match3[j]] != compOfY[cutMax]) {
          cutMax--;
        }

        int id = xNodesHash.get(xDomain[j].twin);

        if (DEBUG) {
          log.debug("do pruning [{},{}] => [{},{}]", x[id].min(), x[id].max(), cutMin, cutMax);
        }

        xDomain[j].setDomain(cutMin, cutMax);
        IntVar v = x[id];
        v.domain.in(store.level, v, domainHash[cutMin], domainHash[cutMax]);
      }

      // check if the solution is still valid now the prunning done
      // useful if max bound reduction lead to a non-existing number and
      // the prunning is so report to the next upper bound (not necessary fitting)
      for (int i = 0; i < xSize; i++) {
        if (x[i].singleton()) {
          // Change, check.
          int value = findPosition(x[i].value(), domainHash);
          yDomain[1][value]--;
          if (yDomain[1][value] < 0) {
            if (DEBUG) {
              log.debug("failure in putting back yNodes domain");
            }
            throw Store.failException;
          }
        }
      }

    } while (store.propagationHasOccurred);
  }

  /**
   * A method to be called in asserts that checks whether all grounded X variables are correctly put
   * at the end of the list.
   *
   * @return false if the X variable order is inconsistent
   */
  private boolean checkXorder() {

    for (int i = this.stamp.value() - 1; i >= 0; i--) {
      if (this.x[i].singleton()) {
        return false;
      }
    }

    for (int i = this.stamp.value(); i < this.x.length; i++) {
      if (!this.x[i].singleton()) {
        return false;
      }
    }

    return true;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void impose(Store store) {

    stamp = new TimeStamp<>(store, xSize);

    // first I will put all the xNodes in a hashTable to be able to use
    // it with the queueVariable function
    // KK, 2015-10-18
    // only non ground variables need to be added
    // no duplicates allowed
    Var.addPositionMapping(xNodesHash, x, true, this.getClass());

    // here I will put normalization
    IntervalDomain d = new IntervalDomain();

    for (int i = 0; i < xSize; i++) {
      d = (IntervalDomain) d.union(x[i].domain);
    }

    // I check the consistency of the x and y variable
    if (d.getSize() != ySize) {
      // if there are more y variable than x variable there is a mistake of conseption
      // as the rest of y variables are 0 in any case. The problem is to know which y variable
      // should not be here. With normalization we assume that it is the last ones in the
      // list but it is an assumption, it's better to throw an exception there and let the
      // user determine what is correct.
      throw new IllegalArgumentException(
          "GCC failure : join domain of x variables doesn't cover all count variables");
    }

    domainHash = new int[d.getSize()];
    IntervalDomainValueEnumeration venum = new IntervalDomainValueEnumeration(d);
    int i = 0;
    do {

      int j = venum.nextElement();
      domainHash[i++] = j;

    } while (venum.hasMoreElements());

    for (i = 0; i < xSize; i++) {
      this.xDomain[i] =
          new Xdomain(
              x[i], findPosition(x[i].min(), domainHash), findPosition(x[i].max(), domainHash));
    }

    for (i = 0; i < ySize; i++) {
      this.yDomain[0][i] = counters[i].min();
      this.yDomain[1][i] = counters[i].max();
    }
    super.impose(store);
  }

  @Override
  public void queueVariable(int level, Var v) {
    if (DEBUG) {
      log.debug("in queue variable {} level {}", v, level);
    }
    this.changedVariables.add((IntVar) v);
  }

  @Override
  public boolean satisfied() {

    if (!grounded()) {
      return false;
    }

    int[] count = new int[domainHash.length];

    for (IntVar xVar : x) {
      int xValue = xVar.value();
      int position = 0;
      while (position < count.length && domainHash[position] != xValue) {
        position++;
      }
      assert position < count.length;
      count[position]++;
    }

    for (int i = 0; i < counters.length; i++) {
      if (counters[i].value() != count[i]) {
        return false;
      }
    }

    return true;
  }

  @Override
  public String toString() {

    StringBuilder toString = new StringBuilder(id());

    toString.append(" : GCC ([");
    for (int i = 0; i < xSize - 1; i++) {
      toString.append(x[i].toString()).append(", ");
    }
    toString.append(x[xSize - 1].toString());
    toString.append("], [");
    for (int j = 0; j < ySize - 1; j++) {
      toString.append(counters[j].toString()).append(", ");
    }
    toString.append(counters[ySize - 1].toString()).append("])");

    return toString.toString();
  }

  // private methods

  // -----------------------FIND_GENERALIZED_MATCHING--------------------------------//

  private void findGeneralizedMatching() {

    Arrays.fill(nbOfMatchPerY, 0);

    if (DEBUG) {
      log.debug("Xdomain");
      for (int i = 0; i < stampValue; i++) {
        log.debug("{} [{}-{}]", i, xDomain[i].min(), xDomain[i].max());
      }
    }
    // first pass
    firstPass();

    // check we are in the good ranges for match1 and match1xOrder
    assert checkFirstPass();

    secondPass();

    assert checkSecondPass();

    thirdPass();

    assert checkThirdPass();
  }

  private boolean checkFirstPass() {

    for (int j = 0; j < stampValue; j++) {
      assert match1[j] >= 0;
      assert match1[j] < ySize;
      assert match1xOrder[j] >= 0;
      assert match1xOrder[j] < stampValue;
    }

    return true;
  }

  private boolean checkSecondPass() {

    for (int j = 1; j < stampValue; j++) {
      assert match2[match2xOrder[j]] >= match2[match2xOrder[j - 1]];
    }

    return true;
  }

  private boolean checkThirdPass() {

    for (int j = 0; j < stampValue; j++) {
      assert xDomain[j].min() <= match3[j];
      assert xDomain[j].max() >= match3[j];
    }

    return true;
  }

  private void firstPass() {

    pFirst.clear();
    int xIndex = 0;
    int maxY;
    int match1xOrderIndex = 0;
    int top;

    for (int i = 0; i < ySize; i++) {
      // first we add all the x which min domain is y
      while ((xIndex < stampValue) && xDomain[xIndex].min() == i) {
        // add a new element with index to get it back after the good element
        // and the max of the domain of xNode to sort them.
        xDomain[xIndex].index = xIndex;
        pFirst.add(xDomain[xIndex]);
        xIndex++;
      }
      int u = 0;
      // second we add the maximum of these xs possible to the current y
      maxY = yDomain[1][i];
      while (!pFirst.isEmpty() && u < maxY) {
        top = pFirst.remove().index; // index of the first element of pFirst
        match1[top] = i;
        u++;
        // match1xOrder gives the order in which xs where in the priority queue
        // that sorted them by domain max by group of domain min.
        // That is there are first sorted by domain min and after by domain max.
        match1xOrder[match1xOrderIndex] = top;
        match1xOrderIndex++;

        if (xDomain[top].max() < i) {
          if (DEBUG) {
            log.debug("failure first pass");
          }

          throw Store.failException;
          // it was checked that the min == i so max cannot be under min. Well, yes there are cases
          // where it's useful.
        }
      }
    }

    // I add the test on the queue. It is possible if the maxY = 0 and is the last one visited
    // otherwise the element in the queue can be used by the next yNode.
    if (!pFirst.isEmpty()) {

      if (DEBUG) {
        log.debug("failure the queue is not empty");
      }

      throw Store.failException;
    }

    if (DEBUG) {
      StringBuilder sb = new StringBuilder("match1Xorder : ");
      for (int aMatch1XOrder : match1xOrder) {
        sb.append(aMatch1XOrder).append(" ");
      }
      log.debug("{}", sb);

      sb = new StringBuilder("match1 : ");
      for (int aMatch1 : match1) {
        sb.append(aMatch1).append(" ");
      }
      log.debug("{}", sb);
    }
  }

  private void secondPass() {

    pSecond.clear();
    int top;
    int xIndex = 0;
    int minY;
    int match2xOrderIndex = 0;
    int order;

    for (int i = 0; i < ySize; i++) {
      // I should iterate on the match1xOrder instead of the normal order
      // we take all the xs that where matched with yi in the first pass.
      while ((xIndex < stampValue) && (match1[match1xOrder[xIndex]] == i)) {
        order = match1xOrder[xIndex];
        xDomain[order].index = order;
        pSecond.add(xDomain[order]);
        xIndex++;
      }
      minY = yDomain[0][i];
      for (int l = 0; l < minY; l++) {
        if (pSecond.isEmpty()) {
          // failure need to be expressed
          if (DEBUG) {
            log.debug("failure second pass");
          }

          throw Store.failException;
        }
        top = pSecond.remove().index;
        match2[top] = i;

        match2xOrder[match2xOrderIndex] = top;
        match2xOrderIndex++;
        nbOfMatchPerY[i]++;
      }
      while (!pSecond.isEmpty() && pSecond.element().max() < i + 1) {
        top = pSecond.remove().index;
        match2[top] = i;
        match2xOrder[match2xOrderIndex] = top;
        match2xOrderIndex++;
        nbOfMatchPerY[i]++;
      }
    }

    if (DEBUG) {
      StringBuilder sb = new StringBuilder("match2Xorder : ");
      for (int aMatch2XOrder : match2xOrder) {
        sb.append(aMatch2XOrder).append(" ");
      }
      log.debug("{}", sb);

      sb = new StringBuilder("match2 : ");
      for (int aMatch2 : match2) {
        sb.append(aMatch2).append(" ");
      }
      log.debug("{}", sb);
    }
  }

  private void thirdPass() {

    int xIndex = stampValue - 1;
    int e;
    int xIdx = 0;

    System.arraycopy(match2, 0, match3, 0, stampValue);

    for (int i = ySize - 1; i >= 0; i--) {
      while ((xIndex >= 0) && (match2[match2xOrder[xIndex]] > i)) {
        xIndex--;
      }

      e = nbOfMatchPerY[i] - yDomain[1][i]; // excess of y mates
      while (e > 0) {

        assert match2[match2xOrder[xIndex]] == i;

        while (xIndex >= 0) {
          xIdx = match2xOrder[xIndex];
          if (match1[xIdx] == i) {
            xIndex--;
          } else {
            break;
          }
        }

        assert match1[xIdx] < i;
        assert match2[xIdx] == i;

        match3[xIdx] = match1[xIdx];
        nbOfMatchPerY[i]--;
        nbOfMatchPerY[match1[xIdx]]++;
        xIndex--;
        e--;
      }
    }
    if (DEBUG) {
      StringBuilder sb = new StringBuilder("match3 : ");
      for (int aMatch3 : match3) {
        sb.append(aMatch3).append(" ");
      }
      log.debug("{}", sb);
    }
  }

  // --------------------------------SCCs-------------------------------------//

  private void sccs() {

    int sccNb;
    int maxYreachedFromS;
    int[] compReachesLeft = new int[ySize];
    int[] compReachesRight = new int[ySize];
    int[] yreachesLeft = new int[ySize];
    int[] yreachesRight = new int[ySize];

    for (int i = 0; i < ySize; i++) {
      compOfY[i] = i;
    }

    sccNb = sccsWithoutS(compReachesLeft, compReachesRight, yreachesLeft, yreachesRight);
    // now compReaches(Left, Right) and compOfY contain the left and right most y per comp and to
    // which comp a y belong
    if (DEBUG) {
      log.debug("sccNb : {}", sccNb);
      StringBuilder sb = new StringBuilder("compReachesLeft ");
      for (int aCompReachesLeft : compReachesLeft) {
        sb.append(aCompReachesLeft).append(" ");
      }
      log.debug("{}", sb);

      sb = new StringBuilder("compReachesRight ");
      for (int aCompReachesRight : compReachesRight) {
        sb.append(aCompReachesRight).append(" ");
      }
      log.debug("{}", sb);

      sb = new StringBuilder("compOfY ");
      for (int aCompOfY : compOfY) {
        sb.append(aCompOfY).append(" ");
      }
      log.debug("{}", sb);
    }
    boolean[] reachedFromS = new boolean[sccNb];
    boolean[] reachesS = new boolean[sccNb];

    // reachedFromS and reachesS need to contain only value false.
    // by default satisfied by Java, therefore the two lines below are not needed.

    // init reachedFromS and reachesS
    int comp;
    for (int i = 0; i < ySize; i++) {
      comp = compOfY[i];
      assert comp >= 0;
      assert comp <= sccNb;

      // if there are stictly more match to y than the minimum required
      // an edge exist from s to y
      if (yDomain[0][i] < nbOfMatchPerY[i]) {
        reachedFromS[comp] = true;
      }

      // if there are strictly less match to y than the maximum possible
      // an edge exist from y to s
      if (yDomain[1][i] > nbOfMatchPerY[i]) {
        reachesS[comp] = true;
      }
    }

    maxYreachedFromS = -1;
    int maxYreachesS = -1;

    int C;
    for (int i = 0; i < ySize; i++) {
      C = compOfY[i];

      assert C >= 0;
      assert C <= sccNb;

      // if the max y that can be reached is greater than the current y,
      // that the comp it belongs to can be reached from s.
      if (maxYreachedFromS >= i) {
        reachedFromS[C] = true;
      }

      // if it's reached we can extand the max y reached to the compReachesRight of the component
      if (reachedFromS[C]) {
        maxYreachedFromS = Math.max(maxYreachedFromS, compReachesRight[C]);
      }

      // same in the other way : if the ReachesLeft of the comp is under the max y that
      // reaches S this comp reaches S
      if (compReachesLeft[C] <= maxYreachesS) {
        reachesS[C] = true;
      }

      // if it's reachesS we can extand the max Y that reaches it to the current y.
      if (reachesS[C]) {
        maxYreachesS = Math.max(maxYreachesS, i);
      }
    }

    // same as before but for minimum

    int minYreachedFromS = ySize;
    int minYreachesS = ySize;

    for (int i = ySize - 1; i >= 0; i--) {
      C = compOfY[i];
      assert C >= 0;
      assert C <= sccNb;
      if (minYreachedFromS <= i) {
        reachedFromS[C] = true;
      }

      if (reachedFromS[C]) {
        minYreachedFromS = Math.min(minYreachedFromS, compReachesLeft[C]);
      }

      if (compReachesRight[C] >= minYreachesS) {
        reachesS[C] = true;
      }

      if (reachesS[C]) {
        minYreachesS = Math.min(minYreachesS, i);
      }
    }

    // merge all comp that are strongly connected through s and
    // give this new comp a new number

    for (int i = 0; i < ySize; i++) {
      if (reachesS[compOfY[i]] && reachedFromS[compOfY[i]]) {
        compOfY[i] = sccNb;
      }
    }

    if (DEBUG) {
      StringBuilder sb = new StringBuilder("compOfY after S ");
      for (int aCompOfY : compOfY) {
        sb.append(aCompOfY).append(" ");
      }
      log.debug("{}", sb);
    }
  }

  private int sccsWithoutS(
      int[] compReachesLeft, int[] compReachesRight, int[] yreachesLeft, int[] yreachesRight) {

    Component C;
    Component C1;
    int sccNb = 0;
    S1.clear();
    S2.clear();

    reachedFromY(yreachesLeft, yreachesRight);

    // init all componant as containing only one y and set these component
    // reachesLeft and reachesRight to y reachesLeft and Right
    for (int y = 0; y < ySize; y++) {
      compReachesLeft[y] = yreachesLeft[y];
      compReachesRight[y] = yreachesRight[y];
    }

    for (int y = 0; y < ySize; y++) {
      // set comp to (root, rightmostY, maxX)
      C = new Component(y, y, yreachesRight[y]);

      if (S2.isEmpty()) {
        S1.push(y);
        S2.push(C);
        continue;
      }

      // once S2 not empty
      // this first part treat the case we have a new component.
      // (c1.max < C.root)

      while ((!S2.isEmpty()) && (S2.peek().maxX < C.root)) {
        compReachesLeft[sccNb] = ySize;
        compReachesRight[sccNb] = -1;

        assert !S1.isEmpty();

        C1 = S2.pop();
        while (!S1.isEmpty() && S1.peek() >= C1.root && S1.peek() <= C1.rightmostY) {
          int popY;
          popY = S1.pop();
          compOfY[popY] = sccNb;
          compReachesLeft[sccNb] = Math.min(compReachesLeft[sccNb], yreachesLeft[popY]);
          compReachesRight[sccNb] = Math.max(compReachesRight[sccNb], yreachesRight[popY]);
        }
        sccNb++;
      }

      assert S2.isEmpty() || S2.peek().maxX >= C.root;

      // this second part treat the case the new c1 is in fact attainable by the current component

      while (!S2.isEmpty() && yreachesLeft[y] <= S2.peek().rightmostY) {
        C1 = S2.pop();
        C.maxX = Math.max(C.maxX, C1.maxX);
        C.root =
            C1.root; // as they are taken in order from left to right c1.root is always < C.root
        C.rightmostY = y; // same remark
      }

      assert S2.isEmpty() || yreachesLeft[y] > S2.peek().rightmostY && S2.peek().maxX >= C.root;

      S1.push(y);
      S2.push(C);
    } // end for

    // for every component still on the pile update compOfY, compReachesLeft and Right, and sccNb
    while (!S2.isEmpty()) {
      assert !S1.isEmpty();
      C = S2.pop();
      compReachesLeft[sccNb] = ySize;
      compReachesRight[sccNb] = -1;

      while (!S1.isEmpty() && S1.peek() >= C.root && S1.peek() <= C.rightmostY) {
        int y;
        y = S1.pop();
        compOfY[y] = sccNb;
        compReachesLeft[sccNb] = Math.min(compReachesLeft[sccNb], yreachesLeft[y]);
        compReachesRight[sccNb] = Math.max(compReachesRight[sccNb], yreachesRight[y]);
      }
      sccNb++;
    }

    assert S1.isEmpty();
    return sccNb;
  }

  private void reachedFromY(int[] yreachesLeft, int[] yreachesRight) {

    for (int i = 0; i < ySize; i++) {
      yreachesLeft[i] = i;
      yreachesRight[i] = i;
    }

    int i;
    // we check what is the minimum ymin and the maximum ymax reachable by y.
    // For that we check every x linked to y to keep the minimal and maximal domain
    // bondaries of these xs.
    for (int j = 0; j < stampValue; j++) {
      i = match3[j];
      assert i >= 0;
      assert i < ySize;
      yreachesLeft[i] = Math.min(yreachesLeft[i], xDomain[j].min());
      yreachesRight[i] = Math.max(yreachesRight[i], xDomain[j].max());
    }
    if (DEBUG) {
      StringBuilder sb = new StringBuilder("yreachesLeft ");
      for (i = 0; i < yreachesLeft.length; i++) {
        sb.append(yreachesLeft[i]).append(" ");
      }
      log.debug("{}", sb);

      sb = new StringBuilder("yreachesRight ");
      for (i = 0; i < yreachesRight.length; i++) {
        sb.append(yreachesRight[i]).append(" ");
      }
      log.debug("{}", sb);
    }
  }

  // ------------------------USED_FOR_REDUCING_DOMAIN--------------------------//

  private void putToTheEnd(IntVar[] list, int element) {
    // I swap the element with the last one before the stamp
    // which have nothing to do in the no-more-seen variables
    IntVar v1 = list[element];
    int currentStampValue = stamp.value();
    list[element] = list[currentStampValue];
    // update the index of the moved element which was behind the stamp value
    xNodesHash.put(list[currentStampValue], element);
    // and update the one put to the end
    xNodesHash.put(v1, currentStampValue);
    list[currentStampValue] = v1;
  }

  // ---------------------------COUNT_BOUND_CONCISTENCY-----------------------//

  private void countBoundConsistency(Store store) {
    int[] max_u = new int[ySize];
    Arrays.fill(max_u, ySize - 1);

    int[] min_l = new int[ySize];
    Arrays.fill(min_l, 0);

    upperCount(max_u);
    lowerCount(min_l);

    if (DEBUG) {
      StringBuilder sb = new StringBuilder("max_u ");
      for (int aMax_u : max_u) {
        sb.append(aMax_u).append(" ");
      }
      log.debug("{}", sb);

      sb = new StringBuilder("min_l ");
      for (int aMin_l : min_l) {
        sb.append(aMin_l).append(" ");
      }
      log.debug("{}", sb);
    }
    for (int i = 0; i < ySize; i++) {
      if (DEBUG) {
        log.debug(
            "do pruning [{},{}] => [{},{}]",
            counters[i].min(),
            counters[i].max(),
            min_l[i],
            max_u[i]);
      }

      if (yDomain[1][i] != max_u[i] || yDomain[0][i] != min_l[i]) {
        yDomain[0][i] = min_l[i];
        yDomain[1][i] = max_u[i];
      }
    }
    // add the rest of nodes not treated in this pass that was already singleton
    if (DEBUG) {
      log.debug("increase yDomain with xNodes singleton");
    }

    for (int i = 0; i < xSize; i++) {
      if (x[i].singleton()) {
        // Change, check.
        int value = findPosition(x[i].value(), domainHash);
        yDomain[1][value]++;
        yDomain[0][value]++;
      }
    }

    if (DEBUG) {
      log.debug("set yNodes");
    }

    for (int i = 0; i < ySize; i++) {
      counters[i].domain.in(store.level, counters[i], yDomain[0][i], yDomain[1][i]);
    }
  }

  private void upperCount(int[] maxU) {

    int xIndex;
    int xIdx;
    pCount.clear();
    xIndex = stampValue - 1;
    for (int i = ySize - 1; i >= 0; i--) {
      while (xIndex >= 0) {
        xIdx = match2xOrder[xIndex];
        if (match2[xIdx] == i) {
          pCount.add(match1[xIdx]);
          xIndex--;
        } else {
          break;
        }
      }
      maxU[i] = Math.min(yDomain[1][i], pCount.size());
      for (int l = 0; l < yDomain[0][i]; l++) {
        assert !pCount.isEmpty();
        pCount.remove();
      }

      // well see how it works for the second part of the condition
      while (!pCount.isEmpty() && pCount.peek() == i) {
        pCount.remove();
      }
    }
  }

  private void lowerCount(int[] minL) {
    int xIndex;
    int count;
    int xIdx;
    pCount.clear();
    xIndex = stampValue - 1;
    for (int i = ySize - 1; i >= 0; i--) {
      count = 0;
      while (xIndex >= 0) {
        xIdx = match2xOrder[xIndex];
        if (match2[xIdx] == i) {
          pCount.add(match1[xIdx]);
          xIndex--;
        } else {
          break;
        }
      }

      for (int l = 0; l < yDomain[0][i]; l++) {
        assert !pCount.isEmpty();
        pCount.remove();
        count++;
      }

      while (!pCount.isEmpty() && pCount.peek() == i) {
        pCount.remove();
        count++;
      }

      minL[i] = count;
      while ((!pCount.isEmpty()) && (count < yDomain[1][i])) {
        pCount.remove();
        count++;
      }
    }
  }

  // ----------------------------SORT_AND_COMPARATOR--------------------------//

  private void sortXbyDomainMin() {
    // I need to sort only the part concern, otherwise old values still after
    // the stamp value will interfer with the sorting
    Arrays.sort(xDomain, 0, stampValue, compareLowerBound);
  }

  private int findPosition(int value, int[] values) {

    int left = 0;
    int right = values.length - 1;

    int position = (left + right) >> 1;

    if (DEBUG) {
      StringBuilder sb = new StringBuilder("Looking for ").append(value);
      for (int v : values) {
        sb.append(" val ").append(v);
      }
      log.debug("{}", sb);
    }

    while (left + 1 < right) {

      if (DEBUG) {
        log.debug("left {} right {} position {}", left, right, position);
      }

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

  // -----------------------INNER CLASSES-----------------------------------//
  private static class Component {

    int root;
    int rightmostY;
    int maxX;

    public Component(int root, int rightmostY, int maxX) {
      this.root = root;
      this.rightmostY = rightmostY;
      this.maxX = maxX;
    }
  }

  private static class Xdomain extends IntervalDomain {
    Var twin;
    int index;

    Xdomain(Var twin, int min, int max) {
      super(min, max);
      this.twin = twin;
    }
  }
}
