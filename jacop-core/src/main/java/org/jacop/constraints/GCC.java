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

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.core.InitOnce;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;

/**
 * GCC constraint counts the number of occurences of given values in x variables. The counters are
 * specified by y's. The occurence of all values in the domain of xs is counted.
 *
 * <p>It implements the bound consistency algorithm of I. Katriel and S. Thiel, "Complete bound
 * consistency for the global cardinality constraint", Constraints 10(3), 2005. The bounds of the x
 * variables (over the union of their values) and the bounds of the counters are made bound
 * consistent.
 *
 * <p>We would like to thank Irit Katriel for making the code of GCC in C she wrote available to us.
 *
 * @author Jocelyne Lotfi and Radoslaw Szymanek.
 * @version 5.0
 */
@SuppressWarnings(
    "checkstyle:AbbreviationAsWordInName") // GCC is standard constraint programming terminology
public class GCC extends Constraint implements SatisfiedPresent {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It specifies variables x whose values are counted. The variables before the stamp are not
   * singletons, the ones after it are.
   */
  private final IntVar[] x;

  /**
   * It species variables counters for counting occurences of each possible value from the intial
   * domain of x variables.
   */
  protected final IntVar[] counters;

  private final int xSize;
  private final int ySize;

  /** Counters of values that no x variable can take, set to zero at the first consistency call. */
  private Set<IntVar> zeroCounters;

  /** The counted values in increasing order; a value is referred to by its position here. */
  private int[] domainHash;

  /** The counted values as a domain. */
  private IntervalDomain countedValues;

  /** Whether some x variable can take a value that is not counted, so x is restricted first. */
  private boolean restrictX;

  /** Whether the counted values form an interval, so the position of a value is value - base. */
  private boolean contiguous;

  private int base;

  /** The bounds of the counters, less the variables that are already assigned. */
  private final int[] yMin;

  private final int[] yMax;

  /** The number of assigned x variables taking each value. */
  private final int[] singletons;

  /** The unassigned x variables sorted by the position of their minimum: index and bounds. */
  private final int[] slotX;

  private final int[] slotMin;
  private final int[] slotMax;
  private final int[] unsortedMin;
  private final int[] unsortedMax;
  private final int[] countOfMin;

  /** The first matching, which may not respect the lower bounds of the counters. */
  private final int[] match1;

  /** The second matching, which may not respect the upper bounds of the counters. */
  private final int[] match2;

  /** The matching respecting both bounds, constructed from the first and the second one. */
  private final int[] match3;

  private final int[] match1xOrder;
  private final int[] match2xOrder;
  private final int[] nbOfMatchPerY;
  private final int[] compOfY;
  private final int[] compReachesLeft;
  private final int[] compReachesRight;
  private final int[] yReachesLeft;
  private final int[] yReachesRight;
  private final boolean[] reachedFromS;
  private final boolean[] reachesS;
  private final int[] maxU;
  private final int[] minL;

  /** Stack of values and stack of components (root, rightmost value, maximum reached value). */
  private final int[] s1;

  private final int[] s2Root;
  private final int[] s2RightmostY;
  private final int[] s2MaxX;

  private final IntHeap heap;

  /** One-time work of the first consistency call. */
  final InitOnce init = new InitOnce();

  TimeStamp<Integer> stamp;
  private int stampValue;

  /**
   * It constructs global cardinality constraint.
   *
   * @param x variables which values are counted.
   * @param counters variables which count the values.
   */
  public GCC(IntVar[] x, IntVar[] counters) {
    this(x, counters, null);
  }

  /**
   * It constructs global cardinality constraint where counters[i] counts the occurrences of value
   * firstValue + i. Unlike {@link #GCC(IntVar[], IntVar[])} it does not depend on the current
   * domains of x, so x may contain singletons or variables that cannot take some counted value. The
   * variables x can take only the counted values.
   *
   * @param x variables which values are counted.
   * @param counters variables which count the values firstValue, firstValue + 1, ...
   * @param firstValue the value counted by counters[0].
   */
  public GCC(IntVar[] x, IntVar[] counters, int firstValue) {
    this(x, counters, Integer.valueOf(firstValue));
  }

  private GCC(IntVar[] x, IntVar[] counters, Integer firstValue) {

    checkInputForNullness(new String[] {"x", "counters"}, x, counters);
    checkInputForDuplicationSkipSingletons("x", x);

    this.queueIndex = 1;
    numberId = idNumber.incrementAndGet();

    counters =
        firstValue == null
            ? removeZeroCounters(x, counters)
            : removeZeroCounters(x, counters, firstValue);

    xSize = x.length;
    ySize = counters.length;

    this.x = Arrays.copyOf(x, xSize);
    this.counters = Arrays.copyOf(counters, ySize);

    yMin = new int[ySize];
    yMax = new int[ySize];
    singletons = new int[ySize];
    slotX = new int[xSize];
    slotMin = new int[xSize];
    slotMax = new int[xSize];
    unsortedMin = new int[xSize];
    unsortedMax = new int[xSize];
    countOfMin = new int[ySize + 1];
    match1 = new int[xSize];
    match2 = new int[xSize];
    match3 = new int[xSize];
    match1xOrder = new int[xSize];
    match2xOrder = new int[xSize];
    nbOfMatchPerY = new int[ySize];
    compOfY = new int[ySize];
    compReachesLeft = new int[ySize];
    compReachesRight = new int[ySize];
    yReachesLeft = new int[ySize];
    yReachesRight = new int[ySize];
    reachedFromS = new boolean[ySize];
    reachesS = new boolean[ySize];
    maxU = new int[ySize];
    minL = new int[ySize];
    s1 = new int[ySize];
    s2Root = new int[ySize];
    s2RightmostY = new int[ySize];
    s2MaxX = new int[ySize];
    heap = new IntHeap(xSize);

    setScope(Stream.concat(Arrays.stream(x), Arrays.stream(counters)));
  }

  /**
   * It constructs global cardinality constraint.
   *
   * @param x variables which values are counted.
   * @param counters variables which count the values.
   */
  public GCC(List<? extends IntVar> x, List<? extends IntVar> counters) {

    this(x.toArray(IntVar[]::new), counters.toArray(IntVar[]::new));
  }

  private IntVar[] removeZeroCounters(IntVar[] x, IntVar[] counters) {

    IntervalDomain d = new IntervalDomain();

    for (IntVar aX : x) {
      d = (IntervalDomain) d.union(aX.domain);
    }

    // there must be a counter for every value of the union of the x domains, or for every value
    // between its minimum and its maximum; it is not guessed which counters are superfluous
    if (d.getSize() != counters.length && (d.max() - d.min() + 1) != counters.length) {
      throw new IllegalArgumentException(
          "GCC failure : join domain of x variables doesn't cover all count variables");
    }

    if (d.getSize() == counters.length) {
      // the counters are of the values of the union, in increasing order
      int[] values = new int[counters.length];
      int i = 0;
      for (ValueEnumeration e = d.valueEnumeration(); e.hasMoreElements(); ) {
        values[i++] = e.nextElement();
      }
      return keepCounters(x, counters, values);
    }

    // the counters are of every value from the minimum of the union to its maximum
    return removeZeroCounters(x, counters, d.min());
  }

  /** The counters are of the values firstValue, firstValue + 1, ... */
  private IntVar[] removeZeroCounters(IntVar[] x, IntVar[] counters, int firstValue) {

    int[] values = new int[counters.length];
    for (int k = 0; k < counters.length; k++) {
      values[k] = firstValue + k;
    }
    return keepCounters(x, counters, values);
  }

  /**
   * Keeps the counters of the values some x variable can take, records their values in domainHash
   * and the other counters in zeroCounters.
   *
   * @param values values[i] is the value counted by counters[i], in increasing order.
   */
  private IntVar[] keepCounters(IntVar[] x, IntVar[] counters, int[] values) {

    IntervalDomain d = new IntervalDomain();
    for (IntVar aX : x) {
      d = (IntervalDomain) d.union(aX.domain);
    }

    List<IntVar> kept = new ArrayList<>();
    List<Integer> keptValues = new ArrayList<>();
    for (int k = 0; k < counters.length; k++) {
      if (d.contains(values[k])) {
        kept.add(counters[k]);
        keptValues.add(values[k]);
      } else {
        if (zeroCounters == null) {
          zeroCounters = new HashSet<>();
        }
        zeroCounters.add(counters[k]);
      }
    }

    domainHash = keptValues.stream().mapToInt(Integer::intValue).toArray();
    countedValues = new IntervalDomain();
    for (int v : domainHash) {
      countedValues.unionAdapt(v, v);
    }
    restrictX = !countedValues.contains(d);
    if (domainHash.length > 0) {
      base = domainHash[0];
      contiguous = domainHash[domainHash.length - 1] - base + 1 == domainHash.length;
    }

    return kept.toArray(new IntVar[0]);
  }

  @Override
  public void consistency(Store store) {
    if (init.begin(store)) {
      if (zeroCounters != null) {
        for (IntVar zeroCounter : zeroCounters) {
          zeroCounter.domain.inValue(store.level, zeroCounter, 0);
        }
      }
      if (restrictX) {
        for (IntVar v : x) {
          v.domain.in(store.level, v, countedValues);
        }
      }
    }
    // The new bounds are the bounds over the solutions of the problem in which every variable
    // ranges over its bounds, so imposing them leaves that problem with the same solutions. Only
    // when a variable ends up with other bounds, because of a hole in its domain or because it is
    // both counted and a counter, the problem changes and the propagation is repeated.
    boolean repeat;
    do {
      moveSingletonsToTheEnd();
      readCounterBounds();
      sortXbyDomainMin();
      findGeneralizedMatching();
      sccs();
      countBoundConsistency(store);
      pruneXDomains(store);
      repeat = boundsDifferFromPruned();
      verifyCountersAfterPruning();
    } while (repeat);
  }

  /** Moves the assigned variables after the stamp, which then counts the unassigned ones. */
  private void moveSingletonsToTheEnd() {
    int end = stamp.value();
    int k = 0;
    while (k < end) {
      if (x[k].singleton()) {
        end--;
        IntVar v = x[k];
        x[k] = x[end];
        x[end] = v;
      } else {
        k++;
      }
    }
    if (end != stamp.value()) {
      stamp.update(end);
    }
    stampValue = end;
  }

  /** Reads the counter bounds and takes out the variables that are already assigned. */
  private void readCounterBounds() {
    for (int i = 0; i < ySize; i++) {
      yMin[i] = counters[i].min();
      yMax[i] = counters[i].max();
    }
    Arrays.fill(singletons, 0);
    for (int k = stampValue; k < xSize; k++) {
      int value = position(x[k].value());
      singletons[value]++;
      if (yMin[value] > 0) {
        yMin[value]--;
      }
      yMax[value]--;
      if (yMax[value] < 0) {
        throw Store.failException;
      }
    }
  }

  /** Sorts the unassigned variables by the position of their minimum with a counting sort. */
  private void sortXbyDomainMin() {
    Arrays.fill(countOfMin, 0);
    for (int k = 0; k < stampValue; k++) {
      unsortedMin[k] = position(x[k].min());
      unsortedMax[k] = position(x[k].max());
      countOfMin[unsortedMin[k] + 1]++;
    }
    for (int i = 1; i <= ySize; i++) {
      countOfMin[i] += countOfMin[i - 1];
    }
    for (int k = 0; k < stampValue; k++) {
      int j = countOfMin[unsortedMin[k]]++;
      slotX[j] = k;
      slotMin[j] = unsortedMin[k];
      slotMax[j] = unsortedMax[k];
    }
  }

  private void pruneXDomains(Store store) {
    for (int j = 0; j < stampValue; j++) {
      int comp = compOfY[match3[j]];
      int cutMin = slotMin[j];
      int cutMax = slotMax[j];
      while (comp != compOfY[cutMin]) {
        cutMin++;
      }
      while (comp != compOfY[cutMax]) {
        cutMax--;
      }
      IntVar v = x[slotX[j]];
      v.domain.in(store.level, v, domainHash[cutMin], domainHash[cutMax]);
      slotMin[j] = cutMin;
      slotMax[j] = cutMax;
    }
  }

  /** Whether some variable has bounds other than the ones the propagation has just imposed. */
  private boolean boundsDifferFromPruned() {
    for (int j = 0; j < stampValue; j++) {
      IntVar v = x[slotX[j]];
      if (v.min() != domainHash[slotMin[j]] || v.max() != domainHash[slotMax[j]]) {
        return true;
      }
    }
    for (int i = 0; i < ySize; i++) {
      if (counters[i].min() != yMin[i] || counters[i].max() != yMax[i]) {
        return true;
      }
    }
    return false;
  }

  private void verifyCountersAfterPruning() {
    for (int i = 0; i < xSize; i++) {
      if (!x[i].singleton()) {
        continue;
      }
      int value = position(x[i].value());
      yMax[value]--;
      if (yMax[value] < 0) {
        throw Store.failException;
      }
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void impose(Store store) {

    stamp = new TimeStamp<>(store, xSize);

    super.impose(store);
  }

  @Override
  public boolean satisfied() {

    if (!grounded()) {
      return false;
    }

    int[] count = new int[ySize];
    for (IntVar xVar : x) {
      int p = position(xVar.value());
      if (p < 0 || p >= ySize || domainHash[p] != xVar.value()) {
        return false;
      }
      count[p]++;
    }

    for (int i = 0; i < ySize; i++) {
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

  // -----------------------FIND_GENERALIZED_MATCHING--------------------------------//

  private void findGeneralizedMatching() {

    Arrays.fill(nbOfMatchPerY, 0);

    firstPass();
    secondPass();
    thirdPass();

    if (ASSERTS_ENABLED) {
      for (int j = 0; j < stampValue; j++) {
        if (match3[j] < slotMin[j] || match3[j] > slotMax[j]) {
          throw new IllegalStateException("GCC matching outside the domain of a variable");
        }
      }
    }
  }

  /** Matches the variables to values by earliest deadline, respecting the counter maximums. */
  private void firstPass() {

    heap.clear(slotMax);
    int xIndex = 0;
    int orderIndex = 0;

    for (int i = 0; i < ySize; i++) {
      while (xIndex < stampValue && slotMin[xIndex] == i) {
        heap.push(xIndex++);
      }
      int maxY = yMax[i];
      for (int u = 0; u < maxY && !heap.isEmpty(); u++) {
        int top = heap.pop();
        if (slotMax[top] < i) {
          throw Store.failException;
        }
        match1[top] = i;
        match1xOrder[orderIndex++] = top;
      }
    }

    if (!heap.isEmpty()) {
      throw Store.failException;
    }
  }

  /** Moves matched variables to the right so that the counter minimums are respected. */
  private void secondPass() {

    heap.clear(slotMax);
    int xIndex = 0;
    int orderIndex = 0;

    for (int i = 0; i < ySize; i++) {
      while (xIndex < stampValue && match1[match1xOrder[xIndex]] == i) {
        heap.push(match1xOrder[xIndex++]);
      }
      for (int l = 0; l < yMin[i]; l++) {
        if (heap.isEmpty()) {
          throw Store.failException;
        }
        int top = heap.pop();
        match2[top] = i;
        match2xOrder[orderIndex++] = top;
        nbOfMatchPerY[i]++;
      }
      while (!heap.isEmpty() && slotMax[heap.peek()] < i + 1) {
        int top = heap.pop();
        match2[top] = i;
        match2xOrder[orderIndex++] = top;
        nbOfMatchPerY[i]++;
      }
    }
  }

  /** Combines both matchings into one that respects the minimums and the maximums. */
  private void thirdPass() {

    int xIndex = stampValue - 1;
    int xIdx = 0;

    System.arraycopy(match2, 0, match3, 0, stampValue);

    for (int i = ySize - 1; i >= 0; i--) {
      while (xIndex >= 0 && match2[match2xOrder[xIndex]] > i) {
        xIndex--;
      }

      int excess = nbOfMatchPerY[i] - yMax[i];
      while (excess > 0) {

        while (xIndex >= 0) {
          xIdx = match2xOrder[xIndex];
          if (match1[xIdx] == i) {
            xIndex--;
          } else {
            break;
          }
        }

        if (ASSERTS_ENABLED && (match1[xIdx] >= i || match2[xIdx] != i)) {
          throw new IllegalStateException("GCC third pass found no variable to move");
        }

        match3[xIdx] = match1[xIdx];
        nbOfMatchPerY[i]--;
        nbOfMatchPerY[match1[xIdx]]++;
        xIndex--;
        excess--;
      }
    }
  }

  // --------------------------------SCCs-------------------------------------//

  private void sccs() {
    for (int i = 0; i < ySize; i++) {
      compOfY[i] = i;
    }
    int sccNb = sccsWithoutS();
    Arrays.fill(reachedFromS, 0, sccNb, false);
    Arrays.fill(reachesS, 0, sccNb, false);

    for (int i = 0; i < ySize; i++) {
      int comp = compOfY[i];
      if (yMin[i] < nbOfMatchPerY[i]) {
        reachedFromS[comp] = true;
      }
      if (yMax[i] > nbOfMatchPerY[i]) {
        reachesS[comp] = true;
      }
    }

    int maxYreachedFromS = -1;
    int maxYreachesS = -1;
    for (int i = 0; i < ySize; i++) {
      int c = compOfY[i];
      if (maxYreachedFromS >= i) {
        reachedFromS[c] = true;
      }
      if (reachedFromS[c]) {
        maxYreachedFromS = Math.max(maxYreachedFromS, compReachesRight[c]);
      }
      if (compReachesLeft[c] <= maxYreachesS) {
        reachesS[c] = true;
      }
      if (reachesS[c]) {
        maxYreachesS = Math.max(maxYreachesS, i);
      }
    }

    int minYreachedFromS = ySize;
    int minYreachesS = ySize;
    for (int i = ySize - 1; i >= 0; i--) {
      int c = compOfY[i];
      if (minYreachedFromS <= i) {
        reachedFromS[c] = true;
      }
      if (reachedFromS[c]) {
        minYreachedFromS = Math.min(minYreachedFromS, compReachesLeft[c]);
      }
      if (compReachesRight[c] >= minYreachesS) {
        reachesS[c] = true;
      }
      if (reachesS[c]) {
        minYreachesS = Math.min(minYreachesS, i);
      }
    }

    // the components that reach the sink and are reached from it form one component
    for (int i = 0; i < ySize; i++) {
      if (reachesS[compOfY[i]] && reachedFromS[compOfY[i]]) {
        compOfY[i] = sccNb;
      }
    }
  }

  /** Computes the components of the values in the residual graph without the sink. */
  private int sccsWithoutS() {

    int sccNb = 0;
    int s1Size = 0;
    int s2Size = 0;

    reachedFromY();

    System.arraycopy(yReachesLeft, 0, compReachesLeft, 0, ySize);
    System.arraycopy(yReachesRight, 0, compReachesRight, 0, ySize);

    for (int y = 0; y < ySize; y++) {
      int root = y;
      int rightmostY = y;
      int maxX = yReachesRight[y];

      while (s2Size > 0 && s2MaxX[s2Size - 1] < root) {
        s2Size--;
        s1Size = popComponent(sccNb++, s1Size, s2Root[s2Size], s2RightmostY[s2Size]);
      }

      while (s2Size > 0 && yReachesLeft[y] <= s2RightmostY[s2Size - 1]) {
        s2Size--;
        maxX = Math.max(maxX, s2MaxX[s2Size]);
        root = s2Root[s2Size];
        rightmostY = y;
      }

      s1[s1Size++] = y;
      s2Root[s2Size] = root;
      s2RightmostY[s2Size] = rightmostY;
      s2MaxX[s2Size] = maxX;
      s2Size++;
    }

    while (s2Size > 0) {
      s2Size--;
      s1Size = popComponent(sccNb++, s1Size, s2Root[s2Size], s2RightmostY[s2Size]);
    }

    if (ASSERTS_ENABLED && s1Size != 0) {
      throw new IllegalStateException("GCC left values outside of the components");
    }
    return sccNb;
  }

  private int popComponent(int sccNb, int s1Size, int root, int rightmostY) {
    compReachesLeft[sccNb] = ySize;
    compReachesRight[sccNb] = -1;
    while (s1Size > 0 && s1[s1Size - 1] >= root && s1[s1Size - 1] <= rightmostY) {
      int popY = s1[--s1Size];
      compOfY[popY] = sccNb;
      compReachesLeft[sccNb] = Math.min(compReachesLeft[sccNb], yReachesLeft[popY]);
      compReachesRight[sccNb] = Math.max(compReachesRight[sccNb], yReachesRight[popY]);
    }
    return s1Size;
  }

  /** Computes, for every value, the smallest and the largest value its matched variables reach. */
  private void reachedFromY() {

    for (int i = 0; i < ySize; i++) {
      yReachesLeft[i] = i;
      yReachesRight[i] = i;
    }

    for (int j = 0; j < stampValue; j++) {
      int i = match3[j];
      yReachesLeft[i] = Math.min(yReachesLeft[i], slotMin[j]);
      yReachesRight[i] = Math.max(yReachesRight[i], slotMax[j]);
    }
  }

  // ---------------------------COUNT_BOUND_CONCISTENCY-----------------------//

  private void countBoundConsistency(Store store) {

    upperCount();
    lowerCount();

    // the counters also count the assigned variables; yMax is reused by the check after pruning
    for (int i = 0; i < ySize; i++) {
      yMin[i] = minL[i] + singletons[i];
      yMax[i] = maxU[i] + singletons[i];
    }

    for (int i = 0; i < ySize; i++) {
      counters[i].domain.in(store.level, counters[i], yMin[i], yMax[i]);
    }
  }

  private void upperCount() {

    heap.clear(null);
    int xIndex = stampValue - 1;
    for (int i = ySize - 1; i >= 0; i--) {
      while (xIndex >= 0) {
        int xIdx = match2xOrder[xIndex];
        if (match2[xIdx] == i) {
          // a max-heap of the first matching, kept as a min-heap of negated values
          heap.push(-match1[xIdx]);
          xIndex--;
        } else {
          break;
        }
      }
      maxU[i] = Math.min(yMax[i], heap.size());
      for (int l = 0; l < yMin[i]; l++) {
        heap.pop();
      }

      while (!heap.isEmpty() && -heap.peek() == i) {
        heap.pop();
      }
    }
  }

  private void lowerCount() {

    heap.clear(null);
    int xIndex = stampValue - 1;
    for (int i = ySize - 1; i >= 0; i--) {
      int count = 0;
      while (xIndex >= 0) {
        int xIdx = match2xOrder[xIndex];
        if (match2[xIdx] == i) {
          heap.push(-match1[xIdx]);
          xIndex--;
        } else {
          break;
        }
      }

      for (int l = 0; l < yMin[i]; l++) {
        heap.pop();
        count++;
      }

      while (!heap.isEmpty() && -heap.peek() == i) {
        heap.pop();
        count++;
      }

      minL[i] = count;
      while (!heap.isEmpty() && count < yMax[i]) {
        heap.pop();
        count++;
      }
    }
  }

  /** Returns the position of a counted value. */
  private int position(int value) {
    if (contiguous) {
      return value - base;
    }
    return Arrays.binarySearch(domainHash, value);
  }

  // -----------------------INNER CLASSES-----------------------------------//

  /** A binary min-heap of ints ordered by keys[element], or by the element itself without keys. */
  private static final class IntHeap {

    private final int[] elements;
    private int size;
    private int[] keys;

    IntHeap(int capacity) {
      elements = new int[Math.max(capacity, 1)];
    }

    void clear(int[] keys) {
      this.keys = keys;
      size = 0;
    }

    boolean isEmpty() {
      return size == 0;
    }

    int size() {
      return size;
    }

    int peek() {
      return elements[0];
    }

    private int key(int element) {
      return keys == null ? element : keys[element];
    }

    void push(int element) {
      int i = size++;
      int k = key(element);
      while (i > 0) {
        int parent = (i - 1) >>> 1;
        if (key(elements[parent]) <= k) {
          break;
        }
        elements[i] = elements[parent];
        i = parent;
      }
      elements[i] = element;
    }

    int pop() {
      if (size == 0) {
        throw Store.failException;
      }
      int top = elements[0];
      int last = elements[--size];
      int k = key(last);
      int i = 0;
      int half = size >>> 1;
      while (i < half) {
        int child = 2 * i + 1;
        int right = child + 1;
        if (right < size && key(elements[right]) < key(elements[child])) {
          child = right;
        }
        if (k <= key(elements[child])) {
          break;
        }
        elements[i] = elements[child];
        i = child;
      }
      if (size > 0) {
        elements[i] = last;
      }
      return top;
    }
  }
}
