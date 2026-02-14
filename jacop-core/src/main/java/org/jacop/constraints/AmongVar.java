/*
 * AmongVar.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2008 Polina Maakeva and Radoslaw Szymanek
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

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.MutableDomain;
import org.jacop.core.MutableDomainValue;
import org.jacop.core.MutableVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;

/**
 * Among constraint in its general form. It establishes the following relation. The given number N
 * of X`s take values from the set specified by Y`s.
 *
 * <p>This constraint significantly extends the algorithms presented in the literature as it does
 * not use the decomposition into simpler constraints.
 *
 * <p>Therefore as a result, it provides stronger pruning methods without noticeable increase in the
 * execution time. The large part of the computation is reused across following executions of the
 * consistency function. The strength of propagation algorithm is incomporable to BC.
 *
 * @author Polina Makeeva and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class AmongVar extends Constraint implements UsesQueueVariable, Stateful, SatisfiedPresent {

  /** It turns out printing debugging information. */
  public static final boolean DEBUG_ALL = false;

  /** Number of Among constraints created. */
  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * List of variables x which values are checked against values of variables y. Each x is counted
   * only once as equal to one of the elements of list y.
   */
  private final IntVar[] listOfX;

  /** It specifies what values we are counting in the list of x's. */
  private final IntVar[] listOfY;

  // Derived variables
  /**
   * It specifies the number of x variables equal to at least one value present in the list of y.
   */
  private final IntVar n;

  private final LinkedHashSet<Integer> variableQueueY = new LinkedHashSet<>();
  // All variables attributes
  private Map<IntVar, Integer> xIndex;
  private Map<IntVar, Integer> yIndex;
  // FIXME, check if timestamp over IntervalDomain is not better/cleaner.
  private MutableVar lbS;
  private MutableVar futureLbS;
  // Time stamps
  private TimeStamp<Integer> lb0Ts;
  private TimeStamp<Integer> ub0Ts;
  private TimeStamp<Integer> yGrounded;
  private TimeStamp<Integer> xGrounded;

  /**
   * It constructs an AmongVar constraint.
   *
   * @param listOfX the list of variables whose equality to other set of variables we count
   * @param listOfY the list of variable to which equality is counted.
   * @param n how many variables from list x are equal to at least one variable from list y.
   */
  public AmongVar(IntVar[] listOfX, IntVar[] listOfY, IntVar n) {

    checkInputForNullness(
        new String[] {"listOfX", "listOfY", "n"}, listOfX, listOfY, new Object[] {n});
    checkInputForDuplication("listOfX", listOfX);
    checkInputForDuplication("listOfY", listOfY);

    this.queueIndex = 1;

    numberId = idNumber.incrementAndGet();

    this.listOfX = Arrays.copyOf(listOfX, listOfX.length);
    this.listOfY = Arrays.copyOf(listOfY, listOfY.length);
    this.n = n;

    setScope(
        Stream.concat(Stream.concat(Arrays.stream(listOfX), Arrays.stream(listOfY)), Stream.of(n)));
  }

  /**
   * It constructs an AmongVar constraint.
   *
   * @param listOfX the list of variables whose equality to other set of variables we count
   * @param listOfY the list of variable to which equality is counted.
   * @param n how many variables from list x are equal to at least one variable from list y.
   */
  public AmongVar(List<? extends IntVar> listOfX, List<? extends IntVar> listOfY, IntVar n) {
    this(listOfX.toArray(new IntVar[0]), listOfY.toArray(new IntVar[0]), n);
  }

  @Override
  public void removeLevel(int level) {
    this.variableQueueY.clear();
  }

  /**
   * Is called when all y are grounded and amongForSet is equivalent to simple version of Among.
   *
   * @param store constraint store in which context that consistency function is being executed.
   */
  public void consistencyForX(Store store) {

    IntDomain lbSdom = (IntDomain) ((MutableDomainValue) lbS.value()).domain;

    int lb0 = lb0Ts.value();
    int ub0 = ub0Ts.value();

    IntVar x;

    boolean inLb;

    for (int i = lb0; i < ub0; i++) {
      x = listOfX[i];
      inLb = false;
      // watch the relation with lbS
      if (lbSdom.getSize() > 0 && lbSdom.contains(x.domain)) {
        swapXtoFront(i, lb0);
        lb0++;
        inLb = true;
        x.removeConstraint(this);
      }

      if (!inLb && !lbSdom.isIntersecting(x.domain)) {
        swapXtoBack(i, ub0 - 1);
        ub0--;
        i--;
        x.removeConstraint(this);
      }
    }

    if (lb0 != lb0Ts.value()) {
      lb0Ts.update(lb0);
    }
    if (ub0 != ub0Ts.value()) {
      ub0Ts.update(ub0);
    }

    if (DEBUG_ALL) {
      log.debug("-------------Consistency FOR X -------------");
      log.debug("--LEVEL : {}", store.level);
      log.debug("{}", this);
      log.debug("--lbS = {}", lb0);
      log.debug("--ubS = {}", ub0);
      log.debug("------------");
    }

    int minN = Math.max(n.min(), lb0);
    int maxN = Math.min(n.max(), ub0);

    if (minN > maxN) {
      throw Store.failException;
    }

    n.domain.in(store.level, n, minN, maxN);

    if (DEBUG_ALL) {
      log.debug("-- K =  {}", lbSdom);
    }

    if (n.domain.singleton()) {

      if (lb0 == n.min() && ub0 == n.min()) {
        removeConstraint();
        return;
      }

      if (lb0 == n.min()) {
        for (int i = lb0; i < ub0; i++) {
          x = listOfX[i];

          x.domain.in(store.level, x, x.domain.subtract(lbSdom));
          if (DEBUG_ALL) {
            log.debug("-- {} in {}", x.id(), x.domain);
          }
        }
      }

      if (ub0 == n.min()) {
        for (int i = lb0; i < ub0; i++) {
          x = listOfX[i];
          x.domain.in(store.level, x, x.domain.intersect(lbSdom));
          if (DEBUG_ALL) {
            log.debug("-- {} in {}", x.id(), x.domain);
          }
        }
      }
    }
  }

  /**
   * The number of x in lbsDom is equal to the number of X intersecting ubSdom.
   *
   * <p>1) If there are not enough of y to cover future domain then fail 2)
   *
   * @param store a constraint store in which context all prunings are executed.
   */
  public void consistencyWhenLb0EqUb0(Store store) {

    IntDomain futureDom = (IntDomain) ((MutableDomainValue) futureLbS.value()).domain;
    IntVar y;
    int i;
    // number of grounded Y
    int yGround = yGrounded.value();
    // number of Y that can potentially cover some X
    int potentialCover = 0;
    for (i = yGround; i < listOfY.length; i++) {
      y = listOfY[i];
      if (y.domain.isIntersecting(futureDom)) {
        potentialCover++;
      }
    }

    if (DEBUG_ALL) {
      log.debug("-------------Consistency when LB0 == UB0 -------------");
      log.debug("--LEVEL : {}", store.level);
      IntDomain lbSdom = (IntDomain) ((MutableDomainValue) lbS.value()).domain;
      log.debug("--lbSdom  = {}", lbSdom);
      log.debug("--futureDom  = {}", futureDom);
      log.debug("covered min {}", yGround);
      log.debug("left y that may play role{}", potentialCover);
      log.debug("------------");
    }

    if (potentialCover < futureDom.getSize()) {
      if (DEBUG_ALL) {
        log.debug("Fail beacuase there are not enough of y to cover x");
      }
      throw Store.failException;
    }

    if (potentialCover == futureDom.getSize()) {
      if (DEBUG_ALL) {
        log.debug("if the number of y is just enough to cover future domain");
        log.debug("than we can decrease their domain to future dom");
        log.debug("and detauch those who are not intersecting the future dom");
      }

      for (i = yGround; i < listOfY.length; i++) {
        y = listOfY[i];
        if (y.domain.isIntersecting(futureDom)) {
          y.domain.in(store.level, y, y.domain.intersect(futureDom));
        } else {
          y.removeConstraint(this);
        }
      }
    }
  }

  /**
   * It is a function which makes Y consistent if all X's are grounded.
   *
   * @param store a constraint store in which context all prunings are executed.
   */
  public void consistencyForY(Store store) {

    IntDomain K = new IntervalDomain();
    for (IntVar x : listOfX) {
      if (x.singleton()) {
        K = K.union(x.min());
      } else {
        assert false : "consistencyForY is called without all X being grounded";
        return;
      }
    }

    IntDomain lbSdom = (IntDomain) ((MutableDomainValue) lbS.value()).domain;
    IntDomain futureDomain = (IntDomain) ((MutableDomainValue) futureLbS.value()).domain;
    IntDomain U;

    if (lbSdom.getSize() > 0) {
      if (futureDomain.getSize() > 0) {
        U = lbSdom.subtract(futureDomain);
      } else {
        U = lbSdom.copy();
      }
    } else {
      U = new IntervalDomain();
    }

    if (DEBUG_ALL) {
      log.debug("-------------Consistency FOR Y -------------");
      log.debug("--LEVEL : {}", store.level);
      log.debug("{}", this);
      log.debug("--x formed K = {}", K);
      log.debug("--y formed U = {}", U);
      log.debug("------------");
    }

    int yGr = this.yGrounded.value();
    int ub0 = this.ub0Ts.value();
    IntVar y;
    IntVar x;

    // number of X that are already covered by some y
    int countCoverMin = 0;
    // Number of Y who are not playing role in covering x
    int noRoleY = 0;

    // Number of Y who already covering some x
    int alreadyCover = 0;

    for (int i = 0; i < ub0; i++) {
      x = this.listOfX[i];
      if (U.contains(x.value())) {
        countCoverMin++;
      }
    }

    for (int i = 0; i < yGr; i++) {
      y = listOfY[i];
      if (K.contains(y.domain)) {
        alreadyCover++;
      } else {
        noRoleY++;
      }
    }

    new IntervalDomain();
    IntDomain intersectK;
    IntDomain disjoint = new IntervalDomain();
    // Number of Y who might cover x that were not yet covered
    int potentialCover = 0;
    // Number of disjoint Y who will cover x that were not yet covered
    int disjointCover = 0;
    for (int i = yGr; i < listOfY.length; i++) {
      y = listOfY[i];
      if (y.singleton()) {
        if (K.contains(y.domain)) {
          alreadyCover++;
        } else {
          noRoleY++;
        }
      } else {

        intersectK = y.domain.intersect(K).subtract(U);

        if (intersectK.getSize() == 0) {
          noRoleY++;
        } else if (intersectK.getSize() == y.domain.getSize()) {
          potentialCover++;
          if (!disjoint.isIntersecting(y.domain)) {
            disjointCover++;
            disjoint = disjoint.union(y.domain);
          }
        } else {
          potentialCover++;
        }
      }
    }

    if (DEBUG_ALL) {
      log.debug("--number of x already covered=       {}", countCoverMin);
      log.debug("--number of y that already cover x = {}", alreadyCover);
      log.debug("--number of no role y=               {}", noRoleY);
      log.debug("--number of potential cover y=       {}", potentialCover);
      log.debug("--min nb of y for disjoint cover=    {}", disjointCover);
      log.debug("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%");
    }

    if (countCoverMin > n.max()) {
      if (DEBUG_ALL) {
        log.debug("........Fail because the number of covered X is bigger than N........");
      }
      throw Store.failException;
    }

    if (noRoleY == (listOfY.length - alreadyCover)) {
      if (DEBUG_ALL) {
        log.debug("........N must be equal to {}", countCoverMin);
      }
      n.domain.inValue(store.level, n, countCoverMin);
    }

    K = K.subtract(U);

    if ((countCoverMin == n.min()) && n.singleton()) {

      if (DEBUG_ALL) {
        log.debug("--K \\ U = {}", K);
      }

      for (int i = yGr; i < listOfY.length; i++) {
        y = listOfY[i];
        if (y.domain.isIntersecting(K)) {
          y.domain.in(store.level, y, y.domain.subtract(K));
        }
      }
      return;
    }

    int mayLeftToCover = listOfX.length - ub0;
    for (int i = 0; i < ub0; i++) {
      x = listOfX[i];
      if (K.contains(x.min())) {
        mayLeftToCover++;
      }
    }

    if (K.getSize() == mayLeftToCover) {
      n.domain.in(store.level, n, countCoverMin + disjointCover, countCoverMin + potentialCover);
    }

    if (n.singleton()) {
      if (potentialCover <= K.getSize()
          && mayLeftToCover == (n.min() - countCoverMin)
          && K.getSize() == mayLeftToCover) {
        for (int i = yGr; i < listOfY.length; i++) {
          y = listOfY[i];
          if (y.domain.isIntersecting(K)) {
            y.domain.in(store.level, y, K);
          }
        }
      }
      if (potentialCover == n.min() - countCoverMin && K.getSize() == mayLeftToCover) {
        for (int i = yGr; i < listOfY.length; i++) {
          y = listOfY[i];
          if (y.domain.isIntersecting(K)) {
            y.domain.in(store.level, y, K);
          }
        }
      }
    }
  }

  @Override
  public void consistency(Store store) {

    // pureUbs ubs usually equals to ubs \ lbs and is used upon calculating
    // the lbV and ubV hashtables
    IntervalDomain pureUbs = new IntervalDomain();
    HashMap<Integer, Integer> lbV = new HashMap<>();
    HashMap<Integer, Integer> ubV = new HashMap<>();

    // Take the lbs domain computed on the previous level
    // it contain the Y values that will be or must be present in S domain
    IntDomain lbSdom = (IntDomain) ((MutableDomainValue) this.lbS.value()).domain;

    // Ubs domain must be recalculated on the each level because the
    // shrinking of the Y domain will cause ubs's decrease
    IntDomain ubSdom;
    if (lbSdom.getSize() > 0) {
      ubSdom = lbSdom.copy();
    } else {
      ubSdom = new IntervalDomain();
    }

    // Future domain contains the Y values that are not must be present in S
    // meaning that one (or more) Y must be grounded to such values
    IntDomain futureDom = (IntDomain) ((MutableDomainValue) this.futureLbS.value()).domain;

    // mustBeCoveredNow consists of the Y values that must be present in lbs
    // but they were pruned out from some Y domain, and thus need a check-up
    IntervalDomain mustBeCoveredNow = new IntervalDomain();

    // we will count the number of new grounded Y in order to move such Y
    // in the beginning of the array and move the pointer. It helps to avoid
    // some recalculations and give potential to fail if the number of ungrounded Y
    // is not enough to cover the future domain
    IntVar y;
    int lastIndex = yGrounded.value();
    IntervalDomain lbVubV = new IntervalDomain();

    boolean skipInitialLb0Ub0Calculation = false;

    boolean firstTimeWhileLoop = true;

    while (!variableQueueY.isEmpty() || firstTimeWhileLoop) {

      // ----------------------------------------------------------
      if (DEBUG_ALL) {
        log.debug("LEVEL : {}", store.level);
        log.debug("{}", this);
      }
      // ----------------------------------------------------------

      pureUbs.clear();
      // Construction of lbSdom
      while (!variableQueueY.isEmpty()) {
        for (Integer yi : this.variableQueueY) {
          y = this.listOfY[yi];
          if (y.singleton()) {
            if (DEBUG_ALL) {
              log.debug("New y {} was grouded to {}", y.id, y.value());
            }
            // Increase the lbSdom with grounded y
            lbSdom = lbSdom.union(y.domain);
            if (futureDom.getSize() > 0) {
              futureDom = futureDom.subtract(y.value(), y.value());
            }
            if (y.domain.getPreviousDomain() != null) {
              mustBeCoveredNow =
                  (IntervalDomain) mustBeCoveredNow.union(y.domain.getPreviousDomain());
              if (!firstTimeWhileLoop) {
                pureUbs = (IntervalDomain) pureUbs.union(y.domain.getPreviousDomain());
              }
            }
            if (yi >= lastIndex) {
              if (yi != lastIndex) {
                int yInt = yi;
                IntVar tmp = listOfY[lastIndex];
                listOfY[lastIndex] = y;
                listOfY[yInt] = tmp;
                yIndex.put(y, lastIndex);
                yIndex.put(tmp, yInt);
              }
              lastIndex++;
            }
          } else {
            if (!firstTimeWhileLoop && y.domain.getPreviousDomain() != null) {
              pureUbs = (IntervalDomain) pureUbs.union(y.domain.getPreviousDomain());
            }
            if (y.domain.getPreviousDomain() != null) {
              mustBeCoveredNow =
                  (IntervalDomain) mustBeCoveredNow.union(y.domain.getPreviousDomain());
            }
          }
        }
        variableQueueY.clear();
        yGrounded.update(lastIndex);

        if (futureDom.getSize() > 0) {
          mustBeCoveredNow = (IntervalDomain) mustBeCoveredNow.intersect(futureDom);
        } else {
          mustBeCoveredNow = (IntervalDomain) futureDom;
        }

        // If there appeared the Y values that have a risk to stay ungrounded
        // we will count their cardinality and FAIL if its 0, ground some Y if it is 1
        if (mustBeCoveredNow.getSize() > 0) {
          if (DEBUG_ALL) {
            log.debug("It appears that we must cover such values : {}", mustBeCoveredNow);
          }
          int cardinalityV;
          int last;
          IntVar y_last;
          // Go though all the intervals of the domain

          Interval inv;
          for (int h = 0; h < mustBeCoveredNow.size; h++) {
            inv = mustBeCoveredNow.intervals[h];
            // go through each value of the interval
            for (int v = inv.min(); v <= inv.max(); v++) {
              cardinalityV = 0;
              last = -1;
              // count the cardinality of v among Y
              for (int i = this.yGrounded.value(); i < this.listOfY.length; i++) {
                y = this.listOfY[i];

                if (y.singleton() && y.min() == v) {
                  mustBeCoveredNow = mustBeCoveredNow.subtract(v, v);
                  cardinalityV = -1;
                  break;
                }
                if (y.domain.contains(v)) {
                  cardinalityV++;
                  last = i;
                }
              }
              if (cardinalityV == 0) {
                if (DEBUG_ALL) {
                  log.debug("Cardinality of {} is 0 => FAIL ", v);
                }
                throw Store.failException;
              } else if (cardinalityV == 1) {
                y_last = this.listOfY[last];
                if (DEBUG_ALL) {
                  log.debug("Cardinality of {} is 1 => Groud {}", v, y_last.id);
                }

                swapYtoFront(last, lastIndex);
                lastIndex++;
                y_last.domain.inValue(store.level, y_last, v);

                mustBeCoveredNow = mustBeCoveredNow.subtract(v, v);
              }
            }
          }
        }
      }
      lbS.update(new MutableDomainValue(lbSdom));
      mustBeCoveredNow = new IntervalDomain();
      futureLbS.update(new MutableDomainValue(futureDom));

      if (DEBUG_ALL) {
        log.debug("Future domain is {}", futureDom);
      }

      if (this.listOfY.length - this.yGrounded.value() < futureDom.getSize()) {
        if (DEBUG_ALL) {
          log.debug(
              "Fail because the number of not grounded y is not enough to cover future lbS domain");
        }
        throw Store.failException;
      }
      if (this.yGrounded.value() == this.listOfY.length) {
        if (DEBUG_ALL) {
          log.debug(
              "All Y were grounded, thus we can pass to simple ve rsion of Among contrians where GAC can be reached");
        }
        consistencyForX(store);
        return;
      }

      for (IntVar v : this.listOfY) {
        ubSdom = ubSdom.union(v.domain);
      }

      // ----------------------------------------------------------
      if (DEBUG_ALL) {
        log.debug("lbS = {}", lbSdom);
        log.debug("ubS = {}", ubSdom);
        log.debug("--------");
      }
      // ----------------------------------------------------------

      // Next part of consistency count occupy the X variables: count the lb0, glb0, ub0, lub0
      int lb0 = lb0Ts.value();
      int ub0 = ub0Ts.value();

      int glb0 = lb0;

      // [x1, x2, x3, ... x_lb0] ..... [ x_ub0 .... x_n]

      // lbSDOm and ubSdom are ready
      IntVar x;
      if (!skipInitialLb0Ub0Calculation) {
        for (int i = lb0; i < ub0; i++) {
          x = listOfX[i];
          // a) count the grounded x

          // b) watch the relation with lbS
          if (lbSdom.getSize() > 0) {
            if (lbSdom.contains(x.domain)) {
              swapXtoFront(i, lb0);
              lb0++;
              glb0++;
              x.removeConstraint(this);
            } else if (lbSdom.isIntersecting(x.domain)) {
              glb0++;
            }
          }

          if (!ubSdom.isIntersecting(x.domain)) {
            swapXtoBack(i, ub0 - 1);
            ub0--;
            i--;
            x.removeConstraint(this);
          }
        }

        if (lb0 != lb0Ts.value()) {
          lb0Ts.update(lb0);
        }
        if (ub0 != ub0Ts.value()) {
          ub0Ts.update(ub0);
        }
      }

      if (this.satisfied()) {
        return;
      }

      if (DEBUG_ALL) {
        log.debug("--------");
        log.debug("- lb0  = {}", lb0);
        log.debug("- glb0 = {}", glb0);
        log.debug("- ub0  = {}", ub0);
        log.debug(
            " domain of N {} is in [ {}, {} ]",
            n.domain,
            Math.max(n.min(), lb0),
            Math.min(n.max(), ub0));
        log.debug("--------");
      }

      int minN = Math.max(n.min(), lb0);
      int maxN = Math.min(n.max(), ub0);

      if (minN > maxN) {
        throw Store.failException;
      }

      n.domain.in(store.level, n, minN, maxN);

      /*----------------------------------------------------------
          Now we will enter the pruning N part
       For each value of UBS we will calculate :
       lbV - lower border on N if v was included into S
       weight - max number of X which can take value from S if v was included into S
       ubV - upper border on N if v as excluded from S
       _____________________________________________________
       lbV - lb0 gives min number of X which can take value from S if v was included into S

       N must be in the Union[ (lbV - lb0 ), weight] and their combinations


      */
      int lbTmp;
      int ubTmp;
      int weight;

      if (firstTimeWhileLoop) {
        lbVubV = new IntervalDomain(lb0, glb0);
        lbVubV = (IntervalDomain) lbVubV.union(ub0);
      }

      int lbMin = Integer.MAX_VALUE;
      int ubMax = Integer.MIN_VALUE;
      if (firstTimeWhileLoop) {
        pureUbs = (IntervalDomain) ubSdom.subtract(lbSdom);
      } else {
        pureUbs = (IntervalDomain) pureUbs.intersect(ubSdom.subtract(lbSdom));
      }

      Interval inv;

      for (int h = 0; h < pureUbs.size; h++) {
        inv = pureUbs.intervals[h];
        // for each interval of UBS
        if (inv != null) {
          // For each value of the interval
          for (int v = inv.min(); v <= inv.max(); v++) {
            lbTmp = lb0;
            weight = 0;
            ubTmp = 0;

            for (int i = 0; i < lb0; i++) {
              x = listOfX[i];
              if (ubSdom.subtract(v, v).isIntersecting(x.domain)) {
                ubTmp++;
              }
            }

            for (int i = lb0; i < ub0; i++) {
              x = listOfX[i];
              // a) count the weight
              if (firstTimeWhileLoop && x.domain.contains(v)) {
                weight++;
              }
              // b)count the relation with lbS
              if (lbSdom.union(v).contains(x.domain)) {
                lbTmp++;
              }
              // c)count the relation with ubs
              if (ubSdom.subtract(v, v).isIntersecting(x.domain)) {
                ubTmp++;
              }
            }
            if (DEBUG_ALL) {
              log.debug("--- lb[{}] = {}", v, lbTmp);
            }
            if (DEBUG_ALL) {
              log.debug("--- ub[{}] = {}", v, ubTmp);
            }
            lbV.put(v, lbTmp);
            ubV.put(v, ubTmp);
            if (ubTmp > ubMax) {
              ubMax = ubTmp;
            }

            if (lbTmp < lbMin) {
              lbMin = lbTmp;
            }

            if (DEBUG_ALL && firstTimeWhileLoop) {
              log.debug("--- weight[{}] = {}", v, weight);
            }

            if (firstTimeWhileLoop && weight != 0 && !lbVubV.contains(n.domain)) {
              int max;
              int min;
              lbTmp = lbTmp - lb0;

              if (lbVubV.getSize() > 0) {
                for (Interval a : lbVubV.intervals) {
                  if (a != null) {
                    max = Math.min(weight + a.max(), ub0);
                    min = Math.max(lbTmp + a.min(), lb0);

                    if (min <= max) {
                      lbVubV = (IntervalDomain) lbVubV.union(min, max);
                      if (DEBUG_ALL && a != null) {
                        log.debug(" >>>> {} + [{}, {}] = [{}, {} ]", a, lbTmp, weight, min, max);
                      }
                    } else if (DEBUG_ALL && a != null) {
                      log.debug(" >>>> {} + [{}, {}] = NOTHING", a, lbTmp, weight);
                    }
                  }
                }
              }
            }
          }
        }
      }

      if (DEBUG_ALL) {
        log.debug(" Made up n domain = {}", lbVubV);
      }

      if (firstTimeWhileLoop) {
        n.domain.in(store.level, n, lbVubV.intersect(n.domain));
      } else {
        n.domain.in(store.level, n, Math.max(lb0, n.min()), Math.min(ub0, n.max()));
      }

      boolean recalculateLb0 = false;
      boolean recalculateUb0 = false;

      pureUbs = (IntervalDomain) ubSdom.subtract(lbSdom);

      for (int h = 0; h < pureUbs.size; h++) {
        inv = pureUbs.intervals[h];
        if (inv != null) {

          for (int v = inv.min(); v <= inv.max(); v++) {
            if (DEBUG_ALL) {
              log.debug(">>>>>>>>>>>>>>>>>>>{}", v);
            }
            if (ubV.get(v) < n.min()) {
              if (DEBUG_ALL) {
                log.debug("{} must be be present in S", v);
              }
              lbSdom = lbSdom.union(v);
              recalculateLb0 = true;

              int cardinalityV = 0;
              int last = -1;
              IntVar y_last;
              for (int i = this.yGrounded.value(); i < this.listOfY.length; i++) {
                y = this.listOfY[i];

                if (y.domain.contains(v)) {
                  cardinalityV++;
                  last = i;
                }
              }

              if (cardinalityV == 1) {
                y_last = this.listOfY[last];
                if (!y_last.singleton()) {
                  y_last = this.listOfY[last];

                  if (DEBUG_ALL) {
                    log.debug("Only {} can cover {} so I ground it", y_last.id, v);
                  }

                  mustBeCoveredNow =
                      (IntervalDomain) mustBeCoveredNow.union(y_last.domain.subtract(v, v));

                  swapYtoFront(last, lastIndex);
                  lastIndex++;

                  y_last.domain.in(store.level, y_last, v, v);
                }
              } else {
                if (cardinalityV == 0) {
                  throw Store.failException;
                }
                futureDom = futureDom.union(v);
              }
            }

            if (lbV.get(v) > n.max()) {
              ubSdom = ubSdom.subtract(v, v);
              recalculateUb0 = true;

              if (DEBUG_ALL) {
                log.debug("{} must be pruned out of all y", v);
              }

              for (int i = yGrounded.value(); i < listOfY.length; i++) {
                y = listOfY[i];

                if (y.singleton()) {
                  if (y.value() == v) {
                    throw Store.failException;
                  }
                } else {
                  y.domain.inComplement(store.level, y, v);
                  if (y.singleton()) {
                    if (futureDom.getSize() > 0) {
                      futureDom = futureDom.subtract(y.value(), y.value());
                    }
                    lbSdom = lbSdom.union(y.value());
                    recalculateLb0 = true;

                    if (i != lastIndex) {
                      variableQueueY.remove(i);
                      IntVar tmp = listOfY[lastIndex];
                      listOfY[lastIndex] = y;
                      listOfY[i] = tmp;
                      yIndex.put(y, lastIndex);
                      variableQueueY.add(lastIndex);
                      yIndex.put(tmp, i);
                    }
                    lastIndex++;
                  }
                }
              }
            }
          }
        }
      }

      if (DEBUG_ALL) {
        log.debug("Future domain is {}", futureDom);
      }
      this.futureLbS.update(new MutableDomainValue(futureDom));

      skipInitialLb0Ub0Calculation = false;
      if (recalculateLb0 || recalculateUb0) {
        skipInitialLb0Ub0Calculation = true;
        boolean inLb;
        for (int i = lb0; i < ub0; i++) {
          x = listOfX[i];
          inLb = false;

          // watch the relation with lbS
          if (lbSdom.getSize() > 0 && lbSdom.contains(x.domain)) {
            swapXtoFront(i, lb0);
            lb0++;
            inLb = true;
            x.removeConstraint(this);
          }

          if (!inLb && recalculateUb0 && !ubSdom.isIntersecting(x.domain)) {
            swapXtoBack(i, ub0 - 1);
            ub0--;
            i--;
            x.removeConstraint(this);
          }
        }

        if (lb0 != lb0Ts.value()) {
          lb0Ts.update(lb0);
        }
        if (ub0 != ub0Ts.value()) {
          ub0Ts.update(ub0);
        }
      }

      lbS.update(new MutableDomainValue(lbSdom));

      if (DEBUG_ALL) {
        log.debug("lb(S) := lb(S) U {{v | ub[v] < min(N) }} = {}", lbSdom);
        log.debug("ub(S) := ub(S) \\ {{v | lb[v] > max(N) }} = {}", ubSdom);
        log.debug("(min(N) = max(N)) = {}", n.singleton());
        log.debug("- lb0  = {}", lb0);
        log.debug("- ub0  = {}", ub0);
        log.debug(
            " domain of N {} is in [ {}, {} ]",
            n.domain,
            Math.max(n.min(), lb0),
            Math.min(n.max(), ub0));
      }

      n.domain.in(store.level, n, Math.max(n.min(), lb0), Math.min(n.max(), ub0));

      if (lbSdom.getSize() > ubSdom.getSize() || lbSdom.getSize() > listOfY.length) {
        if (DEBUG_ALL) {
          log.debug(
              "........Fail because lbSdom.getSize() > ubSdom.getSize()  || lbSdom.getSize() > this.yVarList.length........");
        }
        throw Store.failException;
      }

      if (n.singleton()) {
        if (lbSdom.getSize() > 0 && n.value() == lb0) {
          for (int i = lb0; i < ub0; i++) {
            x = listOfX[i];
            x.domain.in(store.level, x, x.domain.subtract(lbSdom));
          }
        }
        if (n.value() == ub0) {
          for (int i = lb0; i < ub0; i++) {
            x = listOfX[i];
            x.domain.in(store.level, x, x.domain.intersect(ubSdom));
          }
        }
      }

      if (xGrounded.value() == listOfX.length) {
        consistencyForY(store);
      } else if (lb0 == ub0) {
        consistencyWhenLb0EqUb0(store);
      }

      if (satisfied()) {
        removeConstraint();
        return;
      }

      if (DEBUG_ALL) {
        log.debug("{}", this);
      }

      firstTimeWhileLoop = false;
    }
  }

  @Override
  public void impose(Store store) {

    xIndex = Var.positionMapping(listOfX, false, this.getClass());

    yIndex = Var.positionMapping(listOfY, false, this.getClass());

    lbS = new MutableDomain(store);
    futureLbS = new MutableDomain(store);

    lb0Ts = new TimeStamp<>(store, 0);
    ub0Ts = new TimeStamp<>(store, listOfX.length);

    final int gx = (int) Arrays.stream(listOfX).filter(IntVar::singleton).count();
    xGrounded = new TimeStamp<>(store, gx);
    yGrounded = new TimeStamp<>(store, 0);

    store.raiseLevelBeforeConsistency = true;

    super.impose(store);
  }

  @Override
  public void queueVariable(int level, Var variable) {

    if (!(variable instanceof IntVar intVar)) {
      return;
    }

    if (DEBUG_ALL) {
      log.debug(" %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% ");
      log.debug("Var {}{}", intVar, intVar.recentDomainPruning());
    }

    Integer index = yIndex.get(intVar);
    if (index != null) {
      variableQueueY.add(index);
      return;
    }

    if (intVar != this.n && intVar.singleton()) {
      // It can be only X
      xGrounded.update(xGrounded.value() + 1);
    }
  }

  @Override
  public boolean satisfied() {

    if (n.singleton()) {

      int lb0 = lb0Ts.value();
      int ub0 = ub0Ts.value();

      boolean allYsGrounded = yGrounded.value() == listOfY.length;
      boolean allXsGrounded = xGrounded.value() == listOfX.length;

      if (allYsGrounded && n.value() == lb0 && lb0 == ub0) {
        return true;
      }

      assert !allYsGrounded || !allXsGrounded || (n.value() == lb0)
          : " Domain of N or value of timestamp LBoUTS was not maintenated properly";
    }
    return false;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id()).append("\n");

    for (IntVar v : this.listOfX) {
      result.append("X variable ").append(v.id).append(" : ").append(v.domain);
      result.append("       among attached : ");
      result.append(v.domain.constraints().contains(this)).append(" \n");
    }

    for (IntVar v : this.listOfY) {
      result.append("Y variable ").append(v.id).append(" : ").append(v.domain);
      result.append("       among attached : ");
      result.append(v.domain.constraints().contains(this)).append(" \n");
    }

    result.append("variable ").append(n.id).append(" : ").append(n.domain);
    result.append("       among attached : ");
    result.append(n.domain.constraints().contains(this)).append("\n");

    return result.toString();
  }

  private void swapXtoFront(int fromIndex, int targetIndex) {
    if (fromIndex != targetIndex) {
      IntVar x = listOfX[fromIndex];
      IntVar tmp = listOfX[targetIndex];
      listOfX[targetIndex] = x;
      listOfX[fromIndex] = tmp;
      xIndex.put(x, targetIndex);
      xIndex.put(tmp, fromIndex);
    }
  }

  private void swapXtoBack(int fromIndex, int targetIndex) {
    if (fromIndex != targetIndex) {
      IntVar x = listOfX[fromIndex];
      IntVar tmp = listOfX[targetIndex];
      listOfX[targetIndex] = x;
      listOfX[fromIndex] = tmp;
      xIndex.put(x, targetIndex);
      xIndex.put(tmp, fromIndex);
    }
  }

  private void swapYtoFront(int fromIndex, int targetIndex) {
    if (fromIndex != targetIndex) {
      IntVar y = listOfY[fromIndex];
      IntVar tmp = listOfY[targetIndex];
      listOfY[targetIndex] = y;
      listOfY[fromIndex] = tmp;
      yIndex.put(y, targetIndex);
      yIndex.put(tmp, fromIndex);
    }
  }
}
