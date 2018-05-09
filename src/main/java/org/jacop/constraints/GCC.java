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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.*;

/**
 * GCC constraint counts the number of occurences of given
 * values in x variables. The counters are specified by y's.
 * The occurence of all values in the domain of xs is counted.
 *
 * We would like to thank Irit Katriel for making the code of GCC in C she wrote
 * available to us.
 *
 * @author Jocelyne Lotfi and Radoslaw Szymanek.
 *
 * @version 4.5
 */

public class GCC extends Constraint implements UsesQueueVariable, Stateful, SatisfiedPresent {

    /**
     * TODO An improvement to increase the incrementality even further.
     *
     * 1. The first matching uses minimal values. Remember which minimal value has changed which
     * removed from the domain the value which was used in the matching.
     * Reuse from old matching 1 all values smaller than the minimal which has changed.
     *
     * Similar principle applies to matching 2 (skip the positions (variables) until
     * the first index for which m1 did change or for which the m2 value is no longer in the
     * domain.
     *
     *
     * 2. Use IndexDomainView instead of local solution.
     *
     *
     * 3. boolean variable first - is it only once in the consistency function? Then this functionality
     * can be moved out of the while(newPropagation), if it should be executed every time consistency
     * is executed then (it should be setup to true somewhere).
     *
     *
     */

    boolean firstConsistencyCheck = true;

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * The array which stores the first computed matching, which may not take into account
     * the lower bound of count variables.
     */
    private int[] match1;

    /**
     * The array which stores the second computed matching, which may not take into account
     * the upper bound of count variables.
     */
    private int[] match2;

    /**
     * The array which stores the third proper matching, constructed from the first one
     * and second one so both lower and upper bounds are respected.
     */
    private int[] match3;

    private int[] match1XOrder;
    private int[] match2XOrder;
    private int[] nbOfMatchPerY;

    private int[] compOfY;

    private XDomain[] xDomain;
    private BoundDomain[] yDomain;

    private int xSize;
    private int ySize;

    private ArrayDeque<Integer> S1;
    private ArrayDeque<Component> S2;
    private PriorityQueue<XDomain> pFirst, pSecond;
    private PriorityQueue<Integer> pCount;

    private final static boolean debug = false;

    private int[] domainHash;

    private Map<IntVar, Integer> xNodesHash;
    private Set<IntVar> xVariableToChange;

    TimeStamp<Integer> stamp;

    private int stampValue;
    int firstConsistencyLevel;

    /**
     * It specifies variables x whose values are counted.
     */
    public IntVar[] x;

    /**
     * It species variables counters for counting occurences of each possible value from the
     * intial domain of x variables.
     */
    private IntVar[] counters;

    private Comparator<XDomain> compareLowerBound = (o1, o2) -> {
        if (o1.min < o2.min)
            return -1;
        else if (o1.min > o2.min)
            return 1;
        return 0;
    };

    private Comparator<XDomain> sortPriorityMinOrder = (o1, o2) -> {
        if (o1.max < o2.max)
            return -1;
        else if (o1.max > o2.max)
            return 1;

        return 0;
    };

    private Comparator<Integer> sortPriorityMaxOrder = (e1, e2) -> -e1.compareTo(e2);

    /**It constructs global cardinality constraint.
     * @param x variables which values are counted.
     * @param counters variables which count the values.
     */
    public GCC(IntVar[] x, IntVar[] counters) {

        checkInputForNullness(new String[]{"x", "counters"}, x, counters);
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

        this.xDomain = new XDomain[xSize];
        this.yDomain = new BoundDomain[ySize];

        // rest of the init
        match1 = new int[xSize];
        match2 = new int[xSize];
        match3 = new int[xSize];
        match1XOrder = new int[xSize];
        match2XOrder = new int[xSize];

        nbOfMatchPerY = new int[ySize];
        compOfY = new int[ySize];

        S1 = new ArrayDeque<>();
        S2 = new ArrayDeque<>();
        pFirst = new PriorityQueue<>(10, sortPriorityMinOrder);
        pSecond = new PriorityQueue<>(10, sortPriorityMinOrder);
        pCount = new PriorityQueue<>(10, sortPriorityMaxOrder);

        xNodesHash = Var.createEmptyPositioning();
        xVariableToChange = new HashSet<>();

        setScope(Stream.concat(Arrays.stream(x), Arrays.stream(counters)));

    }

    private Set<IntVar> zeroCounters;

    /** Fix suggested by Radek: a set that keeps track of the variables that have changed and need to be revisited in the consistency method */
    private Set<Var> changedVariables = new HashSet<>();

    private IntVar[] removeZeroCounters(IntVar[] x, IntVar[] counters) {

        IntVar[] result;

        // here I will put normalization
        IntervalDomain d = new IntervalDomain();

        for (IntVar aX : x)
            d = (IntervalDomain) d.union(aX.domain);

        // I check the consistency of the x and y variable
        if (d.getSize() != counters.length && (d.max() - d.min() + 1) != counters.length)
            // if there are more y variable than x variable there is a mistake of conseption
            // as the rest of y variables are 0 in any case. The problem is to know which y variable
            // should not be here. With normalization we assume that it is the last ones in the
            // list but it is an assumption, it's better to throw an exception there and let the
            // user determine what is correct.
            throw new IllegalArgumentException("GCC failure : join domain of x variables doesn't cover all count variables");

        // no changes required
        if (d.getSize() == counters.length)
            return counters;

        // zero counters encountered.
        result = new IntVar[d.getSize()];
        zeroCounters = new HashSet<>();

        int i = 0;
        for (int k = d.min(); k <= d.max(); k++)
            if (d.contains(k))
                result[i++] = counters[k - d.min()];
            else
                zeroCounters.add(counters[k - d.min()]);

        return result;
    }

    /**It constructs global cardinality constraint.
     * @param x variables which values are counted.
     * @param counters variables which count the values.
     */
    public GCC(List<? extends IntVar> x, List<? extends IntVar> counters) {

        this(x.toArray(new IntVar[x.size()]), counters.toArray(new IntVar[counters.size()]));

    }

    @Override public void removeLevel(int level) {
        if (level == firstConsistencyLevel)
            firstConsistencyCheck = true;
    }

    @Override public void consistency(Store store) {

        // the stamp is here to represent the number of x variable still
        // not singleton and that need to be pruned (the rest is set and
        // doesn't need to be pass though the whole calculation of matching
        // and SCC's). The same trick can not be apply to the y as the order
        // matter a lot.

        // I take out all the xNodes that are singleton and I put them
        // after the stamp value
        if (firstConsistencyCheck) {

            if (zeroCounters != null)
                for (IntVar zeroCounter : zeroCounters)
                    zeroCounter.domain.in(store.level, zeroCounter, 0, 0);

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

        // no need to rerun the consistancy function as the reduction on x domains doesn't affect
        // the matching and the y count is base on the matching and doesn't affect it. So
        // rerunning the constraint doesn't bring anything new. We can suppose that y counting
        // achieve bound consistancy.


        do {

            store.propagationHasOccurred = false;

            // Fix suggested by Radek (moved from queueVariable)
            Set<Var> changedVariablesCopy = this.changedVariables;
            this.changedVariables = new HashSet<Var>();
            for (Var var : changedVariablesCopy) {
                // if v is singleton and is an X variable
                if (var.singleton() && xNodesHash.containsKey(var)) {
                    // if
                    if (xNodesHash.get(var) < stamp.value()) { // changing '<=' to '<' (KK)
                        if (debug)
                            System.out.println(" in xVariableToChange: " + var);
                        if (stamp.value() > 0) {
                            stamp.update(stamp.value() - 1);
                            putToTheEnd(x, xNodesHash.get(var));
                        }
                    }
                }
            }

            assert checkXorder() : "Inconsistent X variable order: " + Arrays.toString(this.x);

            if (debug) {
                System.out.println("XNodes");
                for (int i = 0; i < xSize; i++)
                    System.out.println(x[i]);
                System.out.println("stamp before " + stamp.value());
            }

            stampValue = stamp.value();

            if (debug) {
                System.out.println("stamp after " + stampValue);
                System.out.println("XDomain");
            }
            // put in the xDomain all xNodes that are not singleton

            for (int i = 0; i < stampValue; i++) {
                xDomain[i].setDomain(findPosition(x[i].min(), domainHash), findPosition(x[i].max(), domainHash));

                xDomain[i].twin = x[i];
                if (debug)
                    System.out.println(xDomain[i]);
            }
            if (debug)
                System.out.println("YDomain");

            // put all yNodes in yDomain
            for (int i = 0; i < ySize; i++) {
                yDomain[i].setDomain(counters[i].min(), counters[i].max());

                if (debug)
                    System.out.println(yDomain[i]);
            }

            if (debug)
                System.out.println("take out singleton xNodes");

            // check all xNodes and if singleton change the yDomain value
            // to count down the xNode already link to this yNode
            for (int i = 0; i < xSize; i++) {
                if (x[i].singleton()) {
                    //Change, check.
                    int value = findPosition(x[i].value(), domainHash);
                    if (yDomain[value].min > 0) {
                        yDomain[value].min--;
                    }
                    yDomain[value].max--;
                    if (yDomain[value].max < 0)
                        throw Store.failException;
                }
            }

            if (debug) {
                System.out.println("pass in consistency");
                System.out.println("YDomain");
                for (int i = 0; i < ySize; i++)
                    System.out.println(yDomain[i]);
            }

            sortXByDomainMin();

            FindGeneralizedMatching();
            SCCs();
            // I do the countConcistancy before the x pruning so the
            // change in x variable doesn't affect the pruning of y variable
            countBoundConsistency(store);

            // do the pruning
            for (int j = 0; j < stampValue; j++) {

                assert ((match3[j] >= 0) && (match3[j] < ySize));
                assert ((compOfY[match3[j]] >= 0) && (compOfY[match3[j]] <= ySize));

                int cutMin = xDomain[j].min;
                int cutMax = xDomain[j].max;

                if (debug)
                    System.out.println("cutmax " + cutMax);

                while (compOfY[match3[j]] != compOfY[cutMin])
                    cutMin++;

                while (compOfY[match3[j]] != compOfY[cutMax]) {
                    cutMax--;
                }

                int id = xNodesHash.get(xDomain[j].twin);

                if (debug)
                    System.out.println("do pruning [" + x[id].min() + "," + x[id].max() + "] => [" + cutMin + "," + cutMax + "]");

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
                    yDomain[value].max--;
                    if (yDomain[value].max < 0) {
                        if (debug)
                            System.out.println("failure in putting back yNodes domain");
                        throw Store.failException;
                    }
                }
            }


        } while (store.propagationHasOccurred);

    }

    /** A method to be called in asserts that checks whether all grounded X variables are correctly put at the end of the list
     * @return false if the X variable order is inconsistent
     */
    private boolean checkXorder() {

        for (int i = this.stamp.value() - 1; i >= 0; i--)
            if (this.x[i].singleton())
                return false;

        for (int i = this.stamp.value(); i < this.x.length; i++)
            if (!this.x[i].singleton())
                return false;

        return true;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public void impose(Store store) {

        stamp = new TimeStamp<>(store, xSize);

        // first I will put all the xNodes in a hashTable to be able to use
        // it with the queueVariable function
        // KK, 2015-10-18
        // only non ground variables need to be added
        // no duplicates allowed
        Var.addPositionMapping(xNodesHash, x, true, this.getClass());

        // here I will put normalization
        IntervalDomain d = new IntervalDomain();

        for (int i = 0; i < xSize; i++)
            d = (IntervalDomain) d.union(x[i].domain);

        // I check the consistency of the x and y variable
        if (d.getSize() != ySize)
            // if there are more y variable than x variable there is a mistake of conseption
            // as the rest of y variables are 0 in any case. The problem is to know which y variable
            // should not be here. With normalization we assume that it is the last ones in the
            // list but it is an assumption, it's better to throw an exception there and let the
            // user determine what is correct.
            throw new IllegalArgumentException("GCC failure : join domain of x variables doesn't cover all count variables");

        domainHash = new int[d.getSize()];
        IntervalDomainValueEnumeration venum = new IntervalDomainValueEnumeration(d);
        int i = 0;
        do {

            Integer j = venum.nextElement();
            domainHash[i++] = j;

        } while (venum.hasMoreElements());

        for (i = 0; i < xSize; i++)
            this.xDomain[i] = new XDomain(x[i], findPosition(x[i].min(), domainHash), findPosition(x[i].max(), domainHash));

        for (i = 0; i < ySize; i++)
            this.yDomain[i] = new BoundDomain(counters[i].min(), counters[i].max());

        super.impose(store);

    }

    @Override public void queueVariable(int level, Var var) {
        if (debug)
            System.out.println("in queue variable " + var + " level " + level);

        // Fix suggested by Radek: the queueVariable function should store the variables that are changing in a HashSet
        this.changedVariables.add(var);
    }

    @Override public boolean satisfied() {

        if (!grounded())
            return false;

        int count[] = new int[domainHash.length];

        for (IntVar xVar : x) {
            int xValue = xVar.value();
            int position = 0;
            for (; position < count.length && domainHash[position] != xValue; position++)
                ;
            assert (position < count.length);
            count[position]++;
        }

        for (int i = 0; i < counters.length; i++)
            if (counters[i].value() != count[i])
                return false;

        return true;
    }

    @Override public String toString() {

        StringBuilder toString = new StringBuilder(id());

        toString.append(" : GCC ([");
        for (int i = 0; i < xSize - 1; i++)
            toString.append(x[i].toString()).append(", ");
        toString.append(x[xSize - 1].toString());
	toString.append("], [");
        for (int j = 0; j < ySize - 1; j++)
            toString.append(counters[j].toString()).append(", ");
        toString.append(counters[ySize - 1].toString()).append("])");

        return toString.toString();

    }


    // private methods

    //-----------------------FIND_GENERALIZED_MATCHING--------------------------------//

    private void FindGeneralizedMatching() {

        Arrays.fill(nbOfMatchPerY, 0);

        if (debug) {
            System.out.println("XDomain");
            for (int i = 0; i < stampValue; i++)
                System.out.println(i + " [" + xDomain[i].min + "-" + xDomain[i].max + "]");
        }
        // first pass
        firstPass();

        // check we are in the good ranges for match1 and match1XOrder
        assert (checkFirstPass());

        secondPass();

        assert (checkSecondPass());

        thirdPass();

        assert (checkThirdPass());

    }

    private boolean checkFirstPass() {

        for (int j = 0; j < stampValue; j++) {
            assert (match1[j] >= 0);
            assert (match1[j] < ySize);
            assert (match1XOrder[j] >= 0);
            assert (match1XOrder[j] < stampValue);
        }

        return true;
    }

    private boolean checkSecondPass() {

        for (int j = 1; j < stampValue; j++)
            assert (match2[match2XOrder[j]] >= match2[match2XOrder[j - 1]]);

        return true;
    }

    private boolean checkThirdPass() {

        for (int j = 0; j < stampValue; j++) {
            assert (xDomain[j].min <= match3[j]);
            assert (xDomain[j].max >= match3[j]);
        }

        return true;
    }

    private void firstPass() {

        pFirst.clear();
        //		int j = 0;
        int xIndex = 0;
        int maxY;
        int match1XOrderIndex = 0;
        int top;

        for (int i = 0; i < ySize; i++) {
            // first we add all the x which min domain is y
            while ((xIndex < stampValue) && xDomain[xIndex].min == i) {
                // add a new element with index to get it back after the good element
                // and the max of the domain of xNode to sort them.
                xDomain[xIndex].index = xIndex;
                pFirst.add(xDomain[xIndex]);
                xIndex++;
            }
            int u = 0;
            // second we add the maximum of these xs possible to the current y
            maxY = yDomain[i].max;
            while (!pFirst.isEmpty() && u < maxY) {
                top = (pFirst.remove()).index; // index of the first element of pFirst
                match1[top] = i;
                u++;
                // match1XOrder gives the order in which xs where in the priority queue
                // that sorted them by domain max by group of domain min.
                // That is there are first sorted by domain min and after by domain max.
                match1XOrder[match1XOrderIndex] = top;
                match1XOrderIndex++;

                if (xDomain[top].max < i) {
                    if (debug)
                        System.out.println("failure first pass");

                    throw Store.failException;
                    // it was checked that the min == i so max cannot be under min. Well, yes there are cases
                    // where it's useful.
                }
                //				j++;
            }
        }

        // do we have to check that the queue is empty ? If not it means that an x was not paired.
        // I add the test on the queue. It is possible if the maxY = 0 and is the last one visited
        // otherwise the element in the queue can be used by the next yNode.
        if (!pFirst.isEmpty()) {

            if (debug)
                System.out.println("failure the queue is not empty");

            throw Store.failException;

        }

        if (debug) {

            System.out.print("match1Xorder : ");
            for (int aMatch1XOrder : match1XOrder)
                System.out.print(aMatch1XOrder + " ");

            System.out.println("");
            System.out.print("match1 : ");

            for (int aMatch1 : match1)
                System.out.print(aMatch1 + " ");

            System.out.println("");
        }

    }

    private void secondPass() {

        pSecond.clear();
        //		int j = 0;
        int top;
        int xIndex = 0;
        int minY;
        int match2XOrderIndex = 0;
        int order;

        for (int i = 0; i < ySize; i++) {
            // I should iterate on the match1XOrder instead of the normal order
            // we take all the xs that where matched with yi in the first pass.
            while ((xIndex < stampValue) && (match1[match1XOrder[xIndex]] == i)) {
                order = match1XOrder[xIndex];
                xDomain[order].index = order;
                pSecond.add(xDomain[order]);
                xIndex++;
            }
            minY = yDomain[i].min;
            for (int l = 0; l < minY; l++) {
                if (pSecond.isEmpty()) {
                    // failure need to be expressed
                    if (debug)
                        System.out.println("failure second pass");

                    throw Store.failException;
                }
                top = pSecond.remove().index;
                //change, check.
                match2[top] = i;

                match2XOrder[match2XOrderIndex] = top;
                match2XOrderIndex++;
                nbOfMatchPerY[i]++;
                //				j++;
            }
            while (!pSecond.isEmpty() && ((pSecond.element().max) < i + 1)) {
                top = pSecond.remove().index;
                // change, check.
                match2[top] = i;
                match2XOrder[match2XOrderIndex] = top;
                match2XOrderIndex++;
                nbOfMatchPerY[i]++;
                //				j++;
            }
        }


        if (debug) {

            System.out.print("match2Xorder : ");

            for (int aMatch2XOrder : match2XOrder)
                System.out.print(aMatch2XOrder + " ");

            System.out.println("");

            System.out.print("match2 : ");
            for (int aMatch2 : match2)
                System.out.print(aMatch2 + " ");

            System.out.println("");
        }

    }

    private void thirdPass() {

        int xIndex = stampValue - 1;
        int e;
        int x = 0;

        System.arraycopy(match2, 0, match3, 0, stampValue);

        for (int i = ySize - 1; i >= 0; i--) {
            while ((xIndex >= 0) && (match2[match2XOrder[xIndex]] > i))
                xIndex--;

            e = nbOfMatchPerY[i] - yDomain[i].max; // excess of y mates
            while (e > 0) {

                assert (match2[match2XOrder[xIndex]] == i);

                while (xIndex >= 0) {
                    x = match2XOrder[xIndex];
                    if (match1[x] == i)
                        xIndex--;
                    else
                        break;
                }

                assert (match1[x] < i);
                assert (match2[x] == i);

                match3[x] = match1[x];
                nbOfMatchPerY[i]--;
                nbOfMatchPerY[match1[x]]++;
                xIndex--;
                e--;
            }
        }
        if (debug) {
            System.out.print("match3 : ");
            for (int aMatch3 : match3)
                System.out.print(aMatch3 + " ");
            System.out.println("");
        }
    }

    //--------------------------------SCCs-------------------------------------//

    private void SCCs() {

        int sccNb, C;
        int maxYReachedFromS, maxYReachesS;
        int minYReachedFromS, minYReachesS;
        int[] compReachesLeft = new int[ySize];
        int[] compReachesRight = new int[ySize];
        int[] yReachesLeft = new int[ySize];
        int[] yReachesRight = new int[ySize];

        for (int i = 0; i < ySize; i++)
            compOfY[i] = i;

        sccNb = SCCsWithoutS(compReachesLeft, compReachesRight, yReachesLeft, yReachesRight);
        // now compReaches(Left, Right) and compOfY contain the left and right most y per comp and to which comp a y belong
        if (debug) {
            System.out.println("sccNb : " + sccNb);
            System.out.println("compReachesLeft ");
            for (int aCompReachesLeft : compReachesLeft)
                System.out.print(aCompReachesLeft + " ");

            System.out.println("");
            System.out.println("compReachesRight ");
            for (int aCompReachesRight : compReachesRight)
                System.out.print(aCompReachesRight + " ");

            System.out.println("");
            System.out.println("compOfY ");
            for (int aCompOfY : compOfY)
                System.out.print(aCompOfY + " ");

            System.out.println("");
        }
        boolean[] reachedFromS = new boolean[sccNb];
        boolean[] reachesS = new boolean[sccNb];

        // reachedFromS and reachesS need to contain only value false.
        // by default satisfied by Java, therefore the two lines below are not needed.
        // Arrays.fill(reachedFromS, false);
        // Arrays.fill(reachesS, false);

        // init reachedFromS and reachesS
        int comp;
        for (int i = 0; i < ySize; i++) {
            comp = compOfY[i];
            assert (comp >= 0);
            assert (comp <= sccNb);

            // if there are stictly more match to y than the minimum required
            // an edge exist from s to y
            if (yDomain[i].min < nbOfMatchPerY[i])
                reachedFromS[comp] = true;

            // if there are strictly less match to y than the maximum possible
            // an edge exist from y to s
            if (yDomain[i].max > nbOfMatchPerY[i])
                reachesS[comp] = true;
        }

        maxYReachedFromS = -1;
        maxYReachesS = -1;

        for (int i = 0; i < ySize; i++) {
            C = compOfY[i];

            assert (C >= 0);
            assert (C <= sccNb);

            // if the max y that can be reached is greater than the current y,
            // that the comp it belongs to can be reached from s.
            if (maxYReachedFromS >= i)
                reachedFromS[C] = true;

            // if it's reached we can extand the max y reached to the compReachesRight of the component
            if (reachedFromS[C])
                maxYReachedFromS = Math.max(maxYReachedFromS, compReachesRight[C]);

            // same in the other way : if the ReachesLeft of the comp is under the max y that
            // reaches S this comp reaches S
            if (compReachesLeft[C] <= maxYReachesS)
                reachesS[C] = true;

            // if it's reachesS we can extand the max Y that reaches it to the current y.
            if (reachesS[C])
                maxYReachesS = Math.max(maxYReachesS, i);

        }

        // same as before but for minimum

        minYReachedFromS = ySize;
        minYReachesS = ySize;

        for (int i = ySize - 1; i >= 0; i--) {
            C = compOfY[i];
            assert (C >= 0);
            assert (C <= sccNb);
            if (minYReachedFromS <= i)
                reachedFromS[C] = true;

            if (reachedFromS[C])
                minYReachedFromS = Math.min(minYReachedFromS, compReachesLeft[C]);

            if (compReachesRight[C] >= minYReachesS)
                reachesS[C] = true;

            if (reachesS[C])
                minYReachesS = Math.min(minYReachesS, i);

        }

        // merge all comp that are strongly connected through s and
        // give this new comp a new number

        for (int i = 0; i < ySize; i++)

            if (reachesS[compOfY[i]] && reachedFromS[compOfY[i]])
                compOfY[i] = sccNb;

        if (debug) {
            System.out.println("compOfY after S ");
            for (int aCompOfY : compOfY)
                System.out.print(aCompOfY + " ");

            System.out.println("");
        }
    }

    private int SCCsWithoutS(int[] compReachesLeft, int[] compReachesRight, int[] yReachesLeft, int[] yReachesRight) {

        Component C, C1;
        int sccNb = 0;
        S1.clear();
        S2.clear();

        ReachedFromY(yReachesLeft, yReachesRight);

        // init all componant as containing only one y and set these component
        // reachesLeft and reachesRight to y reachesLeft and Right
        for (int y = 0; y < ySize; y++) {
            compReachesLeft[y] = yReachesLeft[y];
            compReachesRight[y] = yReachesRight[y];
        }

        for (int y = 0; y < ySize; y++) {
            // set comp to (root, rightmostY, maxX)
            C = new Component(y, y, yReachesRight[y]);

            if (S2.isEmpty()) {
                S1.push(y);
                S2.push(C);
                continue;
            }

            // once S2 not empty
            // this first part treat the case we have a new component.
            // (c1.max < C.root)

            while ((!S2.isEmpty()) && ((S2.peek().maxX < C.root))) {
                compReachesLeft[sccNb] = ySize;
                compReachesRight[sccNb] = -1;

                assert (!S1.isEmpty());

                C1 = S2.pop();
                while (!S1.isEmpty() && S1.peek() >= C1.root && S1.peek() <= C1.rightmostY) {
                    int popY;
                    assert (!S1.isEmpty());
                    popY = S1.pop();
                    compOfY[popY] = sccNb;
                    compReachesLeft[sccNb] = Math.min(compReachesLeft[sccNb], yReachesLeft[popY]);
                    compReachesRight[sccNb] = Math.max(compReachesRight[sccNb], yReachesRight[popY]);
                }
                sccNb++;
            }

            assert (S2.isEmpty() || S2.peek().maxX >= C.root);

            // this second part treat the case the new c1 is in fact attainable by the current component

            while (!S2.isEmpty() && yReachesLeft[y] <= S2.peek().rightmostY) {
                assert (!S2.isEmpty());
                C1 = S2.pop();
                C.maxX = Math.max(C.maxX, C1.maxX);
                C.root = C1.root; // as they are taken in order from left to right c1.root is always < C.root
                C.rightmostY = y; // same remark
            }

            assert (S2.isEmpty() || ((yReachesLeft[y] > S2.peek().rightmostY) && (S2.peek().maxX >= C.root)));

            S1.push(y);
            S2.push(C);
        } // end for


        // for every component still on the pile update compOfY, compReachesLeft and Right, and sccNb
        while (!S2.isEmpty()) {
            assert (!S1.isEmpty());
            C = S2.pop();
            compReachesLeft[sccNb] = ySize;
            compReachesRight[sccNb] = -1;

            while (!S1.isEmpty() && S1.peek() >= C.root && S1.peek() <= C.rightmostY) {
                int y;
                assert (!S1.isEmpty());
                y = S1.pop();
                compOfY[y] = sccNb;
                compReachesLeft[sccNb] = Math.min(compReachesLeft[sccNb], yReachesLeft[y]);
                compReachesRight[sccNb] = Math.max(compReachesRight[sccNb], yReachesRight[y]);
            }
            sccNb++;
        }

        assert (S1.isEmpty() && S2.isEmpty());
        return sccNb;
    }

    private void ReachedFromY(int[] yReachesLeft, int[] yReachesRight) {


        for (int i = 0; i < ySize; i++) {
            yReachesLeft[i] = i;
            yReachesRight[i] = i;
        }

        int i;
        // we check what is the minimum ymin and the maximum ymax reachable by y.
        // For that we check every x linked to y to keep the minimal and maximal domain
        // bondaries of these xs.
        for (int j = 0; j < stampValue; j++) {
            i = match3[j];
            assert (i >= 0);
            assert (i < ySize);
            yReachesLeft[i] = Math.min(yReachesLeft[i], xDomain[j].min);
            yReachesRight[i] = Math.max(yReachesRight[i], xDomain[j].max);
        }
        if (debug) {
            System.out.println("yReachesLeft ");
            for (i = 0; i < yReachesLeft.length; i++)
                System.out.print(yReachesLeft[i] + " ");

            System.out.println("");
            System.out.println("yReachesRight ");
            for (i = 0; i < yReachesRight.length; i++)
                System.out.print(yReachesRight[i] + " ");

            System.out.println("");
        }
    }

    //------------------------USED_FOR_REDUCING_DOMAIN--------------------------//


    private void putToTheEnd(IntVar[] list, int element) {
        // I swap the element with the last one before the stamp
        // which have nothing to do in the no-more-seen variables
        IntVar v1 = list[element];
        int stampValue = stamp.value();
        list[element] = list[stampValue];
        // update the index of the moved element which was behind the stamp value
        xNodesHash.put(list[stampValue], element);
        // and update the one put to the end
        xNodesHash.put(v1, stampValue);
        list[stampValue] = v1;
    }

    //---------------------------COUNT_BOUND_CONCISTENCY-----------------------//

    private void countBoundConsistency(Store store) {
        int[] max_u = new int[ySize];
        Arrays.fill(max_u, ySize - 1);

        int[] min_l = new int[ySize];
        Arrays.fill(min_l, 0);

        upperCount(max_u);
        lowerCount(min_l);

        if (debug) {
            System.out.println("max_u ");
            for (int aMax_u : max_u)
                System.out.print(aMax_u + " ");

            System.out.println("");
            System.out.println("min_l ");
            for (int aMin_l : min_l)
                System.out.print(aMin_l + " ");

            System.out.println("");
        }
        // do the pruning of the domain
        for (int i = 0; i < ySize; i++) {
            if (debug)
                System.out
                    .println("do pruning [" + counters[i].min() + "," + counters[i].max() + "] => [" + min_l[i] + "," + max_u[i] + "]");

            if (yDomain[i].max != max_u[i] || yDomain[i].min != min_l[i])
                yDomain[i].setDomain(min_l[i], max_u[i]);
        }
        // add the rest of nodes not treated in this pass that was already singleton
        if (debug)
            System.out.println("increase yDomain with xNodes singleton");

        for (int i = 0; i < xSize; i++) {
            if (x[i].singleton()) {
                //Change, check.
                int value = findPosition(x[i].value(), domainHash);
                yDomain[value].max++;
                yDomain[value].min++;
            }
        }

        if (debug)
            System.out.println("set yNodes");

        for (int i = 0; i < ySize; i++)
            counters[i].domain.in(store.level, counters[i], yDomain[i].min, yDomain[i].max);

    }

    private void upperCount(int[] max_u) {

        int xIndex, x;
        pCount.clear();
        xIndex = stampValue - 1;
        for (int i = ySize - 1; i >= 0; i--) {
            while (xIndex >= 0) {
                x = match2XOrder[xIndex];
                if (match2[x] == i) {
                    pCount.add(match1[x]);
                    xIndex--;
                } else
                    break;
            }
            max_u[i] = Math.min(yDomain[i].max, pCount.size());
            for (int l = 0; l < yDomain[i].min; l++) {
                assert (!pCount.isEmpty());
                pCount.remove();
            }

            // well see how it works for the second part of the condition
            while (!pCount.isEmpty() && (pCount.peek() == i)) {
                pCount.remove();
            }
        }
    }

    private void lowerCount(int[] min_l) {
        int xIndex, count, x;
        pCount.clear();
        xIndex = stampValue - 1;
        for (int i = ySize - 1; i >= 0; i--) {
            count = 0;
            while (xIndex >= 0) {
                x = match2XOrder[xIndex];
                if (match2[x] == i) {
                    pCount.add(match1[x]);
                    xIndex--;
                } else
                    break;

            }

            for (int l = 0; l < yDomain[i].min; l++) {
                assert (!pCount.isEmpty());
                pCount.remove();
                count++;
            }

            while ((!pCount.isEmpty()) && (pCount.peek() == i)) {
                pCount.remove();
                count++;
            }

            min_l[i] = count;
            while ((!pCount.isEmpty()) && (count < yDomain[i].max)) {
                pCount.remove();
                count++;
            }
        }
    }

    //	----------------------------SORT_AND_COMPARATOR--------------------------//

    private void sortXByDomainMin() {
        // I need to sort only the part concern, otherwise old values still after
        // the stamp value will interfer with the sorting
        Arrays.sort(xDomain, 0, stampValue, compareLowerBound);

    }

    //-----------------------INNER CLASSES-----------------------------------//
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


    private static class XDomain extends BoundDomain {
        Var twin;
        int index;

        XDomain(Var twin, int min, int max) {
            super(min, max);
            this.twin = twin;
        }
    }

    private int findPosition(int value, int[] values) {

        int left = 0;
        int right = values.length - 1;

        int position = (left + right) >> 1;

        if (debug) {
            System.out.println("Looking for " + value);
            for (int v : values)
                System.out.print("val " + v);
            System.out.println("");
        }

        while (!(left + 1 >= right)) {

            if (debug)
                System.out.println("left " + left + " right " + right + " position " + position);

            if (values[position] > value) {
                right = position;
            } else {
                left = position;
            }

            position = (left + right) >> 1;

        }

        if (values[left] == value)
            return left;

        if (values[right] == value)
            return right;

        return -1;

    }
}
