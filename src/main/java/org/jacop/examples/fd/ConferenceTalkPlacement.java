/*
 * ConferenceTalkPlacement.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.examples.fd;

import org.jacop.constraints.*;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.*;

import java.util.*;

/**
 *
 * It solves a simple conference talk placement problem.
 *
 * @author Radoslaw Szymanek
 * @version 4.5
 *
 * It solves a simple conference example problem, where different sessions
 * must be scheduled according to the specified constraints.
 *
 */
public class ConferenceTalkPlacement {

    Store store;
    IntVar cost;
    List<IntVar> vars;
    IntVar[][] varsMatrix;
    DepthFirstSearch<IntVar> search;

    private Map<Integer, Map<Integer, Integer>> transformCosts(int[][] costs, int noOfTalks) {

        Map<Integer, Map<Integer, Integer>> result = new HashMap<Integer, Map<Integer, Integer>>();

        for (int i = 0; i < noOfTalks; i++)
            result.put(i, new HashMap<Integer, Integer>());

        for (int i = 0; i < costs.length; i++)
            result.get(costs[i][0]).put(costs[i][1], costs[i][2]);

        System.out.println(result);

        return result;
    }

    private Map<Integer, Map<Integer, Integer>> randomCosts(int noOfTalks, int randomSeed, int maxSingleCost) {

        Random seed = new Random(randomSeed);

        Map<Integer, Map<Integer, Integer>> result = new HashMap<Integer, Map<Integer, Integer>>();

        for (int i = 0; i < noOfTalks; i++)
            result.put(i, new HashMap<Integer, Integer>());

        for (int i = 0; i < noOfTalks; i++)
            for (int j = i + 1; j < noOfTalks; j++)
                result.get(i).put(j, seed.nextInt(maxSingleCost));

        return result;
    }

    // assumes noTalks = noOfParallelTracks * noOfTimeSlots
    private int computeLowerBound(int noOfParallelTracks, int noOfTimeSlots, Map<Integer, Map<Integer, Integer>> costs) {

        List<Integer> costsList = new ArrayList<>();
        for (Map<Integer, Integer> elH : costs.values())
            costsList.addAll(elH.values());

        Integer[] sortedArray = costsList.toArray(new Integer[costsList.size()]);
        Arrays.sort(sortedArray);

        int noOfTalksInOneTimeSlot = noOfParallelTracks;
        int lowerBound = 0;
        for (int i = 0; i < noOfTimeSlots * (noOfTalksInOneTimeSlot * (noOfTalksInOneTimeSlot - 1) / 2); i++)
            lowerBound += sortedArray[i];

        System.out.println(lowerBound);
        return lowerBound;
    }

    public void model(int noOfParallelTracks, int noOfTalks, int noOfTimeSlots, int maxSingleCost,
        Map<Integer, Map<Integer, Integer>> costMap) {

        store = new Store();

        varsMatrix = new IntVar[noOfTalks * (noOfTalks - 1) / 2][3];

        IntVar[] talkPlacement = new IntVar[noOfTalks];

        for (int i = 0; i < noOfTalks; i++)
            talkPlacement[i] = new IntVar(store, "talk[" + i + "]-track", 0, noOfParallelTracks - 1);

        IntVar[] talkCounterInTrack = new IntVar[noOfParallelTracks];
        for (int i = 0; i < noOfParallelTracks; i++)
            talkCounterInTrack[i] = new IntVar(store, "noOfTalksIn-" + i + "-th-Track", noOfTalks / noOfParallelTracks - 1, noOfTimeSlots);

        for (int i = 0; i < noOfParallelTracks; i++)
            store.impose(new Count(talkPlacement, talkCounterInTrack[i], i));

        IntVar[] pairCosts = new IntVar[noOfTalks * (noOfTalks - 1) / 2];

        int pairNo = 0;
        for (int i = 0; i < noOfTalks; i++)
            for (int j = i + 1; j < noOfTalks; j++) {

                pairCosts[pairNo] = new IntVar(store, "pair(" + i + ", " + j + ")Cost", 0, maxSingleCost);

                varsMatrix[pairNo][0] = pairCosts[pairNo];
                varsMatrix[pairNo][1] = talkPlacement[i];
                varsMatrix[pairNo][2] = talkPlacement[j];

                if (costMap.get(i).get(j) != null) {

                    store.impose(
                        new IfThenElse(new XeqY(talkPlacement[i], talkPlacement[j]), new XeqC(pairCosts[pairNo], costMap.get(i).get(j)),
                            new XeqC(pairCosts[pairNo], 0)));

                    IntervalDomain costPairDomain = new IntervalDomain(0, 0);
                    costPairDomain.unionAdapt(costMap.get(i).get(j));
                    store.impose(new In(pairCosts[pairNo], costPairDomain));
                } else
                    store.impose(new XeqC(pairCosts[pairNo], 0));

                pairNo++;
            }

        cost = new IntVar(store, "cost", 0, IntDomain.MaxInt);

        store.impose(new SumInt(pairCosts, "==", cost));

        vars = new ArrayList<>();
        for (int i = 0; i < talkPlacement.length; i++)
            vars.add(talkPlacement[i]);

        // store.print();
    }


    /**
     *
     * It uses MaxRegret variable ordering heuristic to search for a solution.
     * @param timeOutSeconds time-out in seconds
     * @return true if there is a solution, false otherwise.
     *
     */
    public boolean searchMaxRegretForMatrixOptimal(int timeOutSeconds) {

        long T1, T2, T;
        T1 = System.currentTimeMillis();

        search = new DepthFirstSearch<IntVar>();
        PrintOutListener<IntVar> solutionListener = new PrintOutListener<IntVar>();
        search.setSolutionListener(solutionListener);

        if (timeOutSeconds > 0)
            search.setTimeOut(timeOutSeconds);

        // pivot variable is at index 0.
        SelectChoicePoint<IntVar> select =
            new SimpleMatrixSelect<IntVar>(varsMatrix, new MaxRegret<IntVar>(), new SmallestDomain<IntVar>(), new IndomainMin<IntVar>());

        boolean result = search.labeling(store, select, cost);

        T2 = System.currentTimeMillis();
        T = T2 - T1;

        if (result)
            System.out.println("Variables : " + vars);
        else
            System.out.println("Failed to find any solution");

        System.out.println("\n\t*** Execution time = " + T + " ms");

        return result;

    }

    public boolean search(int maxCostAllowed, int timeOutSeconds) {

        if (maxCostAllowed != -1)
            store.impose(new XlteqC(cost, maxCostAllowed));

        long T1, T2, T;
        T1 = System.currentTimeMillis();

        search = new DepthFirstSearch<IntVar>();

        // pivot variable is at index 0.
        SelectChoicePoint<IntVar> select =
            new SimpleMatrixSelect<IntVar>(varsMatrix, new MaxRegret<IntVar>(), new SmallestDomain<IntVar>(), new IndomainMin<IntVar>());

        if (timeOutSeconds > 0)
            search.setTimeOut(timeOutSeconds);

        boolean result = search.labeling(store, select);

        T2 = System.currentTimeMillis();
        T = T2 - T1;

        if (result)
            System.out.println("Variables : " + vars);
        else
            System.out.println("Failed to find any solution");

        System.out.println("\n\t*** Execution time = " + T + " ms");

        return result;

    }

    /**
     * It executes the program to solve this Travelling Salesman Problem.
     * @param args no argument is used.
     */
    public static void main(String args[]) {

        int noOfParallelTracks = 6;
        int noOfTimeSlots = 6;
        int noOfTalks = noOfParallelTracks * noOfTimeSlots;
        int maxSingleCost = 50;
        int randomSeed = 55;

        ConferenceTalkPlacement example = new ConferenceTalkPlacement();

        // The first key in the main hashmap denotes the first (lower id value) talk in any pair.
        // The second key in the secondary hashmap denotes the second (higher id value) talk in any pair.
        // The value in the nested hashmap specify the cost if pair of talks (first key, second key) are scheduled
        // in the same time slot.
        // The goal is to minimize the sum of costs.
        Map<Integer, Map<Integer, Integer>> costMap = example.randomCosts(noOfTalks, randomSeed, maxSingleCost);

        example.model(noOfParallelTracks, noOfTalks, noOfTimeSlots, maxSingleCost, costMap);

        // example.store.print(); // Useful for small examples.

        // If you get the first time out then it means that the problem gets too difficult or you have setup the
        // maximum cost too low.
        int timeOutSeconds = 180;

        // Unlikely to finish anytime soon for random examples of size more than noOfParallelTracks=3, and noOfTimeSlots=3.
        // Real life examples maybe solvable to optimality for much larger sizes.

        if (example.searchMaxRegretForMatrixOptimal(timeOutSeconds)) {
            System.out.println("Solution(s) found");
            return;
        }

        // Everytime you find a solution reduce the maximum cost by a bit (e.g. 5%).
/*
        int maximumCost = 1700;
        if ( example.search(maximumCost, timeOutSeconds)) {
            System.out.println("Solution found with cost " + example.cost);
        }
*/

        // example.store.print(); // Useful for small examples.
    }
}
