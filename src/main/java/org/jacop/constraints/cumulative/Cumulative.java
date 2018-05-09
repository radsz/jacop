/*
 * Cumulative.java
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


package org.jacop.constraints.cumulative;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

import java.util.*;
import java.util.function.Function;

/**
 * Cumulative implements the scheduling constraint using
 * <p>
 * edge-finding algorithms based on
 * <p>
 * Petr Vilim, "Edge Finding Filtering Algorithm for Discrete Cumulative Resources in O(kn log n)",
 * Principles and Practice of Constraint Programming - CP 2009 Volume 5732 of the series Lecture
 * Notes in Computer Science pp 802-816.
 * <p>
 * and
 * <p>
 * Joseph Scott, "Filtering Algorithms for Discrete Cumulative Resources", MSc thesis, Uppsala
 * University, Department of Information Technology, 2010, no IT 10 048,
 * @see <a href="http://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-132172">http://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-132172</a>
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class Cumulative extends CumulativeBasic {

    TaskView[] taskReversed;

    private boolean doEdgeFind = true;

    private Set<Integer> preComputedCapacities = null;
    private int[] preComputedCapMap;
    
    protected Comparator<TaskView> taskIncEstComparator = (o1, o2) -> {
        return (o1.est() == o2.est()) ? (o1.lct() - o2.lct()) : (o1.est() - o2.est());
    };

    protected Comparator<TaskView> taskDecLctComparator = (o1, o2) -> {
        return (o2.lct() == o1.lct()) ? (o2.est() - o1.est()) : (o2.lct() - o1.lct());
    };

    /**
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     */
    public Cumulative(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit) {

        super(starts, durations, resources, limit);

        taskReversed = new TaskReversedView[starts.length];
        for (int i = 0; i < starts.length; i++) {
            taskReversed[i] = new TaskReversedView(starts[i], durations[i], resources[i]);
            taskReversed[i].index = i;
        }

        // check for possible overflow
        if (limit != null)
            for (Task t : taskNormal) {
                Math.addExact(t.start.max(), t.dur.max());
            }

        String s = System.getProperty("max_edge_find_size");
        int limitOnEdgeFind = 100;
        if (s != null)
            limitOnEdgeFind = Integer.parseInt(s);
        doEdgeFind = (starts.length <= limitOnEdgeFind);

	if (!possibleZeroTasks && grounded(resources)) {
	    preComputedCapacities = new LinkedHashSet<>();
	    for (TaskView t : taskNormal)
	    	preComputedCapacities.add(t.res.min());
	    
	    preComputedCapMap = new int[starts.length];
	    int capIndex = 0;
	    for (int ci : preComputedCapacities) {
		for (TaskView aT : taskNormal) {
		    if (aT.res.min() == ci)
			preComputedCapMap[aT.index] = capIndex;
		}
		capIndex++;
	    }
	}
    }

    /**
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     */
    public Cumulative(List<? extends IntVar> starts, List<? extends IntVar> durations, List<? extends IntVar> resources, IntVar limit) {

        this(starts.toArray(new IntVar[starts.size()]), durations.toArray(new IntVar[durations.size()]),
            resources.toArray(new IntVar[resources.size()]), limit);

    }

    @Override public void consistency(Store store) {

        do {

            store.propagationHasOccurred = false;

            profileProp(store);

            if (!store.propagationHasOccurred && doEdgeFind) {
	    	// overloadCheck();  // not needed if profile propagator is used
	    	edgeFind(store);
	    }

        } while (store.propagationHasOccurred);
    }

    /*
    void overloadCheck() {

	TaskView[] estList = new TaskNormalView[taskNormal.length];
	System.arraycopy(taskNormal, 0, estList, 0, estList.length);
	Arrays.sort(estList, (o1, o2) -> {
            return o1.est() - o2.est();
        }); // task est incremental comparator
	// System.out.println(java.util.Arrays.asList(estList));

	ThetaLambdaTree tree = new ThetaLambdaTree(limit);
	tree.buildTree(estList);
	tree.clearTree();

	TaskView[] lctList = new TaskNormalView[taskNormal.length];
	for (int i = 0; i < taskNormal.length; i++)
	    lctList[i] = new TaskNormalView(taskNormal[i]);
	Arrays.sort(lctList, (o1, o2) -> {
            return o1.lct() - o2.lct();
        });// task lct incremental comparator
	//System.out.println(java.util.Arrays.asList(lctList));

    
	long C = (long)limit.max();
	for (int j = 0; j < lctList.length; j++) {
	    tree.enableNode(lctList[j].treeIndex, lctList[j].res.min());

	    // System.out.println("j = " + j +", lctList[j].treeIndex = "+lctList[j].treeIndex+", tree.rootNode().env "+ tree.rootNode().env +", lctList[j].lct() = " + lctList[j].lct() + ", C = "+ C);

	    if (tree.rootNode().env > C * (long)lctList[j].lct()) {
		// System.out.println("FAIL");

		throw Store.failException;
	    }
	}
    }
    */
    
    private void edgeFind(Store store) {

        edgeFind(store, taskNormal);
        edgeFind(store, taskReversed);

    }

    private void edgeFind(Store store, TaskView[] tn) {

        // tasks sorted in non-decreasing order of est
        TaskView[] estList = filterZeroTasks(tn); // new TaskView[taskNormal.length];
        // System.arraycopy(tn, 0, estList, 0, estList.length);
        if (estList == null)
            return;

        Arrays.sort(estList, taskIncEstComparator);

        ThetaLambdaTree tree = new ThetaLambdaTree(limit);
        tree.buildTree(estList);

        // tasks sorted in non-increasing order of lct
        TaskView[] lctList = new TaskView[estList.length];
        System.arraycopy(estList, 0, lctList, 0, estList.length);
        Arrays.sort(lctList, taskDecLctComparator);

        int[] auxOrderListInv = new int[lctList.length];
        for (int i = 0; i < lctList.length; i++) {
            auxOrderListInv[lctList[i].index] = i;
        }

        // ========== Detect Order ============
        int[] prec = detectOrder(tree, lctList, auxOrderListInv, (long) limit.max());
        // System.out.println("*** prec = " + intArrayToString(prec));
        // write ThetaLambdaTree as dot file for visualization
        // tree.printTree("tree_init");

        // ========== Adjust Bounds ============
        adjustBounds(store, tree, lctList, prec, (long) limit.max());

    }

    private int[] detectOrder(ThetaLambdaTree tree, TaskView[] t, int[] lctInvOrder, long C) {

        int n = t.length;
        int[] prec = new int[n];

        for (TaskView aT1 : t)
            prec[aT1.index] = aT1.ect();

        for (TaskView aT : t) {
            if (tree.rootNode().env > C * (long) aT.lct()) {
                throw Store.failException;
            }

            while (tree.rootNode().envLambda > C * (long) aT.lct()) {
                int i = tree.rootNode().responsibleEnvLambda;
                prec[tree.get(i).task.index] = Math.max(prec[tree.get(i).task.index], aT.lct());
                tree.removeFromLambda(i);
            }
            tree.moveToLambda(aT.treeIndex);
        }

        int[] lctPrec = new int[n];
        for (int i = 0; i < prec.length; i++) {
            lctPrec[lctInvOrder[i]] = prec[i];
        }

        return lctPrec;
    }

    private void adjustBounds(Store store, ThetaLambdaTree tree, TaskView[] t, int[] prec, long cap) {

        int n = t.length;
        Set<Integer> capacities;
	int[] capMap;
	if (preComputedCapacities == null) {
	    capacities = new LinkedHashSet<>();
	    for (TaskView aT1 : t)
		capacities.add(aT1.res.min());
	    
	    capMap = new int[n];
	    int capIndex = 0;
	    for (int ci : capacities) {
		for (TaskView aT : t) {
		    if (aT.res.min() == ci)
			capMap[aT.index] = capIndex;
		}
		capIndex++;
	    }
	}
	else {
	    capacities = preComputedCapacities;
	    capMap = preComputedCapMap;
	}	
        // System.out.println("capacities = " + capacities);


        int[][] update = new int[capacities.size()][n];

        int capi = 0;
        for (int ci : capacities) {

            tree.clearTree();

            int upd = Integer.MIN_VALUE;

            for (int l = n - 1; l >= 0; l--) { // by non-decreasing of lct

                tree.enableNode(t[l].treeIndex, (long) ci);
                // tree.printTree("tree_task_"+t[l].index);

                long envlc = tree.calcEnvlc((long) t[l].lct(), (long) ci);
                int diff = Integer.MIN_VALUE;
                if (envlc != Long.MIN_VALUE) {
                    long tmp = envlc - (cap - (long) ci) * (long) t[l].lct();
                    long diffLong = divRoundUp(tmp, ci);
                    if (diffLong > Integer.MIN_VALUE && diffLong < Integer.MAX_VALUE)
                        diff = (int) diffLong;
                }
                upd = Math.max(upd, diff);
                update[capi][l] = upd;
            }
            capi++;
        }
	
        Integer[] precTaskOrder = new Integer[n];
	for (int i = 0; i < n; i++)
            precTaskOrder[i] = i;
        Arrays.sort(precTaskOrder, (Integer o1, Integer o2) -> prec[o2.intValue()] - prec[o1.intValue()]);

        int j = 0;
        outer:
        for (int i = 0; i < n; i++) {

            TaskView taskI = t[precTaskOrder[i]];
            int precI = prec[precTaskOrder[i]];

            // first skip all task j that are lct after prec
            while (j < n && t[j].lct() > precI) 
                j++;

            if (j < n) {

                // update est[i] if possible
                int nj = j;
                inner:
                while (nj < n && t[nj].lct() == precI) {
                    if (t[nj].lct() < taskI.lct()) {
                        taskI.updateEdgeFind(store.level, update[capMap[taskI.index]][nj]);
                        break inner;
                    }
                    nj++;
                }
            } else
                break outer;
        }
    }

    TaskView[] filterZeroTasks(TaskView[] ts) {

        if (possibleZeroTasks) {
            TaskView[] nonZeroTasks = new TaskView[ts.length];
            int k = 0;

            for (TaskView t1 : ts)
                if (t1.res.min() != 0 && t1.dur.min() != 0) {
                    nonZeroTasks[k] = t1;
                    t1.index = k++;
                }

            if (k == 0)
                return null;
            TaskView[] t = new TaskView[k];
            System.arraycopy(nonZeroTasks, 0, t, 0, k);
            return t;
        } else
            return ts;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());
        if (doEdgeFind)
            result.append(" : cumulative([ ");
        else if (super.cumulativeForConstants != null)
            result.append(" : cumulativePrimary([ ");
        else
            result.append(" : cumulativeBasic([ ");

        for (int i = 0; i < taskNormal.length - 1; i++)
            result.append(taskNormal[i]).append(", ");

        result.append(taskNormal[taskNormal.length - 1]);

        result.append(" ]").append(", limit = ").append(limit).append(" )");

        return result.toString();

    }

    private long divRoundUp(long a, long b) {
        if (a >= 0)
            return (a + b - 1) / b;
        else // a < 0
            return a / b;
    }

}
