/*
 * CumulativeUnary.java
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

import org.jacop.core.IntVar;
import org.jacop.core.Store;

import java.util.Arrays;
import java.util.Comparator;
import java.util.List;

/**
 * CumulativeUnary implements the scheduling constraint for unary resources using
 * <p>
 * overload, not-first-not-last and detectable algorithms based on
 * <p>
 * Petr Vilim, "O(n log n) Filtering Algorithms for Unary Resource Constraints", Proceedings of
 * CP-AI-OR 2004,
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class CumulativeUnary extends Cumulative {

    private boolean doProfile = false;

    /**
     * Local copies of tasks in normal and reserved views
     */
    final private TaskView[] tvn;
    final private TaskView[] tvr;

    private Comparator<TaskView> taskIncLctComparator = (o1, o2) -> (o1.lct() == o2.lct()) ? (o1.est() - o2.est()) : (o1.lct() - o2.lct());

    private Comparator<TaskView> taskIncLstComparator = (o1, o2) -> (o1.lst() == o2.lst()) ? (o1.est() - o2.est()) : (o1.lst() - o2.lst());

    private Comparator<TaskView> taskIncEctComparator = (o1, o2) -> (o1.ect() == o2.ect()) ? (o1.est() - o2.est()) : (o1.ect() - o2.ect());

    /**
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     */
    public CumulativeUnary(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit) {

        super(starts, durations, resources, limit);
        checkInput(durations, i -> i.min() >= 0, "duration does not allow negative values");
        checkInput(resources, i -> i.min() >= 0, "resource does not allow negative values");
        queueIndex = 2;

        tvn = new TaskNormalView[starts.length];
        tvr = super.taskReversed;
        for (int i = 0; i < starts.length; i++) {
            tvn[i] = new TaskNormalView(starts[i], durations[i], resources[i]);
            tvn[i].index = i;
        }
    }

    /**
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     * @param doProfile defines whether to do profile-based propagation (true) or not (false); default is false
     */
    public CumulativeUnary(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit, boolean doProfile) {

        this(starts, durations, resources, limit);
        this.doProfile = doProfile;
    }

    /**
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     */
    public CumulativeUnary(List<? extends IntVar> starts, List<? extends IntVar> durations, List<? extends IntVar> resources,
        IntVar limit) {

        this(starts.toArray(new IntVar[starts.size()]), durations.toArray(new IntVar[durations.size()]),
            resources.toArray(new IntVar[resources.size()]), limit);
    }

    /**
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     * @param doProfile defines whether to do profile-based propagation (true) or not (false); default is false
     */
    public CumulativeUnary(List<? extends IntVar> starts, List<? extends IntVar> durations, List<? extends IntVar> resources, IntVar limit,
        boolean doProfile) {

        this(starts.toArray(new IntVar[starts.size()]), durations.toArray(new IntVar[durations.size()]),
            resources.toArray(new IntVar[resources.size()]), limit, doProfile);
    }

    @Override public void consistency(Store store) {

        TaskView[] tn = filterZeroTasks(tvn);
        if (tn == null)
            return;
        TaskView[] tr = filterZeroTasks(tvr);

        do {

            store.propagationHasOccurred = false;

            if (doProfile)
                profileProp(store);

            if (! store.propagationHasOccurred) {

                if (!doProfile)
                    overload(tn);
                detectable(store, tn, tr);
                notFirstNotLast(store, tn, tr);
                edgeFind(store, tn, tr);
            }

        } while (store.propagationHasOccurred);
    }

    private void overload(TaskView[] ts) {

        TaskView[] t = new TaskView[ts.length];
        System.arraycopy(ts, 0, t, 0, ts.length);
        // tasks sorted in ascending order of EST for Theta tree
        Arrays.sort(t, taskIncEstComparator);

        ThetaTree tree = new ThetaTree();
        tree.initTree(t);
        //tree.printTree("tree_init");

        // tasks sorted in ascending order of lct
        Arrays.sort(t, taskIncLctComparator);

        for (TaskView aT : t) {
            tree.enableNode(aT.treeIndex);
            if (tree.get(tree.root()).ect > aT.lct())
                throw Store.failException;
        }
    }

    private void notFirstNotLast(Store store, TaskView[] tn, TaskView[] tr) {

        notFirstNotLastPhase(store, tn);
        notFirstNotLastPhase(store, tr);

    }

    private void notFirstNotLastPhase(Store store, TaskView[] tc) {

        TaskView[] t = new TaskView[tc.length];
        System.arraycopy(tc, 0, t, 0, tc.length);
        // tasks sorted in ascending order of EST for Theta tree
        Arrays.sort(t, taskIncEstComparator);

        ThetaTree tree = new ThetaTree();
        tree.initTree(t);
        // tree.printTree("tree_init");

        // tasks sorted in ascending order of lct
        Arrays.sort(t, taskIncLctComparator);

        // tasks sorted in ascending order of lct - p (lst)
        TaskView[] q = new TaskView[t.length];
        System.arraycopy(t, 0, q, 0, t.length);
        Arrays.sort(q, taskIncLstComparator);

        notLast(store, tree, t, q, tc);
    }

    private void notLast(Store store, ThetaTree tree, TaskView[] t, TaskView[] q, TaskView[] tc) {

        int n = t.length;
        int[] updateLCT = new int[n];
        for (int i = 0; i < n; i++)
            updateLCT[i] = t[i].lct();

        int indexQ = 0;
        for (int i = 0; i < n; i++) {
            int j = -1;

            while (indexQ < n && t[i].lct() > q[indexQ].lst()) {

                if (tree.ect(t[i].treeIndex) > t[i].lst())
                    updateLCT[i] = Math.min(q[indexQ - 1].lst(), updateLCT[i]);

                j = tc[q[indexQ].index].treeIndex;
                tree.enableNode(j);
                indexQ++;
            }

            if (j >= 0 && tree.ect(t[i].treeIndex) > t[i].lst()) {
                updateLCT[i] = Math.min(q[indexQ - 1].lst(), updateLCT[i]);
                // updateLCT[i] = Math.min(to[tree.get(j).task.index].lst(), updateLCT[i]);
            }
        }

        for (int i = 0; i < n; i++) {
            t[i].updateNotFirstNotLast(store.level, updateLCT[i]);
        }
    }


    private void detectable(Store store, TaskView[] tn, TaskView[] tr) {
        detectablePhase(store, tn);
        detectablePhase(store, tr);
    }


    private void detectablePhase(Store store, TaskView[] tc) {

        TaskView[] t = new TaskView[tc.length];
        System.arraycopy(tc, 0, t, 0, tc.length);
        // tasks sorted in ascending order of EST for Theta tree
        Arrays.sort(t, taskIncEstComparator);

        ThetaTree tree = new ThetaTree();
        tree.initTree(t);
        // tree.printTree("tree_init");

        // tasks sorted in ascending order of lct
        Arrays.sort(t, taskIncEctComparator);

        // tasks sorted in ascending order of lct - p (lst)
        TaskView[] q = new TaskView[t.length];
        System.arraycopy(t, 0, q, 0, t.length);
        Arrays.sort(q, taskIncLstComparator);

        detectable(store, tree, t, q, tc);

    }

    private void detectable(Store store, ThetaTree tree, TaskView[] t, TaskView[] q, TaskView[] to) {

        int n = t.length;
        int[] updateEST = new int[n];

        int indexQ = 0;
        for (int i = 0; i < n; i++) {
            int j;

            while (indexQ < n && t[i].ect() > q[indexQ].lst()) {
                j = to[q[indexQ].index].treeIndex;
                tree.enableNode(j);
                indexQ++;
            }
            updateEST[i] = tree.ect(t[i].treeIndex);
        }

        for (int i = 0; i < n; i++) {
            t[i].updateDetectable(store.level, updateEST[i]);
        }

    }

    private void edgeFind(Store store, TaskView[] tn, TaskView[] tr) {

        edgeFindPhase(store, tn);
        edgeFindPhase(store, tr);

    }

    private void edgeFindPhase(Store store, TaskView[] tc) {

        // tasks sorted in non-decreasing order of est
        TaskView[] estList = new TaskView[tc.length];
        System.arraycopy(tc, 0, estList, 0, tc.length);
        Arrays.sort(estList, taskIncEstComparator);

        ThetaLambdaUnaryTree tree = new ThetaLambdaUnaryTree();
        tree.buildTree(estList);

        // tasks sorted in non-increasing order of lct
        TaskView[] lctList = new TaskView[estList.length];
        System.arraycopy(estList, 0, lctList, 0, estList.length);
        Arrays.sort(lctList, taskDecLctComparator);

        int n = lctList.length;
        TaskView t = lctList[0];
        for (int i = 0; i < n - 1; i++) {
            if (tree.ect() > t.lct())
                throw Store.failException;

            tree.moveToLambda(t.treeIndex);
            t = lctList[i + 1];

            while (tree.ectLambda() > t.lct()) {
                int j = tree.rootNode().responsibleEctLambda;
                tc[tree.get(j).task.index].updateEdgeFind(store.level, tree.ect());
                tree.removeFromLambda(j);
            }
        }
    }


    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());

        result.append(" : cumulativeUnary([ ");
        for (int i = 0; i < taskNormal.length - 1; i++)
            result.append(taskNormal[i]).append(", ");

        result.append(taskNormal[taskNormal.length - 1]);

        result.append(" ]").append(", limit = ").append(limit).append(" )");

        return result.toString();

    }

}

