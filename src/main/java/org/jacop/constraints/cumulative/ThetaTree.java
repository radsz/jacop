/**
 * ThetaTree.java
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

import java.io.PrintStream;
import java.io.FileOutputStream;
import java.io.IOException;

/**
 * Implements ThetaTree and operations on this tree for Cumulative constraint
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */


/*
 * Defines the basic data structure for cumulative constraint's edge-finding algorithm.
 */
class ThetaTree extends Tree {

    // number of leaves (tasks)
    int n;
    // array that keeps all nodes of the balanced binary tree and organizes the tree structure
    ThetaNode[] tree;
    // list of ordered tasks
    TaskView[] orderedTasks;

    ThetaNode empty = new ThetaNode();

    public ThetaTree() {
    }

    // public void buildEmptyTree(TaskView[] task) {
    //   int n = task.length;
    //   treeSize = (int)Math.pow(2 , Math.round(Math.ceil(Math.log(n) / Math.log(2)))) + n - 1;
    //   tree = new ThetaNode[treeSize];

    //   orderedTasks = task;

    //   // clear leaves
    //   for (int i = treeSize-1; i >= treeSize - n; i--)
    //     clearNode(i);
    //   // clear intermediate nodes
    //   for (int i = treeSize - n - 1; i >= 0; i--)
    //     clearNode(i);
    // }

    public void buildTree(TaskView[] task) {
        n = task.length;
        treeSize = (int) Math.pow(2, Math.round(Math.ceil(Math.log(n) / Math.log(2)))) + n - 1;
        tree = new ThetaNode[treeSize];

        orderedTasks = task;

        for (int i = treeSize - 1; i >= treeSize - n; i--)
            computeLeaveVals(i);
        for (int i = treeSize - n - 1; i >= 0; i--)
            computeNodeVals(i);
    }

    public void initTree(TaskView[] task) {
        n = task.length;
        treeSize = (int) Math.pow(2, Math.round(Math.ceil(Math.log(n) / Math.log(2)))) + n - 1;
        tree = new ThetaNode[treeSize];

        orderedTasks = task;

        for (int i = treeSize - 1; i >= treeSize - n; i--)
            addLeave(i);
        for (int i = treeSize - n - 1; i >= 0; i--)
            addNode(i);
    }

    void addLeave(int i) {
        tree[i] = new ThetaNode();
        tree[i].index = i;

        int t = i - (treeSize - n); // in our case we pass list of ordered tasks already
        tree[i].task = orderedTasks[t];
        orderedTasks[t].treeIndex = i;

        tree[i].p = 0;
        tree[i].ect = Integer.MIN_VALUE;

        tree[i].pT = orderedTasks[t].dur().min();
        tree[i].ectT = tree[i].task.ect();

    }

    void computeLeaveVals(int i) {
        tree[i] = new ThetaNode();
        tree[i].index = i;

        addToThetaInit(i);
    }

    void addToThetaInit(int i) {
        int t = i - (treeSize - n); // in our case we pass list of ordered tasks already
        tree[i].task = orderedTasks[t];
        orderedTasks[t].treeIndex = i;

        tree[i].p = orderedTasks[t].dur().min();
        tree[i].ect = tree[i].task.ect();
    }

    void computeNodeVals(int i) {

        if (notExist(left(i))) {
            tree[i] = empty;
            tree[i].index = i;
            clearNode(i);
        } else if (notExist(right(i))) {
            tree[i] = tree[left(i)];
        } else {
            tree[i] = new ThetaNode();
            tree[i].index = i;

            ThetaNode node = tree[i];
            ThetaNode l = tree[left(i)];
            ThetaNode r = tree[right(i)];

            node.p = plus(l.p, r.p);
            node.ect = Math.max(plus(l.ect, r.p), r.ect);
        }
    }


    void addNode(int i) {

        if (notExist(left(i))) {
            tree[i] = empty;
            tree[i].index = i;
            clearNode(i);
        } else if (notExist(right(i))) {
            tree[i] = tree[left(i)];
        } else {
            tree[i] = new ThetaNode();
            tree[i].index = i;

            ThetaNode node = tree[i];

            node.p = 0;
            node.ect = Integer.MIN_VALUE;
        }
    }

    void computeNode(int i) {

        if (notExist(left(i))) {
            tree[i] = empty;
            tree[i].index = i;
            clearNode(i);
        } else if (notExist(right(i))) {
            tree[i] = tree[left(i)];
        } else {

            ThetaNode node = tree[i];
            ThetaNode l = tree[left(i)];
            ThetaNode r = tree[right(i)];

            node.p = plus(l.p, r.p);
            node.ect = Math.max(plus(l.ect, r.p), r.ect);
        }
    }

    void clearNode(int i) {

        tree[i].p = 0;
        tree[i].ect = Integer.MIN_VALUE;
    }

    void clearTree() {
        for (int i = 0; i < treeSize; i++)
            clearNode(i);
    }

    void updateTree(int i) {
        while (exist(i)) {
            computeNode(i);
            i = parent(i);
        }
    }

    void enableNode(int i) {
        tree[i].assignValues();
        // node keeps the original values; assigned in method addLeave
        // node.p = tree[i].task.dur().min();
        // node.ect = tree[i].task.ect();

        updateTree(parent(i));
    }

    void disableNode(int i) {
        clearNode(i);
        updateTree(parent(i));
    }

    int ect(int i) {
        if (tree[i].ect != Integer.MIN_VALUE) {

            disableNode(i);
            int ect = tree[root()].ect;
            enableNode(i);

            return ect;
        } else {
            return tree[root()].ect;
        }
    }

    int leaveIndex(int i) {
        return i - (treeSize - n);
    }

    ThetaNode leaf(int i) {
        return tree[leaveIndex(i)];
    }

    boolean isLeaf(int i) {
        int l = tree[i].index;
        return l >= treeSize - n && l < treeSize;
    }

    ThetaNode rootNode() {
        return tree[root()];
    }

    ThetaNode get(int i) {
        return tree[i];
    }

    public void printTree(String name) {

        try (PrintStream out = new PrintStream(new FileOutputStream(name + ".dot"))) {
            out.print(toGraph(name));
            out.close();
        } catch (IOException e) {
            //do stuff with exception
            System.out.println("IO exception; ignored");
            System.exit(0);
        }
    }


    public String toGraph(String name) {

        StringBuffer result = new StringBuffer();

        result.append("digraph ThetaTree" + name);
        result.append(" {");
        result.append("graph [  fontsize = 12,");
        result.append("size = \"5,5\" ];\n");

        for (int i = 0; i < treeSize; i++) {
            result.append("node_" + i + " [shape = box, label = \"" + tree[i] + "\"]\n");
        }

        result.append(treeToGraph(root()));

        result.append("label =\"\n\nThetaTree" + name + "\n\"");

        result.append("}");

        return result.toString();
    }

    StringBuffer treeToGraph(int i) {

        StringBuffer result = new StringBuffer("");

        if (notExist(i)) {
            return result;
        } else {
            String s = "node_" + i + " -> "; //"[label = \""+ tree[i] +"\"] -> ";
            if (exist(left(i))) {
                result.append(s + "node_" + left(i) + "\n");
                result.append(treeToGraph(left(i)));
            }
            if (exist(right(i))) {
                result.append(s + "node_" + right(i) + "\n");
                result.append(treeToGraph(right(i)));
            }

            return result;
        }
    }

    public String toString() {

        StringBuffer result = new StringBuffer();

        result.append("ThetaTree\n");
        for (int i = 0; i < treeSize; i++)
            result.append("Node " + i + "\n============\n" + tree[i] + "\n============\n");

        return result.toString();
    }

}
