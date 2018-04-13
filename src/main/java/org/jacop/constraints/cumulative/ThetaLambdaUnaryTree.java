/*
 * ThetaLambdaUnaryTree.java
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
 * Implements ThetaLambdaUnaryTree and operations on this tree for Cumulative constraint
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */


/*
 * Defines the basic data structure for cumulative constraint's edge-finding algorithm.
 */
class ThetaLambdaUnaryTree extends ThetaTree {

    // array that keeps all nodes of the balanced binary tree and organizes the tree structure
    ThetaLambdaUnaryNode[] tree;
    // list of ordered tasks
    TaskView[] orderedTasks;

    ThetaLambdaUnaryNode empty = new ThetaLambdaUnaryNode();

    public ThetaLambdaUnaryTree() {
    }

    public void buildTree(TaskView[] task) {
        n = task.length;
        treeSize = (int) Math.pow(2, Math.round(Math.ceil(Math.log(n) / Math.log(2)))) + n - 1;
        tree = new ThetaLambdaUnaryNode[treeSize];

        orderedTasks = task;

        for (int i = treeSize - 1; i >= treeSize - n; i--)
            computeLeaveVals(i);

        for (int i = treeSize - n - 1; i >= 0; i--) {

	    if (notExist(left(i))) {
		tree[i] = empty;
		tree[i].index = i;
		clearNode(i);
	    } else if (notExist(right(i))) {
		tree[i] = tree[left(i)];
	    } else {
		tree[i] = new ThetaLambdaUnaryNode();
		tree[i].index = i;

		computeNodeVals(i);
	    }
	}
    }

    void computeLeaveVals(int i) {
        tree[i] = new ThetaLambdaUnaryNode();
        tree[i].index = i;

        addToThetaInit(i);
        tree[i].ectLambda = Integer.MIN_VALUE;
        tree[i].pLambda = Integer.MIN_VALUE;
        tree[i].responsiblePLambda = i;
        tree[i].responsibleEctLambda = i;
    }

    void addToThetaInit(int i) {
        int t = i - (treeSize - n); // in our case we pass list of ordered tasks already
        tree[i].task = orderedTasks[t];
        orderedTasks[t].treeIndex = i;

        tree[i].p = orderedTasks[t].dur.min();
        tree[i].ect = tree[i].task.ect();
    }

    void computeNodeVals(int i) {

	if (notExist(left(i)) || notExist(right(i)))
	    return;
	else {

            ThetaLambdaUnaryNode node = tree[i];
            ThetaLambdaUnaryNode l = tree[left(i)];
            ThetaLambdaUnaryNode r = tree[right(i)];

            node.p = plus(l.p, r.p);
            node.ect = Math.max(plus(l.ect, r.p), r.ect);

            if (plus(l.pLambda, r.p) > plus(r.pLambda, l.p)) {
		node.pLambda = plus(l.pLambda, r.p);
                node.responsiblePLambda = l.responsiblePLambda;
            } else {
                node.pLambda = plus(r.pLambda, l.p);
                node.responsiblePLambda = r.responsiblePLambda;
            }

            if (plus(l.ectLambda, r.p) > plus(r.pLambda, l.ect)) {
                if (plus(l.ectLambda, r.p) > r.ectLambda) {
                    node.ectLambda = plus(l.ectLambda, r.p);
                    node.responsibleEctLambda = l.responsibleEctLambda;
                } else {
                    node.ectLambda = r.ectLambda;
                    node.responsibleEctLambda = r.responsibleEctLambda;
                }
            } else {
                if (plus(r.pLambda, l.ect) > r.ectLambda) {
                    node.ectLambda = plus(r.pLambda, l.ect);
                    node.responsibleEctLambda = r.responsiblePLambda;
                } else {
                    node.ectLambda = r.ectLambda;
                    node.responsibleEctLambda = r.responsibleEctLambda;
                }
            }
        }
    }

    int ect() {
        return tree[0].ect;
    }

    int ectLambda() {
        return tree[0].ectLambda;
    }

    void clearNode(int i) {
        tree[i].p = 0;
        tree[i].ect = Integer.MIN_VALUE;
        tree[i].pLambda = Integer.MIN_VALUE;
        tree[i].ectLambda = Integer.MIN_VALUE;
    }

    void moveToLambda(int i) {
        ThetaLambdaUnaryNode node = tree[i];
        node.pLambda = node.p;
        node.ectLambda = node.ect;
        node.p = 0;
        node.ect = Integer.MIN_VALUE;
        updateTree(parent(i));
    }

    void removeFromLambda(int i) {
        ThetaLambdaUnaryNode node = tree[i];
        node.pLambda = Integer.MIN_VALUE;
        node.ectLambda = Integer.MIN_VALUE;
        updateTree(parent(i));
    }

    void updateTree(int i) {
        while (exist(i)) {
            computeNodeVals(i);
            i = parent(i);
        }
    }

    ThetaLambdaUnaryNode leaf(int i) {
        return tree[leafIndex(i)];
    }

    boolean isLeaf(int i) {
        int l = tree[i].index;
        return l >= treeSize - n && l < treeSize;
    }

    ThetaLambdaUnaryNode rootNode() {
        return tree[root()];
    }

    ThetaLambdaUnaryNode get(int i) {
        return tree[i];
    }

    public void printTree(String name) {

        try (PrintStream out = new PrintStream(new FileOutputStream(name + ".dot"), true, "UTF-8")) {
            out.print(toGraph(name));
            out.close();
        } catch (IOException e) {
	    throw new RuntimeException("IO exception; ignored");
        }
    }


    public String toGraph(String name) {

        StringBuffer result = new StringBuffer();

        result.append("digraph ThetaLambdaUnaryTree" + name);
        result.append(" {");
        result.append("graph [  fontsize = 12,");
        result.append("size = \"5,5\" ];\n");

        for (int i = 0; i < treeSize; i++) {
            result.append("node_" + i + " [shape = box, label = \"" + tree[i] + "\"]\n");
        }

        result.append(treeToGraph(root()));

        result.append("label =\"\n\nThetaLambdaUnaryTree" + name + "\n\"");

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

        result.append("ThetaLambdaUnaryTree\n");
        for (int i = 0; i < treeSize; i++)
            result.append("Node " + i + "\n============\n" + tree[i] + "\n============\n");

        return result.toString();
    }

}
