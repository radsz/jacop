/*
 * ThetaLambdaTree.java
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

import java.io.PrintStream;
import java.io.FileOutputStream;
import java.io.IOException;

/**
 * Implements ThetaLambdaTree and operations on this tree for Cumulative constraint
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */


/*
 * Defines the basic data structure for cumulative constraint's edge-finding algorithm.
 */
class ThetaLambdaTree extends Tree {

    // array that keeps all nodes of the balanced binary tree and organizes the tree structure
    private ThetaLambdaNode[] tree;
    // capacity
    IntVar C;
    // list of ordered tasks
    private TaskView[] orderedTasks;

    private ThetaLambdaNode empty = new ThetaLambdaNode();

    public ThetaLambdaTree(IntVar capacity) {
        C = capacity;
    }

    public void buildTree(TaskView[] task) {
        n = task.length;
        treeSize = (int) Math.pow(2, Math.round(Math.ceil(Math.log(n) / Math.log(2)))) + n - 1;
        tree = new ThetaLambdaNode[treeSize];

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
		tree[i] = new ThetaLambdaNode();
		tree[i].index = i;

		computeNodeVals(i);
	    }
	}
    }

    private void computeLeaveVals(int i) {
	ThetaLambdaNode node = new ThetaLambdaNode();
        tree[i] = node;
        node.index = i;

        addToThetaInit(i);
        node.envLambda = Long.MIN_VALUE;
        node.eLambda = 0L;
        node.responsibleELambda = i;
        node.responsibleEnvLambda = i;
    }

    private void addToThetaInit(int i) {
        int t = i - (treeSize - n); // in our case we pass list of ordered tasks already
        tree[i].task = orderedTasks[t];
        orderedTasks[t].treeIndex = i;

        tree[i].e = orderedTasks[t].e();
        tree[i].env = tree[i].task.env((long)C.max());
    }

    private void computeNodeVals(int i) {

	if (notExist(left(i)) || notExist(right(i)))
	    return;
	else {
	    
            ThetaLambdaNode node = tree[i];
            ThetaLambdaNode l = tree[left(i)];
            ThetaLambdaNode r = tree[right(i)];

            node.e = l.e + r.e;
            node.env = Math.max(plus(l.env, r.e), r.env);
            node.envC = Math.max(plus(l.envC, r.e), r.envC);

            if (l.eLambda + r.e > l.e + r.eLambda) {
                node.eLambda = l.eLambda + r.e;
                node.responsibleELambda = l.responsibleELambda;
            } else {
                node.eLambda = l.e + r.eLambda;
                node.responsibleELambda = r.responsibleELambda;
            }

            if (plus(l.envLambda, r.e) > plus(l.env, r.eLambda)) {
                if (plus(l.envLambda, r.e) > r.envLambda) {
                    node.envLambda = plus(l.envLambda, r.e);
                    node.responsibleEnvLambda = l.responsibleEnvLambda;
                } else {
                    node.envLambda = r.envLambda;
                    node.responsibleEnvLambda = r.responsibleEnvLambda;
                }
            } else {
                if (plus(l.env, r.eLambda) > r.envLambda) {
                    node.envLambda = plus(l.env, r.eLambda);
                    node.responsibleEnvLambda = r.responsibleELambda;
                } else {
                    node.envLambda = r.envLambda;
                    node.responsibleEnvLambda = r.responsibleEnvLambda;
                }
            }
	}
    }

    private void computeThetaNode(int i) {

        if (notExist(left(i))) {
            return;
        } else if (notExist(right(i))) {
            return;
        } else {

            ThetaLambdaNode node = tree[i];
            ThetaLambdaNode l = tree[left(i)];
            ThetaLambdaNode r = tree[right(i)];

            node.e = l.e + r.e;
            node.env = Math.max(plus(l.env, r.e), r.env);
            node.envC = Math.max(plus(l.envC, r.e), r.envC);
        }
    }

    void clearNode(int i) {
	ThetaLambdaNode node = tree[i];
        node.e = 0L;
        node.env = Long.MIN_VALUE;
        node.envC = Long.MIN_VALUE;
        node.eLambda = 0L;
        node.envLambda = Long.MIN_VALUE;
    }

    private void updateThetaTree(int i) {
        while (exist(i)) {
            computeThetaNode(i);
            i = parent(i);
        }
    }

    void enableNode(int i, long ci) {
        ThetaLambdaNode node = tree[i];
        node.e = node.task.e();
        node.env = node.task.env(C.max());
        node.envC = ((long)C.max() - ci) * (long)node.task.est() + node.task.e();

        updateThetaTree(parent(i));
    }

    void disableNode(int i) {
        clearNode(i);
        updateThetaTree(parent(i));
    }

    void moveToLambda(int i) {
        ThetaLambdaNode node = tree[i];
        node.eLambda = node.e;
        node.envLambda = node.env;
        node.e = 0L;
        node.env = Long.MIN_VALUE;
        node.envC = Long.MIN_VALUE;
        updateTree(parent(i));
    }

    void removeFromLambda(int i) {
        ThetaLambdaNode node = tree[i];
        node.eLambda = 0L;
        node.envLambda = Long.MIN_VALUE;
        updateTree(parent(i));
    }

    private void updateTree(int i) {
        while (exist(i)) {
            computeNodeVals(i);
            i = parent(i);
        }
    }

    long calcEnvlc(long bound, long c) {

        int v = root();
        long e = 0L;
        long maxEnvC = ((long)C.max() - c) * bound;

        while (!isLeaf(v)) {
            if (plus(tree[right(v)].envC, e) > maxEnvC) {
                v = right(v);
            } else {
                e += tree[right(v)].e;
                v = left(v);
            }
        }
        // Cut
        // v is the rightmost node in the alpha subtree

        // System.out.println("---------> Cut at node " + v + ", est = " + tree[v].task.start.min());

        long e_alpha = tree[v].e;
        long env_alpha = tree[v].env;
        long e_beta = 0L;

        while (!isRoot(v)) {
            if (isLeft(v)) {
                e_beta += tree[siblingRight(v)].e;
            } else { // isRight(v)
                env_alpha = Math.max(plus(tree[siblingLeft(v)].env, e_alpha), env_alpha);
                e_alpha += tree[siblingLeft(v)].e;
            }
            v = parent(v);
        }
        // System.out.println("e_beta = " + e_beta + ", env_alpha = " + env_alpha);

        return plus(env_alpha, e_beta);
    }

    IntVar getCapacity() {
        return C;
    }

    void setCapacity(IntVar capacity) {
        C = capacity;
    }

    ThetaLambdaNode leaf(int i) {
        return tree[leafIndex(i)];
    }

    private boolean isLeaf(int i) {
        int l = tree[i].index; // must use this since we make tree balanced and copy nodes up in the tree sometimes
        return l >= treeSize - n && l < treeSize;
    }

    ThetaLambdaNode rootNode() {
        return tree[root()];
    }

    ThetaLambdaNode get(int i) {
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

        result.append("digraph ThetaLambdaTree").append(name);
        result.append(" {");
        result.append("graph [  fontsize = 12,");
        result.append("size = \"5,5\" ];\n");

        for (int i = 0; i < treeSize; i++) {
            result.append("node_").append(i).append(" [shape = box, label = \"").append(tree[i]).append("\"]\n");
        }

        result.append(treeToGraph(root()));

        result.append("label =\"\n\nThetaLambdaTree").append(name).append("\n\"");

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
                result.append(s).append("node_").append(left(i)).append("\n");
                result.append(treeToGraph(left(i)));
            }
            if (exist(right(i))) {
                result.append(s).append("node_").append(right(i)).append("\n");
                result.append(treeToGraph(right(i)));
            }

            return result;
        }
    }

    public String toString() {

        StringBuffer result = new StringBuffer();

        result.append("ThetaLambdaTree\n");
        for (int i = 0; i < treeSize; i++)
            result.append("Node ").append(i).append("\n============\n").append(tree[i]).append("\n============\n");

        return result.toString();
    }

}
