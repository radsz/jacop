/*
 * ThetaLambdaTree.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.constraints.cumulative;

import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntVar;

/*
 * Implements ThetaLambdaTree and operations on this tree for Cumulative constraint
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */

/*
 * Defines the basic data structure for cumulative constraint's edge-finding algorithm.
 */
@Slf4j
class ThetaLambdaTree extends Tree {

  private final ThetaLambdaNode empty = new ThetaLambdaNode();
  // capacity
  IntVar c;
  // array that keeps all nodes of the balanced binary tree and organizes the tree structure
  private ThetaLambdaNode[] tree;
  // list of ordered tasks
  private TaskView[] orderedTasks;

  public ThetaLambdaTree(IntVar capacity) {
    c = capacity;
  }

  public void buildTree(TaskView[] task) {
    n = task.length;
    treeSize = (int) Math.pow(2, Math.round(Math.ceil(Math.log(n) / Math.log(2)))) + n - 1;
    tree = new ThetaLambdaNode[treeSize];

    orderedTasks = task;

    for (int i = treeSize - 1; i >= treeSize - n; i--) {
      computeLeaveVals(i);
    }

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
    node.responsibleElambda = i;
    node.responsibleEnvLambda = i;
  }

  private void addToThetaInit(int i) {
    int t = i - (treeSize - n); // in our case we pass list of ordered tasks already
    tree[i].task = orderedTasks[t];
    orderedTasks[t].treeIndex = i;

    tree[i].e = orderedTasks[t].energy();
    tree[i].env = tree[i].task.env(c.max());
  }

  private void computeNodeVals(int i) {

    if (!notExist(left(i)) && !notExist(right(i))) {

      ThetaLambdaNode node = tree[i];
      ThetaLambdaNode l = tree[left(i)];
      ThetaLambdaNode r = tree[right(i)];

      node.e = l.e + r.e;
      node.env = Math.max(plus(l.env, r.e), r.env);
      node.envC = Math.max(plus(l.envC, r.e), r.envC);

      if (l.eLambda + r.e > l.e + r.eLambda) {
        node.eLambda = l.eLambda + r.e;
        node.responsibleElambda = l.responsibleElambda;
      } else {
        node.eLambda = l.e + r.eLambda;
        node.responsibleElambda = r.responsibleElambda;
      }

      computeEnvLambda(node, l, r);
    }
  }

  private void computeEnvLambda(ThetaLambdaNode node, ThetaLambdaNode l, ThetaLambdaNode r) {
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
        node.responsibleEnvLambda = r.responsibleElambda;
      } else {
        node.envLambda = r.envLambda;
        node.responsibleEnvLambda = r.responsibleEnvLambda;
      }
    }
  }

  private void computeThetaNode(int i) {

    if (!notExist(left(i)) && !notExist(right(i))) {

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
    node.e = node.task.energy();
    node.env = node.task.env(c.max());
    node.envC = (c.max() - ci) * node.task.est() + node.task.energy();

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

  long calcEnvlc(long bound, long cap) {

    int v = root();
    long e = 0L;
    long maxEnvC = (c.max() - cap) * bound;

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

    long eAlpha = tree[v].e;
    long envAlpha = tree[v].env;
    long eBeta = 0L;

    while (!isRoot(v)) {
      if (isLeft(v)) {
        eBeta += tree[siblingRight(v)].e;
      } else { // isRight(v)
        envAlpha = Math.max(plus(tree[siblingLeft(v)].env, eAlpha), envAlpha);
        eAlpha += tree[siblingLeft(v)].e;
      }
      v = parent(v);
    }

    return plus(envAlpha, eBeta);
  }

  IntVar getCapacity() {
    return c;
  }

  void setCapacity(IntVar capacity) {
    c = capacity;
  }

  ThetaLambdaNode leaf(int i) {
    return tree[leafIndex(i)];
  }

  private boolean isLeaf(int i) {
    int l =
        tree[i].index; // must use this since we make tree balanced and copy nodes up in the tree
    // sometimes
    return l >= treeSize - n && l < treeSize;
  }

  ThetaLambdaNode rootNode() {
    return tree[root()];
  }

  ThetaLambdaNode get(int i) {
    return tree[i];
  }

  @Override
  protected String treeName() {
    return "ThetaLambdaTree";
  }

  @Override
  protected String getNodeString(int i) {
    return tree[i].toString();
  }
}
