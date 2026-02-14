/*
 * ThetaTree.java
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

/*
 * Implements ThetaTree and operations on this tree for Cumulative constraint
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */

/*
 * Defines the basic data structure for cumulative constraint's edge-finding algorithm.
 */
class ThetaTree extends Tree {

  private final ThetaNode empty = new ThetaNode();
  // number of leaves (tasks)
  int leafCount;
  // array that keeps all nodes of the balanced binary tree and organizes the tree structure
  private ThetaNode[] tree;
  // list of ordered tasks
  private TaskView[] orderedTasks;

  public ThetaTree() {}

  public void buildTree(TaskView[] task) {
    leafCount = task.length;
    treeSize =
        (int) Math.pow(2, Math.round(Math.ceil(Math.log(leafCount) / Math.log(2)))) + leafCount - 1;
    tree = new ThetaNode[treeSize];

    orderedTasks = task;

    for (int i = treeSize - 1; i >= treeSize - leafCount; i--) {
      computeLeaveVals(i);
    }
    for (int i = treeSize - leafCount - 1; i >= 0; i--) {
      computeNodeVals(i);
    }
  }

  public void initTree(TaskView[] task) {
    leafCount = task.length;
    treeSize =
        (int) Math.pow(2, Math.round(Math.ceil(Math.log(leafCount) / Math.log(2)))) + leafCount - 1;
    tree = new ThetaNode[treeSize];

    orderedTasks = task;

    for (int i = treeSize - 1; i >= treeSize - leafCount; i--) {
      addLeave(i);
    }
    for (int i = treeSize - leafCount - 1; i >= 0; i--) {
      addNode(i);
    }
  }

  private void addLeave(int i) {
    ThetaNode node = new ThetaNode();
    tree[i] = node;
    node.index = i;

    int t = i - (treeSize - leafCount); // in our case we pass list of ordered tasks already
    node.task = orderedTasks[t];
    orderedTasks[t].treeIndex = i;

    node.p = 0;
    node.ect = Integer.MIN_VALUE;

    node.pT = orderedTasks[t].dur().min();
    node.ectT = node.task.ect();
  }

  void computeLeaveVals(int i) {
    tree[i] = new ThetaNode();
    tree[i].index = i;

    addToThetaInit(i);
  }

  void addToThetaInit(int i) {
    int t = i - (treeSize - leafCount); // in our case we pass list of ordered tasks already
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

      node.p = l.p + r.p;
      node.ect = Math.max(plus(l.ect, r.p), r.ect);
    }
  }

  private void addNode(int i) {

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

  private void computeNode(int i) {
    computeNodeVals(i);
  }

  void clearNode(int i) {

    tree[i].p = 0;
    tree[i].ect = Integer.MIN_VALUE;
  }

  void clearTree() {
    for (int i = 0; i < treeSize; i++) {
      clearNode(i);
    }
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

    updateTree(parent(i));
  }

  private void disableNode(int i) {
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

  private int leaveIndex(int i) {
    return i - (treeSize - leafCount);
  }

  ThetaNode leaf(int i) {
    return tree[leaveIndex(i)];
  }

  boolean isLeaf(int i) {
    int l = tree[i].index;
    return l >= treeSize - leafCount && l < treeSize;
  }

  ThetaNode rootNode() {
    return tree[root()];
  }

  ThetaNode get(int i) {
    return tree[i];
  }

  @Override
  protected String treeName() {
    return "ThetaTree";
  }

  @Override
  protected String getNodeString(int i) {
    return tree[i].toString();
  }
}
