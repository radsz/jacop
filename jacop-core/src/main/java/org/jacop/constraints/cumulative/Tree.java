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

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;

/*
 * Implements ThetaLambdaTree and operations on this tree for Cumulative constraint
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */

/*
 * Defines the basic data structure for cumulative constraint's edge-finding algorithm.
 */
abstract class Tree {

  // binary tree structure; number of nodes
  int treeSize;
  // number of leaves (tasks)
  int n;

  abstract void clearNode(int i);

  protected abstract String treeName();

  protected abstract String getNodeString(int i);

  void clearTree() {
    for (int i = 0; i < treeSize; i++) {
      clearNode(i);
    }
  }

  int root() {
    return 0;
  }

  boolean isRoot(int i) {
    return i == root();
  }

  int parent(int i) {
    return (i - 1) < 0 ? -1 : (i - 1) / 2;
  }

  int left(int i) {
    return 2 * i + 1;
  }

  int right(int i) {
    return 2 * i + 2;
  }

  int siblingLeft(int i) {
    return left(parent(i));
  }

  int siblingRight(int i) {
    return right(parent(i));
  }

  boolean isLeft(int i) {
    return i % 2 != 0;
  }

  boolean isRight(int i) {
    return !isLeft(i);
  }

  int leafIndex(int i) {
    return i - (treeSize - n);
  }

  boolean notExist(int i) {
    return i < 0 || i >= treeSize;
  }

  boolean exist(int i) {
    return !notExist(i);
  }

  long plus(long x, long y) {
    if (x == Long.MIN_VALUE) {
      return Long.MIN_VALUE;
    } else {
      return x + y;
    }
  }

  int plus(int x, int y) {
    if (x == Integer.MIN_VALUE) {
      return Integer.MIN_VALUE;
    } else {
      return x + y;
    }
  }

  public void printTree(String name) {

    try (PrintStream out =
        new PrintStream(new FileOutputStream(name + ".dot"), true, StandardCharsets.UTF_8)) {
      out.print(toGraph(name));
      // out.close(); not needed; auto close
    } catch (IOException _) {
      throw new RuntimeException("IO exception; ignored");
    }
  }

  public String toGraph(String name) {

    StringBuilder result = new StringBuilder();

    result.append("digraph ").append(treeName()).append(name);
    result.append(" {");
    result.append("graph [  fontsize = 12,");
    result.append("size = \"5,5\" ];\n");

    for (int i = 0; i < treeSize; i++) {
      result
          .append("node_")
          .append(i)
          .append(" [shape = box, label = \"")
          .append(getNodeString(i))
          .append("\"]\n");
    }

    result.append(treeToGraph(root()));

    result.append("label =\"\n\n").append(treeName()).append(name).append("\n\"");

    result.append("}");

    return result.toString();
  }

  StringBuffer treeToGraph(int i) {

    StringBuffer result = new StringBuffer();

    if (notExist(i)) {
      return result;
    } else {
      String s = "node_" + i + " -> "; // "[label = \""+ tree[i] +"\"] -> ";
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

    StringBuilder result = new StringBuilder();

    result.append(treeName()).append("\n");
    for (int i = 0; i < treeSize; i++) {
      result
          .append("Node ")
          .append(i)
          .append("\n============\n")
          .append(getNodeString(i))
          .append("\n============\n");
    }

    return result.toString();
  }
}
