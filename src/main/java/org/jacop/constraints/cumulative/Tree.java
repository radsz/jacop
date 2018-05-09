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

/**
 * Implements ThetaLambdaTree and operations on this tree for Cumulative constraint
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
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

    void clearTree() {
        for (int i = 0; i < treeSize; i++)
            clearNode(i);
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
        if (x == Long.MIN_VALUE) 
            return Long.MIN_VALUE;
        else
            return x + y;
    }

    int plus(int x, int y) {
        if (x == Integer.MIN_VALUE) {
            return Integer.MIN_VALUE;
	}
        else
            return x + y;
    }

}
