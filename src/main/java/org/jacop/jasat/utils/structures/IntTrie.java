/*
 * IntTrie.java
 * <p>
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

package org.jacop.jasat.utils.structures;

import java.util.Set;


/**
 * A class that implements, (hopefully) efficiently, a Trie on integers. It is
 * parametrized by the type of the nodes to carry useful data.
 * implementation based on Trie (or Radix Tree, see
 * http://en.wikipedia.org/wiki/Radix_tree).
 * <p>
 * It can be used directly as a (simple) set.
 *
 * @param <N> the type of the nodes of the Trie
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */
public class IntTrie<N extends IntTrie.Node<N>> {

    // root of the Trie
    private final N root;

    // size of the Trie
    private int size = 0;

    /**
     * add i to the Trie
     *
     * @param i the int to add to the Trie
     * @return the node corresponding to i
     */
    public final N add(int i) {
        // is it >= 0 ?
        int j = i;
        boolean isPos = true;
        if (j < 0) {
            isPos = false;
            j = -j;
        }

        // go down the Trie
        N current = root;
        while (j != 0) {

            // least significant bit
            int lsb = j & 1;
            if (lsb == 0) {
                if (current.son0 == null)
                    current.son0 = current.getNew();
                current = current.son0;
            } else {
                if (current.son1 == null)
                    current.son1 = current.getNew();
                current = current.son1;
            }
            j = j >> 1;  // shift right
        }

        // we have arrived to the leaf node
        if (isPos) {
            if (!current.posMember)
                size++;
            current.posMember = true;
        } else {
            if (!current.negMember)
                size++;
            current.negMember = true;
        }
        return current;
    }

    /**
     * does the Trie contains i ?
     *
     * @param i the int
     * @return true if the Trie contains i, false otherwise
     */
    public final boolean contains(int i) {
        N iNode = getNode(i);
        if (iNode == null)
            return false;
        if (i >= 0)
            return iNode.posMember;
        else
            return iNode.negMember;
    }

    /**
     * get the node associated with i, or maybe the node that would be
     * associated with i if i was in the Trie (*optional* feature)
     *
     * @param i the int
     * @return the node associated with i if it exists, null otherwise
     */
    public final N getNode(int i) {
        // is it >= 0 ?
        int j = i;
        if (j < 0)
            j = -j;

        // go down the Trie
        N current = root;
        while (j != 0) {

            // least significant bit
            int lsb = j & 0x1;
            if (lsb == 0) {
                if (current.son0 == null)
                    return null;
                current = current.son0;
            } else {
                if (current.son1 == null)
                    return null;
                current = current.son1;
            }
            j = j >> 1;  // shift right
        }

        // we have arrived to the leaf node
        return current;
    }

    /**
     * @return the root node
     */
    public final N getRoot() {
        return root;
    }

    /**
     * remove the int i.
     *
     * @param i the int to remove from the Trie
     * @return true if i was in the Trie (and has been removed), false
     * if it was not
     */
    public final boolean remove(int i) {

        // special case for 0
        if (i == 0) {
            boolean answer = root.posMember;
            root.posMember = false;
            if (answer)
                size--;
            return answer;
        }

        // is it >= 0 ?
        int j = i;
        boolean isPos = true;
        if (j < 0) {
            isPos = false;
            j = -j;
        }

        // the last node which we must keep (because it contains something)
        N lastGoodNode = root;
        boolean lastBranch = false; // was it 0 or 1 ? (false is 0)

        // go down the Trie
        N current = root;
        while (j != 0) {

            // least significant bit
            int lsb = j & 1;
            if (lsb == 0) {
                if (current.son0 == null)
                    return false;
                if (current.posMember || current.negMember || current.son1 != null) {
                    lastGoodNode = current;
                    lastBranch = false; // record the '0'
                }
                current = current.son0;
            } else {
                if (current.son1 == null)
                    return false;
                if (current.posMember || current.negMember || current.son0 != null) {
                    lastGoodNode = current;
                    lastBranch = true; // record the '1'
                }
                current = current.son1;
            }
            j = j >> 1;  // shift right
        }

        // we are now at the node containing (maybe) j
        boolean answer = isPos ? current.posMember : current.negMember;
        if (isPos)
            current.posMember = false;
        else
            current.negMember = false;
        // is the node useless, now ?
        boolean useless = current.son0 == null && current.son1 == null && !(isPos ? current.negMember : current.posMember);

        // clear the nodes that became useless, if there are some
        if (useless) {
            if (current != lastGoodNode) {
                if (lastBranch)
                    lastGoodNode.son1 = null;
                else
                    lastGoodNode.son0 = null;
            }
        }

        // update size and return answer
        if (answer)
            size--;
        return answer;
    }


    /**
     * empty the Trie, removing all elements from it
     */
    public final void clear() {
        root.son0 = root.son1 = null;
        root.posMember = false;
        size = 0;
    }

    /**
     * @return true if and only if the trie does not contain anything
     */
    public final boolean isEmpty() {
        return size == 0;
    }

    /**
     * @return the number of elements in the Trie
     */
    public final int size() {
        return size;
    }

    /**
     * @return the set of values that the Trie contains (quite inefficient)
     */
    @SuppressWarnings("unused")
    public Set<Integer> values() {
        throw new UnsupportedOperationException();
    }

    /**
     * initializes the Trie with a root node
     *
     * @param root the root node.
     */
    public IntTrie(N root) {
        this.root = root;
    }


    /**
     * class of nodes of the Trie. One can subclass this class to add any
     * payload he wants to the nodes.
     *
     * @author simon
     */
    public static abstract class Node<E> {
        E son0;  // node with suffix "0"
        E son1;  // node with suffix "1"

        boolean posMember = false;  // is this node a leaf with sign +
        boolean negMember = false;  // is this node a leaf with sign -

        /**
         * allocate a new value of type E
         *
         * @return the value of type E
         */
        public abstract E getNew();
    }


    /**
     * The most simple node possible
     *
     * @author simon
     */
    public static final class SimpleNode extends Node<SimpleNode> {
        @Override public SimpleNode getNew() {
            return new SimpleNode();
        }
    }
}
