/*
 * LazyCpVarDomain.java
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

package org.jacop.satwrapper.translation;

import org.jacop.core.IntVar;
import org.jacop.satwrapper.SatWrapper;

/*
 * TODO : code this correctly and test
 */


/**
 * double linked lazy list, to store boolean variables that represent a range
 * of values for a variable
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */
@Deprecated  // TODO : implement it completely
public final class LazyCpVarDomain<E extends IntVar> extends SatCPBridge {

    // pointers to the leftmost and rightmost variables of the range
    public ListNode left;
    public ListNode right;

    private ListNode minNode;
    private ListNode maxNode;

    // the special clauses database of the wrapper
    @SuppressWarnings("unused") private DomainClausesDatabase database;


    @Override public int cpValueToBoolVar(int value, boolean isEquality) {
        assert value >= minNode.value;
        assert value <= maxNode.value;

        // TODO perform some search (sorted by value list)
        return 0;
    }

    @Override public int boolVarToCpValue(int literal) {
        // TODO Auto-generated method stub
        return 0;
    }

    @Override public boolean isEqualityBoolVar(int literal) {
        // TODO Auto-generated method stub
        return false;
    }

    @Override public void setDomain(int minValue, int maxValue) {
        super.setDomain(minValue, maxValue);

        // first node of the list
        minNode = new ListNode();
        minNode.left = minNode.right = null;
        minNode.value = minValue;
        minNode.variable = wrapper.core.getFreshVariable();

        // last node of the list
        maxNode = new ListNode();
        maxNode.left = maxNode.right = null;
        maxNode.value = maxValue;
        maxNode.variable = wrapper.core.getFreshVariable();

        // current pointers to nodes
        left = minNode;
        right = maxNode;
    }

    @Override public void propagate(int literal) {
        // TODO Auto-generated method stub
    /*
		 * TODO : lazy propagation (only propagate literals that are generated)
		 */
    }

    @Override public boolean isTranslated() {
        return false;
    }

    /**
     * creates the var list
     *
     * @param variable the variable this list represents
     */
    public LazyCpVarDomain(IntVar variable) {
        super(variable);
    }



    @Override public void initialize(SatWrapper wrapper) {
        // the wrapper must be a SmartSatWrapper
        this.wrapper = wrapper;
        assert wrapper.domainDatabase != null : "DomainClausesDatabase is needed";
        this.database = wrapper.domainDatabase;
    }



    /**
     * a node of the double linked list
     *
     * @author simon
     */
    @SuppressWarnings("unused") private final static class ListNode {

        public ListNode left;
        public ListNode right;

        // the boolean variable of this list node
        public int variable;

        // the CP variable value associated with this node
        public int value;

        // TODO : more payload ?
        // TODO : a single node should carry a range rather than a single value
    }
}
