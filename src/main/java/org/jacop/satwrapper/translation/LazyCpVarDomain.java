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
 * @author simon
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
