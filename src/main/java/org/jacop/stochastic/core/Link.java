package org.jacop.stochastic.core;

/**
 * Implements a Link of Bipartite Graphs.
 */
public class Link {

	/**
	 * Edge value.
	 */
	public int edge;
	
	/**
	 * Leaf value.
	 */
	public int leaf;
	
	/**
	 * This constructor creates a Link instance.
	 * @param edge : Edge value
	 * @param leaf : Leaf value
	 */
	public Link(int edge, int leaf) {
		
		this.edge = edge;
		this.leaf = leaf;
	}

    public String toString() {
        return "(" + edge + ", " + leaf + ")";

    }
}