package org.jacop.jasat.utils.structures;

/**
 * A mix of a priority queue and a hashmap, specialized for ints
 * 
 * @author simon
 *
 */
@SuppressWarnings("unused") // TODO remove
public final class IntPriorityQueue {
	
	// O(1) access to the Node of any int in the PriorityQueue
	private final IntHashMap<Node> map =
		new IntHashMap<Node>();
	
	// the root of the priority queue
	private Node root = null;

	/**
	 * the priority of i is now the old priority (or 0) + the amount. The
	 * priority stays >= 0.
	 * @param i			the int of which we want to modify the priority
	 * @param amount	the amount by which we modify the priority
	 * @return	the new priority of i
	 */
	public int addPriority(int i, int amount) {
		// TODO
		return 0;
	}
	
	/**
	 * equivalent to addPriority(i, 1)
	 */
	public int percolateUp(int i) {
		// TODO
		return 0;
	}
	
	/**
	 * equivalent to addPriority(i, -1);
	 */
	public int percolateDown(int i) {
		// TODO
		return 0;
	}
	
	/**
	 * accesses the priority of i. If i had no priority, returns 0.
	 * @param i	the int
	 * @return	the priority of i
	 */
	public int getPriority(int i) {
		Node n = map.get(i);
		if (n == null)
			return 0;
		else
			return n.priority;
	}
	
	/**
	 * forget about i. Next call to getPriority(i) will be 0.
	 * @param i	the int to forget
	 */
	public void remove(int i) {
		Node n = map.get(i);
		if (n != null) {
			// is the left Son deeper than the right ?
			int leftIsDeeper = n.rightSon.depth <= n.leftSon.depth ? 1 : 0;
			// is n the left node of its parent ?
			Node parent = n.parentNode;
			int isLeft = parent.leftSon == n ? 2 : 0;
			assert isLeft == 2 || parent.rightSon == n;
			
			// TODO
		}
	}
	
	/**
	 * access the element with highest priority, or 0 if it is empty
	 */
	public int getTop() {
		// TODO
		return 0;
	}
	
	/**
	 * checks if the priority queue is empty
	 */
	public boolean isEmpty() {
		return root == null;
	}
	
	
	/**
	 * finds the rightmost node, at the last level of depth
	 * @return this node, or null
	 */
	private Node findLastNode() {
		if (root == null)
			return null;
		
		Node current = root;
		int depth = root.depth;
		// search down the tree
		while (depth > 0) {
			assert current.leftSon != null || current.rightSon != null;
			if (current.leftSon == null) {
				current = current.rightSon;
			} else if (current.rightSon == null) {
				current = current.leftSon;
			} else {
				// follow preferently the rigth node, but if the tree
				// is node of size 2^n the left node might lead to a higher depth
				current = current.leftSon.depth > current.rightSon.depth ?
						current.leftSon : current.rightSon;
			}
			depth --;
		}
		assert current.leftSon == null;
		assert current.rightSon == null;
		
		return current;
	}
	
	/**
	 * heapify the tree by swapping nodes (from the root) until the tree becomes
	 * a heap
	 */
	private final void percolateDown() {
		// TODO
	}
	
	/**
	 * balances the tree again so that the given node moves up (to be called
	 * when the current node has highest priority than its parent)
	 * @param n	the node
	 */
	private final void percolateUp(Node n) {
		// TODO
	}
	
	/**
	 * a node containing the data associated with each int
	 * @author simon
	 *
	 */
	final static class Node {
		public Node leftSon;	// left node in binary tree
		public Node rightSon;	// right tree in binary tree
		public Node parentNode; // the parent node of this node
		public int priority;	// current priority in the tree
		public int depth = 0;	// depth of the deepest leaf in this subtree;
	}
	
}
