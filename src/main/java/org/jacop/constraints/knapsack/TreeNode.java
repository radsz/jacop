/**
 *  TreeNode.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Radoslaw Szymanek and Wadeck Follonier
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.jacop.constraints.knapsack;

/**
 * It contains information required by an internal node of the item tree.
 * 
 * @author Radoslaw Szymanek and Wadeck Follonier
 *
 */

public class TreeNode {

	/**
	 * It specifies the maximal weight of an item in the subtree rooted at this node.
	 * The consistency algorithm will know that it can skip the entire subtree if the 
	 * weight is not sufficiently large.
	 */
	private int wMax;
	
	/**
	 * It specifies the sum of the weight of all items in the subtree rooted at this node.
	 */
	private int wSum;
	
	/**
	 * It specifies the sum of the profit of all items in the subtree rooted at this node.
	 */
	private int pSum;
	
	/**
	 * It specifies the parent of this node. If it is equal to null then this node
	 * is the root of the whole item tree.
	 */
	public TreeNode parent;
	
	/**
	 * It specifies the left child. It can not be equal to null.
	 */
	public final TreeNode left;
	
	/**
	 * It specifies the right child. It can not be equal to null.
	 */
	public final TreeNode right;

	
	/**
	 * It specifies the left neighbor.
	 */
	public TreeNode leftNeighbor;
	
	/**
	 * It specifies the right neighbor. 
	 */
	public TreeNode rightNeighbor;
	
	/**
	 * The constructor used by tree leaves.
	 */
	public TreeNode() {
		this.left = null;
		this.right = null;
	}

	/**
	 * It constructs a node of the item tree.
	 * @param left left child
	 * @param right right child
	 */
	public TreeNode(TreeNode left, TreeNode right) {
		this.left = left;
		this.right = right;
		left.parent = this;
		right.parent = this;
		this.wSum = left.getWSum() + right.getWSum();
		this.pSum = left.getPSum() + right.getPSum();
		this.wMax = Math.max(left.getWMax(), right.getWMax());
	}

	/**
	 * It sets the left neighbor of this tree node.
	 * @param leftNeighbor left neighbor of this node.
	 */
	public void setLeftNeighbor(TreeNode leftNeighbor) {
		this.leftNeighbor = leftNeighbor;
	}
	

	/**
	 * It sets the right neighbor of this tree node.
	 * @param rightNeighbor right neighbor of this node.
	 */
	public void setRightNeighbor(TreeNode rightNeighbor) {
		this.rightNeighbor = rightNeighbor;
	}

	/**
	 * @return true if the node is a leaf, false otherwise.
	 */
	public boolean isLeaf() {
		return false;
	}

	/**
	 * It does not recompute the maximum of weights.
	 * 
	 * @return The previously computed maximum weight of its children
	 */
	public int getWMax() {
		return wMax;
	}

	/**
	 * It does not recompute sum of weights. 
	 * 
	 * @return The previously computed sum of weights of its children
	 */
	public int getWSum() {
		return wSum;

	}

	/**
	 * It does not recompute sum of profits.
	 * @return The previously computed sum of profits of its children
	 */
	public int getPSum() {
		return pSum;

	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer();
		
		result.append("[wmax: ").append(wMax).append(", wsum: ").append(wSum);
		result.append(", psum: ").append(pSum).append(";");
		result.append(left.toString()).append("^").append(right.toString());
		result.append("]");
		
		return result.toString();
	}

	/**
	 * This function is used to recompute the attributes of all nodes
	 * on the way to root from this node. It assumes that left and right
	 * subtree have a correct values for their attributes.
	 * 
	 * @param tree only added to be in agreement with the function template 
	 * for leaf which need information about tree it belongs to. 
	 */
	public void recomputeUp(Tree tree) {
		
		pSum = left.getPSum() + right.getPSum();
		wMax = Math.max(left.getWMax(), right.getWMax());
		wSum = left.getWSum() + right.getWSum();
		
		// recursion until we reach the root node.
		if (parent != null)
			parent.recomputeUp(tree);
	}

	/**
	 * This function recomputes the attributes of this node after
	 * recomputing the left and right subtree.
	 * 
	 * @param tree It is required by leaves so tree atributes like alreadyUsedCapacity are properly updated.
	 */
	public void recomputeDown(Tree tree) {
		
		left.recomputeDown(tree);
		right.recomputeDown(tree);
		
		pSum = left.getPSum() + right.getPSum();
		wSum = left.getWSum() + right.getWSum();
		wMax = Math.max(left.getWMax(), right.getWMax());
		
	}
	
	/**
	 * It generates description of the node only.
	 * @return the description containing values of all node internal attributes.
	 */
	public String nodeToString() {
		
	StringBuffer result = new StringBuffer();
		
		result.append("[wmax: ").append(wMax).append(", wsum: ").append(wSum);
		result.append(", psum: ").append(pSum).append(";");
		result.append("]");
		
		return result.toString();
		
	}
	
	
}
