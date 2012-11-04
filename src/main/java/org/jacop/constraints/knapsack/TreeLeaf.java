/**
 *  TreeLeaf.java 
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

import org.jacop.core.IntVar;

/**
 * It contains information required by the leaf node of the item tree.
 * 
 * @author Radoslaw Szymanek and Wadeck Follonier
 *
 */

public final class TreeLeaf extends TreeNode {

	
	/**
	 * It specifies the finite domain variable denoting the allowed 
	 * quantity of the item, 
	 */
	final public IntVar quantity;
	
	/**
	 * It specifies the efficiency of the item in the leaf.
	 */
	final public double efficiency;
	
	/**
	 * It specifies the maximal value of quantity variable after the last 
	 * consistency check. It is used to determine if the maximal 
	 * value of the quantity variable has changed since the last 
	 * execution of the consistency function.  
	 */
	public int previousMaxQ;
	
	/**
	 * It specifies the minimal value of quantity variable after the last 
	 * consistency check. It is used to determine if the minimal
	 * value of the quantity variable has changed since the last 
	 * execution of the consistency function.  
	 */
	public int previousMinQ;

	/**
	 * It stores the weight of one instance of the item stored in this leaf.
	 */
	public final int weightOfOne;
	
	/**
	 * It store the profit of one instance of the item stored in this leaf.
	 */
	public final int profitOfOne;

	/**
	 * It represents the offset from the minimal value. Slice of value 1 
	 * means that 1 item has been already counted in capacity and profit 
	 * of the knapsack and quantity variable should be offset by one. Both
	 * min and max values will be reduced by one. 
	 */
	public int slice;

	/**
	 * It specifies the position in the tree.
	 */
	public int positionInTheTree;
	
	/**
	 * It creates a leaf in the tree of items.
	 * 
	 * @param quantity finite domain variable specifying the quantity. 
	 * @param weight it specifies the weight of one instance of the item.
	 * @param profit it specifies the profit of one instance of the item.
	 * @param positionInTheTree it specifies the position in the tree.
	 */

	public TreeLeaf(IntVar quantity, 
					int weight, 
					int profit, 
					int positionInTheTree) {
		
		super();

		this.quantity = quantity;
		this.previousMaxQ = quantity.max();
		this.previousMinQ = quantity.min();
		this.weightOfOne = weight;
		this.profitOfOne = profit;
		this.positionInTheTree = positionInTheTree;
		this.efficiency = profitOfOne / (double) weightOfOne;
		this.slice = 0;
	}

	/**
	 * @return The variable stored in this leaf
	 */
	public final IntVar getVariable() {
		return quantity;
	}

	/**
	 * @return The profit of one unit of the variable
	 */
	public int getProfitOfOne() {
		return profitOfOne;
	}

	/**
	 * @return The weight of one unit of the variable
	 */
	public int getWeightOfOne() {
		return weightOfOne;
	}

	/**
	 * Used to know the changes that occurred
	 * 
	 * @return If the minimum has changed
	 */
	final public boolean hasMinChanged() {
		return min() != previousMinQ;
	}

	/**
	 * Used to know the changes that occurred
	 * 
	 * @return The last change of the minimum
	 */
	final public int lastIncreasedOfMin() {
		return min() - previousMinQ;
	}

	/**
	 * Used to know the changes that occurred
	 * 
	 * @return If the maximum has changed
	 */
	final public boolean hasMaxChanged() {
		
		return max() != previousMaxQ;

	}

	@Override
	final public int getWMax() {
		
		// max() function reflects the value of the slice.
		return max() * weightOfOne;

	}

	@Override
	final public int getWSum() {
		
		// max() function reflects the value of the slice.
		return max() * weightOfOne;
		
	}

	@Override
	final public int getPSum() {

		// max() function reflects the value of the slice.
		return max() * profitOfOne;

	}

	@Override
	public final boolean isLeaf() {
		return true;
	}

	/**
	 * It returns computed beforehand 
	 * the efficiency of the item stored in this tree leaf. 
	 * 
	 * @return the efficiency of the item stored at this computer.
	 */
	public final double getEfficiency() {
		return efficiency;
	}

	
	@Override
	public final String toString() {
		
		StringBuffer result = new StringBuffer();
		
		result.append("{wmax: ").append( getWMax()).append( ", eff: " ).append( efficiency );
		result.append(", var: ").append( quantity ).append( "(, slice: " ).append( slice );
		result.append(")[").append( min() ).append("..").append( max() ).append("]}");
		
		return result.toString();
	
	}

	@Override
	public final String nodeToString() {
		return toString();
	}

	/**
	 * Only used in removeLevelLate(), update the internal value like previous
	 * and slice. It does not updates anything else in the tree.
	 * 
	 * @param tree it specifies the tree to which this leaf belongs too. 
	 * 
	 */
	public void updateInternalValues(Tree tree) {
				
		int delta = quantity.min() - slice;
		
		tree.alreadyObtainedProfit += delta * profitOfOne;
		tree.alreadyUsedCapacity += delta * weightOfOne;
		
		slice = quantity.min();
		previousMinQ = min();
		previousMaxQ = max();
				
	}

	/**
	 * @return The minimum value of the variable after slicing. 
	 */
	final public int min() {
		return quantity.min() - slice;
	}

	/**
	 * @return The maximum value of the variable after slicing
	 */
	final public int max() {
		return quantity.max() - slice;
	}

	@Override
	public void recomputeDown(Tree tree) {
		updateInternalValues(tree);
	}

	@Override
	public void recomputeUp(Tree tree) {
		
		updateInternalValues(tree);
		// It is possible to send null as information about the tree 
		// the internal node belongs to is not needed.
		parent.recomputeUp(null);

	}

}
