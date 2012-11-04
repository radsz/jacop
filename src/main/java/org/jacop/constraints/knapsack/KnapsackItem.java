/**
 *  KnapsackItem.java 
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
 * 
 * This class stores information about items being considered by a Knapsack constraint. 
 * It is a holder for integer attributes like weight and profit, as well as finite domain 
 * variable denoting the quantity being taken. It also stores precomputed efficiency of the item. 
 * 
 * It implements comparable interface in such a away so that items can be sorted in decreasing 
 * efficiency. In case of equal efficiency then item which is heavier is preferred.
 * 
 * @author Radoslaw Szymanek and Wadeck Follonier
 *
 */

public final class KnapsackItem implements Comparable<KnapsackItem> {
	
	/**
	 * It is a finite domain variable specifying the possible quantity of that item. 
	 */
	public IntVar quantity;
	
	/**
	 * It specifies the weight of a single instance of this item. 
	 */
	public int weight;
	
	/**
	 * It specifies the profit of a single instance of this item.
	 */
	public int profit;
	
	/**
	 * It stores information about the item efficiency - profit/weight.
	 */
	public double efficiency;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"quantity", "weight", "profit"};

	/**
	 * It constructs an item. It requires information about weight and profit, 
	 * as well as finite domain variable denoting the quantity. It will compute 
	 * efficiency as well. 
	 * @param quantity - number of items it is possible to take.
	 * @param weight - weight of the single item.
	 * @param profit - profit due to one single item.
	 */
	public KnapsackItem(IntVar quantity, int weight, int profit) {
		super();
		if (weight <= 0)
			throw new IllegalArgumentException("Weight attribute has to be greater than 0.");
		if (profit <= 0)
			throw new IllegalArgumentException("Profit attribute has to be greater than 0.");
		this.quantity = quantity;
		this.weight = weight;
		this.profit = profit;
		this.efficiency = this.profit / (double) this.weight;
	}

	/**
	 * Method used in the sorting of the items, we use profit and weight to know
	 * the less efficient item without using division. This function returns 1 if 
	 * this item is less efficient than that item. This function returns -1 if
	 * this item is more efficient than that item. If both items are equally efficient
	 * then this function returns 1 if this item has smaller weight than that item.
	 * 
	 * In connection with Arrays.sort() it will produce items from most efficient to 
	 * least efficient breaking ties in the favor of the larger weight. 
	 */

	public int compareTo(KnapsackItem that) {
	
		long comparison = (long) weight * (long) that.profit - (long) profit * (long) that.weight;
		
		if (comparison == 0) {
			
			if (that.weight >= weight)
				return 1;
			else
				return -1;
			
		} else {
			
			if (comparison > 0)
				return 1;
			else
				return -1;
			
		}
	}

	/**
	 * t returns quantity variable associated with that item. 
	 * 
	 * @return quantity finite domain variable.
	 */
	
	public final IntVar getVariable() {
		return quantity;
	}

	
	/**
	 * It returns a profit of a single instance of that item. 
	 * 
	 * @return profit of a single instance of that item. 
	 */
	public final int getProfit() {
		return profit;
	}

	/**
	 * It returns a weight of a single instance of that item. 
	 * 
	 * @return weight of a single instance of that item.
	 */
	public final int getWeight() {
		return weight;
	}

	/**
	 * It returns an efficiency of that item. 
	 * 
	 * @return the efficiency of that item. 
	 * 
	 */
	public final double getEfficiency() {
		return efficiency;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer();
		result.append("item[ fdv: ").append(quantity.toString()).append(", weight: ").append(weight);
		result.append(", profit: ").append(profit).append(", efficiency: ").append(efficiency).append(" ]");

		return result.toString();
	}
	
}
