/**
 *  Knapsack.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.examples.fd;

import java.util.ArrayList;

import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XgteqY;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * 
 * It shows the capabilities and usage of Knapsack constraint.
 * 
 * @author Radoslaw Szymanek
 * @version 4.2
 * 
 * It models and solves a simple knapsack problem. There 
 * are two different models. The first one uses quantity
 * from 0 to n, where the second model is allowed to use
 * only binary variables. 
 * 
 * Each item is specified by its weight and profit. Find
 * what objects should be put in the knapsack to maximize 
 * the profit without exceeding the knapsack capacity.
 * 
 */

public class KnapsackExample extends ExampleFD {

	/**
	 * It stores the parameters of the main function to be 
	 * used by the model functions.
	 */
	public String[] args = new String[0];
	
	@Override
	public void model() {

		int noItems = 3;
		int volume = 9;
		int[] weights = { 4, 3, 2 };
		int[] profits = { 15, 10, 7 };
		String[] names = { "whisky", "perfumes", "cigarets" };

		int[] maxs = new int[noItems];
		for (int i = 0; i < noItems; i++)
			maxs[i] = volume / weights[i];

		// It is possible to supply the program
		// with the volume size and items (weight, profit, maximum_quantity,
		// name )
		if (args.length >= 5 && ((args.length - 1) % 4) == 0) {
			volume = new Integer(args[0]);
			noItems = (args.length - 1) / 4;
			weights = new int[noItems];
			profits = new int[noItems];
			maxs = new int[noItems];
			names = new String[noItems];
			for (int i = 1; i < args.length;) {
				weights[(i - 1) / 4] = new Integer(args[i++]);
				profits[(i - 1) / 4] = new Integer(args[i++]);
				maxs[(i - 1) / 4] = new Integer(args[i++]);
				names[(i - 1) / 4] = args[i++];
			}
		}

		// Creating constraint store
		store = new Store();
		
		vars = new ArrayList<IntVar>();
		
		// I-th variable represents if i-th item is taken
		IntVar quantity[] = new IntVar[noItems];

		// Each quantity variable has a domain from 0 to max value
		for (int i = 0; i < quantity.length; i++) {
			quantity[i] = new IntVar(store, "Quantity_" + names[i], 0, maxs[i]);
			vars.add(quantity[i]);
		}
		
		IntVar profit = new IntVar(store, "Profit", 0, 1000000);
		IntVar weight = new IntVar(store, "Weight", 0, 1000000);

		//  Redundant constraints.
		//	store.impose(new SumWeight(quantity, weights, weight));
		//	store.impose(new SumWeight(quantity, profits, profit));

		store.impose(new Knapsack(profits, weights, quantity,
								  weight, profit));
		
		store.impose(new XlteqC(weight, volume));

		IntVar profitNegation = new IntVar(store, "ProfitNegation", -100000, 0);

		store.impose(new XplusYeqC(profit, profitNegation, 0));
		
		cost = profitNegation;
		
	}
	
	
	

	
	/**
	 * It does not use Knapsack constraint only SumWeight constraints.
	 * 
	 */
	public void modelNoKnapsackConstraint() {

		int noItems = 3;
		int volume = 9;
		int[] weights = { 4, 3, 2 };
		int[] profits = { 15, 10, 7 };
		String[] names = { "whisky", "perfumes", "cigarets" };

		int[] maxs = new int[noItems];
		for (int i = 0; i < noItems; i++)
			maxs[i] = volume / weights[i];

		// It is possible to supply the program
		// with the volume size and items (weight, profit, maximum_quantity,
		// name )
		if (args.length >= 5 && ((args.length - 1) % 4) == 0) {
			volume = new Integer(args[0]);
			noItems = (args.length - 1) / 4;
			weights = new int[noItems];
			profits = new int[noItems];
			maxs = new int[noItems];
			names = new String[noItems];
			for (int i = 1; i < args.length;) {
				weights[(i - 1) / 4] = new Integer(args[i++]);
				profits[(i - 1) / 4] = new Integer(args[i++]);
				maxs[(i - 1) / 4] = new Integer(args[i++]);
				names[(i - 1) / 4] = args[i++];
			}
		}

		// Creating constraint store
		store = new Store();
		
		vars = new ArrayList<IntVar>();
		
		// I-th variable represents if i-th item is taken
		IntVar quantity[] = new IntVar[noItems];

		// Each quantity variable has a domain from 0 to max value
		for (int i = 0; i < quantity.length; i++) {
			quantity[i] = new IntVar(store, "Quantity_" + names[i], 0, maxs[i]);
			vars.add(quantity[i]);
		}
		
		IntVar profit = new IntVar(store, "Profit", 0, 1000000);
		IntVar weight = new IntVar(store, "Weight", 0, 1000000);

		store.impose(new SumWeight(quantity, weights, weight));
		store.impose(new SumWeight(quantity, profits, profit));
		
		store.impose(new XlteqC(weight, volume));

		IntVar profitNegation = new IntVar(store, "ProfitNegation", -100000, 0);

		store.impose(new XplusYeqC(profit, profitNegation, 0));
		
		cost = profitNegation;
		
	}
	
	
	/**
	 * It does not use Knapsack constraint only SumWeight constraints.
	 * 
	 */
	public void modelBoth() {

		int noItems = 3;
		int volume = 9;
		int[] weights = { 4, 3, 2 };
		int[] profits = { 15, 10, 7 };
		String[] names = { "whisky", "perfumes", "cigarets" };

		int[] maxs = new int[noItems];
		for (int i = 0; i < noItems; i++)
			maxs[i] = volume / weights[i];

		// It is possible to supply the program
		// with the volume size and items (weight, profit, maximum_quantity,
		// name )
		if (args.length >= 5 && ((args.length - 1) % 4) == 0) {
			volume = new Integer(args[0]);
			noItems = (args.length - 1) / 4;
			weights = new int[noItems];
			profits = new int[noItems];
			maxs = new int[noItems];
			names = new String[noItems];
			for (int i = 1; i < args.length;) {
				weights[(i - 1) / 4] = new Integer(args[i++]);
				profits[(i - 1) / 4] = new Integer(args[i++]);
				maxs[(i - 1) / 4] = new Integer(args[i++]);
				names[(i - 1) / 4] = args[i++];
			}
		}

		// Creating constraint store
		store = new Store();
		
		vars = new ArrayList<IntVar>();
		
		// I-th variable represents if i-th item is taken
		IntVar quantity[] = new IntVar[noItems];

		// Each quantity variable has a domain from 0 to max value
		for (int i = 0; i < quantity.length; i++) {
			quantity[i] = new IntVar(store, "Quantity_" + names[i], 0, maxs[i]);
			vars.add(quantity[i]);
		}
		
		IntVar profit = new IntVar(store, "Profit", 0, 1000000);
		IntVar weight = new IntVar(store, "Weight", 0, 1000000);

		store.impose(new SumWeight(quantity, weights, weight));
		
		store.impose(new Knapsack(profits, weights, quantity,
				  weight, profit));

		store.impose(new SumWeight(quantity, profits, profit));

		store.impose(new XlteqC(weight, volume));

		IntVar profitNegation = new IntVar(store, "ProfitNegation", -100000, 0);

		store.impose(new XplusYeqC(profit, profitNegation, 0));
		
		cost = profitNegation;
		
	}

	
	
	/**
	 * It creates a model where quantity variable is allowed only to be 
	 * between 0 and 1, so if the original description allows n items
	 * n copies of that items must be created.
	 */
	public void modelBasic() {
		
		// Since volume/(whisky weight) = 2.25 then maximum
		// 2 whiskeys can be taken
		// Since volume/(perfume weight) = 3 then maximum
		// 3 perfumes can be taken
		// Since volume/(cigaret weight) = 4.5 then maximum
		// 4 cigarets can be taken
		// this gives 2+3+4=9 items in the model
		int volume = 9;
		int noItems = 9;
		int[] weights = { 4, 4, 3, 3, 3, 2, 2, 2, 2 };
		int[] profits = { 15, 15, 10, 10, 10, 7, 7, 7, 7 };
		String[] names = { "whisky_1", "whisky_2", "perfumes_1", "perfumes_2",
				"perfumes_3", "cigarets_1", "cigarets_2", "cigarets_3",
				"cigarets_4" };

		// It is possible to supply the program
		// with the volume size and items (weight, profit, maximumQuantity, name)
		if (args.length >= 5 && ((args.length - 1) % 4) == 0) {
			volume = new Integer(args[0]);
			noItems = 0;
			for (int i = 3; i < args.length; i += 4) {
				noItems += Integer.parseInt(args[i]);
			}
			weights = new int[noItems];
			profits = new int[noItems];
			names = new String[noItems];
			int currentItem = 0;
			for (int i = 1; i < args.length; i += 4) {
				for (int j = Integer.parseInt(args[i+2]); j > 0; j--) {
					weights[currentItem] = Integer.parseInt(args[i]);
					profits[currentItem] = Integer.parseInt(args[i+1]);
					names[currentItem] = args[i+3] + "_" + j;
					currentItem++;
				}
			}
		}

		// Creating constraint store
		store = new Store();
		vars = new ArrayList<IntVar>();
		
		// I-th variable represents if i-th item is taken
		IntVar quantity[] = new IntVar[noItems];

		// Each quantity variable has a domain from 0 to 1
		for (int i = 0; i < quantity.length; i++) {
			quantity[i] = new IntVar(store, "Quantity_" + names[i], 0, 1);
			vars.add(quantity[i]);
		}
		
		IntVar profit = new IntVar(store, "Profit", 0, 1000000);
		IntVar weight = new IntVar(store, "Weight", 0, 1000000);

		store.impose(new SumWeight(quantity, weights, weight));
		store.impose(new SumWeight(quantity, profits, profit));

		store.impose(new XlteqC(weight, volume));
		
		// symmetry breaking
		// if item ith is not taken then jth neither
		// (assuming the same item characteristics)
		for (int i = 0; i < quantity.length; i++)
			for (int j = i + 1; j < quantity.length; j++)
				if (weights[i] == weights[j] && profits[i] == profits[j])
					store.impose(new XgteqY(quantity[i], quantity[j]));

		IntVar profitNegation = new IntVar(store, "ProfitNegation", -100000, 0);

		store.impose(new XplusYeqC(profit, profitNegation, 0));		
		
		cost = profitNegation;
		
	}
	
	/**
	 * It executes the two different models to find a solution to a knapsack problem. 
	 * It is possible to supply the knapsack problem through the parameters.
	 * The parameters are order as follows :
	 * string denoting the capacity of the knapsack
	 * 4 strings denoting the item (weight, profit, maximumQuantity, name)
	 * the number of strings total must be equal to 1+4*noOfItems.
	 * 
	 * If no arguments is provided or improper number of them the program will use
	 * internal instance of the knapsack problem.
	 * 
	 * @param args
	 */
	public static void main(String args[]) {

		KnapsackExample example = new KnapsackExample();
		
		example.args = args;
		
		example.model();

		if (example.searchOptimal())
			System.out.println("Solution(s) found");
		
		example = new KnapsackExample();
		
		example.args = args;
		example.modelBasic();
		
		if (example.searchOptimal())
			System.out.println("Solution(s) found");
		
	}	
		
}
