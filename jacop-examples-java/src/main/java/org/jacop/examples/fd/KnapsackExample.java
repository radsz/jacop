/*
 * Knapsack.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.examples.fd;

import java.util.ArrayList;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XgteqY;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * It shows the capabilities and usage of Knapsack constraint.
 *
 * <p>It models and solves a simple knapsack problem. There are two different models. The first one
 * uses quantity from 0 to n, where the second model is allowed to use only binary variables.
 *
 * <p>Each item is specified by its weight and profit. Find what objects should be put in the
 * knapsack to maximize the profit without exceeding the knapsack capacity.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class KnapsackExample extends ExampleFd {

  /** It stores the parameters of the main function to be used by the model functions. */
  public String[] args = new String[0];

  /**
   * It executes the two different models to find a solution to a knapsack problem. It is possible
   * to supply the knapsack problem through the parameters. The parameters are order as follows :
   * string denoting the capacity of the knapsack 4 strings denoting the item (weight, profit,
   * maximumQuantity, name) the number of strings total must be equal to 1+4*noOfItems.
   *
   * <p>If no arguments is provided or improper number of them the program will use internal
   * instance of the knapsack problem.
   *
   * @param args the capacity of the knapsack, 4 strings denoting the item (weight, profit,
   *     maximumQuantity, name), the number of strings total must be equal to 1+4*noOfItems.
   */
  static void main(String[] args) {

    KnapsackExample example = new KnapsackExample();

    example.args = args;

    example.model();

    if (example.searchOptimal()) {
      log.info("Solution(s) found");
    }

    example = new KnapsackExample();

    example.args = args;
    example.modelBasic();

    if (example.searchOptimal()) {
      log.info("Solution(s) found");
    }
  }

  /**
   * Parsed knapsack data for quantity-based models (model, modelNoKnapsackConstraint, modelBoth).
   */
  protected static final class KnapsackData {
    final int noItems;
    final int volume;
    final int[] weights;
    final int[] profits;
    final int[] maxs;
    final String[] names;

    KnapsackData(
        int noItems, int volume, int[] weights, int[] profits, int[] maxs, String[] names) {
      this.noItems = noItems;
      this.volume = volume;
      this.weights = weights;
      this.profits = profits;
      this.maxs = maxs;
      this.names = names;
    }
  }

  /** Parses args or returns default knapsack data for quantity-based models. */
  protected KnapsackData parseQuantityKnapsackData() {
    int noItems = 3;
    int volume = 9;
    int[] weights = {4, 3, 2};
    int[] profits = {15, 10, 7};
    String[] names = {"whisky", "perfumes", "cigarets"};

    int[] maxs = new int[noItems];
    for (int i = 0; i < noItems; i++) {
      maxs[i] = volume / weights[i];
    }

    if (args.length >= 5 && ((args.length - 1) % 4) == 0) {
      volume = Integer.parseInt(args[0]);
      noItems = (args.length - 1) / 4;
      weights = new int[noItems];
      profits = new int[noItems];
      maxs = new int[noItems];
      names = new String[noItems];
      for (int i = 1; i < args.length; ) {
        weights[(i - 1) / 4] = Integer.parseInt(args[i++]);
        profits[(i - 1) / 4] = Integer.parseInt(args[i++]);
        maxs[(i - 1) / 4] = Integer.parseInt(args[i++]);
        names[(i - 1) / 4] = args[i++];
      }
    }

    return new KnapsackData(noItems, volume, weights, profits, maxs, names);
  }

  /** Holder for quantity-based model variables. */
  protected static final class QuantityModelVars {
    final IntVar[] quantity;
    final IntVar weight;
    final IntVar profit;

    QuantityModelVars(IntVar[] quantity, IntVar weight, IntVar profit) {
      this.quantity = quantity;
      this.weight = weight;
      this.profit = profit;
    }
  }

  /**
   * Builds store, vars, quantity, weight, profit and cost; returns vars for model-specific
   * constraints.
   */
  protected QuantityModelVars buildQuantityBase(KnapsackData data) {
    store = new Store();
    vars = new ArrayList<>();

    IntVar[] quantity = new IntVar[data.noItems];
    for (int i = 0; i < quantity.length; i++) {
      quantity[i] = new IntVar(store, "Quantity_" + data.names[i], 0, data.maxs[i]);
      vars.add(quantity[i]);
    }

    IntVar profit = new IntVar(store, "Profit", 0, 1000000);
    IntVar weight = new IntVar(store, "Weight", 0, 1000000);

    store.impose(new XlteqC(weight, data.volume));

    IntVar profitNegation = new IntVar(store, "ProfitNegation", -100000, 0);
    store.impose(new XplusYeqC(profit, profitNegation, 0));
    cost = profitNegation;

    return new QuantityModelVars(quantity, weight, profit);
  }

  @Override
  public void model() {
    KnapsackData data = parseQuantityKnapsackData();
    QuantityModelVars v = buildQuantityBase(data);
    store.impose(
        Knapsack.builder()
            .profits(data.profits)
            .weights(data.weights)
            .quantity(v.quantity)
            .knapsackCapacity(v.weight)
            .knapsackProfit(v.profit)
            .build());
  }

  /** It does not use Knapsack constraint only SumWeight constraints. */
  public void modelNoKnapsackConstraint() {
    KnapsackData data = parseQuantityKnapsackData();
    QuantityModelVars v = buildQuantityBase(data);
    store.impose(new LinearInt(v.quantity, data.weights, "==", v.weight));
    store.impose(new LinearInt(v.quantity, data.profits, "==", v.profit));
  }

  /** Uses both Knapsack and LinearInt constraints. */
  public void modelBoth() {
    KnapsackData data = parseQuantityKnapsackData();
    QuantityModelVars v = buildQuantityBase(data);
    store.impose(new LinearInt(v.quantity, data.weights, "==", v.weight));
    store.impose(
        Knapsack.builder()
            .profits(data.profits)
            .weights(data.weights)
            .quantity(v.quantity)
            .knapsackCapacity(v.weight)
            .knapsackProfit(v.profit)
            .build());
    store.impose(new LinearInt(v.quantity, data.profits, "==", v.profit));
  }

  /** Computes total number of items from args (weight, profit, maxQty, name per group). */
  private static int countItemsFromArgs(String[] args) {
    int noItems = 0;
    for (int i = 3; i < args.length; i += 4) {
      noItems += Integer.parseInt(args[i]);
    }
    return noItems;
  }

  /**
   * Fills weights, profits, names from args; arrays must be allocated with length from
   * countItemsFromArgs.
   */
  private static void fillItemsFromArgs(
      String[] args, int[] weights, int[] profits, String[] names) {
    int currentItem = 0;
    for (int i = 1; i < args.length; i += 4) {
      for (int j = Integer.parseInt(args[i + 2]); j > 0; j--) {
        weights[currentItem] = Integer.parseInt(args[i]);
        profits[currentItem] = Integer.parseInt(args[i + 1]);
        names[currentItem] = args[i + 3] + "_" + j;
        currentItem++;
      }
    }
  }

  /**
   * It creates a model where quantity variable is allowed only to be between 0 and 1, so if the
   * original description allows n items n copies of that items must be created.
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
    int[] weights = {4, 4, 3, 3, 3, 2, 2, 2, 2};
    int[] profits = {15, 15, 10, 10, 10, 7, 7, 7, 7};
    String[] names = {
      "whisky_1",
      "whisky_2",
      "perfumes_1",
      "perfumes_2",
      "perfumes_3",
      "cigarets_1",
      "cigarets_2",
      "cigarets_3",
      "cigarets_4"
    };

    // It is possible to supply the program with volume size and items (weight, profit, maxQty,
    // name)
    if (args.length >= 5 && ((args.length - 1) % 4) == 0) {
      volume = Integer.parseInt(args[0]);
      noItems = countItemsFromArgs(args);
      weights = new int[noItems];
      profits = new int[noItems];
      names = new String[noItems];
      fillItemsFromArgs(args, weights, profits, names);
    }

    // Creating constraint store
    store = new Store();
    vars = new ArrayList<>();

    // I-th variable represents if i-th item is taken
    IntVar[] quantity = new IntVar[noItems];

    // Each quantity variable has a domain from 0 to 1
    for (int i = 0; i < quantity.length; i++) {
      quantity[i] = new IntVar(store, "Quantity_" + names[i], 0, 1);
      vars.add(quantity[i]);
    }

    IntVar profit = new IntVar(store, "Profit", 0, 1000000);
    IntVar weight = new IntVar(store, "Weight", 0, 1000000);

    store.impose(new LinearInt(quantity, weights, "==", weight));
    store.impose(new LinearInt(quantity, profits, "==", profit));

    store.impose(new XlteqC(weight, volume));

    // symmetry breaking
    // if item ith is not taken then jth neither
    // (assuming the same item characteristics)
    for (int i = 0; i < quantity.length; i++) {
      for (int j = i + 1; j < quantity.length; j++) {
        if (weights[i] == weights[j] && profits[i] == profits[j]) {
          store.impose(new XgteqY(quantity[i], quantity[j]));
        }
      }
    }

    IntVar profitNegation = new IntVar(store, "ProfitNegation", -100000, 0);

    store.impose(new XplusYeqC(profit, profitNegation, 0));

    cost = profitNegation;
  }
}
