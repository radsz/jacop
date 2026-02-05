/*
 * TreeLeaf.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Radoslaw Szymanek and Wadeck Follonier
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

package org.jacop.constraints.knapsack;

import lombok.Getter;
import org.jacop.core.IntVar;

/**
 * It contains information required by the leaf node of the item tree.
 *
 * @author Radoslaw Szymanek and Wadeck Follonier
 * @version 4.10
 */
@Getter
public final class TreeLeaf extends TreeNode {

  /** It specifies the finite domain variable denoting the allowed quantity of the item,. */
  public final IntVar quantity;

  /** It specifies the efficiency of the item in the leaf. */
  public final double efficiency;

  /** It stores the weight of one instance of the item stored in this leaf. */
  public final int weightOfOne;

  /** It store the profit of one instance of the item stored in this leaf. */
  public final int profitOfOne;

  /**
   * It specifies the maximal value of quantity variable after the last consistency check. It is
   * used to determine if the maximal value of the quantity variable has changed since the last
   * execution of the consistency function.
   */
  public int previousMaxQ;

  /**
   * It specifies the minimal value of quantity variable after the last consistency check. It is
   * used to determine if the minimal value of the quantity variable has changed since the last
   * execution of the consistency function.
   */
  public int previousMinQ;

  /**
   * It represents the offset from the minimal value. Slice of value 1 means that 1 item has been
   * already counted in capacity and profit of the knapsack and quantity variable should be offset
   * by one. Both min and max values will be reduced by one.
   */
  public int slice;

  /** It specifies the position in the tree. */
  public int positionInTheTree;

  /**
   * It creates a leaf in the tree of items.
   *
   * @param quantity finite domain variable specifying the quantity.
   * @param weight it specifies the weight of one instance of the item.
   * @param profit it specifies the profit of one instance of the item.
   * @param positionInTheTree it specifies the position in the tree.
   */
  public TreeLeaf(IntVar quantity, int weight, int profit, int positionInTheTree) {

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
   * Used to know the changes that occurred.
   *
   * @return If the minimum has changed
   */
  public boolean hasMinChanged() {
    return min() != previousMinQ;
  }

  /**
   * Used to know the changes that occurred.
   *
   * @return The last change of the minimum
   */
  public int lastIncreasedOfMin() {
    return min() - previousMinQ;
  }

  /**
   * Used to know the changes that occurred.
   *
   * @return If the maximum has changed
   */
  public boolean hasMaxChanged() {

    return max() != previousMaxQ;
  }

  @Override
  public int getWMax() {

    // max() function reflects the value of the slice.
    return max() * weightOfOne;
  }

  @Override
  public int getWSum() {

    // max() function reflects the value of the slice.
    return max() * weightOfOne;
  }

  @Override
  public int getPSum() {

    // max() function reflects the value of the slice.
    return max() * profitOfOne;
  }

  @Override
  public boolean isLeaf() {
    return true;
  }

  @Override
  public String toString() {

    return "{wmax: "
        + getWMax()
        + ", eff: "
        + efficiency
        + ", var: "
        + quantity
        + "(, slice: "
        + slice
        + ")["
        + min()
        + ".."
        + max()
        + "]}";
  }

  @Override
  public String nodeToString() {
    return toString();
  }

  /**
   * Only used in removeLevelLate(), update the internal value like previous and slice. It does not
   * updates anything else in the tree.
   *
   * @param tree it specifies the tree to which this leaf belongs too.
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
  public int min() {
    return quantity.min() - slice;
  }

  /**
   * @return The maximum value of the variable after slicing
   */
  public int max() {
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
