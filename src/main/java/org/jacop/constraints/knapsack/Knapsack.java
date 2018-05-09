/*
 * Knapsack.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.constraints.knapsack;

import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.*;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.Stream;

/**
 * It specifies a knapsack constraint. This implementation was inspired
 * by the paper by Irit Katriel, Meinolf Sellmann, Eli Upfal,
 * Pascal Van Hentenryck: "Propagating Knapsack Constraints in Sublinear Time",
 * AAAI 2007: pp. 231-236.
 * <p>
 * Tha major extensions of that paper are the following. The quantity variables
 * do not have to be binary. The profit and capacity of the knapsacks do not
 * have to be integers. In both cases, the constraint accepts any finite
 * domain variable.
 * <p>
 * This implementation is based on the implementation obtained by Wadeck
 * Follonier during his work on a student semester project.
 * <p>
 * We would like to thank Meinolf Sellmann for his appreciation of our work
 * and useful comments.
 *
 * @author Radoslaw Szymanek and Wadeck Follonier
 * @version 4.5
 *
 */

public class Knapsack extends Constraint implements UsesQueueVariable, Stateful, SatisfiedPresent {

    private final static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies if any debugging information should be printed.
     */
    public static final boolean debugAll = false;

    /**
     * It specifies mapping from variables into the leaf of the knapsack tree.
     */
    private Map<IntVar, TreeLeaf> variableLeafMapping;

    /**
     * The current position of the critical item in the tree
     */
    private TimeStamp<Integer> positionOfCriticalItem;

    /**
     * It stores all the leaves of the knapsack tree in one array. The leaves
     * are sorted from the most efficient to the least efficient.
     */
    private TreeLeaf[] leaves;

    /**
     * It stores for each level the leaves which have changed at this level.
     * It is used by removeLevel function. There is a limit at which leaves
     * will not be added and the whole tree will be updated.
     */
    private Map<Integer, List<TreeLeaf>> hashForUpdate;

    /**
     * It specifies the limit after which the changed leaves are not
     * store and the remove level will simply recompute attributes
     * of all nodes in the knapsack tree. By default it is equal to
     * n/log(n), where n is the number of the items.
     */
    private int updateLimit;

    /**
     * It specifies if the constraint has already discovered to be unsatisfied
     * during the imposition stage.
     */

    private boolean impositionFailure = false;

    /**
     * This is a finite domain variable to specify the knapsack capacity.
     */
    private IntVar knapsackCapacity;

    /**
     * This is a finite domain variable to specify the knapsack profit.
     */
    private IntVar knapsackProfit;


    /**
     * It specifies the current level of the constraint store at which
     * the consistency function of this constraint is being executed.
     */
    public int currentLevel;

    /**
     * It specifies the position of the last changed item which has been
     * already been recomputed. It helps to avoid recomputation of the same
     * parts of the tree if consistency function of the knapsack constraint
     * is called multiple times within the same store level.
     */

    private int positionOfAlreadyUpdated;

    /**
     * It specifies if the knapsack tree requires an update.
     */
    private boolean needUpdate = true;

    /**
     * It specifies if the consistency function should execute.
     */
    private boolean needConsistency = true;

    /**
     * It specifies if the mandatory part of the consistency algorithm should be
     * executed.
     */
    private boolean needMandatory = true;

    /**
     * It specifies if the forbidden part of the consistency algortihm should be
     * executed.
     */
    private boolean needForbidden = true;

    /**
     * It specifies if the recomputation of the critical item should take place.
     */
    private boolean needCriticalUpdate = true;

    /**
     * It specifies if the constraint is executing the consistency function.
     */
    private boolean inConsistency = false;

    /**
     * The tree for the storing information about the maximalWeight,
     * sum of weights and sum of profits.
     */
    public Tree tree;

    /**
     * The array of items present in the knapsack constraint.
     */
    public KnapsackItem[] items;


    /**
     * It counts the number of time the consistency function has been executed.
     */
    private int countConsistency = 0;

    /**
     * It counts the number of times the queueVariable function has been executed.
     */
    private int countQueueVariable = 0;

    /**
     * It counts the number of time the removeLevel function has been executed.
     */
    private int countRemoveLevel = 0;


    /**
     * It specifies how many removeLevel functions must be executed before the information
     * about the constraint is being printed out.
     */
    private int REMOVE_INFO_FROM = 0;

    /**
     * It specifies how many queueVariable functions must be executed before the information
     * about the constraint is being printed out.
     */

    private int QUEUE_INFO_FROM = 0;

    /**
     * It specifies how many consistency functions must be executed before the information
     * about the constraint is being printed out.
     */

    private int CONSISTENCY_INFO_FROM = 0;


    /**
     * It constructs an knapsack constraint.
     *
     * @param items            list of items in knapsack with its weight, profit and quantity variable.
     * @param knapsackCapacity overall knapsack capacity.
     * @param knapsackProfit   overall profit obtained by the items in the knapsack.
     */
    public Knapsack(KnapsackItem[] items, IntVar knapsackCapacity, IntVar knapsackProfit) {

        checkInputForNullness(new String[] {"items", "knapsackCapacity", "knapsackProfit"},
            new Object[][] {items, {knapsackCapacity}, {knapsackProfit}});

        // it handles duplicates.
        commonInitialization(Arrays.stream(items).mapToInt(KnapsackItem::getProfit).toArray(),
            Arrays.stream(items).mapToInt(KnapsackItem::getWeight).toArray(),
            Arrays.stream(items).map(KnapsackItem::getVariable).toArray(IntVar[]::new), knapsackCapacity, knapsackProfit);

    }

    /**
     * It constructs the knapsack constraint.
     *
     * @param profits          the list of profits, each for the corresponding item no.
     * @param weights          the list of weights, each for the corresponding item no.
     * @param quantity         finite domain variable specifying allowed values for the vars.
     * @param knapsackCapacity finite domain variable specifying the capacity limit of the knapsack.
     * @param knapsackProfit   finite domain variable defining the profit
     */
    public Knapsack(int[] profits, int[] weights, IntVar[] quantity, IntVar knapsackCapacity, IntVar knapsackProfit) {

        checkInputForNullness(new String[] {"profits", "weights", "quantity", "knapsackCapacity", "knapsackProfit"},
            new Object[][] {{profits}, {weights}, quantity, {knapsackCapacity}, {knapsackProfit}});

        if (profits.length != weights.length)
            throw new IllegalArgumentException("Constraint Knapsack has profits and weights parameters of different length");

        if (profits.length != quantity.length)
            throw new IllegalArgumentException("Constraint Knapsack has profits and quantity parameters of different length");

        commonInitialization(profits, weights, quantity, knapsackCapacity, knapsackProfit);
    }

    private void commonInitialization(int[] profits, int[] weights, IntVar[] quantity, IntVar knapsackCapacity, IntVar knapsackProfit) {

        numberId = idNumber.incrementAndGet();
        queueIndex = 1;

		    /* We start to create an array of items */
        /* KKU- 2016/01/14, duplicated items are collected into a single item */
        LinkedHashMap<IntVar, KnapsackItem> itemPar = new LinkedHashMap<>();
        for (int i = 0; i < quantity.length; i++) {
            if (itemPar.get(quantity[i]) != null) {
                KnapsackItem ki = itemPar.get(quantity[i]);
                Integer nw = ki.getWeight() + weights[i];
                Integer np = ki.getProfit() + profits[i];
                itemPar.put(quantity[i], new KnapsackItem(quantity[i], nw, np));
            } else
                itemPar.put(quantity[i], new KnapsackItem(quantity[i], weights[i], profits[i]));
        }

        items = itemPar.values().toArray(new KnapsackItem[itemPar.size()]);
        this.knapsackCapacity = knapsackCapacity;
        this.knapsackProfit = knapsackProfit;
        this.updateLimit = (int) (quantity.length / (Math.log(quantity.length) / Math.log(2)));

        setScope(Stream.concat(Arrays.stream(quantity), Stream.of(knapsackCapacity, knapsackProfit)));

    }

    @Override public void removeLevel(int level) {
        // we do nothing here, the work is done in removeLevelLate()
    }

    @Override public void cleanAfterFailure() {
        inConsistency = false;
    }

    @Override public void removeLevelLate(int level) {

        countRemoveLevel++;

        if (debugAll) {

            if (countRemoveLevel >= REMOVE_INFO_FROM) {

                System.out.println("Removelevel for " + level + " is called.");
                System.out.println(displayQuantitiesInEfficiencyOrder());

            }

        }

        List<TreeLeaf> list = hashForUpdate.get(level);
		/* there was some change in this level */
        if (list != null) {
			/* use the array to update */
            if (list.size() > updateLimit) {
                tree.recompute();
                needCriticalUpdate = true;
            } else {
                tree.updateFromList(list, 0);
                needCriticalUpdate = true;
            }

			/* and then, we delete it */
            hashForUpdate.put(level, null);
        }

        tree.criticalLeaf.positionInTheTree = positionOfCriticalItem.value();

    }

    /**
     * It makes sure that no item has a possibility to use more than
     * available capacity.
     * <p>
     * quantity.max() * weight < remainingCapacity.
     *
     * @param store             the constraint store responsible for stroing the problem.
     * @param parent            the node from which the restriction
     *                          of items quantities takes place (usually the root).
     * @param availableCapacity it specifies how much left there is a knapsack company.
     */
    private void restrictItemQuantity(Store store, TreeNode parent, int availableCapacity) {

        if (parent.getWMax() > availableCapacity) {

            // This is abrupt change outside normal mandatory/forbidden algorithm so it may influence
            // those algorithms. It is treated as outside change.
            inConsistency = false;

            TreeNode current;

            { /* left part */
                current = parent.left;
                if (!current.isLeaf()) {
                    restrictItemQuantity(store, current, availableCapacity);
                } else if (current.getWMax() > availableCapacity) {

                    IntVar quantity = ((TreeLeaf) current).quantity;

                    assert (quantity.min() == ((TreeLeaf) current).slice) : "Quantity.min is not equal slice.";

                    quantity.domain.inMax(store.level, quantity,
                        quantity.min() + (int) Math.floor(availableCapacity / (double) ((TreeLeaf) current).weightOfOne));
                }
            }

            { /* right part */
                current = parent.right;
                if (!current.isLeaf()) {
                    restrictItemQuantity(store, current, availableCapacity);
                } else if (current.getWMax() > availableCapacity) {

                    TreeLeaf leaf = (TreeLeaf) current;

                    int maxNoOfAllowed = (int) Math.floor(availableCapacity / (double) leaf.getWeightOfOne());

                    IntVar quantity = leaf.quantity;

                    assert (quantity.min() == leaf.slice) : "Quantity.min is not equal slice.";

                    quantity.domain.inMax(currentLevel, quantity, quantity.min() + maxNoOfAllowed);

                    needUpdate = true;
                }
            }

            inConsistency = true;

        }


    }

    /**
     * It updates the knapsack tree to reflect all the changes which
     * has happen since the last execution of the consistency function.
     * It will in particular update information about already obtained
     * profit as well as already used capacity. The domain of knapsack profit
     * or capacity variable may be reduced.
     */
    private void blockUpdate() {

        // It first updates the tree data structure.
        if (needUpdate) {
            needUpdate = false;

            List<TreeLeaf> list = hashForUpdate.get(currentLevel);
            if (list != null) {
                // there were too many updates to use incremental recomputation
                if (list.size() > updateLimit) {
                    tree.recompute();
                    needCriticalUpdate = true;
                } else {
                    // there were few updates so each change is propagated up to the root.
                    tree.updateFromList(list, positionOfAlreadyUpdated);
                    positionOfAlreadyUpdated = list.size();
                    needCriticalUpdate = true;
                }
            }
        }

        // It computes based on the minimum required profit a minimum required weight to get that profit.
        if (knapsackProfit.min() > tree.alreadyObtainedProfit) {
            int minWeight = tree.computeMinWeight(knapsackProfit.min() - tree.alreadyObtainedProfit);

            if (knapsackCapacity.min() < minWeight)
                knapsackCapacity.domain.inMin(currentLevel, knapsackCapacity, minWeight);

        }

        // It makes sure that knapsack capacity is within limits of already used capacity and the maximal
        // remaining capacity which can be used.
        knapsackCapacity.domain
            .in(currentLevel, knapsackCapacity, tree.alreadyUsedCapacity, tree.alreadyUsedCapacity + tree.root.getWSum());


        if (debugAll)
            System.out.println("Capacity after potential update : " + knapsackCapacity);


        // It computes based on the minimum required capacity the minimum possible profit obtained if
        // that capacity is being used.
        if (knapsackCapacity.min() > tree.alreadyUsedCapacity) {
            int minProfit = tree.computeMinProfit(knapsackCapacity.min() - tree.alreadyUsedCapacity);

            if (knapsackProfit.min() < minProfit)
                knapsackProfit.domain.inMin(currentLevel, knapsackProfit, minProfit);
        }


        if (needCriticalUpdate) {
            // If there was an update which can shift critical item then critical item is recomputed.
            needCriticalUpdate = false;
            tree.updateCritical(knapsackCapacity.max() - tree.alreadyUsedCapacity);
            positionOfCriticalItem.update(tree.criticalLeaf.positionInTheTree);
        }

        // It computes the range for profit given the fact that we use the remaining weight optimally in non-fractional fashion.
        knapsackProfit.domain
            .in(currentLevel, knapsackProfit, tree.alreadyObtainedProfit, tree.alreadyObtainedProfit + (int) Math.ceil(tree.optimalProfit));

        if (debugAll)
            System.out.println("Profit after potential update : " + knapsackProfit);

    }

    @Override public void consistency(Store store) {

        // it is possible that there changes to variables which have no chance to cause any pruning.
        // it is already the case that constraint is not even notified of ANY pruning events.
        if (!needConsistency)
            return;

        if (impositionFailure)
            throw Store.failException;

        if (debugAll)
            System.out.println("Entering consistency " + this);

        currentLevel = store.level;
        countConsistency++;
        inConsistency = true;
        needUpdate = true;

        blockUpdate();

        if (debugAll) {
            if (countConsistency >= CONSISTENCY_INFO_FROM)
                System.out.println(displayQuantitiesInEfficiencyOrder());
        }

        assert (sliceInvariant());

        if (debugAll)
            System.out.println("Tree root \n" + tree.root);

        // it checks if not too many items exceeding the capacity constraints
        // have been put in knapsack.

        assert (checkInvariants());

        //@TODO possibly redundant check, going from the root.
        restrictItemQuantity(store, tree.root, knapsackCapacity.max() - tree.alreadyUsedCapacity);

        if (needUpdate) {
            blockUpdate();
            assert (sliceInvariant());
        }

        if (debugAll)
            System.out.println("After single item restrictions " + this);

        if (debugAll)
            System.out.println("Tree root \n" + tree.root);

        assert (checkInvariants());

		/* compute mandatory items using jump */
        if (needMandatory)
            computeMandatory();

        blockUpdate();

        assert (checkInvariants());
        assert (sliceInvariant());
		
		/* compute forbidden items using jump */
        if (needForbidden)
            computeForbidden();

        blockUpdate();
        assert (checkInvariants());

        needConsistency = false;
        needUpdate = false;
        needCriticalUpdate = false;
        needMandatory = false;
        needForbidden = false;

        if (debugAll) {
            if (countConsistency >= CONSISTENCY_INFO_FROM)
                System.out.println(displayQuantitiesInEfficiencyOrder());
        }

        inConsistency = false;

    }

    /**
     * It searches through a subset of right items to find the ones which
     * can not be fully included without violating the profit requirement
     * in the knapsack constraint.
     */
    private void computeForbidden() {

        tree.initializeComputeForbidden();

        TreeLeaf leaf = tree.getLast();

        int criticalLeafPosition = tree.criticalLeaf.positionInTheTree;

        if (leaf.getWMax() == 0)
            leaf = tree.findPreviousLeafAtLeastOfWeight(leaf, tree.currentWeight);

        if (leaf == null)
            return;

        // Perform forbidden reasoning only on the right items.
        if (leaf.positionInTheTree <= criticalLeafPosition)
            return;

        // double profitSlack = (int) Math.ceil( tree.optimalProfit ) +
        //				  tree.alreadyObtainedProfit - knapsackProfit.min();
        // @TODO, check that lack of safe rounding (ceil) is not a problem
        // rounding errors may suggest that there is too little slack for an item.
        double profitSlack = tree.optimalProfit + tree.alreadyObtainedProfit - knapsackProfit.min();


        while (true) {

            int intrusionWeight = tree.computeIntrusionWeight(leaf.weightOfOne, leaf.max(), leaf.profitOfOne, leaf.efficiency, profitSlack);

            int itemMaxWeight = leaf.max() * leaf.weightOfOne;

            if (intrusionWeight < itemMaxWeight) {

                int forbiddenQuantity = (int) Math.ceil((itemMaxWeight - intrusionWeight) / (double) leaf.weightOfOne);

                IntVar quantity = leaf.getVariable();
                quantity.domain.inMax(currentLevel, quantity, quantity.max() - forbiddenQuantity);

                needUpdate = true;
            }

            if (debugAll)
                System.out.println("Forbidden check for " + leaf + " finished. Intrusion weight = " + intrusionWeight);

            leaf = tree.findPreviousLeafAtLeastOfWeight(leaf, tree.currentWeight);

            if (leaf == null)
                break;

            // Perform forbidden reasoning only on the right items.
            if (leaf.positionInTheTree <= criticalLeafPosition)
                break;

        }

    }

    /**
     * It computes the mandatory part of the knapsack pruning.
     */
    private void computeMandatory() {

        tree.initializeComputeMandatory();

        int criticalLeafPosition = tree.criticalLeaf.positionInTheTree;

        TreeLeaf leaf = tree.getFirst();

        if (leaf.getWMax() == 0)
            leaf = tree.findNextLeafAtLeastOfWeight(leaf, tree.currentWeight);

        if (leaf == null)
            return;

        // Perform mandatory reasoning only on the left items.
        if (leaf.positionInTheTree >= criticalLeafPosition)
            return;

        // double profitSlack = (int) Math.ceil( tree.optimalProfit ) +
        //				  tree.alreadyObtainedProfit - knapsackProfit.min();
        // @todo Test, that there is no rounding errors due to using double for
        // profitSlack and not safe ceil(profitSlack).
        double profitSlack = tree.optimalProfit + tree.alreadyObtainedProfit - knapsackProfit.min();

        while (true) {

            int replacableWeight =
                tree.computeReplacableWeight(leaf.weightOfOne, leaf.max(), leaf.profitOfOne, leaf.efficiency, profitSlack);

            int itemMaxWeight = leaf.max() * leaf.weightOfOne;

            if (replacableWeight < itemMaxWeight) {

                int mandatoryWeight = itemMaxWeight - replacableWeight;
                int mandatoryQuantity = (int) Math.ceil(mandatoryWeight / (double) leaf.weightOfOne);

                IntVar quantity = leaf.getVariable();
                quantity.domain.inMin(currentLevel, quantity, quantity.min() + mandatoryQuantity);

                needUpdate = true;
            }

            if (debugAll)
                System.out.println("Mandatory check for " + leaf + " finished. MaxWeight = " + replacableWeight);

            leaf = tree.findNextLeafAtLeastOfWeight(leaf, tree.currentWeight);

            if (leaf == null)
                break;

            // Perform mandatory reasoning only on the left items.
            if (leaf.positionInTheTree >= criticalLeafPosition)
                break;

        }


    }

    @Override public void impose(Store store) {

        store.registerRemoveLevelLateListener(this);

        hashForUpdate = new HashMap<>();

        /* We sort it with a sorting method */
        Arrays.sort(items);

        /*
         * We create the tree from the items and initialize the positionsInTree
         */

        IntVar zero = new IntVar(store, 0, 0);

        leaves = new TreeLeaf[items.length];

        variableLeafMapping = Var.createEmptyPositioning();

        tree = new Tree(items, variableLeafMapping, leaves, zero);

        if (knapsackCapacity.max() >= tree.alreadyUsedCapacity) {
            tree.updateCritical(knapsackCapacity.max() - tree.alreadyUsedCapacity);
            positionOfCriticalItem = new TimeStamp<>(store, tree.criticalLeaf.positionInTheTree);
        } else
            impositionFailure = true;

        if (tree.root.getPSum() + tree.alreadyObtainedProfit < knapsackProfit.min())
            impositionFailure = true;

        if (tree.root.getWSum() + tree.alreadyUsedCapacity < knapsackCapacity.min())
            impositionFailure = true;

        if (debugAll) {

            if (!impositionFailure)
                System.out.println("The impose function is completed. ");
            else
                System.out.println("The impose function has already detected inconsistency.");

            System.out.println(this);
            System.out.println(tree.toString());
        }

        super.impose(store);

    }

    @Override public void queueVariable(int level, Var v) {

        countQueueVariable++;

        if (debugAll) {
            if (countQueueVariable >= QUEUE_INFO_FROM) {

                System.out.println("queueVariable is executed for the " + countQueueVariable + "-th time");
                System.out.println(displayQuantitiesInEfficiencyOrder());

            }
        }

        if (v == knapsackCapacity || v == knapsackProfit) {

            if (inConsistency)
                return;

            needConsistency = true;
            needForbidden = true;
            needMandatory = true;
            needUpdate = true;
            needCriticalUpdate = true;

            return;
        }

        final TreeLeaf leafForV = variableLeafMapping.get(v);

        final boolean maxBoundHasChanged = leafForV.hasMaxChanged();
        final boolean minBoundHasChanged = leafForV.hasMinChanged();
		
		    /* at least one bound has changed */
        if (maxBoundHasChanged || minBoundHasChanged) {

			      /* we test if a list exist and if it is different from null */
            List<TreeLeaf> list;
            if ((list = hashForUpdate.get(level)) == null) {
                list = new ArrayList<>();
                hashForUpdate.put(level, list);
                positionOfAlreadyUpdated = 0;
            }

            if (list.size() > updateLimit) {
				        /* we don't add, we recompute */
            } else {
                list.add(leafForV);
            }

            needUpdate = true;

        }

        if (inConsistency)
            return;

        //@TODO What if item changed is critical, make sure the code is correct in that case.

        final boolean rightToCrit = leafForV.positionInTheTree > positionOfCriticalItem.value();

        final boolean leftToCrit = leafForV.positionInTheTree < positionOfCriticalItem.value();

        assert (!(leftToCrit && rightToCrit)) : "Error, a leaf cannot be right and left to the critical ";

		    /* we look if there is some changed to do */
        if (maxBoundHasChanged) {
			      /* for max decreased of mandatory items */
            if (leftToCrit) {
                needConsistency = true;
                needMandatory = true;
                needForbidden = true;
                needCriticalUpdate = true;
            }
			      /* for max decreased of forbidden items */
            else {
                needConsistency = true;
                if (leafForV.positionInTheTree <= tree.criticalRightLeaf)
                    needMandatory = true;
            }
        }

        if (minBoundHasChanged) {
			  /* for min increased of mandatory items */
            if (leftToCrit) {
                needConsistency = true;
                if (leafForV.positionInTheTree >= tree.criticalLeftLeaf)
                    needForbidden = true;
            }
			      /* for min increased of forbidden items */
            else {
                needConsistency = true;
                needMandatory = true;
                needForbidden = true;
                needCriticalUpdate = true;
            }
        }

    }

    @Override public int numberArgs() {
        return items.length + 2;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public boolean satisfied() {

        if (!knapsackProfit.singleton())
            return false;

        if (!knapsackCapacity.singleton())
            return false;

        if (tree.root.getWSum() != 0)
            return false;

        if (tree.alreadyObtainedProfit != knapsackProfit.value())
            return false;

        if (tree.alreadyUsedCapacity != knapsackCapacity.value())
            return false;

        return true;
    }



    @Override public String toString() {

        StringBuilder result = new StringBuilder();

        result.append("Knapsack[ [");
        for (int i = 0; i < items.length; i++) {
            result.append(items[i].toString());
            if (i < items.length - 1)
                result.append(",\n");
        }
        result.append("], \nCapacity: ").append(knapsackCapacity);
        result.append(", \nProfit: ").append(knapsackProfit);
        result.append("]\n");

        return result.toString();

    }


    /**
     * It checks that the minimal values of items are contributing
     * correctly towards tree already obtained profit, as well as
     * already used capacity.
     *
     * @return true to specify that invariants are maintained correctly.
     */
    private boolean sliceInvariant() {

        int alreadyObtainedProfit = 0, alreadyUsedCapacity = 0;

        for (TreeLeaf leave : leaves)
            if (leave.slice > 0) {
                alreadyObtainedProfit += leave.slice * leave.getProfitOfOne();
                alreadyUsedCapacity += leave.slice * leave.getWeightOfOne();
            }

        assert (alreadyObtainedProfit == tree.alreadyObtainedProfit) : "Already obtained profit is not correctly maintained.";

        assert (alreadyUsedCapacity == tree.alreadyUsedCapacity) : "Already used capacity is not correctly maintained.";

        return true;

    }

    private String displayQuantitiesInEfficiencyOrder() {

        StringBuilder result = new StringBuilder();

        result.append("[ ");

        for (KnapsackItem item : items)
            result.append(item.getVariable().domain).append(" ");

        result.append("]");

        return result.toString();

    }

    /**
     * It verifies that leaves within tree have properly reflected slice variables
     * within the items.
     */
    private boolean checkInvariants() {

        for (TreeLeaf leaf : leaves)
            assert (leaf.slice == leaf.quantity.min()) : "Slice variable has not been adjusted to leaf quantity" + leaf.toString();

        int overallProfit = 0;
        int overallCapacity = 0;
        int maxLeafCapacity = 0;

        for (TreeLeaf leaf : leaves) {
            overallProfit += leaf.getPSum();
            overallCapacity += leaf.getWSum();
            maxLeafCapacity = Math.max(maxLeafCapacity, leaf.getWMax());
        }

        assert (overallProfit == tree.root.getPSum()) : "Sum of profits for the tree does not reflect the quantity variables state";
        assert (overallCapacity == tree.root.getWSum()) : "Sum of capacities for the tree does not reflect the quantity variables state";
        assert (maxLeafCapacity == tree.root.getWMax()) : "Max of capacities for the tree does not reflect the quantity variables state";

        return true;
    }

}
