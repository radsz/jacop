/*
 * Linear.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.floats.constraints.linear;

import java.io.Serializable;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.DoubleStream;
import java.util.stream.Stream;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;
import org.jacop.floats.core.FloatDomain;
import org.jacop.floats.core.FloatInterval;
import org.jacop.floats.core.FloatVar;

/**
 * Linear constraint implements the weighted summation over several Variable's . It provides the
 * weighted sum from all Variable's on the list. The weights must be positive integers.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
@SuppressWarnings("serial")
public class Linear extends PrimitiveConstraint implements UsesQueueVariable {

  /** Defines relations. */
  public static final byte EQ = 0;

  public static final byte LT = 1;
  public static final byte LE = 2;
  public static final byte NE = 3;
  public static final byte GT = 4;
  public static final byte GE = 5;

  /** Defines negated relations. */
  static final byte[] NEG_REL = {
    NE, // EQ=0,
    GE, // LT=1,
    GT, // LE=2,
    EQ, // NE=3,
    LE, // GT=4,
    LT // GE=5;
  };

  static final AtomicInteger idNumber = new AtomicInteger(0);
  final Map<FloatVar, VariableNode> varMap = Var.createEmptyPositioning();
  final LinkedHashSet<FloatVar> variableQueue = new LinkedHashSet<>();

  /** It specifies what relations is used by this constraint. */
  public byte relationType;

  /** It specifies a list of variables being summed. */
  public FloatVar[] list;

  /** It specifies a list of weights associated with the variables being summed. */
  public double[] weights;

  /** It specifies variable for the overall sum. */
  public double sum;

  Store store;
  boolean reified = true;

  Btree linearTree;

  TimeStamp<Boolean> noSat;

  /**
   * Constructs a Linear constraint with a constant sum.
   *
   * @param store current store
   * @param list variables which are being multiplied by weights.
   * @param weights weight for each variable.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "{@literal !=}"
   * @param sum the sum of weighted variables.
   */
  public Linear(Store store, FloatVar[] list, double[] weights, String rel, double sum) {
    commonInitialization(store, list, weights, rel, sum);
  }

  /**
   * Constructs a Linear constraint with a variable sum.
   *
   * @param store current store
   * @param list variables which are being multiplied by weights.
   * @param weights weight for each variable.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}", "{@literal !=}"
   * @param sum variable containing the sum of weighted variables.
   */
  public Linear(Store store, FloatVar[] list, double[] weights, String rel, FloatVar sum) {

    checkInputForNullness(
        new String[] {"list", "weights", "rel", "sum"},
        new Object[][] {list, {weights}, {rel}, {sum}});

    commonInitialization(
        store,
        Stream.concat(Arrays.stream(list), Stream.of(sum)).toArray(FloatVar[]::new),
        DoubleStream.concat(Arrays.stream(weights), DoubleStream.of(-1)).toArray(),
        rel,
        0);
  }

  /**
   * It constructs the constraint Linear.
   *
   * @param store current store
   * @param variables variables which are being multiplied by weights.
   * @param weights weight for each variable.
   * @param rel the relation, one of "==", "{@literal <}", "{@literal >}", "{@literal <=}",
   *     "{@literal >=}"
   * @param sum variable containing the sum of weighted variables.
   */
  public Linear(
      Store store,
      List<? extends FloatVar> variables,
      List<Double> weights,
      String rel,
      double sum) {

    checkInputForNullness(
        new String[] {"variables", "weights", "rel"}, new Object[] {variables, weights, rel});
    commonInitialization(
        store,
        variables.toArray(new FloatVar[0]),
        weights.stream().mapToDouble(i -> i).toArray(),
        rel,
        sum);
  }

  private void commonInitialization(
      Store store, FloatVar[] list, double[] weights, String rel, double sum) {

    this.relationType = relation(rel);
    this.store = store;
    queueIndex = 1;

    if (list.length != weights.length) {
      throw new IllegalArgumentException(
          "Constraint Linear has parameters list and weights of different length.");
    }

    numberId = idNumber.incrementAndGet();
    this.sum = sum;
    noSat = new TimeStamp<>(store, false);

    Map<FloatVar, Double> parameters = buildParametersMap(list, weights);
    installListAndWeights(parameters);

    if (this.list.length == 0) {
      installEmptyListFallback(store);
    }
    if (this.list.length == 1) {
      installSingleVariableFallback(store);
    }

    VariableNode[] leafNodes = new VariableNode[this.list.length];

    for (int i = 0; i < this.list.length; i++) {

      if (this.weights[i] == 1) {
        leafNodes[i] = new VarNode(store, this.list[i]);
      } else {
        leafNodes[i] = new VarWeightNode(store, this.list[i], this.weights[i]);
      }
      leafNodes[i].rel = relationType;

      varMap.put(this.list[i], leafNodes[i]);
    }

    Arrays.sort(leafNodes, new VarWeightComparator<>());

    RootBnode root = buildBinaryTree(leafNodes);
    linearTree = new Btree(root);

    setScope(this.list);

    checkForOverflow();
  }

  private Map<FloatVar, Double> buildParametersMap(FloatVar[] list, double[] weights) {
    Map<FloatVar, Double> parameters = new LinkedHashMap<>();
    for (int i = 0; i < list.length; i++) {
      if (weights[i] != 0) {
        if (list[i].min() == list[i].max()) {
          this.sum -= list[i].value() * weights[i];
        } else if (parameters.get(list[i]) != null) {
          Double coeff = parameters.get(list[i]);
          Double sumOfCoeff = coeff + weights[i];
          parameters.put(list[i], sumOfCoeff);
        } else {
          parameters.put(list[i], weights[i]);
        }
      }
    }
    return parameters;
  }

  private void installListAndWeights(Map<FloatVar, Double> parameters) {
    this.list = new FloatVar[parameters.size()];
    this.weights = new double[parameters.size()];
    int k = 0;
    for (Map.Entry<FloatVar, Double> e : parameters.entrySet()) {
      this.list[k] = e.getKey();
      this.weights[k] = e.getValue();
      k++;
    }
  }

  private void installEmptyListFallback(Store store) {
    this.list = new FloatVar[2];
    this.weights = new double[2];
    this.list[0] = new FloatVar(store, 0, 0);
    this.weights[0] = 1;
    this.list[1] = new FloatVar(store, 0, 0);
    this.weights[1] = 1;
    if (Math.abs(this.sum) < FloatDomain.precision()) {
      this.sum = 0;
    }
  }

  private void installSingleVariableFallback(Store store) {
    FloatVar v = this.list[0];
    double w = this.weights[0];
    this.list = new FloatVar[2];
    this.weights = new double[2];
    this.list[0] = v;
    this.weights[0] = w;
    this.list[1] = new FloatVar(store, 0, 0);
    this.weights[1] = 1;
  }

  RootBnode buildBinaryTree(BinaryNode[] nodes) {

    BinaryNode[] nextLevelNodes = new BinaryNode[nodes.length / 2 + nodes.length % 2];

    if (nodes.length > 1) {
      for (int i = 0; i < nodes.length - 1; i += 2) {
        BinaryNode parent;

        if (nodes.length == 2) {
          parent = new RootBnode(store, FloatDomain.MIN_FLOAT, FloatDomain.MAX_FLOAT);
        } else {
          parent = new Bnode(store, FloatDomain.MIN_FLOAT, FloatDomain.MAX_FLOAT);
        }

        parent.left = nodes[i];
        parent.right = nodes[i + 1];

        // currently sibling not used

        nodes[i].parent = parent;
        nodes[i + 1].parent = parent;

        nextLevelNodes[i / 2] = parent;
      }
      if (nodes.length % 2 == 1) {
        nextLevelNodes[nextLevelNodes.length - 1] = nextLevelNodes[0];
        nextLevelNodes[0] = nodes[nodes.length - 1];
      }

      return buildBinaryTree(nextLevelNodes);
    } else {
      // root node
      ((RootBnode) nodes[0]).val = this.sum;
      ((RootBnode) nodes[0]).rel = relationType;

      return (RootBnode) nodes[0];
    }
  }

  @Override
  public void consistency(Store store) {

    // compute for original relation
    linearTree.root.rel = relationType;

    pruneRelation();

    if (relationType != EQ && entailed(relationType)) {
      removeConstraint();
    }
  }

  @Override
  public void notConsistency(Store store) {

    // compute for negated original relation
    linearTree.root.rel = NEG_REL[relationType];

    pruneRelation();

    if (NEG_REL[relationType] != EQ && entailed(NEG_REL[relationType])) {
      removeConstraint();
    }
  }

  private void pruneRelation() {

    while (!variableQueue.isEmpty()) {
      // propagate changes in FDV's and prune

      Iterator<FloatVar> it = variableQueue.iterator();
      FloatVar v = it.next();
      it.remove();
      VariableNode n = varMap.get(v);

      n.propagateAndPrune();
    }
  }

  void propagate(Set<FloatVar> fdvs) {

    while (!fdvs.isEmpty()) {

      Iterator<FloatVar> it = fdvs.iterator();
      FloatVar v = it.next();
      it.remove();
      VariableNode n = varMap.get(v);

      n.propagate();
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  @Override
  public void impose(Store store) {

    reified = false;
    super.impose(store);
  }

  @Override
  public void queueVariable(int level, Var v) {
    variableQueue.add((FloatVar) v);
  }

  /**
   * Checks reified constraint state and returns the entailment result.
   *
   * @param rel the relation type to check entailment for.
   * @param failResult the value to return when propagation fails or was already diagnosed as not
   *     satisfied.
   * @return whether the constraint is satisfied/notSatisfied according to the given relation.
   */
  private boolean checkReifiedEntailment(byte rel, boolean failResult) {

    if (reified) {

      // check whether constraint has been already diagnosed as not satisfied at this level
      if (noSat.stamp() < store.level) {
        noSat.update(false);
      } else if (noSat.stamp() == store.level && noSat.value()) {
        return failResult;
      }
      // ==========

      try {
        propagate(variableQueue);
      } catch (FailException _) {
        noSat.update(true);
        return failResult;
      }
    }

    return entailed(rel);
  }

  @Override
  public boolean satisfied() {
    return checkReifiedEntailment(relationType, false);
  }

  @Override
  public boolean notSatisfied() {
    return checkReifiedEntailment(NEG_REL[relationType], true);
  }

  private boolean entailed(byte rel) {

    BoundsVarValue b = (BoundsVarValue) linearTree.root.bound.value();

    switch (rel) {
      case EQ:
        FloatInterval rootInterval = new FloatInterval(b.lb, b.ub);

        if (rootInterval.singleton() && b.lb <= sum && sum <= b.ub) {
          return true;
        }
        break;
      case LT:
        if (b.ub < sum) {
          return true;
        }
        break;
      case LE:
        if (b.ub <= sum) {
          return true;
        }
        break;
      case NE:
        if (b.lb > sum || b.ub < sum) {
          return true;
        }
        break;
      case GT:
        if (b.lb > sum) {
          return true;
        }
        break;
      case GE:
        if (b.lb >= sum) {
          return true;
        }
        break;
      default:
        break;
    }

    return false;
  }

  void checkForOverflow() {

    double sumMin = 0;
    double sumMax = 0;
    for (int i = 0; i < list.length; i++) {
      double n1 = list[i].min() * weights[i];
      double n2 = list[i].max() * weights[i];
      if (Double.isInfinite(n1) || Double.isInfinite(n2)) {
        throw new ArithmeticException("Overflow occurred in floating point operations");
      }

      if (n1 <= n2) {
        sumMin += n1;
        sumMax += n2;
      } else {
        sumMin += n2;
        sumMax += n1;
      }

      if (Double.isInfinite(sumMin) || Double.isInfinite(sumMax)) {
        throw new ArithmeticException("Overflow occurred in floating point operations");
      }
    }
  }

  /**
   * Converts a string relation to a byte code.
   *
   * @param r the relation string (e.g., {@code "=="}, {@code "<"}, {@code "<="}, {@code "!="},
   *     {@code ">"}, {@code ">="})
   * @return the byte code representing the relation
   */
  public byte relation(String r) {
    switch (r) {
      case "==", "=" -> {
        return EQ;
      }
      case "<" -> {
        return LT;
      }
      case "<=", "=<" -> {
        return LE;
      }
      case "!=" -> {
        return NE;
      }
      case ">" -> {
        return GT;
      }
      case ">=", "=>" -> {
        return GE;
      }
      default -> {
        System.err.println("Wrong relation symbol in Linear constraint " + r + "; assumed ==");
        return EQ;
      }
    }
  }

  /**
   * Converts the relation byte code to a string representation.
   *
   * @return the string representation of the relation
   */
  public String rel2String() {
    return switch (relationType) {
      case EQ -> "==";
      case LT -> "<";
      case LE -> "<=";
      case NE -> "!=";
      case GT -> ">";
      case GE -> ">=";
      default -> "?";
    };
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append(" : Linear( [ ");

    for (int i = 0; i < list.length; i++) {
      result.append(list[i]);
      if (i < list.length - 1) {
        result.append(", ");
      }
    }
    result.append("], [");

    for (int i = 0; i < weights.length; i++) {
      result.append(weights[i]);
      if (i < weights.length - 1) {
        result.append(", ");
      }
    }

    result.append("], ").append(rel2String()).append(", ").append(sum).append(" )");

    return result.toString();
  }

  static class VarWeightComparator<T extends VariableNode> implements Comparator<T>, Serializable {

    VarWeightComparator() {}

    public int compare(T o1, T o2) {
      double diff_o1;
      double diff_o2;

      if (o1 instanceof VarNode) {
        diff_o1 = o1.max() - o1.min();
      } else {
        diff_o1 = (o1.max() - o1.min()) * ((VarWeightNode) o1).weight;
      }

      if (o2 instanceof VarNode) {
        diff_o2 = o2.max() - o2.min();
      } else {
        diff_o2 = (o2.max() - o2.min()) * ((VarWeightNode) o2).weight;
      }

      return Double.compare(diff_o1, diff_o2);
    }
  }
}
