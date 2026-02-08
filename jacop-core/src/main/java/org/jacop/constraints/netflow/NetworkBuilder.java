/*
 * NetworkBuilder.java
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

package org.jacop.constraints.netflow;

import java.util.ArrayList;
import java.util.List;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Eq;
import org.jacop.constraints.In;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Not;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.netflow.DomainStructure.Behavior;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * A builder class for the network flow constraints. Models should use or inherit from this class to
 * build a network.
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 5.0
 */
public class NetworkBuilder {

  public final List<Node> nodeList = new ArrayList<>();
  public final List<Arc> arcList = new ArrayList<>();
  public final List<VarHandler> handlerList = new ArrayList<>();
  public IntVar costVariable;
  private int nextNodeName = 1;

  /** Creates a new network builder with no cost variable. */
  public NetworkBuilder() {
    this.costVariable = null;
  }

  /**
   * Creates a new network builder with the specified cost variable.
   *
   * @param costVariable the variable representing the total cost of the network flow
   */
  public NetworkBuilder(IntVar costVariable) {
    this.costVariable = costVariable;
  }

  /* cost variable */

  public void setCostVariable(IntVar costVariable) {
    this.costVariable = costVariable;
  }

  /* add node */

  /**
   * Adds a new node with zero balance to the network.
   *
   * @return the newly created node
   */
  public Node addNode() {
    return addNode(0);
  }

  /**
   * Adds a new node with the specified balance to the network.
   *
   * @param balance the supply (positive) or demand (negative) at this node
   * @return the newly created node
   */
  public Node addNode(int balance) {
    String name = "(" + nextNodeName++ + ")";
    return addNode(name, balance);
  }

  /**
   * Adds a new node with the specified name and zero balance to the network.
   *
   * @param name the name of the node
   * @return the newly created node
   */
  public Node addNode(String name) {
    return addNode(name, 0);
  }

  /**
   * Adds a new node with the specified name and balance to the network.
   *
   * @param name the name of the node
   * @param balance the supply (positive) or demand (negative) at this node
   * @return the newly created node
   */
  public Node addNode(String name, int balance) {
    Node node = new Node(name, balance);
    nodeList.add(node);
    return node;
  }

  /* add arc */

  /**
   * Adds an arc with variable weight and variable flow to the network.
   *
   * @param from the source node
   * @param to the destination node
   * @param wvar the variable representing the arc weight (cost per unit flow)
   * @param xvar the variable representing the flow on this arc
   * @return the newly created arc
   */
  public Arc addArc(Node from, Node to, IntVar wvar, IntVar xvar) {

    Arc arc = addArc(from, to, wvar, xvar.min(), xvar.max());

    arc.companion.xVar = xvar;

    return arc;
  }

  /**
   * Adds an arc with fixed weight and variable flow to the network.
   *
   * @param from the source node
   * @param to the destination node
   * @param weight the fixed cost per unit of flow
   * @param xvar the variable representing the flow on this arc
   * @return the newly created arc
   */
  public Arc addArc(Node from, Node to, int weight, IntVar xvar) {

    Arc arc = addArc(from, to, weight, xvar.min(), xvar.max());

    if (arc.companion == null) {
      arc.companion = new ArcCompanion(arc, 0);
    }

    arc.companion.xVar = xvar;
    handlerList.add(arc.companion);

    return arc;
  }

  /**
   * Adds an arc with variable weight and specified capacity bounds to the network.
   *
   * @param from the source node
   * @param to the destination node
   * @param wvar the variable representing the arc weight (cost per unit flow)
   * @param lowerCapacity the minimum flow capacity of the arc
   * @param upperCapacity the maximum flow capacity of the arc
   * @return the newly created arc
   */
  public Arc addArc(Node from, Node to, IntVar wvar, int lowerCapacity, int upperCapacity) {

    int weight = wvar.min();
    Arc arc = addArc(from, to, weight, lowerCapacity, upperCapacity);

    if (arc.companion == null) {
      arc.companion = new ArcCompanion(arc, 0);
    }

    arc.companion.wVar = wvar;
    handlerList.add(arc.companion);

    return arc;
  }

  /**
   * Adds an arc with fixed weight and specified capacity bounds to the network.
   *
   * @param from the source node
   * @param to the destination node
   * @param weight the fixed cost per unit of flow
   * @param lowerCapacity the minimum flow capacity of the arc
   * @param upperCapacity the maximum flow capacity of the arc
   * @return the newly created arc
   */
  public Arc addArc(Node from, Node to, int weight, int lowerCapacity, int upperCapacity) {
    Arc arc = new Arc(from, to, weight, lowerCapacity, upperCapacity);
    arcList.add(arc);
    return arc;
  }

  /**
   * Adds an arc with fixed weight, zero lower capacity, and specified upper capacity.
   *
   * @param from the source node
   * @param to the destination node
   * @param weight the fixed cost per unit of flow
   * @param capacity the maximum flow capacity of the arc
   * @return the newly created arc
   */
  public Arc addArc(Node from, Node to, int weight, int capacity) {
    return addArc(from, to, weight, 0, capacity);
  }

  /**
   * Adds an arc with fixed weight and unlimited capacity.
   *
   * @param from the source node
   * @param to the destination node
   * @param weight the fixed cost per unit of flow
   * @return the newly created arc
   */
  public Arc addArc(Node from, Node to, int weight) {
    return addArc(from, to, weight, Integer.MAX_VALUE);
  }

  /**
   * Adds an arc with zero weight and unlimited capacity.
   *
   * @param from the source node
   * @param to the destination node
   * @return the newly created arc
   */
  public Arc addArc(Node from, Node to) {
    return addArc(from, to, 0);
  }

  /* value graph */

  /**
   * Returns two arrays containing the nodes for each variable and the nodes for each domain,
   * respectively.
   *
   * @param vars varibales for nodes
   * @param domains nodes for each variable
   * @return two arrays containing the nodes for each variable and the nodes for each domain,
   *     respectively
   */
  public Node[][] valueGraph(IntVar[] vars, IntDomain[] domains) {

    int n = vars.length;
    int m = domains.length;

    Node[] v = new Node[n];
    Node[] d = new Node[m];

    for (int i = 0; i < n; i++) {
      v[i] = addNode(vars[i].id, 1);
    }

    for (int i = 0; i < m; i++) {
      d[i] = addNode(domains[i].toString(), 0);
    }

    for (int i = 0; i < n; i++) {

      IntVar var = vars[i];

      List<Arc> arcs = new ArrayList<>();
      List<Domain> doms = new ArrayList<>();

      IntDomain vardom = var.domain;
      for (int j = 0; j < m; j++) {
        if (vardom.isIntersecting(domains[j])) {
          arcs.add(addArc(v[i], d[j], 0, 1));
          doms.add(domains[j]);
        }
      }
      handlerList.add(new DomainStructure(var, doms, arcs));
    }
    return new Node[][] {v, d};
  }

  /* list variables */

  /**
   * Returns a list of all variables in the network, excluding the cost variable.
   *
   * @return a list of all flow and weight variables managed by the handlers
   */
  public ArrayList<IntVar> listVariables() {

    ArrayList<IntVar> list = new ArrayList<>();

    for (VarHandler handler : handlerList) {
      list.addAll(handler.listVariables());
    }

    return list;
  }

  /* build network */

  /**
   * Builds and returns a {@link NetworkFlow} constraint from the current network configuration.
   *
   * @return the constructed network flow constraint
   */
  public NetworkFlow build() {
    return new NetworkFlow(this);
  }

  /**
   * Generally speaking, especially in case of multiple arcs between two nodes and structure
   * constraints imposed on arcs makes it hard to decompose network flow constraint into primitive
   * ones. Since, the decomposition introduces new variables and removal of artificial solutions is
   * not practically achievable in all cases it is possible that decomposition will have more
   * solutions due to the fact that decomposition may use more expensive arcs to transfer the flow.
   *
   * @param store current store
   * @return decomposed network using primitive constraints
   */
  public List<Constraint> primitiveDecomposition(Store store) {

    List<Constraint> result = new ArrayList<>();

    // @TODO: fix it? Check the remark above.
    for (Node node : nodeList) {
      List<IntVar> in = new ArrayList<>();
      List<IntVar> out = new ArrayList<>();

      for (Arc arc : arcList) {

        // This code replaces, the one below to handle
        if (arc.head == node || arc.tail() == node) {

          if (arc.getCompanion() == null) {
            // the above condition is satisfied sometimes.
            arc.companion = new ArcCompanion(arc, 0);
          }

          IntVar var = arc.getCompanion().xVar;
          if (var == null) {
            var =
                new IntVar(
                    store,
                    arc.getCompanion().flowOffset,
                    arc.getCompanion().flowOffset + arc.capacity + arc.sister.capacity);
          }
          if (arc.head == node) {
            in.add(var);
          }
          if (arc.tail() == node) {
            out.add(var);
          }
          arc.getCompanion().xVar = var;
        }
      }

      if (node.balance != 0) {
        IntVar balance = new IntVar(store, node.balance, node.balance);
        in.add(balance);
      }

      // added.
      if (in.isEmpty() || out.isEmpty()) {
        continue;
      }

      if (in.size() == 1) {
        sumC(result, store, out, in.getFirst());
      } else if (out.size() == 1) {
        sumC(result, store, in, out.getFirst());
      } else {
        IntVar sum = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
        sumC(result, store, in, sum);
        sumC(result, store, out, sum);
      }
    }

    for (VarHandler handler : handlerList) {

      if (handler instanceof DomainStructure structure) {

        for (int i = 0; i < structure.arcs.length; i++) {

          Arc arc = structure.arcs[i];
          IntDomain dom = structure.domains[i];

          if (structure.behavior != Behavior.PRUNE_ACTIVE) {
            result.add(
                new Eq(
                    new Not(new In(structure.variable, dom)),
                    new XeqC(arc.getCompanion().xVar, arc.getCompanion().flowOffset)));
          }

          if (structure.behavior != Behavior.PRUNE_INACTIVE) {
            int maxFlow = arc.getCompanion().flowOffset + arc.capacity + arc.sister.capacity;
            result.add(
                new Eq(
                    new In(structure.variable, dom), new XeqC(arc.getCompanion().xVar, maxFlow)));
          }
        }
      }
    }

    List<IntVar> vars = new ArrayList<>();
    List<Integer> weights = new ArrayList<>();

    boolean simpleSum = true;
    for (Arc arc : arcList) {
      if (arc.getCompanion().wVar != null) {
        IntVar var = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
        result.add(new XmulYeqZ(arc.getCompanion().xVar, arc.getCompanion().wVar, var));
        vars.add(var);
        weights.add(1);
      } else if (arc.cost == 1) {
        vars.add(arc.getCompanion().xVar);
        weights.add(1);
      } else if (arc.cost != 0) {

        simpleSum = false;
        vars.add(arc.getCompanion().xVar);
        weights.add(arc.cost);
      }
    }

    // @TODO: SumWeight could be used instead of Sum and auxiliary variables weight above.
    if (simpleSum) {
      sumC(result, store, vars, costVariable);
    } else {
      int n = vars.size();
      IntVar[] vs = new IntVar[n + 1];
      int[] ws = new int[n + 1];
      for (int i = 0; i < n; i++) {
        vs[i] = vars.get(i);
        ws[i] = weights.get(i);
      }
      vs[n] = costVariable;
      ws[n] = -1;
      result.add(new LinearInt(vs, ws, "==", 0));
      // result.add(new SumWeight(vars, weights, costVariable)); deprecated
    }
    return result;
  }

  private void sumC(List<Constraint> list, Store store, List<IntVar> vars, IntVar result) {

    if (result == null) {
      throw new AssertionError();
    }

    if (vars.isEmpty()) {
      list.add(new XeqY(result, new IntVar(store, 0, 0)));
    } else if (vars.size() == 1) {
      list.add(new XeqY(result, vars.getFirst()));
    } else {
      list.add(new SumInt(vars, "==", result));
      // list.add(new Sum(vars, result)); deprecated
    }
  }
}
