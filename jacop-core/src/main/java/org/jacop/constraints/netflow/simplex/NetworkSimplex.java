/*
 * NetworkSimplex.java
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

package org.jacop.constraints.netflow.simplex;

import static org.jacop.constraints.netflow.Assert.checkBeforeUpdate;
import static org.jacop.constraints.netflow.Assert.checkFlow;
import static org.jacop.constraints.netflow.Assert.checkInfeasibleNodes;
import static org.jacop.constraints.netflow.Assert.checkOptimality;
import static org.jacop.constraints.netflow.Assert.checkStructure;
import static org.jacop.constraints.netflow.Assert.checkTreePotentials;
import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.netflow.Pruning;

/**
 * Implementation of the network simplex for solving minimum cost flow problems.
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
@SuppressWarnings("PMD.TooManyStaticImports")
public class NetworkSimplex {

  public static final boolean DEBUG = false; // true;

  @SuppressWarnings("PointlessBooleanExpression")
  public static final boolean DEBUG_ALL = DEBUG;

  public static final int LARGE_COST = 100000; // 1 << 29; // or 28 ?

  public static final int TREE_ARC = -1;
  public static final int DELETED_ARC = -3;

  // 'nodes' does NOT contain the root
  // 'lower' is the list of arcs at their lower bound
  // lower[*].sister is the list of arcs at their upper bound
  public final Node root;
  public final Node[] nodes;
  public final Arc[] lower;
  // the set of nodes with non-zero balance
  public final Set<Node> infeasibleNodes;
  public final List<Arc> allArcs;
  protected final PivotRule pivotRule;
  public int numArcs;
  // second 'return' value of augmentFlow method
  public Arc blocking;
  // the number of arcs incident to all nodes, each arc counted at both ends, artificial arcs once
  private int incidentArcs;
  // the best entering arc found so far by a dual pivot, and its reduced cost
  private Arc bestEntering;
  private int bestEnteringCost;

  /**
   * Constructs a network simplex solver with the given nodes and arcs, initializing the spanning
   * tree.
   *
   * @param nodes the list of nodes in the network.
   * @param arcs the list of arcs in the network.
   */
  public NetworkSimplex(List<Node> nodes, List<Arc> arcs) {

    this.allArcs = new ArrayList<>(arcs);

    this.nodes = nodes.toArray(new Node[0]);
    this.lower = allArcs.toArray(new Arc[0]);
    this.root = new Node("(root)", 0);
    this.numArcs = lower.length;
    this.pivotRule = new Danzig(this);
    this.infeasibleNodes = new LinkedHashSet<>();

    // initialize index pointers
    for (int i = 0; i < lower.length; i++) {
      lower[i].index = lower[i].sister.index = i;
    }

    // create initial spanning tree structure
    Node nextOnThread = root;
    for (int i = 0; i < this.nodes.length; i++) {
      Node node = this.nodes[i];
      node.index = i;
      node.parent = root;
      node.thread = nextOnThread;
      nextOnThread.threadPredecessor = node;
      node.depth = 1;
      nextOnThread = node;

      Arc arc = new Arc(node, root);
      node.artificial = arc;
      node.toParent = arc;
      arc.index = TREE_ARC;
      arc.sister.index = TREE_ARC;

      // register infeasible nodes
      if (node.deltaBalance != 0) {
        infeasibleNodes.add(node);
      }
    }

    root.thread = nextOnThread;
    nextOnThread.threadPredecessor = root;
    root.potential = 0;
    root.depth = 0;
    root.computePotentials();

    // Initialize adjacency counter
    for (Arc arc : allArcs) {
      incrementDegree(arc.head, arc);
      incrementDegree(arc.tail(), arc);
    }
    initializeIncidentArcs();

    if (ASSERTS_ENABLED && !checkFlow(this)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !checkStructure(this)) {
      throw new IllegalStateException("Assertion failed");
    }
  }

  private void initializeIncidentArcs() {
    Map<Node, List<Arc>> incident = new IdentityHashMap<>();
    for (Arc arc : allArcs) {
      incident.computeIfAbsent(arc.head, k -> new ArrayList<>()).add(arc);
      incident.computeIfAbsent(arc.tail(), k -> new ArrayList<>()).add(arc);
    }
    incident.forEach((node, arcs) -> node.incident = arcs.toArray(new Arc[0]));
    incidentArcs = 2 * allArcs.size() + nodes.length;
  }

  private void incrementDegree(Node node, Arc myArc) {

    if (node.degree < 2) {
      node.adjacencyList[node.degree] = myArc.forward ? myArc : myArc.sister;
    }

    node.degree++;
  }

  private void decrementDegree(Node node) {
    if (ASSERTS_ENABLED && node == root) {
      throw new IllegalStateException("Assertion failed");
    }

    node.degree--;
    if (node.degree == 2) {
      rebuildAdjacencyListForDegree2(node);
    }
    if (node.degree < 2) {
      removeDeletedArcsFromAdjacencyList(node);
      if (ASSERTS_ENABLED
          && !((node.degree == 1
                  && (node.adjacencyList[0] == null) ^ (node.adjacencyList[1] == null))
              || (node.degree == 0
                  && (node.adjacencyList[0] == null)
                  && (node.adjacencyList[1] == null)))) {
        throw new IllegalStateException(
            String.valueOf(node + "\n" + node.degree + ": " + Arrays.toString(node.adjacencyList)));
      }
    }
  }

  private void rebuildAdjacencyListForDegree2(Node node) {
    int i = 0;
    for (Arc arc : allArcs) {
      if (arc.index != DELETED_ARC && (arc.head == node || arc.tail() == node)) {
        if (ASSERTS_ENABLED && i >= 2) {
          throw new IllegalStateException(String.valueOf(node + " has extra arc " + arc));
        }
        node.adjacencyList[i++] = arc;
      }
    }
    if (ASSERTS_ENABLED && i != 2) {
      throw new IllegalStateException("Assertion failed");
    }
  }

  private void removeDeletedArcsFromAdjacencyList(Node node) {
    Arc arc = node.adjacencyList[0];
    if (arc != null && arc.index == DELETED_ARC) {
      node.adjacencyList[0] = node.adjacencyList[1];
      node.adjacencyList[1] = null;
    }
    arc = node.adjacencyList[1];
    if (arc != null && arc.index == DELETED_ARC) {
      node.adjacencyList[1] = null;
    }
  }

  /**
   * Adds an arc to the network.
   *
   * @param arc the network arc being added
   */
  protected void addArc(Arc arc) {
    if (ASSERTS_ENABLED && arc.index != DELETED_ARC) {
      throw new IllegalStateException(String.valueOf(arc));
    }
    int index = numArcs++;
    arc.index = arc.sister.index = index;
    if (arc.capacity == 0) {
      // arc at upper bound
      lower[index] = arc.sister;
    } else {
      // arc at lower bound
      lower[index] = arc;
      if (ASSERTS_ENABLED && arc.sister.capacity != 0) {
        throw new IllegalStateException("Assertion failed");
      }
    }

    if (arc.companion != null) {
      ((Pruning) this).numActiveArcs++;
    }

    incrementDegree(arc.head, arc);
    incrementDegree(arc.tail(), arc);
  }

  /**
   * Adds an arc back into the network, performing a primal step if the arc carries flow.
   *
   * @param arc the arc to add, which must currently be marked as deleted.
   */
  public void addArcWithFlow(Arc arc) {
    if (ASSERTS_ENABLED && arc.index != DELETED_ARC) {
      throw new IllegalStateException(String.valueOf(arc));
    }
    int index = numArcs++;
    arc.index = arc.sister.index = index;
    if (arc.capacity == 0) {
      // arc at upper bound
      lower[index] = arc.sister;
    } else {
      // arc at lower bound
      lower[index] = arc;

      if (arc.sister.capacity > 0) {
        primalStep(arc.sister);
      }
      if (ASSERTS_ENABLED && arc.sister.capacity != 0 && arc.index != TREE_ARC) {
        throw new IllegalStateException("Assertion failed");
      }
    }

    if (arc.companion != null) {
      ((Pruning) this).numActiveArcs++;
    }

    incrementDegree(arc.head, arc);
    incrementDegree(arc.tail(), arc);
  }

  /**
   * Removes an arc from the network and updates adjacency information.
   *
   * @param arc the arc to remove from the network.
   */
  public void removeArc(Arc arc) {
    // Remove arc from graph
    int index = arc.index;
    if (ASSERTS_ENABLED && index < 0) {
      throw new IllegalStateException(String.valueOf(arc.toString()));
    }
    if (index < --numArcs) {
      Arc last = lower[numArcs];
      lower[index] = last;
      last.index = last.sister.index = index;
    }
    lower[numArcs] = null;
    arc.index = arc.sister.index = DELETED_ARC;

    if (arc.companion != null) {
      ((Pruning) this).numActiveArcs--;
    }

    decrementDegree(arc.head);
    decrementDegree(arc.tail());
  }

  /**
   * Removing the costs of the artificial arcs changes the potentials, so the flow found with them
   * need not be optimal any more; this continues pivoting on the real costs until it is.
   *
   * @param maxPivots max value of the pivot
   * @param pivots the number of pivots performed so far, or -1 if the maximum was reached
   * @param failure whether clearing the artificial arcs found the network infeasible
   * @return the total number of pivots, or -1 if the maximum number of pivots was reached.
   */
  private int continuePivoting(int maxPivots, int pivots, boolean failure) {
    if (failure || pivots == -1) {
      return pivots;
    }
    int morePivots = runPivotLoop(maxPivots - pivots);
    return morePivots == -1 ? -1 : pivots + morePivots;
  }

  /**
   * Executes the network simplex algorithm to find an optimal solution.
   *
   * @param maxPivots max value of the pivot
   * @return the number of pivots performed until optimality was reached, or -1 if the maximum
   *     number of pivots was reached.
   */
  public int networkSimplex(int maxPivots) {

    if (ASSERTS_ENABLED && !checkFlow(this)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !checkStructure(this)) {
      throw new IllegalStateException("Assertion failed");
    }

    initializeArtificialArcs();
    root.computePotentials();
    if (ASSERTS_ENABLED && !checkInfeasibleNodes(this)) {
      throw new IllegalStateException("Assertion failed");
    }

    int pivots = runPivotLoop(maxPivots);

    boolean failure = clearArtificialArcs();

    root.computePotentials();

    pivots = continuePivoting(maxPivots, pivots, failure);

    if (ASSERTS_ENABLED && !checkFlow(this)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !checkStructure(this)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && pivots != -1 && !failure && !checkOptimality(this)) {
      throw new IllegalStateException("Assertion failed");
    }

    if (DEBUG) {
      logNetworkSimplexResult(pivots, maxPivots, failure);
    }
    if (failure && pivots != -1) {
      pivots = -2;
    }
    return pivots;
  }

  /**
   * Restores an optimal flow after changes that keep every node balance and every arc cost, such as
   * the analysis of one arc. The potentials are then still valid, so when no node is infeasible the
   * primal pivots alone are enough: there are no artificial arcs to set up or clear.
   *
   * @param maxPivots max value of the pivot
   * @return the number of pivots performed until optimality was reached, -1 if the maximum number
   *     of pivots was reached, or -2 if the network is infeasible.
   */
  public int reoptimize(int maxPivots) {
    for (Node node : infeasibleNodes) {
      if (node.deltaBalance != 0) {
        return networkSimplex(maxPivots);
      }
    }
    if (ASSERTS_ENABLED && !checkTreePotentials(this)) {
      throw new IllegalStateException("Assertion failed");
    }
    return runPivotLoop(maxPivots);
  }

  private void initializeArtificialArcs() {
    Iterator<Node> it = infeasibleNodes.iterator();
    while (it.hasNext()) {
      Node node = it.next();
      int delta = node.deltaBalance;
      if (delta > 0) {
        Arc arc = node.artificial;
        arc.sister.set(-LARGE_COST, delta);
        if (ASSERTS_ENABLED && arc.index == DELETED_ARC) {
          throw new IllegalStateException("Assertion failed");
        }
        if (arc.index != TREE_ARC) {
          lower[arc.index] = arc.sister;
        }
      } else if (delta < 0) {
        Arc arc = node.artificial;
        arc.set(-LARGE_COST, -delta);
        if (ASSERTS_ENABLED && arc.index == DELETED_ARC) {
          throw new IllegalStateException("Assertion failed");
        }
        if (arc.index != TREE_ARC) {
          lower[arc.index] = arc;
        }
      } else {
        it.remove();
      }
    }
  }

  private int runPivotLoop(int maxPivots) {
    pivotRule.reset();
    int pivots = 0;
    Arc entering;
    while ((entering = pivotRule.next()) != null) {
      if (pivots >= maxPivots) {
        return -1;
      }
      primalStep(entering);
      pivots++;
    }
    return pivots;
  }

  private boolean clearArtificialArcs() {
    boolean failure = false;
    Iterator<Node> it = infeasibleNodes.iterator();
    while (it.hasNext()) {
      Node node = it.next();
      Arc arc = node.artificial;
      int delta = node.deltaBalance;
      int infeasibleFlow;
      if (delta > 0) {
        infeasibleFlow = arc.sister.capacity;
      } else {
        infeasibleFlow = -arc.capacity;
        if (ASSERTS_ENABLED && delta == 0) {
          throw new IllegalStateException("Assertion failed");
        }
      }

      arc.clear();
      node.balance += delta - infeasibleFlow;
      node.deltaBalance = infeasibleFlow;
      if (infeasibleFlow != 0) {
        failure = true;
      } else {
        it.remove();
      }
    }
    return failure;
  }

  private void logNetworkSimplexResult(int pivots, int maxPivots, boolean failure) {
    if (pivots == -1) {
      log.debug("Abort after {} iterations", maxPivots);
    } else if (failure) {
      log.debug("Failure after {} iterations", pivots);
    } else {
      log.debug("{} iterations ({} arcs)", pivots, numArcs);
    }
  }

  /**
   * Performs a primal pivot.
   *
   * @param entering a non-tree arc that violates optimality
   */
  public void primalStep(Arc entering) {
    // entering arc (k,l)
    Node k = entering.tail();
    Node l = entering.head;
    int delta = entering.capacity;

    // augment flow
    delta = augmentFlow(l, k, delta);
    entering.addFlow(delta);

    // find leaving arc
    Arc leaving = this.blocking;

    if (DEBUG_ALL) {
      log.debug("Entering: {}", entering);
      log.debug("Leaving : {}", leaving);
      log.debug("Delta   : {}", delta);
      log.debug("");
    }

    // update tree
    if (leaving == null) {
      lower[entering.index] = entering.sister;
    } else {
      updateTree(leaving, entering);
    }
  }

  /**
   * Augments the flow between two nodes by the maximum amount along the unique tree path that
   * connects these nodes.
   *
   * @param from the source of the flow
   * @param to the sink of the flow
   * @param delta an upper limit on the flow to send
   * @return the actual flow that was sent. the blocking arc is 'returned' in the instance field
   *     'blocking'.
   */
  public int augmentFlow(Node from, Node to, int delta) {
    if (ASSERTS_ENABLED && delta < 0) {
      throw new IllegalStateException("Assertion failed");
    }

    blocking = null; // default value
    if (delta == 0) {
      return 0;
    }

    // entering arc (k,l)
    Node apex = to.lca(from);

    // find leaving arc
    for (Node i = from; i != apex; i = i.parent) {
      int arcCapacity = i.toParent.capacity;
      if (delta >= arcCapacity) {
        delta = arcCapacity;
        blocking = i.toParent;
      }
    }
    for (Node i = to; i != apex; i = i.parent) {
      int arcCapacity = i.toParent.sister.capacity;
      if (delta > arcCapacity) {
        delta = arcCapacity;
        blocking = i.toParent.sister;
      }
    }

    // augment flow
    for (Node j = to; j != apex; j = j.parent) {
      j.toParent.addFlow(-delta);
    }
    for (Node i = from; i != apex; i = i.parent) {
      i.toParent.addFlow(delta);
    }

    return delta;
  }

  /**
   * Both arcs must form a cycle in the tree and point in the same direction on that cycle.
   *
   * @param leaving the tree arc that leaves the tree
   * @param entering the non-tree arc that enters the tree
   */
  public void updateTree(Arc leaving, Arc entering) {

    // reverse arcs, to make both point towards the root
    if (leaving.tail().parent != leaving.head) {
      leaving = leaving.sister;
    } else {
      entering = entering.sister;
    }

    Node lastParent = leaving.head;
    Node node = entering.tail();
    Node newParent = entering.head;

    if (DEBUG) {
      log.debug("leaving  = {}", leaving);
      log.debug("entering = {}", entering);
    }

    if (ASSERTS_ENABLED && !checkBeforeUpdate(leaving, entering)) {
      throw new IllegalStateException("Assertion failed");
    }

    // Let (p,q) and (k,l) be the leaving and entering arcs,
    // respectively
    // - Initially:
    //   o q is the parent of p
    //   o {q,l} are in the same subtree, rooted at the root
    //   o {p,k} are in the same subtree, rooted at p
    // - Make l the new parent of k
    // - Reverse parent/child relation along the path k -> p
    Arc arcToNewParent = entering;
    while (node != lastParent) {
      Node oldParent = node.parent;
      treeSwap(oldParent, node, newParent);

      Arc temp = node.toParent.sister;
      node.toParent = arcToNewParent;
      arcToNewParent = temp;

      newParent = node;
      node = oldParent;
    }

    // insert leaving arc to lower arcs list
    int index = entering.index;
    if (leaving.capacity == 0) {
      lower[index] = leaving.sister;
    } else {

      lower[index] = leaving;
    }
    leaving.index = index;
    leaving.sister.index = index;

    // recompute potentials of the modified subtree
    entering.index = TREE_ARC;
    entering.sister.index = TREE_ARC;
    entering.head.computePotentials();
  }

  /**
   * Changes the parent of a node and updates the thread data structure. (This operation invalidates
   * the depth values in the subtree.)
   *
   * <p>Runs in O(T2) amortized time over all treeSwaps performed by an updateTree operation where
   * T2 is the size of the subtree that is being reversed.
   *
   * @param a the old parent of a
   * @param b the child node
   * @param c the new parent of a
   */
  public void treeSwap(Node a, Node b, Node c) {
    // shortcut for multiple arcs (for performance, not correctness)
    if (a == c) {
      return;
    }

    Node i = b.predecessorOnThread();
    Node j = b.rightMostLeaf();

    Node next = j.thread;
    i.thread = next;
    next.threadPredecessor = i;
    next = c.thread;
    j.thread = next;
    next.threadPredecessor = j;
    c.thread = b;
    b.threadPredecessor = c;

    b.parent = c;
  }

  /**
   * Given an optimal flow that satisfies all feasibility constraints except mass balance on two
   * nodes, the parametric simplex algorithm tries to achieve feasibility while keeping the solution
   * optimal.
   *
   * @param source source node
   * @param sink sink node
   * @param balance difference between in flow and out flow the flow to send from the source to the
   *     sink
   * @param maxPivots limits the number of dual pivots
   * @return the number of pivots on success, -1 if the pivot limit was reached, -2 if the problem
   *     is infeasible
   */
  public int parametricStep(Node source, Node sink, int balance, int maxPivots) {
    // check input
    if (balance < 0) {
      Node temp = source;
      source = sink;
      sink = temp;
      balance = -balance;
    } else if (balance == 0) {
      return 1;
    }

    // Augment flow
    balance -= augmentFlow(source, sink, balance);

    int pivots = 0;
    while (balance > 0) {
      // stop when limit is reached
      if (pivots >= maxPivots) {
        if (DEBUG) {
          log.debug("Abort after {} iterations", pivots);
        }
        return -1;
      }

      // Perform dual pivot
      if (dualPivot(this.blocking)) {
        pivots++;
      } else {
        return -2; // infeasible
      }

      // Augment flow
      balance -= augmentFlow(source, sink, balance);
    }
    if (DEBUG) {
      log.debug("{} iterations", pivots);
    }
    return pivots;
  }

  /**
   * Performs a dual pivot operation by finding and swapping an entering arc for the leaving arc.
   *
   * @param leaving the tree arc that is leaving the basis.
   * @return true if a valid entering arc was found and the pivot was performed, false if
   *     infeasible.
   */
  public boolean dualPivot(Arc leaving) {
    // Perform dual pivot
    Node tree;
    boolean forward;
    if (leaving.tail().parent == leaving.head) {
      tree = leaving.tail();
      forward = true;
    } else {
      tree = leaving.head;
      forward = false;
    }

    // find entering arc
    Arc entering;
    int subtreeArcs = tree.markTree(true);
    if (Math.min(subtreeArcs, incidentArcs - subtreeArcs) < numArcs) {
      entering = enteringArcFromCut(tree, forward, subtreeArcs);
    } else {
      entering = null;
      int minimumCost = Integer.MAX_VALUE;
      for (int i = 0; i < numArcs; i++) {
        Arc arc = lower[i];
        if (arc.capacity > 0 && arc.isInCut(forward)) {

          int reducedCost = arc.reducedCost();
          if (minimumCost > reducedCost) {
            minimumCost = reducedCost;
            entering = arc;
          }
        }
      }
    }
    tree.markTree(false);

    // update tree
    if (entering == null) {
      return false; // infeasible
    } else {

      updateTree(leaving.sister, entering);
      return true;
    }
  }

  /**
   * Finds the entering arc of a dual pivot among the arcs incident to one side of the cut, the
   * marked subtree or the rest of the tree, whichever has fewer incident arcs. This is cheaper than
   * scanning all non-tree arcs. Of the arcs with the smallest reduced cost it picks the one with
   * the smallest index, as the scan of all arcs does.
   *
   * @param tree the root of the marked subtree
   * @param forward whether the entering arc leaves the subtree (true) or enters it (false)
   * @param subtreeArcs the number of arcs incident to the subtree, artificial arcs included
   * @return the entering arc, or null if there is none
   */
  private Arc enteringArcFromCut(Node tree, boolean forward, int subtreeArcs) {
    bestEntering = null;
    bestEnteringCost = Integer.MAX_VALUE;
    Node last = tree.rightMostLeaf();
    if (2 * subtreeArcs <= incidentArcs) {
      for (Node node = tree; node != last.thread; node = node.thread) {
        for (Arc arc : node.incident) {
          considerEnteringArc(arc, node, forward, forward);
        }
        considerEnteringArc(node.artificial, node, forward, forward);
      }
    } else {
      // the artificial arcs of the subtree are the only arcs from it to the root
      for (Node node = tree; node != last.thread; node = node.thread) {
        considerEnteringArc(node.artificial, node, forward, forward);
      }
      for (Node node = last.thread; node != tree; node = node.thread) {
        for (Arc arc : node.incident) {
          considerEnteringArc(arc, node, !forward, forward);
        }
      }
    }
    return bestEntering;
  }

  /**
   * Keeps the residual direction of a non-tree arc as the entering arc if it crosses the cut in the
   * right direction and is better than the current one.
   *
   * @param arc an arc incident to node
   * @param node a node on the side of the cut that is scanned
   * @param leaving whether the residual arc must leave node (true) or enter it (false)
   * @param forward whether the entering arc leaves the marked subtree
   */
  private void considerEnteringArc(Arc arc, Node node, boolean leaving, boolean forward) {
    if (arc.index < 0) {
      return;
    }
    Arc residual = (arc.head == node) == leaving ? arc.sister : arc;
    if (residual.capacity <= 0 || !residual.isInCut(forward)) {
      return;
    }
    int reducedCost = residual.reducedCost();
    if (reducedCost < bestEnteringCost
        || (reducedCost == bestEnteringCost && residual.index < bestEntering.index)) {
      bestEntering = residual;
      bestEnteringCost = reducedCost;
    }
  }

  /**
   * Computes the total cost of the current flow solution.
   *
   * <p>The cost is always summed over all arcs: arcs can have negative costs, so a partial sum
   * above the cutoff does not mean that the total is above it.
   *
   * @param cutoff not used; kept for compatibility.
   * @return the total cost of the current flow.
   */
  public long cost(long cutoff) {
    long cost = 0;
    // non-tree arcs
    for (int i = 0; i < numArcs; i++) {
      cost += lower[i].longCost();
    }
    // tree arcs
    for (Node node = root.thread; node != root; node = node.thread) {
      cost += node.toParent.longCost();
    }
    return cost;
  }

  /** Debug. */

  // displays the state of the spanning tree and the flow
  public void print() {

    log.debug("Nodes:");
    for (Node n : nodes) {
      log.debug("\t{}", n);
    }

    log.debug("Arcs:");

    for (Arc a : allArcs) {
      log.debug("\t{}", a);
    }

    log.debug("Tree:");

    for (Node i = root; ; i = i.thread) {
      log.debug("\t{}\t\t{}", i, i.toParent);
      if (i.thread == root) {
        break;
      }
    }

    log.debug("Flow");
    int cost = 0;
    for (Arc a : allArcs) {
      if (!a.forward) {
        a = a.sister;
      }

      int flow = a.sister.capacity;
      if (a.companion != null) {
        flow += a.companion.flowOffset;
      }

      if (flow > 0) {
        log.debug("{}\t{}", flow, a.toFlow());
        cost += flow * a.cost;
      }
    }
    log.debug("Cost: {}", cost);
    log.debug("");
  }
}
