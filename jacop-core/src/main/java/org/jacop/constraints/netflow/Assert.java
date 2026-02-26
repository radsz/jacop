/*
 * Asserts.java
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

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.ArrayList;
import java.util.List;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.NetworkSimplex;
import org.jacop.constraints.netflow.simplex.Node;

/**
 * Utility class for validating network flow constraints.
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Assert {

  private static final String BALANCE_EQUALS = ", balance = ";
  private static final String MSG_I = "\ni = ";
  private static final String MSG_J = "\nj = ";
  private static final String MSG_IJ = "\nij = ";
  private static final String MSG_P = "\np = ";

  private Assert() {}

  /**
   * Validates flow conservation constraints on all nodes of the network.
   *
   * @param g the network simplex to validate.
   * @return true if flow conservation holds on all nodes.
   */
  public static boolean checkFlow(NetworkSimplex g) {

    final List<Arc> allArcsForDebug = allArcsForDebug(g);
    int sum = 0;
    for (Node n : g.nodes) {
      sum += n.balance;
    }

    if (ASSERTS_ENABLED && !(sum == 0)) {
      throw new IllegalStateException(String.valueOf("sum != 0"));
    }
    if (ASSERTS_ENABLED && !(g.root.balance == 0)) {
      throw new IllegalStateException(String.valueOf("root balance != 0"));
    }

    for (Node n : g.nodes) {
      FlowCounts counts = computeFlowCountsForNode(n, allArcsForDebug);
      assertNodeBalance(n, counts);
    }

    assertRootBalance(g, allArcsForDebug);

    return true;
  }

  private static void assertNodeBalance(Node n, FlowCounts counts) {
    if (ASSERTS_ENABLED && !(n.balance == counts.out - counts.in)) {
      throw new IllegalStateException(
          String.valueOf(
              "Balance on node\n"
                  + "out = "
                  + counts.out
                  + ", in = "
                  + counts.in
                  + BALANCE_EQUALS
                  + n.balance
                  + "\n"
                  + n
                  + "\n"));
    }

    if (ASSERTS_ENABLED
        && !(n.initialBalance - n.balance - n.deltaBalance == counts.delOut - counts.delIn)) {
      throw new IllegalStateException(
          String.valueOf(
              "Balance on deleted node\n"
                  + "out = "
                  + counts.delOut
                  + ", in = "
                  + counts.delIn
                  + BALANCE_EQUALS
                  + n.balance
                  + ", delta = "
                  + n.deltaBalance
                  + ", initial = "
                  + n.initialBalance
                  + "\n"
                  + "  out-in = "
                  + (counts.delOut - counts.delIn)
                  + ", initial-balance-delta = "
                  + (n.initialBalance - n.balance - n.deltaBalance)
                  + "\n"
                  + n
                  + "\n"));
    }
  }

  private static FlowCounts computeFlowCountsForNode(Node n, List<Arc> allArcsForDebug) {
    int delOut = 0;
    int delIn = 0;
    int out = 0;
    int in = 0;

    for (Arc a : allArcsForDebug) {
      if (!a.forward) {
        a = a.sister;
      }

      if (a.companion != null) {
        if (a.head == n) {
          delIn += a.companion.flowOffset;
        } else if (a.tail() == n) {
          delOut += a.companion.flowOffset;
        }
      }

      if (a.index == -3) {
        if (a.head == n) {
          delIn += a.sister.capacity;
        } else if (a.tail() == n) {
          delOut += a.sister.capacity;
        }
      } else {
        if (a.head == n) {
          in += a.sister.capacity;
        } else if (a.tail() == n) {
          out += a.sister.capacity;
        }
      }
    }

    return new FlowCounts(delOut, delIn, out, in);
  }

  private static void assertRootBalance(NetworkSimplex g, List<Arc> allArcsForDebug) {
    int out = 0;
    int in = 0;
    for (Arc a : allArcsForDebug) {
      if (!a.forward) {
        a = a.sister;
      }
      if (a.head == g.root) {
        in += a.sister.capacity;
      }
      if (a.tail() == g.root) {
        out += a.sister.capacity;
      }
    }

    if (ASSERTS_ENABLED && !(0 == out - in)) {
      throw new IllegalStateException(
          String.valueOf(
              "Balance on node (root)\n"
                  + "in = "
                  + out
                  + ", out = "
                  + in
                  + BALANCE_EQUALS
                  + 0
                  + "\n"
                  + g.root
                  + "\n"));
    }
  }

  private static final class FlowCounts {
    final int delOut;
    final int delIn;
    final int out;
    final int in;

    FlowCounts(int delOut, int delIn, int out, int in) {
      this.delOut = delOut;
      this.delIn = delIn;
      this.out = out;
      this.in = in;
    }
  }

  /**
   * Validates preconditions before a tree update (pivot) operation.
   *
   * @param leaving the arc leaving the basis tree.
   * @param entering the arc entering the basis tree.
   * @return true if the preconditions for the update are satisfied.
   */
  public static boolean checkBeforeUpdate(Arc leaving, Arc entering) {

    if (ASSERTS_ENABLED && !(leaving.index == -1)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(entering.index >= 0)) {
      throw new IllegalStateException("Assertion failed");
    }

    Node k = entering.sister.head;
    Node l = entering.head;
    Node p = leaving.sister.head;
    Node q = leaving.head;

    if (ASSERTS_ENABLED && !(q == p.parent)) {
      throw new IllegalStateException(String.valueOf("\nexpected: q is the parent of p\n"));
    }
    if (ASSERTS_ENABLED && !(p == p.lca(k))) {
      throw new IllegalStateException(
          String.valueOf("\nexpected: {p,k} are in the same subtree\n"));
    }
    if (ASSERTS_ENABLED && !(p != p.lca(l))) {
      throw new IllegalStateException(
          String.valueOf("\nexpected: {p,l} are not in the same subtree\n"));
    }

    return true;
  }

  /**
   * Validates the structural integrity of the network simplex data structures.
   *
   * @param g the network simplex to validate.
   * @return true if the tree structure, arc indices, and node degrees are consistent.
   */
  public static boolean checkStructure(NetworkSimplex g) {
    List<Arc> allArcsForDebug = allArcsForDebug(g);
    List<Arc> tree = new ArrayList<>();

    long delCost = collectArcsAndValidate(g, allArcsForDebug, tree);
    int n = g.nodes.length + 1;
    if (ASSERTS_ENABLED && !(n - 1 == tree.size())) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(n - 1 == allArcsForDebug.size() - g.lower.length)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(((Network) g).costOffset == delCost)) {
      throw new IllegalStateException("Assertion failed");
    }

    assertLowerArcsCapacityZero(g);
    assertRootInvariants(g);
    assertThreadAndTreeConsistency(g, tree, n);

    for (Node node : g.nodes) {
      assertNodeDegreeConsistent(node, allArcsForDebug);
    }

    return true;
  }

  private static long collectArcsAndValidate(
      NetworkSimplex g, List<Arc> allArcsForDebug, List<Arc> tree) {
    long delCost = 0L;
    for (Arc arc : allArcsForDebug) {
      if (arc.index == -1) {
        tree.add(arc);
        assertTreeArcParentConsistency(arc);
      } else if (arc.index != -3) {
        assertNonTreeArcConsistency(g, arc);
      } else {
        delCost += arc.longCost();
      }
    }
    return delCost;
  }

  private static void assertTreeArcParentConsistency(Arc arc) {
    Node j = arc.head;
    Node i = arc.sister.head;
    if (i.toParent == arc) {
      if (ASSERTS_ENABLED && !(j == i.parent)) {
        throw new IllegalStateException(
            String.valueOf(MSG_I + i + MSG_J + j + MSG_IJ + arc + "\n"));
      }
    } else {
      if (ASSERTS_ENABLED && !(arc.sister == j.toParent)) {
        throw new IllegalStateException(
            String.valueOf(MSG_I + i + MSG_J + j + MSG_IJ + arc + "\n"));
      }
      if (ASSERTS_ENABLED && !(i == j.parent)) {
        throw new IllegalStateException(
            String.valueOf(MSG_I + i + MSG_J + j + MSG_IJ + arc + "\n"));
      }
    }
  }

  private static void assertNonTreeArcConsistency(NetworkSimplex g, Arc arc) {
    if (ASSERTS_ENABLED && !(arc.index == arc.sister.index)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(0 <= arc.index && arc.index < g.numArcs)) {
      throw new IllegalStateException(String.valueOf(g.numArcs + ", " + arc));
    }
    if (arc.capacity > 0) {
      if (ASSERTS_ENABLED && !(0 == arc.sister.capacity)) {
        throw new IllegalStateException(String.valueOf("\n" + arc));
      }
      if (ASSERTS_ENABLED && !(arc == g.lower[arc.index])) {
        throw new IllegalStateException(String.valueOf("\n" + arc));
      }
    } else if (arc.sister.capacity > 0) {
      if (ASSERTS_ENABLED && !(0 == arc.capacity)) {
        throw new IllegalStateException("Assertion failed");
      }
      if (ASSERTS_ENABLED && !(arc.sister == g.lower[arc.index])) {
        throw new IllegalStateException("Assertion failed");
      }
    } else {
      if (ASSERTS_ENABLED && !(arc.capacity == 0)) {
        throw new IllegalStateException("Assertion failed");
      }
      if (ASSERTS_ENABLED && !(arc.sister.capacity == 0)) {
        throw new IllegalStateException("Assertion failed");
      }
      boolean b1 = arc.sister == g.lower[arc.index];
      boolean b2 = arc == g.lower[arc.index];
      if (ASSERTS_ENABLED && !(b1 ^ b2)) {
        throw new IllegalStateException("Assertion failed");
      }
    }
  }

  private static void assertLowerArcsCapacityZero(NetworkSimplex g) {
    for (int i = 0; i < g.numArcs; i++) {
      Arc arc = g.lower[i];
      if (ASSERTS_ENABLED && !(arc.sister.capacity == 0)) {
        throw new IllegalStateException("Assertion failed");
      }
    }
  }

  private static void assertRootInvariants(NetworkSimplex g) {
    if (ASSERTS_ENABLED && !(g.root.parent == null)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(g.root.toParent == null)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(0 == g.root.balance)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(0 == g.root.potential)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !(0 == g.root.depth)) {
      throw new IllegalStateException("Assertion failed");
    }
  }

  private static void assertThreadAndTreeConsistency(
      NetworkSimplex g, List<Arc> tree, int expectedCount) {
    int x = 1;
    for (Node i = g.root.thread; i != g.root; i = i.thread) {
      x++;
      Node p = i.parent;
      if (ASSERTS_ENABLED && !(p.depth + 1 == i.depth)) {
        throw new IllegalStateException(String.valueOf(MSG_I + i + MSG_P + p + "\n"));
      }
      if (ASSERTS_ENABLED && !(i == i.toParent.sister.head)) {
        throw new IllegalStateException(String.valueOf(MSG_I + i + MSG_P + p + "\n"));
      }
      if (ASSERTS_ENABLED && !(p == i.toParent.head)) {
        throw new IllegalStateException(String.valueOf(MSG_I + i + MSG_P + p + "\n"));
      }
      if (ASSERTS_ENABLED && !(0 == i.toParent.reducedCost())) {
        throw new IllegalStateException(String.valueOf(MSG_I + i + MSG_P + p + "\n"));
      }
      boolean b1 = tree.contains(i.toParent);
      boolean b2 = tree.contains(i.toParent.sister);
      if (ASSERTS_ENABLED && !(b1 ^ b2)) {
        throw new IllegalStateException(String.valueOf(MSG_I + i + MSG_P + p + "\n"));
      }
    }
    if (ASSERTS_ENABLED && !(expectedCount == x)) {
      throw new IllegalStateException("Assertion failed");
    }
  }

  private static void assertNodeDegreeConsistent(Node node, List<Arc> allArcsForDebug) {
    int count = -1;
    for (Arc arc : allArcsForDebug) {
      if (arc.index != NetworkSimplex.DELETED_ARC && (arc.head == node || arc.tail() == node)) {
        count++;
      }
    }
    if (ASSERTS_ENABLED && !(count == node.degree)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (node.degree <= 2) {
      int count2 = 0;
      for (Arc arc : node.adjacencyList) {
        if (arc != null) {
          if (ASSERTS_ENABLED && !((arc.head == node) ^ (arc.tail() == node))) {
            throw new IllegalStateException("Assertion failed");
          }
          if (ASSERTS_ENABLED && !(arc.index != NetworkSimplex.DELETED_ARC)) {
            throw new IllegalStateException("Assertion failed");
          }
          count2++;
        }
      }
      if (ASSERTS_ENABLED && !(count == count2)) {
        throw new IllegalStateException("Assertion failed");
      }
    }
  }

  /**
   * Checks optimality conditions by verifying reduced costs of all arcs.
   *
   * @param g the network simplex to validate.
   * @return true if all arcs satisfy the optimality conditions.
   */
  public static boolean checkOptimality(NetworkSimplex g) {
    StringBuilder s = new StringBuilder();
    for (Arc arc : allArcsForDebug(g)) {
      if (arc.index == -3) {
        continue;
      }

      int reduced = arc.reducedCost();

      if (arc.capacity > 0 && reduced < 0) {
        s.append("\n").append(arc);
      }
      if (arc.sister.capacity > 0 && reduced > 0) {
        s.append("\n").append(arc);
      }
    }
    if (ASSERTS_ENABLED && !(s.isEmpty())) {
      throw new IllegalStateException(String.valueOf("non-optimal arcs:" + s));
    }

    return true;
  }

  /**
   * Validates that the infeasible nodes set is consistent with node delta balances.
   *
   * @param g the network simplex to validate.
   * @return true if the infeasible nodes set matches the actual infeasible nodes.
   */
  public static boolean checkInfeasibleNodes(NetworkSimplex g) {

    for (Node node : g.nodes) {
      if (node.deltaBalance == 0) {
        if (ASSERTS_ENABLED && !(!g.infeasibleNodes.contains(node))) {
          throw new IllegalStateException(String.valueOf("" + node));
        }
      } else {
        if (ASSERTS_ENABLED && !(g.infeasibleNodes.contains(node))) {
          throw new IllegalStateException(String.valueOf("" + node));
        }
      }
    }

    return true;
  }

  /** Forces assertion checking to verify that assertions are enabled in the JVM. */
  @SuppressWarnings("PMD.UnusedLocalVariable")
  public static void forceAsserts() {

    boolean asserts = false;
    if (ASSERTS_ENABLED && !(asserts = true)) {
      throw new IllegalStateException("Assertion failed");
    }
  }

  /**
   * Returns all arcs in the network including artificial arcs, for debugging purposes.
   *
   * @param g the network simplex whose arcs are collected.
   * @return a list containing all arcs and artificial arcs in the network.
   */
  public static List<Arc> allArcsForDebug(NetworkSimplex g) {
    List<Arc> arcs = new ArrayList<>(g.allArcs);
    for (Node node : g.nodes) {
      arcs.add(node.artificial);
    }
    return arcs;
  }
}
