/*
 * ExtensionalSupportMdd.java
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

package org.jacop.constraints;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.VarMap;
import org.jacop.constraints.regular.LayeredGraphConstraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.util.Mdd;

/**
 * Extensional constraint assures that one of the tuples is enforced in the relation. The relation
 * is given as a multi-valued decision diagram (MDD), either an {@link Mdd} built from a table or a
 * layered graph given by its nodes and labelled edges as in the MiniZinc {@code mdd} and {@code
 * mdd_nondet} constraints.
 *
 * <p>The diagram is propagated as a layered graph by {@link LayeredGraphConstraint}, which achieves
 * generalized arc consistency incrementally: a removed value only visits the edges labelled with it
 * and the edges of nodes that lose all their incoming or outgoing edges, and backtracking restores
 * only the counters that changed. This replaces the earlier mddc algorithm (Cheng and Yap, CP
 * 2008), which searched the whole remaining diagram at every call.
 *
 * <p>The variables must be different, except for singleton variables.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ExtensionalSupportMdd extends LayeredGraphConstraint
    implements SatisfiedPresent, Copyable<ExtensionalSupportMdd> {

  /** It specifies if the debugging information is printed. */
  public static final boolean DEBUG_ALL = false;

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The ways in which the diagram can be propagated. */
  public enum Propagation {
    /** The incremental counters or support search, chosen by timing both during the search. */
    AUTO,
    /** Counters of alive edges per node, updated incrementally and trailed. */
    INCREMENTAL,
    /** A depth first search for supports at every call, as in the mddc algorithm. */
    SUPPORT_SEARCH
  }

  private Propagation propagation = Propagation.AUTO;

  // With AUTO the diagram starts with the counters and may switch to support search once both have
  // been timed on the same calls, see LayeredGraphConstraint.

  /** It specifies a multiple value decision diagram used by this constraint, or null. */
  private final Mdd mdd;

  // The diagram in the MiniZinc form, used when mdd is null: the level (1-based) of each node
  // 1..N and, for each edge, its source node, its label and its target node, where 0 is the
  // terminal node.
  private final int[] nodeLevel;
  private final int[] from;
  private final IntDomain[] label;
  private final int[] to;

  /**
   * It creates an extensional constraint.
   *
   * @param diagram multiple-valued decision diagram describing allowed tuples.
   */
  public ExtensionalSupportMdd(Mdd diagram) {
    super(checkedVars(diagram), 1);
    this.mdd = diagram;
    this.nodeLevel = null;
    this.from = null;
    this.label = null;
    this.to = null;
    numberId = idNumber.incrementAndGet();
  }

  private static IntVar[] checkedVars(Mdd diagram) {
    if (diagram == null || diagram.vars == null || diagram.views == null) {
      throw new IllegalArgumentException("Constraint ExtensionalSupportMdd has null diagram");
    }
    return diagram.vars;
  }

  /**
   * It constructs extensional support constraint. Please note that parameters will be stored
   * internally as references until the impose of the constraint takes place. Changing parameters
   * after constructing the constraint and before its imposition will change the constraint too.
   *
   * @param vars the variables in the scope of the constraint.
   * @param table list of tuples which are allowed.
   */
  public ExtensionalSupportMdd(IntVar[] vars, int[][] table) {
    this(new Mdd(vars, table));
  }

  /**
   * It constructs an MDD constraint from a layered graph as in the MiniZinc {@code mdd} and {@code
   * mdd_nondet} constraints. Node 1 is the root and node 0 the terminal node. An assignment is
   * allowed when it labels a path from the root to the terminal node. The diagram may be
   * non-deterministic, that is several edges leaving a node may share values.
   *
   * @param vars the variables, the i-th of them labels the edges leaving the nodes of level i + 1.
   * @param level the level of each node 1..N, from 1 (the root) to vars.length; level[n - 1] is the
   *     level of node n.
   * @param from the source node (1..N) of each edge.
   * @param label the values of each edge.
   * @param to the target node (0..N, where 0 is the terminal node) of each edge.
   */
  public ExtensionalSupportMdd(
      IntVar[] vars, int[] level, int[] from, IntDomain[] label, int[] to) {
    super(vars, 1);
    if (level == null || from == null || label == null || to == null) {
      throw new IllegalArgumentException("Constraint ExtensionalSupportMdd has null arguments");
    }
    checkInputForNullness("label", label);
    if (from.length != label.length || from.length != to.length) {
      throw new IllegalArgumentException(
          "Constraint ExtensionalSupportMdd has from, label and to of different lengths");
    }
    int nodes = level.length;
    if (nodes > 0 && level[0] != 1) {
      throw new IllegalArgumentException(
          "Constraint ExtensionalSupportMdd has root not at level 1");
    }
    for (int e = 0; e < from.length; e++) {
      if (from[e] < 1 || from[e] > nodes || to[e] < 0 || to[e] > nodes) {
        throw new IllegalArgumentException(
            "Constraint ExtensionalSupportMdd has edge " + (e + 1) + " outside nodes 1.." + nodes);
      }
      int targetLevel = to[e] == 0 ? vars.length + 1 : level[to[e] - 1];
      if (level[from[e] - 1] < 1 || level[from[e] - 1] + 1 != targetLevel) {
        throw new IllegalArgumentException(
            "Constraint ExtensionalSupportMdd has edge "
                + (e + 1)
                + " that does not go from a level to the next one");
      }
    }
    this.mdd = null;
    this.nodeLevel = Arrays.copyOf(level, level.length);
    this.from = Arrays.copyOf(from, from.length);
    this.label = Arrays.copyOf(label, label.length);
    this.to = Arrays.copyOf(to, to.length);
    numberId = idNumber.incrementAndGet();
  }

  @Override
  protected void describeGraph(LayeredGraphDescription graph) {
    if (mdd != null) {
      describeMdd(graph);
    } else {
      describeEdges(graph);
    }
  }

  /**
   * It describes the diagram of an {@link Mdd}. A node of level i is a block of domainLimits[i]
   * entries of the diagram array, the k-th of which holds the child for the k-th value of the i-th
   * variable, NOEDGE or TERMINAL.
   */
  private void describeMdd(LayeredGraphDescription graph) {
    int levels = list.length;
    if (levels == 0) {
      graph.setNodes(0, 1);
      return;
    }
    int[] diagram = mdd.diagram;
    int[] localId = new int[Math.max(mdd.freePosition, diagram.length)];
    Arrays.fill(localId, -1);
    int[] current = {0};
    int currentSize = 1;
    int[] next = new int[16];
    graph.setNodes(0, 1);
    localId[0] = 0;
    for (int level = 0; level < levels; level++) {
      int[] indexToValue = mdd.views[level].indexToValue;
      int width = Math.min(mdd.domainLimits[level], indexToValue.length);
      boolean last = level == levels - 1;
      int nextSize = 0;
      // Edges of this level are added once the next level knows its node count, so they are
      // collected first.
      int[] edges = new int[16];
      int edgeCount = 0;
      for (int n = 0; n < currentSize; n++) {
        int node = current[n];
        for (int k = 0; k < width; k++) {
          int child = diagram[node + k];
          if (child == Mdd.NOEDGE) {
            continue;
          }
          int target;
          if (last) {
            if (child != Mdd.TERMINAL) {
              throw new IllegalArgumentException(
                  "Constraint ExtensionalSupportMdd has a diagram longer than its variables");
            }
            target = 0;
          } else {
            if (child == Mdd.TERMINAL) {
              throw new IllegalArgumentException(
                  "Constraint ExtensionalSupportMdd has a diagram shorter than its variables");
            }
            if (localId[child] < 0) {
              if (nextSize == next.length) {
                next = Arrays.copyOf(next, 2 * nextSize);
              }
              localId[child] = nextSize;
              next[nextSize++] = child;
            }
            target = localId[child];
          }
          if (3 * edgeCount + 3 > edges.length) {
            edges = Arrays.copyOf(edges, 2 * edges.length);
          }
          edges[3 * edgeCount] = localId[node];
          edges[3 * edgeCount + 1] = indexToValue[k];
          edges[3 * edgeCount + 2] = target;
          edgeCount++;
        }
      }
      graph.setNodes(level + 1, last ? 1 : nextSize);
      for (int e = 0; e < edgeCount; e++) {
        graph.addEdge(level, edges[3 * e], edges[3 * e + 1], edges[3 * e + 2]);
      }
      int[] swap = current;
      current = next;
      next = swap.length >= 16 ? swap : new int[16];
      currentSize = nextSize;
    }
  }

  /** It describes the diagram given in the MiniZinc form. Only node 1 is a root. */
  private void describeEdges(LayeredGraphDescription graph) {
    int levels = list.length;
    int[] localId = new int[nodeLevel.length + 1];
    int[] levelCount = new int[levels + 1];
    localId[0] = 0;
    levelCount[levels] = 1;
    if (nodeLevel.length > 0) {
      localId[1] = 0;
      levelCount[0] = 1;
    }
    for (int n = 2; n <= nodeLevel.length; n++) {
      int level = nodeLevel[n - 1] - 1;
      localId[n] = level >= 1 && level < levels ? levelCount[level]++ : -1;
    }
    for (int level = 0; level <= levels; level++) {
      graph.setNodes(level, levelCount[level]);
    }
    for (int e = 0; e < from.length; e++) {
      int level = nodeLevel[from[e] - 1] - 1;
      int source = localId[from[e]];
      int target = localId[to[e]];
      if (source < 0 || target < 0 || (level == 0 && from[e] != 1)) {
        continue;
      }
      for (ValueEnumeration v = label[e].valueEnumeration(); v.hasMoreElements(); ) {
        graph.addEdge(level, source, v.nextElement(), target);
      }
    }
  }

  /**
   * It sets how the diagram is propagated. It must be called before the constraint is imposed.
   *
   * @param propagation the propagation to use.
   */
  public void setPropagation(Propagation propagation) {
    this.propagation = propagation;
  }

  @Override
  protected Engine defaultEngine() {
    return switch (propagation) {
      case INCREMENTAL -> Engine.COUNTERS;
      case SUPPORT_SEARCH -> Engine.SUPPORT_SEARCH;
      case AUTO -> Engine.AUTO;
    };
  }

  @Override
  public boolean satisfied() {
    return groundAssignmentAllowed();
  }

  @Override
  protected boolean explainedByPaths() {
    return getClass() == ExtensionalSupportMdd.class;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : extensionalSupportMDD( ");

    for (IntVar v : list) {
      result.append(v).append(" ");
    }

    if (mdd != null) {
      result.append(")").append("size = ").append(mdd.freePosition);
    } else {
      result.append(")").append("nodes = ").append(nodeLevel.length);
      result.append(", edges = ").append(from.length);
    }

    result.append(")\n");

    return result.toString();
  }

  @Override
  public ExtensionalSupportMdd copy(VarMap map) {
    ExtensionalSupportMdd copy =
        mdd != null
            ? new ExtensionalSupportMdd(mdd.copyOver(map.get(mdd.vars)))
            : new ExtensionalSupportMdd(map.get(list), nodeLevel, from, label, to);
    copy.propagation = propagation;
    copyEngineTo(copy);
    return copy;
  }
}
