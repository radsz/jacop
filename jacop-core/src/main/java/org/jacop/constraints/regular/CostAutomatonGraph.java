/*
 * CostAutomatonGraph.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2026 Radoslaw Szymanek
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

package org.jacop.constraints.regular;

import java.util.Arrays;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;

/**
 * A deterministic finite automaton with transition costs unfolded over a word into a layered graph,
 * shared by {@link CostRegular} and {@link MultiCostRegular}. A forward pass collects the states
 * reachable at each level, a backward pass keeps the states from which a final state can be
 * reached, and the edges between kept states are created level by level. Each edge keeps the state
 * and the symbol of its transition, so a constraint can look up its costs.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class CostAutomatonGraph {

  /** Nodes of level l are levelNodeStart[l]..levelNodeStart[l+1]-1; node 0 is the source. */
  final int[] levelNodeStart;

  /** Edges of level l are edgeStart[l]..edgeStart[l+1]-1. */
  final int[] edgeStart;

  /**
   * The values labelling edges of level l are slotValue[levelSlotStart[l]..levelSlotStart[l+1]-1].
   */
  final int[] levelSlotStart;

  final int[] slotValue;

  final int[] edgeSource;
  final int[] edgeTarget;
  final int[] edgeSlot;
  final int[] edgeState;
  final int[] edgeSymbol;

  /**
   * It unfolds the automaton over the current domains of the word.
   *
   * @param list the variables whose values form the word.
   * @param transition the successor of state q on value firstValue + j is transition[q][j], or -1.
   * @param firstValue the value of the first column of transition.
   * @param initialState the initial state.
   * @param finalStates the accepting states.
   */
  CostAutomatonGraph(
      IntVar[] list, int[][] transition, int firstValue, int initialState, int[] finalStates) {
    int levels = list.length;
    int states = transition.length;
    int symbols = transition[0].length;

    boolean[] accepting = new boolean[states];
    for (int q : finalStates) {
      accepting[q] = true;
    }

    // Values of each level that are in the domain and in the alphabet.
    int[][] values = new int[levels][];
    for (int level = 0; level < levels; level++) {
      IntDomain dom = list[level].dom();
      int[] buffer = new int[Math.max(0, Math.min(dom.getSize(), symbols))];
      int count = 0;
      for (var e = dom.valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        if (v >= firstValue && (long) v - firstValue < symbols) {
          buffer[count++] = v - firstValue;
        }
      }
      values[level] = Arrays.copyOf(buffer, count);
    }

    // Forward pass: states reachable at each level.
    int[][] reachable = new int[levels + 1][];
    boolean[] marked = new boolean[states];
    int[] buffer = new int[states];
    reachable[0] = new int[] {initialState};
    for (int level = 0; level < levels; level++) {
      int count = 0;
      for (int q : reachable[level]) {
        for (int j : values[level]) {
          int t = transition[q][j];
          if (t >= 0 && !marked[t] && (level < levels - 1 || accepting[t])) {
            marked[t] = true;
            buffer[count++] = t;
          }
        }
      }
      reachable[level + 1] = Arrays.copyOf(buffer, count);
      for (int i = 0; i < count; i++) {
        marked[buffer[i]] = false;
      }
    }
    if (levels == 0 && !accepting[initialState]) {
      reachable[0] = new int[0];
    }

    // Backward pass: keep the states with a transition to a kept state of the next level.
    int[][] kept = new int[levels + 1][];
    kept[levels] = reachable[levels];
    int[] position = new int[states];
    Arrays.fill(position, -1);
    for (int level = levels - 1; level >= 0; level--) {
      for (int i = 0; i < kept[level + 1].length; i++) {
        position[kept[level + 1][i]] = i;
      }
      int count = 0;
      for (int q : reachable[level]) {
        for (int j : values[level]) {
          int t = transition[q][j];
          if (t >= 0 && position[t] >= 0) {
            buffer[count++] = q;
            break;
          }
        }
      }
      kept[level] = Arrays.copyOf(buffer, count);
      for (int t : kept[level + 1]) {
        position[t] = -1;
      }
    }

    levelNodeStart = new int[levels + 2];
    for (int level = 0; level <= levels; level++) {
      levelNodeStart[level + 1] = levelNodeStart[level] + kept[level].length;
    }

    // Edges and slots, level by level.
    edgeStart = new int[levels + 1];
    levelSlotStart = new int[levels + 1];
    int[][] edges = new int[5][16];
    int edgeCount = 0;
    int[] slots = new int[16];
    int slotCount = 0;
    int[] slotOf = new int[symbols];
    for (int level = 0; level < levels; level++) {
      edgeStart[level] = edgeCount;
      levelSlotStart[level] = slotCount;
      for (int i = 0; i < kept[level + 1].length; i++) {
        position[kept[level + 1][i]] = i;
      }
      Arrays.fill(slotOf, -1);
      // Slots in increasing order of values.
      for (int j : values[level]) {
        boolean used = false;
        for (int q : kept[level]) {
          int t = transition[q][j];
          if (t >= 0 && position[t] >= 0) {
            used = true;
            break;
          }
        }
        if (used) {
          if (slotCount == slots.length) {
            slots = Arrays.copyOf(slots, 2 * slotCount);
          }
          slotOf[j] = slotCount;
          slots[slotCount++] = firstValue + j;
        }
      }
      for (int i = 0; i < kept[level].length; i++) {
        int q = kept[level][i];
        for (int j : values[level]) {
          int t = transition[q][j];
          if (t < 0 || position[t] < 0) {
            continue;
          }
          if (edgeCount == edges[0].length) {
            for (int k = 0; k < edges.length; k++) {
              edges[k] = Arrays.copyOf(edges[k], 2 * edgeCount);
            }
          }
          edges[0][edgeCount] = levelNodeStart[level] + i;
          edges[1][edgeCount] = levelNodeStart[level + 1] + position[t];
          edges[2][edgeCount] = slotOf[j];
          edges[3][edgeCount] = q;
          edges[4][edgeCount] = j;
          edgeCount++;
        }
      }
      for (int t : kept[level + 1]) {
        position[t] = -1;
      }
    }
    edgeStart[levels] = edgeCount;
    levelSlotStart[levels] = slotCount;

    edgeSource = Arrays.copyOf(edges[0], edgeCount);
    edgeTarget = Arrays.copyOf(edges[1], edgeCount);
    edgeSlot = Arrays.copyOf(edges[2], edgeCount);
    edgeState = Arrays.copyOf(edges[3], edgeCount);
    edgeSymbol = Arrays.copyOf(edges[4], edgeCount);
    slotValue = Arrays.copyOf(slots, slotCount);
  }

  /** The number of nodes. */
  int nodes() {
    return levelNodeStart[levelNodeStart.length - 1];
  }

  /** The number of edges. */
  int edges() {
    return edgeSource.length;
  }

  /** The numbers of edges of each level. */
  int[] edgesPerLevel() {
    int[] result = new int[edgeStart.length - 1];
    for (int level = 0; level < result.length; level++) {
      result[level] = edgeStart[level + 1] - edgeStart[level];
    }
    return result;
  }

  /**
   * It appends the word and the automaton of a cost regular constraint to its description.
   *
   * @param result the description so far, ending with the constraint's id.
   * @param list the word.
   * @param transition the transition table.
   * @param firstValue the value of the first column.
   * @param initialState the initial state.
   * @param finalStates the accepting states.
   * @return result.
   */
  static StringBuilder describe(
      StringBuilder result,
      IntVar[] list,
      int[][] transition,
      int firstValue,
      int initialState,
      int[] finalStates) {
    result.append("([");
    for (int i = 0; i < list.length; i++) {
      result.append(list[i].id()).append(i + 1 < list.length ? ", " : "");
    }
    result.append("], transition=").append(Arrays.deepToString(transition));
    result.append(", firstValue=").append(firstValue);
    result.append(", initialState=").append(initialState);
    result.append(", finalStates=").append(Arrays.toString(finalStates));
    return result;
  }

  /**
   * It checks the automaton and the costs of a cost regular constraint.
   *
   * @param name the constraint named in the messages.
   * @param length the length of the word.
   * @param transition the transition table.
   * @param firstValue the value of the first column.
   * @param initialState the initial state.
   * @param finalStates the accepting states.
   * @param costs the cost matrices, one per position of the word.
   * @throws IllegalArgumentException if a state, a row or a matrix is out of shape.
   */
  static void check(
      String name,
      int length,
      int[][] transition,
      int firstValue,
      int initialState,
      int[] finalStates,
      int[][][] costs) {
    int states = transition.length;
    if (states == 0) {
      throw new IllegalArgumentException(name + ": the automaton has no states");
    }
    int symbols = transition[0] == null ? 0 : transition[0].length;
    if (initialState < 0 || initialState >= states) {
      throw new IllegalArgumentException(
          name + ": initial state " + initialState + " is not a state");
    }
    for (int q : finalStates) {
      if (q < 0 || q >= states) {
        throw new IllegalArgumentException(name + ": final state " + q + " is not a state");
      }
    }
    for (int[] row : transition) {
      if (row == null || row.length != symbols) {
        throw new IllegalArgumentException(name + ": transition rows must have equal lengths");
      }
      for (int t : row) {
        if (t < -1 || t >= states) {
          throw new IllegalArgumentException(name + ": transition to " + t + " is not a state");
        }
      }
    }
    if (costs == null || costs.length != length) {
      throw new IllegalArgumentException(name + ": costs must have one matrix per variable");
    }
    for (int[][] matrix : costs) {
      if (matrix == null || matrix.length != states) {
        throw new IllegalArgumentException(name + ": costs must have a row per state");
      }
      for (int[] row : matrix) {
        if (row == null || row.length != symbols) {
          throw new IllegalArgumentException(name + ": costs must have a column per value");
        }
      }
    }
    if ((long) firstValue + symbols - 1 > IntDomain.MAX_INT) {
      throw new IllegalArgumentException(name + ": values out of range");
    }
  }
}
