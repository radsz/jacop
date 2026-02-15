/*
 * Mdd.java
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

package org.jacop.util;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;
import java.util.TreeMap;
import lombok.AccessLevel;
import lombok.NoArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntVar;

/**
 * Defines an Mdd as used in the following paper.
 *
 * <p>K.C. Cheng and R.H. Yap, "Maintaining generalized arc consistency on ad-hoc n-ary
 * constraints.", CP 2008.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
@NoArgsConstructor(access = AccessLevel.PROTECTED)
public class Mdd {

  /** It specifies an identifier which denotes a terminal node. */
  public static final int TERMINAL = -1;

  /**
   * It specifies an identifier which denotes lack of the edge for a given value (in the context of
   * the current level (variable) of an Mdd.
   */
  public static final int NOEDGE = 0;

  /** The initial size of the array representing an Mdd. */
  public static final int START_SIZE = 1000;

  private static final boolean DEBUG_ALL = false;

  /** The ordered list of variables participating in Mdd. */
  public IntVar[] vars;

  /** The initial domain limits used to create an Mdd array representation. */
  public int[] domainLimits;

  /**
   * For each node at given index i-th it specifies all possible outgoing edges. If there was no
   * edge for a value of the variable associated to the current node then the entry corresponding to
   * that value is set to NOEDGE. If a given path specifies an allowed tuple than it is terminated
   * with a terminal node.
   */
  public int[] diagram;

  /**
   * It creates index domain views so operations based on indexes of values can be performed
   * efficiently.
   */
  public IndexDomainView[] views;

  /** It specifies the first position in the array which is available for use. */
  public int freePosition;

  List<int[]>[][] same;
  List<Integer>[][] id;
  TreeMap<Integer, Integer> reducedNodes;
  int memorySavings;

  /**
   * It creates and Mdd representation given the list of variables. Tuples must be added manually
   * (addTuple function). After all tuples are added reduce function can be called to reduce Mdd.
   * After reducing Mdd adding tuples is not allowed to maintain cannonic and minimal
   * representation.
   */
  private boolean extendable;

  /**
   * It creates an Mdd. Please note that diagram argument which is potentially a very large array
   * and can be used across many constraints is not copied by the constructor but used directly.
   *
   * @param vars variables involved in this multiple-value decision diagram.
   * @param diagram an int array representation of the diagram.
   * @param domainLimits the limits on the number of values imposed on each variable.
   */
  public Mdd(IntVar[] vars, int[] diagram, int[] domainLimits) {

    this.vars = new IntVar[vars.length];
    System.arraycopy(vars, 0, vars, 0, vars.length);

    this.domainLimits = new int[vars.length];

    this.views = new IndexDomainView[vars.length];

    for (int i = 0; i < vars.length; i++) {
      this.views[i] = new IndexDomainView(vars[i], true);
      assert domainLimits[i] >= vars[i].getSize()
          : i + "-th variable has a size larger than its domain limit size";
      if (domainLimits[i] < vars[i].domain.getSize()) {
        throw new IllegalArgumentException(
            "domain limites are smaller than actual domain of an mdd.");
      }
      this.domainLimits[i] = domainLimits[i];
    }

    this.freePosition = diagram.length;
    this.diagram = diagram;
  }

  /**
   * It creates and Mdd representation given the list of variables and (dis)allowed tuples. Minimum
   * domain limits allows artificially increase the size of the variable domain to make reuse of the
   * same mdd across multiple constraints possible.
   *
   * @param vars variables and their order used in the Mdd.
   * @param minimumDomainLimits it specifies the minimal number of values used for each of the
   *     variables.
   * @param table it specifies the allowed tuples which are being converted into an Mdd.
   */
  public Mdd(IntVar[] vars, int[] minimumDomainLimits, int[][] table) {

    // it needs to transform tuples based on actual values into
    // tuples based on indexes of these values in variables
    // domains.

    // it needs to transform table into Trie, which later will
    // be transformed into Mdd representation. Trie is stored in
    // diagram array.

    this.vars = new IntVar[vars.length];
    System.arraycopy(vars, 0, this.vars, 0, vars.length);

    domainLimits = new int[vars.length];

    views = new IndexDomainView[vars.length];

    for (int i = 0; i < vars.length; i++) {
      views[i] = new IndexDomainView(vars[i], true);
      domainLimits[i] = vars[i].domain.getSize();
      if (domainLimits[i] < minimumDomainLimits[i]) {
        domainLimits[i] = minimumDomainLimits[i];
      }
    }

    freePosition = domainLimits[0];
    diagram = new int[START_SIZE];

    mtree(table);

    // Mtree stored in diagram array is being transformed into Mdd.
    // diagram array is being resized to save on memory.
    reduce();
  }

  /**
   * It creates and Mdd representation given the list of variables and (dis)allowed tuples. Minimum
   * domain limits allows artificially increase the size of the variable domain to make reuse of the
   * same mdd across multiple constraints possible.
   *
   * @param vars variables and their order used in the Mdd.
   * @param table it specifies the allowed tuples which are being converted into an Mdd.
   */
  public Mdd(IntVar[] vars, int[][] table) {

    // it needs to transform tuples based on actual values into
    // tuples based on indexes of these values in variables
    // domains.

    // it needs to transform table into Trie, which later will
    // be transformed into Mdd representation. Trie is stored in
    // diagram array.

    this.vars = new IntVar[vars.length];
    System.arraycopy(vars, 0, this.vars, 0, vars.length);

    domainLimits = new int[vars.length];

    views = new IndexDomainView[vars.length];

    int maxDomainSize = 0;

    for (int i = 0; i < vars.length; i++) {
      views[i] = new IndexDomainView(vars[i], true);
      domainLimits[i] = vars[i].domain.getSize();

      if (maxDomainSize < domainLimits[i]) {
        maxDomainSize = domainLimits[i];
      }
    }

    freePosition = domainLimits[0];

    diagram = new int[table.length * vars.length * maxDomainSize];

    mtree(table);

    // Mtree stored in diagram array is being transformed into Mdd.
    // diagram array is being resized to save on memory.
    reduce();
  }

  /*
   * This function encodes table constraint in the form of a table
   * into an mtree represented using a table
   *
   */

  /**
   * It creates and Mdd representation given the list of variables. The domain limits are set to be
   * equal to the size of the variables domains. The tuples are being added separately one by one.
   *
   * @param vars variables and their order used in the Mdd.
   */
  public Mdd(IntVar[] vars) {

    // it needs to transform tuples based on actual values into
    // tuples based on indexes of these values in variables
    // domains.

    // it needs to transform table into Trie, which later will
    // be transformed into Mdd representation. Trie is stored in
    // diagram array.

    this.vars = new IntVar[vars.length];
    System.arraycopy(vars, 0, this.vars, 0, vars.length);

    domainLimits = new int[vars.length];

    views = new IndexDomainView[vars.length];

    for (int i = 0; i < vars.length; i++) {
      views[i] = new IndexDomainView(vars[i], true);
      domainLimits[i] = vars[i].domain.getSize();
    }

    freePosition = domainLimits[0];
    diagram = new int[START_SIZE];

    extendable = true;

    // Adding tuples and Mdd reduction must be performed separetely.

  }

  /**
   * If possible it will return an Mdd which reuse an array representation of the current Mdd. It
   * returns null if one of the variables supplied has a larger domain then assumed by respective
   * variable from this Mdd. In order to make reuse possible first create Mdd for largest size
   * variables.
   *
   * @param vars array of new variables for which this Mdd is being reused for.
   * @return an Mdd with parts of it reused for new variables.
   */
  public Mdd reuse(IntVar[] vars) {

    Mdd result = new Mdd();

    result.vars = new IntVar[vars.length];
    System.arraycopy(vars, 0, result.vars, 0, vars.length);

    result.domainLimits = new int[vars.length];

    result.views = new IndexDomainView[vars.length];

    for (int i = 0; i < vars.length; i++) {
      result.views[i] = new IndexDomainView(vars[i], true);
      if (domainLimits[i] < vars[i].domain.getSize()) {
        return null;
      }
      result.domainLimits[i] = domainLimits[i];
    }

    result.freePosition = freePosition;
    result.diagram = diagram;

    return result;
  }

  /**
   * Common logic for adding a tuple to the diagram structure.
   *
   * @param tuple the tuple to add
   * @param positions precomputed positions array (can be null, will be computed if needed)
   * @return the final node position after adding the tuple
   */
  private int addTupleToDiagram(int[] tuple, int[] positions) {
    int nodePosition = 0;
    int varNo = 0;

    for (int i = 0; i < tuple.length; i++) {
      int value = tuple[i];
      int indexOfValue;
      if (positions != null && i < positions.length && positions[i] != -1) {
        indexOfValue = positions[i];
      } else {
        indexOfValue = findPosition(value, views[varNo].indexToValue);
      }
      assert indexOfValue != -1;
      nodePosition += indexOfValue;
      varNo++;

      ensureSize(nodePosition + 1);

      if (diagram[nodePosition] == NOEDGE) {
        // new node and path.
        if (varNo == tuple.length) {
          diagram[nodePosition] = TERMINAL;
        } else {
          diagram[nodePosition] = freePosition;
          freePosition += domainLimits[varNo];
          nodePosition = diagram[nodePosition];
        }
      } else {
        nodePosition = diagram[nodePosition];
      }
    }
    return nodePosition;
  }

  /**
   * It allows to add one by one tuple before the reduction of the initial Mdd takes place.
   *
   * @param tuple an allowed tuple being added to Mdd.
   */
  public void addTuple(int[] tuple) {

    assert extendable : "Mdd can not be extended after shrinking operation was performed";

    addTupleToDiagram(tuple, null);
  }

  /**
   * It makes sure that diagram uses an array of at least given size.
   *
   * @param size the size the array must be at least of.
   */
  public void ensureSize(int size) {

    if (diagram.length < size) {

      int[] newDiagram;

      if (diagram.length * 2 < size) {
        newDiagram = new int[size * 2];
      } else {
        newDiagram = new int[diagram.length * 2];
      }

      System.arraycopy(diagram, 0, newDiagram, 0, diagram.length);
      diagram = newDiagram;
    }
  }

  private void shrink() {

    extendable = false;

    int[] range = new int[reducedNodes.size() + 1];
    int[] shift = new int[reducedNodes.size() + 1];

    int shiftPosition = 1;
    int cumulativeShift = 0;

    int[] shrankDiagram = new int[freePosition - memorySavings];

    if (reducedNodes.isEmpty()) {

      System.arraycopy(diagram, 0, shrankDiagram, 0, freePosition);
      diagram = shrankDiagram;
    } else {
      int positionInShrankDiagram = 0;

      int previousShift = 0;

      while (!reducedNodes.isEmpty()) {

        Entry<Integer, Integer> firstEntry = reducedNodes.pollFirstEntry();
        range[shiftPosition] = firstEntry.getKey();

        System.arraycopy(
            diagram,
            range[shiftPosition - 1] + previousShift,
            shrankDiagram,
            positionInShrankDiagram,
            range[shiftPosition] - range[shiftPosition - 1] - previousShift);
        positionInShrankDiagram += range[shiftPosition] - range[shiftPosition - 1] - previousShift;

        previousShift = firstEntry.getValue();
        cumulativeShift += previousShift;
        shift[shiftPosition] = cumulativeShift;
        shiftPosition++;
      }

      if (positionInShrankDiagram < shrankDiagram.length) {
        System.arraycopy(
            diagram,
            range[shiftPosition - 1] + previousShift,
            shrankDiagram,
            positionInShrankDiagram,
            shrankDiagram.length - positionInShrankDiagram);
      }

      for (int i = 0; i < shrankDiagram.length; i++) {

        if (shrankDiagram[i] == TERMINAL || shrankDiagram[i] == NOEDGE) {
          continue;
        }

        int shiftForI = shift[findRange(shrankDiagram[i], range)];
        shrankDiagram[i] -= shiftForI;
      }

      diagram = shrankDiagram;
      freePosition -= memorySavings;
    }
  }

  private void mtree(int[][] table) {

    int[] positions = new int[table[0].length];

    for (int[] tuple : table) {

      assert tuple.length == positions.length : "Tuples have different length.";

      if (!fillPositionsForTuple(tuple, positions)) {
        continue;
      }

      addTuplePathToDiagram(positions, tuple);
    }
  }

  /**
   * Fills positions from tuple; returns false if any value is out of domain (position -1).
   *
   * @param tuple the tuple
   * @param positions array to fill (same length as tuple)
   * @return true if all positions are valid
   */
  private boolean fillPositionsForTuple(int[] tuple, int[] positions) {
    for (int i = 0; i < tuple.length; i++) {
      positions[i] = findPosition(tuple[i], views[i].indexToValue);
      if (positions[i] == -1) {
        return false;
      }
    }
    return true;
  }

  private void addTuplePathToDiagram(int[] positions, int[] tuple) {
    int nodePosition = 0;
    for (int i = 0; i < tuple.length; i++) {

      assert positions[i] != -1
          : "value specified by tuple "
              + List.of(tuple)
              + "for variable no. "
              + i
              + "is already outside its initial domain.";

      nodePosition += positions[i];

      ensureSize(nodePosition + 1);

      if (diagram[nodePosition] == NOEDGE) {
        if (i + 1 == tuple.length) {
          diagram[nodePosition] = TERMINAL;
        } else {
          diagram[nodePosition] = freePosition;
          freePosition += domainLimits[i + 1];
          nodePosition = diagram[nodePosition];
        }
      } else {
        nodePosition = diagram[nodePosition];
      }
    }
  }

  /**
   * Performs binary search on the given array, returning the left and right boundary positions.
   *
   * @param value the value to search for.
   * @param values the array to search in.
   * @return an array of two elements: [left, right] boundary positions after the search.
   */
  private int[] binarySearchBounds(int value, int[] values) {

    int left = 0;
    int right = values.length - 1;

    int position = (left + right) >> 1;

    if (DEBUG_ALL) {
      log.debug("Looking for {}", value);
      for (int v : values) {
        log.debug("val {}", v);
      }
    }

    while (!(left + 1 >= right)) {

      if (DEBUG_ALL) {
        log.debug("left {} right {} position {}", left, right, position);
      }

      if (values[position] > value) {
        right = position;
      } else {
        left = position;
      }

      position = (left + right) >> 1;
    }

    return new int[] {left, right};
  }

  /**
   * It finds a position of a value inside the array.
   *
   * @param value the value being searched.
   * @param values the array in which the value is being searched for.
   * @return position of the value in the array.
   */
  public int findPosition(int value, int[] values) {

    int[] bounds = binarySearchBounds(value, values);

    if (values[bounds[0]] == value) {
      return bounds[0];
    }

    if (values[bounds[1]] == value) {
      return bounds[1];
    }

    return -1;
  }

  /**
   * It finds the position of a value within a range of values using binary search.
   *
   * @param value the value to search for.
   * @param values the array of values to search in.
   * @return the position of the value, or -1 if not found.
   */
  protected int findRange(int value, int[] values) {

    int[] bounds = binarySearchBounds(value, values);

    if (values[bounds[1]] <= value) {
      return bounds[1];
    } else {
      return bounds[0];
    }
  }

  /** It reduces Mdd to minimal canonical form by identifying and merging equivalent nodes. */
  @SuppressWarnings("unchecked")
  public void reduce() {

    reducedNodes = new TreeMap<>();

    same = new ArrayList[vars.length][];
    id = new ArrayList[vars.length][];

    for (int i = 0; i < vars.length; i++) {
      same[i] = new ArrayList[domainLimits[i]];
      id[i] = new ArrayList[domainLimits[i]];
    }

    memorySavings = 0;

    reduce(0, 0);

    shrink();

    same = null;
    id = null;
    reducedNodes = null;
  }

  private int reduce(int node, int level) {

    // Recursive function which going back from bottom to top
    // discovers equal nodes and only keeps one in the representation.
    // This technique allows to reduce Mdd cheaply.

    // The first key ingredient is to find if there is already a node with the
    // same children.

    // The same children means
    // a) nodes must be at the same level
    // b) nodes must have the same number of kids.
    // c) kids must be the same.
    // A three dimensional array - 1st index node level, 2nd index number of kids
    // a third index - kid with a given number. A linear scan through all values of
    // a third index.

    // The second ingredient is to remove dead nodes from the middle of an array.

    int[] nodeChildren = new int[domainLimits[level]];

    int numberOfChildren = -1;
    for (int k = 0; k < domainLimits[level]; k++) {
      if (diagram[node + k] == TERMINAL) {
        nodeChildren[k] = TERMINAL;
        numberOfChildren++;
      } else if (diagram[node + k] != NOEDGE) {
        nodeChildren[k] = reduce(diagram[node + k], level + 1);
        diagram[node + k] = nodeChildren[k];
        numberOfChildren++;
      }
    }

    Integer existingId = findEqualNode(level, numberOfChildren, nodeChildren, node);
    if (existingId != null) {
      return existingId;
    }

    if (same[level][numberOfChildren] == null) {
      same[level][numberOfChildren] = new ArrayList<>();
      id[level][numberOfChildren] = new ArrayList<>();
    }

    id[level][numberOfChildren].add(node);
    same[level][numberOfChildren].add(nodeChildren);

    return node;
  }

  private Integer findEqualNode(int level, int numberOfChildren, int[] nodeChildren, int node) {

    if (same[level][numberOfChildren] == null) {
      return null;
    }
    for (int j = same[level][numberOfChildren].size() - 1; j >= 0; j--) {
      int[] currentNode = same[level][numberOfChildren].get(j);
      boolean equal = true;
      for (int i = currentNode.length - 1; i >= 0; i--) {
        if (currentNode[i] != nodeChildren[i]) {
          equal = false;
          break;
        }
      }
      if (equal) {
        reducedNodes.put(node, domainLimits[level]);
        memorySavings += domainLimits[level];
        return id[level][numberOfChildren].get(j);
      }
    }
    return null;
  }

  /**
   * It checks if the specified tuple is allowed.
   *
   * @param tuple the tuple being checked.
   * @return true if the tuple is allowed, false otherwise.
   */
  public boolean checkIfAllowed(int[] tuple) {

    assert tuple.length == vars.length;

    int position = views[0].indexOfValue(tuple[0]);

    if (position == -1) {
      return false;
    }

    for (int i = 1; i < tuple.length; i++) {
      if (diagram[position] == NOEDGE) {
        return false;
      }
      if (diagram[position] == TERMINAL) {
        return true;
      }
      int delta = views[i].indexOfValue(tuple[i]);
      if (delta == -1) {
        return false;
      }
      position = diagram[position] + delta;
    }

    return diagram[position] == TERMINAL;
  }

  /**
   * Checks if all variables are grounded and their values are allowed by the Mdd.
   *
   * @return true only if all variables are grounded and the values assigned to variables are
   *     allowed by a Mdd.
   */
  public boolean checkIfAllowed() {

    if (!vars[0].singleton()) {
      return false;
    }

    int position = views[0].indexOfValue(vars[0].value());

    for (int i = 1; i < vars.length; i++) {
      if (diagram[position] == NOEDGE) {
        return false;
      }
      if (diagram[position] == TERMINAL) {
        return true;
      }
      if (!vars[i].singleton()) {
        return false;
      }
      int delta = views[i].indexOfValue(vars[i].value());
      position = diagram[position] + delta;
    }

    return diagram[position] == TERMINAL;
  }

  @Override
  public String toString() {

    StringBuilder buffer = new StringBuilder();
    for (int i = 0; i < diagram.length && i < freePosition; i++) {
      buffer.append(diagram[i]).append(" ");
    }

    return buffer.toString().trim();
  }
}
