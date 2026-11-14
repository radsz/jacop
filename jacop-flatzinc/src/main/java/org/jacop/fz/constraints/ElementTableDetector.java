/*
 * ElementTableDetector.java
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

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.TableCliques;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.FzConsole;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Element constraints over constant arrays that share one index variable become one table.
 *
 * <p>MiniZinc flattens a row lookup {@code x[j] = t[row, j]} of a constant matrix into one element
 * constraint per column, all indexed by {@code row} (crosswords: the letters of a word and the word
 * number; cgt: the attributes of a chosen option). Each element is domain consistent on its own,
 * and together they reach the same fixpoint as the table {@code (row, x[1], ..., x[k])}, but
 * through the index domain: a letter loses a value only after every row with that letter has left
 * the index domain, one propagator at a time. Under LCG the reason of that letter value is then one
 * {@code row != i} atom per such row, thousands on a dictionary of words, and the learnt clauses
 * grow to thousands of literals (crosswords grid-05.04: 2,550 on average, 130 nodes per second).
 *
 * <p>The table propagates all columns at once with bit-sets, and its explanation states a removed
 * letter by the other columns' missing values, which the dead rows share. CP-SAT gets the same
 * effect from its shared encoding of the index literals.
 *
 * <p>Groups of at least two such elements are merged; the elements stay in the parse tree for the
 * detectors that read it. The system property {@code org.jacop.fz.elementTable=false} turns it off.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class ElementTableDetector implements ParserTreeConstants {

  /** At most this many rows in one merged table. */
  static final int MAX_ROWS = 1 << 20;

  private final Support support;

  private final Set<SimpleNode> replaced = new HashSet<>();

  private int tables;

  /** One element: value = array[index - first]. */
  private static final class Element {
    private final ASTConstElem node;
    private final int[] array;
    private final int first;
    private final IntVar value;

    Element(ASTConstElem node, int[] array, int first, IntVar value) {
      this.node = node;
      this.array = array;
      this.first = first;
      this.value = value;
    }

    ASTConstElem node() {
      return node;
    }

    int[] array() {
      return array;
    }

    int first() {
      return first;
    }

    IntVar value() {
      return value;
    }
  }

  /**
   * It creates a detector reading variables through the given support.
   *
   * @param support the support of the FlatZinc front end.
   */
  public ElementTableDetector(Support support) {
    this.support = support;
  }

  /**
   * It tells if the detection is on.
   *
   * @return false if the system property org.jacop.fz.elementTable is false.
   */
  public static boolean enabled() {
    return !"false".equalsIgnoreCase(System.getProperty("org.jacop.fz.elementTable"));
  }

  /**
   * The element constraints that a table replaced; they are not posted.
   *
   * @return the constraint nodes of the merged elements.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  /**
   * It scans the constraint items of the model and posts one table for each index variable shared
   * by at least two element constraints over constant arrays.
   *
   * @param astTree the root of the parsed model.
   */
  public void detect(SimpleNode astTree) {
    Map<IntVar, List<Element>> groups = new IdentityHashMap<>();
    List<IntVar> order = new ArrayList<>();
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTCONSTRAINTITEMS) {
        for (int j = 0; j < node.jjtGetNumChildren(); j++) {
          SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
          if (item.getId() == JJTCONSTELEM) {
            collect((ASTConstElem) item, groups, order);
          }
        }
      }
    }
    for (IntVar index : order) {
      List<Element> group = groups.get(index);
      if (group.size() >= 2) {
        merge(index, group);
      }
    }
    if (support.options.debug() && tables > 0) {
      FzConsole.println(
          "% element table detector: " + tables + " tables of " + replaced.size() + " elements");
    }
  }

  private void collect(ASTConstElem node, Map<IntVar, List<Element>> groups, List<IntVar> order) {
    String name = node.getName();
    int first;
    switch (name) {
      case "array_int_element",
          "array_bool_element",
          "array_var_int_element",
          "array_var_bool_element" ->
          first = 1;
      case "jacop_array_var_int_element_nonshifted", "jacop_array_var_bool_element_nonshifted" ->
          first = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(3));
      default -> {
        return;
      }
    }
    IntVar index = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
    if (index.singleton()) {
      return;
    }
    IntVar[] vars = support.getVarArray((SimpleNode) node.jjtGetChild(1));
    int[] array = new int[vars.length];
    for (int k = 0; k < vars.length; k++) {
      if (!vars[k].singleton()) {
        return;
      }
      array[k] = vars[k].value();
    }
    IntVar value = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
    List<Element> group = groups.get(index);
    if (group == null) {
      group = new ArrayList<>();
      groups.put(index, group);
      order.add(index);
    }
    group.add(new Element(node, array, first, value));
  }

  private void merge(IntVar index, List<Element> group) {
    if (index.getSize() > MAX_ROWS) {
      return;
    }
    // the columns: each distinct value variable once, then the index; a variable met again (or the
    // index itself as a value) keeps only the rows where both arrays agree. The index goes last
    // because the explanation prefers the first column among equally cheap ones, and the values'
    // atoms are shared by many rows where the index has one atom per row.
    Map<IntVar, Integer> column = new LinkedHashMap<>();
    int[] columnOf = new int[group.size()];
    for (int e = 0; e < group.size(); e++) {
      IntVar v = group.get(e).value();
      if (v == index) {
        columnOf[e] = -1;
        continue;
      }
      Integer c = column.get(v);
      if (c == null) {
        c = column.size();
        column.put(v, c);
      }
      columnOf[e] = c;
    }
    int last = column.size();
    for (int e = 0; e < group.size(); e++) {
      if (columnOf[e] < 0) {
        columnOf[e] = last;
      }
    }
    column.put(index, last);
    IntVar[] vars = column.keySet().toArray(new IntVar[0]);
    List<int[]> rows = new ArrayList<>(index.getSize());
    for (ValueEnumeration en = index.dom().valueEnumeration(); en.hasMoreElements(); ) {
      int[] row = row(en.nextElement(), group, columnOf, vars.length);
      if (row != null) {
        rows.add(row);
      }
    }
    if (rows.isEmpty()) {
      throw Store.failException;
    }
    int[][] tuples = rows.toArray(new int[0][]);
    if (vars.length <= TableCliques.MAX_ARITY) {
      // for the linear relaxation: the results of the elements over the columns of the index
      support.dictionary.addTable(vars, tuples);
    }
    support.pose(new HybridTable(vars, tuples));
    for (Element e : group) {
      replaced.add(e.node());
    }
    tables++;
  }

  /**
   * The row of index value i, the index in the last column, or null when an array has no entry i or
   * two entries of one column disagree.
   */
  private static int[] row(int i, List<Element> group, int[] columnOf, int arity) {
    int[] row = new int[arity];
    boolean[] set = new boolean[arity];
    row[arity - 1] = i;
    set[arity - 1] = true;
    for (int e = 0; e < group.size(); e++) {
      Element el = group.get(e);
      long k = (long) i - el.first();
      if (k < 0 || k >= el.array().length) {
        return null;
      }
      int v = el.array()[(int) k];
      int c = columnOf[e];
      if (set[c] && row[c] != v) {
        return null;
      }
      row[c] = v;
      set[c] = true;
    }
    return row;
  }
}
