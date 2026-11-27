/*
 * ArgumentCheck.java
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

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import org.jacop.core.IntDomain;
import org.jacop.fz.ASTConstElem;
import org.jacop.fz.ASTScalarFlatExpr;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * Checks the sizes of the arguments of the built-ins as each constraint is read, after its types:
 * the numbers of rows, columns, vectors, dimensions, nodes or states that a flattened array must
 * fit. A model that breaks them is an error of the model (an IllegalArgumentException, printed as
 * %% Error:), as MiniZinc reports it with its assertions; the generators and the detectors that
 * read the constraints before them assume the sizes agree.
 */
public final class ArgumentCheck implements ParserTreeConstants {

  private interface Rule {
    void check(Arguments a);
  }

  private static final Map<String, Rule> RULES = new HashMap<>();

  // the arrays whose elements a predicate pairs (the weights and variables of a linear row, the
  // starts, durations and resources of tasks, values and counts) are checked to be of one length
  // with the types of the arguments, by org.jacop.fz.ConstraintArguments as each constraint is
  // read; the rules here check the sizes that other arguments give

  static {
    // flattened matrices: the number of vectors, lists, rows or columns must divide the array
    // (jacop_lex_chain_less_int with a negative number is left to the generator)
    rule(a -> a.parts(0, a.intArg(1), null, a.intArg(1) + " vectors"), "jacop_lex_chain_less_int");
    rule(
        a -> a.parts(0, a.intArg(1), "vectors", a.intArg(1) + " vectors"),
        "jacop_lex_chain_less_bool",
        "jacop_lex_chain_lesseq_int",
        "jacop_lex_chain_lesseq_bool");
    rule(
        a -> {
          int rows = a.intArg(1);
          int length = a.parts(0, rows, "lists", rows + " lists");
          if (a.count() > 2 && rows > 0) {
            a.parts(2, length, null, "excluded tuples of length " + length);
          }
        },
        "jacop_all_different_lists",
        "jacop_all_different_lists_except");
    rule(
        a -> {
          int columns = a.intArg(1);
          int rows = a.parts(0, columns, "columns", "rows of " + columns + " columns");
          a.size(2, rows, "row_count", "one count per row");
          a.size(3, columns, "col_count", "one count per column");
        },
        "jacop_symmetric_gcc");
    rule(
        a -> {
          int columns = a.intArg(1);
          int rows = a.parts(0, columns, "columns", "rows of " + columns + " columns");
          int values = a.length(2);
          if (values >= 0) {
            a.size(3, (long) rows * values, "row_count", "one count per row and value");
            a.size(4, (long) columns * values, "col_count", "one count per column and value");
          }
        },
        "jacop_cardinality_matrix");
    rule(
        a -> {
          int k = a.intArg(2);
          a.parts(0, k, "dimensions", "boxes of " + k + " dimensions");
          if (k == 0) {
            // a box has at least one dimension (as ConstraintArguments read it, rejecting k < 1)
            a.fail("the number of dimensions is not positive");
          }
        },
        "jacop_diffn_k");

    // a Boolean per value of the set
    rule(a -> a.size(1, a.set(2).getSize(), "b", "one Boolean per value"), "jacop_channel");

    // tables: tuples of one value per variable
    rule(
        a -> {
          int n = a.length(0);
          a.parts(1, Math.max(0, n), null, "tuples of " + n + " values");
        },
        "jacop_table_int",
        "jacop_table_bool",
        "jacop_table_int_reif",
        "jacop_table_bool_reif",
        "jacop_table_int_imp",
        "jacop_table_bool_imp",
        "jacop_negative_table_int",
        "jacop_short_table_int");

    // a network: two nodes per arc, numbered from 1 or from the lowest node of the arcs
    rule(
        a -> {
          a.size(0, 2L * Math.max(0, a.length(1)), "arc", "two nodes per flow");
          int[] arc = a.ints(0);
          int nodes = a.length(3);
          if (arc != null && arc.length > 0 && nodes >= 0) {
            int first = Math.min(1, Arrays.stream(arc).min().getAsInt());
            for (int node : arc) {
              if ((long) node - first >= nodes) {
                a.fail("the node " + node + " has no balance");
              }
            }
          }
        },
        "jacop_networkflow");

    // geost: k dimensions, boxes of k sizes and offsets, objects of k coordinates and a kind, and
    // shapes made of boxes
    rule(ArgumentCheck::geost, "jacop_geost");
    rule(
        a -> {
          geost(a);
          int k = a.intArg(0);
          a.size(6, k, "l", "one bound per dimension");
          a.size(7, k, "u", "one bound per dimension");
        },
        "jacop_geost_bb");

    // automata: states 1..Q, a transition table of Q rows, next states in 0..Q (0 fails)
    rule(a -> a.automaton(a.intArg(2), true), "jacop_regular");
    rule(a -> a.automaton(a.set(2).getSize(), true), "jacop_regular_set");
    rule(
        a -> {
          a.automaton(a.intArg(2), true);
          a.size(6, (long) a.intArg(1) * a.intArg(2), "the cost table", "one cost per transition");
        },
        "jacop_cost_regular");
    rule(
        a -> {
          int columns = a.intArg(8);
          if (columns < 0) {
            a.fail("the number of symbols is negative");
          }
          a.automaton(columns, false);
        },
        "jacop_regular_nfa");
  }

  private ArgumentCheck() {}

  /**
   * Checks the sizes of the arguments of one constraint item, as it is read: the item is at hand,
   * and the parameters and arrays it names are declared before it.
   *
   * @param support the support of the model, with its parameters and arrays declared
   * @param constraintItem the constraint item, whose first child is the call
   * @throws IllegalArgumentException when the sizes of the arguments of the constraint do not agree
   */
  public static void check(Support support, SimpleNode constraintItem) {
    if (constraintItem.jjtGetChild(0) instanceof ASTConstElem call && call.getName() != null) {
      Rule rule = RULES.get(call.getName());
      if (rule != null) {
        rule.check(new Arguments(support, call.getName(), call));
      }
    }
  }

  private static void geost(Arguments a) {
    int k = a.intArg(0);
    a.sameLength("the sizes and the offsets of the boxes", 1, 2);
    int boxes = a.parts(1, k, "dimensions", "boxes of " + k + " dimensions");
    int objects = a.parts(4, k, "dimensions", "objects of " + k + " dimensions");
    a.size(5, objects, "kind", "one kind per object");
    IntDomain[] shapes = a.sets(3);
    if (shapes != null && a.length(1) >= 0) {
      for (int s = 0; s < shapes.length; s++) {
        if (shapes[s].isEmpty() || shapes[s].min() < 1 || shapes[s].max() > boxes) {
          a.fail("the shape " + (s + 1) + " is not a set of boxes 1.." + boxes);
        }
      }
    }
  }

  private static void rule(Rule rule, String... names) {
    for (String name : names) {
      RULES.put(name, rule);
    }
  }

  /** The arguments of one constraint. */
  private static final class Arguments {
    private final Support support;
    private final String name;
    private final SimpleNode node;

    Arguments(Support support, String name, SimpleNode node) {
      this.support = support;
      this.name = name;
      this.node = node;
    }

    int count() {
      return node.jjtGetNumChildren();
    }

    SimpleNode arg(int i) {
      return (SimpleNode) node.jjtGetChild(i);
    }

    // the length of an array argument, -1 when it is not an array this check knows
    int length(int i) {
      SimpleNode a = arg(i);
      if (a.getId() == JJTARRAYLITERAL) {
        return a.jjtGetNumChildren();
      }
      if (a.getId() != JJTSCALARFLATEXPR || ((ASTScalarFlatExpr) a).getType() != 2) {
        return -1;
      }
      return support.dictionary.arrayLength(((ASTScalarFlatExpr) a).getIdent());
    }

    int intArg(int i) {
      return support.getInt((ASTScalarFlatExpr) arg(i));
    }

    // the integers of an array argument, null when it is not an array of integers
    int[] ints(int i) {
      try {
        return support.getIntArray(arg(i));
      } catch (IllegalArgumentException _) {
        return null;
      }
    }

    void fail(String what) {
      throw new IllegalArgumentException(name + ": " + what);
    }

    /**
     * Checks that array i splits into parts of equal length, as a flattened matrix does.
     *
     * @param i the array
     * @param k the number of parts, or their length
     * @param negative what k counts, for the message when it is negative; null to leave a negative
     *     k unchecked
     * @param parts what the parts are, for the message when k does not divide the array
     * @return the length of the array divided by k, 0 when k is 0 or not checked
     */
    int parts(int i, int k, String negative, String parts) {
      int n = length(i);
      if (n < 0 || k < 0 && negative == null) {
        return 0;
      }
      if (k < 0) {
        fail("the number of " + negative + " is negative");
      }
      if (k == 0 ? n != 0 : n % k != 0) {
        fail(n + " elements do not split into " + parts);
      }
      return k == 0 ? 0 : n / k;
    }

    // the sets of an array argument, null when it is not an array of sets
    IntDomain[] sets(int i) {
      try {
        return support.getSetArray(arg(i));
      } catch (IllegalArgumentException _) {
        return null;
      }
    }

    IntDomain set(int i) {
      return support.getSetLiteral(node, i);
    }

    /**
     * Checks an automaton (x, Q, S, d, q0, F, ...) with Q states, a table d of Q rows of the given
     * number of columns, and the start state q0 among the states.
     *
     * @param columns the number of symbols, the columns of d
     * @param dfa whether d holds next states, which must be states or 0, and F must hold states
     */
    void automaton(int columns, boolean dfa) {
      int states = intArg(1);
      if (states <= 0) {
        fail("the number of states is not positive");
      }
      if (dfa && columns <= 0) {
        fail("the number of symbols is not positive");
      }
      size(
          3,
          (long) states * columns,
          "the transition table",
          states + " x " + columns + " entries");
      int start = intArg(4);
      if (start < 1 || start > states) {
        fail("the start state " + start + " is not a state 1.." + states);
      }
      if (!dfa) {
        return;
      }
      int[] d = ints(3);
      if (d != null) {
        for (int next : d) {
          if (next < 0 || next > states) {
            fail("the next state " + next + " is not a state 0.." + states);
          }
        }
      }
      IntDomain finalStates = set(5);
      if (!finalStates.isEmpty() && (finalStates.min() < 1 || finalStates.max() > states)) {
        fail("a final state is not a state 1.." + states);
      }
    }

    void size(int i, long expected, String array, String what) {
      int n = length(i);
      if (n >= 0 && n != expected) {
        fail(array + " has " + n + " elements, not " + what);
      }
    }

    void sameLength(String what, int... args) {
      int first = -1;
      for (int i : args) {
        int n = length(i);
        if (n < 0) {
          continue;
        }
        if (first < 0) {
          first = n;
        } else if (n != first) {
          fail(what + " have different lengths");
        }
      }
    }
  }
}
