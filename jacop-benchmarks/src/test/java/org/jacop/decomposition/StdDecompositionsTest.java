/*
 * StdDecompositionsTest.java
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

package org.jacop.decomposition;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;
import org.jacop.fz.Fz2jacop;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Checks each decomposition in {@link StdDecompositions} on a small model: JaCoP's constraint and
 * the decomposition must give the same solutions. This keeps the decompositions that {@link
 * DecompositionCheck} relies on correct, and checks the global constraints on small cases as well.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class StdDecompositionsTest {

  @TempDir Path dir;

  /** Declares n output variables name1..namen with the given domain; returns the array literal. */
  private static String vars(StringBuilder decls, String name, int n, String domain) {
    List<String> names = new ArrayList<>();
    for (int i = 1; i <= n; i++) {
      decls.append("var ").append(domain).append(": ").append(name).append(i);
      decls.append(" :: output_var;\n");
      names.add(name + i);
    }
    return "[" + String.join(",", names) + "]";
  }

  private static Arguments model(String name, String decls, String constraint) {
    return Arguments.of(name, decls + "constraint " + constraint + ";\nsolve satisfy;\n");
  }

  static Stream<Arguments> models() {
    List<Arguments> models = new ArrayList<>();
    StringBuilder d = new StringBuilder();
    String x = vars(d, "x", 4, "1..4");
    models.add(model("alldiff", d.toString(), "jacop_alldiff(" + x + ")"));

    d = new StringBuilder();
    x = vars(d, "x", 4, "0..3");
    models.add(
        model("alldifferent_except_0", d.toString(), "jacop_alldifferent_except_0(" + x + ")"));
    models.add(
        model("alldifferent_except", d.toString(), "jacop_alldifferent_except(" + x + ",{1,3})"));
    models.add(model("all_equal_int", d.toString(), "jacop_all_equal_int(" + x + ")"));
    models.add(model("increasing", d.toString(), "jacop_increasing(" + x + ")"));
    models.add(model("strictly_increasing", d.toString(), "jacop_strictly_increasing(" + x + ")"));
    models.add(model("decreasing", d.toString(), "jacop_decreasing(" + x + ")"));
    models.add(model("value_precede_int", d.toString(), "jacop_value_precede_int(1,2," + x + ")"));
    models.add(model("atleast", d.toString(), "jacop_atleast(" + x + ",2,2)"));
    models.add(model("atmost", d.toString(), "jacop_atmost(" + x + ",2,1)"));
    models.add(model("among", d.toString(), "jacop_among(" + x + ",{0,2},2)"));
    models.add(
        model(
            "count_values_bounds",
            d.toString(),
            "jacop_count_values_bounds(" + x + ",[0,1,2],[1,0,1],[2,1,2])"));

    d = new StringBuilder();
    x = vars(d, "x", 4, "0..2");
    vars(d, "n", 1, "0..4");
    models.add(model("count", d.toString(), "jacop_count(" + x + ",1,n1)"));
    models.add(model("nvalue", d.toString(), "jacop_nvalue(n1," + x + ")"));
    String y = vars(d, "y", 1, "0..2");
    models.add(model("count_var", d.toString(), "jacop_count_var(" + x + ",y1,n1)"));
    String b = vars(d, "b", 1, "bool");
    models.add(model("count_reif", d.toString(), "jacop_count_reif(" + x + ",1,n1,b1)"));
    models.add(model("atmost_reif", d.toString(), "jacop_atmost_reif(" + x + ",1,2,b1)"));
    models.add(model("member_int_reif", d.toString(), "jacop_member_int_reif(" + x + ",y1,b1)"));
    String c = vars(d, "c", 3, "0..4");
    models.add(
        model("count_values", d.toString(), "jacop_count_values(" + x + ",[0,2,3]," + c + ")"));

    d = new StringBuilder();
    x = vars(d, "x", 4, "-1..3");
    vars(d, "m", 1, "-2..4");
    models.add(model("minimum", d.toString(), "jacop_minimum(m1," + x + ")"));
    models.add(model("maximum", d.toString(), "jacop_maximum(m1," + x + ")"));
    models.add(model("minimum_arg_int", d.toString(), "jacop_minimum_arg_int(" + x + ",m1,0)"));
    models.add(model("maximum_arg_int", d.toString(), "jacop_maximum_arg_int(" + x + ",m1,0)"));
    models.add(
        model(
            "element_nonshifted",
            d.toString(),
            "jacop_array_var_int_element_nonshifted(m1," + x + ",x1,0)"));

    d = new StringBuilder();
    x = vars(d, "x", 3, "1..3");
    models.add(
        model(
            "table_int",
            d.toString(),
            "jacop_table_int(" + x + ",[1,2,3, 2,2,2, 3,1,2, 1,1,1, 3,3,1])"));
    // automaton over {1,2} accepting words without two consecutive 2s, ending in state 1 or 2
    models.add(
        model("regular", d.toString(), "jacop_regular(" + x + ",3,2,[1,2, 1,3, 0,0],1,1..2,1)"));
    vars(d, "k", 1, "0..20");
    models.add(
        model(
            "cost_regular",
            d.toString(),
            "jacop_cost_regular(" + x + ",2,3,[1,2,2, 2,1,0],1,{1},[1,2,3, 4,5,6],k1)"));

    d = new StringBuilder();
    x = vars(d, "x", 3, "bool");
    y = vars(d, "y", 3, "bool");
    models.add(
        model(
            "table_bool",
            d.toString(),
            "jacop_table_bool(" + x + ",[true,false,true, false,false,false])"));
    models.add(
        model("lex_lesseq_bool", d.toString(), "jacop_lex_lesseq_bool(" + x + "," + y + ")"));
    models.add(model("lex_less_bool", d.toString(), "jacop_lex_less_bool(" + x + "," + y + ")"));
    models.add(model("increasing_bool", d.toString(), "jacop_increasing(" + x + ")"));
    vars(d, "b", 1, "bool");
    models.add(
        model(
            "if_then_else_bool",
            d.toString(),
            "jacop_if_then_else_bool([x1,x2,true],[y1,y2,y3],b1)"));

    d = new StringBuilder();
    x = vars(d, "x", 3, "0..2");
    y = vars(d, "y", 3, "0..2");
    models.add(model("lex_lesseq_int", d.toString(), "jacop_lex_lesseq_int(" + x + "," + y + ")"));
    models.add(model("lex_less_int", d.toString(), "jacop_lex_less_int(" + x + "," + y + ")"));
    models.add(
        model(
            "lex_chain_lesseq_int",
            d.toString(),
            "jacop_lex_chain_lesseq_int([x1,x2,x3,y1,y2,y3],3)"));
    models.add(
        model(
            "lex_chain_less_int", d.toString(), "jacop_lex_chain_less_int([x1,x2,x3,y1,y2,y3],2)"));

    d = new StringBuilder();
    x = vars(d, "x", 5, "1..5");
    models.add(model("circuit", d.toString(), "jacop_circuit(" + x + ")"));
    models.add(model("subcircuit", d.toString(), "jacop_subcircuit(" + x + ")"));
    y = vars(d, "y", 5, "1..5");
    models.add(model("assignment", d.toString(), "jacop_assignment(" + x + "," + y + ",1,1)"));

    d = new StringBuilder();
    x = vars(d, "x", 4, "3..6");
    models.add(model("circuit_offset", d.toString(), "jacop_circuit_offset(" + x + ",3)"));
    y = vars(d, "y", 4, "0..3");
    models.add(
        model("assignment_offset", d.toString(), "jacop_assignment(" + x + "," + y + ",0,3)"));

    d = new StringBuilder();
    x = vars(d, "x", 3, "0..3");
    y = vars(d, "y", 3, "0..2");
    String dx = vars(d, "w", 3, "0..2");
    models.add(
        model(
            "diff2_strict",
            d.toString(),
            "jacop_diff2_strict(" + x + "," + y + "," + dx + ",[1,2,1])"));
    models.add(
        model(
            "list_diff2",
            d.toString(),
            "jacop_list_diff2(" + x + "," + y + "," + dx + ",[1,2,1])"));

    d = new StringBuilder();
    String s = vars(d, "s", 4, "0..4");
    String dur = vars(d, "d", 2, "0..2");
    String o = vars(d, "o", 4, "bool");
    String r = "[2,1,1,2]";
    models.add(
        model("cumulative", d.toString(), "jacop_cumulative(" + s + ",[d1,d2,2,1]," + r + ",3)"));
    models.add(
        model(
            "cumulative_optional",
            d.toString(),
            "jacop_cumulative_optional(" + s + ",[d1,d2,2,1]," + r + ",2," + o + ")"));
    models.add(
        model(
            "disjunctive_optional",
            d.toString(),
            "jacop_disjunctive_optional(" + s + ",[d1,d2,2,1]," + o + ")"));

    d = new StringBuilder();
    String ss = vars(d, "s", 3, "0..4");
    String sd = vars(d, "d", 2, "0..2");
    String sp = vars(d, "p", 4, "bool");
    vars(d, "m", 1, "0..5");
    vars(d, "l", 1, "-1..6");
    models.add(
        model(
            "alternative",
            d.toString(),
            "jacop_alternative(p4,m1,l1,[p1,p2,p3]," + ss + ",[d1,d2,2])"));
    models.add(model("span", d.toString(), "jacop_span(p4,m1,l1,[p1,p2,p3]," + ss + ",[d1,d2,2])"));
    models.add(
        model(
            "alternative_present",
            d.toString(),
            "jacop_alternative(true,m1,l1,[p1,p2,p3]," + ss + ",[d1,d2,2])"));
    models.add(
        model(
            "span_present",
            d.toString(),
            "jacop_span(true,m1,l1,[p1,p2,p3]," + ss + ",[d1,d2,2])"));

    d = new StringBuilder();
    String f = vars(d, "f", 4, "0..3");
    vars(d, "k", 1, "0..30");
    // arcs 1->2, 1->3, 2->3, 3->4 with supply 3 at node 1 and demand 3 at node 4
    models.add(
        model(
            "networkflow",
            d.toString(),
            "jacop_networkflow([1,2, 1,3, 2,3, 3,4]," + f + ",[1,3,1,2],[3,0,0,-3],k1)"));
    vars(d, "v", 2, "0..20");
    models.add(
        model("knapsack", d.toString(), "jacop_knapsack([1,2,3,4],[2,1,4,3],v1,v2," + f + ")"));

    d = new StringBuilder();
    String bin = vars(d, "p", 4, "1..3");
    String load = vars(d, "l", 3, "0..6");
    models.add(
        model(
            "bin_packing",
            d.toString(),
            "jacop_bin_packing(" + bin + "," + load + ",[1,2,2,3],1)"));
    models.add(
        model(
            "bin_packing_capacity",
            d.toString(),
            "jacop_bin_packing_capacity(" + bin + ",[3,4,2],[1,2,2,3],1)"));

    d = new StringBuilder();
    b = vars(d, "b", 2, "bool");
    vars(d, "v", 1, "0..5");
    models.add(
        model("if_then_else_int", d.toString(), "jacop_if_then_else_int([b1,b2,true],[1,3,5],v1)"));

    d = new StringBuilder();
    x = vars(d, "x", 3, "0..2");
    vars(d, "y", 1, "0..3");
    vars(d, "b", 1, "bool");
    models.add(model("member_int", d.toString(), "jacop_member_int(" + x + ",y1)"));
    models.add(model("all_equal_int_reif", d.toString(), "jacop_all_equal_int_reif(" + x + ",b1)"));

    d = new StringBuilder();
    x = vars(d, "x", 3, "bool");
    vars(d, "m", 1, "0..4");
    models.add(model("minimum_arg_bool", d.toString(), "jacop_minimum_arg_bool(" + x + ",m1,1)"));
    models.add(model("maximum_arg_bool", d.toString(), "jacop_maximum_arg_bool(" + x + ",m1,1)"));

    d = new StringBuilder();
    x = vars(d, "x", 4, "0..3");
    models.add(
        model("seq_precede_chain_int", d.toString(), "jacop_seq_precede_chain_int(" + x + ")"));
    models.add(
        model(
            "value_precede_chain_int",
            d.toString(),
            "jacop_value_precede_chain_int([2,0,3]," + x + ")"));

    d = new StringBuilder();
    s = vars(d, "s", 3, "0..3");
    o = vars(d, "o", 3, "bool");
    models.add(
        model(
            "disjunctive_strict_optional",
            d.toString(),
            "jacop_disjunctive_strict_optional(" + s + ",[1,0,2]," + o + ")"));

    d = new StringBuilder();
    x = vars(d, "x", 3, "0..3");
    String counts = vars(d, "c", 3, "0..3");
    models.add(model("gcc", d.toString(), "jacop_gcc(" + x + "," + counts + ",0)"));
    d = new StringBuilder();
    x = vars(d, "x", 4, "0..3");
    models.add(model("gcc_magic", d.toString(), "jacop_gcc(" + x + "," + x + ",0)"));

    d = new StringBuilder();
    x = vars(d, "x", 3, "1..3");
    models.add(
        model(
            "mdd",
            d.toString(),
            "jacop_mdd("
                + x
                + ",[1,2,2,3],[1,1,2,3,3,4],[{1},{2,3},{1,2},{3},{1},{1,3}],[2,3,4,4,4,0])"));

    d = new StringBuilder();
    String sets = vars(d, "t", 3, "set of 1..3");
    b = vars(d, "b", 3, "bool");
    models.add(
        model("link_set_to_booleans", d.toString(), "jacop_link_set_to_booleans(t1," + b + ",1)"));
    models.add(model("disjoint", d.toString(), "jacop_disjoint(t1,t2)"));
    models.add(model("partition_set", d.toString(), "jacop_partition_set(" + sets + ",1..3)"));
    models.add(
        model(
            "if_then_else_set",
            d.toString(),
            "jacop_if_then_else_set([b1,b2,true],[{1},{2,3},{}],t1)"));
    vars(d, "x", 3, "1..2");
    models.add(
        model("int_set_channel", d.toString(), "jacop_int_set_channel([x1,x2,x3],[t1,t2],1,1)"));
    return models.stream();
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("models")
  void decompositionHasTheSameSolutions(String name, String fzn) throws IOException {
    FznModel model = FznModel.parse(fzn);
    FznBuilder builder = new FznBuilder(model, "X_DECOMP_");
    FznModel.Constraint c = model.constraints.getFirst();
    StdDecompositions.decompose(builder, c.name(), c.args());
    String decomposed =
        DecompositionCheck.render(model, Set.of(c.index()), builder, null, false, false);

    Set<String> expected = solveAll(fzn);
    Set<String> actual = solveAll(decomposed);
    assertTrue(!expected.isEmpty(), name + " has no solution");
    assertEquals(expected, actual, name + ":\n" + decomposed);
  }

  @Test
  void staticSearchReplacesDynamicHeuristics() {
    assertEquals(
        " :: seq_search([int_search(x,input_order,indomain_min,complete),"
            + "int_search(y,input_order,indomain_max,complete)])",
        DecompositionCheck.staticSearch(
            " :: seq_search([int_search(x,first_fail,indomain_median,complete),"
                + "int_search(y,dom_w_deg,indomain_max,complete)])"));
  }

  @Test
  void renderKeepsTheModel() {
    String fzn =
        "predicate p(var int: x);\n"
            + "array [1..2] of int: c = [1,2];\n"
            + "var 1..3: x :: output_var;\n"
            + "var 1..3: y;\n"
            + "array [1..2] of var int: a :: output_array([1..2]) = [x,y];\n"
            + "constraint int_lin_le(c,a,4);\n"
            + "solve :: int_search(a,first_fail,indomain_min,complete) minimize y;\n";
    FznModel model = FznModel.parse(fzn);
    assertEquals(fzn, DecompositionCheck.render(model, Set.of(), null, null, false, false));
    assertTrue(
        DecompositionCheck.render(model, Set.of(), null, "int_le(y,2)", true, true)
            .contains(
                "var 1..3: y :: output_var;\n"
                    + "array [1..2] of var int: a :: output_array([1..2]) = [x,y];\n"
                    + "constraint int_lin_le(c,a,4);\n"
                    + "constraint int_le(y,2);\n"
                    + "solve :: int_search(a,input_order,indomain_min,complete) satisfy;\n"));
  }

  private Set<String> solveAll(String fzn) throws IOException {
    Path file = Files.createTempFile(dir, "model", ".fzn");
    Path out = Path.of(file + ".out");
    Files.writeString(file, fzn, StandardCharsets.UTF_8);
    new Fz2jacop().callMain(new String[] {"-a", "--outputfile", out.toString(), file.toString()});
    String result = Files.readString(out, StandardCharsets.UTF_8);
    Set<String> solutions = new TreeSet<>();
    for (String solution : result.split("----------")) {
      String t = solution.strip();
      if (!t.isEmpty() && !t.startsWith("==========")) {
        solutions.add(t);
      }
    }
    return solutions;
  }
}
