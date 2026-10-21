/*
 * MznlibGlobalsTest.java
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

package org.jacop.fz;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

/**
 * Checks the global constraints that JaCoP's MiniZinc library maps to native propagators.
 *
 * <p>Each model in {@code src/test/fz/mznlib} is compiled twice by {@code regenerate.sh}: with
 * JaCoP's library ({@code X.fzn}) and with the MiniZinc standard library only ({@code
 * X-decomp.fzn}). Both must have exactly the same set of solutions.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class MznlibGlobalsTest {

  private static final String DIR = "src/test/fz/mznlib/";
  private static final String SEPARATOR = "----------";

  @ParameterizedTest
  @ValueSource(
      strings = {
        "hook_cumulatives",
        "hook_cumulatives_opt",
        "hook_cumulatives_lb",
        "hook_sliding_among_int",
        "hook_sliding_among_bool",
        "hook_sliding_among_edge",
        "hook_count_bool_var",
        "hook_count_bool_par",
        "hook_bin_packing_capa",
        "hook_bin_packing_opt",
        "hook_regular_reif",
        "hook_cost_regular",
        "hook_cost_regular_holes",
        "hook_cost_regular_cost_in_word",
        "hook_mdd",
        "hook_mdd_nondet",
        "hook_network_flow_isolated",
        "hook_network_flow_cost_zero_based",
        "hook_network_flow_cost_loop",
        "hook_disjunctive_strict_opt_var",
        "hook_element_nonshifted",
        "hook_element2d",
        "hook_count_var_rel",
        "hook_regular_nfa",
        "hook_regular_nfa_set",
        "hook_sum_set",
        "hook_all_different_opt",
        "hook_table_reif",
        "hook_table_reif_wide"
      })
  void sameSolutionsAsDecomposition(String model) {
    Set<String> nativeSolutions = solveAll(DIR + model + ".fzn");
    Set<String> decompSolutions = solveAll(DIR + model + "-decomp.fzn");

    assertFalse(nativeSolutions.isEmpty(), model + " has no solutions");
    assertEquals(decompSolutions, nativeSolutions, model);
  }

  @Test
  void atanhRedefinitionGivesTheInverseOfTanh() {
    // float_atanh was redefined with t = ln(x) and y = (t + 1) / (t - 1) / 2, so atanh(0.5)
    // was -0.0906 instead of 0.5493.
    Set<String> solutions = solveAll(DIR + "redef_float_atanh.fzn");

    assertEquals(3, solutions.size(), solutions.toString());
    for (String solution : solutions) {
      Matcher m = Pattern.compile("i = (\\d+);\\s+f = (\\S+);").matcher(solution);
      assertTrue(m.find(), solution);
      double x = Integer.parseInt(m.group(1)) / 4.0;
      double expected = 0.5 * Math.log((1 + x) / (1 - x));
      assertEquals(expected, Double.parseDouble(m.group(2)), 1e-6, solution);
    }
  }

  private static Set<String> solveAll(String fzn) {
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(new String[] {"-a", fzn});
    } finally {
      System.setOut(originalOut);
    }
    String result = buffer.toString(StandardCharsets.UTF_8);
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(result.split(SEPARATOR))
        .map(String::strip)
        .filter(s -> !s.isEmpty() && !s.startsWith("=========="))
        .forEach(solutions::add);
    return solutions;
  }
}
