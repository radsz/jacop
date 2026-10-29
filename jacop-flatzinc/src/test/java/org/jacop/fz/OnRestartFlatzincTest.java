/*
 * OnRestartFlatzincTest.java
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
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Tests of MiniZinc's on_restart built-ins ({@code jacop_on_restart_*}), which MiniZinc's library
 * aborted on before. The models are FlatZinc from MiniZinc 2.10.1 with JaCoP's library.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class OnRestartFlatzincTest {

  @TempDir Path tmp;

  private static final String BUILT_INS =
      """
      var 3..7: x;
      var bool: b;
      var 1.0..2.0: f;
      var 1..5: st:: output_var;
      var 3..7: s:: output_var;
      var 3..7: l:: output_var;
      var bool: sb:: output_var;
      var 1..3: u:: output_var;
      var 1.0..2.0: sf:: output_var;
      constraint jacop_on_restart_status(st);
      constraint jacop_on_restart_sol_int(x,s);
      constraint jacop_on_restart_last_val_int(x,l);
      constraint jacop_on_restart_sol_bool(b,sb);
      constraint jacop_on_restart_uniform_int(1,3,u);
      constraint jacop_on_restart_sol_float(f,sf);
      """;

  @Test
  void builtInsTakeTheirStartValuesWithoutRestarts() throws IOException {
    // without restarts there is one run: status START, and before any solution sol and last_val
    // take the smallest value of their input
    String out = run(BUILT_INS + "solve satisfy;\n");
    assertTrue(out.contains("st = 1;\ns = 3;\nl = 3;\nsb = false;\n"), out);
    assertTrue(out.contains("sf = 1.0;"), out);
    assertTrue(Pattern.compile("u = [123];").matcher(out).find(), out);
  }

  @Test
  void builtInsTakeTheirStartValuesInTheFirstRun() throws IOException {
    String out = run(BUILT_INS + "solve :: restart_luby(10) satisfy;\n");
    assertTrue(out.contains("st = 1;\ns = 3;\nl = 3;\nsb = false;\n"), out);
  }

  @Test
  void completeMarkerEndsTheSearch() throws IOException {
    // complete() marks the search space as explored, so no solution means none exists
    String fzn =
        """
        var 1..3: x:: output_var;
        constraint jacop_on_restart_complete(true);
        solve :: restart_luby(10) satisfy;
        """;
    assertTrue(run(fzn).contains("=====UNSATISFIABLE====="));
  }

  @Test
  void lnsImprovesTheSolutionOfTheFirstRun() throws IOException {
    // basic_lns(forall(i in 1..6)(uniform_on_restart(1, 100) <= 60 -> x[i] = sol(x[i]))) on
    // minimize sum(i * x[i]) over a permutation x, int_search(x, input_order, indomain_min) and
    // restart_constant(3); st is status()
    String fzn = PERMUTATION_LNS;
    String out = run(fzn, "-a", "--restart-limit", "200", "-r", "1");
    checkLnsSolutions(out);
    // a neighbourhood explored to the end proves nothing, and the bound 55 does not fail at the
    // root, so the search ends only at the restart limit
    assertFalse(out.contains("=========="), out);
  }

  @Test
  void lnsUnderFreeSearchRunsTheBuiltInsInEachRun() throws IOException {
    // free search runs the built-ins at the root of its own runs, limited by the model's restarts
    String out = run(PERMUTATION_LNS, "-f", "-a", "-t", "1500", "-r", "1");
    checkLnsSolutions(out);
    assertFalse(out.contains("=========="), out);
  }

  @Test
  void completeMarkerEndsFreeSearch() throws IOException {
    String fzn =
        """
        var 1..3: x:: output_var;
        constraint jacop_on_restart_complete(true);
        solve :: restart_luby(10) satisfy;
        """;
    assertTrue(run(fzn, "-f").contains("=====UNSATISFIABLE====="));
  }

  @Test
  void adaptiveLnsKeepsTheOptimum() throws IOException {
    // minimize sum(i * x[i]) over a permutation, without on_restart: large neighbourhood search of
    // free search and of LCG free search finds and proves the optimum 56
    String fzn =
        """
        array [1..6] of int: w = [1,2,3,4,5,6];
        var 1..6: x1:: output_var;
        var 1..6: x2:: output_var;
        var 1..6: x3:: output_var;
        var 1..6: x4:: output_var;
        var 1..6: x5:: output_var;
        var 1..6: x6:: output_var;
        var 21..126: cost:: output_var:: is_defined_var;
        constraint jacop_alldiff([x1,x2,x3,x4,x5,x6]);
        constraint int_lin_eq([1,2,3,4,5,6,-1],[x1,x2,x3,x4,x5,x6,cost],0):: defines_var(cost);
        solve minimize cost;
        """;
    for (String[] options :
        new String[][] {
          {"-f", "--free-config", "lns=1,lns-fails=2"},
          {"--lcg", "-f", "--free-config", "lns=1,lns-conflicts=2"}
        }) {
      String out = run(fzn, options);
      assertTrue(out.contains("cost = 56;"), out);
      assertTrue(out.contains("=========="), out);
    }
  }

  private static void checkLnsSolutions(String out) {
    List<int[]> solutions = new ArrayList<>();
    Matcher m = Pattern.compile("cost = (\\d+);\\nst = (\\d);").matcher(out);
    while (m.find()) {
      solutions.add(new int[] {Integer.parseInt(m.group(1)), Integer.parseInt(m.group(2))});
    }
    assertEquals(1, solutions.getFirst()[1], out);
    // the runs after the first solution have a status of SAT, UNSAT or UNKNOWN
    assertTrue(solutions.stream().anyMatch(sol -> sol[1] != 1), out);
    for (int i = 1; i < solutions.size(); i++) {
      assertTrue(solutions.get(i)[0] < solutions.get(i - 1)[0], out);
    }
    // 6 * 1 + 5 * 2 + ... + 1 * 6
    assertEquals(56, solutions.getLast()[0], out);
  }

  private static final String PERMUTATION_LNS =
      """

        var 1..6: X_INTRODUCED_16_;
        var 1..6: X_INTRODUCED_17_;
        var 1..6: X_INTRODUCED_18_;
        var 1..6: X_INTRODUCED_19_;
        var 1..6: X_INTRODUCED_20_;
        var 1..6: X_INTRODUCED_21_;
        var 21..126: cost:: output_var:: is_defined_var;
        var 1..5: st ::output_var;
        var 1..6: X_INTRODUCED_34_ ::var_is_introduced ;
        var bool: X_INTRODUCED_35_ ::var_is_introduced :: is_defined_var;
        var 1..100: X_INTRODUCED_36_ ::var_is_introduced ;
        var bool: X_INTRODUCED_37_ ::var_is_introduced :: is_defined_var;
        var bool: X_INTRODUCED_38_ ::var_is_introduced :: is_defined_var;
        var 1..6: X_INTRODUCED_39_ ::var_is_introduced ;
        var bool: X_INTRODUCED_40_ ::var_is_introduced :: is_defined_var;
        var 1..100: X_INTRODUCED_41_ ::var_is_introduced ;
        var bool: X_INTRODUCED_42_ ::var_is_introduced :: is_defined_var;
        var bool: X_INTRODUCED_43_ ::var_is_introduced :: is_defined_var;
        var 1..6: X_INTRODUCED_44_ ::var_is_introduced ;
        var bool: X_INTRODUCED_45_ ::var_is_introduced :: is_defined_var;
        var 1..100: X_INTRODUCED_46_ ::var_is_introduced ;
        var bool: X_INTRODUCED_47_ ::var_is_introduced :: is_defined_var;
        var bool: X_INTRODUCED_48_ ::var_is_introduced :: is_defined_var;
        var 1..6: X_INTRODUCED_49_ ::var_is_introduced ;
        var bool: X_INTRODUCED_50_ ::var_is_introduced :: is_defined_var;
        var 1..100: X_INTRODUCED_51_ ::var_is_introduced ;
        var bool: X_INTRODUCED_52_ ::var_is_introduced :: is_defined_var;
        var bool: X_INTRODUCED_53_ ::var_is_introduced :: is_defined_var;
        var 1..6: X_INTRODUCED_54_ ::var_is_introduced ;
        var bool: X_INTRODUCED_55_ ::var_is_introduced :: is_defined_var;
        var 1..100: X_INTRODUCED_56_ ::var_is_introduced ;
        var bool: X_INTRODUCED_57_ ::var_is_introduced :: is_defined_var;
        var bool: X_INTRODUCED_58_ ::var_is_introduced :: is_defined_var;
        var 1..6: X_INTRODUCED_59_ ::var_is_introduced ;
        var bool: X_INTRODUCED_60_ ::var_is_introduced :: is_defined_var;
        var 1..100: X_INTRODUCED_61_ ::var_is_introduced ;
        var bool: X_INTRODUCED_62_ ::var_is_introduced :: is_defined_var;
        var bool: X_INTRODUCED_63_ ::var_is_introduced :: is_defined_var;
        var bool: X_INTRODUCED_64_ ::var_is_introduced :: is_defined_var;
        var bool: X_INTRODUCED_65_ ::var_is_introduced :: is_defined_var;
        array [1..6] of var int: x:: output_array([1..6]) = [X_INTRODUCED_16_,X_INTRODUCED_17_,X_INTRODUCED_18_,X_INTRODUCED_19_,X_INTRODUCED_20_,X_INTRODUCED_21_];
        constraint jacop_on_restart_status(st);
        constraint jacop_alldiff(x);
        constraint jacop_on_restart_sol_int(X_INTRODUCED_16_,X_INTRODUCED_34_);
        constraint jacop_on_restart_uniform_int(1,100,X_INTRODUCED_36_);
        constraint jacop_on_restart_sol_int(X_INTRODUCED_17_,X_INTRODUCED_39_);
        constraint jacop_on_restart_uniform_int(1,100,X_INTRODUCED_41_);
        constraint jacop_on_restart_sol_int(X_INTRODUCED_18_,X_INTRODUCED_44_);
        constraint jacop_on_restart_uniform_int(1,100,X_INTRODUCED_46_);
        constraint jacop_on_restart_sol_int(X_INTRODUCED_19_,X_INTRODUCED_49_);
        constraint jacop_on_restart_uniform_int(1,100,X_INTRODUCED_51_);
        constraint jacop_on_restart_sol_int(X_INTRODUCED_20_,X_INTRODUCED_54_);
        constraint jacop_on_restart_uniform_int(1,100,X_INTRODUCED_56_);
        constraint jacop_on_restart_sol_int(X_INTRODUCED_21_,X_INTRODUCED_59_);
        constraint jacop_on_restart_uniform_int(1,100,X_INTRODUCED_61_);
        constraint bool_clause([X_INTRODUCED_64_,X_INTRODUCED_65_],[]);
        constraint int_lin_eq([1,2,3,4,5,6,-1],[X_INTRODUCED_16_,X_INTRODUCED_17_,X_INTRODUCED_18_,X_INTRODUCED_19_,X_INTRODUCED_20_,X_INTRODUCED_21_,cost],0):: defines_var(cost);
        constraint int_eq_reif(X_INTRODUCED_16_,X_INTRODUCED_34_,X_INTRODUCED_35_):: defines_var(X_INTRODUCED_35_);
        constraint int_le_reif(61,X_INTRODUCED_36_,X_INTRODUCED_37_):: defines_var(X_INTRODUCED_37_);
        constraint bool_clause_reif([X_INTRODUCED_35_,X_INTRODUCED_37_],[],X_INTRODUCED_38_):: defines_var(X_INTRODUCED_38_);
        constraint int_eq_reif(X_INTRODUCED_17_,X_INTRODUCED_39_,X_INTRODUCED_40_):: defines_var(X_INTRODUCED_40_);
        constraint int_le_reif(61,X_INTRODUCED_41_,X_INTRODUCED_42_):: defines_var(X_INTRODUCED_42_);
        constraint bool_clause_reif([X_INTRODUCED_40_,X_INTRODUCED_42_],[],X_INTRODUCED_43_):: defines_var(X_INTRODUCED_43_);
        constraint int_eq_reif(X_INTRODUCED_18_,X_INTRODUCED_44_,X_INTRODUCED_45_):: defines_var(X_INTRODUCED_45_);
        constraint int_le_reif(61,X_INTRODUCED_46_,X_INTRODUCED_47_):: defines_var(X_INTRODUCED_47_);
        constraint bool_clause_reif([X_INTRODUCED_45_,X_INTRODUCED_47_],[],X_INTRODUCED_48_):: defines_var(X_INTRODUCED_48_);
        constraint int_eq_reif(X_INTRODUCED_19_,X_INTRODUCED_49_,X_INTRODUCED_50_):: defines_var(X_INTRODUCED_50_);
        constraint int_le_reif(61,X_INTRODUCED_51_,X_INTRODUCED_52_):: defines_var(X_INTRODUCED_52_);
        constraint bool_clause_reif([X_INTRODUCED_50_,X_INTRODUCED_52_],[],X_INTRODUCED_53_):: defines_var(X_INTRODUCED_53_);
        constraint int_eq_reif(X_INTRODUCED_20_,X_INTRODUCED_54_,X_INTRODUCED_55_):: defines_var(X_INTRODUCED_55_);
        constraint int_le_reif(61,X_INTRODUCED_56_,X_INTRODUCED_57_):: defines_var(X_INTRODUCED_57_);
        constraint bool_clause_reif([X_INTRODUCED_55_,X_INTRODUCED_57_],[],X_INTRODUCED_58_):: defines_var(X_INTRODUCED_58_);
        constraint int_eq_reif(X_INTRODUCED_21_,X_INTRODUCED_59_,X_INTRODUCED_60_):: defines_var(X_INTRODUCED_60_);
        constraint int_le_reif(61,X_INTRODUCED_61_,X_INTRODUCED_62_):: defines_var(X_INTRODUCED_62_);
        constraint bool_clause_reif([X_INTRODUCED_60_,X_INTRODUCED_62_],[],X_INTRODUCED_63_):: defines_var(X_INTRODUCED_63_);
        constraint array_bool_and([X_INTRODUCED_38_,X_INTRODUCED_43_,X_INTRODUCED_48_,X_INTRODUCED_53_,X_INTRODUCED_58_,X_INTRODUCED_63_],X_INTRODUCED_64_):: defines_var(X_INTRODUCED_64_);
        constraint int_eq_imp(st,1,X_INTRODUCED_65_):: defines_var(X_INTRODUCED_65_);
        solve :: restart_constant(3):: int_search(x,input_order,indomain_min,complete) minimize cost;
        """;

  private String run(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return out.toString(StandardCharsets.UTF_8);
  }
}
