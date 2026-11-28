/*
 * ClausalFlatzincTest.java
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
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random satisfaction models over domains of at most three values, solved with their CNF compiled
 * by {@link org.jacop.fz.constraints.ClausalCompiler} and without it: the answers must agree, and a
 * solution of the CNF must be one of the store (otherwise the front end reports it rejected and
 * solves the model again, which the test also catches). {@code clausal.fuzz.runs} sets the number
 * of models (default 150), {@code clausal.fuzz.seed} the first seed.
 */
class ClausalFlatzincTest {

  @TempDir Path tmp;

  private static final int RUNS = Integer.getInteger("clausal.fuzz.runs", 150);
  private static final long SEED = Long.getLong("clausal.fuzz.seed", 1L);

  private static final int[][] DOMAINS = {{-1, 1}, {0, 2}, {-1, 0, 1}, {1, 3}, {0, 1}};

  /** Domains of four to eight values, compiled when the limit is raised. */
  private static final int[][] WIDE = {{-2, 3}, {0, 5}, {-3, 4}, {1, 4}, {0, 1}};

  /** A random model in FlatZinc. */
  static String model(long seed) {
    return model(seed, DOMAINS);
  }

  /** A random model in FlatZinc over the given domains, the last one 0..1. */
  static String model(long seed, int[][] domains) {
    Random r = new Random(seed);
    int n = 6 + r.nextInt(5);
    int[][] dom = new int[n][];
    StringBuilder s = new StringBuilder();
    for (int i = 0; i < n; i++) {
      // the first variable has a value other than 0 and 1, so the model is compiled
      dom[i] = i == 0 ? domains[r.nextInt(4)] : domains[r.nextInt(domains.length)];
      s.append("var ").append(dom[i][0]).append("..").append(dom[i][1]).append(": x");
      s.append(i).append(" :: output_var;\n");
    }
    int nb = 4;
    for (int i = 0; i < nb; i++) {
      s.append("var bool: b").append(i).append(" :: output_var;\n");
    }
    int m = 3 + r.nextInt(6);
    for (int c = 0; c < m; c++) {
      s.append("constraint ").append(constraint(r, n, nb, dom)).append(";\n");
    }
    s.append("solve satisfy;\n");
    return s.toString();
  }

  private static String x(Random r, int n) {
    return "x" + r.nextInt(n);
  }

  private static String xs(Random r, int n, int k) {
    StringBuilder s = new StringBuilder("[");
    for (int i = 0; i < k; i++) {
      s.append(i == 0 ? "" : ",").append(x(r, n));
    }
    return s.append(']').toString();
  }

  private static String ints(Random r, int k, int lo, int hi) {
    StringBuilder s = new StringBuilder("[");
    for (int i = 0; i < k; i++) {
      s.append(i == 0 ? "" : ",").append(lo + r.nextInt(hi - lo + 1));
    }
    return s.append(']').toString();
  }

  private static String b(Random r, int nb) {
    return "b" + r.nextInt(nb);
  }

  private static String constraint(Random r, int n, int nb, int[][] dom) {
    int k = 2 + r.nextInt(4);
    String[] rel = {"eq", "le", "ne"};
    String[] bin = {"eq", "ne", "le", "lt"};
    switch (r.nextInt(17)) {
      case 0:
        return "int_times(" + x(r, n) + "," + x(r, n) + "," + x(r, n) + ")";
      case 1:
        return "int_lin_"
            + rel[r.nextInt(3)]
            + "("
            + ints(r, k, -2, 2)
            + ","
            + xs(r, n, k)
            + ","
            + (r.nextInt(7) - 3)
            + ")";
      case 2:
        return "int_lin_"
            + rel[r.nextInt(3)]
            + (r.nextBoolean() ? "_reif(" : "_imp(")
            + ints(r, k, -2, 2)
            + ","
            + xs(r, n, k)
            + ","
            + (r.nextInt(7) - 3)
            + ","
            + b(r, nb)
            + ")";
      case 3:
        return "int_" + bin[r.nextInt(4)] + "(" + x(r, n) + "," + x(r, n) + ")";
      case 4:
        return "int_"
            + bin[r.nextInt(4)]
            + (r.nextBoolean() ? "_reif(" : "_imp(")
            + x(r, n)
            + ","
            + x(r, n)
            + ","
            + b(r, nb)
            + ")";
      case 5:
        return "bool_clause([" + b(r, nb) + "," + b(r, nb) + "],[" + b(r, nb) + "])";
      case 6:
        return (r.nextBoolean() ? "array_bool_or([" : "array_bool_and([")
            + b(r, nb)
            + ","
            + b(r, nb)
            + "],"
            + b(r, nb)
            + ")";
      case 7:
        {
          // a variable over 0..1 for bool2int
          for (int i = 0; i < n; i++) {
            if (dom[i][0] == 0 && dom[i][1] == 1) {
              return "bool2int(" + b(r, nb) + ",x" + i + ")";
            }
          }
          return "bool_xor(" + b(r, nb) + "," + b(r, nb) + "," + b(r, nb) + ")";
        }
      case 8:
        return "jacop_alldiff(" + xs(r, n, 2 + r.nextInt(2)) + ")";
      case 9:
        return "jacop_count_values("
            + xs(r, n, k)
            + ","
            + ints(r, 2, -1, 2)
            + ","
            + xs(r, n, 2)
            + ")";
      case 10:
        return "jacop_among(" + xs(r, n, k) + ",{0,1}," + x(r, n) + ")";
      case 11:
        return (r.nextBoolean() ? "jacop_increasing(" : "jacop_strictly_increasing(")
            + xs(r, n, k)
            + ")";
      case 12:
        return (r.nextBoolean() ? "jacop_maximum(" : "jacop_minimum(")
            + x(r, n)
            + ","
            + xs(r, n, k)
            + ")";
      case 13:
        // two rows of three columns: the columns are the vectors
        return "jacop_lex_chain_lesseq_int(" + xs(r, n, 6) + ",3)";
      case 14:
        return "jacop_value_precede_chain_int([0,1]," + xs(r, n, k) + ")";
      case 15:
        {
          String t = ints(r, 3 * (1 + r.nextInt(5)), -2, 3);
          return switch (r.nextInt(3)) {
            case 0 -> "jacop_short_table_int(" + xs(r, n, 3) + "," + t + ",-2)";
            case 1 -> "jacop_table_int(" + xs(r, n, 3) + "," + t.replace("-2", "0") + ")";
            default -> "jacop_negative_table_int(" + xs(r, n, 3) + "," + t + ")";
          };
        }
      default:
        {
          // an automaton of 3 states over the values -1..3, all states final but state 3
          return "jacop_regular_set("
              + xs(r, n, k)
              + ",3,-1..3,"
              + ints(r, 15, 0, 3)
              + ",1,{1,2},-1)";
        }
    }
  }

  @Test
  void compiledModelsAgreeWithSearch() throws IOException {
    agree(DOMAINS, null);
  }

  @Test
  void compiledModelsOverLargerDomainsAgreeWithSearch() throws IOException {
    agree(WIDE, "8");
  }

  @Test
  void regularOverMoreThanThreeValuesIsNotCompiled() throws IOException {
    String small =
        """
        var 1..3: x0 :: output_var;
        var 1..3: x1 :: output_var;
        constraint jacop_regular_set([x0,x1],2,1..3,[2,2,2,2,2,2],1,{2},1);
        constraint int_ne(x0,x1);
        solve satisfy;
        """;
    assertTrue(run(small, true).contains("clausalModel=true"), small);
    String wide = small.replace("1..3", "1..4").replace("[2,2,2,2,2,2]", "[2,2,2,2,2,2,2,2]");
    String out = run(wide, true);
    assertFalse(out.contains("clausalModel=true"), wide + out);
    assertTrue(out.contains("----------"), wide + out);
  }

  // with a larger maxDomain the sums over wide domains are compiled too, so the fuzz covers them
  @Test
  void differenceOverMoreThanThreeValuesIsNotCompiled() throws IOException {
    String small =
        """
        var 0..2: x0 :: output_var;
        var 0..2: x1 :: output_var;
        var 1..2: d :: output_var;
        constraint int_lin_eq([1,-1,-1],[x0,x1,d],0);
        constraint int_ne(x0,x1);
        solve satisfy;
        """;
    assertTrue(run(small, true).contains("clausalModel=true"), small);
    // the differences of a Costas array: lazy clause generation is faster
    String wide = small.replace("0..2", "0..3");
    String out = run(wide, true);
    assertFalse(out.contains("clausalModel=true"), wide + out);
    assertTrue(out.contains("----------"), wide + out);
  }

  private void agree(int[][] domains, String maxDomain) throws IOException {
    String old = System.getProperty("org.jacop.fz.clausal.maxDomain");
    String oldSum = System.getProperty("org.jacop.fz.clausal.sumDomain");
    if (maxDomain != null) {
      System.setProperty("org.jacop.fz.clausal.maxDomain", maxDomain);
      System.setProperty("org.jacop.fz.clausal.sumDomain", maxDomain);
    }
    try {
      agree(domains);
    } finally {
      restore("org.jacop.fz.clausal.maxDomain", old);
      restore("org.jacop.fz.clausal.sumDomain", oldSum);
    }
  }

  private static void restore(String key, String value) {
    if (value == null) {
      System.clearProperty(key);
    } else {
      System.setProperty(key, value);
    }
  }

  private void agree(int[][] domains) throws IOException {
    int compiled = 0;
    int unsat = 0;
    for (long seed = SEED; seed < SEED + RUNS; seed++) {
      String fzn = model(seed, domains);
      String with = run(fzn, true);
      String without = run(fzn, false);
      assertFalse(with.contains("rejected"), seed + "\n" + fzn + with);
      boolean u = with.contains("=====UNSATISFIABLE=====");
      assertEquals(
          without.contains("=====UNSATISFIABLE====="), u, "seed " + seed + "\n" + fzn + with);
      assertEquals(!u, with.contains("----------"), "seed " + seed + "\n" + fzn + with);
      if (!u) {
        // every variable gets a value, also one in no constraint, which the clauses leave out
        for (String line : fzn.split("\n")) {
          if (line.startsWith("var ")) {
            String name = line.substring(line.indexOf(": ") + 2, line.indexOf(" ::"));
            assertTrue(
                with.contains(name + " = "), "seed " + seed + " " + name + "\n" + fzn + with);
          }
        }
      }
      compiled += with.contains("clausalModel=true") ? 1 : 0;
      unsat += u ? 1 : 0;
    }
    assertTrue(compiled >= RUNS / 3, compiled + " of " + RUNS + " compiled");
    assertTrue(unsat > 0 && unsat < RUNS, unsat + " unsatisfiable");
  }

  private String run(String model, boolean clausal) throws IOException {
    Path fzn = tmp.resolve("run.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    List<String> args =
        new ArrayList<>(List.of("--lcg", "-s", "-f", "-t", "10000", fzn.toString()));
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    PrintStream originalErr = System.err;
    String old = System.getProperty("org.jacop.fz.clausal");
    System.setProperty("org.jacop.fz.clausal", Boolean.toString(clausal));
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      System.setErr(capture);
      new Fz2jacop().callMain(args.toArray(new String[0]));
    } finally {
      System.setOut(originalOut);
      System.setErr(originalErr);
      if (old == null) {
        System.clearProperty("org.jacop.fz.clausal");
      } else {
        System.setProperty("org.jacop.fz.clausal", old);
      }
    }
    return out.toString(StandardCharsets.UTF_8);
  }

  /**
   * The count of an among whose variable has a hole ({0, 2}) takes no value in the hole: the
   * clauses tied only y >= 2 to "at least two", so a count of 1 gave y = 0, and the store rejected
   * the solution of the clausal model.
   */
  @Test
  void aCountWithAHoleTakesNoValueInIt() throws IOException {
    String model =
        """
        var {-3,-2,0,1}: x:: output_var;
        var 2..6: y:: output_var;
        var {0,2}: c:: output_var;
        constraint jacop_among([y,x],{-1,1,2},c);
        solve satisfy;
        """;
    String out = run(model, true);
    assertTrue(out.contains("clausalModel=true") && !out.contains("rejected"), out);
  }
}
