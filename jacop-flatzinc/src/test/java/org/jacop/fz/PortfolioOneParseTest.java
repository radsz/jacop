/*
 * PortfolioOneParseTest.java
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
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.concurrent.atomic.AtomicReference;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;

/** The portfolio reads the model once and each thread builds its store from that reading. */
@Timeout(60)
class PortfolioOneParseTest {

  @TempDir Path tmp;

  // parameters, scalar and array variables, an alias, an annotated search and output
  private static final String ALL_SOLUTIONS =
      """
      array [1..3] of int: w = [2, 3, 4];
      var 1..5: x :: output_var;
      var {1, 3, 5}: y :: output_var;
      var bool: b :: output_var;
      array [1..2] of var 0..4: z :: output_array([1..2]);
      array [1..3] of var int: v = [x, y, z[1]];
      constraint int_lin_le(w, v, 20);
      constraint int_ne(x, y);
      constraint int_lt_reif(z[1], z[2], b);
      constraint int_le(z[2], 2);
      solve :: int_search([x, y, z[1], z[2]], input_order, indomain_min, complete) satisfy;
      """;

  private static final String MINIMISE =
      """
      array [1..4] of var 0..9: q :: output_array([1..4]);
      var 0..100: cost :: output_var;
      constraint int_lin_eq([1, 2, 3, 4, -1], [q[1], q[2], q[3], q[4], cost], 0);
      constraint int_lin_le([-1, -1, -1, -1], [q[1], q[2], q[3], q[4]], -11);
      constraint int_ne(q[1], q[2]);
      constraint int_ne(q[3], q[4]);
      solve minimize cost;
      """;

  @Test
  void aTreeReadOnceBuildsTheSameModelAsReadingIt() throws Exception {
    Path fzn = write(ALL_SOLUTIONS);
    Options opt = new Options(new String[] {"-a", "--lcg", "off", fzn.toString()});
    String read =
        capture(
            () -> {
              try (FileInputStream in = new FileInputStream(fzn.toFile())) {
                Parser parser = new Parser(in);
                parser.setOptions(opt);
                parser.model();
              }
            });
    SimpleNode tree;
    try (FileInputStream in = new FileInputStream(fzn.toFile())) {
      Parser parser = new Parser(in);
      parser.setOptions(opt);
      tree = parser.parseModel();
    }
    assertTrue(read.contains("=========="), read);
    // reading only translates nothing; two parsers build from the tree, one after the other
    for (int i = 0; i < 2; i++) {
      String built =
          capture(
              () -> {
                Parser parser = new Parser(java.io.InputStream.nullInputStream());
                parser.setOptions(opt);
                parser.build(tree);
              });
      assertEquals(solutionLines(read), solutionLines(built));
    }
  }

  // z is an affine function of x used only in linear rows, which affine folding rewrites
  private static final String FOLDED =
      """
      var 0..2: x :: output_var;
      var 0..3: y :: output_var;
      var -20..20: z;
      constraint int_times(3, x, z);
      constraint int_lin_le([1, 1], [z, y], 4);
      solve :: int_search([x, y], input_order, indomain_min, complete) satisfy;
      """;

  /**
   * Affine folding rewrote the rows of the tree in place, with an array that only the dictionary of
   * the thread that folded knows: a thread that built from the tree later read "Cannot find array
   * X_JACOP_AFFINE_0" (rcpsp ship-schedule 6ShipsMixedUnconst under -p 4 with portfolio-split=4),
   * and one building at the same time could read a half-written row.
   */
  @Test
  void rewritingPassesLeaveTheReadTreeAsItWas() throws Exception {
    Path fzn = write(FOLDED);
    Options opt = new Options(new String[] {"-a", "--lcg", "off", fzn.toString()});
    SimpleNode tree;
    try (FileInputStream in = new FileInputStream(fzn.toFile())) {
      Parser parser = new Parser(in);
      parser.setOptions(opt);
      tree = parser.parseModel();
    }
    String before = dump(tree);
    for (int i = 0; i < 2; i++) {
      String built =
          capture(
              () -> {
                Parser parser = new Parser(java.io.InputStream.nullInputStream());
                parser.setOptions(opt);
                parser.build(tree);
              });
      assertEquals(
          """
          x = 0;
          y = 0;
          ----------
          x = 0;
          y = 1;
          ----------
          x = 0;
          y = 2;
          ----------
          x = 0;
          y = 3;
          ----------
          x = 1;
          y = 0;
          ----------
          x = 1;
          y = 1;
          ----------
          ==========""",
          solutionLines(built).strip());
      assertEquals(before, dump(tree));
    }
  }

  private static String dump(Node node) {
    StringBuilder s = new StringBuilder(node.toString());
    if (node instanceof ASTScalarFlatExpr e) {
      s.append(' ')
          .append(e.getType())
          .append(' ')
          .append(e.getIdent())
          .append(' ')
          .append(e.getInt());
    }
    s.append('(');
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      s.append(dump(node.jjtGetChild(i))).append(',');
    }
    return s.append(')').toString();
  }

  @Test
  void threadsBuildingFromOneTreeFindTheOptimum() throws IOException {
    Path fzn = write(MINIMISE);
    for (String oneParse : new String[] {"1", "0"}) {
      String out =
          run(
              "-p",
              "4",
              "-t",
              "20000",
              "--free-config",
              "portfolio-one-parse=" + oneParse,
              fzn.toString());
      assertTrue(out.contains("cost = 14;"), out);
      assertTrue(out.contains("=========="), out);
    }
  }

  // issue 797: a portfolio slower than one thread could not be attributed to a thread
  @Test
  void searchStatisticsPrintEachThread() throws IOException {
    Path fzn = write(MINIMISE);
    for (String[] stats : new String[][] {{"-s", "-v"}, {"-s", "--search-statistics"}}) {
      String out = run(stats[0], stats[1], "-p", "2", "-t", "20000", fzn.toString());
      assertTrue(out.contains("cost = 14;"), out);
      String block = out.substring(out.lastIndexOf("%%%mzn-stat: portfolioThread.given.ended="));
      assertTrue(block.contains("%%%mzn-stat: portfolioThread.given.nodes="), block);
      assertTrue(block.matches("(?s).*%%%mzn-stat: portfolioThread\\.[^.]+\\.solveTime=.*"), block);
      assertTrue(block.endsWith("%%%mzn-stat-end\n"), block);
    }
    // plain -s prints no thread statistics
    assertTrue(!run("-s", "-p", "2", fzn.toString()).contains("portfolioThread."));
  }

  @Test
  void aModelThatDoesNotParseIsReportedByTheThreads() throws IOException {
    Path fzn = write("var 1..3: x :: output_var;\nconstraint int_le(x, ;\nsolve satisfy;\n");
    AtomicReference<String> err = new AtomicReference<>();
    String out = run(err, "-p", "2", fzn.toString());
    assertTrue(!out.contains("x = "), out);
    assertTrue(err.get().contains("Parser error"), err.get());
  }

  private Path write(String model) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    return fzn;
  }

  private static String solutionLines(String out) {
    return String.join(
        "\n", Arrays.stream(out.split("\n")).filter(l -> !l.startsWith("%")).toList());
  }

  private interface Body {
    void run() throws Exception;
  }

  private static String capture(Body body) throws Exception {
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream c = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(c);
      body.run();
    } finally {
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  private static String run(String... args) {
    return run(new AtomicReference<>(), args);
  }

  private static String run(AtomicReference<String> err, String... args) {
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ByteArrayOutputStream errors = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    PrintStream originalErr = System.err;
    try (PrintStream o = new PrintStream(out, true, StandardCharsets.UTF_8);
        PrintStream e = new PrintStream(errors, true, StandardCharsets.UTF_8)) {
      System.setOut(o);
      System.setErr(e);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
      System.setErr(originalErr);
    }
    err.set(errors.toString(StandardCharsets.UTF_8));
    return out.toString(StandardCharsets.UTF_8);
  }

  @Test
  void aNumberOfSolutionsLimitsThePortfolioAsOneThread() throws IOException {
    // each thread stopped after k solutions of its own, and the portfolio printed every improving
    // solution of all of them: 8 solutions with -n 2 -p 4
    StringBuilder model = new StringBuilder();
    model.append("array [1..8] of var 0..9: x :: output_array([1..8]);\n");
    model.append("var 0..1000: cost :: output_var;\n");
    model.append("constraint int_lin_eq([1, 2, 3, 4, 5, 6, 7, 8, -1], [x[1], x[2], x[3], x[4], ");
    model.append("x[5], x[6], x[7], x[8], cost], 0);\n");
    model.append("constraint int_lin_le([-1, -1, -1, -1, -1, -1, -1, -1], [x[1], x[2], x[3], ");
    model.append("x[4], x[5], x[6], x[7], x[8]], -30);\n");
    model.append("solve :: int_search(x, input_order, indomain_max, complete) minimize cost;\n");
    Path fzn = tmp.resolve("limit.fzn");
    Files.writeString(fzn, model.toString(), StandardCharsets.UTF_8);
    assertEquals(2, count(run("-n", "2", fzn.toString()), "----------"));
    for (String p : new String[] {"2", "4"}) {
      String out = run("-n", "2", "-p", p, fzn.toString());
      // fewer when a thread proves a solution optimal before
      int printed = count(out, "----------");
      assertTrue(printed >= 1 && printed <= 2, out);
    }
  }

  private static int count(String out, String line) {
    return (int) out.lines().filter(line::equals).count();
  }
}
