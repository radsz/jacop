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
}
