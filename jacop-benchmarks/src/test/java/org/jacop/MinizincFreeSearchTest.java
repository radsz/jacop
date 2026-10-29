/*
 * MinizincFreeSearchTest.java
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

package org.jacop;

import static org.assertj.core.api.Assertions.assertThat;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;
import org.jacop.floats.core.FloatDomain;
import org.jacop.fz.Fz2jacop;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Runs free search ({@code -f}) on the upTo5sec models and compares its answer with the one of the
 * model's own search, recorded in {@code free-search-reference.txt}: the same satisfiability, the
 * same optimum and the same number of solutions when free search completes, and never an objective
 * better than the optimum. Free search finds other solutions in another order, so the outputs
 * themselves are not compared.
 *
 * <p>The system property {@code freesearch.options} replaces {@code -f}, for example {@code
 * -Dfreesearch.options="--lcg on --presolve check"} checks the default fixed search of fzn-jacop.
 *
 * <p>Each line of the reference file is {@code model kind value}: kind {@code UNSAT}, {@code SAT}
 * (one solution), {@code ALL} (value is the number of solutions), {@code MIN} or {@code MAX} (value
 * is the optimum).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class MinizincFreeSearchTest {

  private static final String CATEGORY = "src/test/fz/upTo5sec/";
  private static final String REFERENCE = CATEGORY + "free-search-reference.txt";
  private static final String TIME_LIMIT_MS = "5000";
  private static final String OBJECTIVE = "%%%mzn-stat: objective=";

  static Stream<String> reference() throws IOException {
    return Files.readAllLines(Path.of(REFERENCE), StandardCharsets.UTF_8).stream()
        .filter(l -> !l.isBlank() && !l.startsWith("#"));
  }

  @ParameterizedTest
  @MethodSource("reference")
  @Timeout(30)
  void freeSearchAgreesWithTheModelSearch(String line) throws IOException {
    check(line, List.of(System.getProperty("freesearch.options", "-f").trim().split("\\s+")));
  }

  /**
   * Solves a model of the reference with the given search options and checks the result against the
   * reference line.
   */
  static void check(String line, List<String> searchOptions) throws IOException {
    String[] fields = line.trim().split("\\s+");
    String model = fields[0];
    String kind = fields[1];
    long value = fields.length > 2 ? Long.parseLong(fields[2]) : 0;

    List<String> output = run(model, searchOptions);
    long solutions = output.stream().filter(l -> l.trim().equals("----------")).count();
    boolean complete = output.stream().anyMatch(l -> l.trim().equals("=========="));
    boolean unsat = output.stream().anyMatch(l -> l.contains("=====UNSATISFIABLE====="));
    List<Long> objectives =
        output.stream()
            .filter(l -> l.startsWith(OBJECTIVE))
            .map(l -> Long.parseLong(l.substring(OBJECTIVE.length()).trim()))
            .toList();
    String context = model + " (" + line.trim() + ")\n" + String.join("\n", output);

    assertThat(complete && solutions == 0)
        .as("search reported complete without a solution: %s", context)
        .isFalse();
    switch (kind) {
      case "UNSAT" -> assertThat(solutions).as("solution of an UNSAT model: %s", context).isZero();
      case "SAT" -> assertThat(unsat).as("UNSAT reported for a SAT model: %s", context).isFalse();
      case "ALL" -> {
        assertThat(unsat && value > 0).as("UNSAT reported: %s", context).isFalse();
        assertThat(solutions)
            .as("more solutions than exist: %s", context)
            .isLessThanOrEqualTo(value);
        if (complete) {
          assertThat(solutions).as("number of solutions: %s", context).isEqualTo(value);
        }
      }
      case "MIN", "MAX" -> {
        assertThat(unsat).as("UNSAT reported for a model with an optimum: %s", context).isFalse();
        for (long objective : objectives) {
          assertThat(kind.equals("MIN") ? objective >= value : objective <= value)
              .as("objective %d better than the optimum %d: %s", objective, value, context)
              .isTrue();
        }
        if (complete) {
          assertThat(objectives).as("no objective printed: %s", context).isNotEmpty();
          assertThat(objectives.getLast()).as("optimum: %s", context).isEqualTo(value);
        }
      }
      default -> throw new IllegalArgumentException("Unknown kind in " + REFERENCE + ": " + line);
    }
  }

  /** Runs the model with the search options and returns what it prints. */
  private static List<String> run(String model, List<String> searchOptions) throws IOException {
    String fzn = CATEGORY + model + ".fzn";
    List<String> args = new ArrayList<>();
    Path options = Path.of(fzn).getParent().resolve("options.opt");
    if (Files.exists(options)) {
      try (BufferedReader reader = Files.newBufferedReader(options, Charset.defaultCharset())) {
        args.add(reader.readLine());
        args.add(reader.readLine());
      }
    }
    args.addAll(searchOptions);
    args.addAll(List.of("-v", "-t", TIME_LIMIT_MS, fzn));
    PrintStream out = System.out;
    ByteArrayOutputStream captured = new ByteArrayOutputStream();
    try (PrintStream capture = new PrintStream(captured, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args.toArray(String[]::new));
    } finally {
      System.setOut(out);
      FloatDomain.setFormat(Double.MAX_VALUE);
    }
    return captured.toString(StandardCharsets.UTF_8).lines().toList();
  }
}
