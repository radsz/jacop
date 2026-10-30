/*
 * MinizincCompetitionTest.java
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

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.math.BigDecimal;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.regex.Pattern;
import java.util.stream.Stream;
import java.util.zip.GZIPInputStream;
import org.jacop.floats.core.FloatDomain;
import org.jacop.fz.Fz2jacop;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Runs JaCoP on the MiniZinc Challenge instances of the radsz/minizinc-competition repository and
 * checks each answer against the golden reference of that repository. The references come from
 * other solvers (the Challenge's own per-instance results and runs of CP-SAT, Chuffed and Gecode),
 * never from JaCoP, so a failure means JaCoP answered something another solver contradicts.
 *
 * <p>The test needs a checkout of the repository and is not part of any build profile. Run it with
 *
 * <pre>
 * mvn -pl jacop-benchmarks test -Dtest=MinizincCompetitionTest -Dmznc.dir=../minizinc-competition
 *     [-Dmznc.tiers=upTo5sec,upTo30sec] [-Dmznc.options="-f"] [-Dmznc.filter=rcpsp]
 *     [-Dmznc.timeFactor=3]
 * </pre>
 *
 * <p>{@code mznc.dir} (or the environment variable {@code MZNC_DIR}) is the repository root;
 * without it the test is skipped. {@code mznc.tiers} selects the time categories (default
 * upTo5sec), {@code mznc.options} adds JaCoP options (for example {@code -f} or {@code --lcg -f}),
 * {@code mznc.filter} keeps instances whose name matches the regular expression, and {@code
 * mznc.timeFactor} multiplies the time limit of the category (default 3, as for the other FlatZinc
 * categories).
 *
 * <p>Each line of a category's {@code reference.txt} is {@code instance kind [value]}:
 *
 * <ul>
 *   <li>{@code UNSAT}: two solver families proved that there is no solution;
 *   <li>{@code SAT}: a solution exists;
 *   <li>{@code MIN v} or {@code MAX v}: two solver families proved the optimum v;
 *   <li>{@code MIN_FEAS v} or {@code MAX_FEAS v}: a solution with objective v exists, the optimum
 *       is not settled;
 *   <li>{@code UNKNOWN}: nothing certain is known; only a crash or a contradiction within JaCoP's
 *       own answer fails.
 * </ul>
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class MinizincCompetitionTest {

  private static final String OBJECTIVE = "%%%mzn-stat: objective=";
  private static final List<String> TIERS =
      List.of(
          "upTo5sec", "upTo30sec", "upTo1min", "upTo5min", "upTo10min", "upTo1hour", "above1hour");
  private static final long[] TIER_SECONDS = {5, 30, 60, 300, 600, 3600, 3600};

  /** One instance of the bench: its category and its reference line. */
  record Instance(String tier, String line) {
    @Override
    public String toString() {
      return tier + "/" + line;
    }
  }

  static Path root() {
    String dir = System.getProperty("mznc.dir", System.getenv("MZNC_DIR"));
    return dir == null || dir.isBlank() ? null : Path.of(dir);
  }

  static Stream<Instance> instances() throws IOException {
    Path root = root();
    if (root == null) {
      return Stream.of(new Instance("none", "none"));
    }
    Pattern filter = Pattern.compile(System.getProperty("mznc.filter", ""));
    List<Instance> all = new ArrayList<>();
    for (String tier : System.getProperty("mznc.tiers", "upTo5sec").split(",")) {
      Path reference = root.resolve("fz").resolve(tier.trim()).resolve("reference.txt");
      for (String line : Files.readAllLines(reference, StandardCharsets.UTF_8)) {
        if (!line.isBlank() && !line.startsWith("#") && filter.matcher(line).find()) {
          all.add(new Instance(tier.trim(), line.trim()));
        }
      }
    }
    return all.stream();
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("instances")
  void agreesWithTheReference(Instance instance) throws IOException {
    Assumptions.assumeTrue(
        root() != null, "set -Dmznc.dir to a checkout of radsz/minizinc-competition");
    String[] fields = instance.line().split("\\s+");
    String name = fields[0];
    String kind = fields[1];
    BigDecimal value = fields.length > 2 ? new BigDecimal(fields[2]) : null;

    int index = TIERS.indexOf(instance.tier());
    long seconds =
        (index < 0 ? 60 : TIER_SECONDS[index])
            * Long.parseLong(System.getProperty("mznc.timeFactor", "3"));
    List<String> output = run(instance.tier(), name, seconds);

    long solutions = output.stream().filter(l -> l.trim().equals("----------")).count();
    boolean complete = output.stream().anyMatch(l -> l.trim().equals("=========="));
    boolean unsat = output.stream().anyMatch(l -> l.contains("=====UNSATISFIABLE====="));
    List<BigDecimal> objectives =
        output.stream()
            .filter(l -> l.startsWith(OBJECTIVE))
            .map(l -> new BigDecimal(l.substring(OBJECTIVE.length()).trim()))
            .toList();
    String context = instance + "\n" + String.join("\n", tail(output));

    assertThat(complete && solutions == 0)
        .as("search reported complete without a solution: %s", context)
        .isFalse();
    assertThat(unsat && solutions > 0).as("UNSAT reported after a solution: %s", context).isFalse();
    switch (kind) {
      case "UNSAT" ->
          assertThat(solutions).as("solution of an UNSAT instance: %s", context).isZero();
      case "SAT" ->
          assertThat(unsat).as("UNSAT reported for a SAT instance: %s", context).isFalse();
      case "MIN", "MAX" -> {
        assertThat(unsat)
            .as("UNSAT reported for an instance with an optimum: %s", context)
            .isFalse();
        for (BigDecimal objective : objectives) {
          assertThat(better(kind, objective, value))
              .as("objective %s better than the optimum %s: %s", objective, value, context)
              .isFalse();
        }
        if (complete) {
          assertThat(objectives).as("no objective printed: %s", context).isNotEmpty();
          assertThat(compare(objectives.getLast(), value))
              .as("optimum %s, expected %s: %s", objectives.getLast(), value, context)
              .isZero();
        }
      }
      case "MIN_FEAS", "MAX_FEAS" -> {
        String direction = kind.substring(0, 3);
        assertThat(unsat).as("UNSAT reported for a feasible instance: %s", context).isFalse();
        if (complete && !objectives.isEmpty()) {
          assertThat(better(direction, value, objectives.getLast()))
              .as(
                  "optimum %s reported, but a solution with %s exists: %s",
                  objectives.getLast(), value, context)
              .isFalse();
        }
      }
      case "UNKNOWN" -> {
        // nothing is certain; the checks above still apply
      }
      default -> throw new IllegalArgumentException("Unknown kind in reference: " + instance);
    }
  }

  /** Whether objective a is strictly better than b for kind MIN or MAX. */
  private static boolean better(String kind, BigDecimal a, BigDecimal b) {
    int c = compare(a, b);
    return kind.startsWith("MIN") ? c < 0 : c > 0;
  }

  /**
   * Compares two objective values. Float objectives are printed rounded, so values that are not
   * both integers count as equal within a relative tolerance of 1e-5.
   */
  private static int compare(BigDecimal a, BigDecimal b) {
    boolean integers = a.stripTrailingZeros().scale() <= 0 && b.stripTrailingZeros().scale() <= 0;
    if (!integers) {
      double x = a.doubleValue();
      double y = b.doubleValue();
      if (Math.abs(x - y) <= 1e-5 * Math.max(1.0, Math.max(Math.abs(x), Math.abs(y)))) {
        return 0;
      }
    }
    return a.compareTo(b);
  }

  private static List<String> tail(List<String> lines) {
    return lines.size() <= 40 ? lines : lines.subList(lines.size() - 40, lines.size());
  }

  /**
   * Solves the instance (gunzipped to a temporary file if needed) and returns what JaCoP prints.
   */
  private static List<String> run(String tier, String name, long seconds) throws IOException {
    Path dir = root().resolve("fz").resolve(tier);
    Path fzn = dir.resolve(name + ".fzn");
    Path temporary = null;
    if (!Files.exists(fzn)) {
      temporary = Files.createTempFile("mznc", ".fzn");
      try (InputStream in =
          new GZIPInputStream(Files.newInputStream(dir.resolve(name + ".fzn.gz")))) {
        Files.copy(in, temporary, StandardCopyOption.REPLACE_EXISTING);
      }
      fzn = temporary;
    }
    List<String> args = new ArrayList<>();
    String options = System.getProperty("mznc.options", "").trim();
    if (!options.isEmpty()) {
      args.addAll(Arrays.asList(options.split("\\s+")));
    }
    args.addAll(List.of("-v", "-t", String.valueOf(seconds * 1000), fzn.toString()));
    PrintStream out = System.out;
    ByteArrayOutputStream captured = new ByteArrayOutputStream();
    try (PrintStream capture = new PrintStream(captured, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args.toArray(String[]::new));
    } finally {
      System.setOut(out);
      FloatDomain.setFormat(Double.MAX_VALUE);
      if (temporary != null) {
        Files.deleteIfExists(temporary);
      }
    }
    return captured.toString(StandardCharsets.UTF_8).lines().toList();
  }
}
