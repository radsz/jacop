/*
 * DefaultSymmetryBruteForceTest.java
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
import static org.junit.jupiter.api.Assertions.fail;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Solves small symmetric and near-symmetric models with the symmetry breaking of the command line
 * default ({@code --symmetry on}; surefire sets {@code jacop.symmetry=presolve}, which turns it off
 * in every other FlatZinc test) and compares the answers with stored brute-force answers.
 *
 * <p>The models, in {@code default-symmetry-models.txt}, are graph colourings, bin packings,
 * cumulative and diffn schedules, 0/1 matrices with row and column sums, assignments with
 * all-different, gcc, count, nvalue, element and member, clauses closed under complement, Latin
 * squares, blocks of values with their counts, and card sequences with an inverse channel, some
 * with a symmetry broken in one way (a value left out of a domain, a side constraint, a removed
 * table row, an asymmetric objective, a bound or hole in the objective's domain, an equality of two
 * variables), and random search annotations. Each was picked where the default symmetry breaking
 * posts something (lex-leader constraints, value precedence, orbitopes, Schreier-Sims cuts or
 * conditional value swaps). The first blocks are the reproducers of earlier wrong answers (value
 * precedence under an objective whose domain misses the relabelled maximum, LateCount's dominance
 * against the lex-leader order, value permutations that move the counts of a gcc ranked first by
 * the annotation or by the model's own lex-leader constraint). Each block starts with {@code ## }
 * and the expected answer: {@code % unsat}, {@code % opt v}, or {@code % sat n} followed by the n
 * solutions ({@code % sol}, the values of the variables in declaration order).
 *
 * <p>Every model is solved without and with LCG, and every fourth under free search: a printed
 * solution must be one of the brute force, an optimum the brute-force optimum, UNSAT only for an
 * unsatisfiable model. The system property {@code symmetry.default.models} bounds the number of
 * models (all by default).
 */
class DefaultSymmetryBruteForceTest {

  private static final Pattern VAR = Pattern.compile("^var [^:]+: ([A-Za-z_][A-Za-z0-9_]*)");
  private static final Pattern VALUE = Pattern.compile("^([A-Za-z_][A-Za-z0-9_]*) = (.+);$");

  @TempDir Path tmp;

  private record Case(String header, String expect, Set<String> solutions, String model) {}

  private static List<Case> cases() throws IOException {
    List<Case> cases = new ArrayList<>();
    try (InputStream in =
        DefaultSymmetryBruteForceTest.class.getResourceAsStream("default-symmetry-models.txt")) {
      String text = new String(in.readAllBytes(), StandardCharsets.UTF_8);
      for (String block : text.split("(?m)^(?=## )")) {
        if (block.isBlank()) {
          continue;
        }
        String[] lines = block.split("\n");
        String expect = null;
        Set<String> solutions = new HashSet<>();
        StringBuilder model = new StringBuilder();
        for (int i = 1; i < lines.length; i++) {
          if (lines[i].startsWith("% sol ")) {
            solutions.add(lines[i].substring(6));
          } else if (lines[i].startsWith("% ")) {
            expect = lines[i].substring(2);
          } else {
            model.append(lines[i]).append('\n');
          }
        }
        cases.add(new Case(lines[0], expect, solutions, model.toString()));
      }
    }
    return cases;
  }

  @Test
  void defaultSymmetryBreakingKeepsTheBruteForceAnswers() throws IOException {
    List<Case> cases = cases();
    int limit = Integer.getInteger("symmetry.default.models", cases.size());
    assertTrue(cases.size() >= 100, "models read: " + cases.size());
    List<String> failures = new ArrayList<>();
    for (int k = 0; k < Math.min(limit, cases.size()); k++) {
      Case c = cases.get(k);
      List<String[]> configurations = new ArrayList<>();
      configurations.add(new String[] {"--symmetry", "on", "--lcg", "off"});
      configurations.add(new String[] {"--symmetry", "on", "--lcg", "on"});
      if (k % 4 == 0) {
        configurations.add(new String[] {"--symmetry", "on", "-f"});
      }
      for (String[] options : configurations) {
        String problem = check(c, run(c.model(), options));
        if (problem != null) {
          failures.add(
              c.header() + " " + String.join(" ", options) + ": " + problem + "\n" + c.model());
        }
      }
    }
    if (!failures.isEmpty()) {
      fail(failures.size() + " wrong answers, first:\n" + failures.get(0));
    }
  }

  /** The problem with the output of a run, or null. */
  private static String check(Case c, String out) {
    List<String> names = new ArrayList<>();
    for (String line : c.model().split("\n")) {
      Matcher m = VAR.matcher(line);
      if (m.find()) {
        names.add(m.group(1));
      }
    }
    boolean unsat = out.contains("=====UNSATISFIABLE=====");
    List<List<String>> printed = new ArrayList<>();
    String[] values = new String[names.size()];
    for (String line : out.split("\n")) {
      Matcher m = VALUE.matcher(line.trim());
      if (m.find()) {
        int i = names.indexOf(m.group(1));
        if (i >= 0) {
          values[i] = value(m.group(2));
        }
      } else if (line.equals("----------")) {
        printed.add(Arrays.asList(values));
        values = new String[names.size()];
      }
    }
    if (c.expect().equals("unsat")) {
      return unsat && printed.isEmpty() ? null : "expected UNSAT\n" + out;
    }
    if (unsat || printed.isEmpty()) {
      return "expected " + c.expect() + "\n" + out;
    }
    List<String> last = printed.get(printed.size() - 1);
    if (c.expect().startsWith("sat")) {
      if (printed.size() != 1) {
        return printed.size() + " solutions printed\n" + out;
      }
      String key = String.join(",", last);
      return c.solutions().contains(key) ? null : "not a solution: " + key + "\n" + out;
    }
    // an optimum: the objective is the variable of the solve item
    Matcher solve =
        Pattern.compile("(minimize|maximize) ([A-Za-z_][A-Za-z0-9_]*);").matcher(c.model());
    assertTrue(solve.find(), c.model());
    String objective = last.get(names.indexOf(solve.group(2)));
    String expected = c.expect().substring(4);
    if (!out.contains("==========")) {
      return "optimum not proved\n" + out;
    }
    return expected.equals(objective)
        ? null
        : "optimum " + objective + ", expected " + expected + "\n" + out;
  }

  /**
   * A printed value as the brute force writes it: a Boolean as 0 or 1, a set of 1..k as the bit
   * mask of its elements.
   */
  private static String value(String text) {
    if (text.equals("true") || text.equals("false")) {
      return text.equals("true") ? "1" : "0";
    }
    if (!text.startsWith("{") && !text.contains("..")) {
      return text;
    }
    int mask = 0;
    String elements = text.startsWith("{") ? text.substring(1, text.length() - 1) : text;
    for (String e : elements.split(",")) {
      e = e.trim();
      if (e.isEmpty()) {
        continue;
      }
      String[] range = e.split("\\.\\.");
      int lo = Integer.parseInt(range[0].trim());
      int hi = Integer.parseInt(range[range.length - 1].trim());
      for (int x = lo; x <= hi; x++) {
        mask |= 1 << (x - 1);
      }
    }
    return String.valueOf(mask);
  }

  private String run(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    String[] args = new String[options.length + 1];
    System.arraycopy(options, 0, args, 0, options.length);
    args[options.length] = fzn.toString();
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    PrintStream original = System.out;
    try (PrintStream capture = new PrintStream(out, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(original);
    }
    return out.toString(StandardCharsets.UTF_8).replace("\r\n", "\n");
  }

  @Test
  void corpusHasEveryKindOfSymmetry() throws IOException {
    Set<String> kinds = new HashSet<>();
    for (Case c : cases()) {
      String[] header = c.header().split(" ");
      kinds.addAll(List.of(header[header.length - 1].split(",")));
    }
    assertEquals(Set.of("lex", "valprec", "orbitope", "sscut", "swaps"), kinds);
  }
}
