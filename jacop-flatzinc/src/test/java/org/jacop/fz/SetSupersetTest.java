/*
 * SetSupersetTest.java
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
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.BiPredicate;
import java.util.stream.Stream;
import org.junit.jupiter.api.Timeout;
import org.junit.jupiter.api.io.TempDir;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Checks the FlatZinc builtins set_superset(x, y) (x is a superset of y) and set_superset_reif(x,
 * y, r) (r iff x is a superset of y) by comparing every solution JaCoP finds with a brute-force
 * enumeration of all assignments.
 */
class SetSupersetTest {

  private static final int TIMEOUT_MS = 15_000;

  @TempDir Path tmp;

  /** A set argument: either a variable with domain lo..hi, or a fixed set literal. */
  private record SetArg(String name, int lo, int hi, Integer fixed) {

    static SetArg var(String name, int lo, int hi) {
      return new SetArg(name, lo, hi, null);
    }

    static SetArg fixed(int mask) {
      return new SetArg(null, 0, 0, mask);
    }

    boolean isVar() {
      return fixed == null;
    }

    List<Integer> values() {
      List<Integer> result = new ArrayList<>();
      if (isVar()) {
        // masks over bits lo..hi
        int width = hi - lo + 1;
        for (int m = 0; m < (1 << width); m++) {
          result.add(m << lo);
        }
      } else {
        result.add(fixed);
      }
      return result;
    }

    String fzn() {
      return isVar() ? name : literal(fixed);
    }
  }

  static Stream<Arguments> cases() {
    SetArg x = SetArg.var("x", 1, 4);
    SetArg y = SetArg.var("y", 1, 4);
    SetArg xNarrow = SetArg.var("x", 1, 3);
    SetArg yShifted = SetArg.var("y", 2, 5);
    SetArg c23 = SetArg.fixed(mask(2, 3));
    SetArg c123 = SetArg.fixed(mask(1, 2, 3));
    SetArg empty = SetArg.fixed(0);
    return Stream.of(
        Arguments.of(x, y, null),
        Arguments.of(xNarrow, yShifted, null),
        Arguments.of(yShifted, xNarrow, null),
        Arguments.of(x, c23, null),
        Arguments.of(c123, y, null),
        Arguments.of(empty, y, null),
        Arguments.of(x, y, "b"),
        Arguments.of(xNarrow, yShifted, "b"),
        Arguments.of(yShifted, xNarrow, "b"),
        Arguments.of(x, y, "true"),
        Arguments.of(x, y, "false"),
        Arguments.of(xNarrow, yShifted, "false"),
        Arguments.of(x, c23, "b"),
        Arguments.of(c123, y, "b"),
        Arguments.of(c23, y, "false"),
        Arguments.of(empty, y, "b"));
  }

  @ParameterizedTest(name = "set_superset{2}({0}, {1})")
  @MethodSource("cases")
  @Timeout(TIMEOUT_MS)
  void allSolutionsMatchBruteForce(SetArg a, SetArg b, String reif) throws IOException {
    BiPredicate<Integer, Integer> superset = (va, vb) -> (vb & ~va) == 0;

    StringBuilder fzn = new StringBuilder();
    List<String> outputs = new ArrayList<>();
    for (SetArg s : List.of(a, b)) {
      if (s.isVar()) {
        fzn.append("var set of ")
            .append(s.lo())
            .append("..")
            .append(s.hi())
            .append(": ")
            .append(s.name())
            .append(":: output_var;\n");
        outputs.add(s.name());
      }
    }
    boolean reifVar = "b".equals(reif);
    if (reifVar) {
      fzn.append("var bool: b:: output_var;\n");
    }
    if (reif == null) {
      fzn.append("constraint set_superset(").append(a.fzn()).append(",").append(b.fzn());
    } else {
      fzn.append("constraint set_superset_reif(")
          .append(a.fzn())
          .append(",")
          .append(b.fzn())
          .append(",")
          .append(reif);
    }
    fzn.append(");\nsolve satisfy;\n");

    Set<String> expected = new TreeSet<>();
    for (int va : a.values()) {
      for (int vb : b.values()) {
        boolean holds = superset.test(va, vb);
        // a free reification variable admits every pair; a fixed one only matching pairs
        boolean keep =
            switch (reif == null ? "true" : reif) {
              case "true" -> holds;
              case "false" -> !holds;
              default -> true;
            };
        if (!keep) {
          continue;
        }
        StringBuilder sol = new StringBuilder();
        if (a.isVar()) {
          sol.append(a.name()).append("=").append(literal(va)).append(";");
        }
        if (b.isVar()) {
          sol.append(b.name()).append("=").append(literal(vb)).append(";");
        }
        if (reifVar) {
          sol.append("b=").append(holds).append(";");
        }
        expected.add(sol.toString());
      }
    }

    List<String> actual = solve(fzn.toString());
    Set<String> actualSet = new TreeSet<>(actual);

    assertEquals(actual.size(), actualSet.size(), "duplicate solutions for\n" + fzn);
    assertEquals(expected, actualSet, "solutions differ for\n" + fzn);
  }

  /** Solves the model for all solutions and returns each one in canonical form. */
  private List<String> solve(String model) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);

    ByteArrayOutputStream captured = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try {
      System.setOut(new PrintStream(captured, true, StandardCharsets.UTF_8));
      new Fz2jacop().callMain(new String[] {"-a", fzn.toString()});
    } finally {
      System.setOut(originalOut);
    }

    List<String> lines = captured.toString(StandardCharsets.UTF_8).lines().toList();
    assertTrue(lines.contains("=========="), "search did not complete:\n" + lines);

    List<String> solutions = new ArrayList<>();
    StringBuilder current = new StringBuilder();
    for (String line : lines) {
      String l = line.trim();
      if ("----------".equals(l)) {
        solutions.add(current.toString());
        current.setLength(0);
      } else if (l.contains("=") && !l.startsWith("=") && !l.startsWith("%")) {
        String name = l.substring(0, l.indexOf('=')).trim();
        String value = l.substring(l.indexOf('=') + 1, l.lastIndexOf(';')).trim();
        String canonical =
            "true".equals(value) || "false".equals(value) ? value : literal(parseSet(value));
        current.append(name).append("=").append(canonical).append(";");
      }
    }
    return solutions;
  }

  /** Parses JaCoP set output such as {}, 2..4 or {1, 3..4}. */
  private static int parseSet(String text) {
    String body = text.replace("{", "").replace("}", "").trim();
    int m = 0;
    if (body.isEmpty()) {
      return m;
    }
    for (String part : body.split(",")) {
      String p = part.trim();
      int dots = p.indexOf("..");
      int lo = Integer.parseInt(dots < 0 ? p : p.substring(0, dots));
      int hi = Integer.parseInt(dots < 0 ? p : p.substring(dots + 2));
      for (int v = lo; v <= hi; v++) {
        m |= 1 << v;
      }
    }
    return m;
  }

  private static int mask(int... values) {
    int m = 0;
    for (int v : values) {
      m |= 1 << v;
    }
    return m;
  }

  private static String literal(int mask) {
    StringBuilder sb = new StringBuilder("{");
    for (int v = 0; v < Integer.SIZE - 1; v++) {
      if ((mask & (1 << v)) != 0) {
        if (sb.length() > 1) {
          sb.append(",");
        }
        sb.append(v);
      }
    }
    return sb.append("}").toString();
  }
}
