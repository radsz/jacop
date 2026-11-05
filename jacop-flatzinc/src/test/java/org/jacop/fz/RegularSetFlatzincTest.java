/*
 * RegularSetFlatzincTest.java
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

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks jacop_regular_set (MiniZinc regular with a set alphabet) when the alphabet does not start
 * at 1. The transition table holds 1-based states whatever the alphabet; reading the states with
 * the alphabet offset crashed for alphabets from 0 and gave wrong UNSAT for alphabets from 2 (found
 * on an XCSP3 Nonogram instance converted by CPMpy, whose alphabets are 0..1).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class RegularSetFlatzincTest {

  @TempDir Path tmp;

  @Test
  void alphabetFromTwoKeepsTheOnlySolution() throws IOException {
    // states 1..3 from 1: 1 -2-> 2, 1 -3-> 3, 2 -2-> 2, 3 -3-> 3; accept {3}: only 3 3 3
    String fzn = model(3, 3, 2, 3, new int[] {2, 3, 2, 0, 0, 3}, Set.of(3));
    assertEquals(Set.of("x = array1d(1..3, [3, 3, 3]);"), solveAll(fzn));
  }

  @Test
  void randomAutomataMatchBruteForce() throws IOException {
    Random random = new Random(20261031);
    for (int run = 0; run < 40; run++) {
      int lo = random.nextInt(4) - 1; // alphabets from -1, 0, 1 or 2
      int symbols = 2 + random.nextInt(2);
      int states = 1 + random.nextInt(4);
      int n = 1 + random.nextInt(4);
      int[] d = new int[states * symbols];
      for (int i = 0; i < d.length; i++) {
        d[i] = random.nextInt(states + 1);
      }
      Set<Integer> finals = new TreeSet<>();
      for (int q = 1; q <= states; q++) {
        if (random.nextBoolean()) {
          finals.add(q);
        }
      }
      if (finals.isEmpty()) {
        finals.add(1 + random.nextInt(states));
      }
      Set<String> expected = new TreeSet<>();
      enumerate(new int[n], 0, lo, symbols, states, d, finals, expected);
      String fzn = model(n, states, lo, lo + symbols - 1, d, finals);
      assertEquals(expected, solveAll(fzn), "run " + run + "\n" + fzn);
    }
  }

  private static void enumerate(
      int[] x,
      int i,
      int lo,
      int symbols,
      int states,
      int[] d,
      Set<Integer> finals,
      Set<String> out) {
    if (i == x.length) {
      int q = 1;
      for (int v : x) {
        q = d[(q - 1) * symbols + (v - lo)];
        if (q == 0) {
          return;
        }
      }
      if (finals.contains(q)) {
        out.add(
            Arrays.stream(x)
                .mapToObj(String::valueOf)
                .collect(Collectors.joining(", ", "x = array1d(1.." + x.length + ", [", "]);")));
      }
      return;
    }
    for (int v = lo; v < lo + symbols; v++) {
      x[i] = v;
      enumerate(x, i + 1, lo, symbols, states, d, finals, out);
    }
  }

  private static String model(int n, int states, int lo, int hi, int[] d, Set<Integer> finals) {
    StringBuilder fzn = new StringBuilder();
    fzn.append(
        "predicate jacop_regular_set(array [int] of var int: x,int: Q,set of int: S,"
            + "array [int] of int: d,int: q0,set of int: F,int: min_index);\n");
    fzn.append("array [1..")
        .append(d.length)
        .append("] of int: d = ")
        .append(
            Arrays.stream(d).mapToObj(String::valueOf).collect(Collectors.joining(",", "[", "]")))
        .append(";\n");
    for (int i = 0; i < n; i++) {
      fzn.append("var ").append(lo).append("..").append(hi).append(": x").append(i).append(";\n");
    }
    fzn.append("array [1..")
        .append(n)
        .append("] of var int: x:: output_array([1..")
        .append(n)
        .append("]) = ")
        .append(
            IntStream.range(0, n).mapToObj(i -> "x" + i).collect(Collectors.joining(",", "[", "]")))
        .append(";\n");
    fzn.append("constraint jacop_regular_set(x,")
        .append(states)
        .append(',')
        .append(lo)
        .append("..")
        .append(hi)
        .append(",d,1,")
        .append(finals.stream().map(String::valueOf).collect(Collectors.joining(",", "{", "}")))
        .append(',')
        .append(lo)
        .append(");\nsolve satisfy;\n");
    return fzn.toString();
  }

  private String solve(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String[] args = Arrays.copyOf(options, options.length + 1);
    args[options.length] = fzn.toString();
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(args);
    } finally {
      System.setOut(originalOut);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  private Set<String> solveAll(String model) throws IOException {
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(solve(model, "-a").split("----------"))
        .map(String::strip)
        .filter(s -> s.startsWith("x = "))
        .forEach(solutions::add);
    return solutions;
  }
}
