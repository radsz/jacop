/*
 * PrecedenceFlatzincTest.java
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
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Predicate;
import java.util.stream.IntStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Checks the precedences the FlatZinc front end reads from the difference constraints of a model
 * and gives to jacop_reservoir and to the energy precedence posted for jacop_cumulative: all
 * solutions must match a brute-force enumeration.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
class PrecedenceFlatzincTest {

  @TempDir Path tmp;

  /** A difference constraint between x[first] and x[second] and its relation on an assignment. */
  private record Arc(String fzn, Predicate<int[]> holds) {}

  // a random difference constraint in one of the forms the front end reads
  private static Arc arc(Random random, int n, String name) {
    int a = random.nextInt(n);
    int b = (a + 1 + random.nextInt(n - 1)) % n;
    String x = name + a;
    String y = name + b;
    int lag = -1 + random.nextInt(4);
    switch (random.nextInt(5)) {
      case 0:
        return new Arc("constraint int_le(" + x + "," + y + ");\n", v -> v[a] <= v[b]);
      case 1:
        return new Arc("constraint int_lt(" + x + "," + y + ");\n", v -> v[a] < v[b]);
      case 2:
        {
          // k * (x - y) <= c
          int k = 1 + random.nextInt(3);
          int c = -k * lag + random.nextInt(k);
          return random.nextBoolean()
              ? new Arc(
                  "constraint int_lin_le(["
                      + k
                      + ","
                      + -k
                      + "],["
                      + x
                      + ","
                      + y
                      + "],"
                      + c
                      + ");\n",
                  v -> k * (v[a] - v[b]) <= c)
              : new Arc(
                  "constraint int_lin_le(["
                      + -k
                      + ","
                      + k
                      + "],["
                      + y
                      + ","
                      + x
                      + "],"
                      + c
                      + ");\n",
                  v -> k * (v[a] - v[b]) <= c);
        }
      case 3:
        return new Arc(
            "constraint int_lin_eq([1,-1],[" + y + "," + x + "]," + lag + ");\n",
            v -> v[b] - v[a] == lag);
      default:
        // not a difference: 2 * x - y <= lag
        return new Arc(
            "constraint int_lin_le([2,-1],[" + x + "," + y + "]," + lag + ");\n",
            v -> 2 * v[a] - v[b] <= lag);
    }
  }

  @Test
  void reservoirMatchesBruteForce() throws IOException {
    Random random = new Random(21);
    for (int trial = 0; trial < 300; trial++) {
      int n = 2 + random.nextInt(4);
      int[][] domains = new int[n][];
      int[] changes = new int[n];
      StringBuilder fzn = new StringBuilder();
      for (int i = 0; i < n; i++) {
        domains[i] = IntStream.rangeClosed(0, 4).filter(v -> random.nextInt(4) != 0).toArray();
        if (domains[i].length == 0) {
          domains[i] = new int[] {random.nextInt(5)};
        }
        changes[i] = random.nextBoolean() ? 1 + random.nextInt(3) : -1 - random.nextInt(3);
        fzn.append("var ").append(set(domains[i])).append(": t").append(i).append(";\n");
      }
      int min = -random.nextInt(4);
      int max = random.nextInt(5);
      fzn.append(array("t", n));
      List<Arc> arcs = new ArrayList<>();
      for (int k = random.nextInt(4); k > 0; k--) {
        arcs.add(arc(random, n, "t"));
        fzn.append(arcs.getLast().fzn());
      }
      fzn.append("constraint jacop_reservoir(t,")
          .append(set(changes).replace('{', '[').replace('}', ']'))
          .append(',')
          .append(min)
          .append(',')
          .append(max)
          .append(");\n");
      fzn.append("solve satisfy;\n");

      Set<String> expected = new TreeSet<>();
      enumerate(
          0,
          new int[n],
          domains,
          values -> {
            if (!arcs.stream().allMatch(arc -> arc.holds().test(values))) {
              return;
            }
            for (int time : values) {
              int level = 0;
              for (int i = 0; i < n; i++) {
                level += values[i] <= time ? changes[i] : 0;
              }
              if (level < min || level > max) {
                return;
              }
            }
            expected.add(output("t", values));
          });
      assertEquals(expected, solutions(run(fzn.toString(), "-a")), "trial " + trial + "\n" + fzn);
    }
  }

  @Test
  void energyPrecedenceKeepsAllSolutions() throws IOException {
    Random random = new Random(22);
    int posted = 0;
    for (int trial = 0; trial < 300; trial++) {
      // the tasks and an end point after all of them
      int n = 2 + random.nextInt(3);
      int[] durations = new int[n];
      int[] heights = new int[n];
      int limit = 1 + random.nextInt(3);
      StringBuilder fzn = new StringBuilder();
      for (int i = 0; i < n; i++) {
        durations[i] = random.nextInt(3);
        heights[i] = 1 + random.nextInt(limit);
        fzn.append("var 0..").append(3 + random.nextInt(3)).append(": s").append(i).append(";\n");
      }
      fzn.append("var 0..").append(4 + random.nextInt(4)).append(": s").append(n).append(";\n");
      fzn.append(array("s", n + 1));
      List<Arc> arcs = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        int task = i;
        arcs.add(
            new Arc(
                "constraint int_lin_le([1,-1],[s" + i + ",s" + n + "]," + -durations[i] + ");\n",
                v -> v[task] + durations[task] <= v[n]));
        fzn.append(arcs.getLast().fzn());
      }
      for (int k = random.nextInt(3); k > 0; k--) {
        arcs.add(arc(random, n, "s"));
        fzn.append(arcs.getLast().fzn());
      }
      StringBuilder starts = new StringBuilder();
      for (int i = 0; i < n; i++) {
        starts.append(i == 0 ? "" : ",").append('s').append(i);
      }
      fzn.append("constraint jacop_cumulative([")
          .append(starts)
          .append("],")
          .append(set(durations).replace('{', '[').replace('}', ']'))
          .append(',')
          .append(set(heights).replace('{', '[').replace('}', ']'))
          .append(',')
          .append(limit)
          .append(");\n");
      fzn.append("solve satisfy;\n");

      int[][] domains = new int[n + 1][];
      for (int i = 0; i <= n; i++) {
        String bound = fzn.toString().split("var 0\\.\\.")[i + 1].split(":")[0];
        domains[i] = IntStream.rangeClosed(0, Integer.parseInt(bound)).toArray();
      }
      Set<String> expected = new TreeSet<>();
      enumerate(
          0,
          new int[n + 1],
          domains,
          values -> {
            if (!arcs.stream().allMatch(arc -> arc.holds().test(values))) {
              return;
            }
            for (int time = 0; time <= values[n]; time++) {
              int load = 0;
              for (int i = 0; i < n; i++) {
                load += values[i] <= time && time < values[i] + durations[i] ? heights[i] : 0;
              }
              if (load > limit) {
                return;
              }
            }
            expected.add(output("s", values));
          });
      String out = run(fzn.toString(), "-a", "-debug");
      if (out.contains("% energy precedence on 1 of 1")) {
        posted++;
      }
      assertEquals(expected, solutions(out), "trial " + trial + "\n" + fzn);
    }
    assertTrue(posted > 100, "posted " + posted);
  }

  private static String array(String name, int n) {
    StringBuilder xs = new StringBuilder();
    for (int i = 0; i < n; i++) {
      xs.append(i == 0 ? "" : ",").append(name).append(i);
    }
    return "array [1.."
        + n
        + "] of var int: "
        + name
        + ":: output_array([1.."
        + n
        + "]) = ["
        + xs
        + "];\n";
  }

  private static String output(String name, int[] values) {
    return name + " = array1d(1.." + values.length + ", " + Arrays.toString(values) + ");";
  }

  private interface Visitor {
    void visit(int[] values);
  }

  private static void enumerate(int i, int[] x, int[][] domains, Visitor visitor) {
    if (i == x.length) {
      visitor.visit(x.clone());
      return;
    }
    for (int v : domains[i]) {
      x[i] = v;
      enumerate(i + 1, x, domains, visitor);
    }
  }

  private static String set(int[] values) {
    StringBuilder s = new StringBuilder("{");
    for (int k = 0; k < values.length; k++) {
      s.append(k == 0 ? "" : ",").append(values[k]);
    }
    return s.append('}').toString();
  }

  private String run(String model, String... options) throws IOException {
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

  private static Set<String> solutions(String out) {
    Set<String> solutions = new TreeSet<>();
    Arrays.stream(out.split("----------"))
        .map(
            s ->
                String.join(
                    " ",
                    new TreeSet<>(
                        Arrays.stream(s.strip().split("\\R"))
                            .filter(l -> !l.isBlank() && !l.startsWith("%"))
                            .toList())))
        .filter(s -> !s.isEmpty() && !s.startsWith("==========") && !s.contains("UNSATISFIABLE"))
        .forEach(solutions::add);
    return solutions;
  }
}
