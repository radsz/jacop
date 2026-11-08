/*
 * DecompositionCheck.java
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

package org.jacop.decomposition;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;
import org.jacop.decomposition.AllSolutionsSuite.Objective;
import org.jacop.decomposition.FznBuilder.Term;
import org.jacop.fz.Fz2jacop;
import org.junit.jupiter.api.io.TempDir;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * The small models of the all-solutions suite ({@code src/test/fz/allsolutions}), each written for
 * a JaCoP global constraint that no benchmark problem uses: the model flattened with JaCoP's
 * library and the same model flattened with MiniZinc's standard library (every global decomposed)
 * must have the same solutions, and minimising a random linear objective with LCG must reach the
 * minimum of the objective over these solutions in both.
 *
 * <p>The full suite, {@link AllSolutionsSuite}, runs outside the build.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class AllSolutionsModelsTest {

  private static final Path DIR = Path.of("src/test/fz/allsolutions");

  @TempDir Path tmp;

  static Stream<String> models() throws IOException {
    try (Stream<Path> s = Files.list(DIR)) {
      return s
          .filter(p -> Files.exists(p.resolve(p.getFileName() + ".std.fzn")))
          .map(p -> p.getFileName().toString())
          .sorted()
          .toList()
          .stream();
    }
  }

  @ParameterizedTest
  @MethodSource("models")
  void sameSolutionsAsTheStandardDecomposition(String name) throws IOException {
    Path nativeFzn = DIR.resolve(name).resolve(name + ".fzn");
    Path stdFzn = DIR.resolve(name).resolve(name + ".std.fzn");
    String nativeText = Files.readString(nativeFzn, StandardCharsets.UTF_8);
    FznModel jacop = FznModel.parse(nativeText);
    FznModel std = FznModel.parse(Files.readString(stdFzn, StandardCharsets.UTF_8));
    Set<String> printed = AllSolutionsSuite.outputNames(jacop);
    printed.retainAll(AllSolutionsSuite.outputNames(std));

    Run all = solve(nativeFzn, "-a");
    Run allStd = solve(stdFzn, "-a");
    assertTrue(all.complete && allStd.complete, name + ": enumeration did not finish");
    assertEquals(projections(all, printed), projections(allStd, printed), name);

    List<Objective> objs =
        AllSolutionsSuite.objectives(jacop, DecompositionCheck.sha(nativeText), printed, 1, 1);
    if (objs.isEmpty() || all.solutions.isEmpty()) {
      return;
    }
    Objective o = objs.get(0);
    long min = Long.MAX_VALUE;
    for (String s : all.solutions) {
      min = Math.min(min, o.value(AllSolutionsSuite.values(jacop, s)));
    }
    for (FznModel m : List.of(jacop, std)) {
      Objective on = o.on(m);
      FznBuilder b = new FznBuilder(m, "X_DECOMP_");
      Term obj = AllSolutionsSuite.objectiveTerm(b, on);
      String text = DecompositionCheck.render(m, Set.of(), b, null, true, false);
      text = text.substring(0, text.lastIndexOf("satisfy;")) + "minimize " + obj.text() + ";\n";
      Path file = tmp.resolve(name + (m == std ? ".std" : "") + ".obj.fzn");
      Files.writeString(file, text, StandardCharsets.UTF_8);
      Run r = solve(file, "--lcg");
      assertTrue(r.complete && !r.solutions.isEmpty(), name + ": --lcg did not prove an optimum");
      assertEquals(
          min,
          on.value(AllSolutionsSuite.values(m, r.solutions.getLast())),
          name + (m == std ? " (standard decomposition)" : "") + ": --lcg minimum");
    }
  }

  private static Set<Long> projections(Run r, Set<String> names) {
    Set<Long> result = new HashSet<>();
    for (String s : r.solutions) {
      result.add(AllSolutionsSuite.projection(s, names));
    }
    return result;
  }

  private record Run(List<String> solutions, boolean complete) {}

  private Run solve(Path fzn, String option) throws IOException {
    // the solutions and the final status line, as printed on the standard output
    ByteArrayOutputStream bytes = new ByteArrayOutputStream();
    PrintStream stdout = System.out;
    try (PrintStream capture = new PrintStream(bytes, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop().callMain(new String[] {option, "-t", "60000", fzn.toString()});
    } finally {
      System.setOut(stdout);
    }
    List<String> solutions = new ArrayList<>();
    StringBuilder current = new StringBuilder();
    boolean complete = false;
    for (String line : bytes.toString(StandardCharsets.UTF_8).split("\n")) {
      String t = line.strip();
      if (t.isEmpty() || t.startsWith("%")) {
        continue;
      }
      switch (t) {
        case "----------" -> {
          solutions.add(current.toString());
          current.setLength(0);
        }
        case "==========", "=====UNSATISFIABLE=====" -> complete = true;
        default -> current.append(t).append('\n');
      }
    }
    return new Run(solutions, complete);
  }
}
