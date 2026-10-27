/*
 * PresolveFlatzincTest.java
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

import static org.assertj.core.api.Assertions.assertThat;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;
import org.jacop.api.Copyable;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.presolve.Derivation;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Presolve on the models of the MiniZinc library hooks: every constraint FlatZinc posts for them
 * can be copied, and searching the derived store gives the solutions of the original store.
 */
class PresolveFlatzincTest {

  private static final String DIR = "src/test/fz/mznlib/";

  /** The number of solutions compared. */
  private static final int LIMIT = 1000;

  static Stream<String> models() throws IOException {
    try (Stream<Path> files = Files.list(Path.of(DIR))) {
      return files
          .map(p -> p.getFileName().toString())
          .filter(n -> n.endsWith(".fzn"))
          .sorted()
          .toList()
          .stream();
    }
  }

  @ParameterizedTest
  @MethodSource("models")
  void derivedStoreHasTheSolutionsOfTheOriginal(String model) {
    Store original;
    try {
      original = load(model);
    } catch (TrivialSolution e) {
      // the front end solved the model while loading it
      return;
    }
    IntVar[] originalVars = intVars(original);

    Store store = load(model);
    IntVar[] vars = intVars(store);
    constraints(store)
        .forEach(c -> assertThat(Copyable.canCopy(c)).as("%s in %s", c, model).isTrue());

    Derivation derivation = Derivation.of(store).retention(Derivation.Retention.KEPT).derive();
    assertThat(derivation.outcome()).as(model).isNotEqualTo(Derivation.Outcome.LIVE);
    if (originalVars == null || vars == null) {
      // a model with set or float variables: only its derivation is checked
      return;
    }

    // with the same variable order and smallest values first, both searches enumerate solutions in
    // lexicographic order, so their first solutions are the same however strong the propagation
    List<List<Integer>> expected = new ArrayList<>();
    if (original.consistency()) {
      solve(original, originalVars, () -> expected.add(values(originalVars)));
    }

    List<List<Integer>> found = new ArrayList<>();
    if (derivation.outcome() != Derivation.Outcome.INFEASIBLE) {
      IntVar[] counterparts = derivation.counterparts(vars);
      Store child = derivation.child();
      Runnable record =
          () -> {
            if (derivation.returnSolution()) {
              found.add(values(vars));
            }
          };
      if (child.consistency()) {
        if (counterparts.length == 0) {
          record.run();
        } else {
          solve(child, counterparts, record);
        }
      }
    }
    assertThat(found).as(model).isEqualTo(expected);
  }

  /**
   * The front end prints the same with presolve in checking mode as without it: the same solutions
   * in the same order, and checking mode verifies each of them against the loaded model.
   */
  @ParameterizedTest
  @MethodSource("models")
  void frontEndPrintsTheSameWithPresolve(String model) {
    assertThat(solve(model, "check")).as(model).isEqualTo(solve(model, "off"));
  }

  /** Solves a model with the front end, as from the command line, and returns what it prints. */
  private static String solve(String model, String presolve) {
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream out = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      new Fz2jacop()
          .callMain(
              new String[] {
                "-a",
                "-n",
                String.valueOf(LIMIT),
                "--default-search",
                "input",
                "--presolve",
                presolve,
                DIR + model
              });
    } finally {
      System.setOut(out);
    }
    return buffer.toString(StandardCharsets.UTF_8);
  }

  private static Store load(String model) {
    PrintStream out = System.out;
    try (PrintStream quiet = new PrintStream(OutputStream.nullOutputStream())) {
      System.setOut(quiet);
      FlatzincLoader loader = new FlatzincLoader(new String[] {DIR + model});
      loader.load();
      return loader.getStore();
    } finally {
      System.setOut(out);
    }
  }

  /** The integer variables of a store, or null if it has variables of other kinds. */
  private static IntVar[] intVars(Store store) {
    List<IntVar> result = new ArrayList<>();
    for (Var v : allVariables(store)) {
      if (!(v instanceof IntVar iv)) {
        return null;
      }
      result.add(iv);
    }
    return result.toArray(new IntVar[0]);
  }

  private static List<Var> allVariables(Store store) {
    List<Var> result = new ArrayList<>(Arrays.asList(store.vars).subList(0, store.size()));
    store.variablesHashMap.values().stream()
        .filter(v -> v.index() < 0)
        .sorted((a, b) -> a.id().compareTo(b.id()))
        .forEach(result::add);
    return result;
  }

  private static Set<Constraint> constraints(Store store) {
    Set<Constraint> result = new HashSet<>();
    for (Var v : allVariables(store)) {
      for (Constraint c : v.dom().constraints()) {
        if (c != null) {
          result.add(c);
        }
      }
    }
    return result;
  }

  private static List<Integer> values(IntVar[] vars) {
    return Arrays.stream(vars).map(IntVar::value).toList();
  }

  /** Finds the first {@link #LIMIT} solutions. */
  private static void solve(Store store, IntVar[] vars, Runnable onSolution) {
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            onSolution.run();
            return result;
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.getSolutionListener().setSolutionLimit(LIMIT);
    search.labeling(store, new SimpleSelect<>(vars, null, new IndomainMin<>()));
  }
}
