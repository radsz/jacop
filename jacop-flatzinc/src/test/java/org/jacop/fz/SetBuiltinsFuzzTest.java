/*
 * SetBuiltinsFuzzTest.java
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
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Predicate;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random small FlatZinc models over set variables, solved for all solutions and compared with
 * brute-force enumeration of the builtins' MiniZinc meaning.
 *
 * <p>Each model has two or three set variables over small universes, a few integer and Boolean
 * variables, and one to four calls of the set builtins (set_*, array_(var_)set_element and the
 * jacop_* set globals of JaCoP's mznlib), with constants, repeated variables and reifications,
 * under a random set_search annotation. Each model is solved three times, with the LCG explanation
 * checker on:
 *
 * <ul>
 *   <li>all solutions with plain search: exactly the enumerated ones and, under input_order, in the
 *       order the annotation defines: for each set in the annotation's order, each element from the
 *       smallest (indomain_min, outdomain_min) or the largest, with the element in the set first
 *       (indomain) or out of it first (outdomain);
 *   <li>one solution with LCG: the first of that order under input_order, UNSAT when there is none;
 *   <li>in turn, the optimum of a random integer variable (LCG with the annotation, LCG with free
 *       search, plain search), or all solutions with presolve or with free search.
 * </ul>
 *
 * <pre>
 * mvn -Pmin -pl jacop-flatzinc test -Dtest=SetBuiltinsFuzzTest -Dsurefire.rerunFailingTestsCount=0 \
 *     -Dsetfuzz.trials=5000 -Dsetfuzz.seed=7
 * </pre>
 *
 * <p>{@code -Dsetfuzz.dump=DIR} also writes each model to DIR, and {@code -Dsetfuzz.std=true}
 * leaves out the jacop_* globals, so the models can be given to other solvers.
 */
class SetBuiltinsFuzzTest {

  private static final int TRIALS = Integer.getInteger("setfuzz.trials", 300);
  private static final long SEED = Long.getLong("setfuzz.seed", 20261105L);
  private static final String DUMP = System.getProperty("setfuzz.dump");
  private static final boolean STANDARD_ONLY = Boolean.getBoolean("setfuzz.std");
  private static final int MAX_CALLS = Integer.getInteger("setfuzz.calls", 4);

  /** Element e of a set is bit e + OFF of its mask. */
  private static final int OFF = 4;

  private static final int MAX_ASSIGNMENTS = 1 << 21;
  private static final int MAX_SOLUTIONS = 300;
  private static final int MAX_REPORTED = 5;

  private static final String[] VAR_SELECTIONS = {
    "input_order",
    "input_order",
    "first_fail",
    "anti_first_fail",
    "smallest",
    "largest",
    "occurrence",
    "most_constrained"
  };
  private static final String[] VALUE_SELECTIONS = {
    "indomain_min", "indomain_max", "outdomain_min", "outdomain_max"
  };

  @TempDir Path tmp;

  private enum Kind {
    SET,
    INT,
    BOOL
  }

  /** A variable: a set over the elements of mask lub, an integer lo..hi or a Boolean. */
  private record Var(String name, Kind kind, int lo, int hi, int lub) {

    /** All values: masks of the subsets of lub, the integers lo..hi, or 0 and 1. */
    int[] values() {
      if (kind != Kind.SET) {
        int[] v = new int[hi - lo + 1];
        Arrays.setAll(v, i -> lo + i);
        return v;
      }
      List<Integer> masks = new ArrayList<>();
      int sub = lub;
      while (true) {
        masks.add(sub);
        if (sub == 0) {
          break;
        }
        sub = (sub - 1) & lub;
      }
      return masks.stream().mapToInt(Integer::intValue).toArray();
    }
  }

  /** An argument of a call: variable index var, or a constant value when var is negative. */
  private record Arg(int aVar, int value, String text) {
    int of(int[] v) {
      return aVar >= 0 ? v[aVar] : value;
    }
  }

  /** One call: its FlatZinc text and its meaning on a complete assignment. */
  private record Call(String fzn, Predicate<int[]> holds) {}

  /** A random model. */
  private static final class Model {
    final List<Var> vars = new ArrayList<>();
    final List<Call> calls = new ArrayList<>();
    final Random r;
    int[] setOrder;
    String varSelection;
    String valueSelection;

    Model(Random r) {
      this.r = r;
    }

    List<Integer> ofKind(Kind k) {
      List<Integer> l = new ArrayList<>();
      for (int i = 0; i < vars.size(); i++) {
        if (vars.get(i).kind == k) {
          l.add(i);
        }
      }
      return l;
    }

    int pick(Kind k) {
      List<Integer> l = ofKind(k);
      return l.get(r.nextInt(l.size()));
    }

    Arg setVar() {
      int i = pick(Kind.SET);
      return new Arg(i, 0, vars.get(i).name);
    }

    /** A set variable, or now and then a constant set. */
    Arg set(boolean constantAllowed) {
      if (constantAllowed && r.nextInt(5) == 0) {
        int mask = 0;
        for (int e = -1; e <= 5; e++) {
          if (r.nextInt(3) == 0) {
            mask |= 1 << (e + OFF);
          }
        }
        return new Arg(-1, mask, setLiteral(mask, r));
      }
      return setVar();
    }

    Arg intArg() {
      if (r.nextInt(5) == 0) {
        int c = r.nextInt(7) - 1;
        return new Arg(-1, c, Integer.toString(c));
      }
      int i = pick(Kind.INT);
      return new Arg(i, 0, vars.get(i).name);
    }

    Arg boolArg() {
      if (r.nextInt(8) == 0) {
        boolean b = r.nextBoolean();
        return new Arg(-1, b ? 1 : 0, Boolean.toString(b));
      }
      int i = pick(Kind.BOOL);
      return new Arg(i, 0, vars.get(i).name);
    }

    /** Two set arguments, at least one of them a variable. */
    Arg[] twoSets() {
      Arg a = set(true);
      Arg b = a.aVar < 0 ? setVar() : set(true);
      return r.nextBoolean() ? new Arg[] {a, b} : new Arg[] {b, a};
    }

    String fzn(String goal) {
      StringBuilder sb = new StringBuilder();
      for (Var v : vars) {
        String type =
            switch (v.kind) {
              case SET -> "var set of " + setLiteral(v.lub, r);
              case INT -> "var " + v.lo + ".." + v.hi;
              case BOOL -> "var bool";
            };
        sb.append(type).append(": ").append(v.name).append(" :: output_var;\n");
      }
      for (Call c : calls) {
        sb.append("constraint ").append(c.fzn).append(";\n");
      }
      List<String> searches = new ArrayList<>();
      List<String> sets = new ArrayList<>();
      for (int i : setOrder) {
        sets.add(vars.get(i).name);
      }
      searches.add(
          "set_search(["
              + String.join(", ", sets)
              + "], "
              + varSelection
              + ", "
              + valueSelection
              + ", complete)");
      for (Kind k : new Kind[] {Kind.INT, Kind.BOOL}) {
        List<String> names = ofKind(k).stream().map(i -> vars.get(i).name).toList();
        if (!names.isEmpty()) {
          searches.add(
              (k == Kind.INT ? "int" : "bool")
                  + "_search(["
                  + String.join(", ", names)
                  + "], input_order, indomain_min, complete)");
        }
      }
      sb.append("solve :: seq_search([")
          .append(String.join(", ", searches))
          .append("]) ")
          .append(goal)
          .append(";\n");
      return sb.toString();
    }
  }

  @Test
  void setBuiltinsAgreeWithEnumeration() throws IOException {
    Random r = new Random(SEED);
    List<String> failures = new ArrayList<>();
    int checked = 0;
    System.setProperty("jacop.lcg.check", "true");
    try {
      for (int trial = 0; trial < TRIALS && failures.size() < MAX_REPORTED; trial++) {
        Model m = randomModel(r);
        List<int[]> expected = bruteForce(m);
        if (expected == null) {
          trial--;
          continue;
        }
        checked++;
        expected.sort(annotationOrder(m));
        String error = check(m, expected, trial, r);
        if (error != null) {
          failures.add("trial " + trial + " " + error);
        }
      }
    } finally {
      System.clearProperty("jacop.lcg.check");
    }
    assertTrue(
        failures.isEmpty(),
        failures.size() + " failing model(s) of " + checked + "\n" + String.join("\n", failures));
  }

  // outdomain_min and outdomain_max fell back to indomain_min with a warning
  @Test
  void outdomainLeavesTheElementOutFirst() throws IOException {
    String[][] firsts = {
      {"indomain_min", "1..1"},
      {"indomain_max", "4..4"},
      {"outdomain_min", "4..4"},
      {"outdomain_max", "1..1"}
    };
    for (String[] f : firsts) {
      String fzn =
          "var set of 1..4: s :: output_var;\n"
              + "constraint set_card(s, 1);\n"
              + "solve :: set_search([s], input_order, "
              + f[0]
              + ", complete) satisfy;\n";
      for (String[] options : new String[][] {{"--lcg", "off"}, {"--lcg"}}) {
        assertEquals(
            List.of("s = " + f[1] + ";"),
            solutionLines(fzn, options),
            f[0] + " " + String.join(" ", options));
      }
    }
  }

  // smallest and largest chose by the cardinality of the glb and the lub, most_constrained by the
  // glb; MiniZinc (and Gecode for smallest and largest) look at the undecided elements. The two
  // sets hold one element together, so the set chosen first takes its smallest one.
  @Test
  void setVariableSelectionLooksAtTheUndecidedElements() throws IOException {
    String[][] cases = {
      // selection, lub of s1, lub of s2, annotation order, first solution
      {"smallest", "{3}", "1..2", "s1, s2", "s1 = {}; s2 = 1..1;"},
      {"largest", "{1, 7}", "2..4", "s2, s1", "s1 = 1..1; s2 = {};"},
      {"most_constrained", "1..3", "4..5", "s1, s2", "s1 = {}; s2 = 4..4;"}
    };
    for (String[] c : cases) {
      String fzn =
          "var set of "
              + c[1]
              + ": s1 :: output_var;\nvar set of "
              + c[2]
              + ": s2 :: output_var;\nvar set of 1..7: u;\n"
              + "constraint set_union(s1, s2, u);\nconstraint set_card(u, 1);\n"
              + "solve :: set_search(["
              + c[3]
              + "], "
              + c[0]
              + ", indomain_min, complete) satisfy;\n";
      for (String[] options : new String[][] {{"--lcg", "off"}, {"--lcg"}}) {
        assertEquals(
            List.of(c[4]), solutionLines(fzn, options), c[0] + " " + String.join(" ", options));
      }
    }
  }

  // an array literal of set variables was rejected: "var_set_element with list of set variables
  // is not available"
  @Test
  void arrayVarSetElementTakesAnArrayLiteralOfVariables() throws IOException {
    String fzn =
        """
        var set of 1..2: a :: output_var;
        var set of 2..3: b :: output_var;
        var 1..2: i :: output_var;
        constraint array_var_set_element(i, [a, b], 2..2);
        solve satisfy;
        """;
    // i = 1 with a = {2} and any b, or i = 2 with b = {2} and any a
    assertEquals(8, solutionCount(fzn, "-a"));
  }

  // ChannelBoolSet rejects a repeated variable, so the model had no solution
  @Test
  void linkSetToBooleansTakesARepeatedBoolean() throws IOException {
    String fzn =
        """
        var set of 0..1: s :: output_var;
        var bool: b :: output_var;
        constraint jacop_link_set_to_booleans(s, [b, b], 0);
        solve satisfy;
        """;
    assertEquals(
        Set.of("b = false; s = {};", "b = true; s = 0..1;"),
        new java.util.TreeSet<>(solutionLines(fzn, "-a")));
  }

  /** The solutions a run prints, each as its sorted output lines joined by a space. */
  private List<String> solutionLines(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("case.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      List<String> args = new ArrayList<>(Arrays.asList(options));
      args.add(fzn.toString());
      new Fz2jacop().callMain(args.toArray(new String[0]));
    } finally {
      System.setOut(originalOut);
    }
    List<String> solutions = new ArrayList<>();
    for (String block : buffer.toString(StandardCharsets.UTF_8).split("----------")) {
      List<String> lines =
          Arrays.stream(block.strip().split("\\R"))
              .filter(l -> l.contains(" = ") && !l.startsWith("%"))
              .sorted()
              .toList();
      if (!lines.isEmpty()) {
        solutions.add(String.join(" ", lines));
      }
    }
    return solutions;
  }

  private int solutionCount(String model, String... options) throws IOException {
    return solutionLines(model, options).size();
  }

  /**
   * Solves a model three ways: all solutions with plain search, the first solution with LCG, and in
   * turn an objective (LCG with the annotation, LCG with free search, plain search) or all
   * solutions with presolve or free search. Returns the first disagreement, or null.
   */
  private String check(Model m, List<int[]> expected, int trial, Random r) throws IOException {
    boolean ordered = m.varSelection.equals("input_order");
    String satisfy = m.fzn("satisfy");
    if (DUMP != null) {
      Path dir = Path.of(DUMP);
      Files.createDirectories(dir);
      Files.writeString(dir.resolve("set-" + trial + ".fzn"), satisfy, StandardCharsets.UTF_8);
    }
    List<Integer> ints = m.ofKind(Kind.INT);
    int objective = ints.get(r.nextInt(ints.size()));
    boolean minimize = r.nextBoolean();
    String optimize = m.fzn((minimize ? "minimize " : "maximize ") + m.vars.get(objective).name);
    // the build runs the tests with LCG off by default (jacop.lcg), so LCG is asked for
    String[][] third = {
      {"--lcg"}, {"--lcg", "-f"}, {"--lcg", "off"}, {"-a", "--presolve", "on"}, {"-a", "-f"}
    };
    String[] options3 = third[trial % third.length];
    boolean optimization = !Arrays.asList(options3).contains("-a");
    Object[][] runs = {
      {satisfy, new String[] {"-a", "--lcg", "off"}, "ordered"},
      {satisfy, new String[] {"--lcg"}, "first"},
      {optimization ? optimize : satisfy, options3, optimization ? "optimum" : "all"}
    };
    for (Object[] run : runs) {
      String fzn = (String) run[0];
      String[] options = (String[]) run[1];
      String error;
      try {
        Output out = solve(m, fzn, options);
        error =
            switch ((String) run[2]) {
              case "ordered" -> compare(m, expected, out, ordered);
              case "all" -> compare(m, expected, out, false);
              case "first" -> first(m, expected, out, ordered);
              default -> optimum(m, expected, out, objective, minimize);
            };
      } catch (RuntimeException | StackOverflowError e) {
        error = "exception " + e;
      }
      if (error != null) {
        return "options " + Arrays.toString(options) + ": " + error + "\n" + fzn;
      }
    }
    return null;
  }

  // ---------------------------------------------------------------- the random models

  private static Model randomModel(Random r) {
    Model m = new Model(r);
    int sets = 2 + r.nextInt(2);
    for (int i = 1; i <= sets; i++) {
      int base = r.nextInt(4) - 1;
      int width = 3 + r.nextInt(3);
      int lub = 0;
      while (Integer.bitCount(lub) < 1) {
        for (int e = base; e < base + width; e++) {
          if (r.nextInt(4) != 0 && Integer.bitCount(lub) < 4) {
            lub |= 1 << (e + OFF);
          }
        }
      }
      m.vars.add(new Var("s" + i, Kind.SET, 0, 0, lub));
    }
    int ints = 1 + r.nextInt(2);
    for (int i = 1; i <= ints; i++) {
      int lo = r.nextInt(3) - 1;
      m.vars.add(new Var("x" + i, Kind.INT, lo, lo + 1 + r.nextInt(4), 0));
    }
    int bools = 1 + r.nextInt(2);
    for (int i = 1; i <= bools; i++) {
      m.vars.add(new Var("b" + i, Kind.BOOL, 0, 1, 0));
    }
    int calls = 1 + r.nextInt(MAX_CALLS);
    for (int c = 0; c < calls; c++) {
      m.calls.add(randomCall(m, r));
    }
    List<Integer> setIdx = m.ofKind(Kind.SET);
    java.util.Collections.shuffle(setIdx, r);
    m.setOrder = setIdx.stream().mapToInt(Integer::intValue).toArray();
    m.varSelection = VAR_SELECTIONS[r.nextInt(VAR_SELECTIONS.length)];
    m.valueSelection = VALUE_SELECTIONS[r.nextInt(VALUE_SELECTIONS.length)];
    return m;
  }

  private static Call randomCall(Model m, Random r) {
    int kinds = STANDARD_ONLY ? 9 : 17;
    switch (r.nextInt(kinds)) {
      case 0 -> {
        Arg s = m.setVar();
        Arg x = m.intArg();
        return new Call(
            "set_card(" + s.text + ", " + x.text + ")", v -> Integer.bitCount(s.of(v)) == x.of(v));
      }
      case 1 -> {
        Arg x = m.intArg();
        Arg s = m.set(x.aVar >= 0);
        String[] kind = {"", "_reif", "_imp"};
        String k = kind[r.nextInt(3)];
        if (k.isEmpty()) {
          return new Call("set_in(" + x.text + ", " + s.text + ")", v -> member(x.of(v), s.of(v)));
        }
        Arg b = m.boolArg();
        boolean reif = k.equals("_reif");
        return new Call(
            "set_in" + k + "(" + x.text + ", " + s.text + ", " + b.text + ")",
            v ->
                reif
                    ? (b.of(v) == 1) == member(x.of(v), s.of(v))
                    : b.of(v) == 0 || member(x.of(v), s.of(v)));
      }
      case 2, 3 -> {
        String[] rel = {"subset", "superset", "eq", "ne", "le", "lt"};
        String name = rel[r.nextInt(rel.length)];
        Arg[] ab = m.twoSets();
        boolean reified = r.nextInt(3) == 0;
        Arg b = reified ? m.boolArg() : null;
        String text =
            "set_"
                + name
                + (reified ? "_reif" : "")
                + "("
                + ab[0].text
                + ", "
                + ab[1].text
                + (reified ? ", " + b.text : "")
                + ")";
        return new Call(
            text,
            v -> {
              boolean holds = relation(name, ab[0].of(v), ab[1].of(v));
              return reified ? holds == (b.of(v) == 1) : holds;
            });
      }
      case 4, 5 -> {
        String[] op = {"union", "intersect", "diff", "symdiff"};
        String name = op[r.nextInt(op.length)];
        Arg[] ab = m.twoSets();
        Arg c = m.set(ab[0].aVar >= 0 && ab[1].aVar >= 0);
        return new Call(
            "set_" + name + "(" + ab[0].text + ", " + ab[1].text + ", " + c.text + ")",
            v -> operation(name, ab[0].of(v), ab[1].of(v)) == c.of(v));
      }
      case 6 -> {
        int n = 1 + r.nextInt(3);
        int[] consts = new int[n];
        String[] texts = new String[n];
        for (int i = 0; i < n; i++) {
          Arg a = m.set(true);
          while (a.aVar >= 0) {
            a = m.set(true);
          }
          consts[i] = a.value;
          texts[i] = a.text;
        }
        Arg x = m.intArg();
        Arg s = m.setVar();
        return new Call(
            "array_set_element(" + x.text + ", [" + String.join(", ", texts) + "], " + s.text + ")",
            v -> x.of(v) >= 1 && x.of(v) <= n && consts[x.of(v) - 1] == s.of(v));
      }
      case 7 -> {
        int n = 1 + r.nextInt(3);
        Arg[] xs = new Arg[n];
        for (int i = 0; i < n; i++) {
          xs[i] = m.set(true);
        }
        Arg x = m.intArg();
        Arg s = m.setVar();
        return new Call(
            "array_var_set_element(" + x.text + ", " + list(xs) + ", " + s.text + ")",
            v -> x.of(v) >= 1 && x.of(v) <= n && xs[x.of(v) - 1].of(v) == s.of(v));
      }
      case 8 -> {
        // set_card with a constant, the cardinality case of the front end
        Arg s = m.setVar();
        int k = r.nextInt(4);
        return new Call("set_card(" + s.text + ", " + k + ")", v -> Integer.bitCount(s.of(v)) == k);
      }
      case 9 -> {
        Arg[] ab = {m.setVar(), m.setVar()};
        return new Call(
            "jacop_disjoint(" + ab[0].text + ", " + ab[1].text + ")",
            v -> (ab[0].of(v) & ab[1].of(v)) == 0);
      }
      case 10 -> {
        Arg[] xs = setVars(m, r);
        return new Call(
            "jacop_all_disjoint(" + list(xs) + ")",
            v -> {
              int seen = 0;
              for (Arg a : xs) {
                if ((seen & a.of(v)) != 0) {
                  return false;
                }
                seen |= a.of(v);
              }
              return true;
            });
      }
      case 11 -> {
        Arg[] xs = setVars(m, r);
        int u = 0;
        for (Arg a : xs) {
          int lub = m.vars.get(a.aVar).lub;
          u |= lub & (r.nextInt(3) == 0 ? lub >> 1 | lub << 1 : -1);
        }
        int universe = u;
        return new Call(
            "jacop_partition_set(" + list(xs) + ", " + setLiteral(universe, r) + ")",
            v -> {
              int seen = 0;
              for (Arg a : xs) {
                if ((seen & a.of(v)) != 0) {
                  return false;
                }
                seen |= a.of(v);
              }
              return seen == universe;
            });
      }
      case 12 -> {
        int n = 1 + r.nextInt(4);
        int[] values = new int[n];
        int[] weights = new int[n];
        for (int i = 0; i < n; i++) {
          values[i] = r.nextInt(7) - 1;
          weights[i] = r.nextInt(4);
        }
        Arg s = m.setVar();
        Arg x = m.intArg();
        return new Call(
            "jacop_sum_set("
                + Arrays.toString(values)
                + ", "
                + Arrays.toString(weights)
                + ", "
                + s.text
                + ", "
                + x.text
                + ")",
            v -> {
              int sum = 0;
              for (int i = 0; i < n; i++) {
                if (member(values[i], s.of(v))) {
                  sum += weights[i];
                }
              }
              return sum == x.of(v);
            });
      }
      case 13 -> {
        // the index set of b covers the elements the set may hold, as link_set_to_booleans asks
        Arg s = m.setVar();
        int lub = m.vars.get(s.aVar).lub;
        int offset = Integer.numberOfTrailingZeros(lub) - OFF - r.nextInt(2);
        int n = 31 - Integer.numberOfLeadingZeros(lub) - OFF - offset + 1 + r.nextInt(2);
        Arg[] bs = new Arg[n];
        for (int i = 0; i < n; i++) {
          bs[i] = m.boolArg();
        }
        return new Call(
            "jacop_link_set_to_booleans(" + s.text + ", " + list(bs) + ", " + offset + ")",
            v -> {
              for (int i = 0; i < n; i++) {
                if ((bs[i].of(v) == 1) != member(offset + i, s.of(v))) {
                  return false;
                }
              }
              return true;
            });
      }
      case 14 -> {
        int nx = 1 + r.nextInt(2);
        Arg[] xs = new Arg[nx];
        for (int i = 0; i < nx; i++) {
          int k = m.pick(Kind.INT);
          xs[i] = new Arg(k, 0, m.vars.get(k).name);
        }
        Arg[] ys = setVars(m, r);
        int xoff = r.nextInt(3);
        int yoff = r.nextInt(3);
        return new Call(
            "jacop_int_set_channel(" + list(xs) + ", " + list(ys) + ", " + xoff + ", " + yoff + ")",
            v -> {
              for (int i = 0; i < nx; i++) {
                int j = xs[i].of(v);
                if (j < yoff || j >= yoff + ys.length) {
                  return false;
                }
              }
              for (int j = 0; j < ys.length; j++) {
                int y = ys[j].of(v);
                for (int e = -OFF; e < 32 - OFF; e++) {
                  boolean in = member(e, y);
                  int i = e - xoff;
                  if (in && (i < 0 || i >= nx)) {
                    return false;
                  }
                  if (i >= 0 && i < nx && in != (xs[i].of(v) == j + yoff)) {
                    return false;
                  }
                }
              }
              return true;
            });
      }
      case 15 -> {
        int n = 1 + r.nextInt(3);
        Arg[] cs = new Arg[n];
        for (int i = 0; i + 1 < n; i++) {
          cs[i] = m.boolArg();
        }
        cs[n - 1] = new Arg(-1, 1, "true");
        boolean constants = r.nextBoolean();
        Arg[] xs = new Arg[n];
        for (int i = 0; i < n; i++) {
          Arg a = m.set(true);
          while (constants && a.aVar >= 0) {
            a = m.set(true);
          }
          xs[i] = a;
        }
        Arg y = m.setVar();
        return new Call(
            "jacop_if_then_else_set(" + list(cs) + ", " + list(xs) + ", " + y.text + ")",
            v -> {
              for (int i = 0; i < n; i++) {
                if (cs[i].of(v) == 1) {
                  return xs[i].of(v) == y.of(v);
                }
              }
              return true;
            });
      }
      default -> {
        // two relations on the same variable: aliasing in the front end
        Arg s = m.setVar();
        String[] rel = {"subset", "superset", "eq", "ne", "le", "lt"};
        String name = rel[r.nextInt(rel.length)];
        return new Call(
            "set_" + name + "(" + s.text + ", " + s.text + ")",
            v -> relation(name, s.of(v), s.of(v)));
      }
    }
  }

  private static Arg[] setVars(Model m, Random r) {
    int n = 2 + r.nextInt(2);
    Arg[] xs = new Arg[n];
    for (int i = 0; i < n; i++) {
      xs[i] = m.setVar();
    }
    return xs;
  }

  private static String list(Arg[] args) {
    return "[" + String.join(", ", Arrays.stream(args).map(Arg::text).toList()) + "]";
  }

  private static boolean member(int e, int mask) {
    return e + OFF >= 0 && e + OFF < 32 && (mask >> (e + OFF) & 1) == 1;
  }

  private static boolean relation(String name, int a, int b) {
    return switch (name) {
      case "subset" -> (a & ~b) == 0;
      case "superset" -> (b & ~a) == 0;
      case "eq" -> a == b;
      case "ne" -> a != b;
      case "le" -> lexCompare(a, b) <= 0;
      default -> lexCompare(a, b) < 0;
    };
  }

  /** MiniZinc's order of sets: the lexicographic order of their sorted elements. */
  private static int lexCompare(int a, int b) {
    while (a != 0 && b != 0) {
      int ea = Integer.numberOfTrailingZeros(a);
      int eb = Integer.numberOfTrailingZeros(b);
      if (ea != eb) {
        return ea < eb ? -1 : 1;
      }
      a &= a - 1;
      b &= b - 1;
    }
    return Integer.compare(a == 0 ? 0 : 1, b == 0 ? 0 : 1);
  }

  private static int operation(String name, int a, int b) {
    return switch (name) {
      case "union" -> a | b;
      case "intersect" -> a & b;
      case "diff" -> a & ~b;
      default -> a ^ b;
    };
  }

  /** A set constant as {a, b, ...}, or as lo..hi when it is an interval and now and then. */
  private static String setLiteral(int mask, Random r) {
    if (mask == 0) {
      return "{}";
    }
    int lo = Integer.numberOfTrailingZeros(mask);
    int hi = 31 - Integer.numberOfLeadingZeros(mask);
    if (Integer.bitCount(mask) == hi - lo + 1 && r.nextBoolean()) {
      return (lo - OFF) + ".." + (hi - OFF);
    }
    List<String> elements = new ArrayList<>();
    for (int e = lo; e <= hi; e++) {
      if ((mask >> e & 1) == 1) {
        elements.add(Integer.toString(e - OFF));
      }
    }
    return "{" + String.join(", ", elements) + "}";
  }

  // ---------------------------------------------------------------- enumeration and order

  /** All solutions, or null when the model is too large or has too many of them. */
  private static List<int[]> bruteForce(Model m) {
    int n = m.vars.size();
    int[][] values = new int[n][];
    long size = 1;
    for (int i = 0; i < n; i++) {
      values[i] = m.vars.get(i).values();
      size *= values[i].length;
    }
    if (size > MAX_ASSIGNMENTS) {
      return null;
    }
    List<int[]> solutions = new ArrayList<>();
    int[] index = new int[n];
    int[] v = new int[n];
    while (true) {
      for (int i = 0; i < n; i++) {
        v[i] = values[i][index[i]];
      }
      boolean ok = true;
      for (Call c : m.calls) {
        if (!c.holds.test(v)) {
          ok = false;
          break;
        }
      }
      if (ok) {
        solutions.add(v.clone());
        if (solutions.size() > MAX_SOLUTIONS) {
          return null;
        }
      }
      int i = 0;
      while (i < n && ++index[i] == values[i].length) {
        index[i++] = 0;
      }
      if (i == n) {
        return solutions;
      }
    }
  }

  /**
   * The order of solutions of the annotation with input_order: the sets in the annotation's order,
   * each decided element by element; then the integers and Booleans from the smallest value.
   */
  private static Comparator<int[]> annotationOrder(Model m) {
    boolean fromMax = m.valueSelection.endsWith("max");
    boolean inFirst = m.valueSelection.startsWith("indomain");
    return (a, b) -> {
      for (int i : m.setOrder) {
        int diff = a[i] ^ b[i];
        if (diff != 0) {
          int bit =
              fromMax
                  ? 31 - Integer.numberOfLeadingZeros(diff)
                  : Integer.numberOfTrailingZeros(diff);
          boolean aIn = (a[i] >> bit & 1) == 1;
          return aIn == inFirst ? -1 : 1;
        }
      }
      for (int i = 0; i < m.vars.size(); i++) {
        if (m.vars.get(i).kind != Kind.SET && a[i] != b[i]) {
          return Integer.compare(a[i], b[i]);
        }
      }
      return 0;
    };
  }

  private static String compare(Model m, List<int[]> expected, Output out, boolean wholeOrder) {
    if (!out.complete) {
      return "the search did not finish";
    }
    List<String> want = new ArrayList<>();
    for (int[] s : expected) {
      want.add(show(m, s));
    }
    List<String> got = new ArrayList<>();
    for (int[] s : out.solutions) {
      got.add(show(m, s));
    }
    Set<String> gotSet = new LinkedHashSet<>(got);
    if (gotSet.size() != got.size()) {
      return "a solution is reported twice: " + head(got);
    }
    Set<String> wantSet = new LinkedHashSet<>(want);
    if (!gotSet.equals(wantSet)) {
      Set<String> missing = new LinkedHashSet<>(wantSet);
      missing.removeAll(gotSet);
      Set<String> extra = new LinkedHashSet<>(gotSet);
      extra.removeAll(wantSet);
      return "expected "
          + want.size()
          + " solutions, found "
          + got.size()
          + "; missing "
          + head(missing)
          + "; not solutions "
          + head(extra);
    }
    if (wholeOrder && !want.equals(got)) {
      return "solutions in the wrong order; expected " + head(want) + ", found " + head(got);
    }
    return null;
  }

  /** The one solution of a satisfaction run: the first of the annotation's order when ordered. */
  private static String first(Model m, List<int[]> expected, Output out, boolean ordered) {
    if (expected.isEmpty()) {
      return out.solutions.isEmpty() && out.complete ? null : "expected UNSATISFIABLE";
    }
    if (out.solutions.size() != 1) {
      return "expected one solution, found " + out.solutions.size();
    }
    String got = show(m, out.solutions.get(0));
    String want = show(m, expected.get(0));
    if (ordered && !got.equals(want)) {
      return "wrong first solution; expected " + want + ", found " + got;
    }
    for (int[] s : expected) {
      if (show(m, s).equals(got)) {
        return null;
      }
    }
    return "not a solution: " + got;
  }

  /** An optimisation run: its last solution is a solution with the optimum, which it proves. */
  private static String optimum(
      Model m, List<int[]> expected, Output out, int objective, boolean minimize) {
    if (!out.complete) {
      return "the search did not finish";
    }
    if (expected.isEmpty()) {
      return out.solutions.isEmpty() ? null : "expected UNSATISFIABLE";
    }
    if (out.solutions.isEmpty()) {
      return "no solution found";
    }
    int best = expected.get(0)[objective];
    for (int[] s : expected) {
      best = minimize ? Math.min(best, s[objective]) : Math.max(best, s[objective]);
    }
    int[] last = out.solutions.get(out.solutions.size() - 1);
    String got = show(m, last);
    if (expected.stream().noneMatch(s -> show(m, s).equals(got))) {
      return "not a solution: " + got;
    }
    return last[objective] == best ? null : "optimum " + best + " expected, found " + got;
  }

  private static String head(java.util.Collection<String> c) {
    return c.stream().limit(6).toList() + (c.size() > 6 ? " ..." : "");
  }

  private static String show(Model m, int[] s) {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < s.length; i++) {
      Var v = m.vars.get(i);
      sb.append(i == 0 ? "" : " ").append(v.name).append('=');
      if (v.kind == Kind.SET) {
        List<String> elements = new ArrayList<>();
        for (int e = 0; e < 32; e++) {
          if ((s[i] >> e & 1) == 1) {
            elements.add(Integer.toString(e - OFF));
          }
        }
        sb.append('{').append(String.join(",", elements)).append('}');
      } else {
        sb.append(s[i]);
      }
    }
    return sb.toString();
  }

  // ---------------------------------------------------------------- running JaCoP

  /** The solutions a run printed, and whether it finished (========== or UNSATISFIABLE). */
  private record Output(List<int[]> solutions, boolean complete) {}

  private Output solve(Model m, String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      List<String> args = new ArrayList<>(Arrays.asList(options));
      args.add(fzn.toString());
      new Fz2jacop().callMain(args.toArray(new String[0]));
    } finally {
      System.setOut(originalOut);
    }
    String text = buffer.toString(StandardCharsets.UTF_8);
    List<int[]> solutions = new ArrayList<>();
    for (String block : text.split("----------")) {
      int[] s = new int[m.vars.size()];
      int assigned = 0;
      for (String line : block.strip().split("\\R")) {
        int eq = line.indexOf(" = ");
        if (line.startsWith("%") || eq < 0) {
          continue;
        }
        String name = line.substring(0, eq);
        String value = line.substring(eq + 3, line.lastIndexOf(';'));
        for (int i = 0; i < m.vars.size(); i++) {
          if (m.vars.get(i).name.equals(name)) {
            s[i] = parseValue(m.vars.get(i).kind, value);
            assigned++;
          }
        }
      }
      if (assigned == m.vars.size()) {
        solutions.add(s);
      } else if (assigned > 0) {
        throw new IllegalStateException("incomplete solution in the output: " + block);
      }
    }
    boolean complete = text.contains("==========") || text.contains("=====UNSATISFIABLE=====");
    boolean satisfaction = model.contains(" satisfy;");
    boolean all = Arrays.asList(options).contains("-a");
    // a satisfaction run for one solution stops at it without ==========
    return new Output(solutions, complete || satisfaction && !all && solutions.size() == 1);
  }

  private static int parseValue(Kind kind, String value) {
    switch (kind) {
      case BOOL -> {
        return value.equals("true") ? 1 : 0;
      }
      case INT -> {
        return Integer.parseInt(value);
      }
      default -> {
        String body = value.startsWith("{") ? value.substring(1, value.length() - 1) : value;
        int mask = 0;
        for (String item : body.split(",")) {
          item = item.strip();
          if (item.isEmpty()) {
            continue;
          }
          int dots = item.indexOf("..");
          int lo = Integer.parseInt(dots < 0 ? item : item.substring(0, dots));
          int hi = dots < 0 ? lo : Integer.parseInt(item.substring(dots + 2));
          for (int e = lo; e <= hi; e++) {
            mask |= 1 << (e + OFF);
          }
        }
        return mask;
      }
    }
  }
}
