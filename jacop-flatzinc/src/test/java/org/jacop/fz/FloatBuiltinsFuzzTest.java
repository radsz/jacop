/*
 * FloatBuiltinsFuzzTest.java
 * <p>
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

import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.fail;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.Random;
import java.util.Set;
import java.util.StringJoiner;
import java.util.TreeSet;
import java.util.function.ToDoubleFunction;
import java.util.stream.Collectors;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * Random FlatZinc models over the float built-ins, solved for all solutions and compared with
 * enumeration.
 *
 * <p>Each model has two or three small integer variables, each turned into a float by {@code
 * int2float}, and one call of a float built-in on them: a comparison or a linear constraint (plain
 * or reified), or a function such as {@code float_times} or {@code float_sin} whose result is
 * compared with a constant by a reified comparison. The search labels the integers and the Boolean,
 * so the solutions are tuples of integers that Java's arithmetic decides: constants are quarters,
 * exact in binary, and a function's result is never within 1e-6 of the constant it is compared
 * with. Each model is solved with several option sets (plain, presolve, --lcg, which float models
 * ignore, and -f).
 *
 * <p>Models are {@code float.builtins.trials} (lower in the {@code min} profile).
 */
class FloatBuiltinsFuzzTest {

  private static final int TRIALS = Integer.getInteger("float.builtins.trials", 400);

  private static final long SEED = Long.getLong("float.builtins.seed", 20261105L);

  private static final String[][] OPTIONS = {{}, {"--presolve", "on"}, {"--lcg"}, {"-f"}};

  @TempDir Path tmp;

  /** A float function of the integer values, NaN where it is undefined (the call fails). */
  private record Function(String name, int arity, ToDoubleFunction<double[]> f, int lo, int hi) {}

  private static final Function[] FUNCTIONS = {
    new Function("float_plus", 2, x -> x[0] + x[1], -3, 3),
    new Function("float_times", 2, x -> x[0] * x[1], -3, 3),
    new Function("float_div", 2, x -> x[1] == 0 ? Double.NaN : x[0] / x[1], -3, 3),
    new Function("float_min", 2, x -> Math.min(x[0], x[1]), -3, 3),
    new Function("float_max", 2, x -> Math.max(x[0], x[1]), -3, 3),
    new Function("float_pow", 2, x -> Math.pow(x[0], x[1]), 1, 3),
    new Function("float_abs", 1, x -> Math.abs(x[0]), -3, 3),
    new Function("float_sqrt", 1, x -> x[0] < 0 ? Double.NaN : Math.sqrt(x[0]), -1, 6),
    new Function("float_exp", 1, x -> Math.exp(x[0]), -3, 3),
    new Function("float_ln", 1, x -> x[0] <= 0 ? Double.NaN : Math.log(x[0]), -1, 6),
    new Function("float_log10", 1, x -> x[0] <= 0 ? Double.NaN : Math.log10(x[0]), -1, 6),
    new Function(
        "float_log2", 1, x -> x[0] <= 0 ? Double.NaN : Math.log(x[0]) / Math.log(2), -1, 6),
    new Function("float_sin", 1, x -> Math.sin(x[0]), -4, 4),
    new Function("float_cos", 1, x -> Math.cos(x[0]), -4, 4),
    new Function("float_tan", 1, x -> Math.tan(x[0]), -4, 4),
    new Function("float_asin", 1, x -> Math.abs(x[0]) > 1 ? Double.NaN : Math.asin(x[0]), -2, 2),
    new Function("float_acos", 1, x -> Math.abs(x[0]) > 1 ? Double.NaN : Math.acos(x[0]), -2, 2),
    new Function("float_atan", 1, x -> Math.atan(x[0]), -4, 4),
  };

  private record Model(String fzn, Set<String> expected) {}

  @Test
  void floatBuiltinsAgreeWithEnumeration() {
    assertTimeoutPreemptively(
        Duration.ofMinutes(10),
        () -> {
          Random random = new Random(SEED);
          List<String> failures = new ArrayList<>();
          for (int t = 0; t < TRIALS && failures.size() < 5; t++) {
            Model m = randomModel(random);
            String[] opts = OPTIONS[t % OPTIONS.length];
            Set<String> found = new TreeSet<>(solveAll(m.fzn(), opts));
            found.remove("=====UNSATISFIABLE=====");
            if (!found.equals(m.expected())) {
              Set<String> missing = new TreeSet<>(m.expected());
              missing.removeAll(found);
              Set<String> extra = new TreeSet<>(found);
              extra.removeAll(m.expected());
              failures.add(
                  "options "
                      + Arrays.toString(opts)
                      + "\n"
                      + m.fzn()
                      + "missing "
                      + missing
                      + "\nwrong "
                      + extra);
            }
          }
          if (!failures.isEmpty()) {
            fail(String.join("\n\n", failures));
          }
        });
  }

  /**
   * Minimises or maximises a float function of the integers (a built-in, or a linear sum defined by
   * float_lin_eq), and checks the last solution against the optimum found by enumeration.
   */
  @Test
  void floatObjectivesReachTheOptimum() {
    assertTimeoutPreemptively(
        Duration.ofMinutes(10),
        () -> {
          Random random = new Random(SEED + 1);
          List<String> failures = new ArrayList<>();
          for (int t = 0; t < TRIALS / 4 && failures.size() < 5; t++) {
            String failure = optimise(random, OPTIONS[t % OPTIONS.length]);
            if (failure != null) {
              failures.add(failure);
            }
          }
          if (!failures.isEmpty()) {
            fail(String.join("\n\n", failures));
          }
        });
  }

  private String optimise(Random random, String[] opts) throws IOException {
    boolean linear = random.nextInt(3) == 0;
    Function fn = FUNCTIONS[random.nextInt(FUNCTIONS.length)];
    int n = linear ? 1 + random.nextInt(3) : fn.arity();
    int[] lo = new int[n];
    int[] hi = new int[n];
    int[] var = new int[n];
    double[] w = new double[n];
    StringBuilder fzn = new StringBuilder();
    StringBuilder constraints = new StringBuilder();
    StringJoiner search = new StringJoiner(",");
    StringJoiner args = new StringJoiner(",");
    for (int i = 0; i < n; i++) {
      int a = linear ? -3 : fn.lo();
      int b = linear ? 3 : fn.hi();
      lo[i] = a + random.nextInt(b - a + 1);
      hi[i] = Math.min(b, lo[i] + random.nextInt(4));
      var[i] = i > 0 && random.nextInt(5) == 0 ? var[random.nextInt(i)] : i;
      if (var[i] == i) {
        fzn.append("var ").append(lo[i]).append("..").append(hi[i]).append(": x").append(i);
        fzn.append(":: output_var;\n");
        fzn.append("var float: f").append(i).append(";\n");
        constraints.append("constraint int2float(x").append(i).append(",f").append(i);
        constraints.append(");\n");
        search.add("x" + i);
      }
      args.add("f" + var[i]);
      w[i] = quarter(random);
      w[i] = w[i] == 0 ? 1.5 : w[i];
    }
    fzn.append("var float: r:: output_var;\n");
    if (linear) {
      StringJoiner ws = new StringJoiner(",");
      for (double x : w) {
        ws.add(q(x));
      }
      constraints.append("constraint float_lin_eq([").append(ws).append(",-1.0],[").append(args);
      constraints.append(",r],0.0):: defines_var(r);\n");
    } else {
      constraints.append("constraint ").append(fn.name()).append("(").append(args);
      constraints.append(",r):: defines_var(r);\n");
    }
    boolean minimise = random.nextBoolean();
    fzn.append(constraints);
    fzn.append("solve :: int_search([")
        .append(search)
        .append("], input_order, indomain_min, complete) ")
        .append(minimise ? "minimize r;\n" : "maximize r;\n");

    double best = minimise ? Double.POSITIVE_INFINITY : Double.NEGATIVE_INFINITY;
    double[] value = {best};
    int[] v = new int[n];
    enumerate(
        0,
        v,
        lo,
        hi,
        var,
        () -> {
          double[] x = new double[n];
          for (int i = 0; i < n; i++) {
            x[i] = v[var[i]];
          }
          double r;
          if (linear) {
            r = 0;
            for (int i = 0; i < n; i++) {
              r += w[i] * x[i];
            }
          } else {
            r = fn.f().applyAsDouble(x);
          }
          if (!Double.isNaN(r)) {
            value[0] = minimise ? Math.min(value[0], r) : Math.max(value[0], r);
          }
        });
    String out = run(fzn.toString(), opts);
    String where = "options " + Arrays.toString(opts) + "\n" + fzn;
    if (Double.isInfinite(value[0])) {
      return out.contains("=====UNSATISFIABLE=====")
          ? null
          : where + "expected UNSATISFIABLE\n" + out;
    }
    if (!out.contains("==========")) {
      return where + "no proof of optimality\n" + out;
    }
    double last = Double.NaN;
    for (String line : out.split("\\R")) {
      if (line.startsWith("r = ")) {
        last = Double.parseDouble(line.substring(4, line.length() - 1));
      }
    }
    if (!(Math.abs(last - value[0]) <= 1e-6 * (1 + Math.abs(value[0])))) {
      return where + "optimum " + value[0] + ", last solution r = " + last + "\n" + out;
    }
    return null;
  }

  private String run(String model, String... options) throws IOException {
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
    return buffer.toString(StandardCharsets.UTF_8);
  }

  private static String q(double v) {
    return String.format(Locale.ROOT, "%.2f", v);
  }

  /** A quarter in [-4, 4]. */
  private static double quarter(Random random) {
    return (random.nextInt(33) - 16) / 4.0;
  }

  private static Model randomModel(Random random) {
    int kind = random.nextInt(4);
    Function fn = FUNCTIONS[random.nextInt(FUNCTIONS.length)];
    int n = kind == 2 ? 1 + random.nextInt(3) : kind == 3 ? fn.arity() : 2;
    int[] lo = new int[n];
    int[] hi = new int[n];
    for (int i = 0; i < n; i++) {
      int a = kind == 3 ? fn.lo() : -3;
      int b = kind == 3 ? fn.hi() : 3;
      lo[i] = a + random.nextInt(b - a + 1);
      hi[i] = Math.min(b, lo[i] + random.nextInt(4));
    }
    // a variable used twice now and then
    int[] var = new int[n];
    for (int i = 0; i < n; i++) {
      var[i] = i > 0 && random.nextInt(5) == 0 ? var[random.nextInt(i)] : i;
    }
    StringBuilder fzn = new StringBuilder();
    StringJoiner search = new StringJoiner(",");
    for (int i = 0; i < n; i++) {
      if (var[i] == i) {
        fzn.append("var ").append(lo[i]).append("..").append(hi[i]).append(": x").append(i);
        fzn.append(":: output_var;\n");
        // a float with bounds or without
        fzn.append(random.nextBoolean() ? "var float: f" : "var -10.0..10.0: f").append(i);
        fzn.append(";\n");
        search.add("x" + i);
      }
    }
    boolean reified = kind == 3 || random.nextBoolean();
    if (reified) {
      fzn.append("var bool: b:: output_var;\n");
    }
    StringBuilder constraints = new StringBuilder();
    for (int i = 0; i < n; i++) {
      if (var[i] == i) {
        constraints.append("constraint int2float(x").append(i).append(",f").append(i);
        constraints.append(");\n");
      }
    }
    String[] ops = {"eq", "ne", "le", "lt"};
    String op = ops[random.nextInt(ops.length)];
    double c = quarter(random);
    double[] w = new double[n];
    // the relation over the values of the integers, as a Java predicate
    Relation relation;
    switch (kind) {
      case 0, 1 -> {
        // float_eq/ne/le/lt(f0, f1) or with a constant
        boolean constant = kind == 1;
        String a = "f" + var[0];
        String b = constant ? q(c) : "f" + var[1];
        if (constant && random.nextBoolean()) {
          String s = a;
          a = b;
          b = s;
        }
        boolean constFirst = constant && a.equals(q(c));
        constraints
            .append("constraint float_")
            .append(op)
            .append(reified ? "_reif(" : "(")
            .append(a)
            .append(",")
            .append(b)
            .append(reified ? ",b" : "")
            .append(");\n");
        relation =
            x -> {
              double l = constFirst ? c : x[0];
              double r = constant ? (constFirst ? x[0] : c) : x[1];
              return compare(op, l, r);
            };
      }
      case 2 -> {
        // float_lin_*: quarter weights, a repeated variable at times
        StringJoiner ws = new StringJoiner(",");
        StringJoiner vs = new StringJoiner(",");
        for (int i = 0; i < n; i++) {
          w[i] = quarter(random);
          w[i] = w[i] == 0 ? 0.5 : w[i];
          ws.add(q(w[i]));
          vs.add("f" + var[i]);
        }
        constraints
            .append("constraint float_lin_")
            .append(op)
            .append(reified ? "_reif([" : "([")
            .append(ws)
            .append("],[")
            .append(vs)
            .append("],")
            .append(q(c))
            .append(reified ? ",b" : "")
            .append(");\n");
        relation =
            x -> {
              double s = 0;
              for (int i = 0; i < n; i++) {
                s += w[i] * x[i];
              }
              return compare(op, s, c);
            };
      }
      default -> {
        // r = fn(f...), then b <-> r op c, op one of le, lt; c away from every value of r
        String rel = random.nextBoolean() ? "le" : "lt";
        double[] values = values(fn, n, lo, hi, var);
        double cc = c;
        for (int tries = 0; tries < 50 && tooClose(values, cc); tries++) {
          cc = quarter(random) + random.nextInt(8) / 8.0 - 0.5;
        }
        if (tooClose(values, cc)) {
          cc = 100.5;
        }
        double fc = cc;
        fzn.append("var float: r;\n");
        StringJoiner args = new StringJoiner(",");
        for (int i = 0; i < n; i++) {
          args.add("f" + var[i]);
        }
        constraints.append("constraint ").append(fn.name()).append("(").append(args);
        constraints.append(",r);\n");
        boolean resultFirst = random.nextBoolean();
        constraints
            .append("constraint float_")
            .append(rel)
            .append("_reif(")
            .append(resultFirst ? "r," + q(fc) : q(fc) + ",r")
            .append(",b);\n");
        relation =
            x -> {
              double r = fn.f().applyAsDouble(x);
              if (Double.isNaN(r)) {
                return null;
              }
              return resultFirst ? compare(rel, r, fc) : compare(rel, fc, r);
            };
      }
    }
    fzn.append(constraints);
    if (reified) {
      search.add("b");
    }
    String searchVars = search.toString();
    String ints = searchVars.replace(",b", "");
    fzn.append("solve :: seq_search([int_search([")
        .append(ints)
        .append("], input_order, indomain_min, complete)")
        .append(reified ? ", bool_search([b], input_order, indomain_min, complete)" : "")
        .append("]) satisfy;\n");

    Set<String> expected = new TreeSet<>();
    int[] v = new int[n];
    enumerate(
        0,
        v,
        lo,
        hi,
        var,
        () -> {
          double[] x = new double[n];
          for (int i = 0; i < n; i++) {
            x[i] = v[var[i]];
          }
          Boolean holds = relation.holds(x);
          if (holds == null) {
            return;
          }
          StringJoiner sol = new StringJoiner(" ");
          for (int i = 0; i < n; i++) {
            if (var[i] == i) {
              sol.add("x" + i + " = " + v[i] + ";");
            }
          }
          if (!reified) {
            if (holds) {
              expected.add(sol.toString());
            }
          } else {
            expected.add("b = " + holds + "; " + sol);
          }
        });
    return new Model(fzn.toString(), expected);
  }

  private interface Relation {
    /** Whether the relation holds, or null where a function is undefined. */
    Boolean holds(double[] x);
  }

  private static boolean compare(String op, double a, double b) {
    return switch (op) {
      case "eq" -> a == b;
      case "ne" -> a != b;
      case "le" -> a <= b;
      default -> a < b;
    };
  }

  private static double[] values(Function fn, int n, int[] lo, int[] hi, int[] var) {
    List<Double> values = new ArrayList<>();
    int[] v = new int[n];
    enumerate(
        0,
        v,
        lo,
        hi,
        var,
        () -> {
          double[] x = new double[n];
          for (int i = 0; i < n; i++) {
            x[i] = v[var[i]];
          }
          values.add(fn.f().applyAsDouble(x));
        });
    return values.stream().mapToDouble(Double::doubleValue).toArray();
  }

  private static boolean tooClose(double[] values, double c) {
    for (double v : values) {
      if (Math.abs(v - c) < 1e-6 * (1 + Math.abs(c))) {
        return true;
      }
    }
    return false;
  }

  private static void enumerate(int i, int[] v, int[] lo, int[] hi, int[] var, Runnable check) {
    if (i == v.length) {
      check.run();
      return;
    }
    if (var[i] != i) {
      enumerate(i + 1, v, lo, hi, var, check);
      return;
    }
    for (v[i] = lo[i]; v[i] <= hi[i]; v[i]++) {
      enumerate(i + 1, v, lo, hi, var, check);
    }
  }

  private List<String> solveAll(String model, String... options) throws IOException {
    Path fzn = tmp.resolve("model.fzn");
    Files.writeString(fzn, model, StandardCharsets.UTF_8);
    ByteArrayOutputStream buffer = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    try (PrintStream capture = new PrintStream(buffer, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      List<String> args = new ArrayList<>(List.of("-a"));
      args.addAll(Arrays.asList(options));
      args.add(fzn.toString());
      new Fz2jacop().callMain(args.toArray(new String[0]));
    } finally {
      System.setOut(originalOut);
    }
    return Arrays.stream(buffer.toString(StandardCharsets.UTF_8).split("----------"))
        .map(
            s ->
                String.join(
                    " ",
                    Arrays.stream(s.strip().split("\\R"))
                        .filter(line -> !line.startsWith("%"))
                        .collect(Collectors.toCollection(TreeSet::new))))
        .filter(s -> !s.isEmpty() && !s.startsWith("=========="))
        .collect(Collectors.toList());
  }
}
