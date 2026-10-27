/*
 * FloatImposeGroundingHarness.java
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

package org.jacop.floats;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.Implies;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.Xor;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.core.FloatIntervalDomain;
import org.jacop.floats.core.FloatVar;

/**
 * Checks that a float constraint can be imposed when some or all of its variables are already
 * ground, and that it still accepts exactly the right points of a grid.
 *
 * <p>This is the float counterpart of {@code ImposeGroundingHarness} in jacop-core. Each variable
 * is a {@link FloatVar} or an {@link IntVar} with a small grid of exactly representable values (for
 * example multiples of 0.25), so the intended relation can be decided exactly on the grid. A float
 * variable has either the continuous interval spanned by its grid or the union of its grid points
 * as its domain. The harness finds all grid solutions by brute force and then, for many grounding
 * plans, builds a fresh store, grounds a subset of the variables to grid values at a chosen {@link
 * When moment}, imposes the constraint and enumerates the grid in the store, one variable per level
 * with a consistency at every level. The grid points that survive must be exactly the brute-force
 * solutions that agree with the grounded values, and nothing but {@link FailException} may be
 * thrown.
 *
 * <p>Subsets, values and moments are the same as in the int harness. A {@link PrimitiveConstraint}
 * is also checked under {@link Reified}, {@link Not}, {@link Xor}, {@link Implies} and {@link
 * IfThen} with an extra 0/1 variable, and {@code satisfied()} (and {@code notSatisfied()} of a
 * primitive constraint) must give the relation once all variables are ground.
 */
public final class FloatImposeGroundingHarness {

  /** How many failures are reported for a case before the harness stops looking for more. */
  private static final int MAX_REPORTED = 8;

  /** Value used in a grounding plan for a variable that is not grounded. */
  private static final double FREE = Double.NaN;

  private FloatImposeGroundingHarness() {}

  /** When the grounded variables get their values. */
  public enum When {
    /** The variable is created with a singleton domain. */
    SINGLETON_DOMAIN,
    /** The variable is created with its full domain and grounded with {@code in} before impose. */
    BEFORE_IMPOSE,
    /** Grounded with {@code in} after impose, before the first store consistency. */
    AFTER_IMPOSE,
    /**
     * Grounded at store level + 1 after the root consistency; the level is then removed and all
     * solutions of the ungrounded constraint must still be found (checks the trail).
     */
    AT_SEARCH_LEVEL,
    /** Even-indexed grounded variables as singleton domains, the others after impose. */
    MIXED
  }

  /**
   * One variable of a case.
   *
   * @param grid the values checked, ascending and exactly representable
   * @param isFloat a {@link FloatVar} if true, an {@link IntVar} (integral grid) if false
   * @param continuous for a float variable, the domain is the interval min..max of the grid if true
   *     and the union of the grid points if false; an int variable has the grid as domain
   */
  public record Spec(double[] grid, boolean isFloat, boolean continuous) {

    /** A float variable with the interval spanned by the grid as its domain. */
    public static Spec interval(double... grid) {
      return new Spec(grid, true, true);
    }

    /** A float variable whose domain is the union of the grid points. */
    public static Spec points(double... grid) {
      return new Spec(grid, true, false);
    }

    /** An int variable with the given values as its domain. */
    public static Spec integer(int... values) {
      return new Spec(Arrays.stream(values).asDoubleStream().toArray(), false, false);
    }

    @Override
    public String toString() {
      return (isFloat ? (continuous ? "float" : "floatPoints") : "int") + Arrays.toString(grid);
    }
  }

  /**
   * One random instance of a constraint.
   *
   * @param vars the variables
   * @param build builds the constraint on the variables of a store
   * @param semantics the intended relation on grid points, in variable order
   * @param description printed with failures to reproduce the instance
   */
  public record Case(
      Spec[] vars,
      Function<Var[], Constraint> build,
      Predicate<double[]> semantics,
      String description) {}

  /**
   * Runs all grounding plans on {@code trials} random instances of a constraint and throws an
   * {@link AssertionError} listing the first failures.
   *
   * @param name the constraint name used in messages and as the random seed
   * @param generator makes a random instance
   * @param trials how many random instances to check
   */
  public static void check(String name, Function<Random, Case> generator, int trials) {
    List<String> failures = check(name, generator, trials, new Random(name.hashCode()));
    if (!failures.isEmpty()) {
      throw new AssertionError(
          name + ": " + failures.size() + " failing plan(s)\n" + String.join("\n", failures));
    }
  }

  /** Like {@link #check(String, Function, int)} but returns the failures instead of throwing. */
  public static List<String> check(
      String name, Function<Random, Case> generator, int trials, Random random) {
    List<String> failures = new ArrayList<>();
    for (int trial = 0; trial < trials && failures.size() < MAX_REPORTED; trial++) {
      Case c = generator.apply(random);
      checkCase(name + " trial " + trial, c, random, failures);
      checkSatisfied(name + " trial " + trial, c, random, failures);
      checkWrapped(name + " trial " + trial, c, random, failures);
      Case aliased = alias(c, random);
      if (aliased != null) {
        String label = name + " trial " + trial + " aliased";
        checkCase(label, aliased, random, failures);
        checkSatisfied(label, aliased, random, failures);
        checkWrapped(label, aliased, random, failures);
      }
    }
    return failures;
  }

  private static void checkWrapped(String label, Case c, Random random, List<String> failures) {
    if (isPrimitive(c)) {
      for (String wrapper : List.of("Reified", "Not", "Xor", "Implies", "IfThen")) {
        checkCase(label + " " + wrapper, wrap(c, wrapper), random, failures);
      }
    }
  }

  /**
   * The case with two variables of the same kind merged into one, or null when there are no two
   * such variables or their grids share no point. The aliased case has one variable fewer: position
   * {@code j} of the original reads the variable of position {@code i}, whose grid is the points
   * both grids share (an interval only if both were intervals).
   */
  static Case alias(Case c, Random random) {
    int n = c.vars().length;
    if (n < 2) {
      return null;
    }
    int i = random.nextInt(n);
    int k = random.nextInt(n - 1);
    int j = k >= i ? k + 1 : k;
    Spec a = c.vars()[i];
    Spec b = c.vars()[j];
    double[] shared =
        Arrays.stream(a.grid())
            .filter(v -> Arrays.stream(b.grid()).anyMatch(w -> w == v))
            .toArray();
    if (a.isFloat() != b.isFloat() || shared.length == 0) {
      return null;
    }
    int[] map = new int[n];
    Spec[] vars = new Spec[n - 1];
    for (int p = 0, q = 0; p < n; p++) {
      if (p == j) {
        continue;
      }
      map[p] = q;
      vars[q++] =
          p == i ? new Spec(shared, a.isFloat(), a.continuous() && b.continuous()) : c.vars()[p];
    }
    map[j] = map[i];
    Case aliased =
        new Case(
            vars,
            x -> c.build().apply(Arrays.stream(map).mapToObj(p -> x[p]).toArray(Var[]::new)),
            t -> c.semantics().test(Arrays.stream(map).mapToDouble(p -> t[p]).toArray()),
            c.description() + " (x" + j + " is x" + i + " of the original)");
    try {
      Store store = new Store();
      aliased.build().apply(create(store, vars, new double[n - 1], When.BEFORE_IMPOSE));
    } catch (IllegalArgumentException e) {
      // the constraint rejects a variable in two roles
      return null;
    }
    return aliased;
  }

  private static boolean isPrimitive(Case c) {
    Store store = new Store();
    return c.build().apply(create(store, c.vars(), new double[c.vars().length], When.BEFORE_IMPOSE))
        instanceof PrimitiveConstraint;
  }

  /** The case under a wrapper; the extra 0/1 variable (if any) is the last one. */
  private static Case wrap(Case c, String wrapper) {
    Function<Var[], Constraint> build = c.build();
    Predicate<double[]> semantics = c.semantics();
    int n = c.vars().length;
    if (wrapper.equals("Not")) {
      return new Case(
          c.vars(),
          x -> new Not((PrimitiveConstraint) build.apply(x)),
          t -> !semantics.test(t),
          c.description());
    }
    Spec[] vars = Arrays.copyOf(c.vars(), n + 1);
    vars[n] = Spec.integer(0, 1);
    Function<Var[], Constraint> wrapped =
        x -> {
          PrimitiveConstraint p = (PrimitiveConstraint) build.apply(Arrays.copyOf(x, n));
          IntVar b = (IntVar) x[n];
          return switch (wrapper) {
            case "Reified" -> new Reified(p, b);
            case "Xor" -> new Xor(p, b);
            case "Implies" -> new Implies(b, p);
            default -> new IfThen(new XeqC(b, 1), p);
          };
        };
    Predicate<double[]> relation =
        t -> {
          boolean holds = semantics.test(Arrays.copyOf(t, n));
          boolean b = t[n] == 1;
          return switch (wrapper) {
            case "Reified" -> b == holds;
            case "Xor" -> b != holds;
            default -> !b || holds;
          };
        };
    return new Case(vars, wrapped, relation, c.description() + " (b is the last variable)");
  }

  private static void checkCase(String label, Case c, Random random, List<String> failures) {
    int n = c.vars().length;
    Set<List<Double>> solutions = new HashSet<>();
    bruteForce(c, new double[n], 0, solutions);
    List<List<Double>> solutionList = new ArrayList<>(solutions);
    solutionList.sort(FloatImposeGroundingHarness::compare);

    List<double[]> plans = plans(c, solutionList, random);
    When[] moments = When.values();
    for (int p = 0; p < plans.size() && failures.size() < MAX_REPORTED; p++) {
      double[] plan = plans.get(p);
      // the empty and the full plan run at every moment, the others at one moment each
      boolean extreme =
          Arrays.stream(plan).allMatch(Double::isNaN)
              || Arrays.stream(plan).noneMatch(Double::isNaN);
      List<When> whens = extreme ? List.of(moments) : List.of(moments[p % moments.length]);
      for (When when : whens) {
        String error = run(c, plan, when, solutions);
        if (error != null) {
          failures.add(
              label
                  + " "
                  + when
                  + " grounded="
                  + planToString(plan)
                  + " vars="
                  + Arrays.toString(c.vars())
                  + " "
                  + c.description()
                  + ": "
                  + error);
          return;
        }
      }
    }
  }

  /** The grounding plans for one instance: FREE or the value of each variable. */
  private static List<double[]> plans(Case c, List<List<Double>> solutions, Random random) {
    int n = c.vars().length;
    List<boolean[]> subsets = new ArrayList<>();
    subsets.add(new boolean[n]);
    boolean[] all = new boolean[n];
    Arrays.fill(all, true);
    subsets.add(all);
    for (int i = 0; i < n; i++) {
      boolean[] one = new boolean[n];
      one[i] = true;
      subsets.add(one);
      if (n > 2) {
        boolean[] allButOne = all.clone();
        allButOne[i] = false;
        subsets.add(allButOne);
      }
    }
    if (n > 2) {
      boolean[] ends = new boolean[n];
      ends[0] = true;
      ends[n - 1] = true;
      subsets.add(ends);
    }
    for (int k = 0; k < 2; k++) {
      boolean[] some = new boolean[n];
      for (int i = 0; i < n; i++) {
        some[i] = random.nextBoolean();
      }
      subsets.add(some);
    }

    List<double[]> plans = new ArrayList<>();
    for (int s = 0; s < subsets.size(); s++) {
      boolean[] subset = subsets.get(s);
      // the full subset gets every kind of value, the others one kind each, in turn
      int kinds = s == 1 ? 5 : 1;
      for (int k = 0; k < kinds; k++) {
        int kind = s == 1 ? k : s % 5;
        double[] values = values(c, solutions, random, kind);
        double[] plan = new double[n];
        for (int i = 0; i < n; i++) {
          plan[i] = subset[i] ? values[i] : FREE;
        }
        plans.add(plan);
      }
    }
    return plans;
  }

  /**
   * Values for all variables: 0 from a solution, 1 from a non-solution, 2 the grid minimum, 3 the
   * grid maximum, 4 random grid values.
   */
  private static double[] values(Case c, List<List<Double>> solutions, Random random, int kind) {
    Spec[] vars = c.vars();
    int n = vars.length;
    double[] values = new double[n];
    switch (kind) {
      case 0 -> {
        if (!solutions.isEmpty()) {
          List<Double> s = solutions.get(random.nextInt(solutions.size()));
          for (int i = 0; i < n; i++) {
            values[i] = s.get(i);
          }
          return values;
        }
        return randomValues(vars, random);
      }
      case 1 -> {
        for (int attempt = 0; attempt < 20; attempt++) {
          values = randomValues(vars, random);
          if (!c.semantics().test(values)) {
            return values;
          }
        }
        return values;
      }
      case 2 -> {
        for (int i = 0; i < n; i++) {
          values[i] = vars[i].grid()[0];
        }
        return values;
      }
      case 3 -> {
        for (int i = 0; i < n; i++) {
          values[i] = vars[i].grid()[vars[i].grid().length - 1];
        }
        return values;
      }
      default -> {
        return randomValues(vars, random);
      }
    }
  }

  private static double[] randomValues(Spec[] vars, Random random) {
    double[] values = new double[vars.length];
    for (int i = 0; i < vars.length; i++) {
      values[i] = vars[i].grid()[random.nextInt(vars[i].grid().length)];
    }
    return values;
  }

  /** Runs one plan; returns null if it behaves, or a description of what went wrong. */
  private static String run(Case c, double[] plan, When when, Set<List<Double>> solutions) {
    Set<List<Double>> expected = new HashSet<>();
    for (List<Double> s : solutions) {
      if (agrees(s, plan)) {
        expected.add(s);
      }
    }
    Store store = new Store();
    String phase = "creating variables";
    try {
      Var[] x = create(store, c.vars(), plan, when);
      if (when == When.BEFORE_IMPOSE) {
        phase = "grounding before impose";
        ground(store, x, plan, i -> true);
      }
      phase = "impose";
      store.impose(c.build().apply(x));
      if (when == When.AFTER_IMPOSE || when == When.MIXED) {
        phase = "grounding after impose";
        ground(store, x, plan, i -> when == When.AFTER_IMPOSE || i % 2 == 1);
      }

      if (when == When.AT_SEARCH_LEVEL) {
        phase = "root consistency";
        if (!store.consistency()) {
          return solutions.isEmpty()
              ? null
              : "root consistency failed but "
                  + solutions.size()
                  + " solution(s) exist, e.g. "
                  + first(solutions);
        }
        int root = store.level;
        store.setLevel(root + 1);
        phase = "grounding at search level";
        Set<List<Double>> found = new HashSet<>();
        try {
          ground(store, x, plan, i -> true);
          phase = "search at level " + (root + 1);
          found = solveAll(store, c.vars(), x);
        } catch (FailException e) {
          // the grounding itself is inconsistent; no solutions
        }
        String diff = compare(found, expected);
        if (diff != null) {
          return "after grounding at level " + (root + 1) + ": " + diff;
        }
        phase = "backtracking to the root";
        store.removeLevel(root + 1);
        store.setLevel(root);
        phase = "search after backtracking";
        diff = compare(solveAll(store, c.vars(), x), solutions);
        return diff == null ? null : "after removing the grounding level: " + diff;
      }

      phase = "search";
      return compare(solveAll(store, c.vars(), x), expected);
    } catch (FailException e) {
      return expected.isEmpty()
          ? null
          : "FailException during "
              + phase
              + " but "
              + expected.size()
              + " solution(s) exist, e.g. "
              + first(expected);
    } catch (Throwable e) {
      return describe(e, phase);
    }
  }

  /**
   * Checks {@code satisfied()} (and {@code notSatisfied()} of a primitive constraint) with all
   * variables ground; they must give the relation exactly.
   */
  private static void checkSatisfied(String label, Case c, Random random, List<String> failures) {
    double[] values = randomValues(c.vars(), random);
    boolean holds = c.semantics().test(values);
    Store store = new Store();
    String where = label + " satisfied() values=" + Arrays.toString(values) + " " + c.description();
    try {
      Var[] x = create(store, c.vars(), values, When.SINGLETON_DOMAIN);
      Constraint constraint = c.build().apply(x);
      store.impose(constraint);
      if (constraint instanceof PrimitiveConstraint p) {
        if (p.satisfied() != holds) {
          failures.add(
              where + ": satisfied() is " + p.satisfied() + " but the relation is " + holds);
        } else if (p.notSatisfied() == holds) {
          failures.add(
              where + ": notSatisfied() is " + p.notSatisfied() + " but the relation is " + holds);
        }
      } else if (constraint instanceof SatisfiedPresent s && s.satisfied() != holds) {
        failures.add(where + ": satisfied() is " + s.satisfied() + " but the relation is " + holds);
      }
    } catch (FailException e) {
      if (holds) {
        failures.add(where + ": FailException on impose although the relation holds");
      }
    } catch (Throwable e) {
      failures.add(where + ": " + describe(e, "satisfied()"));
    }
  }

  private static Var[] create(Store store, Spec[] vars, double[] plan, When when) {
    Var[] x = new Var[vars.length];
    for (int i = 0; i < vars.length; i++) {
      Spec s = vars[i];
      boolean singleton =
          !Double.isNaN(plan[i])
              && (when == When.SINGLETON_DOMAIN || when == When.MIXED && i % 2 == 0);
      String name = "x" + i;
      if (s.isFloat()) {
        if (singleton) {
          x[i] = new FloatVar(store, name, plan[i], plan[i]);
        } else if (s.continuous()) {
          x[i] = new FloatVar(store, name, s.grid()[0], s.grid()[s.grid().length - 1]);
        } else {
          FloatIntervalDomain domain = new FloatIntervalDomain();
          for (double v : s.grid()) {
            domain.unionAdapt(v, v);
          }
          x[i] = new FloatVar(store, name, domain);
        }
      } else {
        if (singleton) {
          x[i] = new IntVar(store, name, (int) plan[i], (int) plan[i]);
        } else {
          IntervalDomain domain = new IntervalDomain();
          for (double v : s.grid()) {
            domain.unionAdapt((int) v, (int) v);
          }
          x[i] = new IntVar(store, name, domain);
        }
      }
    }
    return x;
  }

  private static void ground(Var x, int level, double value) {
    if (x instanceof FloatVar f) {
      f.domain.in(level, f, value, value);
    } else {
      IntVar v = (IntVar) x;
      v.domain.in(level, v, (int) value, (int) value);
    }
  }

  private static void ground(Store store, Var[] x, double[] plan, Predicate<Integer> which) {
    for (int i = 0; i < x.length; i++) {
      if (!Double.isNaN(plan[i]) && which.test(i)) {
        ground(x[i], store.level, plan[i]);
      }
    }
  }

  private static String describe(Throwable e, String phase) {
    StackTraceElement[] trace = e.getStackTrace();
    StringBuilder where = new StringBuilder();
    for (int i = 0; i < Math.min(4, trace.length); i++) {
      where.append("\n      at ").append(trace[i]);
    }
    return e.getClass().getSimpleName() + " during " + phase + ": " + e.getMessage() + where;
  }

  private static boolean agrees(List<Double> solution, double[] plan) {
    for (int i = 0; i < plan.length; i++) {
      if (!Double.isNaN(plan[i]) && solution.get(i) != plan[i]) {
        return false;
      }
    }
    return true;
  }

  private static String compare(Set<List<Double>> found, Set<List<Double>> expected) {
    if (found.equals(expected)) {
      return null;
    }
    Set<List<Double>> missing = new HashSet<>(expected);
    missing.removeAll(found);
    Set<List<Double>> wrong = new HashSet<>(found);
    wrong.removeAll(expected);
    return "expected "
        + expected.size()
        + " solution(s), found "
        + found.size()
        + (missing.isEmpty() ? "" : ", missing e.g. " + first(missing))
        + (wrong.isEmpty() ? "" : ", wrong e.g. " + first(wrong));
  }

  private static List<Double> first(Set<List<Double>> solutions) {
    return solutions.stream().min(FloatImposeGroundingHarness::compare).orElseThrow();
  }

  private static int compare(List<Double> a, List<Double> b) {
    for (int i = 0; i < Math.min(a.size(), b.size()); i++) {
      int c = Double.compare(a.get(i), b.get(i));
      if (c != 0) {
        return c;
      }
    }
    return Integer.compare(a.size(), b.size());
  }

  private static String planToString(double[] plan) {
    StringBuilder s = new StringBuilder("[");
    for (int i = 0; i < plan.length; i++) {
      s.append(i == 0 ? "" : ", ").append(Double.isNaN(plan[i]) ? "_" : String.valueOf(plan[i]));
    }
    return s.append(']').toString();
  }

  private static void bruteForce(Case c, double[] values, int index, Set<List<Double>> solutions) {
    if (index == values.length) {
      if (c.semantics().test(values)) {
        solutions.add(Arrays.stream(values).boxed().toList());
      }
      return;
    }
    for (double v : c.vars()[index].grid()) {
      values[index] = v;
      bruteForce(c, values, index + 1, solutions);
    }
  }

  /**
   * The grid points that the store accepts: the variables are grounded to grid values one per
   * level, with a store consistency after each, and the points where every consistency succeeds are
   * returned. The store is back at its starting level afterwards.
   */
  private static Set<List<Double>> solveAll(Store store, Spec[] vars, Var[] x) {
    Set<List<Double>> found = new HashSet<>();
    if (store.consistency()) {
      enumerate(store, vars, x, 0, new double[x.length], found);
    }
    return found;
  }

  private static void enumerate(
      Store store, Spec[] vars, Var[] x, int index, double[] values, Set<List<Double>> found) {
    if (index == x.length) {
      found.add(Arrays.stream(values).boxed().toList());
      return;
    }
    int level = store.level;
    for (double v : vars[index].grid()) {
      store.setLevel(level + 1);
      try {
        ground(x[index], store.level, v);
        if (store.consistency()) {
          values[index] = v;
          enumerate(store, vars, x, index + 1, values, found);
        }
      } catch (FailException e) {
        // v is not in the domain
      }
      store.removeLevel(level + 1);
      store.setLevel(level);
    }
  }
}
