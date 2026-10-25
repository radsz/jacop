/*
 * ImposeGroundingHarness.java
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

package org.jacop;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.function.Predicate;
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
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;

/**
 * Checks that a constraint can be imposed when some or all of its variables are already ground, and
 * that it still has exactly the right solutions.
 *
 * <p>A {@link Case} gives small variable domains, a way to impose the constraint and a plain-Java
 * predicate on complete assignments. For each case the harness enumerates all solutions by brute
 * force and then, for many grounding plans, builds a fresh store, grounds a subset of the variables
 * to chosen values at a chosen moment, imposes the constraint and finds all solutions with search.
 * The found solutions must be exactly the brute-force solutions that agree with the grounded
 * values, and nothing but {@link FailException} may be thrown.
 *
 * <p>Subsets: none, all, each single variable, all but each single variable, first and last, and
 * random subsets. Values: from a solution (the constraint stays satisfiable), from a non-solution
 * (usually violating), the domain minimum or maximum (boundary values), or random domain values.
 * Moments ({@link When}): a singleton domain at creation, {@code in} before impose, {@code in}
 * after impose but before the first consistency, {@code in} at a search level after the root
 * consistency (then the level is removed and all solutions must come back), and a mix of the first
 * and third.
 *
 * <p>When the case also gives the constraint as a {@link PrimitiveConstraint}, the harness checks
 * it under {@link Reified}, {@link Not}, {@link Xor}, {@link Implies} and {@link IfThen} with an
 * extra 0/1 variable (also grounded in the plans), and checks {@code satisfied()} and {@code
 * notSatisfied()} once all variables are ground.
 *
 * <p>Usage from a JUnit test:
 *
 * <pre>{@code
 * ImposeGroundingHarness.check("XplusYeqZ", random -> Case.primitive(
 *     domains, x -> new XplusYeqZ(x[0], x[1], x[2]), t -> t[0] + t[1] == t[2], ""), 100);
 * }</pre>
 */
public final class ImposeGroundingHarness {

  /** How many failures are reported for a case before the harness stops looking for more. */
  private static final int MAX_REPORTED = 8;

  /** Value used in a grounding plan for a variable that is not grounded. */
  private static final int FREE = Integer.MIN_VALUE;

  private ImposeGroundingHarness() {}

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
   * One random instance of a constraint.
   *
   * @param domains the values of each variable (small, may have holes)
   * @param impose imposes the constraint on the variables of a store
   * @param semantics the intended relation on complete assignments, in variable order
   * @param description printed with failures to reproduce the instance
   * @param primitive builds the same constraint as a primitive constraint, or null if it is not
   *     one; enables the reified, negated and satisfied() checks
   */
  public record Case(
      int[][] domains,
      BiConsumer<Store, IntVar[]> impose,
      Predicate<int[]> semantics,
      String description,
      Function<IntVar[], PrimitiveConstraint> primitive) {

    /** A constraint that is imposed by the given code (global or decomposed constraints). */
    public static Case of(
        int[][] domains,
        BiConsumer<Store, IntVar[]> impose,
        Predicate<int[]> semantics,
        String description) {
      return new Case(domains, impose, semantics, description, null);
    }

    /** A primitive constraint; also checked reified, negated and with satisfied(). */
    public static Case primitive(
        int[][] domains,
        Function<IntVar[], PrimitiveConstraint> build,
        Predicate<int[]> semantics,
        String description) {
      return new Case(
          domains, (store, x) -> store.impose(build.apply(x)), semantics, description, build);
    }
  }

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
      if (c.primitive() != null) {
        for (String wrapper : List.of("Reified", "Not", "Xor", "Implies", "IfThen")) {
          checkCase(name + " trial " + trial + " " + wrapper, wrap(c, wrapper), random, failures);
        }
        checkSatisfied(name + " trial " + trial, c, random, failures);
      }
    }
    return failures;
  }

  /** The case under a wrapper; the extra 0/1 variable (if any) is the last one. */
  private static Case wrap(Case c, String wrapper) {
    Function<IntVar[], PrimitiveConstraint> build = c.primitive();
    Predicate<int[]> semantics = c.semantics();
    int n = c.domains().length;
    if (wrapper.equals("Not")) {
      return Case.of(
          c.domains(),
          (store, x) -> store.impose(new Not(build.apply(x))),
          t -> !semantics.test(t),
          c.description());
    }
    int[][] domains = Arrays.copyOf(c.domains(), n + 1);
    domains[n] = new int[] {0, 1};
    BiConsumer<Store, IntVar[]> impose =
        (store, x) -> {
          IntVar[] args = Arrays.copyOf(x, n);
          IntVar b = x[n];
          switch (wrapper) {
            case "Reified" -> store.impose(new Reified(build.apply(args), b));
            case "Xor" -> store.impose(new Xor(build.apply(args), b));
            case "Implies" -> store.impose(new Implies(b, build.apply(args)));
            default -> store.impose(new IfThen(new XeqC(b, 1), build.apply(args)));
          }
        };
    Predicate<int[]> wrapped =
        t -> {
          boolean holds = semantics.test(Arrays.copyOf(t, n));
          boolean b = t[n] == 1;
          return switch (wrapper) {
            case "Reified" -> b == holds;
            case "Xor" -> b != holds;
            default -> !b || holds;
          };
        };
    return Case.of(domains, impose, wrapped, c.description() + " (b is the last variable)");
  }

  private static void checkCase(String label, Case c, Random random, List<String> failures) {
    int n = c.domains().length;
    Set<List<Integer>> solutions = new HashSet<>();
    bruteForce(c, new int[n], 0, solutions);
    List<List<Integer>> solutionList = new ArrayList<>(solutions);
    solutionList.sort(ImposeGroundingHarness::compare);

    List<int[]> plans = plans(c, solutionList, random);
    When[] moments = When.values();
    for (int p = 0; p < plans.size() && failures.size() < MAX_REPORTED; p++) {
      int[] plan = plans.get(p);
      // the empty and the full plan run at every moment, the others at one moment each
      boolean extreme =
          Arrays.stream(plan).allMatch(v -> v == FREE)
              || Arrays.stream(plan).noneMatch(v -> v == FREE);
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
                  + " domains="
                  + Arrays.deepToString(c.domains())
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
  private static List<int[]> plans(Case c, List<List<Integer>> solutions, Random random) {
    int n = c.domains().length;
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

    List<int[]> plans = new ArrayList<>();
    for (int s = 0; s < subsets.size(); s++) {
      boolean[] subset = subsets.get(s);
      // the full subset gets every kind of value, the others one kind each, in turn
      int kinds = s == 1 ? 5 : 1;
      for (int k = 0; k < kinds; k++) {
        int kind = s == 1 ? k : s % 5;
        int[] values = values(c, solutions, random, kind);
        int[] plan = new int[n];
        for (int i = 0; i < n; i++) {
          plan[i] = subset[i] ? values[i] : FREE;
        }
        plans.add(plan);
      }
    }
    return plans;
  }

  /**
   * Values for all variables: 0 from a solution, 1 from a non-solution, 2 the domain minimum, 3 the
   * domain maximum, 4 random domain values.
   */
  private static int[] values(Case c, List<List<Integer>> solutions, Random random, int kind) {
    int[][] domains = c.domains();
    int n = domains.length;
    int[] values = new int[n];
    switch (kind) {
      case 0 -> {
        if (!solutions.isEmpty()) {
          List<Integer> s = solutions.get(random.nextInt(solutions.size()));
          for (int i = 0; i < n; i++) {
            values[i] = s.get(i);
          }
          return values;
        }
        return randomValues(domains, random);
      }
      case 1 -> {
        for (int attempt = 0; attempt < 20; attempt++) {
          values = randomValues(domains, random);
          if (!c.semantics().test(values)) {
            return values;
          }
        }
        return values;
      }
      case 2 -> {
        for (int i = 0; i < n; i++) {
          values[i] = domains[i][0];
        }
        return values;
      }
      case 3 -> {
        for (int i = 0; i < n; i++) {
          values[i] = domains[i][domains[i].length - 1];
        }
        return values;
      }
      default -> {
        return randomValues(domains, random);
      }
    }
  }

  private static int[] randomValues(int[][] domains, Random random) {
    int[] values = new int[domains.length];
    for (int i = 0; i < domains.length; i++) {
      values[i] = domains[i][random.nextInt(domains[i].length)];
    }
    return values;
  }

  /** Runs one plan; returns null if it behaves, or a description of what went wrong. */
  private static String run(Case c, int[] plan, When when, Set<List<Integer>> solutions) {
    Set<List<Integer>> expected = new HashSet<>();
    for (List<Integer> s : solutions) {
      if (agrees(s, plan)) {
        expected.add(s);
      }
    }
    int n = plan.length;
    Store store = new Store();
    IntVar[] x = new IntVar[n];
    String phase = "creating variables";
    try {
      for (int i = 0; i < n; i++) {
        boolean singleton =
            plan[i] != FREE && (when == When.SINGLETON_DOMAIN || when == When.MIXED && i % 2 == 0);
        x[i] =
            singleton
                ? new IntVar(store, "x" + i, plan[i], plan[i])
                : new IntVar(store, "x" + i, domain(c.domains()[i]));
      }
      if (when == When.BEFORE_IMPOSE) {
        phase = "grounding before impose";
        ground(store, x, plan, i -> true);
      }
      phase = "impose";
      c.impose().accept(store, x);
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
        Set<List<Integer>> found = new HashSet<>();
        try {
          ground(store, x, plan, i -> true);
          phase = "search at level " + (root + 1);
          found = solveAll(store, x);
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
        diff = compare(solveAll(store, x), solutions);
        return diff == null ? null : "after removing the grounding level: " + diff;
      }

      phase = "search";
      return compare(solveAll(store, x), expected);
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

  /** Checks satisfied() and notSatisfied() on a primitive constraint with all variables ground. */
  private static void checkSatisfied(String label, Case c, Random random, List<String> failures) {
    int[] values = randomValues(c.domains(), random);
    boolean holds = c.semantics().test(values);
    Store store = new Store();
    IntVar[] x = new IntVar[values.length];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, values[i], values[i]);
    }
    String where = label + " satisfied() values=" + Arrays.toString(values) + " " + c.description();
    try {
      PrimitiveConstraint p = c.primitive().apply(x);
      store.impose(p);
      if (p.satisfied() != holds) {
        failures.add(where + ": satisfied() is " + p.satisfied() + " but the relation is " + holds);
      } else if (p.notSatisfied() == holds) {
        failures.add(
            where + ": notSatisfied() is " + p.notSatisfied() + " but the relation is " + holds);
      }
    } catch (FailException e) {
      if (holds) {
        failures.add(where + ": FailException on impose although the relation holds");
      }
    } catch (Throwable e) {
      failures.add(where + ": " + describe(e, "satisfied()"));
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

  private static void ground(Store store, IntVar[] x, int[] plan, Predicate<Integer> which) {
    for (int i = 0; i < x.length; i++) {
      if (plan[i] != FREE && which.test(i)) {
        x[i].domain.in(store.level, x[i], plan[i], plan[i]);
      }
    }
  }

  private static boolean agrees(List<Integer> solution, int[] plan) {
    for (int i = 0; i < plan.length; i++) {
      if (plan[i] != FREE && solution.get(i) != plan[i]) {
        return false;
      }
    }
    return true;
  }

  private static String compare(Set<List<Integer>> found, Set<List<Integer>> expected) {
    if (found.equals(expected)) {
      return null;
    }
    Set<List<Integer>> missing = new HashSet<>(expected);
    missing.removeAll(found);
    Set<List<Integer>> wrong = new HashSet<>(found);
    wrong.removeAll(expected);
    return "expected "
        + expected.size()
        + " solution(s), found "
        + found.size()
        + (missing.isEmpty() ? "" : ", missing e.g. " + first(missing))
        + (wrong.isEmpty() ? "" : ", wrong e.g. " + first(wrong));
  }

  private static List<Integer> first(Set<List<Integer>> solutions) {
    return solutions.stream().min(ImposeGroundingHarness::compare).orElseThrow();
  }

  private static int compare(List<Integer> a, List<Integer> b) {
    for (int i = 0; i < Math.min(a.size(), b.size()); i++) {
      int c = Integer.compare(a.get(i), b.get(i));
      if (c != 0) {
        return c;
      }
    }
    return Integer.compare(a.size(), b.size());
  }

  private static String planToString(int[] plan) {
    StringBuilder s = new StringBuilder("[");
    for (int i = 0; i < plan.length; i++) {
      s.append(i == 0 ? "" : ", ").append(plan[i] == FREE ? "_" : String.valueOf(plan[i]));
    }
    return s.append(']').toString();
  }

  private static IntervalDomain domain(int[] values) {
    IntervalDomain domain = new IntervalDomain();
    for (int v : values) {
      domain.unionAdapt(v, v);
    }
    return domain;
  }

  private static void bruteForce(Case c, int[] values, int index, Set<List<Integer>> solutions) {
    if (index == values.length) {
      if (c.semantics().test(values)) {
        solutions.add(Arrays.stream(values).boxed().toList());
      }
      return;
    }
    for (int v : c.domains()[index]) {
      values[index] = v;
      bruteForce(c, values, index + 1, solutions);
    }
  }

  private static Set<List<Integer>> solveAll(Store store, IntVar[] x) {
    Set<List<Integer>> found = new HashSet<>();
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            found.add(Arrays.stream(x).map(IntVar::value).toList());
            return result;
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, new SimpleSelect<>(x, null, new IndomainMin<>()));
    return found;
  }
}
