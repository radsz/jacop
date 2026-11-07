/*
 * SetImposeGroundingHarness.java
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

package org.jacop.set;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Predicate;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;

/**
 * Checks that a set constraint can be imposed when some or all of its variables are already ground
 * or partly decided, and that it still has exactly the right solutions.
 *
 * <p>This is the set counterpart of {@code ImposeGroundingHarness} in jacop-core. A {@link Case}
 * gives small integer variables (a list of values) and set variables (a glb and a lub), a way to
 * impose the constraint and a plain-Java predicate on complete assignments. The harness enumerates
 * all solutions by brute force and then, for many grounding plans, builds a fresh store, restricts
 * a subset of the variables at a chosen moment, imposes the constraint and enumerates all solutions
 * with a plain depth-first search that branches on integer values and on set elements. The found
 * solutions must be exactly the brute-force solutions that agree with the restriction, and nothing
 * but {@link FailException} may be thrown.
 *
 * <p>A restricted integer variable is ground. A restricted set variable is either ground or partly
 * decided: some of its undecided elements are put in the glb or removed from the lub, as in the
 * chosen value. Subsets of variables, kinds of values and moments are as in the jacop-core harness:
 * none, all, each single variable, all but one, first and last, random subsets; values from a
 * solution, a non-solution, the smallest value (int minimum, set glb), the largest value (int
 * maximum, set lub) or random; a singleton domain at creation, before impose, after impose, at a
 * search level after the root consistency (then backtracked) and mixed. Grounding after creation
 * alternates between one {@code in} call per variable and element-wise {@code inGlb} / {@code
 * inLubComplement} calls, which raise different events.
 *
 * <p>When the imposed constraint implements {@link SatisfiedPresent}, {@code satisfied()} must be
 * true at every solution found by the search and false right after impose when all variables are
 * ground to a non-solution.
 */
public final class SetImposeGroundingHarness {

  /** How many failures are reported for a case before the harness stops looking for more. */
  private static final int MAX_REPORTED = 8;

  private SetImposeGroundingHarness() {}

  /** When the restricted variables get their restriction. */
  public enum When {
    /** The variable is created with the restricted domain. */
    SINGLETON_DOMAIN,
    /** Restricted after creation, before impose. */
    BEFORE_IMPOSE,
    /** Restricted after impose, before the first store consistency. */
    AFTER_IMPOSE,
    /** Restricted at store level + 1 after the root consistency, then the level is removed. */
    AT_SEARCH_LEVEL,
    /** Even-indexed restricted variables at creation, the others after impose. */
    MIXED
  }

  /**
   * One variable of a case: an integer variable with the given values, or a set variable with the
   * given glb and lub (sorted, glb a subset of lub).
   *
   * @param ints the values of an integer variable, or null for a set variable
   * @param glb the glb of a set variable
   * @param lub the lub of a set variable
   */
  public record Spec(int[] ints, int[] glb, int[] lub) {

    public static Spec intVar(int... values) {
      return new Spec(Arrays.stream(values).sorted().distinct().toArray(), null, null);
    }

    public static Spec setVar(int[] glb, int[] lub) {
      return new Spec(
          null,
          Arrays.stream(glb).sorted().distinct().toArray(),
          Arrays.stream(lub).sorted().distinct().toArray());
    }

    boolean isSet() {
      return ints == null;
    }

    /** All values of the variable; an integer value is a one-element array. */
    List<int[]> values() {
      List<int[]> values = new ArrayList<>();
      if (!isSet()) {
        for (int v : ints) {
          values.add(new int[] {v});
        }
        return values;
      }
      int[] free = Arrays.stream(lub).filter(e -> Arrays.binarySearch(glb, e) < 0).toArray();
      for (int mask = 0; mask < 1 << free.length; mask++) {
        TreeSet<Integer> s = new TreeSet<>();
        for (int e : glb) {
          s.add(e);
        }
        for (int i = 0; i < free.length; i++) {
          if ((mask >> i & 1) == 1) {
            s.add(free[i]);
          }
        }
        values.add(s.stream().mapToInt(Integer::intValue).toArray());
      }
      return values;
    }

    @Override
    public String toString() {
      return isSet() ? Arrays.toString(glb) + ".." + Arrays.toString(lub) : Arrays.toString(ints);
    }
  }

  /** A complete assignment, as seen by the predicate of a case. */
  public static final class Assignment {
    private final int[][] values;

    Assignment(int[][] values) {
      this.values = values;
    }

    /** The value of integer variable k. */
    public int i(int k) {
      return values[k][0];
    }

    /** The value of set variable k. */
    public Set<Integer> s(int k) {
      Set<Integer> s = new TreeSet<>();
      for (int e : values[k]) {
        s.add(e);
      }
      return s;
    }

    /** The sorted elements of set variable k. */
    public int[] elements(int k) {
      return values[k];
    }
  }

  /**
   * One random instance of a set constraint.
   *
   * @param vars the variables
   * @param impose imposes the constraint on the variables (in the order of vars, IntVar or SetVar)
   *     and returns it, or null when it imposes several constraints
   * @param semantics the intended relation on complete assignments
   * @param description printed with failures to reproduce the instance
   */
  public record Case(
      Spec[] vars,
      BiFunction<Store, Var[], Constraint> impose,
      Predicate<Assignment> semantics,
      String description) {}

  /** A restriction of one variable: ground to value, or a set variable within glb..lub. */
  private record Fix(int value, int[] glb, int[] lub) {

    boolean allows(int[] v) {
      if (glb == null) {
        return v[0] == value;
      }
      for (int e : glb) {
        if (Arrays.binarySearch(v, e) < 0) {
          return false;
        }
      }
      for (int e : v) {
        if (Arrays.binarySearch(lub, e) < 0) {
          return false;
        }
      }
      return true;
    }

    @Override
    public String toString() {
      return glb == null
          ? String.valueOf(value)
          : Arrays.equals(glb, lub)
              ? Arrays.toString(glb)
              : Arrays.toString(glb) + ".." + Arrays.toString(lub);
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
    List<String> failures = new ArrayList<>();
    Random random = new Random(name.hashCode());
    for (int trial = 0; trial < trials && failures.size() < MAX_REPORTED; trial++) {
      Case c = generator.apply(random);
      checkCase(name + " trial " + trial, c, random, failures);
    }
    if (!failures.isEmpty()) {
      throw new AssertionError(
          name + ": " + failures.size() + " failing plan(s)\n" + String.join("\n", failures));
    }
  }

  private static void checkCase(String label, Case c, Random random, List<String> failures) {
    Spec[] vars = c.vars();
    int n = vars.length;
    List<List<int[]>> values = new ArrayList<>();
    for (Spec s : vars) {
      values.add(s.values());
    }
    Set<List<Integer>> solutions = new HashSet<>();
    bruteForce(c, values, new int[n], 0, solutions);
    List<List<Integer>> solutionList = new ArrayList<>(solutions);
    solutionList.sort(SetImposeGroundingHarness::compare);

    String error = checkSatisfiedAfterImpose(c, values, solutions, random);
    if (error != null) {
      failures.add(label + " vars=" + Arrays.toString(vars) + " " + c.description() + ": " + error);
      return;
    }

    List<Fix[]> plans = plans(c, values, solutionList, random);
    When[] moments = When.values();
    for (int p = 0; p < plans.size() && failures.size() < MAX_REPORTED; p++) {
      Fix[] plan = plans.get(p);
      boolean extreme =
          Arrays.stream(plan).allMatch(f -> f == null)
              || Arrays.stream(plan).noneMatch(f -> f == null);
      List<When> whens = extreme ? List.of(moments) : List.of(moments[p % moments.length]);
      for (When when : whens) {
        boolean elementWise = (p + when.ordinal()) % 2 == 1;
        error = run(c, values, plan, when, elementWise, solutions);
        if (error != null) {
          failures.add(
              label
                  + " "
                  + when
                  + (elementWise ? " element-wise" : "")
                  + " restricted="
                  + Arrays.toString(plan).replace("null", "_")
                  + " vars="
                  + Arrays.toString(vars)
                  + " "
                  + c.description()
                  + ": "
                  + error);
          return;
        }
      }
    }
  }

  /** Grounds all variables to a random non-solution at creation; satisfied() must be false. */
  private static String checkSatisfiedAfterImpose(
      Case c, List<List<int[]>> values, Set<List<Integer>> solutions, Random random) {
    int n = values.size();
    List<Integer> tuple = null;
    for (int attempt = 0; attempt < 20 && tuple == null; attempt++) {
      List<Integer> t = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        t.add(random.nextInt(values.get(i).size()));
      }
      if (!solutions.contains(t)) {
        tuple = t;
      }
    }
    if (tuple == null) {
      return null;
    }
    Store store = new Store();
    Var[] x = new Var[n];
    Fix[] plan = new Fix[n];
    for (int i = 0; i < n; i++) {
      plan[i] = full(c.vars()[i], values.get(i).get(tuple.get(i)));
      x[i] = create(store, i, c.vars()[i], plan[i]);
    }
    try {
      Constraint constraint = c.impose().apply(store, x);
      if (constraint instanceof SatisfiedPresent s && s.satisfied()) {
        return "satisfied() is true right after impose with all variables ground to the"
            + " non-solution "
            + Arrays.toString(plan);
      }
    } catch (FailException e) {
      // rejecting a non-solution at impose is fine
    } catch (Throwable e) {
      return describe(e, "impose with all variables ground to " + Arrays.toString(plan));
    }
    return null;
  }

  private static Fix full(Spec spec, int[] value) {
    return spec.isSet() ? new Fix(0, value, value) : new Fix(value[0], null, null);
  }

  /** The restriction plans for one instance: null or a restriction for each variable. */
  private static List<Fix[]> plans(
      Case c, List<List<int[]>> values, List<List<Integer>> solutions, Random random) {
    int n = values.size();
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
    for (int k = 0; k < 3; k++) {
      boolean[] some = new boolean[n];
      for (int i = 0; i < n; i++) {
        some[i] = random.nextBoolean();
      }
      subsets.add(some);
    }

    List<Fix[]> plans = new ArrayList<>();
    for (int s = 0; s < subsets.size(); s++) {
      boolean[] subset = subsets.get(s);
      // the full subset gets every kind of value fully ground and once partly decided; the
      // others one kind each, in turn, with set variables partly decided every other time
      int kinds = s == 1 ? 6 : 1;
      for (int k = 0; k < kinds; k++) {
        int kind = s == 1 ? k % 5 : s % 5;
        boolean partial = s == 1 ? k == 5 : s % 2 == 0;
        int[] tuple = tuple(c, values, solutions, random, kind);
        Fix[] plan = new Fix[n];
        for (int i = 0; i < n; i++) {
          if (subset[i]) {
            Spec spec = c.vars()[i];
            int[] value = values.get(i).get(tuple[i]);
            plan[i] = partial && spec.isSet() ? partial(spec, value, random) : full(spec, value);
          }
        }
        plans.add(plan);
      }
    }
    return plans;
  }

  /** Decides a random nonempty subset of the undecided elements of a set variable as in value. */
  private static Fix partial(Spec spec, int[] value, Random random) {
    TreeSet<Integer> glb = new TreeSet<>();
    TreeSet<Integer> lub = new TreeSet<>();
    for (int e : spec.glb()) {
      glb.add(e);
    }
    for (int e : spec.lub()) {
      lub.add(e);
    }
    List<Integer> free = new ArrayList<>(lub);
    free.removeAll(glb);
    if (free.isEmpty()) {
      return full(spec, value);
    }
    int decided = 0;
    for (int e : free) {
      if (random.nextBoolean() || decided == 0 && e == free.get(free.size() - 1)) {
        decided++;
        if (Arrays.binarySearch(value, e) >= 0) {
          glb.add(e);
        } else {
          lub.remove(e);
        }
      }
    }
    return new Fix(
        0,
        glb.stream().mapToInt(Integer::intValue).toArray(),
        lub.stream().mapToInt(Integer::intValue).toArray());
  }

  /**
   * Value indexes for all variables: 0 from a solution, 1 from a non-solution, 2 the smallest
   * values, 3 the largest values, 4 random values.
   */
  private static int[] tuple(
      Case c, List<List<int[]>> values, List<List<Integer>> solutions, Random random, int kind) {
    int n = values.size();
    int[] tuple = new int[n];
    switch (kind) {
      case 0 -> {
        if (!solutions.isEmpty()) {
          List<Integer> s = solutions.get(random.nextInt(solutions.size()));
          for (int i = 0; i < n; i++) {
            tuple[i] = s.get(i);
          }
          return tuple;
        }
        return randomTuple(values, random);
      }
      case 1 -> {
        for (int attempt = 0; attempt < 20; attempt++) {
          tuple = randomTuple(values, random);
          if (!c.semantics().test(assignment(values, tuple))) {
            return tuple;
          }
        }
        return tuple;
      }
      case 2 -> {
        // index 0 is the minimum of an int variable and the glb of a set variable
        return tuple;
      }
      case 3 -> {
        for (int i = 0; i < n; i++) {
          tuple[i] = values.get(i).size() - 1;
        }
        return tuple;
      }
      default -> {
        return randomTuple(values, random);
      }
    }
  }

  private static int[] randomTuple(List<List<int[]>> values, Random random) {
    int[] tuple = new int[values.size()];
    for (int i = 0; i < tuple.length; i++) {
      tuple[i] = random.nextInt(values.get(i).size());
    }
    return tuple;
  }

  private static Assignment assignment(List<List<int[]>> values, int[] tuple) {
    int[][] a = new int[tuple.length][];
    for (int i = 0; i < tuple.length; i++) {
      a[i] = values.get(i).get(tuple[i]);
    }
    return new Assignment(a);
  }

  private static Var create(Store store, int i, Spec spec, Fix fix) {
    if (!spec.isSet()) {
      return fix != null
          ? new IntVar(store, "x" + i, fix.value(), fix.value())
          : new IntVar(store, "x" + i, domain(spec.ints()));
    }
    return fix != null
        ? new SetVar(store, "s" + i, new BoundSetDomain(domain(fix.glb()), domain(fix.lub())))
        : new SetVar(store, "s" + i, new BoundSetDomain(domain(spec.glb()), domain(spec.lub())));
  }

  /** Runs one plan; returns null if it behaves, or a description of what went wrong. */
  private static String run(
      Case c,
      List<List<int[]>> values,
      Fix[] plan,
      When when,
      boolean elementWise,
      Set<List<Integer>> solutions) {
    Set<List<Integer>> expected = new HashSet<>();
    for (List<Integer> s : solutions) {
      if (agrees(values, s, plan)) {
        expected.add(s);
      }
    }
    int n = plan.length;
    Store store = new Store();
    Var[] x = new Var[n];
    Constraint[] constraint = new Constraint[1];
    String phase = "creating variables";
    try {
      for (int i = 0; i < n; i++) {
        boolean atCreation =
            plan[i] != null && (when == When.SINGLETON_DOMAIN || when == When.MIXED && i % 2 == 0);
        x[i] = create(store, i, c.vars()[i], atCreation ? plan[i] : null);
      }
      if (when == When.BEFORE_IMPOSE) {
        phase = "restricting before impose";
        restrict(store, x, plan, i -> true, elementWise);
      }
      phase = "impose";
      constraint[0] = c.impose().apply(store, x);
      if (when == When.AFTER_IMPOSE || when == When.MIXED) {
        phase = "restricting after impose";
        restrict(store, x, plan, i -> when == When.AFTER_IMPOSE || i % 2 == 1, elementWise);
      }

      if (when == When.AT_SEARCH_LEVEL) {
        phase = "root consistency";
        if (!store.consistency()) {
          return solutions.isEmpty()
              ? null
              : "root consistency failed but "
                  + solutions.size()
                  + " solution(s) exist, e.g. "
                  + show(values, first(solutions));
        }
        int root = store.level;
        store.setLevel(root + 1);
        phase = "restricting at search level";
        Set<List<Integer>> found = new HashSet<>();
        String[] satisfiedError = new String[1];
        try {
          restrict(store, x, plan, i -> true, elementWise);
          phase = "search at level " + (root + 1);
          found = solveAll(store, x, values, constraint[0], satisfiedError);
        } catch (FailException e) {
          // the restriction itself is inconsistent; no solutions
        }
        if (satisfiedError[0] != null) {
          return satisfiedError[0];
        }
        String diff = compare(values, found, expected);
        if (diff != null) {
          return "after restricting at level " + (root + 1) + ": " + diff;
        }
        phase = "backtracking to the root";
        store.removeLevel(root + 1);
        store.setLevel(root);
        phase = "search after backtracking";
        diff =
            compare(values, solveAll(store, x, values, constraint[0], satisfiedError), solutions);
        if (satisfiedError[0] != null) {
          return satisfiedError[0];
        }
        return diff == null ? null : "after removing the restriction level: " + diff;
      }

      phase = "search";
      String[] satisfiedError = new String[1];
      Set<List<Integer>> found = solveAll(store, x, values, constraint[0], satisfiedError);
      if (satisfiedError[0] != null) {
        return satisfiedError[0];
      }
      return compare(values, found, expected);
    } catch (FailException e) {
      return expected.isEmpty()
          ? null
          : "FailException during "
              + phase
              + " but "
              + expected.size()
              + " solution(s) exist, e.g. "
              + show(values, first(expected));
    } catch (Throwable e) {
      return describe(e, phase);
    }
  }

  private static String describe(Throwable e, String phase) {
    StackTraceElement[] trace = e.getStackTrace();
    StringBuilder where = new StringBuilder();
    for (int i = 0; i < Math.min(5, trace.length); i++) {
      where.append("\n      at ").append(trace[i]);
    }
    return e.getClass().getSimpleName() + " during " + phase + ": " + e.getMessage() + where;
  }

  private static void restrict(
      Store store, Var[] x, Fix[] plan, Predicate<Integer> which, boolean elementWise) {
    for (int i = 0; i < x.length; i++) {
      Fix fix = plan[i];
      if (fix == null || !which.test(i)) {
        continue;
      }
      if (x[i] instanceof IntVar v) {
        v.domain.in(store.level, v, fix.value(), fix.value());
      } else {
        SetVar s = (SetVar) x[i];
        if (elementWise) {
          for (int e : fix.glb()) {
            s.domain.inGlb(store.level, s, e);
          }
          for (int e : s.dom().lub().toIntArray()) {
            if (Arrays.binarySearch(fix.lub(), e) < 0) {
              s.domain.inLubComplement(store.level, s, e);
            }
          }
        } else {
          s.domain.in(store.level, s, domain(fix.glb()), domain(fix.lub()));
        }
      }
    }
  }

  private static boolean agrees(List<List<int[]>> values, List<Integer> solution, Fix[] plan) {
    for (int i = 0; i < plan.length; i++) {
      if (plan[i] != null && !plan[i].allows(values.get(i).get(solution.get(i)))) {
        return false;
      }
    }
    return true;
  }

  private static String compare(
      List<List<int[]>> values, Set<List<Integer>> found, Set<List<Integer>> expected) {
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
        + (missing.isEmpty() ? "" : ", missing e.g. " + show(values, first(missing)))
        + (wrong.isEmpty() ? "" : ", wrong e.g. " + show(values, first(wrong)));
  }

  private static String show(List<List<int[]>> values, List<Integer> tuple) {
    StringBuilder s = new StringBuilder("[");
    for (int i = 0; i < tuple.size(); i++) {
      s.append(i == 0 ? "" : ", ").append(Arrays.toString(values.get(i).get(tuple.get(i))));
    }
    return s.append(']').toString();
  }

  private static List<Integer> first(Set<List<Integer>> solutions) {
    return solutions.stream().min(SetImposeGroundingHarness::compare).orElseThrow();
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

  private static IntDomain domain(int[] values) {
    IntervalDomain domain = new IntervalDomain();
    for (int v : values) {
      domain.unionAdapt(v, v);
    }
    return domain;
  }

  private static void bruteForce(
      Case c, List<List<int[]>> values, int[] tuple, int index, Set<List<Integer>> solutions) {
    if (index == tuple.length) {
      if (c.semantics().test(assignment(values, tuple))) {
        solutions.add(Arrays.stream(tuple).boxed().toList());
      }
      return;
    }
    for (int v = 0; v < values.get(index).size(); v++) {
      tuple[index] = v;
      bruteForce(c, values, tuple, index + 1, solutions);
    }
  }

  /**
   * All solutions below the current store level, by a depth-first search that branches on the
   * smallest value of the first unground integer variable (x = v, x != v) or on the smallest
   * undecided element of the first unground set variable (e in s, e not in s).
   */
  private static Set<List<Integer>> solveAll(
      Store store, Var[] x, List<List<int[]>> values, Constraint constraint, String[] error) {
    List<Map<String, Integer>> index = new ArrayList<>();
    for (List<int[]> vs : values) {
      Map<String, Integer> m = new HashMap<>();
      for (int i = 0; i < vs.size(); i++) {
        m.put(Arrays.toString(vs.get(i)), i);
      }
      index.add(m);
    }
    Set<List<Integer>> found = new HashSet<>();
    int base = store.level;
    dfs(store, x, index, constraint, found, error);
    store.setLevel(base);
    return found;
  }

  private static void dfs(
      Store store,
      Var[] x,
      List<Map<String, Integer>> index,
      Constraint constraint,
      Set<List<Integer>> found,
      String[] error) {
    if (!store.consistency()) {
      return;
    }
    int k = 0;
    while (k < x.length && x[k].singleton()) {
      k++;
    }
    if (k == x.length) {
      List<Integer> tuple = new ArrayList<>();
      for (int i = 0; i < x.length; i++) {
        int[] v =
            x[i] instanceof IntVar iv
                ? new int[] {iv.value()}
                : ((SetVar) x[i]).dom().glb().toIntArray();
        Integer t = index.get(i).get(Arrays.toString(v));
        if (t == null) {
          error[0] = "search found a value outside the domain: " + x[i];
          return;
        }
        tuple.add(t);
      }
      if (constraint instanceof SatisfiedPresent s && !s.satisfied() && error[0] == null) {
        error[0] = "satisfied() is false at the solution " + Arrays.toString(x);
      }
      found.add(tuple);
      return;
    }
    int level = store.level;
    for (int branch = 0; branch < 2; branch++) {
      store.setLevel(level + 1);
      try {
        if (x[k] instanceof IntVar v) {
          int min = v.min();
          if (branch == 0) {
            v.domain.in(store.level, v, min, min);
          } else {
            v.domain.inComplement(store.level, v, min);
          }
        } else {
          SetVar s = (SetVar) x[k];
          int e = s.dom().lub().subtract(s.dom().glb()).min();
          if (branch == 0) {
            s.domain.inGlb(store.level, s, e);
          } else {
            s.domain.inLubComplement(store.level, s, e);
          }
        }
        dfs(store, x, index, constraint, found, error);
      } catch (FailException e) {
        // dead branch
      }
      store.removeLevel(level + 1);
      store.setLevel(level);
    }
  }
}
