/*
 * SetPrimitiveGroundingHarness.java
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
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
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
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;

/**
 * Checks that a set constraint can be imposed when some or all of its variables are already ground
 * or partly decided, and that it still has exactly the right solutions. It follows the plan of
 * {@code org.jacop.ImposeGroundingHarness} in jacop-core, with set variables.
 *
 * <p>A {@link Case} gives small variable specifications ({@link Spec}: an int variable with a list
 * of values, or a set variable with a glb, a lub and optionally a cardinality range), a way to
 * impose the constraint and a plain-Java predicate on complete assignments, where an int variable
 * is an {@link Integer} and a set variable a {@link SortedSet} of its elements. The harness
 * enumerates all solutions by brute force and then, for many grounding plans, builds a fresh store,
 * fixes a subset of the variables at a chosen moment, imposes the constraint and finds all
 * solutions with its own depth-first search (int variables by value, set variables element in or
 * out). The found solutions must be exactly the brute-force solutions that agree with the plan, and
 * nothing but {@link FailException} may be thrown.
 *
 * <p>Subsets: none, all, each single variable, all but each single variable, first and last, and
 * random subsets. Values: from a solution, from a non-solution, the smallest value (int minimum,
 * set glb), the largest value (int maximum, set lub) or random values. A set variable in a plan is
 * either ground or, in some plans, only partly decided: a random part of its undecided elements is
 * put into the glb or removed from the lub as in the value, which checks states between free and
 * ground. Moments ({@link When}): singleton domain at creation, before impose, after impose but
 * before the first consistency, at a search level after the root consistency (then the level is
 * removed and all solutions must come back), and a mix of the first and third.
 *
 * <p>{@code SetImposeGroundingHarness} does the same for any set constraint and checks {@code
 * satisfied()} along the search; this harness is for primitive constraints, whose negation and
 * reification are where grounded variables most often broke them.
 *
 * <p>When the case also gives the constraint as a {@link PrimitiveConstraint}, the harness checks
 * it under {@link Reified}, {@link Not}, {@link Xor}, {@link Implies} and {@link IfThen} with an
 * extra 0/1 int variable, and checks {@code satisfied()} and {@code notSatisfied()} once all
 * variables are ground.
 */
public final class SetPrimitiveGroundingHarness {

  /** How many failures are reported for a case before the harness stops looking for more. */
  private static final int MAX_REPORTED = 8;

  /** Value used in a grounding plan for a variable that is not fixed. */
  private static final int FREE = Integer.MIN_VALUE;

  private SetPrimitiveGroundingHarness() {}

  /** When the fixed variables get their values. */
  public enum When {
    /** The variable is created with its fixed domain. */
    SINGLETON_DOMAIN,
    /** The variable is created with its full domain and fixed before impose. */
    BEFORE_IMPOSE,
    /** Fixed after impose, before the first store consistency. */
    AFTER_IMPOSE,
    /** Fixed at store level + 1 after the root consistency; the level is then removed. */
    AT_SEARCH_LEVEL,
    /** Even-indexed fixed variables at creation, the others after impose. */
    MIXED
  }

  /**
   * One variable: an int variable with the given values, or a set variable with glb, lub and a
   * cardinality range. Set values are encoded as bit masks over the positions of {@code lub}.
   *
   * @param ints the values of an int variable, or null for a set variable
   * @param glb the elements every value of a set variable contains
   * @param lub the elements a value of a set variable may contain, sorted
   * @param cardMin the smallest cardinality of a set value
   * @param cardMax the largest cardinality of a set value
   */
  public record Spec(int[] ints, int[] glb, int[] lub, int cardMin, int cardMax) {

    /** An int variable with these values. */
    public static Spec ints(int... values) {
      return new Spec(values, null, null, 0, 0);
    }

    /** A set variable between glb and lub (sorted, glb within lub). */
    public static Spec set(int[] glb, int[] lub) {
      return new Spec(null, glb, lub, 0, Integer.MAX_VALUE);
    }

    /** A set variable between glb and lub with a cardinality range. */
    public static Spec set(int[] glb, int[] lub, int cardMin, int cardMax) {
      return new Spec(null, glb, lub, cardMin, cardMax);
    }

    boolean isSet() {
      return ints == null;
    }

    int glbMask() {
      int mask = 0;
      for (int e : glb) {
        mask |= 1 << Arrays.binarySearch(lub, e);
      }
      return mask;
    }

    /** All encoded values of this variable in increasing order of code. */
    int[] values() {
      if (!isSet()) {
        return ints;
      }
      int glbMask = glbMask();
      List<Integer> codes = new ArrayList<>();
      for (int mask = 0; mask < 1 << lub.length; mask++) {
        int card = Integer.bitCount(mask);
        if ((mask & glbMask) == glbMask && card >= cardMin && card <= cardMax) {
          codes.add(mask);
        }
      }
      return codes.stream().mapToInt(Integer::intValue).toArray();
    }

    /** The plain-Java value of a code: an Integer or a sorted set. */
    Object decode(int code) {
      if (!isSet()) {
        return code;
      }
      SortedSet<Integer> s = new TreeSet<>();
      for (int i = 0; i < lub.length; i++) {
        if ((code & 1 << i) != 0) {
          s.add(lub[i]);
        }
      }
      return s;
    }

    IntDomain domainOf(int code) {
      IntervalDomain d = new IntervalDomain();
      for (int i = 0; i < lub.length; i++) {
        if ((code & 1 << i) != 0) {
          d.unionAdapt(lub[i], lub[i]);
        }
      }
      return d;
    }

    String toText() {
      if (!isSet()) {
        return Arrays.toString(ints);
      }
      return "glb="
          + Arrays.toString(glb)
          + " lub="
          + Arrays.toString(lub)
          + (cardMin > 0 || cardMax != Integer.MAX_VALUE
              ? " card=" + cardMin + ".." + cardMax
              : "");
    }
  }

  /**
   * One random instance of a constraint.
   *
   * @param specs the variables
   * @param impose imposes the constraint on the variables of a store (IntVar or SetVar, in order)
   * @param semantics the intended relation on complete assignments, in variable order
   * @param description printed with failures to reproduce the instance
   * @param primitive builds the same constraint as a primitive constraint, or null if it is not one
   */
  public record Case(
      Spec[] specs,
      BiConsumer<Store, Var[]> impose,
      Predicate<Object[]> semantics,
      String description,
      Function<Var[], PrimitiveConstraint> primitive) {

    /** A constraint that is imposed by the given code. */
    public static Case of(
        Spec[] specs,
        BiConsumer<Store, Var[]> impose,
        Predicate<Object[]> semantics,
        String description) {
      return new Case(specs, impose, semantics, description, null);
    }

    /** A primitive constraint; also checked reified, negated and with satisfied(). */
    public static Case primitive(
        Spec[] specs,
        Function<Var[], PrimitiveConstraint> build,
        Predicate<Object[]> semantics,
        String description) {
      return new Case(
          specs, (store, x) -> store.impose(build.apply(x)), semantics, description, build);
    }
  }

  /** A plan: the code of each variable (or FREE) and, for set variables, which positions to fix. */
  private record Plan(int[] codes, int[] fixed) {

    boolean agrees(List<Integer> solution, Spec[] specs) {
      for (int i = 0; i < codes.length; i++) {
        if (codes[i] == FREE) {
          continue;
        }
        int mask = specs[i].isSet() ? fixed[i] : -1;
        if ((solution.get(i) & mask) != (codes[i] & mask)) {
          return false;
        }
      }
      return true;
    }

    String toText(Spec[] specs) {
      StringBuilder s = new StringBuilder("[");
      for (int i = 0; i < codes.length; i++) {
        s.append(i == 0 ? "" : ", ");
        if (codes[i] == FREE) {
          s.append('_');
        } else if (!specs[i].isSet()) {
          s.append(codes[i]);
        } else {
          Spec spec = specs[i];
          boolean ground = fixed[i] == (1 << spec.lub().length) - 1;
          if (ground) {
            s.append(spec.decode(codes[i]));
          } else {
            s.append("in ")
                .append(spec.decode(codes[i] & fixed[i]))
                .append(" out ")
                .append(spec.decode(~codes[i] & fixed[i]));
          }
        }
      }
      return s.append(']').toString();
    }
  }

  private static void checkWrapped(String label, Case c, Random random, List<String> failures) {
    if (c.primitive() != null) {
      for (String wrapper : List.of("Reified", "Not", "Xor", "Implies", "IfThen")) {
        checkCase(label + " " + wrapper, wrap(c, wrapper), random, failures);
      }
      checkSatisfied(label, c, random, failures);
    }
  }

  /**
   * The case with two variables of the same specification merged into one, or null when it has no
   * two such variables. The aliased case has one variable fewer: position {@code j} of the original
   * reads the variable of position {@code i}.
   */
  static Case alias(Case c, Random random) {
    int n = c.specs().length;
    List<int[]> pairs = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (i != j
            && c.specs()[i].isSet() == c.specs()[j].isSet()
            && c.specs()[i].toText().equals(c.specs()[j].toText())) {
          pairs.add(new int[] {i, j});
        }
      }
    }
    if (pairs.isEmpty()) {
      return null;
    }
    int[] pair = pairs.get(random.nextInt(pairs.size()));
    int i = pair[0];
    int j = pair[1];
    int[] map = new int[n];
    Spec[] specs = new Spec[n - 1];
    for (int p = 0, q = 0; p < n; p++) {
      if (p == j) {
        continue;
      }
      map[p] = q;
      specs[q++] = c.specs()[p];
    }
    map[j] = map[i];
    Function<Var[], Var[]> expand = x -> Arrays.stream(map).mapToObj(p -> x[p]).toArray(Var[]::new);
    Predicate<Object[]> semantics =
        t -> c.semantics().test(Arrays.stream(map).mapToObj(p -> t[p]).toArray());
    String description = c.description() + " (x" + j + " is x" + i + " of the original)";
    Function<Var[], PrimitiveConstraint> build = c.primitive();
    if (build != null) {
      return Case.primitive(specs, x -> build.apply(expand.apply(x)), semantics, description);
    }
    return Case.of(
        specs, (store, x) -> c.impose().accept(store, expand.apply(x)), semantics, description);
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
      checkWrapped(name + " trial " + trial, c, random, failures);
      Case aliased = alias(c, random);
      if (aliased != null) {
        String label = name + " trial " + trial + " aliased";
        checkCase(label, aliased, random, failures);
        checkWrapped(label, aliased, random, failures);
      }
    }
    if (!failures.isEmpty()) {
      throw new AssertionError(
          name + ": " + failures.size() + " failing plan(s)\n" + String.join("\n", failures));
    }
  }

  /** The case under a wrapper; the extra 0/1 variable (if any) is the last one. */
  private static Case wrap(Case c, String wrapper) {
    Function<Var[], PrimitiveConstraint> build = c.primitive();
    Predicate<Object[]> semantics = c.semantics();
    int n = c.specs().length;
    if (wrapper.equals("Not")) {
      return Case.of(
          c.specs(),
          (store, x) -> store.impose(new Not(build.apply(x))),
          t -> !semantics.test(t),
          c.description());
    }
    Spec[] specs = Arrays.copyOf(c.specs(), n + 1);
    specs[n] = Spec.ints(0, 1);
    BiConsumer<Store, Var[]> impose =
        (store, x) -> {
          Var[] args = Arrays.copyOf(x, n);
          IntVar b = (IntVar) x[n];
          switch (wrapper) {
            case "Reified" -> store.impose(new Reified(build.apply(args), b));
            case "Xor" -> store.impose(new Xor(build.apply(args), b));
            case "Implies" -> store.impose(new Implies(b, build.apply(args)));
            default -> store.impose(new IfThen(new XeqC(b, 1), build.apply(args)));
          }
        };
    Predicate<Object[]> wrapped =
        t -> {
          boolean holds = semantics.test(Arrays.copyOf(t, n));
          boolean b = (Integer) t[n] == 1;
          return switch (wrapper) {
            case "Reified" -> b == holds;
            case "Xor" -> b != holds;
            default -> !b || holds;
          };
        };
    return Case.of(specs, impose, wrapped, c.description() + " (b is the last variable)");
  }

  private static void checkCase(String label, Case c, Random random, List<String> failures) {
    int n = c.specs().length;
    Set<List<Integer>> solutions = new HashSet<>();
    bruteForce(c, new int[n], 0, solutions);
    List<List<Integer>> solutionList = new ArrayList<>(solutions);
    solutionList.sort(SetPrimitiveGroundingHarness::compare);

    List<Plan> plans = plans(c, solutionList, random);
    When[] moments = When.values();
    for (int p = 0; p < plans.size() && failures.size() < MAX_REPORTED; p++) {
      Plan plan = plans.get(p);
      // the empty and the full plan run at every moment, the others at one moment each
      boolean extreme =
          Arrays.stream(plan.codes()).allMatch(v -> v == FREE)
              || Arrays.stream(plan.codes()).noneMatch(v -> v == FREE);
      List<When> whens = extreme ? List.of(moments) : List.of(moments[p % moments.length]);
      for (When when : whens) {
        String error = run(c, plan, when, solutions);
        if (error != null) {
          failures.add(
              label
                  + " "
                  + when
                  + " fixed="
                  + plan.toText(c.specs())
                  + " vars="
                  + specsToText(c.specs())
                  + " "
                  + c.description()
                  + ": "
                  + error);
          return;
        }
      }
    }
  }

  /** The grounding plans for one instance. */
  private static List<Plan> plans(Case c, List<List<Integer>> solutions, Random random) {
    Spec[] specs = c.specs();
    int n = specs.length;
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

    List<Plan> plans = new ArrayList<>();
    for (int s = 0; s < subsets.size(); s++) {
      boolean[] subset = subsets.get(s);
      // the full subset gets every kind of value, the others one kind each, in turn
      int kinds = s == 1 ? 5 : 1;
      for (int k = 0; k < kinds; k++) {
        int kind = s == 1 ? k : s % 5;
        int[] values = values(c, solutions, random, kind);
        // each subset is used ground and, where it has set variables, also partly decided
        for (boolean partial : new boolean[] {false, true}) {
          int[] codes = new int[n];
          int[] fixed = new int[n];
          boolean anyPartial = false;
          for (int i = 0; i < n; i++) {
            codes[i] = subset[i] ? values[i] : FREE;
            if (subset[i] && specs[i].isSet()) {
              int full = (1 << specs[i].lub().length) - 1;
              fixed[i] = partial ? random.nextInt(full + 1) : full;
              anyPartial |= fixed[i] != full;
            }
          }
          if (!partial || anyPartial) {
            plans.add(new Plan(codes, fixed));
          }
        }
      }
    }
    return plans;
  }

  /**
   * Codes for all variables: 0 from a solution, 1 from a non-solution, 2 the smallest values, 3 the
   * largest values, 4 random values.
   */
  private static int[] values(Case c, List<List<Integer>> solutions, Random random, int kind) {
    Spec[] specs = c.specs();
    int n = specs.length;
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
        return randomValues(specs, random);
      }
      case 1 -> {
        for (int attempt = 0; attempt < 20; attempt++) {
          values = randomValues(specs, random);
          if (!c.semantics().test(decode(specs, values))) {
            return values;
          }
        }
        return values;
      }
      case 2, 3 -> {
        for (int i = 0; i < n; i++) {
          int[] all = specs[i].values();
          values[i] = all.length == 0 ? 0 : kind == 2 ? all[0] : all[all.length - 1];
        }
        return values;
      }
      default -> {
        return randomValues(specs, random);
      }
    }
  }

  private static int[] randomValues(Spec[] specs, Random random) {
    int[] values = new int[specs.length];
    for (int i = 0; i < specs.length; i++) {
      int[] all = specs[i].values();
      values[i] = all.length == 0 ? 0 : all[random.nextInt(all.length)];
    }
    return values;
  }

  private static Object[] decode(Spec[] specs, int[] codes) {
    Object[] t = new Object[codes.length];
    for (int i = 0; i < codes.length; i++) {
      t[i] = specs[i].decode(codes[i]);
    }
    return t;
  }

  /** Runs one plan; returns null if it behaves, or a description of what went wrong. */
  private static String run(Case c, Plan plan, When when, Set<List<Integer>> solutions) {
    Spec[] specs = c.specs();
    Set<List<Integer>> expected = new HashSet<>();
    for (List<Integer> s : solutions) {
      if (plan.agrees(s, specs)) {
        expected.add(s);
      }
    }
    int n = specs.length;
    Store store = new Store();
    Var[] x = new Var[n];
    String phase = "creating variables";
    try {
      for (int i = 0; i < n; i++) {
        boolean atCreation =
            plan.codes()[i] != FREE
                && (when == When.SINGLETON_DOMAIN || when == When.MIXED && i % 2 == 0);
        x[i] = create(store, "x" + i, specs[i], atCreation ? plan : null, i);
      }
      if (when == When.BEFORE_IMPOSE) {
        phase = "fixing before impose";
        fix(store, x, specs, plan, i -> true);
      }
      phase = "impose";
      c.impose().accept(store, x);
      if (when == When.AFTER_IMPOSE || when == When.MIXED) {
        phase = "fixing after impose";
        fix(store, x, specs, plan, i -> when == When.AFTER_IMPOSE || i % 2 == 1);
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
        phase = "fixing at search level";
        Set<List<Integer>> found = new HashSet<>();
        try {
          fix(store, x, specs, plan, i -> true);
          phase = "search at level " + (root + 1);
          found = solveAll(store, x, specs);
        } catch (FailException e) {
          // the plan itself is inconsistent; no solutions
        }
        String diff = compare(found, expected);
        if (diff != null) {
          return "after fixing at level " + (root + 1) + ": " + diff;
        }
        phase = "backtracking to the root";
        store.removeLevel(root + 1);
        store.setLevel(root);
        phase = "search after backtracking";
        diff = compare(solveAll(store, x, specs), solutions);
        return diff == null ? null : "after removing the fixing level: " + diff;
      }

      phase = "search";
      return compare(solveAll(store, x, specs), expected);
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

  /** Creates a variable, already fixed by the plan when {@code plan} is not null. */
  private static Var create(Store store, String name, Spec spec, Plan plan, int i) {
    if (!spec.isSet()) {
      if (plan != null) {
        return new IntVar(store, name, plan.codes()[i], plan.codes()[i]);
      }
      IntervalDomain d = new IntervalDomain();
      for (int v : spec.ints()) {
        d.unionAdapt(v, v);
      }
      return new IntVar(store, name, d);
    }
    int full = (1 << spec.lub().length) - 1;
    int glb = spec.glbMask();
    int lub = full;
    if (plan != null) {
      glb |= plan.codes()[i] & plan.fixed()[i];
      lub &= ~(~plan.codes()[i] & plan.fixed()[i]);
    }
    BoundSetDomain d =
        spec.cardMin() > 0 || spec.cardMax() != Integer.MAX_VALUE
            ? new BoundSetDomain(
                spec.domainOf(glb),
                spec.domainOf(lub),
                new IntervalDomain(spec.cardMin(), Math.min(spec.cardMax(), spec.lub().length)))
            : new BoundSetDomain(spec.domainOf(glb), spec.domainOf(lub));
    return new SetVar(store, name, d);
  }

  /** Checks satisfied() and notSatisfied() on a primitive constraint with all variables ground. */
  private static void checkSatisfied(String label, Case c, Random random, List<String> failures) {
    Spec[] specs = c.specs();
    int[] codes = randomValues(specs, random);
    boolean holds = c.semantics().test(decode(specs, codes));
    Store store = new Store();
    Var[] x = new Var[codes.length];
    int[] fixed = new int[codes.length];
    Arrays.fill(fixed, -1);
    Plan plan = new Plan(codes, fixed);
    for (int i = 0; i < x.length; i++) {
      x[i] = create(store, "x" + i, specs[i], plan, i);
    }
    String where =
        label
            + " satisfied() values="
            + Arrays.toString(decode(specs, codes))
            + " "
            + c.description();
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

  private static void fix(Store store, Var[] x, Spec[] specs, Plan plan, Predicate<Integer> which) {
    for (int i = 0; i < x.length; i++) {
      int code = plan.codes()[i];
      if (code == FREE || !which.test(i)) {
        continue;
      }
      if (x[i] instanceof IntVar v) {
        v.domain.in(store.level, v, code, code);
      } else {
        SetVar s = (SetVar) x[i];
        Spec spec = specs[i];
        int in = code & plan.fixed()[i];
        int out = ~code & plan.fixed()[i] & ((1 << spec.lub().length) - 1);
        if (in != 0) {
          s.domain.inGlb(store.level, s, spec.domainOf(in));
        }
        if (out != 0) {
          IntDomain lub = s.domain.lub().subtract(spec.domainOf(out));
          s.domain.inLub(store.level, s, lub);
        }
      }
    }
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
    return solutions.stream().min(SetPrimitiveGroundingHarness::compare).orElseThrow();
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

  private static String specsToText(Spec[] specs) {
    StringBuilder s = new StringBuilder("[");
    for (int i = 0; i < specs.length; i++) {
      s.append(i == 0 ? "" : ", ").append(specs[i].toText());
    }
    return s.append(']').toString();
  }

  private static void bruteForce(Case c, int[] codes, int index, Set<List<Integer>> solutions) {
    if (index == codes.length) {
      if (c.semantics().test(decode(c.specs(), codes))) {
        solutions.add(Arrays.stream(codes).boxed().toList());
      }
      return;
    }
    for (int v : c.specs()[index].values()) {
      codes[index] = v;
      bruteForce(c, codes, index + 1, solutions);
    }
  }

  /**
   * All solutions from the current store state, as codes; solutions are reported as the brute force
   * encodes them (set values as masks over the spec's lub).
   */
  private static Set<List<Integer>> solveAll(Store store, Var[] x, Spec[] specs) {
    Set<List<Integer>> found = new HashSet<>();
    dfs(store, x, specs, found);
    return found;
  }

  private static void dfs(Store store, Var[] x, Spec[] specs, Set<List<Integer>> found) {
    if (!store.consistency()) {
      return;
    }
    for (int i = 0; i < x.length; i++) {
      if (x[i].singleton()) {
        continue;
      }
      int level = store.level;
      if (x[i] instanceof IntVar v) {
        for (ValueEnumeration e = v.dom().valueEnumeration(); e.hasMoreElements(); ) {
          int value = e.nextElement();
          branch(store, x, specs, found, level, () -> v.domain.in(level + 1, v, value, value));
        }
      } else {
        SetVar s = (SetVar) x[i];
        int element = s.domain.lub().subtract(s.domain.glb()).min();
        branch(store, x, specs, found, level, () -> s.domain.inGlb(level + 1, s, element));
        branch(
            store, x, specs, found, level, () -> s.domain.inLubComplement(level + 1, s, element));
      }
      return;
    }
    List<Integer> solution = new ArrayList<>();
    for (int i = 0; i < x.length; i++) {
      if (x[i] instanceof IntVar v) {
        solution.add(v.value());
      } else {
        IntDomain value = ((SetVar) x[i]).domain.glb();
        int code = 0;
        int[] lub = specs[i].lub();
        for (ValueEnumeration e = value.valueEnumeration(); e.hasMoreElements(); ) {
          int pos = Arrays.binarySearch(lub, e.nextElement());
          // an element outside the spec's lub cannot be encoded; make the solution wrong
          code |= pos < 0 ? 1 << 30 : 1 << pos;
        }
        solution.add(code);
      }
    }
    found.add(solution);
  }

  private static void branch(
      Store store, Var[] x, Spec[] specs, Set<List<Integer>> found, int level, Runnable decision) {
    store.setLevel(level + 1);
    try {
      decision.run();
      dfs(store, x, specs, found);
    } catch (FailException e) {
      // dead branch
    }
    store.removeLevel(level + 1);
    store.setLevel(level);
  }
}
