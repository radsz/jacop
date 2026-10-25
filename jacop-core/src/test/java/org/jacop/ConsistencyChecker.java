/*
 * ConsistencyChecker.java
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

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.function.BiFunction;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Among;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.CountBounds;
import org.jacop.constraints.CountVar;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.Distance;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.ElementVariable;
import org.jacop.constraints.ElementVariableFast;
import org.jacop.constraints.GCC;
import org.jacop.constraints.Increasing;
import org.jacop.constraints.Lex;
import org.jacop.constraints.LinearBool;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.Max;
import org.jacop.constraints.Member;
import org.jacop.constraints.Min;
import org.jacop.constraints.Not;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.Values;
import org.jacop.constraints.XdivYeqZ;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XmodYeqZ;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusClteqZImplied;
import org.jacop.constraints.XplusCneqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.geost.GeostInstance;
import org.jacop.geost.GeostInstance.Rect;
import org.jacop.geost.GeostInstanceGenerator;
import org.jacop.geost.GeostInstanceGenerator.Family;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

/**
 * Checks the consistency a propagator reaches, by random search on a store with only that
 * constraint. After propagation at every node it looks for a support of each variable's bounds by
 * brute force:
 *
 * <ul>
 *   <li>bounds(R), only for models that give a check over the reals: the bound with the other
 *       variables anywhere in their real [min, max];
 *   <li>bounds(Z): the bound with the other variables anywhere in their [min, max];
 *   <li>bounds(D): the bound with the other variables in their domains;
 *   <li>domain (GAC): every value with the other variables in their domains.
 * </ul>
 *
 * <p>It also checks that propagation keeps every solution inside the domains it started from, and
 * fails only when there is none, so a propagator that prunes too much is reported as wrong rather
 * than strong.
 *
 * <p>This is a tool for improving propagators, not part of the build: no Maven profile includes it.
 * Run it on demand (see CLAUDE.md):
 *
 * <pre>
 * mvn -Pmin -pl jacop-core test -Dtest=ConsistencyChecker -Dsurefire.rerunFailingTestsCount=0
 * mvn -Pmin -pl jacop-core test -Dtest=ConsistencyChecker -Dconsistency.cases=XmulYeqZ,GCC -Dconsistency.instances=5000
 * </pre>
 *
 * <p>Each case prints the level reached, the node count and the first counterexample of the next
 * level, and fails if it falls below the level recorded in {@link #cases()} or prunes wrongly. To
 * check another propagator, add a {@link Case} with a generator of small random instances and the
 * relation as a Java predicate on complete assignments.
 */
class ConsistencyChecker {

  /** Consistency levels from the weakest to the strongest. */
  enum Level {
    NONE,
    BOUNDS_R,
    BOUNDS_Z,
    BOUNDS_D,
    DOMAIN
  }

  /** Box sizes above this are not enumerated; the node is skipped. */
  private static final long MAX_BOX = 200_000;

  /** Random instances per case, from -Dconsistency.instances. */
  private static final int INSTANCES = Integer.getInteger("consistency.instances", 1000);

  /** Comma-separated parts of case names to run, from -Dconsistency.cases; all cases if unset. */
  private static final String CASES = System.getProperty("consistency.cases", "");

  private static final int DIVES = 3;

  /**
   * Whether vars[i] = value has a support with the other variables anywhere in the real box lo..hi.
   */
  interface RealSupport {
    boolean test(int i, int value, int[] lo, int[] hi);
  }

  /**
   * A constraint over vars and the relation it must enforce, checked on complete assignments, with
   * an optional check of its real relaxation.
   */
  record Model(Object constraint, Predicate<int[]> relation, IntVar[] vars, RealSupport real) {

    Model(Object constraint, Predicate<int[]> relation, IntVar[] vars) {
      this(constraint, relation, vars, null);
    }

    @SuppressWarnings("unchecked")
    void post(Store store) {
      if (constraint instanceof Constraint c) {
        store.impose(c);
      } else {
        store.imposeDecomposition((DecomposedConstraint<Constraint>) constraint);
      }
    }
  }

  /**
   * A propagator, the strongest level it was seen to reach on every node, and a generator of small
   * random instances. A propagator that becomes stronger should have its level raised here.
   */
  record Case(String name, Level reaches, BiFunction<Store, Random, Model> generator) {}

  /** What the random search found for one propagator. */
  static final class Result {
    final String name;
    int nodes;
    int skipped;
    boolean realChecked = true;

    /** Nodes where a bound has no support but running the constraint again would prune more. */
    int notFixpoint;

    final List<String> errors = new ArrayList<>();
    final Map<Level, Integer> violations = new EnumMap<>(Level.class);
    final Map<Level, String> examples = new EnumMap<>(Level.class);

    Result(String name) {
      this.name = name;
    }

    void violation(Level level, String example) {
      violations.merge(level, 1, Integer::sum);
      examples.putIfAbsent(level, example);
    }

    /** The strongest level held at every checked node. */
    Level level() {
      Level reached = Level.NONE;
      for (Level l : Level.values()) {
        if (l != Level.NONE) {
          if (violations.containsKey(l)) {
            break;
          }
          reached = l;
        }
      }
      // bounds(R) holds trivially when it was not checked, so it says nothing on its own
      return reached == Level.BOUNDS_R && !realChecked ? Level.NONE : reached;
    }

    @Override
    public String toString() {
      StringBuilder b = new StringBuilder();
      b.append(String.format("%-28s %-8s nodes %6d", name, level(), nodes));
      if (skipped > 0) {
        b.append(" skipped ").append(skipped);
      }
      if (notFixpoint > 0) {
        b.append(" not at fixpoint ").append(notFixpoint);
      }
      if (!violations.isEmpty()) {
        // nodes that miss each level, to compare propagators that reach none on every node
        b.append(" missing");
        violations.forEach((l, count) -> b.append(' ').append(l).append('=').append(count));
      }
      for (Level l : Level.values()) {
        if (violations.containsKey(l)) {
          b.append(
              String.format(
                  "%n    not %s at %d nodes, e.g. %s", l, violations.get(l), examples.get(l)));
          break;
        }
      }
      errors.forEach(e -> b.append("\n    ERROR ").append(e));
      return b.toString();
    }
  }

  static Result check(Case c, int instances, long seed) {
    Result result = new Result(c.name());
    Random random = new Random(seed);
    for (int run = 0; run < instances && result.errors.size() < 5; run++) {
      Store store = new Store();
      Model m = c.generator().apply(store, random);
      String instance = c.name() + " run " + run + " " + domainsOf(m.vars());
      result.realChecked &= m.real() != null;
      List<int[]> before = solutions(m);
      m.post(store);
      boolean consistent = propagate(store, result, instance);
      checkNode(result, instance, store, m, before, consistent);
      if (!consistent) {
        continue;
      }
      int root = store.level;
      for (int dive = 0; dive < DIVES; dive++) {
        StringBuilder path = new StringBuilder(instance).append(" then");
        while (true) {
          List<IntVar> free = Arrays.stream(m.vars()).filter(v -> !v.singleton()).toList();
          if (free.isEmpty()) {
            break;
          }
          store.setLevel(store.level + 1);
          path.append(' ').append(decide(store, free.get(random.nextInt(free.size())), random));
          before = solutions(m);
          String atNode = path + " gives " + domainsOf(m.vars());
          consistent = propagate(store, result, atNode);
          checkNode(result, atNode, store, m, before, consistent);
          if (!consistent) {
            break;
          }
        }
        while (store.level > root) {
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
        }
      }
    }
    return result;
  }

  private static boolean propagate(Store store, Result result, String instance) {
    try {
      return store.consistency();
    } catch (RuntimeException e) {
      result.errors.add(instance + " threw " + e);
      return false;
    }
  }

  /** Applies a random decision x = v, x != v, x <= v or x >= v that keeps the domain non-empty. */
  private static String decide(Store store, IntVar x, Random random) {
    int[] values = valuesOf(x);
    int i = random.nextInt(values.length);
    switch (random.nextInt(4)) {
      case 0 -> {
        x.domain.in(store.level, x, values[i], values[i]);
        return x.id() + "=" + values[i];
      }
      case 1 -> {
        x.domain.inComplement(store.level, x, values[i]);
        return x.id() + "!=" + values[i];
      }
      case 2 -> {
        int v = values[Math.min(i, values.length - 2)];
        x.domain.in(store.level, x, x.min(), v);
        return x.id() + "<=" + v;
      }
      default -> {
        int v = values[Math.max(i, 1)];
        x.domain.in(store.level, x, v, x.max());
        return x.id() + ">=" + v;
      }
    }
  }

  private static void checkNode(
      Result result, String where, Store store, Model m, List<int[]> before, boolean consistent) {
    IntVar[] vars = m.vars();
    if (!consistent) {
      if (before != null && !before.isEmpty()) {
        result.errors.add(
            where + ": failed, but " + Arrays.toString(before.get(0)) + " is a solution");
      }
      return;
    }
    result.nodes++;
    if (before != null) {
      for (int[] s : before) {
        if (!inDomains(vars, s)) {
          result.errors.add(where + ": removed solution " + Arrays.toString(s));
          return;
        }
      }
    }
    int n = vars.length;
    int[] lo = new int[n];
    int[] hi = new int[n];
    for (int i = 0; i < n; i++) {
      lo[i] = vars[i].min();
      hi[i] = vars[i].max();
    }
    if (boxSize(lo, hi) > MAX_BOX) {
      result.skipped++;
      return;
    }
    // supportedZ[i][k]: value lo[i] + k of vars[i] has a support in the intervals; supportedD in
    // the domains
    boolean[][] supportedZ = new boolean[n][];
    boolean[][] supportedD = new boolean[n][];
    for (int i = 0; i < n; i++) {
      supportedZ[i] = new boolean[hi[i] - lo[i] + 1];
      supportedD[i] = new boolean[hi[i] - lo[i] + 1];
    }
    forEachTuple(
        lo,
        hi,
        t -> {
          if (m.relation().test(t)) {
            boolean inDomains = inDomains(vars, t);
            for (int i = 0; i < n; i++) {
              supportedZ[i][t[i] - lo[i]] = true;
              supportedD[i][t[i] - lo[i]] |= inDomains;
            }
          }
        });
    boolean boundsSupported = true;
    for (int i = 0; i < n; i++) {
      int top = hi[i] - lo[i];
      String bounds = where + ": " + vars[i].id() + " in " + vars[i].dom();
      if (m.real() != null
          && !(m.real().test(i, lo[i], lo, hi) && m.real().test(i, hi[i], lo, hi))) {
        result.violation(Level.BOUNDS_R, bounds + " has a bound without support over the reals");
      }
      boundsSupported &= supportedD[i][0] && supportedD[i][top];
      if (!supportedZ[i][0] || !supportedZ[i][top]) {
        result.violation(Level.BOUNDS_Z, bounds + " has a bound without support in the intervals");
      }
      if (!supportedD[i][0] || !supportedD[i][top]) {
        result.violation(Level.BOUNDS_D, bounds + " has a bound without support in the domains");
      }
      for (int k = 0; k <= top; k++) {
        if (vars[i].domain.contains(lo[i] + k) && !supportedD[i][k]) {
          result.violation(Level.DOMAIN, bounds + " has value " + (lo[i] + k) + " without support");
          break;
        }
      }
    }
    if (!boundsSupported && m.constraint() instanceof Constraint c) {
      String propagated = domainsOf(vars);
      if (!rerun(store, c, vars).equals(propagated)) {
        result.notFixpoint++;
      }
    }
  }

  /** The domains after running the constraint once more at a new level, which is then undone. */
  private static String rerun(Store store, Constraint c, IntVar[] vars) {
    int level = store.level;
    store.setLevel(level + 1);
    String result;
    try {
      c.consistency(store);
      result = domainsOf(vars);
    } catch (FailException e) {
      result = "FAIL";
    }
    store.removeLevel(level + 1);
    store.setLevel(level);
    return result;
  }

  /** All solutions inside the current domains, or null if there are too many tuples to try. */
  private static List<int[]> solutions(Model m) {
    IntVar[] vars = m.vars();
    int[] lo = Arrays.stream(vars).mapToInt(IntVar::min).toArray();
    int[] hi = Arrays.stream(vars).mapToInt(IntVar::max).toArray();
    if (boxSize(lo, hi) > MAX_BOX) {
      return null;
    }
    List<int[]> result = new ArrayList<>();
    forEachTuple(
        lo,
        hi,
        t -> {
          if (inDomains(vars, t) && m.relation().test(t)) {
            result.add(t.clone());
          }
        });
    return result;
  }

  private static long boxSize(int[] lo, int[] hi) {
    long size = 1;
    for (int i = 0; i < lo.length && size <= MAX_BOX; i++) {
      size *= hi[i] - lo[i] + 1;
    }
    return size;
  }

  private static void forEachTuple(int[] lo, int[] hi, java.util.function.Consumer<int[]> action) {
    int[] t = lo.clone();
    while (true) {
      action.accept(t);
      int k = 0;
      while (k < t.length && t[k] == hi[k]) {
        t[k] = lo[k];
        k++;
      }
      if (k == t.length) {
        return;
      }
      t[k]++;
    }
  }

  private static boolean inDomains(IntVar[] vars, int[] t) {
    for (int i = 0; i < vars.length; i++) {
      if (!vars[i].domain.contains(t[i])) {
        return false;
      }
    }
    return true;
  }

  private static int[] valuesOf(IntVar v) {
    return IntStream.rangeClosed(v.min(), v.max()).filter(v.domain::contains).toArray();
  }

  private static String domainsOf(IntVar[] vars) {
    return Arrays.stream(vars).map(IntVar::toString).collect(Collectors.joining(", ", "[", "]"));
  }

  /** A variable over a random non-empty subset of lo..hi, with holes about a fifth of the time. */
  private static IntVar var(Store store, String name, int lo, int hi, Random random) {
    IntVar v = new IntVar(store, name);
    for (int k = lo; k <= hi; k++) {
      if (random.nextInt(5) > 0) {
        v.addDom(k, k);
      }
    }
    if (v.getSize() == 0) {
      v.addDom(lo, lo);
    }
    return v;
  }

  /** A variable over lo..hi with a random sub-interval, so without holes. */
  private static IntVar interval(Store store, String name, int lo, int hi, Random random) {
    int a = lo + random.nextInt(hi - lo + 1);
    int b = lo + random.nextInt(hi - lo + 1);
    return new IntVar(store, name, Math.min(a, b), Math.max(a, b));
  }

  private static IntVar[] vars(Store store, String prefix, int n, int lo, int hi, Random random) {
    return IntStream.range(0, n)
        .mapToObj(i -> var(store, prefix + i, lo, hi, random))
        .toArray(IntVar[]::new);
  }

  private static IntVar[] concat(IntVar[]... parts) {
    return Arrays.stream(parts).flatMap(Arrays::stream).toArray(IntVar[]::new);
  }

  private static final String[] RELATIONS = {"==", "<=", ">=", "<", ">", "!="};

  private static boolean holds(String rel, long lhs, long rhs) {
    return switch (rel) {
      case "==" -> lhs == rhs;
      case "<=" -> lhs <= rhs;
      case ">=" -> lhs >= rhs;
      case "<" -> lhs < rhs;
      case ">" -> lhs > rhs;
      default -> lhs != rhs;
    };
  }

  /** sum(w[i] * x[i]) rel s, with s the last variable. */
  private static Model linear(Store store, Random random, int[] w, String rel, boolean dom) {
    IntVar[] x = vars(store, "x", w.length, -3, 3, random);
    IntVar s = var(store, "s", -8, 8, random);
    Constraint c = dom ? new LinearIntDom(x, w, rel, s) : new LinearInt(x, w, rel, s);
    return new Model(
        c,
        t ->
            holds(
                rel,
                IntStream.range(0, w.length).mapToLong(i -> (long) w[i] * t[i]).sum(),
                t[w.length]),
        concat(x, new IntVar[] {s}),
        linearOverReals(w, rel));
  }

  /** sum(w[i] * b[i]) rel s over 0/1 variables b, with s a variable or a constant. */
  private static Model linearBool(Store store, Random random, String rel, boolean constant) {
    int n = 3 + random.nextInt(4);
    int[] w = new int[n];
    IntVar[] b = new IntVar[n];
    for (int i = 0; i < n; i++) {
      w[i] = (1 + random.nextInt(5)) * (random.nextBoolean() ? 1 : -1);
      b[i] =
          random.nextBoolean() ? new BooleanVar(store, "b" + i) : var(store, "b" + i, 0, 1, random);
    }
    if (constant) {
      int c = random.nextInt(13) - 6;
      return new Model(
          new LinearBool(b, w, rel, c),
          t -> holds(rel, IntStream.range(0, n).mapToLong(i -> (long) w[i] * t[i]).sum(), c),
          b,
          linearOverReals(w, c, rel));
    }
    IntVar s = var(store, "s", -8, 12, random);
    return new Model(
        new LinearBool(b, w, rel, s),
        t -> holds(rel, IntStream.range(0, n).mapToLong(i -> (long) w[i] * t[i]).sum(), t[n]),
        concat(b, new IntVar[] {s}),
        linearOverReals(w, rel));
  }

  /** Support of sum(w[i] * x[i]) rel s over the reals, with s the last variable. */
  private static RealSupport linearOverReals(int[] w, String rel) {
    int[] a = Arrays.copyOf(w, w.length + 1);
    a[w.length] = -1;
    return linearOverReals(a, 0, rel);
  }

  /** Support of sum(a[i] * y[i]) rel c over the reals. */
  private static RealSupport linearOverReals(int[] a, long c, String rel) {
    return (j, value, lo, hi) -> {
      // range of sum(a[k] * y[k]) - c with y[j] = value and the others real in lo..hi
      long min = (long) a[j] * value - c;
      long max = min;
      for (int k = 0; k < a.length; k++) {
        if (k != j) {
          min += Math.min((long) a[k] * lo[k], (long) a[k] * hi[k]);
          max += Math.max((long) a[k] * lo[k], (long) a[k] * hi[k]);
        }
      }
      return switch (rel) {
        case "==" -> min <= 0 && 0 <= max;
        case "<=" -> min <= 0;
        case ">=" -> max >= 0;
        case "<" -> min < 0;
        case ">" -> max > 0;
        default -> min != 0 || max != 0;
      };
    };
  }

  private static int[] weights(Random random, int n, int max) {
    return IntStream.range(0, n)
        .map(i -> (1 + random.nextInt(max)) * (random.nextBoolean() ? 1 : -1))
        .toArray();
  }

  private static Model xyz(
      Store store,
      Random random,
      int[] range,
      TriFunction<IntVar, IntVar, IntVar, Constraint> constraint,
      Predicate<int[]> relation) {
    IntVar x = var(store, "x", range[0], range[1], random);
    IntVar y = var(store, "y", range[2], range[3], random);
    IntVar z = var(store, "z", range[4], range[5], random);
    return new Model(constraint.apply(x, y, z), relation, new IntVar[] {x, y, z});
  }

  /** Support of x * y = z over the reals. */
  private static boolean productOverReals(int i, int value, int[] lo, int[] hi) {
    if (i == 2) {
      long[] p = {
        (long) lo[0] * lo[1], (long) lo[0] * hi[1], (long) hi[0] * lo[1], (long) hi[0] * hi[1]
      };
      return Arrays.stream(p).min().getAsLong() <= value
          && value <= Arrays.stream(p).max().getAsLong();
    }
    // value * [lo, hi] of the other factor must meet the interval of z
    int other = 1 - i;
    long a = (long) value * lo[other];
    long b = (long) value * hi[other];
    return Math.min(a, b) <= hi[2] && lo[2] <= Math.max(a, b);
  }

  interface TriFunction<A, B, C, R> {
    R apply(A a, B b, C c);
  }

  /** Element: value = list[index - 1]. */
  private static Model element(Store store, Random random, boolean variableList, boolean fast) {
    int n = 2 + random.nextInt(3);
    IntVar index = var(store, "i", 0, n + 1, random);
    IntVar value = var(store, "v", 0, 5, random);
    if (variableList) {
      IntVar[] list = vars(store, "l", n, 0, 5, random);
      Constraint c =
          fast
              ? new ElementVariableFast(index, list, value)
              : new ElementVariable(index, list, value);
      return new Model(
          c,
          t -> t[0] >= 1 && t[0] <= n && t[1] == t[1 + t[0]],
          concat(new IntVar[] {index, value}, list));
    }
    int[] list = IntStream.range(0, n).map(i -> random.nextInt(6)).toArray();
    Constraint c =
        fast
            ? new ElementIntegerFast(index, list, value)
            : new ElementInteger(index, list, value, 0);
    return new Model(
        c, t -> t[0] >= 1 && t[0] <= n && t[1] == list[t[0] - 1], new IntVar[] {index, value});
  }

  /** GCC with counters for every value from the smallest to the largest value of x. */
  private static Model gcc(Store store, Random random) {
    int n = 3 + random.nextInt(2);
    IntVar[] x = vars(store, "x", n, 0, 2 + random.nextInt(2), random);
    int lo = Arrays.stream(x).mapToInt(IntVar::min).min().getAsInt();
    int hi = Arrays.stream(x).mapToInt(IntVar::max).max().getAsInt();
    IntVar[] c = vars(store, "c", hi - lo + 1, 0, n, random);
    return new Model(
        new GCC(x, c),
        t -> {
          for (int k = 0; k < c.length; k++) {
            int value = lo + k;
            if (IntStream.range(0, n).filter(i -> t[i] == value).count() != t[n + k]) {
              return false;
            }
          }
          return true;
        },
        concat(x, c));
  }

  /** Cumulative over three tasks; durations and resource uses are positive. */
  private static Model cumulative(Store store, Random random, boolean basic) {
    int n = 3;
    IntVar[] s = vars(store, "s", n, 0, 3, random);
    IntVar[] d =
        IntStream.range(0, n)
            .mapToObj(i -> interval(store, "d" + i, 1, 2, random))
            .toArray(IntVar[]::new);
    IntVar[] r =
        IntStream.range(0, n)
            .mapToObj(i -> interval(store, "r" + i, 1, 2, random))
            .toArray(IntVar[]::new);
    IntVar limit = var(store, "b", 1, 3, random);
    Constraint c = basic ? new CumulativeBasic(s, d, r, limit) : new Cumulative(s, d, r, limit);
    return new Model(
        c,
        t -> {
          for (int time = 0; time <= 5; time++) {
            int load = 0;
            for (int i = 0; i < n; i++) {
              if (t[i] <= time && time < t[i] + t[n + i]) {
                load += t[2 * n + i];
              }
            }
            if (load > t[3 * n]) {
              return false;
            }
          }
          return true;
        },
        concat(s, d, r, new IntVar[] {limit}));
  }

  private static Model alldiff(Store store, Random random, boolean gac) {
    int n = 3 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 0, n, random);
    return new Model(
        gac ? new Alldistinct(x) : new Alldiff(x),
        t -> Arrays.stream(t).distinct().count() == t.length,
        x);
  }

  /**
   * Member over a list that may repeat variables and contain the element itself, plain, negated or
   * reified.
   */
  private static Model member(Store store, Random random, String form) {
    int n = 2 + random.nextInt(3);
    IntVar[] v = vars(store, "v", n, 0, 4, random);
    int e = n - 1;
    int[] picks = IntStream.range(0, 1 + random.nextInt(4)).map(i -> random.nextInt(n)).toArray();
    IntVar[] list = Arrays.stream(picks).mapToObj(i -> v[i]).toArray(IntVar[]::new);
    Member member = new Member(list, v[e]);
    IntVar b = new IntVar(store, "b", 0, 1);
    Predicate<int[]> holds = t -> Arrays.stream(picks).anyMatch(i -> t[i] == t[e]);
    return switch (form) {
      case "reified" ->
          new Model(
              new Reified(member, b),
              t -> holds.test(t) == (t[n] == 1),
              concat(v, new IntVar[] {b}));
      case "not" -> new Model(new Not(member), holds.negate(), v);
      default -> new Model(member, holds, v);
    };
  }

  private static Model minMax(Store store, Random random, boolean min) {
    int n = 2 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, -3, 3, random);
    IntVar m = var(store, "m", -3, 3, random);
    return new Model(
        min ? new Min(x, m) : new Max(x, m),
        t -> {
          int[] list = Arrays.copyOf(t, n);
          return t[n] == (min ? Arrays.stream(list).min() : Arrays.stream(list).max()).getAsInt();
        },
        concat(x, new IntVar[] {m}));
  }

  static List<Case> cases() {
    int[] small = {-4, 4, -4, 4, -8, 8};
    return List.of(
        new Case(
            "XplusYeqZ",
            Level.BOUNDS_Z,
            (s, r) -> xyz(s, r, small, XplusYeqZ::new, t -> t[0] + t[1] == t[2])),
        new Case(
            "XeqY",
            Level.DOMAIN,
            (s, r) -> {
              IntVar x = var(s, "x", -6, 6, r);
              IntVar y = var(s, "y", -6, 6, r);
              return new Model(new XeqY(x, y), t -> t[0] == t[1], new IntVar[] {x, y});
            }),
        new Case(
            "XplusCeqZ",
            Level.DOMAIN,
            (s, r) -> {
              IntVar x = var(s, "x", -6, 6, r);
              IntVar z = var(s, "z", -4, 8, r);
              return new Model(new XplusCeqZ(x, 2, z), t -> t[0] + 2 == t[1], new IntVar[] {x, z});
            }),
        new Case(
            "XplusYeqC",
            Level.DOMAIN,
            (s, r) -> {
              IntVar x = var(s, "x", -6, 6, r);
              IntVar y = var(s, "y", -4, 8, r);
              return new Model(new XplusYeqC(x, y, 2), t -> t[0] + t[1] == 2, new IntVar[] {x, y});
            }),
        new Case(
            "XplusYlteqZ",
            Level.DOMAIN,
            (s, r) -> xyz(s, r, small, XplusYlteqZ::new, t -> t[0] + t[1] <= t[2])),
        // bounds(Z) would also need the bounds of z to be products, e.g. no 11 from x, y in -4..4
        new Case(
            "XmulYeqZ",
            Level.BOUNDS_R,
            (s, r) -> {
              Model m =
                  xyz(
                      s,
                      r,
                      new int[] {-4, 4, -4, 4, -12, 12},
                      XmulYeqZ::new,
                      t -> t[0] * t[1] == t[2]);
              return new Model(
                  m.constraint(), m.relation(), m.vars(), ConsistencyChecker::productOverReals);
            }),
        new Case(
            "XmulCeqZ",
            Level.BOUNDS_D,
            (s, r) -> {
              int c = r.nextInt(7) - 3;
              IntVar x = var(s, "x", -4, 4, r);
              IntVar z = var(s, "z", -12, 12, r);
              return new Model(new XmulCeqZ(x, c, z), t -> t[0] * c == t[1], new IntVar[] {x, z});
            }),
        // no pruning of y while the interval of z contains 0
        new Case(
            "XdivYeqZ",
            Level.NONE,
            (s, r) ->
                xyz(
                    s,
                    r,
                    new int[] {-9, 9, -3, 3, -9, 9},
                    XdivYeqZ::new,
                    t -> t[1] != 0 && t[0] / t[1] == t[2])),
        // e.g. x keeps its positive values when z < 0
        new Case(
            "XmodYeqZ",
            Level.NONE,
            (s, r) ->
                xyz(
                    s,
                    r,
                    new int[] {-9, 9, -4, 4, -4, 4},
                    XmodYeqZ::new,
                    t -> t[1] != 0 && t[0] % t[1] == t[2])),
        new Case(
            "AbsXeqY (bounds)",
            Level.BOUNDS_Z,
            (s, r) -> {
              IntVar x = var(s, "x", -5, 5, r);
              IntVar y = var(s, "y", -2, 6, r);
              return new Model(
                  new AbsXeqY(x, y, false), t -> Math.abs(t[0]) == t[1], new IntVar[] {x, y});
            }),
        new Case(
            "Distance",
            Level.BOUNDS_Z,
            (s, r) ->
                xyz(
                    s,
                    r,
                    new int[] {-4, 4, -4, 4, -2, 8},
                    Distance::new,
                    t -> Math.abs(t[0] - t[1]) == t[2])),
        new Case("Min", Level.BOUNDS_Z, (s, r) -> minMax(s, r, true)),
        new Case("Max", Level.BOUNDS_Z, (s, r) -> minMax(s, r, false)),
        new Case(
            "SumInt",
            Level.BOUNDS_Z,
            (s, r) -> {
              int n = 2 + r.nextInt(3);
              String rel = RELATIONS[r.nextInt(RELATIONS.length)];
              IntVar[] x = vars(s, "x", n, -3, 3, r);
              IntVar sum = var(s, "s", -8, 8, r);
              return new Model(
                  new SumInt(x, rel, sum),
                  t -> holds(rel, Arrays.stream(t, 0, n).sum(), t[n]),
                  concat(x, new IntVar[] {sum}));
            }),
        new Case(
            "LinearInt unit weights",
            Level.BOUNDS_Z,
            (s, r) ->
                linear(
                    s,
                    r,
                    weights(r, 2 + r.nextInt(3), 1),
                    RELATIONS[r.nextInt(RELATIONS.length)],
                    false)),
        // bounds(Z) is NP-hard with non-unit weights
        new Case(
            "LinearInt",
            Level.BOUNDS_R,
            (s, r) ->
                linear(
                    s,
                    r,
                    weights(r, 2 + r.nextInt(3), 3),
                    RELATIONS[r.nextInt(RELATIONS.length)],
                    false)),
        // != is woken only when a variable is fixed, and must still prune every unsupported value
        new Case(
            "LinearInt !=",
            Level.DOMAIN,
            (s, r) -> linear(s, r, weights(r, 2 + r.nextInt(3), 3), "!=", false)),
        // bounds(Z) is NP-hard with non-unit weights, as for LinearInt
        new Case(
            "LinearBool",
            Level.BOUNDS_R,
            (s, r) -> linearBool(s, r, new String[] {"==", "<=", ">="}[r.nextInt(3)], false)),
        new Case(
            "LinearBool constant",
            Level.BOUNDS_R,
            (s, r) -> linearBool(s, r, new String[] {"==", "<=", ">="}[r.nextInt(3)], true)),
        new Case(
            "XplusCneqZ",
            Level.DOMAIN,
            (s, r) -> {
              int c = r.nextInt(7) - 3;
              IntVar x = var(s, "x", -4, 4, r);
              IntVar z = var(s, "z", -4, 4, r);
              return new Model(new XplusCneqZ(x, c, z), t -> t[0] + c != t[1], new IntVar[] {x, z});
            }),
        new Case(
            "XplusClteqZImplied",
            Level.DOMAIN,
            (s, r) -> {
              int c = r.nextInt(7) - 3;
              IntVar b = r.nextBoolean() ? new BooleanVar(s, "b") : var(s, "b", 0, 1, r);
              IntVar x = var(s, "x", -4, 4, r);
              IntVar z = var(s, "z", -4, 4, r);
              return new Model(
                  new XplusClteqZImplied(b, x, c, z),
                  t -> t[0] == 0 || t[1] + c <= t[2],
                  new IntVar[] {b, x, z});
            }),
        new Case(
            "LinearIntDom",
            Level.DOMAIN,
            (s, r) -> linear(s, r, weights(r, 2 + r.nextInt(3), 3), "==", true)),
        new Case("Alldiff", Level.BOUNDS_Z, (s, r) -> alldiff(s, r, false)),
        new Case("Alldistinct", Level.DOMAIN, (s, r) -> alldiff(s, r, true)),
        new Case("Member", Level.DOMAIN, (s, r) -> member(s, r, "plain")),
        new Case("ReifiedMember", Level.DOMAIN, (s, r) -> member(s, r, "reified")),
        new Case("NotMember", Level.DOMAIN, (s, r) -> member(s, r, "not")),
        new Case("GCC", Level.BOUNDS_Z, ConsistencyChecker::gcc),
        new Case("ElementInteger", Level.DOMAIN, (s, r) -> element(s, r, false, false)),
        new Case("ElementIntegerFast", Level.BOUNDS_D, (s, r) -> element(s, r, false, true)),
        // rarely: index values whose list variable cannot reach value stay until the constraint
        // runs again
        new Case("ElementVariable", Level.NONE, (s, r) -> element(s, r, true, false)),
        new Case("ElementVariableFast", Level.BOUNDS_Z, (s, r) -> element(s, r, true, true)),
        new Case(
            "Count",
            Level.DOMAIN,
            (s, r) -> {
              int n = 2 + r.nextInt(4);
              int value = r.nextInt(3);
              IntVar[] x = vars(s, "x", n, 0, 2, r);
              IntVar c = var(s, "c", 0, n, r);
              return new Model(
                  new Count(x, c, value),
                  t -> Arrays.stream(t, 0, n).filter(v -> v == value).count() == t[n],
                  concat(x, new IntVar[] {c}));
            }),
        new Case(
            "CountBounds",
            Level.DOMAIN,
            (s, r) -> {
              int n = 2 + r.nextInt(4);
              int value = r.nextInt(3);
              int lb = r.nextInt(n + 1);
              int ub = lb + r.nextInt(n + 1 - lb);
              IntVar[] x = vars(s, "x", n, 0, 2, r);
              return new Model(
                  new CountBounds(x, value, lb, ub),
                  t -> {
                    long c = Arrays.stream(t).filter(v -> v == value).count();
                    return lb <= c && c <= ub;
                  },
                  x);
            }),
        new Case(
            "CountVar",
            Level.DOMAIN,
            (s, r) -> {
              int n = 2 + r.nextInt(4);
              IntVar[] x = vars(s, "x", n, 0, 2, r);
              IntVar c = var(s, "c", 0, n, r);
              IntVar y = var(s, "y", 0, 2, r);
              return new Model(
                  new CountVar(x, c, y),
                  t -> Arrays.stream(t, 0, n).filter(v -> v == t[n + 1]).count() == t[n],
                  concat(x, new IntVar[] {c, y}));
            }),
        new Case(
            "Among",
            Level.DOMAIN,
            (s, r) -> {
              int n = 2 + r.nextInt(4);
              int a = r.nextInt(3);
              int b = a + r.nextInt(2);
              IntVar[] x = vars(s, "x", n, 0, 3, r);
              IntVar c = var(s, "c", 0, n, r);
              return new Model(
                  new Among(x, new IntervalDomain(a, b), c),
                  t -> Arrays.stream(t, 0, n).filter(v -> a <= v && v <= b).count() == t[n],
                  concat(x, new IntVar[] {c}));
            }),
        // bounds on the intervals for count.max() (hitting sets) and domain pruning from the
        // matching for count.min(); a lower bound on the domains themselves is NP-hard
        new Case(
            "Values",
            Level.BOUNDS_Z,
            (s, r) -> {
              int n = 2 + r.nextInt(3);
              IntVar[] x = vars(s, "x", n, 0, 3, r);
              IntVar c = var(s, "c", 0, n + 1, r);
              return new Model(
                  new Values(x, c),
                  t -> Arrays.stream(t, 0, n).distinct().count() == t[n],
                  concat(x, new IntVar[] {c}));
            }),
        new Case(
            "Increasing",
            Level.DOMAIN,
            (s, r) -> {
              boolean strict = r.nextBoolean();
              IntVar[] x = vars(s, "x", 2 + r.nextInt(3), 0, 4, r);
              return new Model(
                  new Increasing(x, strict),
                  t ->
                      IntStream.range(1, t.length)
                          .allMatch(i -> strict ? t[i - 1] < t[i] : t[i - 1] <= t[i]),
                  x);
            }),
        new Case(
            "Lex",
            Level.DOMAIN,
            (s, r) -> {
              boolean lt = r.nextBoolean();
              int n = 2 + r.nextInt(2);
              IntVar[] a = vars(s, "a", n, 0, 2, r);
              IntVar[] b = vars(s, "b", n, 0, 2, r);
              return new Model(
                  new Lex(new IntVar[][] {a, b}, lt),
                  t -> {
                    int cmp =
                        Arrays.compare(
                            Arrays.copyOfRange(t, 0, n), Arrays.copyOfRange(t, n, 2 * n));
                    return lt ? cmp < 0 : cmp <= 0;
                  },
                  concat(a, b));
            }),
        // bounds(Z) is NP-hard; the limit is not raised to the largest resource use either
        new Case("CumulativeBasic", Level.NONE, (s, r) -> cumulative(s, r, true)),
        new Case("Cumulative", Level.NONE, (s, r) -> cumulative(s, r, false)),
        // Geost sweeps for the first and last feasible origin, so it reaches no level on all
        // nodes; the counts of nodes at each level compare its strength with Diffn and Diff2
        new Case("GeostRect2d", Level.NONE, (s, r) -> geost(s, r, Family.RECT2D, null)),
        new Case(
            "Diffn(rect2d)", Level.NONE, (s, r) -> geost(s, r, Family.RECT2D, Rect.DIFFN_STRICT)),
        new Case("Diff2(rect2d)", Level.NONE, (s, r) -> geost(s, r, Family.RECT2D, Rect.DIFF2)),
        new Case("GeostPoly2d", Level.NONE, (s, r) -> geost(s, r, Family.POLY2D, null)),
        new Case("GeostArea", Level.NONE, (s, r) -> geost(s, r, Family.AREA, null)),
        new Case("GeostTime", Level.NONE, (s, r) -> geost(s, r, Family.TIME, null)),
        new Case("GeostSubdims", Level.NONE, (s, r) -> geost(s, r, Family.SUBDIMS, null)));
  }

  /**
   * A random instance of a Geost generator family, posted as Geost or as one of the rectangle
   * constraints over the same variables.
   */
  private static Model geost(Store store, Random random, Family family, Rect rect) {
    GeostInstance g = new GeostInstanceGenerator(random.nextLong()).generate(family, "consistency");
    while (rect != null && !(g.diffnExpressible() && g.sameBoxCounts())) {
      g = new GeostInstanceGenerator(random.nextLong()).generate(family, "consistency");
    }
    // the checker imposes the constraint itself
    GeostInstance.Posted p =
        rect == null ? g.postGeost(store, false, false) : g.postRectangles(store, rect, false);
    return new Model(p.constraint(), g::check, p.vars());
  }

  @TestFactory
  Stream<DynamicTest> propagatorsReachTheirConsistency() {
    List<String> wanted = Arrays.stream(CASES.split(",")).filter(w -> !w.isBlank()).toList();
    return cases().stream()
        .filter(c -> wanted.isEmpty() || wanted.stream().anyMatch(w -> c.name().contains(w.trim())))
        .map(
            c ->
                DynamicTest.dynamicTest(
                    c.name(),
                    () -> {
                      Result result = check(c, INSTANCES, c.name().hashCode());
                      System.out.println(result);
                      assertThat(result.errors).as(result.toString()).isEmpty();
                      assertThat(result.level())
                          .as(result.toString())
                          .isGreaterThanOrEqualTo(c.reaches());
                    }));
  }
}
