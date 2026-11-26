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
import org.jacop.constraints.AllDifferentLists;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.AlldiffSum;
import org.jacop.constraints.AlldifferentExcept;
import org.jacop.constraints.AlldifferentExceptZero;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Among;
import org.jacop.constraints.AmongSeq;
import org.jacop.constraints.ArgMax;
import org.jacop.constraints.ArgMaxMonotone;
import org.jacop.constraints.ArgMin;
import org.jacop.constraints.ConditionalSelect;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ConvexAllocation;
import org.jacop.constraints.ConvexCost;
import org.jacop.constraints.Count;
import org.jacop.constraints.CountBounds;
import org.jacop.constraints.CountVar;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.DifferenceCycles;
import org.jacop.constraints.Distance;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.ElementVariable;
import org.jacop.constraints.ElementVariableFast;
import org.jacop.constraints.GCC;
import org.jacop.constraints.Increasing;
import org.jacop.constraints.IncreasingNValue;
import org.jacop.constraints.IncreasingSum;
import org.jacop.constraints.InterDistance;
import org.jacop.constraints.LateCount;
import org.jacop.constraints.Lex;
import org.jacop.constraints.LexChain;
import org.jacop.constraints.LexOrder;
import org.jacop.constraints.LinearBool;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.Max;
import org.jacop.constraints.Member;
import org.jacop.constraints.Min;
import org.jacop.constraints.MultiInterDistance;
import org.jacop.constraints.Not;
import org.jacop.constraints.OverlappingAlldiff;
import org.jacop.constraints.PrecedenceCost;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Sort;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.Values;
import org.jacop.constraints.WeightedCompletion;
import org.jacop.constraints.XdivYeqZ;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XexpYeqZ;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmodYeqZ;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusClteqZImplied;
import org.jacop.constraints.XplusCneqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.cumulative.CumulativeUnaryOptional;
import org.jacop.constraints.cumulative.EnergyPrecedence;
import org.jacop.constraints.cumulative.HornFlow;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
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
   * Repeated-variable mode, from -Dconsistency.repeated=true: the variable helpers of the
   * generators return, about a third of the time, a variable created earlier for the same instance
   * whose domain fits the requested range, so a constraint sees one variable at several positions
   * of its scope.
   */
  static final boolean REPEATED = Boolean.getBoolean("consistency.repeated");

  /** The variables created so far for the current instance, while repeated-variable mode is on. */
  private static List<IntVar> pool;

  /** The random generator of the current instance, to pick a repeated variable. */
  private static Random poolRandom;

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

    /** For each position, the first position holding the same variable. */
    int[] alias() {
      int[] first = new int[vars.length];
      for (int i = 0; i < vars.length; i++) {
        first[i] = i;
        for (int j = 0; j < i; j++) {
          if (vars[j] == vars[i]) {
            first[i] = j;
            break;
          }
        }
      }
      return first;
    }

    /** Whether some variable appears at more than one position. */
    boolean repeats() {
      int[] first = alias();
      return IntStream.range(0, first.length).anyMatch(i -> first[i] != i);
    }

    @SuppressWarnings("unchecked")
    void post(Store store) {
      if (constraint instanceof Constraint c) {
        store.impose(c);
      } else if (constraint instanceof List<?> cs) {
        cs.forEach(c -> store.impose((Constraint) c));
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

    /** Instances whose constructor or imposition rejected the variables, in repeated mode. */
    int rejected;

    String rejectedExample;

    /** Instances with a repeated variable, in repeated mode. */
    int repeated;

    boolean realChecked = true;

    /** Nodes where a bound has no support but running the constraint again would prune more. */
    int notFixpoint;

    /** The first node that was not at fixpoint. */
    String fixpointExample;

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
      if (REPEATED) {
        b.append(" repeated ").append(repeated);
      }
      if (rejected > 0) {
        b.append(" rejected ").append(rejected).append(" (").append(rejectedExample).append(')');
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
      if (fixpointExample != null) {
        b.append("\n    not at fixpoint, e.g. ").append(fixpointExample);
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
      pool = REPEATED ? new ArrayList<>() : null;
      poolRandom = random;
      Model m;
      try {
        m = c.generator().apply(store, random);
      } catch (IllegalArgumentException e) {
        if (!REPEATED) {
          throw e;
        }
        result.rejected++;
        result.rejectedExample =
            result.rejectedExample == null ? e.toString() : result.rejectedExample;
        continue;
      } finally {
        pool = null;
      }
      if (REPEATED && !m.repeats()) {
        continue;
      }
      result.repeated += REPEATED ? 1 : 0;
      String instance =
          c.name() + " run " + run + " " + domainsOf(m.vars()) + describe(m.constraint());
      result.realChecked &= m.real() != null;
      List<int[]> before = solutions(m);
      try {
        m.post(store);
      } catch (IllegalArgumentException e) {
        if (!REPEATED) {
          throw e;
        }
        result.rejected++;
        result.rejectedExample =
            result.rejectedExample == null ? e.toString() : result.rejectedExample;
        continue;
      } catch (RuntimeException e) {
        result.errors.add(instance + " impose threw " + e);
        continue;
      }
      boolean consistent = propagate(store, result, instance);
      checkNode(result, instance, store, m, before, consistent);
      if (!consistent) {
        continue;
      }
      int root = store.level;
      for (int dive = 0; dive < DIVES; dive++) {
        StringBuilder path = new StringBuilder(instance).append(" then");
        while (true) {
          List<IntVar> free =
              Arrays.stream(m.vars()).filter(v -> !v.singleton()).distinct().toList();
          if (free.isEmpty()) {
            break;
          }
          store.setLevel(store.level + 1);
          path.append(' ').append(decide(store, free.get(random.nextInt(free.size())), random));
          before = solutions(m);
          String atNode = path + " gives " + domainsOf(m.vars());
          checkSatisfiedBefore(result, path.toString(), m);
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

  /**
   * Whether satisfied() claims nothing false: when it says true, every tuple of the domains is a
   * solution. Checked after propagation and also just after a decision, before propagation, since
   * the LCG represolve and the FlatZinc component split drop a constraint that says it is satisfied
   * at whatever state they find it.
   */
  private static boolean satisfiedIsSound(
      Result result, String where, Model m, int[] lo, int[] hi, int[] first) {
    IntVar[] vars = m.vars();
    if (m.constraint() instanceof org.jacop.api.SatisfiedPresent sp) {
      boolean claimed;
      try {
        claimed = sp.satisfied();
      } catch (RuntimeException e) {
        result.errors.add(where + ": satisfied() threw " + e);
        return false;
      }
      if (claimed) {
        int[][] counter = new int[1][];
        forEachTuple(
            lo,
            hi,
            first,
            t -> {
              if (counter[0] == null && inDomains(vars, t) && !m.relation().test(t)) {
                counter[0] = t.clone();
              }
            });
        if (counter[0] != null) {
          result.errors.add(
              where
                  + ": satisfied() is true, but "
                  + Arrays.toString(counter[0])
                  + " is no solution");
          return false;
        }
      }
    }
    return true;
  }

  /** The satisfied() check on the domains a decision left, before propagation. */
  private static void checkSatisfiedBefore(Result result, String where, Model m) {
    if (m.constraint() instanceof DifferenceCycles || m.constraint() instanceof EnergyPrecedence) {
      return;
    }
    IntVar[] vars = m.vars();
    int n = vars.length;
    int[] lo = new int[n];
    int[] hi = new int[n];
    for (int i = 0; i < n; i++) {
      if (vars[i].domain.isEmpty()) {
        return;
      }
      lo[i] = vars[i].min();
      hi[i] = vars[i].max();
    }
    if (boxSize(lo, hi, m.alias()) <= MAX_BOX) {
      satisfiedIsSound(result, where + " (before propagation)", m, lo, hi, m.alias());
    }
  }

  /** The constraint's own text, with -Dconsistency.describe=true, to read a counterexample. */
  private static String describe(Object constraint) {
    return Boolean.getBoolean("consistency.describe") ? " {" + constraint + "}" : "";
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
    int[] first = m.alias();
    int[] lo = new int[n];
    int[] hi = new int[n];
    for (int i = 0; i < n; i++) {
      lo[i] = vars[i].min();
      hi[i] = vars[i].max();
    }
    if (boxSize(lo, hi, first) > MAX_BOX) {
      result.skipped++;
      return;
    }
    // DifferenceCycles and EnergyPrecedence add pruning to precedences the model posts itself, so
    // they may accept a fixed assignment that breaks one of them
    boolean complete =
        !(m.constraint() instanceof DifferenceCycles || m.constraint() instanceof EnergyPrecedence);
    if (complete && Arrays.stream(vars).allMatch(IntVar::singleton)) {
      int[] t = Arrays.stream(vars).mapToInt(IntVar::value).toArray();
      if (!m.relation().test(t)) {
        result.errors.add(where + ": accepted the non-solution " + Arrays.toString(t));
        return;
      }
    }
    if (complete && !satisfiedIsSound(result, where, m, lo, hi, first)) {
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
        first,
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
      String again = rerun(store, c, vars);
      if (!again.equals(propagated)) {
        result.notFixpoint++;
        if (result.fixpointExample == null) {
          result.fixpointExample = where + ", running it again gives " + again;
        }
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
    } catch (FailException _) {
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
    int[] first = m.alias();
    if (boxSize(lo, hi, first) > MAX_BOX) {
      return null;
    }
    List<int[]> result = new ArrayList<>();
    forEachTuple(
        lo,
        hi,
        first,
        t -> {
          if (inDomains(vars, t) && m.relation().test(t)) {
            result.add(t.clone());
          }
        });
    return result;
  }

  /** The number of tuples over the distinct variables, a repeated one counted once. */
  private static long boxSize(int[] lo, int[] hi, int[] first) {
    long size = 1;
    for (int i = 0; i < lo.length && size <= MAX_BOX; i++) {
      if (first[i] == i) {
        size *= hi[i] - lo[i] + 1;
      }
    }
    return size;
  }

  /**
   * Every tuple of the box lo..hi in which positions of one variable hold one value (first[i] is
   * the first position of the variable at position i).
   */
  private static void forEachTuple(
      int[] lo, int[] hi, int[] first, java.util.function.Consumer<int[]> action) {
    int[] t = lo.clone();
    while (true) {
      for (int i = 0; i < t.length; i++) {
        t[i] = t[first[i]];
      }
      action.accept(t);
      int k = 0;
      while (k < t.length && (first[k] != k || t[k] == hi[k])) {
        if (first[k] == k) {
          t[k] = lo[k];
        }
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
  // starts under a random acyclic graph of precedences, earliness and tardiness at most z
  private static Model precedenceCost(Store s, Random r) {
    int n = 2 + r.nextInt(3);
    IntVar[] x = vars(s, "s", n, 0, 6, r);
    IntVar z = aVar(s, "z", 0, 4 * n, r);
    List<int[]> prec = new ArrayList<>();
    for (int j = 1; j < n; j++) {
      for (int i = 0; i < j; i++) {
        if (r.nextInt(2) == 0) {
          prec.add(new int[] {i, j, r.nextInt(4) - 1});
        }
      }
    }
    int[][] terms = new int[n][];
    for (int i = 0; i < n; i++) {
      terms[i] = new int[] {i, r.nextInt(7), r.nextInt(3), r.nextInt(3)};
    }
    int[][] p = prec.toArray(new int[0][]);
    return new Model(
        new PrecedenceCost(x, p, terms, z),
        t -> {
          for (int[] q : p) {
            if (t[q[1]] < t[q[0]] + q[2]) {
              return false;
            }
          }
          int total = 0;
          for (int[] q : terms) {
            total += q[2] * Math.max(0, q[1] - t[q[0]]) + q[3] * Math.max(0, t[q[0]] - q[1]);
          }
          return total <= t[n];
        },
        concat(x, new IntVar[] {z}));
  }

  private static IntVar aVar(Store store, String name, int lo, int hi, Random random) {
    IntVar again = repeated(lo, hi, false, false);
    if (again != null) {
      return again;
    }
    IntVar v = new IntVar(store, name);
    for (int k = lo; k <= hi; k++) {
      if (random.nextInt(5) > 0) {
        v.addDom(k, k);
      }
    }
    if (v.getSize() == 0) {
      v.addDom(lo, lo);
    }
    return pooled(v);
  }

  /**
   * In repeated-variable mode, about a third of the time, a variable of this instance created
   * earlier whose domain lies in lo..hi (without holes if interval, a BooleanVar if bool); null
   * otherwise.
   */
  private static IntVar repeated(int lo, int hi, boolean interval, boolean bool) {
    if (pool == null || pool.isEmpty() || poolRandom.nextInt(3) != 0) {
      return null;
    }
    List<IntVar> fit =
        pool.stream()
            .filter(v -> v.min() >= lo && v.max() <= hi)
            .filter(v -> !interval || v.getSize() == v.max() - v.min() + 1)
            .filter(v -> !bool || v instanceof BooleanVar)
            .toList();
    return fit.isEmpty() ? null : fit.get(poolRandom.nextInt(fit.size()));
  }

  private static <T extends IntVar> T pooled(T v) {
    if (pool != null) {
      pool.add(v);
    }
    return v;
  }

  /** Sum of x = total and cost &gt;= sum of random convex costs of x, 2 to 4 variables. */
  private static Model convexAllocation(Store store, Random random, boolean lagrangian) {
    int n = 2 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, -2, 4, random);
    ConvexCost[] f = new ConvexCost[n];
    RandomConvexCosts.Cost[] costs = new RandomConvexCosts.Cost[n];
    for (int i = 0; i < n; i++) {
      costs[i] = RandomConvexCosts.random(random, -2, 4);
      f[i] = costs[i].cost();
    }
    int t = random.nextInt(2 * n + 2);
    IntVar total =
        random.nextBoolean()
            ? aVar(store, "t", t, t, random)
            : aVar(store, "t", t - 2, t + 3, random);
    int start = -5 + random.nextInt(30);
    IntVar cost = aVar(store, "c", start, start + 25, random);
    ConvexAllocation c = new ConvexAllocation(x, f, total, cost);
    c.lagrangianOnly(lagrangian);
    return new Model(
        c,
        a -> {
          long sum = 0;
          long value = 0;
          for (int i = 0; i < n; i++) {
            sum += a[i];
            value += costs[i].value().applyAsLong(a[i]);
          }
          return sum == a[n] && value <= a[n + 1];
        },
        concat(x, new IntVar[] {total, cost}));
  }

  /** A chain of 3 or 4 vectors as one LexChain (native) or as pairwise Lex constraints. */
  private static Model lexChain(Store s, Random r, boolean nativeChain) {
    boolean lt = r.nextBoolean();
    int m = 3 + r.nextInt(2);
    int n = 2 + r.nextInt(2);
    IntVar[][] v = new IntVar[m][];
    for (int i = 0; i < m; i++) {
      v[i] = vars(s, "v" + i + "_", n, 0, 2, r);
    }
    Object constraint;
    if (nativeChain) {
      constraint = new LexChain(v, lt);
    } else {
      List<Constraint> pairs = new ArrayList<>();
      for (int i = 0; i + 1 < m; i++) {
        pairs.add(new LexOrder(v[i], v[i + 1], lt));
      }
      constraint = pairs;
    }
    return new Model(
        constraint,
        t -> {
          for (int i = 0; i + 1 < m; i++) {
            int cmp =
                Arrays.compare(
                    Arrays.copyOfRange(t, i * n, (i + 1) * n),
                    Arrays.copyOfRange(t, (i + 1) * n, (i + 2) * n));
            if (lt ? cmp >= 0 : cmp > 0) {
              return false;
            }
          }
          return true;
        },
        concat(v));
  }

  /** A variable over lo..hi with a random sub-interval, so without holes. */
  private static IntVar interval(Store store, String name, int lo, int hi, Random random) {
    IntVar again = repeated(lo, hi, true, false);
    if (again != null) {
      return again;
    }
    int a = lo + random.nextInt(hi - lo + 1);
    int b = lo + random.nextInt(hi - lo + 1);
    return pooled(new IntVar(store, name, Math.min(a, b), Math.max(a, b)));
  }

  private static IntVar[] vars(Store store, String prefix, int n, int lo, int hi, Random random) {
    return IntStream.range(0, n)
        .mapToObj(i -> aVar(store, prefix + i, lo, hi, random))
        .toArray(IntVar[]::new);
  }

  /** A BooleanVar, or in repeated-variable mode sometimes one created earlier. */
  private static IntVar aBool(Store store, String name) {
    IntVar again = repeated(0, 1, true, true);
    return again != null ? again : pooled(new BooleanVar(store, name));
  }

  private static Model boolReif(Store store, Random random, String kind) {
    int n = (kind.equals("orSimple") ? 2 : 1 + random.nextInt(4));
    IntVar[] x = bools(store, "x", n);
    IntVar y = aBool(store, "y");
    Object c =
        switch (kind) {
          case "and" -> new org.jacop.constraints.AndBool(x, y);
          case "or" -> new org.jacop.constraints.OrBool(x, y);
          case "andVector" -> new org.jacop.constraints.AndBoolVector(x, y);
          case "orVector" -> new org.jacop.constraints.OrBoolVector(x, y);
          case "orWatched" -> new org.jacop.constraints.OrBoolWatched(x, y, false);
          case "norWatched" -> new org.jacop.constraints.OrBoolWatched(x, y, true);
          case "orSimple" -> new org.jacop.constraints.OrBoolSimple(x[0], x[1], y);
          default -> new org.jacop.constraints.EqBool(x, y);
        };
    return new Model(
        c,
        t -> {
          int ones = Arrays.stream(t, 0, n).sum();
          boolean value =
              switch (kind) {
                case "and", "andVector" -> ones == n;
                case "norWatched" -> ones == 0;
                case "eq" -> ones == 0 || ones == n;
                default -> ones > 0;
              };
          return t[n] == (value ? 1 : 0);
        },
        concat(x, new IntVar[] {y}));
  }

  private static Model ifThenBool(Store store, Random random) {
    IntVar[] x = bools(store, "x", 3);
    return new Model(
        new org.jacop.constraints.IfThenBool(x[0], x[1], x[2]),
        t -> (t[0] == 0 || t[1] == 1) == (t[2] == 1),
        x);
  }

  private static Model in(Store store, Random random) {
    IntVar x = aVar(store, "x", -3, 6, random);
    IntervalDomain d = new IntervalDomain();
    for (int v = -3; v <= 6; v++) {
      if (random.nextInt(3) > 0) {
        d.unionAdapt(v, v);
      }
    }
    if (d.isEmpty()) {
      d.unionAdapt(0, 0);
    }
    return new Model(new org.jacop.constraints.In(x, d), t -> d.contains(t[0]), new IntVar[] {x});
  }

  private static Model weightedSum(Store store, Random random, boolean weighted) {
    int n = 1 + random.nextInt(4);
    IntVar[] x = vars(store, "x", n, -2, 3, random);
    int[] w = new int[n];
    for (int i = 0; i < n; i++) {
      w[i] = weighted ? random.nextInt(7) - 3 : 1;
    }
    IntVar sum = aVar(store, "sum", -8, 8, random);
    return new Model(
        weighted
            ? new org.jacop.constraints.SumWeight(x, w, sum)
            : new org.jacop.constraints.Sum(x, sum),
        t -> IntStream.range(0, n).map(i -> w[i] * t[i]).sum() == t[n],
        concat(x, new IntVar[] {sum}));
  }

  private static Model maxCliqueBound(Store store, Random random) {
    int n = 2 + random.nextInt(5);
    IntVar[] x = bools(store, "x", n);
    List<int[]> pairs = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (random.nextInt(2) == 0) {
          pairs.add(new int[] {i, j});
        }
      }
    }
    int[][] conflicts =
        IntStream.range(0, n)
            .mapToObj(i -> pairs.stream().filter(p -> p[0] == i).mapToInt(p -> p[1]).toArray())
            .toArray(int[][]::new);
    IntVar sum = aVar(store, "sum", 0, n, random);
    return new Model(
        new org.jacop.constraints.MaxCliqueBound(x, conflicts, sum),
        t -> {
          for (int[] p : pairs) {
            if (t[p[0]] == 1 && t[p[1]] == 1) {
              return false;
            }
          }
          return t[n] <= Arrays.stream(t, 0, n).sum();
        },
        concat(x, new IntVar[] {sum}));
  }

  private static Model disjointConditional(Store store, Random random) {
    // lengths of at least 1: what a zero length means here is not documented
    int k = 2 + random.nextInt(2);
    IntVar[][] rect = new IntVar[k][];
    for (int i = 0; i < k; i++) {
      rect[i] =
          new IntVar[] {
            aVar(store, "o" + i + "_0", 0, 2, random),
            aVar(store, "o" + i + "_1", 0, 2, random),
            aVar(store, "l" + i + "_0", 1, 2, random),
            aVar(store, "l" + i + "_1", 1, 2, random)
          };
    }
    List<List<Integer>> pairs = new ArrayList<>();
    for (int i = 0; i < k; i++) {
      for (int j = i + 1; j < k; j++) {
        if (random.nextBoolean()) {
          pairs.add(List.of(i + 1, j + 1));
        }
      }
    }
    IntVar[] cond = new IntVar[pairs.size()];
    for (int p = 0; p < cond.length; p++) {
      cond[p] = aBool(store, "c" + p);
    }
    IntVar[] all = concat(concat(rect), cond);
    return new Model(
        new org.jacop.constraints.DisjointConditional(
            rect, pairs, Arrays.asList(cond), random.nextBoolean()),
        t -> {
          for (int i = 0; i < k; i++) {
            for (int j = i + 1; j < k; j++) {
              boolean apart =
                  t[4 * i] + t[4 * i + 2] <= t[4 * j]
                      || t[4 * j] + t[4 * j + 2] <= t[4 * i]
                      || t[4 * i + 1] + t[4 * i + 3] <= t[4 * j + 1]
                      || t[4 * j + 1] + t[4 * j + 3] <= t[4 * i + 1];
              int p = pairs.indexOf(List.of(i + 1, j + 1));
              if (!apart && (p < 0 || t[4 * k + p] == 1)) {
                return false;
              }
            }
          }
          return true;
        },
        all);
  }

  private static Model tableCover(Store store, Random random) {
    int groups = 2 + random.nextInt(2);
    IntVar[][] g = new IntVar[groups][];
    int[][][] tuples = new int[groups][][];
    for (int i = 0; i < groups; i++) {
      int size = 1 + random.nextInt(2);
      g[i] = vars(store, "g" + i + "_", size, 0, 4, random);
      int count = 1 + random.nextInt(5);
      tuples[i] = new int[count][size];
      for (int[] tuple : tuples[i]) {
        for (int l = 0; l < size; l++) {
          tuple[l] = random.nextInt(5);
        }
      }
    }
    IntVar[] all = concat(g);
    return new Model(
        new org.jacop.constraints.TableCover(g, tuples, false),
        t -> {
          if (Arrays.stream(t).distinct().count() != t.length) {
            return false;
          }
          int at = 0;
          for (int i = 0; i < groups; i++) {
            int from = at;
            boolean found =
                Arrays.stream(tuples[i])
                    .anyMatch(
                        tuple ->
                            Arrays.equals(tuple, Arrays.copyOfRange(t, from, from + tuple.length)));
            if (!found) {
              return false;
            }
            at += g[i].length;
          }
          return true;
        },
        all);
  }

  private static Model softAlldifferent(Store store, Random random) {
    int n = 2 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    boolean decomposition = random.nextBoolean();
    IntVar cost = aVar(store, "cost", 0, 6, random);
    return new Model(
        new org.jacop.constraints.SoftAlldifferent(
            x,
            cost,
            decomposition
                ? org.jacop.constraints.ViolationMeasure.DECOMPOSITION_BASED
                : org.jacop.constraints.ViolationMeasure.VARIABLE_BASED),
        t -> {
          int violations = 0;
          if (decomposition) {
            for (int i = 0; i < n; i++) {
              for (int j = i + 1; j < n; j++) {
                violations += t[i] == t[j] ? 1 : 0;
              }
            }
          } else {
            violations = n - (int) Arrays.stream(t, 0, n).distinct().count();
          }
          return t[n] == violations;
        },
        concat(x, new IntVar[] {cost}));
  }

  private static Model costRegular(Store store, Random random, boolean multi) {
    int states = 1 + random.nextInt(3);
    int values = 3;
    int[][] transition = new int[states][values];
    for (int[] row : transition) {
      for (int v = 0; v < values; v++) {
        row[v] = random.nextInt(4) == 0 ? -1 : random.nextInt(states);
      }
    }
    int[] finals = IntStream.range(0, states).filter(q -> q == 0 || random.nextBoolean()).toArray();
    int n = 2 + random.nextInt(3);
    int resources = multi ? 1 + random.nextInt(2) : 1;
    int[][][][] costs = new int[resources][n][states][values];
    for (int[][][] byPosition : costs) {
      for (int[][] byState : byPosition) {
        for (int[] row : byState) {
          for (int v = 0; v < values; v++) {
            row[v] = random.nextInt(4) - 1;
          }
        }
      }
    }
    IntVar[] x = vars(store, "x", n, 0, values - 1, random);
    IntVar[] cost = new IntVar[resources];
    for (int r = 0; r < resources; r++) {
      cost[r] = aVar(store, "cost" + r, -n, 2 * n, random);
    }
    Object c =
        multi
            ? new org.jacop.constraints.regular.MultiCostRegular(
                x, transition, 0, 0, finals, costs, cost)
            : new org.jacop.constraints.regular.CostRegular(
                x, transition, 0, 0, finals, costs[0], cost[0]);
    return new Model(
        c,
        t -> {
          int q = 0;
          int[] total = new int[resources];
          for (int i = 0; i < n; i++) {
            int next = transition[q][t[i]];
            if (next < 0) {
              return false;
            }
            for (int r = 0; r < resources; r++) {
              total[r] += costs[r][i][q][t[i]];
            }
            q = next;
          }
          int end = q;
          if (Arrays.stream(finals).noneMatch(f -> f == end)) {
            return false;
          }
          for (int r = 0; r < resources; r++) {
            if (t[n + r] != total[r]) {
              return false;
            }
          }
          return true;
        },
        concat(x, cost));
  }

  private static Model softGcc(Store store, Random random) {
    int n = 2 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    int k = 1 + random.nextInt(2);
    int[] counted = random.nextBoolean() ? new int[] {0, 1, 2}.clone() : new int[] {1, 2, 3};
    counted = Arrays.copyOf(counted, k);
    int[] lower = new int[k];
    int[] upper = new int[k];
    for (int j = 0; j < k; j++) {
      lower[j] = random.nextInt(2);
      upper[j] = lower[j] + random.nextInt(2);
    }
    IntVar[] hard = vars(store, "h", k, 0, n, random);
    boolean valueBased = random.nextBoolean();
    IntVar cost = aVar(store, "cost", 0, 2 * n, random);
    int[] values = counted;
    return new Model(
        new org.jacop.constraints.SoftGCC(
            x,
            hard,
            values,
            lower,
            upper,
            cost,
            valueBased
                ? org.jacop.constraints.ViolationMeasure.VALUE_BASED
                : org.jacop.constraints.ViolationMeasure.VARIABLE_BASED),
        t -> {
          int shortage = 0;
          int excess = 0;
          for (int j = 0; j < k; j++) {
            int v = values[j];
            int count = (int) Arrays.stream(t, 0, n).filter(a -> a == v).count();
            if (t[n + j] != count) {
              return false;
            }
            shortage += Math.max(0, lower[j] - count);
            excess += Math.max(0, count - upper[j]);
          }
          if (!valueBased && Arrays.stream(lower).sum() > n) {
            return false;
          }
          int violation = valueBased ? shortage + excess : Math.max(shortage, excess);
          return t[n + k] == violation;
        },
        concat(x, hard, new IntVar[] {cost}));
  }

  private static Model ifThenElseBool(Store store, Random random) {
    org.jacop.core.BooleanVar[] b = new org.jacop.core.BooleanVar[3];
    for (int i = 0; i < 3; i++) {
      b[i] = new org.jacop.core.BooleanVar(store, "b" + i);
    }
    return new Model(
        new org.jacop.constraints.IfThenElseBool(b[0], b[1], b[2]),
        t -> t[0] == 1 ? t[1] == 1 : t[2] == 1,
        b);
  }

  private static Model sequenceMdd(Store store, Random random) {
    int n = 3 + random.nextInt(2);
    boolean pred = random.nextBoolean();
    IntVar[] arcs = vars(store, "a", n, 0, n - 1, random);
    IntVar[] in = vars(store, "in", n, 0, 6, random);
    IntVar[] out = vars(store, "out", n, 0, 6, random);
    int none = org.jacop.constraints.SequenceMdd.NONE;
    int[][] travel = new int[n][n];
    for (int[] row : travel) {
      for (int j = 0; j < n; j++) {
        row[j] = random.nextInt(5) == 0 ? none : random.nextInt(3);
      }
    }
    int[] delta = new int[n];
    for (int j = 0; j < n; j++) {
      delta[j] = random.nextInt(5) == 0 ? none : random.nextInt(2);
    }
    return new Model(
        new org.jacop.constraints.SequenceMdd(
            arcs, pred, 0, in, out, travel, delta, 0, 1 + random.nextInt(3)),
        t -> {
          int[] succ = new int[n];
          for (int i = 0; i < n; i++) {
            if (pred) {
              succ[t[i]] = i;
            } else {
              succ[i] = t[i];
            }
          }
          if (pred && Arrays.stream(t, 0, n).distinct().count() != n) {
            return false;
          }
          int at = 0;
          for (int k = 0; k < n; k++) {
            int next = succ[at];
            if (travel[at][next] != none && t[n + next] < t[2 * n + at] + travel[at][next]) {
              return false;
            }
            at = next;
            if (at == 0 && k < n - 1) {
              return false;
            }
          }
          if (at != 0) {
            return false;
          }
          for (int j = 1; j < n; j++) {
            if (delta[j] != none && t[2 * n + j] < t[n + j] + delta[j]) {
              return false;
            }
          }
          return true;
        },
        concat(arcs, in, out));
  }

  private static Model costMdd(Store store, Random random) {
    int n = 2 + random.nextInt(3);
    // nodes 1..N by level; node 1 is the root, node 0 the terminal
    List<Integer> levelList = new ArrayList<>();
    List<int[]> byLevel = new ArrayList<>();
    for (int l = 1; l <= n; l++) {
      int width = l == 1 ? 1 : 1 + random.nextInt(2);
      int[] ids = new int[width];
      for (int w = 0; w < width; w++) {
        levelList.add(l);
        ids[w] = levelList.size();
      }
      byLevel.add(ids);
    }
    List<int[]> edges = new ArrayList<>(); // from, lo, hi, cost, to
    for (int l = 0; l < n; l++) {
      for (int u : byLevel.get(l)) {
        int[] next = l + 1 < n ? byLevel.get(l + 1) : new int[] {0};
        for (int e = 1 + random.nextInt(2); e > 0; e--) {
          int lo = random.nextInt(3);
          int hi = lo + random.nextInt(2);
          edges.add(
              new int[] {u, lo, hi, random.nextInt(4) - 1, next[random.nextInt(next.length)]});
        }
      }
    }
    int[] level = levelList.stream().mapToInt(Integer::intValue).toArray();
    int m = edges.size();
    int[] from = new int[m];
    IntDomain[] label = new IntDomain[m];
    int[] edgeCost = new int[m];
    int[] to = new int[m];
    for (int e = 0; e < m; e++) {
      int[] d = edges.get(e);
      from[e] = d[0];
      label[e] = new IntervalDomain(d[1], d[2]);
      edgeCost[e] = d[3];
      to[e] = d[4];
    }
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    IntVar cost = aVar(store, "cost", -n, 2 * n, random);
    return new Model(
        new org.jacop.constraints.regular.CostMdd(x, level, from, label, edgeCost, to, cost),
        t -> {
          // (node, cost so far) pairs reachable after each variable
          java.util.Set<Long> at = new java.util.HashSet<>();
          at.add((long) 1 << 32);
          for (int i = 0; i < n; i++) {
            java.util.Set<Long> next = new java.util.HashSet<>();
            for (long state : at) {
              int node = (int) (state >> 32);
              int c = (int) state;
              for (int[] d : edges) {
                if (d[0] == node && d[1] <= t[i] && t[i] <= d[2]) {
                  next.add(((long) d[4] << 32) | ((c + d[3]) & 0xffffffffL));
                }
              }
            }
            at = next;
          }
          return at.contains(t[n] & 0xffffffffL);
        },
        concat(x, new IntVar[] {cost}));
  }

  private static Model networkFlow(Store store, Random random, boolean varWeight) {
    int nodes = 3 + random.nextInt(2);
    int arcs = 3 + random.nextInt(3);
    int[] from = new int[arcs];
    int[] to = new int[arcs];
    int[] weight = new int[arcs];
    for (int k = 0; k < arcs; k++) {
      from[k] = random.nextInt(nodes);
      to[k] = (from[k] + 1 + random.nextInt(nodes - 1)) % nodes;
      weight[k] = random.nextInt(5) - 1;
    }
    int[] balance = new int[nodes];
    balance[0] = random.nextInt(3);
    balance[1 + random.nextInt(nodes - 1)] -= balance[0];
    IntVar[] x = new IntVar[arcs];
    for (int k = 0; k < arcs; k++) {
      x[k] = aVar(store, "f" + k, 0, 3, random);
    }
    IntVar w = varWeight ? aVar(store, "w", -1, 2, random) : null;
    IntVar cost = aVar(store, "cost", -4, 12, random);
    org.jacop.constraints.netflow.NetworkBuilder net =
        new org.jacop.constraints.netflow.NetworkBuilder();
    org.jacop.constraints.netflow.simplex.Node[] node =
        new org.jacop.constraints.netflow.simplex.Node[nodes];
    for (int i = 0; i < nodes; i++) {
      node[i] = net.addNode("n" + i, balance[i]);
    }
    for (int k = 0; k < arcs; k++) {
      if (varWeight && k == 0) {
        net.addArc(node[from[k]], node[to[k]], w, x[k]);
      } else {
        net.addArc(node[from[k]], node[to[k]], weight[k], x[k]);
      }
    }
    net.setCostVariable(cost);
    IntVar[] vars = varWeight ? concat(x, new IntVar[] {w, cost}) : concat(x, new IntVar[] {cost});
    return new Model(
        new org.jacop.constraints.netflow.NetworkFlow(net),
        t -> {
          int[] out = new int[nodes];
          long total = 0;
          for (int k = 0; k < arcs; k++) {
            out[from[k]] += t[k];
            out[to[k]] -= t[k];
            total += (long) (varWeight && k == 0 ? t[arcs] : weight[k]) * t[k];
          }
          for (int i = 0; i < nodes; i++) {
            if (out[i] != balance[i]) {
              return false;
            }
          }
          return total == t[t.length - 1];
        },
        vars);
  }

  private static Model unaryTransition(Store store, Random random, boolean withOptional) {
    int n = 3;
    IntVar[] starts = vars(store, "s", n, 0, 6, random);
    IntVar[] durations = vars(store, "d", n, 0, 2, random);
    int[] family = new int[n];
    for (int i = 0; i < n; i++) {
      family[i] = random.nextInt(2);
    }
    int[][] transitions = new int[2][2];
    for (int[] row : transitions) {
      for (int g = 0; g < 2; g++) {
        row[g] = random.nextInt(3);
      }
    }
    IntVar[] optional = withOptional ? bools(store, "o", n) : null;
    Object constraint =
        withOptional
            ? new org.jacop.constraints.cumulative.UnaryTransition(
                starts, durations, family, transitions, optional)
            : new org.jacop.constraints.cumulative.UnaryTransition(
                starts, durations, family, transitions);
    return new Model(
        constraint,
        t -> {
          for (int i = 0; i < n; i++) {
            for (int j = i + 1; j < n; j++) {
              if (withOptional && (t[2 * n + i] == 0 || t[2 * n + j] == 0)) {
                continue;
              }
              boolean before = t[i] + t[n + i] + transitions[family[i]][family[j]] <= t[j];
              boolean after = t[j] + t[n + j] + transitions[family[j]][family[i]] <= t[i];
              if (!before && !after) {
                return false;
              }
            }
          }
          return true;
        },
        withOptional ? concat(starts, durations, optional) : concat(starts, durations));
  }

  private static Model multiCumulative(Store store, Random random) {
    int n = 3 + random.nextInt(2);
    int resources = 2;
    IntVar[] starts = vars(store, "s", n, 0, 4, random);
    int[] durations = new int[n];
    int[][] heights = new int[resources][n];
    for (int i = 0; i < n; i++) {
      durations[i] = random.nextInt(4);
      for (int r = 0; r < resources; r++) {
        heights[r][i] = random.nextInt(3);
      }
    }
    IntVar[] limits = vars(store, "l", resources, 0, 4, random);
    return new Model(
        new org.jacop.constraints.cumulative.MultiCumulative(starts, durations, heights, limits),
        t -> {
          for (int r = 0; r < resources; r++) {
            for (int time = 0; time <= 8; time++) {
              int use = 0;
              for (int i = 0; i < n; i++) {
                if (t[i] <= time && time < t[i] + durations[i]) {
                  use += heights[r][i];
                }
              }
              if (use > t[n + r]) {
                return false;
              }
            }
          }
          return true;
        },
        concat(starts, limits));
  }

  private static Model vectorBinpacking(Store store, Random random) {
    int items = 3 + random.nextInt(2);
    int bins = 2;
    int dims = 2;
    IntVar[] bin = vars(store, "b", items, 1, bins, random);
    int[][] w = new int[dims][items];
    IntVar[][] load = new IntVar[dims][bins];
    for (int d = 0; d < dims; d++) {
      for (int i = 0; i < items; i++) {
        w[d][i] = random.nextInt(4);
      }
      load[d] = vars(store, "l" + d + "_", bins, 0, 6, random);
    }
    return new Model(
        new org.jacop.constraints.binpacking.VectorBinpacking(bin, load, w, 1),
        t -> {
          for (int d = 0; d < dims; d++) {
            for (int b = 0; b < bins; b++) {
              int sum = 0;
              for (int i = 0; i < items; i++) {
                if (t[i] == b + 1) {
                  sum += w[d][i];
                }
              }
              if (sum != t[items + d * bins + b]) {
                return false;
              }
            }
          }
          return true;
        },
        concat(bin, load[0], load[1]));
  }

  private static Model colouredSpanningTree(Store store, Random random) {
    int n = 3 + random.nextInt(2);
    int m = n + random.nextInt(3);
    int[] from = new int[m];
    int[] to = new int[m];
    int[] weights = new int[m];
    int[] colours = new int[m];
    int total = 0;
    for (int e = 0; e < m; e++) {
      from[e] = random.nextInt(n);
      to[e] = (from[e] + 1 + random.nextInt(n - 1)) % n;
      weights[e] = random.nextInt(4);
      colours[e] = random.nextInt(3) - 1;
      total += weights[e];
    }
    int[] caps = {random.nextInt(3), random.nextInt(3)};
    IntVar[] es = bools(store, "e", m);
    IntVar cost = aVar(store, "cost", 0, total, random);
    List<Constraint> parts =
        new ArrayList<>(
            new org.jacop.constraints.graph.WeightedSpanningTree(
                    n, from, to, weights, null, es, cost, 0, false)
                .decompose(store));
    for (int c = 0; c < caps.length; c++) {
      final int colour = c;
      IntVar[] ofColour =
          IntStream.range(0, m)
              .filter(e -> colours[e] == colour)
              .mapToObj(e -> es[e])
              .toArray(IntVar[]::new);
      if (ofColour.length > 0) {
        parts.add(new SumInt(ofColour, "<=", new IntVar(store, caps[c], caps[c])));
      }
    }
    parts.add(
        new org.jacop.constraints.graph.ColouredSpanningTreeBound(
            n, from, to, weights, colours, caps, es, cost, 0));
    return new Model(
        parts,
        t -> {
          int[] full = new int[n + m + 2];
          Arrays.fill(full, 0, n, 1);
          System.arraycopy(t, 0, full, n, m);
          int[] used = new int[caps.length];
          int sum = 0;
          for (int e = 0; e < m; e++) {
            sum += t[e] * weights[e];
            if (colours[e] >= 0) {
              used[colours[e]] += t[e];
            }
          }
          for (int c = 0; c < caps.length; c++) {
            if (used[c] > caps[c]) {
              return false;
            }
          }
          full[n + m] = 0;
          return sum == t[m] && graphHolds(full, "tree", false, n, from, to);
        },
        concat(es, new IntVar[] {cost}));
  }

  private static Model knapsackDP(Store store, Random random) {
    int n = 2 + random.nextInt(3);
    int[] w = random.ints(n, 0, 4).toArray();
    int[] p = random.ints(n, 0, 5).toArray();
    IntVar[] q = vars(store, "q", n, 0, 2, random);
    IntVar cap = aVar(store, "c", 0, 12, random);
    IntVar profit = aVar(store, "p", 0, 16, random);
    return new Model(
        new org.jacop.constraints.knapsack.KnapsackDP(p, w, q, cap, profit),
        t -> {
          int sw = 0;
          int sp = 0;
          for (int i = 0; i < n; i++) {
            sw += w[i] * t[i];
            sp += p[i] * t[i];
          }
          return sw == t[n] && sp == t[n + 1];
        },
        concat(q, new IntVar[] {cap, profit}));
  }

  private static Model subcircuitCostPair(Store store, Random random) {
    int n = 3 + random.nextInt(2);
    IntVar[] x = vars(store, "x", n, 1, n, random);
    int[][] c1 = costMatrix(n, random);
    int[][] c2 = costMatrix(n, random);
    IntVar cost1 = aVar(store, "cost1", 0, 4 * n, random);
    IntVar cost2 = aVar(store, "cost2", 0, 4 * n, random);
    return new Model(
        List.of(
            new org.jacop.constraints.Subcircuit(x),
            // the pair only bounds the sums, which other constraints define
            new org.jacop.constraints.SubcircuitCost(x, c1, cost1),
            new org.jacop.constraints.SubcircuitCost(x, c2, cost2),
            new org.jacop.constraints.SubcircuitCostPair(x, c1, cost1, c2, cost2, 1)),
        t -> {
          if (!circuitHolds(t, n, true)) {
            return false;
          }
          int total1 = 0;
          int total2 = 0;
          for (int i = 0; i < n; i++) {
            total1 += c1[i][t[i] - 1];
            total2 += c2[i][t[i] - 1];
          }
          return t[n] == total1 && t[n + 1] == total2;
        },
        concat(x, new IntVar[] {cost1, cost2}));
  }

  private static Model cumulatives(Store store, Random random, boolean upper, boolean optional) {
    int n = 3;
    IntVar[] starts = vars(store, "s", n, 0, 3, random);
    IntVar[] durations = vars(store, "d", n, 0, 2, random);
    IntVar[] heights = vars(store, "h", n, -1, 1, random);
    IntVar[] machines = vars(store, "m", n, 1, 2, random);
    IntVar[] bounds = vars(store, "b", 2, -1, 2, random);
    IntVar[] present = optional ? bools(store, "o", n) : null;
    Object constraint =
        new org.jacop.constraints.cumulative.Cumulatives(
            starts, durations, heights, machines, bounds, upper, 1, present);
    return new Model(
        constraint,
        t -> {
          for (int machine = 1; machine <= 2; machine++) {
            int bound = t[4 * n + machine - 1];
            for (int time = 0; time <= 6; time++) {
              int load = 0;
              boolean runs = false;
              for (int i = 0; i < n; i++) {
                boolean on = !optional || t[4 * n + 2 + i] == 1;
                if (on && t[3 * n + i] == machine && t[i] <= time && time < t[i] + t[n + i]) {
                  runs = true;
                  load += t[2 * n + i];
                }
              }
              if (runs && (upper ? load > bound : load < bound)) {
                return false;
              }
            }
          }
          return true;
        },
        optional
            ? concat(starts, durations, heights, machines, bounds, present)
            : concat(starts, durations, heights, machines, bounds));
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
    IntVar s = aVar(store, "s", -8, 8, random);
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
    return linearBool(store, random, rel, constant, false);
  }

  /** The same, with watched propagation forced for a constant right hand side. */
  private static Model linearBool(
      Store store, Random random, String rel, boolean constant, boolean watched) {
    int n = 3 + random.nextInt(4);
    int[] w = new int[n];
    IntVar[] b = new IntVar[n];
    for (int i = 0; i < n; i++) {
      w[i] = (1 + random.nextInt(5)) * (random.nextBoolean() ? 1 : -1);
      b[i] = random.nextBoolean() ? aBool(store, "b" + i) : aVar(store, "b" + i, 0, 1, random);
    }
    if (constant) {
      int c = random.nextInt(13) - 6;
      LinearBool linear = new LinearBool(b, w, rel, c);
      if (watched) {
        linear.setWatchMinLength(0);
      }
      return new Model(
          linear,
          t -> holds(rel, IntStream.range(0, n).mapToLong(i -> (long) w[i] * t[i]).sum(), c),
          b,
          linearOverReals(w, c, rel));
    }
    IntVar s = aVar(store, "s", -8, 12, random);
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
    IntVar x = aVar(store, "x", range[0], range[1], random);
    IntVar y = aVar(store, "y", range[2], range[3], random);
    IntVar z = aVar(store, "z", range[4], range[5], random);
    return new Model(constraint.apply(x, y, z), relation, new IntVar[] {x, y, z});
  }

  /**
   * z = x^y as MiniZinc's int_pow defines it: 1 div x^-y for y &lt; 0, with no solution at x = 0.
   */
  private static boolean pow(int[] t) {
    int x = t[0];
    int y = t[1];
    if (y < 0) {
      return x != 0 && t[2] == (x == 1 ? 1 : x == -1 ? ((y & 1) == 0 ? 1 : -1) : 0);
    }
    long p = 1;
    for (int i = 0; i < y; i++) {
      p *= x;
    }
    return p == t[2];
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
    IntVar index = aVar(store, "i", 0, n + 1, random);
    IntVar value = aVar(store, "v", 0, 5, random);
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
    Object c =
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
    return cumulative(store, random, basic ? 1 : 0);
  }

  /**
   * Cumulative over three tasks (kind 0), CumulativeBasic (1), or the HornFlow check alone (2),
   * which prunes nothing but must never fail while a solution exists.
   */
  private static Model cumulative(Store store, Random random, int kind) {
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
    IntVar limit = aVar(store, "b", 1, 3, random);
    Object c =
        switch (kind) {
          case 1 -> new CumulativeBasic(s, d, r, limit);
          case 2 -> new HornFlow(s, d, r, limit);
          default -> new Cumulative(s, d, r, limit);
        };
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

  /**
   * CumulativeOptional over three tasks with presences o (unary: CumulativeUnaryOptional, limit 1,
   * uses 0..1), with zero durations, zero uses and uses above the limit: an absent task, a task
   * without duration and a task without use take nothing.
   */
  private static Model cumulativeOptional(Store store, Random random, boolean unary) {
    int n = 3;
    IntVar[] s = vars(store, "s", n, 0, 3, random);
    IntVar[] d =
        IntStream.range(0, n)
            .mapToObj(i -> interval(store, "d" + i, random.nextInt(2), 2, random))
            .toArray(IntVar[]::new);
    IntVar[] r =
        IntStream.range(0, n)
            .mapToObj(i -> interval(store, "r" + i, random.nextInt(2), unary ? 1 : 3, random))
            .toArray(IntVar[]::new);
    IntVar limit = unary ? new IntVar(store, "b", 1, 1) : aVar(store, "b", 0, 2, random);
    IntVar[] o = bools(store, "o", n);
    return new Model(
        unary
            ? new CumulativeUnaryOptional(s, d, r, limit, o)
            : new CumulativeOptional(s, d, r, limit, o),
        t -> {
          for (int time = 0; time <= 5; time++) {
            int load = 0;
            for (int i = 0; i < n; i++) {
              if (t[3 * n + 1 + i] == 1 && t[i] <= time && time < t[i] + t[n + i]) {
                load += t[2 * n + i];
              }
            }
            if (load > t[3 * n]) {
              return false;
            }
          }
          return true;
        },
        concat(s, d, r, new IntVar[] {limit}, o));
  }

  /** inter_distance(x, p) with every variable on its own window of 0..11. */
  private static Model interDistance(Store store, Random random, boolean unary) {
    int n = 2 + random.nextInt(4);
    int p = 1 + random.nextInt(4);
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      int lo = random.nextInt(9);
      x[i] = aVar(store, "x" + i, lo, Math.min(11, lo + 1 + random.nextInt(7)), random);
    }
    IntVar[] d = new IntVar[n];
    IntVar[] one = new IntVar[n];
    for (int i = 0; i < n; i++) {
      d[i] = new IntVar(store, p, p);
      one[i] = new IntVar(store, 1, 1);
    }
    return new Model(
        unary
            ? new CumulativeUnary(x, d, one, new IntVar(store, 1, 1), true)
            : new InterDistance(x, p),
        t -> {
          for (int i = 0; i < n; i++) {
            for (int j = i + 1; j < n; j++) {
              if (Math.abs(t[i] - t[j]) < p) {
                return false;
              }
            }
          }
          return true;
        },
        x);
  }

  /** multi_inter_distance(x, m, p) with every variable on its own window of 0..9. */
  private static Model multiInterDistance(Store store, Random random) {
    int n = 2 + random.nextInt(4);
    int m = 1 + random.nextInt(3);
    int p = 1 + random.nextInt(4);
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      int lo = random.nextInt(7);
      x[i] = aVar(store, "x" + i, lo, Math.min(9, lo + 1 + random.nextInt(6)), random);
    }
    return new Model(
        new MultiInterDistance(x, m, p),
        t -> {
          for (int v : t) {
            if (Arrays.stream(t).filter(w -> v <= w && w < v + p).count() > m) {
              return false;
            }
          }
          return true;
        },
        x);
  }

  /** sort(x, y) or sort(x, y, z) with z numbering the positions from an offset. */
  private static Model sort(Store store, Random random, boolean permutation) {
    int n = 2 + random.nextInt(permutation ? 2 : 3);
    int offset = random.nextInt(3) - 1;
    IntVar[] x = vars(store, "x", n, 0, 4, random);
    IntVar[] y = vars(store, "y", n, 0, 4, random);
    IntVar[] z = permutation ? vars(store, "z", n, offset, offset + n - 1, random) : new IntVar[0];
    return new Model(
        permutation ? new Sort(x, y, z, offset) : new Sort(x, y),
        t -> {
          int[] xs = Arrays.copyOfRange(t, 0, n);
          int[] ys = Arrays.copyOfRange(t, n, 2 * n);
          if (permutation) {
            boolean[] used = new boolean[n];
            for (int i = 0; i < n; i++) {
              int j = t[2 * n + i] - offset;
              if (used[j] || ys[j] != xs[i]) {
                return false;
              }
              used[j] = true;
            }
          }
          Arrays.sort(xs);
          return Arrays.equals(xs, ys);
        },
        concat(x, y, z));
  }

  // 3-4 rows of 2 variables over 0..2 with holes, pairwise different tuples (maybe but excepted
  // ones)
  static Model differentLists(Store s, Random r, boolean withExcept) {
    int m = 3 + r.nextInt(2);
    IntVar[][] x = new IntVar[m][2];
    IntVar[] all = new IntVar[2 * m];
    for (int i = 0; i < m; i++) {
      for (int j = 0; j < 2; j++) {
        x[i][j] = aVar(s, "x" + i + "_" + j, 0, 2, r);
        all[2 * i + j] = x[i][j];
      }
    }
    int[][] except = new int[withExcept ? 1 + r.nextInt(2) : 0][];
    for (int e = 0; e < except.length; e++) {
      except[e] = new int[] {r.nextInt(3), r.nextInt(3)};
    }
    return new Model(
        new AllDifferentLists(x, except),
        t -> {
          for (int i = 0; i < m; i++) {
            for (int k = i + 1; k < m; k++) {
              if (t[2 * i] == t[2 * k] && t[2 * i + 1] == t[2 * k + 1]) {
                int a = t[2 * i];
                int b = t[2 * i + 1];
                if (Arrays.stream(except).noneMatch(e -> e[0] == a && e[1] == b)) {
                  return false;
                }
              }
            }
          }
          return true;
        },
        all);
  }

  private static Model alldiff(Store store, Random random, boolean gac) {
    int n = 3 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 0, n, random);
    return new Model(
        gac ? new Alldistinct(x) : new Alldiff(x),
        t -> Arrays.stream(t).distinct().count() == t.length,
        x);
  }

  /** alldifferent(x) and sum(x) rel s, rel == or, with inequality set, <= or >=. */
  private static Model alldiffSum(
      Store store, Random random, boolean inequality, boolean hallIntervals) {
    int n = 2 + random.nextInt(4);
    int lo = random.nextInt(3) - 2;
    int hi = lo + n + random.nextInt(4);
    IntVar[] x = vars(store, "x", n, lo, hi, random);
    int rel = inequality ? 1 + random.nextInt(2) : 0;
    int sLo = n * lo + n * (n - 1) / 2;
    int sHi = n * hi - n * (n - 1) / 2;
    IntVar s = aVar(store, "s", sLo - 2, sHi + 2, random);
    return new Model(
        new AlldiffSum(x, rel == 0 ? "==" : rel == 1 ? "<=" : ">=", s, hallIntervals),
        t -> {
          if (Arrays.stream(t, 0, n).distinct().count() != n) {
            return false;
          }
          int sum = Arrays.stream(t, 0, n).sum();
          return rel == 0 ? sum == t[n] : rel == 1 ? sum <= t[n] : sum >= t[n];
        },
        concat(x, new IntVar[] {s}));
  }

  /** alldifferent([x, w]) and alldifferent([w, y]) propagated together on the bounds. */
  private static Model overlappingAlldiff(Store store, Random random) {
    int nw = 1 + random.nextInt(3);
    int nx = 1 + random.nextInt(2);
    int ny = 1 + random.nextInt(2);
    int hi = nw + Math.max(nx, ny) + random.nextInt(2);
    IntVar[] w = vars(store, "w", nw, 0, hi, random);
    IntVar[] x = vars(store, "x", nx, 0, hi, random);
    IntVar[] y = vars(store, "y", ny, 0, hi, random);
    IntVar[] s = concat(x, w);
    IntVar[] t = concat(w, y);
    return new Model(
        new OverlappingAlldiff(s, t),
        v ->
            Arrays.stream(v, 0, nx + nw).distinct().count() == nx + nw
                && Arrays.stream(v, nx, nx + nw + ny).distinct().count() == nw + ny,
        concat(x, w, y));
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

  private static Model alldiffExcept(Store store, Random random, boolean zero) {
    int n = 3 + random.nextInt(4);
    IntVar[] x = vars(store, "x", n, -1, n, random);
    IntervalDomain except = new IntervalDomain();
    if (zero) {
      except.unionAdapt(0, 0);
    } else {
      for (int k = random.nextInt(3); k > 0; k--) {
        int e = random.nextInt(n + 3) - 1;
        except.unionAdapt(e, e);
      }
    }
    return new Model(
        zero ? new AlldifferentExceptZero(x) : new AlldifferentExcept(x, except),
        t -> {
          int[] kept = Arrays.stream(t).filter(v -> !except.contains(v)).toArray();
          return Arrays.stream(kept).distinct().count() == kept.length;
        },
        x);
  }

  private static Model minMax(Store store, Random random, boolean min) {
    int n = 2 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, -3, 3, random);
    IntVar m = aVar(store, "m", -3, 3, random);
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
        // bounds consistency for an inequality (Beldiceanu et al.); an equality filters each side
        new Case("AlldiffSumLeGe", Level.BOUNDS_Z, (s, r) -> alldiffSum(s, r, true, true)),
        new Case("AlldiffSumEq", Level.NONE, (s, r) -> alldiffSum(s, r, false, true)),
        // without the Hall intervals the pruning must stay sound
        new Case(
            "AlldiffSumNoHall", Level.NONE, (s, r) -> alldiffSum(s, r, r.nextBoolean(), false)),
        new Case(
            "XplusYeqZ",
            Level.BOUNDS_Z,
            (s, r) -> xyz(s, r, small, XplusYeqZ::new, t -> t[0] + t[1] == t[2])),
        new Case(
            "XeqY",
            Level.DOMAIN,
            (s, r) -> {
              IntVar x = aVar(s, "x", -6, 6, r);
              IntVar y = aVar(s, "y", -6, 6, r);
              return new Model(new XeqY(x, y), t -> t[0] == t[1], new IntVar[] {x, y});
            }),
        new Case(
            "XlteqY",
            Level.DOMAIN,
            (s, r) -> {
              IntVar x = aVar(s, "x", -6, 6, r);
              IntVar y = aVar(s, "y", -6, 6, r);
              return new Model(new XlteqY(x, y), t -> t[0] <= t[1], new IntVar[] {x, y});
            }),
        new Case(
            "XneqY",
            Level.DOMAIN,
            (s, r) -> {
              IntVar x = aVar(s, "x", -3, 3, r);
              IntVar y = aVar(s, "y", -3, 3, r);
              return new Model(new XneqY(x, y), t -> t[0] != t[1], new IntVar[] {x, y});
            }),
        new Case(
            "XplusCeqZ",
            Level.DOMAIN,
            (s, r) -> {
              IntVar x = aVar(s, "x", -6, 6, r);
              IntVar z = aVar(s, "z", -4, 8, r);
              return new Model(new XplusCeqZ(x, 2, z), t -> t[0] + 2 == t[1], new IntVar[] {x, z});
            }),
        new Case(
            "XplusYeqC",
            Level.DOMAIN,
            (s, r) -> {
              IntVar x = aVar(s, "x", -6, 6, r);
              IntVar y = aVar(s, "y", -4, 8, r);
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
              IntVar x = aVar(s, "x", -4, 4, r);
              IntVar z = aVar(s, "z", -12, 12, r);
              return new Model(new XmulCeqZ(x, c, z), t -> t[0] * c == t[1], new IntVar[] {x, z});
            }),
        // exact least costs F_i(v) with the others in their intervals (Hochbaum's greedy)
        new Case("ConvexAllocation", Level.BOUNDS_Z, (s, r) -> convexAllocation(s, r, false)),
        // reduced costs only: sound, weaker
        new Case("ConvexAllocationLagrangian", Level.NONE, (s, r) -> convexAllocation(s, r, true)),
        // bounds(D) would need the holes of y, e.g. y = 2 is a hole between the supported 1 and 3
        new Case(
            "XdivYeqZ",
            Level.BOUNDS_Z,
            (s, r) ->
                xyz(
                    s,
                    r,
                    new int[] {-9, 9, -3, 3, -9, 9},
                    XdivYeqZ::new,
                    t -> t[1] != 0 && t[0] / t[1] == t[2])),
        // bounds(D) would need the holes of z, e.g. z.max() = 2 with remainder 2 only from x = 5
        new Case(
            "XmodYeqZ",
            Level.BOUNDS_Z,
            (s, r) ->
                xyz(
                    s,
                    r,
                    new int[] {-9, 9, -4, 4, -4, 4},
                    XmodYeqZ::new,
                    t -> t[1] != 0 && t[0] % t[1] == t[2])),
        // bounds(Z) above XexpYeqZ.SUPPORT_LIMIT pairs of x and y values, domain consistency below
        new Case(
            "XexpYeqZ",
            Level.BOUNDS_Z,
            (s, r) ->
                xyz(
                    s,
                    r,
                    new int[] {-4, 4, -3, 4, -30, 30},
                    XexpYeqZ::new,
                    ConsistencyChecker::pow)),
        new Case(
            "XexpYeqZ (even exponent)",
            Level.DOMAIN,
            (s, r) ->
                xyz(s, r, new int[] {-6, 6, 2, 2, -5, 40}, XexpYeqZ::new, ConsistencyChecker::pow)),
        new Case(
            "XexpYeqZ (odd exponent)",
            Level.DOMAIN,
            (s, r) ->
                xyz(
                    s,
                    r,
                    new int[] {-4, 4, 3, 3, -70, 70},
                    XexpYeqZ::new,
                    ConsistencyChecker::pow)),
        new Case(
            "XexpYeqZ (non-positive exponent)",
            Level.DOMAIN,
            (s, r) ->
                xyz(s, r, new int[] {-4, 4, -3, 0, -2, 2}, XexpYeqZ::new, ConsistencyChecker::pow)),
        new Case(
            "AbsXeqY (bounds)",
            Level.BOUNDS_Z,
            (s, r) -> {
              IntVar x = aVar(s, "x", -5, 5, r);
              IntVar y = aVar(s, "y", -2, 6, r);
              return new Model(
                  new AbsXeqY(x, y, false), t -> Math.abs(t[0]) == t[1], new IntVar[] {x, y});
            }),
        new Case(
            "AbsXeqY (domain)",
            Level.DOMAIN,
            (s, r) -> {
              IntVar x = aVar(s, "x", -5, 5, r);
              IntVar y = aVar(s, "y", -2, 6, r);
              return new Model(
                  new AbsXeqY(x, y, true), t -> Math.abs(t[0]) == t[1], new IntVar[] {x, y});
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
              IntVar sum = aVar(s, "s", -8, 8, r);
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
            "LinearBool watched",
            Level.BOUNDS_R,
            (s, r) -> linearBool(s, r, new String[] {"==", "<=", ">="}[r.nextInt(3)], true, true)),
        new Case(
            "XplusCneqZ",
            Level.DOMAIN,
            (s, r) -> {
              int c = r.nextInt(7) - 3;
              IntVar x = aVar(s, "x", -4, 4, r);
              IntVar z = aVar(s, "z", -4, 4, r);
              return new Model(new XplusCneqZ(x, c, z), t -> t[0] + c != t[1], new IntVar[] {x, z});
            }),
        new Case(
            "XplusClteqZImplied",
            Level.DOMAIN,
            (s, r) -> {
              int c = r.nextInt(7) - 3;
              IntVar b = r.nextBoolean() ? aBool(s, "b") : aVar(s, "b", 0, 1, r);
              IntVar x = aVar(s, "x", -4, 4, r);
              IntVar z = aVar(s, "z", -4, 4, r);
              return new Model(
                  new XplusClteqZImplied(b, x, c, z),
                  t -> t[0] == 0 || t[1] + c <= t[2],
                  new IntVar[] {b, x, z});
            }),
        new Case(
            "LinearIntDom",
            Level.DOMAIN,
            (s, r) -> linear(s, r, weights(r, 2 + r.nextInt(3), 3), "==", true)),
        // the sumsets alone, on equalities of up to five variables
        new Case(
            "LinearIntDom sumset",
            Level.DOMAIN,
            (s, r) -> {
              Model m = linear(s, r, weights(r, 2 + r.nextInt(4), 4), "==", true);
              ((LinearIntDom) m.constraint()).setSumsets("always");
              return m;
            }),
        new Case("AllDifferentLists", Level.NONE, (s, r) -> differentLists(s, r, false)),
        new Case("AllDifferentListsExcept", Level.NONE, (s, r) -> differentLists(s, r, true)),
        new Case("Alldiff", Level.BOUNDS_Z, (s, r) -> alldiff(s, r, false)),
        // bounds(Z) at all but about 1 node in 60,000: the paper's rule 3a is not applied
        new Case("OverlappingAlldiff", Level.NONE, ConsistencyChecker::overlappingAlldiff),
        new Case("Alldistinct", Level.DOMAIN, (s, r) -> alldiff(s, r, true)),
        new Case("Member", Level.DOMAIN, (s, r) -> member(s, r, "plain")),
        new Case("ReifiedMember", Level.DOMAIN, (s, r) -> member(s, r, "reified")),
        new Case("NotMember", Level.DOMAIN, (s, r) -> member(s, r, "not")),
        new Case("AlldifferentExcept", Level.DOMAIN, (s, r) -> alldiffExcept(s, r, false)),
        new Case("AlldifferentExceptZero", Level.DOMAIN, (s, r) -> alldiffExcept(s, r, true)),
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
              IntVar c = aVar(s, "c", 0, n, r);
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
              IntVar c = aVar(s, "c", 0, n, r);
              IntVar y = aVar(s, "y", 0, 2, r);
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
              IntVar c = aVar(s, "c", 0, n, r);
              return new Model(
                  new Among(x, new IntervalDomain(a, b), c),
                  t -> Arrays.stream(t, 0, n).filter(v -> a <= v && v <= b).count() == t[n],
                  concat(x, new IntVar[] {c}));
            }),
        new Case(
            "AmongSeq",
            Level.DOMAIN,
            (s, r) -> {
              int n = 2 + r.nextInt(6);
              int q = 1 + r.nextInt(n);
              int min = r.nextInt(q + 1);
              int max = min + r.nextInt(q + 1 - min);
              int a = r.nextInt(3);
              int b = a + r.nextInt(2);
              IntVar[] x = vars(s, "x", n, 0, 3, r);
              return new Model(
                  new AmongSeq(x, new IntervalDomain(a, b), q, min, max),
                  t -> {
                    for (int i = 0; i + q <= n; i++) {
                      int count = 0;
                      for (int j = i; j < i + q; j++) {
                        count += a <= t[j] && t[j] <= b ? 1 : 0;
                      }
                      if (count < min || count > max) {
                        return false;
                      }
                    }
                    return true;
                  },
                  x);
            }),
        // bounds on the intervals for count.max() (hitting sets) and domain pruning from the
        // matching for count.min(); a lower bound on the domains themselves is NP-hard
        new Case(
            "Values",
            Level.BOUNDS_Z,
            (s, r) -> {
              int n = 2 + r.nextInt(3);
              IntVar[] x = vars(s, "x", n, 0, 3, r);
              IntVar c = aVar(s, "c", 0, n + 1, r);
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
            "IncreasingSum",
            Level.BOUNDS_Z,
            (s, r) -> {
              boolean strict = r.nextBoolean();
              int n = 2 + r.nextInt(3);
              IntVar[] x = vars(s, "x", n, 0, 4, r);
              IntVar sum = aVar(s, "s", 0, 4 * n, r);
              return new Model(
                  new IncreasingSum(x, sum, strict),
                  t ->
                      IntStream.range(1, n)
                              .allMatch(i -> strict ? t[i - 1] < t[i] : t[i - 1] <= t[i])
                          && IntStream.range(0, n).map(i -> t[i]).sum() == t[n],
                  concat(x, new IntVar[] {sum}));
            }),
        new Case(
            "IncreasingNValue",
            Level.DOMAIN,
            (s, r) -> {
              int n = 2 + r.nextInt(4);
              IntVar[] x = vars(s, "x", n, 0, 5, r);
              IntVar count = aVar(s, "c", 0, n + 1, r);
              return new Model(
                  new IncreasingNValue(x, count),
                  t ->
                      IntStream.range(1, n).allMatch(i -> t[i - 1] <= t[i])
                          && 1 + IntStream.range(1, n).filter(i -> t[i - 1] < t[i]).count() == t[n],
                  concat(x, new IntVar[] {count}));
            }),
        new Case("Sort", Level.BOUNDS_Z, (s, r) -> sort(s, r, false)),
        new Case("InterDistance", Level.BOUNDS_Z, (s, r) -> interDistance(s, r, false)),
        // the same relation as one machine of equal-length tasks, for comparison
        new Case("InterDistanceUnary", Level.NONE, (s, r) -> interDistance(s, r, true)),
        new Case("MultiInterDistance", Level.BOUNDS_Z, ConsistencyChecker::multiInterDistance),
        new Case("SortPermutation", Level.BOUNDS_Z, (s, r) -> sort(s, r, true)),
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
        new Case("LexChain", Level.DOMAIN, (s, r) -> lexChain(s, r, true)),
        // m - 1 pairwise lex constraints, for comparison with LexChain
        new Case("LexChainPairwise", Level.NONE, (s, r) -> lexChain(s, r, false)),
        // bounds(Z) is NP-hard; the limit is not raised to the largest resource use either
        new Case("CumulativeBasic", Level.NONE, (s, r) -> cumulative(s, r, true)),
        new Case("Cumulative", Level.NONE, (s, r) -> cumulative(s, r, false)),
        new Case("HornFlow", Level.NONE, (s, r) -> cumulative(s, r, 2)),
        new Case("CumulativeOptional", Level.NONE, (s, r) -> cumulativeOptional(s, r, false)),
        new Case("CumulativeUnaryOptional", Level.NONE, (s, r) -> cumulativeOptional(s, r, true)),
        // relaxations (Eastman, Even and Isaacs; Moore and Hodgson), so no consistency level, but
        // never wrong pruning
        new Case(
            "WeightedCompletionParallel",
            Level.NONE,
            (s, r) -> {
              int n = 2 + r.nextInt(3);
              int capacity = 2 + r.nextInt(2);
              IntVar[] x = vars(s, "x", n, 0, 4, r);
              int[] d = r.ints(n, 0, 4).toArray();
              int[] use = r.ints(n, 0, capacity + 1).toArray();
              int[] w = r.ints(n, 0, 4).toArray();
              IntVar c = aVar(s, "c", 0, 40, r);
              return new Model(
                  new WeightedCompletion(x, d, use, w, capacity, c),
                  t -> {
                    int total = 0;
                    for (int i = 0; i < n; i++) {
                      total += w[i] * (t[i] + d[i]);
                      int load = 0;
                      for (int j = 0; j < n; j++) {
                        if (d[i] > 0 && d[j] > 0 && t[j] <= t[i] && t[i] < t[j] + d[j]) {
                          load += use[j];
                        }
                      }
                      if (load > capacity) {
                        return false;
                      }
                    }
                    return total <= t[n];
                  },
                  concat(x, new IntVar[] {c}));
            }),
        new Case(
            "LateCount",
            Level.NONE,
            (s, r) -> {
              int n = 2 + r.nextInt(3);
              IntVar[] x = vars(s, "x", n, 0, 5, r);
              int[] d = r.ints(n, 0, 4).toArray();
              int[] due = r.ints(n, 0, 8).toArray();
              IntVar c = aVar(s, "c", 0, n, r);
              return new Model(
                  new LateCount(x, d, due, c),
                  t -> {
                    int late = 0;
                    for (int i = 0; i < n; i++) {
                      late += t[i] + d[i] > due[i] ? 1 : 0;
                      for (int j = i + 1; j < n; j++) {
                        if (d[i] > 0 && d[j] > 0 && t[i] < t[j] + d[j] && t[j] < t[i] + d[i]) {
                          return false;
                        }
                      }
                    }
                    return late <= t[n];
                  },
                  concat(x, new IntVar[] {c}));
            }),
        // Geost sweeps for the first and last feasible origin, so it reaches no level on all
        // nodes; the counts of nodes at each level compare its strength with Diffn and Diff2
        new Case("GeostRect2d", Level.NONE, (s, r) -> geost(s, r, Family.RECT2D, null)),
        new Case(
            "Diffn(rect2d)", Level.NONE, (s, r) -> geost(s, r, Family.RECT2D, Rect.DIFFN_STRICT)),
        new Case("Diff2(rect2d)", Level.NONE, (s, r) -> geost(s, r, Family.RECT2D, Rect.DIFF2)),
        new Case("GeostPoly2d", Level.NONE, (s, r) -> geost(s, r, Family.POLY2D, null)),
        new Case("GeostArea", Level.NONE, (s, r) -> geost(s, r, Family.AREA, null)),
        new Case("GeostTime", Level.NONE, (s, r) -> geost(s, r, Family.TIME, null)),
        new Case("GeostSubdims", Level.NONE, (s, r) -> geost(s, r, Family.SUBDIMS, null)),
        // the bound on the cost is exact over the intervals; the starts are filtered by the
        // reduced cost of one path, which is weaker than bounds(Z)
        new Case("PrecedenceCost", Level.NONE, ConsistencyChecker::precedenceCost),
        // constraint audit, 2026-11-14: the constraints most often posted on the wide set that had
        // no case yet, in order of reach
        new Case("ReifiedLinear", Level.NONE, (s, r) -> reifiedLinear(s, r, false)),
        new Case("ImpliesLinear", Level.NONE, (s, r) -> reifiedLinear(s, r, true)),
        new Case("ChannelReif", Level.DOMAIN, (s, r) -> channel(s, r, true)),
        new Case("ChannelImply", Level.DOMAIN, (s, r) -> channel(s, r, false)),
        new Case("SumBool", Level.DOMAIN, ConsistencyChecker::sumBool),
        // redundant with the difference constraints posted on their own: it only fails earlier, so
        // the check is that it never fails while a solution exists
        new Case("DifferenceCycles", Level.NONE, ConsistencyChecker::differenceCycles),
        new Case("LexOrder", Level.DOMAIN, ConsistencyChecker::lexOrder),
        new Case("HybridTable", Level.DOMAIN, (s, r) -> hybridTable(s, r, false)),
        new Case("HybridTableShort", Level.DOMAIN, (s, r) -> hybridTable(s, r, true)),
        // constraint audit, 2026-11-15: constraints added to develop-5.0 since the last round
        new Case("BinaryBitTable", Level.DOMAIN, ConsistencyChecker::binaryBitTable),
        new Case(
            "ChannelOrder",
            SHARED_ORDER_LITERALS ? Level.NONE : Level.DOMAIN,
            ConsistencyChecker::channelOrder),
        new Case("ArgMax", Level.DOMAIN, (s, r) -> argMaxMonotone(s, r, false)),
        new Case(
            "ArgMin",
            Level.DOMAIN,
            (s, r) -> {
              IntVar[] x = vars(s, "x", 2 + r.nextInt(3), 0, 4, r);
              IntVar index = aVar(s, "i", 0, x.length - 1, r);
              return new Model(
                  new ArgMin(x, index, -1),
                  t -> {
                    int best = 0;
                    for (int k = 1; k < x.length; k++) {
                      if (t[k] < t[best]) {
                        best = k;
                      }
                    }
                    return t[x.length] == best;
                  },
                  concat(x, new IntVar[] {index}));
            }),
        new Case("ArgMaxMonotone", Level.DOMAIN, (s, r) -> argMaxMonotone(s, r, true)),
        new Case("ConditionalSelect", Level.BOUNDS_Z, ConsistencyChecker::conditionalSelect),
        new Case("MaxSimple", Level.BOUNDS_Z, (s, r) -> minMaxSimple(s, r, false)),
        new Case("MinSimple", Level.BOUNDS_Z, (s, r) -> minMaxSimple(s, r, true)),
        new Case("BoolClause", Level.DOMAIN, ConsistencyChecker::boolClause),
        new Case("CountValues", Level.NONE, ConsistencyChecker::countValues),
        new Case("SeqPrecedeChain", Level.DOMAIN, (s, r) -> seqPrecedeChain(s, r, false)),
        new Case("ValuePrecedeChain", Level.DOMAIN, (s, r) -> seqPrecedeChain(s, r, true)),
        // constraint audit round 2: the next constraints by wide-set reach without a case
        new Case("Regular", Level.DOMAIN, ConsistencyChecker::regular),
        new Case("Circuit", Level.NONE, (s, r) -> circuit(s, r, false)),
        new Case("Subcircuit", Level.NONE, (s, r) -> circuit(s, r, true)),
        new Case("Binpacking", Level.NONE, ConsistencyChecker::binpacking),
        new Case("Assignment", Level.NONE, ConsistencyChecker::assignment),
        new Case("CountValuesBounds", Level.NONE, ConsistencyChecker::countValuesBounds),
        new Case("CumulativeUnaryVar", Level.NONE, ConsistencyChecker::cumulativeUnary),
        new Case("EnergyPrecedence", Level.NONE, ConsistencyChecker::energyPrecedence),
        // round 4: globals posted by fewer wide-set instances
        new Case("AtMost", Level.DOMAIN, (s, r) -> atMostLeast(s, r, true)),
        new Case("AtLeast", Level.DOMAIN, (s, r) -> atMostLeast(s, r, false)),
        new Case("AllEqual", Level.DOMAIN, ConsistencyChecker::allEqual),
        new Case("XorBool", Level.DOMAIN, ConsistencyChecker::xorBool),
        new Case("AndBoolSimple", Level.DOMAIN, ConsistencyChecker::andBoolSimple),
        new Case("Knapsack", Level.NONE, ConsistencyChecker::knapsack),
        new Case(
            "SymmetricAlldifferentDomain", Level.DOMAIN, (s, r) -> symmetricAlldiff(s, r, true)),
        new Case(
            "SymmetricAlldifferentBounds", Level.NONE, (s, r) -> symmetricAlldiff(s, r, false)),
        new Case("ValuePrecede", Level.DOMAIN, ConsistencyChecker::valuePrecede),
        new Case("MinOfSums", Level.BOUNDS_Z, ConsistencyChecker::minOfSums),
        new Case("StockingCost", Level.NONE, ConsistencyChecker::stockingCost),
        new Case("CostAlldifferent", Level.NONE, ConsistencyChecker::costAlldifferent),
        new Case("CircuitCost", Level.NONE, ConsistencyChecker::circuitCost),
        new Case("Reachable", Level.DOMAIN, (s, r) -> graph(s, r, "reachable", false)),
        new Case("ReachableDirected", Level.NONE, (s, r) -> graph(s, r, "reachable", true)),
        new Case("Connected", Level.DOMAIN, (s, r) -> graph(s, r, "connected", false)),
        new Case("ConnectedDirected", Level.NONE, (s, r) -> graph(s, r, "connected", true)),
        new Case("Tree", Level.DOMAIN, (s, r) -> graph(s, r, "tree", false)),
        new Case("TreeDirected", Level.NONE, (s, r) -> graph(s, r, "tree", true)),
        new Case("Path", Level.NONE, (s, r) -> graph(s, r, "path", false)),
        new Case("PathDirected", Level.NONE, (s, r) -> graph(s, r, "path", true)),
        new Case("Forest", Level.NONE, (s, r) -> graph(s, r, "forest", false)),
        new Case("Table", Level.DOMAIN, (s, r) -> table(s, r, "table")),
        new Case("SimpleTable", Level.DOMAIN, (s, r) -> table(s, r, "simple")),
        new Case("NegativeTable", Level.DOMAIN, (s, r) -> table(s, r, "negative")),
        new Case("ExtensionalSupportMdd", Level.DOMAIN, (s, r) -> table(s, r, "mdd")),
        new Case("ExtensionalSupportStr", Level.DOMAIN, (s, r) -> table(s, r, "str")),
        new Case("ExtensionalSupportVa", Level.DOMAIN, (s, r) -> table(s, r, "va")),
        new Case("ExtensionalConflictVa", Level.DOMAIN, (s, r) -> table(s, r, "conflict")),
        new Case("TableReified", Level.DOMAIN, (s, r) -> table(s, r, "reified")),
        new Case("TableImplied", Level.DOMAIN, (s, r) -> table(s, r, "implied")),
        new Case("Sequence", Level.DOMAIN, ConsistencyChecker::sequence),
        new Case("Stretch", Level.DOMAIN, ConsistencyChecker::stretch),
        new Case("Same", Level.DOMAIN, (s, r) -> same(s, r, false)),
        new Case("UsedBy", Level.DOMAIN, (s, r) -> same(s, r, true)),
        new Case("ElementBool", Level.DOMAIN, ConsistencyChecker::elementBool),
        new Case("XorSystem", Level.DOMAIN, ConsistencyChecker::xorSystem),
        new Case("ExactCover", Level.NONE, ConsistencyChecker::exactCover),
        new Case("AmongVar", Level.NONE, ConsistencyChecker::amongVar),
        new Case("NoGood", Level.DOMAIN, ConsistencyChecker::noGood),
        new Case("Alternative", Level.NONE, (s, r) -> optionalIntervals(s, r, true)),
        new Case("Span", Level.NONE, (s, r) -> optionalIntervals(s, r, false)),
        new Case("DiffnK", Level.NONE, (s, r) -> diffnK(s, r, true)),
        new Case("DiffnKNonStrict", Level.NONE, (s, r) -> diffnK(s, r, false)),
        new Case("Deviation", Level.NONE, (s, r) -> deviation(s, r, false)),
        new Case("Spread", Level.NONE, (s, r) -> deviation(s, r, true)),
        new Case("SymmetricGCC", Level.NONE, ConsistencyChecker::symmetricGcc),
        new Case("CostGCC", Level.NONE, ConsistencyChecker::costGcc),
        new Case("Reservoir", Level.NONE, ConsistencyChecker::reservoir),
        new Case("GlobalCardinality", Level.NONE, (s, r) -> globalCardinality(s, r, true)),
        new Case("GlobalCardinalityBounds", Level.DOMAIN, (s, r) -> globalCardinality(s, r, false)),
        new Case("Alldifferent", Level.NONE, ConsistencyChecker::alldifferent),
        new Case("Decreasing", Level.DOMAIN, ConsistencyChecker::decreasing),
        new Case("CardinalityMatrix", Level.NONE, ConsistencyChecker::cardinalityMatrix),
        new Case("ConjunctionSum", Level.NONE, ConsistencyChecker::conjunctionSum),
        new Case("UnaryEarlinessTardiness", Level.NONE, ConsistencyChecker::unaryEarliness),
        new Case("Disjoint", Level.NONE, (s, r) -> disjoint(s, r, true)),
        new Case("Diff2Lengths", Level.NONE, (s, r) -> disjoint(s, r, false)),
        new Case("SubcircuitCost", Level.NONE, ConsistencyChecker::subcircuitCost),
        new Case("WeightedSubcircuits", Level.NONE, ConsistencyChecker::weightedSubcircuits),
        new Case("Routes", Level.NONE, ConsistencyChecker::routes),
        new Case("ArcTimes", Level.NONE, ConsistencyChecker::arcTimes),
        new Case("AndBool", Level.DOMAIN, (s, r) -> boolReif(s, r, "and")),
        new Case("OrBool", Level.DOMAIN, (s, r) -> boolReif(s, r, "or")),
        new Case("AndBoolVector", Level.DOMAIN, (s, r) -> boolReif(s, r, "andVector")),
        new Case("OrBoolVector", Level.DOMAIN, (s, r) -> boolReif(s, r, "orVector")),
        new Case("OrBoolWatched", Level.DOMAIN, (s, r) -> boolReif(s, r, "orWatched")),
        new Case("NorBoolWatched", Level.DOMAIN, (s, r) -> boolReif(s, r, "norWatched")),
        new Case("OrBoolSimple", Level.DOMAIN, (s, r) -> boolReif(s, r, "orSimple")),
        new Case("EqBool", Level.DOMAIN, (s, r) -> boolReif(s, r, "eq")),
        new Case("IfThenBool", Level.DOMAIN, ConsistencyChecker::ifThenBool),
        new Case("In(domain)", Level.DOMAIN, ConsistencyChecker::in),
        new Case("Sum(list)", Level.BOUNDS_Z, (s, r) -> weightedSum(s, r, false)),
        new Case("SumWeight", Level.NONE, (s, r) -> weightedSum(s, r, true)),
        new Case("MaxCliqueBound", Level.NONE, ConsistencyChecker::maxCliqueBound),
        new Case("DisjointConditional", Level.NONE, ConsistencyChecker::disjointConditional),
        new Case("TableCover", Level.NONE, ConsistencyChecker::tableCover),
        new Case("SoftAlldifferent", Level.NONE, ConsistencyChecker::softAlldifferent),
        new Case("CostRegular", Level.NONE, (s, r) -> costRegular(s, r, false)),
        new Case("MultiCostRegular", Level.NONE, (s, r) -> costRegular(s, r, true)),
        new Case("SoftGCC", Level.NONE, ConsistencyChecker::softGcc),
        new Case("IfThenElseBool", Level.DOMAIN, ConsistencyChecker::ifThenElseBool),
        new Case("SequenceMdd", Level.NONE, ConsistencyChecker::sequenceMdd),
        new Case("CostMdd", Level.NONE, ConsistencyChecker::costMdd),
        new Case("NetworkFlow(const)", Level.NONE, (s, r) -> networkFlow(s, r, false)),
        new Case("NetworkFlow(var weight)", Level.NONE, (s, r) -> networkFlow(s, r, true)),
        new Case(
            "Steiner(undirected)", Level.NONE, (s, r) -> weightedGraph(s, r, "steiner", false)),
        new Case("Steiner(directed)", Level.NONE, (s, r) -> weightedGraph(s, r, "steiner", true)),
        new Case(
            "WeightedSpanningTree(undirected)",
            Level.NONE,
            (s, r) -> weightedGraph(s, r, "spanning", false)),
        new Case(
            "WeightedSpanningTree(directed)",
            Level.NONE,
            (s, r) -> weightedGraph(s, r, "spanning", true)),
        new Case(
            "BoundedPath(undirected)", Level.NONE, (s, r) -> weightedGraph(s, r, "path", false)),
        new Case("BoundedPath(directed)", Level.NONE, (s, r) -> weightedGraph(s, r, "path", true)),
        new Case("ColouredSpanningTree", Level.NONE, ConsistencyChecker::colouredSpanningTree),
        new Case("KnapsackDP", Level.NONE, ConsistencyChecker::knapsackDP),
        new Case("SubcircuitCostPair", Level.NONE, ConsistencyChecker::subcircuitCostPair),
        // upper, lower and optional forms in turn; each instance enumerates a large box
        new Case(
            "Cumulatives",
            Level.NONE,
            (s, r) -> cumulatives(s, r, r.nextInt(3) != 1, r.nextInt(3) == 2)),
        new Case("UnaryTransition(all)", Level.NONE, (s, r) -> unaryTransition(s, r, false)),
        new Case("UnaryTransition(optional)", Level.NONE, (s, r) -> unaryTransition(s, r, true)),
        new Case("MultiCumulative", Level.NONE, ConsistencyChecker::multiCumulative),
        new Case("VectorBinpacking", Level.NONE, ConsistencyChecker::vectorBinpacking),
        new Case(
            "XmulYeqC",
            Level.DOMAIN,
            (s, r) -> {
              IntVar x = aVar(s, "x", -4, 4, r);
              IntVar y = aVar(s, "y", -4, 4, r);
              int c = r.nextInt(13) - 6;
              return new Model(
                  new org.jacop.constraints.XmulYeqC(x, y, c),
                  t -> t[0] * t[1] == c,
                  new IntVar[] {x, y});
            }),
        new Case(
            "XplusYgtC",
            Level.NONE,
            (s, r) -> {
              IntVar x = aVar(s, "x", -4, 4, r);
              IntVar y = aVar(s, "y", -4, 4, r);
              int c = r.nextInt(9) - 4;
              return new Model(
                  new org.jacop.constraints.XplusYgtC(x, y, c),
                  t -> t[0] + t[1] > c,
                  new IntVar[] {x, y});
            }),
        new Case(
            "XplusClteqZ",
            Level.NONE,
            (s, r) -> {
              IntVar x = aVar(s, "x", -4, 4, r);
              IntVar z = aVar(s, "z", -4, 4, r);
              int c = r.nextInt(7) - 3;
              return new Model(
                  new org.jacop.constraints.XplusClteqZ(x, c, z),
                  t -> t[0] + c <= t[1],
                  new IntVar[] {x, z});
            }));
  }

  /**
   * Disjoint (a rectangle of length 0 may not lie strictly inside another) or Diff2 (it overlaps
   * nothing): 2 or 3 rectangles in two dimensions with variable lengths.
   */
  private static Model disjoint(Store store, Random random, boolean disjoint) {
    int k = 2 + random.nextInt(2);
    List<IntVar> o1 = new ArrayList<>();
    List<IntVar> o2 = new ArrayList<>();
    List<IntVar> l1 = new ArrayList<>();
    List<IntVar> l2 = new ArrayList<>();
    IntVar[] all = new IntVar[4 * k];
    for (int i = 0; i < k; i++) {
      o1.add(aVar(store, "o" + i + "_0", 0, 2, random));
      o2.add(aVar(store, "o" + i + "_1", 0, 2, random));
      l1.add(aVar(store, "l" + i + "_0", 0, 2, random));
      l2.add(aVar(store, "l" + i + "_1", 0, 2, random));
      all[4 * i] = o1.get(i);
      all[4 * i + 1] = o2.get(i);
      all[4 * i + 2] = l1.get(i);
      all[4 * i + 3] = l2.get(i);
    }
    return new Model(
        disjoint
            ? new org.jacop.constraints.Disjoint(o1, o2, l1, l2, random.nextBoolean())
            : new org.jacop.constraints.Diff2(o1, o2, l1, l2, random.nextBoolean()),
        t -> {
          for (int i = 0; i < k; i++) {
            for (int j = i + 1; j < k; j++) {
              boolean apart = false;
              boolean empty = false;
              for (int dim = 0; dim < 2; dim++) {
                int oi = t[4 * i + dim];
                int li = t[4 * i + 2 + dim];
                int oj = t[4 * j + dim];
                int lj = t[4 * j + 2 + dim];
                apart |= oi + li <= oj || oj + lj <= oi;
                empty |= li == 0 || lj == 0;
              }
              if (!apart && (disjoint || !empty)) {
                return false;
              }
            }
          }
          return true;
        },
        all);
  }

  private static int[][] costMatrix(int n, Random random) {
    int[][] c = new int[n][n];
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        c[i][j] = random.nextInt(5);
      }
    }
    return c;
  }

  /** SubcircuitCost over 3 or 4 successors from 1; costs[i][i] is the cost of leaving i out. */
  private static Model subcircuitCost(Store store, Random random) {
    int n = 3 + random.nextInt(2);
    IntVar[] x = vars(store, "x", n, 1, n, random);
    int[][] c = costMatrix(n, random);
    IntVar cost = aVar(store, "cost", 0, 4 * n, random);
    return new Model(
        new org.jacop.constraints.SubcircuitCost(x, c, cost),
        t -> {
          if (!circuitHolds(t, n, true)) {
            return false;
          }
          int total = 0;
          for (int i = 0; i < n; i++) {
            total += c[i][t[i] - 1];
          }
          return t[n] == total;
        },
        concat(x, new IntVar[] {cost}));
  }

  /** WeightedSubcircuits over 3 or 4 successors from 1 with 2 tours. */
  private static Model weightedSubcircuits(Store store, Random random) {
    int n = 3 + random.nextInt(2);
    int tours = 2;
    IntVar[] x = vars(store, "x", n, 1, n, random);
    IntVar[] tour = vars(store, "t", n, 0, tours, random);
    int[][] c = costMatrix(n, random);
    IntVar[] tourCost = vars(store, "tc", tours, 0, 4 * n, random);
    IntVar cost = aVar(store, "cost", 0, 4 * n, random);
    return new Model(
        new org.jacop.constraints.WeightedSubcircuits(x, tour, c, tourCost, cost),
        t -> {
          boolean[] seen = new boolean[n];
          int total = 0;
          int[] perTour = new int[tours];
          for (int i = 0; i < n; i++) {
            int next = t[i] - 1;
            if (next < 0 || next >= n || seen[next]) {
              return false;
            }
            seen[next] = true;
            int k = t[n + i];
            if ((next == i) != (k == 0) || t[n + next] != k) {
              return false;
            }
            total += c[i][next];
            if (k > 0) {
              perTour[k - 1] += c[i][next];
            }
          }
          for (int k = 1; k <= tours; k++) {
            int start = -1;
            int size = 0;
            for (int i = 0; i < n; i++) {
              if (t[n + i] == k) {
                start = i;
                size++;
              }
            }
            if (start >= 0) {
              int len = 0;
              int i = start;
              do {
                i = t[i] - 1;
                len++;
              } while (i != start);
              if (len != size) {
                return false;
              }
            }
            if (t[2 * n + k - 1] != perTour[k - 1]) {
              return false;
            }
          }
          return t[2 * n + tours] == total;
        },
        concat(x, tour, tourCost, new IntVar[] {cost}));
  }

  /** Routes over 3 or 4 nodes, depot 0, on a random set of arcs with some self loops. */
  private static Model routes(Store store, Random random) {
    int nodes = 3 + random.nextInt(2);
    List<int[]> arcs = new ArrayList<>();
    for (int i = 0; i < nodes; i++) {
      for (int j = 0; j < nodes; j++) {
        if (i == j ? i > 0 && random.nextBoolean() : random.nextInt(4) > 0) {
          arcs.add(new int[] {i, j});
        }
      }
    }
    int m = arcs.size();
    // the constraint knows the nodes up to the largest one on an arc
    int n = arcs.stream().mapToInt(a -> Math.max(a[0], a[1])).max().orElse(0) + 1;
    int[] tails = arcs.stream().mapToInt(a -> a[0]).toArray();
    int[] heads = arcs.stream().mapToInt(a -> a[1]).toArray();
    IntVar[] lit = bools(store, "a", m);
    return new Model(
        new org.jacop.constraints.Routes(tails, heads, lit),
        t -> {
          int[] in = new int[n];
          int[] out = new int[n];
          boolean[] loop = new boolean[n];
          int[] parent = IntStream.range(0, n).toArray();
          for (int a = 0; a < m; a++) {
            if (t[a] == 1) {
              if (tails[a] == heads[a]) {
                loop[tails[a]] = true;
              } else {
                out[tails[a]]++;
                in[heads[a]]++;
                int u = tails[a];
                while (parent[u] != u) {
                  u = parent[u];
                }
                int v = heads[a];
                while (parent[v] != v) {
                  v = parent[v];
                }
                parent[u] = v;
              }
            }
          }
          int depot = 0;
          while (parent[depot] != depot) {
            depot = parent[depot];
          }
          for (int v = 1; v < n; v++) {
            boolean outside = loop[v] && in[v] == 0 && out[v] == 0;
            boolean inside = !loop[v] && in[v] == 1 && out[v] == 1;
            if (!outside && !inside) {
              return false;
            }
            if (inside) {
              int u = v;
              while (parent[u] != u) {
                u = parent[u];
              }
              if (u != depot) {
                return false;
              }
            }
          }
          return in[0] == out[0];
        },
        lit);
  }

  /** ArcTimes: x[v] = w + 1 implies t[w] >= t[v] + lag[v][w], over 3 nodes. */
  private static Model arcTimes(Store store, Random random) {
    int n = 3;
    IntVar[] x = vars(store, "x", n, 1, n, random);
    IntVar[] time = vars(store, "t", n, 0, 4, random);
    long[][] lag = new long[n][n];
    for (int v = 0; v < n; v++) {
      for (int w = 0; w < n; w++) {
        lag[v][w] = random.nextInt(4) - 1;
      }
    }
    return new Model(
        new org.jacop.constraints.ArcTimes(x, 1, time, lag),
        t -> {
          for (int v = 0; v < n; v++) {
            int w = t[v] - 1;
            if (t[n + w] < t[n + v] + lag[v][w]) {
              return false;
            }
          }
          return true;
        },
        concat(x, time));
  }

  /** GlobalCardinality over 3 or 4 variables, with counter variables or fixed bounds. */
  private static Model globalCardinality(Store store, Random random, boolean counters) {
    int n = 3 + random.nextInt(2);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    int[] values = IntStream.range(0, 4).filter(v -> random.nextBoolean()).toArray();
    if (values.length == 0) {
      values = new int[] {random.nextInt(4)};
    }
    int[] vs = values;
    int m = vs.length;
    if (counters) {
      IntVar[] c = vars(store, "c", m, 0, n, random);
      return new Model(
          new org.jacop.constraints.GlobalCardinality(x, vs, c),
          t -> {
            for (int k = 0; k < m; k++) {
              int value = vs[k];
              if (IntStream.range(0, n).filter(i -> t[i] == value).count() != t[n + k]) {
                return false;
              }
            }
            return true;
          },
          concat(x, c));
    }
    int[] low = new int[m];
    int[] up = new int[m];
    for (int k = 0; k < m; k++) {
      low[k] = random.nextInt(2);
      up[k] = low[k] + random.nextInt(3);
    }
    return new Model(
        new org.jacop.constraints.GlobalCardinality(x, vs, low, up),
        t -> {
          for (int k = 0; k < m; k++) {
            int value = vs[k];
            long count = IntStream.range(0, n).filter(i -> t[i] == value).count();
            if (count < low[k] || count > up[k]) {
              return false;
            }
          }
          return true;
        },
        x);
  }

  /** Alldifferent over 2 to 4 variables. */
  private static Model alldifferent(Store store, Random random) {
    IntVar[] x = vars(store, "x", 2 + random.nextInt(3), 0, 3, random);
    return new Model(
        new org.jacop.constraints.Alldifferent(x),
        t -> Arrays.stream(t).distinct().count() == t.length,
        x);
  }

  /** Decreasing, strict or not, over 2 to 4 variables. */
  private static Model decreasing(Store store, Random random) {
    IntVar[] x = vars(store, "x", 2 + random.nextInt(3), 0, 4, random);
    boolean strict = random.nextBoolean();
    return new Model(
        new org.jacop.constraints.Decreasing(x, strict),
        t -> {
          for (int i = 1; i < t.length; i++) {
            if (strict ? t[i] >= t[i - 1] : t[i] > t[i - 1]) {
              return false;
            }
          }
          return true;
        },
        x);
  }

  /** CardinalityMatrix of 2 rows and 2 or 3 columns over the values 0..2. */
  private static Model cardinalityMatrix(Store store, Random random) {
    int rows = 2;
    int cols = 2 + random.nextInt(2);
    int[] values = random.nextBoolean() ? new int[] {0, 1} : new int[] {1, 2};
    int m = values.length;
    IntVar[][] x = new IntVar[rows][];
    for (int r = 0; r < rows; r++) {
      x[r] = vars(store, "x" + r + "_", cols, 0, 2, random);
    }
    IntVar[][] rowCount = new IntVar[rows][];
    for (int r = 0; r < rows; r++) {
      rowCount[r] = vars(store, "r" + r + "_", m, 0, cols, random);
    }
    IntVar[][] colCount = new IntVar[cols][];
    for (int c = 0; c < cols; c++) {
      colCount[c] = vars(store, "k" + c + "_", m, 0, rows, random);
    }
    int cells = rows * cols;
    return new Model(
        new org.jacop.constraints.CardinalityMatrix(x, values, rowCount, colCount),
        t -> {
          for (int k = 0; k < m; k++) {
            for (int r = 0; r < rows; r++) {
              int count = 0;
              for (int c = 0; c < cols; c++) {
                count += t[r * cols + c] == values[k] ? 1 : 0;
              }
              if (count != t[cells + r * m + k]) {
                return false;
              }
            }
            for (int c = 0; c < cols; c++) {
              int count = 0;
              for (int r = 0; r < rows; r++) {
                count += t[r * cols + c] == values[k] ? 1 : 0;
              }
              if (count != t[cells + rows * m + c * m + k]) {
                return false;
              }
            }
          }
          return true;
        },
        concat(concat(x), concat(rowCount), concat(colCount)));
  }

  /** ConjunctionSum: sum bounds from below 1 to 3 weighted conjunctions over 3 variables. */
  private static Model conjunctionSum(Store store, Random random) {
    IntVar[] x = vars(store, "x", 3, 0, 2, random);
    int terms = 1 + random.nextInt(3);
    IntVar[][] termVars = new IntVar[terms][];
    int[][] termIndex = new int[terms][];
    int[][] termValues = new int[terms][];
    boolean[][] termEq = new boolean[terms][];
    int[] weights = new int[terms];
    for (int k = 0; k < terms; k++) {
      int size = 1 + random.nextInt(2);
      int first = random.nextInt(3);
      termIndex[k] = size == 1 ? new int[] {first} : new int[] {first, (first + 1) % 3};
      termVars[k] = new IntVar[size];
      termValues[k] = new int[size];
      termEq[k] = new boolean[size];
      for (int l = 0; l < size; l++) {
        termVars[k][l] = x[termIndex[k][l]];
        termValues[k][l] = random.nextInt(3);
        termEq[k][l] = random.nextInt(3) > 0;
      }
      weights[k] = random.nextInt(4);
    }
    IntVar sum = aVar(store, "sum", 0, 8, random);
    return new Model(
        new org.jacop.constraints.ConjunctionSum(termVars, termValues, termEq, weights, sum),
        t -> {
          int total = 0;
          for (int k = 0; k < terms; k++) {
            boolean holds = true;
            for (int l = 0; l < termIndex[k].length; l++) {
              holds &= (t[termIndex[k][l]] == termValues[k][l]) == termEq[k][l];
            }
            total += holds ? weights[k] : 0;
          }
          return t[3] >= total;
        },
        concat(x, new IntVar[] {sum}));
  }

  /** UnaryEarlinessTardiness: 2 or 3 tasks on one machine with a due date each. */
  private static Model unaryEarliness(Store store, Random random) {
    int n = 2 + random.nextInt(2);
    IntVar[] s = vars(store, "s", n, 0, 4, random);
    int[] p = new int[n];
    int[] due = new int[n];
    int[] early = new int[n];
    int[] late = new int[n];
    for (int i = 0; i < n; i++) {
      p[i] = 1 + random.nextInt(2);
      due[i] = random.nextInt(5);
      early[i] = random.nextInt(3);
      late[i] = random.nextInt(3);
    }
    IntVar cost = aVar(store, "cost", 0, 12, random);
    return new Model(
        new org.jacop.constraints.UnaryEarlinessTardiness(s, p, due, early, late, cost),
        t -> {
          int total = 0;
          for (int i = 0; i < n; i++) {
            for (int j = i + 1; j < n; j++) {
              if (t[i] < t[j] + p[j] && t[j] < t[i] + p[i]) {
                return false;
              }
            }
            total += early[i] * Math.max(0, due[i] - t[i]) + late[i] * Math.max(0, t[i] - due[i]);
          }
          return t[n] >= total;
        },
        concat(s, new IntVar[] {cost}));
  }

  /** at_most(k, x, v) or at_least(k, x, v) over 2 to 5 variables. */
  private static Model atMostLeast(Store store, Random random, boolean most) {
    int n = 2 + random.nextInt(4);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    int v = random.nextInt(4);
    int k = random.nextInt(n + 1);
    return new Model(
        most
            ? new org.jacop.constraints.AtMost(x, k, v)
            : new org.jacop.constraints.AtLeast(x, k, v),
        t -> {
          long c = Arrays.stream(t).filter(w -> w == v).count();
          return most ? c <= k : c >= k;
        },
        x);
  }

  private static Model allEqual(Store store, Random random) {
    IntVar[] x = vars(store, "x", 2 + random.nextInt(3), 0, 5, random);
    return new Model(
        new org.jacop.constraints.AllEqual(x), t -> Arrays.stream(t).distinct().count() == 1, x);
  }

  /** xor of 2 to 5 booleans equals y. */
  private static Model xorBool(Store store, Random random) {
    int n = 2 + random.nextInt(4);
    IntVar[] x = vars(store, "x", n, 0, 1, random);
    IntVar y = aVar(store, "y", 0, 1, random);
    return new Model(
        new org.jacop.constraints.XorBool(x, y),
        t -> (Arrays.stream(t, 0, n).sum() & 1) == t[n],
        concat(x, new IntVar[] {y}));
  }

  private static Model andBoolSimple(Store store, Random random) {
    IntVar[] x = vars(store, "x", 3, 0, 1, random);
    return new Model(
        new org.jacop.constraints.AndBoolSimple(x[0], x[1], x[2]), t -> (t[0] & t[1]) == t[2], x);
  }

  /** capacity = sum w * q and profit = sum p * q over 2 to 4 items with quantities 0..2. */
  private static Model knapsack(Store store, Random random) {
    int n = 2 + random.nextInt(3);
    int[] w = random.ints(n, 1, 4).toArray();
    int[] p = random.ints(n, 1, 5).toArray();
    IntVar[] q = vars(store, "q", n, 0, 2, random);
    IntVar cap = aVar(store, "c", 0, 12, random);
    IntVar profit = aVar(store, "p", 0, 16, random);
    return new Model(
        new org.jacop.constraints.knapsack.Knapsack(p, w, q, cap, profit),
        t -> {
          int sw = 0;
          int sp = 0;
          for (int i = 0; i < n; i++) {
            sw += w[i] * t[i];
            sp += p[i] * t[i];
          }
          return sw == t[n] && sp == t[n + 1];
        },
        concat(q, new IntVar[] {cap, profit}));
  }

  /** symmetric_all_different: x[x[i]] = i, numbered from 1, 2 to 6 variables. */
  private static Model symmetricAlldiff(Store store, Random random, boolean domain) {
    int n = 2 + random.nextInt(5);
    IntVar[] x = vars(store, "x", n, 1, n, random);
    return new Model(
        new org.jacop.constraints.SymmetricAlldifferent(x, 1, domain),
        t -> {
          for (int i = 0; i < n; i++) {
            if (t[i] < 1 || t[i] > n || t[t[i] - 1] != i + 1) {
              return false;
            }
          }
          return true;
        },
        x);
  }

  /** value_precede(s, t, x) over 2 to 5 variables on 0..3. */
  private static Model valuePrecede(Store store, Random random) {
    int n = 2 + random.nextInt(4);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    int s = random.nextInt(4);
    int u = (s + 1 + random.nextInt(3)) % 4;
    return new Model(
        new org.jacop.constraints.ValuePrecede(s, u, x),
        t -> {
          for (int v : t) {
            if (v == s) {
              return true;
            }
            if (v == u) {
              return false;
            }
          }
          return true;
        },
        x);
  }

  /** m = min(x[i] + y[i]), some terms without y. */
  private static Model minOfSums(Store store, Random random) {
    int n = 2 + random.nextInt(2);
    IntVar[] x = vars(store, "x", n, -2, 3, random);
    IntVar[] y = new IntVar[n];
    List<IntVar> vs = new ArrayList<>(Arrays.asList(x));
    int[] yIndex = new int[n];
    for (int i = 0; i < n; i++) {
      if (random.nextInt(3) > 0) {
        y[i] = aVar(store, "y" + i, -2, 3, random);
        yIndex[i] = vs.size();
        vs.add(y[i]);
      } else {
        yIndex[i] = -1;
      }
    }
    IntVar m = aVar(store, "m", -4, 6, random);
    int mIndex = vs.size();
    vs.add(m);
    return new Model(
        new org.jacop.constraints.MinOfSums(x, y, m),
        t -> {
          int best = Integer.MAX_VALUE;
          for (int i = 0; i < n; i++) {
            best = Math.min(best, t[i] + (yIndex[i] < 0 ? 0 : t[yIndex[i]]));
          }
          return best == t[mIndex];
        },
        vs.toArray(new IntVar[0]));
  }

  /** StockingCost over 2 to 4 orders, periods 0..4, capacity 1 or 2, random holding costs. */
  private static Model stockingCost(Store store, Random random) {
    int n = 2 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 0, 4, random);
    int[] due = random.ints(n, 1, 5).toArray();
    int[] h = random.ints(n, 1, 3).toArray();
    int cap = 1 + random.nextInt(2);
    IntVar cost = aVar(store, "cost", 0, 10, random);
    return new Model(
        new org.jacop.constraints.StockingCost(x, due, h, cost, cap),
        t -> {
          int[] load = new int[5];
          int c = 0;
          for (int i = 0; i < n; i++) {
            if (t[i] > due[i] || ++load[t[i]] > cap) {
              return false;
            }
            c += h[i] * (due[i] - t[i]);
          }
          return c <= t[n];
        },
        concat(x, new IntVar[] {cost}));
  }

  /** alldifferent with cost = sum costs[i][x[i] - 1], 2 to 4 variables on 1..4. */
  private static Model costAlldifferent(Store store, Random random) {
    int n = 2 + random.nextInt(3);
    int vals = n + random.nextInt(2);
    IntVar[] x = vars(store, "x", n, 1, vals, random);
    int[][] costs = new int[n][vals];
    for (int[] row : costs) {
      for (int j = 0; j < vals; j++) {
        row[j] = random.nextInt(4);
      }
    }
    IntVar cost = aVar(store, "cost", 0, 3 * n, random);
    return new Model(
        new org.jacop.constraints.CostAlldifferent(x, costs, cost),
        t -> {
          int c = 0;
          for (int i = 0; i < n; i++) {
            c += costs[i][t[i] - 1];
          }
          return c == t[n] && Arrays.stream(t, 0, n).distinct().count() == n;
        },
        concat(x, new IntVar[] {cost}));
  }

  /** circuit with cost = sum costs[i][x[i] - 1], 3 to 5 nodes, random (not symmetric) costs. */
  private static Model circuitCost(Store store, Random random) {
    int n = 3 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 1, n, random);
    int[][] costs = new int[n][n];
    boolean symmetric = random.nextBoolean();
    for (int i = 0; i < n; i++) {
      for (int j = symmetric ? i : 0; j < n; j++) {
        costs[i][j] = i == j ? 0 : 1 + random.nextInt(5);
        if (symmetric) {
          costs[j][i] = costs[i][j];
        }
      }
    }
    IntVar cost = aVar(store, "cost", 0, 5 * n, random);
    return new Model(
        new org.jacop.constraints.CircuitCost(x, costs, cost),
        t -> {
          int c = 0;
          for (int i = 0; i < n; i++) {
            if (t[i] < 1 || t[i] > n) {
              return false;
            }
            c += costs[i][t[i] - 1];
          }
          return c == t[n] && isCircuit(t, n);
        },
        concat(x, new IntVar[] {cost}));
  }

  /**
   * A graph global over a random graph of 3 to 5 nodes: node Booleans, edge Booleans and, for
   * reachable and tree, the root, for path the two ends.
   */
  private static Model graph(Store store, Random random, String kind, boolean directed) {
    int n = 3 + random.nextInt(3);
    int m = n - 1 + random.nextInt(4);
    int[] from = new int[m];
    int[] to = new int[m];
    for (int e = 0; e < m; e++) {
      from[e] = random.nextInt(n);
      to[e] = random.nextInt(10) == 0 ? from[e] : (from[e] + 1 + random.nextInt(n - 1)) % n;
    }
    IntVar[] ns = bools(store, "n", n);
    IntVar[] es = bools(store, "e", m);
    IntVar[] ends =
        switch (kind) {
          case "reachable", "tree" ->
              new IntVar[] {
                aVar(
                    store,
                    "r"
                        + java.util.Arrays.toString(from).replaceAll("[^0-9]+", "_")
                        + "T"
                        + java.util.Arrays.toString(to).replaceAll("[^0-9]+", "_"),
                    0,
                    n - 1,
                    random)
              };
          case "path" ->
              new IntVar[] {aVar(store, "s", 0, n - 1, random), aVar(store, "t", 0, n - 1, random)};
          default -> new IntVar[0];
        };
    Object constraint =
        switch (kind) {
          case "reachable" ->
              new org.jacop.constraints.graph.Reachable(from, to, ends[0], ns, es, directed);
          case "connected" ->
              new org.jacop.constraints.graph.Reachable(from, to, null, ns, es, directed);
          case "tree" -> new org.jacop.constraints.graph.Tree(from, to, ends[0], ns, es, directed);
          case "path" ->
              new org.jacop.constraints.graph.Path(from, to, ends[0], ends[1], ns, es, directed);
          default -> new org.jacop.constraints.graph.Forest(ns, es, from, to);
        };
    return new Model(
        constraint, t -> graphHolds(t, kind, directed, n, from, to), concat(concat(ns, es), ends));
  }

  private static Model weightedGraph(Store store, Random random, String kind, boolean directed) {
    int n = 3 + random.nextInt(2);
    int m = n - 1 + random.nextInt(3);
    int[] from = new int[m];
    int[] to = new int[m];
    int[] weights = new int[m];
    int total = 0;
    for (int e = 0; e < m; e++) {
      from[e] = random.nextInt(n);
      to[e] = (from[e] + 1 + random.nextInt(n - 1)) % n;
      weights[e] = random.nextInt(4);
      total += weights[e];
    }
    boolean spanning = kind.equals("spanning");
    IntVar[] ns = spanning ? new IntVar[0] : bools(store, "n", n);
    IntVar[] es = bools(store, "e", m);
    IntVar[] ends =
        kind.equals("path")
            ? new IntVar[] {aVar(store, "s", 0, n - 1, random), aVar(store, "t", 0, n - 1, random)}
            : new IntVar[] {aVar(store, "r", 0, n - 1, random)};
    IntVar cost = aVar(store, "cost", 0, total, random);
    Object constraint =
        switch (kind) {
          case "steiner" ->
              new org.jacop.constraints.graph.Steiner(
                  from, to, weights, ends[0], ns, es, cost, 0, directed);
          case "spanning" ->
              new org.jacop.constraints.graph.WeightedSpanningTree(
                  n, from, to, weights, ends[0], es, cost, 0, directed);
          default ->
              new org.jacop.constraints.graph.BoundedPath(
                  from, to, weights, ends[0], ends[1], ns, es, cost, 0, directed);
        };
    int offset = spanning ? n : 0;
    return new Model(
        constraint,
        t -> {
          int[] full = new int[t.length + offset];
          Arrays.fill(full, 0, offset, 1);
          System.arraycopy(t, 0, full, offset, t.length);
          int sum = 0;
          for (int e = 0; e < m; e++) {
            sum += full[n + e] * weights[e];
          }
          return sum == full[full.length - 1]
              && graphHolds(full, kind.equals("path") ? "path" : "tree", directed, n, from, to);
        },
        concat(concat(ns, es), concat(ends, new IntVar[] {cost})));
  }

  private static boolean graphHolds(
      int[] t, String kind, boolean directed, int n, int[] from, int[] to) {
    int m = from.length;
    int nodes = 0;
    int edges = 0;
    for (int i = 0; i < n; i++) {
      nodes += t[i];
    }
    for (int e = 0; e < m; e++) {
      if (t[n + e] == 1) {
        edges++;
        if (t[from[e]] == 0 || t[to[e]] == 0) {
          return false;
        }
      }
    }
    if (kind.equals("forest")) {
      int[] comp = new int[n];
      for (int i = 0; i < n; i++) {
        comp[i] = i;
      }
      for (int e = 0; e < m; e++) {
        if (t[n + e] == 1) {
          int a = comp[from[e]];
          int b = comp[to[e]];
          if (a == b) {
            return false;
          }
          for (int i = 0; i < n; i++) {
            if (comp[i] == b) {
              comp[i] = a;
            }
          }
        }
      }
      return true;
    }
    int root = kind.equals("connected") ? -1 : t[n + m];
    if (root >= 0 && t[root] == 0) {
      return false;
    }
    if (root < 0) {
      boolean some = false;
      for (int r = 0; r < n && !some; r++) {
        some = t[r] == 1 && reachesAll(t, r, directed, n, from, to);
      }
      return some;
    }
    if (!reachesAll(t, root, directed, n, from, to)) {
      return false;
    }
    if (kind.equals("reachable")) {
      return true;
    }
    if (edges != nodes - 1) {
      return false;
    }
    int[] in = new int[n];
    int[] out = new int[n];
    for (int e = 0; e < m; e++) {
      if (t[n + e] == 1) {
        out[from[e]]++;
        in[to[e]]++;
      }
    }
    if (kind.equals("tree")) {
      // a connected graph with one edge fewer than its nodes is a tree; directed: away from root
      for (int i = 0; directed && i < n; i++) {
        if (t[i] == 1 && in[i] != (i == root ? 0 : 1)) {
          return false;
        }
      }
      return true;
    }
    int last = t[n + m + 1];
    if (t[last] == 0) {
      return false;
    }
    for (int i = 0; i < n; i++) {
      if (t[i] == 0) {
        continue;
      }
      int ends = (i == root ? 1 : 0) + (i == last ? 1 : 0);
      if (directed) {
        int wantIn = i == root ? 0 : 1;
        int wantOut = i == last ? 0 : 1;
        if (root == last && i == root) {
          wantIn = 0;
          wantOut = 0;
        }
        if (in[i] != wantIn || out[i] != wantOut) {
          return false;
        }
      } else if (in[i] + out[i] != (root == last ? (i == root ? 0 : 2) : 2 - ends)) {
        return false;
      }
    }
    return true;
  }

  /** Whether every selected node is reached from r over the selected edges. */
  private static boolean reachesAll(int[] t, int r, boolean directed, int n, int[] from, int[] to) {
    boolean[] seen = new boolean[n];
    seen[r] = true;
    boolean grew = true;
    while (grew) {
      grew = false;
      for (int e = 0; e < from.length; e++) {
        if (t[n + e] == 1) {
          if (seen[from[e]] && !seen[to[e]]) {
            seen[to[e]] = true;
            grew = true;
          } else if (!directed && seen[to[e]] && !seen[from[e]]) {
            seen[from[e]] = true;
            grew = true;
          }
        }
      }
    }
    for (int i = 0; i < n; i++) {
      if (t[i] == 1 && !seen[i]) {
        return false;
      }
    }
    return true;
  }

  /** Whether the first n values, numbered from 1, are the successors of one Hamiltonian circuit. */
  private static boolean isCircuit(int[] t, int n) {
    boolean[] seen = new boolean[n];
    int i = 0;
    for (int len = 0; len < n; len++) {
      if (seen[i]) {
        return false;
      }
      seen[i] = true;
      i = t[i] - 1;
    }
    return i == 0;
  }

  /** CumulativeUnary over 3 or 4 tasks with variable durations and 0/1 resource uses. */
  private static Model cumulativeUnary(Store store, Random random) {
    int n = 3 + random.nextInt(2);
    IntVar[] s = vars(store, "s", n, 0, 5, random);
    IntVar[] d =
        IntStream.range(0, n)
            .mapToObj(i -> interval(store, "d" + i, 0, 3, random))
            .toArray(IntVar[]::new);
    IntVar[] r =
        IntStream.range(0, n)
            .mapToObj(i -> new IntVar(store, "r" + i, random.nextInt(3) == 0 ? 0 : 1, 1))
            .toArray(IntVar[]::new);
    boolean profile = random.nextBoolean();
    return new Model(
        new CumulativeUnary(s, d, r, new IntVar(store, 1, 1), profile),
        t -> {
          for (int i = 0; i < n; i++) {
            for (int j = i + 1; j < n; j++) {
              boolean both = t[2 * n + i] > 0 && t[2 * n + j] > 0 && t[n + i] > 0 && t[n + j] > 0;
              if (both && t[i] < t[j] + t[n + j] && t[j] < t[i] + t[n + i]) {
                return false;
              }
            }
          }
          return true;
        },
        concat(s, d, r));
  }

  /**
   * EnergyPrecedence over 4 tasks on one resource with random precedences between the tasks (lag
   * the duration or a random 0..2) and from every task to a makespan point; the relation is the
   * cumulative and the precedences.
   */
  private static Model energyPrecedence(Store store, Random random) {
    int n = 4;
    IntVar[] s = vars(store, "s", n, 0, 6, random);
    int[] dur = IntStream.range(0, n).map(i -> 1 + random.nextInt(3)).toArray();
    int[] use = IntStream.range(0, n).map(i -> 1 + random.nextInt(2)).toArray();
    IntVar[] d =
        IntStream.range(0, n)
            .mapToObj(i -> new IntVar(store, dur[i], dur[i]))
            .toArray(IntVar[]::new);
    IntVar[] h =
        IntStream.range(0, n)
            .mapToObj(i -> new IntVar(store, use[i], use[i]))
            .toArray(IntVar[]::new);
    int cap = 2 + random.nextInt(2);
    IntVar limit = new IntVar(store, cap, cap);
    IntVar m = aVar(store, "m", 3, 10, random);
    List<IntVar> from = new ArrayList<>();
    List<IntVar> to = new ArrayList<>();
    List<int[]> edges = new ArrayList<>(); // point from, point to (n = m), lag
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (random.nextInt(3) == 0) {
          edges.add(new int[] {i, j, random.nextBoolean() ? dur[i] : random.nextInt(3)});
        }
      }
      edges.add(new int[] {i, n, dur[i]});
    }
    IntVar[] point = concat(s, new IntVar[] {m});
    for (int[] e : edges) {
      from.add(point[e[0]]);
      to.add(point[e[1]]);
    }
    int[] lag = edges.stream().mapToInt(e -> e[2]).toArray();
    return new Model(
        new EnergyPrecedence(
            s, d, h, limit, from.toArray(new IntVar[0]), to.toArray(new IntVar[0]), lag),
        t -> {
          for (int[] e : edges) {
            if (t[e[1]] < t[e[0]] + e[2]) {
              return false;
            }
          }
          for (int time = 0; time <= 9; time++) {
            int load = 0;
            for (int i = 0; i < n; i++) {
              if (t[i] <= time && time < t[i] + dur[i]) {
                load += use[i];
              }
            }
            if (load > cap) {
              return false;
            }
          }
          return true;
        },
        point);
  }

  /** A random automaton of 2 to 4 states over 2 to 5 variables. */
  private static Model regular(Store store, Random random) {
    int states = 2 + random.nextInt(3);
    org.jacop.util.fsm.FsmState[] state = new org.jacop.util.fsm.FsmState[states];
    for (int i = 0; i < states; i++) {
      state[i] = new org.jacop.util.fsm.FsmState();
    }
    org.jacop.util.fsm.Fsm fsm = new org.jacop.util.fsm.Fsm();
    fsm.initState = state[0];
    boolean[] accepting = new boolean[states];
    List<int[]> arcs = new ArrayList<>(); // from, lo, hi, to
    for (int i = 0; i < states; i++) {
      fsm.allStates.add(state[i]);
      if (random.nextInt(3) == 0 || i == states - 1) {
        accepting[i] = true;
        fsm.finalStates.add(state[i]);
      }
      for (int t = 1 + random.nextInt(3); t > 0; t--) {
        int lo = random.nextInt(4);
        int hi = lo + random.nextInt(2);
        int to = random.nextInt(states);
        arcs.add(new int[] {i, lo, hi, to});
        state[i].addTransition(
            new org.jacop.util.fsm.FsmTransition(new IntervalDomain(lo, hi), state[to]));
      }
    }
    int n = 2 + random.nextInt(4);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    return new Model(
        new org.jacop.constraints.regular.Regular(fsm, x),
        t -> {
          boolean[] at = new boolean[states];
          at[0] = true;
          for (int v : t) {
            boolean[] next = new boolean[states];
            for (int[] a : arcs) {
              if (at[a[0]] && a[1] <= v && v <= a[2]) {
                next[a[3]] = true;
              }
            }
            at = next;
          }
          for (int i = 0; i < states; i++) {
            if (at[i] && accepting[i]) {
              return true;
            }
          }
          return false;
        },
        x);
  }

  /** circuit or subcircuit over 3 to 5 successor variables numbered from 1. */
  private static Model circuit(Store store, Random random, boolean sub) {
    int n = 3 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 1, n, random);
    return new Model(
        sub ? new org.jacop.constraints.Subcircuit(x) : new org.jacop.constraints.Circuit(x),
        t -> circuitHolds(t, n, sub),
        x);
  }

  /** Whether t[0..n-1], successors from 1, form a circuit (or a subcircuit when sub). */
  private static boolean circuitHolds(int[] t, int n, boolean sub) {
    // successors form a permutation whose non-fixed points make one cycle (all of them for
    // circuit)
    boolean[] seen = new boolean[n];
    int moving = 0;
    int start = -1;
    for (int i = 0; i < n; i++) {
      if (t[i] < 1 || t[i] > n || seen[t[i] - 1]) {
        return false;
      }
      seen[t[i] - 1] = true;
      if (t[i] != i + 1) {
        moving++;
        start = i;
      }
    }
    if (!sub && moving != n) {
      return false;
    }
    if (moving == 0) {
      return sub;
    }
    int len = 0;
    int i = start;
    do {
      i = t[i] - 1;
      len++;
    } while (i != start && len <= n);
    return len == moving;
  }

  /** load[b] = sum of w[i] over the items i with bin[i] = b, bins numbered from 0. */
  private static Model binpacking(Store store, Random random) {
    int items = 2 + random.nextInt(3);
    int bins = 2 + random.nextInt(2);
    IntVar[] bin = vars(store, "b", items, 0, bins - 1, random);
    int[] w = random.ints(items, 1, 4).toArray();
    int total = Arrays.stream(w).sum();
    IntVar[] load = vars(store, "l", bins, 0, Math.min(total, 6), random);
    return new Model(
        new org.jacop.constraints.binpacking.Binpacking(bin, load, w, 0),
        t -> {
          int[] sum = new int[bins];
          for (int i = 0; i < items; i++) {
            sum[t[i]] += w[i];
          }
          for (int b = 0; b < bins; b++) {
            if (sum[b] != t[items + b]) {
              return false;
            }
          }
          return true;
        },
        concat(bin, load));
  }

  /** d[x[i]] = i and x[d[i]] = i over 2 to 4 positions numbered from 0. */
  private static Model assignment(Store store, Random random) {
    int n = 2 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 0, n - 1, random);
    IntVar[] d = vars(store, "d", n, 0, n - 1, random);
    return new Model(
        new org.jacop.constraints.Assignment(x, d),
        t -> IntStream.range(0, n).allMatch(i -> t[n + t[i]] == i),
        concat(x, d));
  }

  /** lb[j] &lt;= number of x equal to values[j] &lt;= ub[j]. */
  private static Model countValuesBounds(Store store, Random random) {
    int n = 2 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    int k = 1 + random.nextInt(3);
    int[] values = random.ints(0, 4).distinct().limit(k).sorted().toArray();
    int[] lb = new int[k];
    int[] ub = new int[k];
    for (int j = 0; j < k; j++) {
      lb[j] = random.nextInt(2);
      ub[j] = lb[j] + random.nextInt(n);
    }
    return new Model(
        new org.jacop.constraints.CountValuesBounds(x, lb, ub, values),
        t -> {
          for (int j = 0; j < k; j++) {
            int v = values[j];
            long c = Arrays.stream(t).filter(e -> e == v).count();
            if (c < lb[j] || c > ub[j]) {
              return false;
            }
          }
          return true;
        },
        x);
  }

  private static IntVar[] bools(Store store, String prefix, int n) {
    return IntStream.range(0, n)
        .mapToObj(
            i -> {
              IntVar again = repeated(0, 1, true, false);
              return again != null ? again : pooled(new IntVar(store, prefix + i, 0, 1));
            })
        .toArray(IntVar[]::new);
  }

  /** b &lt;=&gt; (or b =&gt;) a linear constraint over 2 or 3 variables. */
  private static Model reifiedLinear(Store store, Random random, boolean implies) {
    int n = 2 + random.nextInt(2);
    IntVar[] x = vars(store, "x", n, -2, 3, random);
    int[] w = weights(random, n, 3);
    String rel = RELATIONS[random.nextInt(RELATIONS.length)];
    int c = random.nextInt(5) - 2;
    IntVar b = new IntVar(store, "b", 0, 1);
    LinearInt lin = new LinearInt(x, w, rel, c);
    Predicate<int[]> holds =
        t -> {
          long sum = 0;
          for (int i = 0; i < n; i++) {
            sum += (long) w[i] * t[i];
          }
          return holds(rel, sum, c);
        };
    Constraint con = implies ? new org.jacop.constraints.Implies(b, lin) : new Reified(lin, b);
    return new Model(
        con,
        t -> implies ? t[n] == 0 || holds.test(t) : (t[n] == 1) == holds.test(t),
        concat(x, new IntVar[] {b}));
  }

  /** b[i] &lt;=&gt; x = v[i] (or b[i] =&gt; x = v[i]) for distinct values, some outside x. */
  private static Model channel(Store store, Random random, boolean reif) {
    IntVar x = aVar(store, "x", 0, 5, random);
    int k = 2 + random.nextInt(4);
    int[] v = random.ints(-1, 7).distinct().limit(k).toArray();
    IntVar[] b = bools(store, "b", k);
    Constraint con =
        reif
            ? new org.jacop.constraints.ChannelReif(x, b, v)
            : new org.jacop.constraints.ChannelImply(x, b, v);
    return new Model(
        con,
        t -> {
          for (int i = 0; i < k; i++) {
            boolean eq = t[0] == v[i];
            if (reif ? (t[i + 1] == 1) != eq : t[i + 1] == 1 && !eq) {
              return false;
            }
          }
          return true;
        },
        concat(new IntVar[] {x}, b));
  }

  /** A relation between the sum of 2 to 6 0/1 variables and a variable. */
  private static Model sumBool(Store store, Random random) {
    int n = 2 + random.nextInt(5);
    IntVar[] b = bools(store, "b", n);
    IntVar s = aVar(store, "s", -1, n + 1, random);
    String rel = RELATIONS[random.nextInt(RELATIONS.length)];
    return new Model(
        new org.jacop.constraints.SumBool(b, rel, s),
        t -> holds(rel, Arrays.stream(t, 0, n).sum(), t[n]),
        concat(b, new IntVar[] {s}));
  }

  /** Difference constraints x - y &lt;= c over 3 or 4 nodes, some conditional on a 0/1 variable. */
  private static Model differenceCycles(Store store, Random random) {
    int nodes = 3 + random.nextInt(2);
    IntVar[] node = vars(store, "n", nodes, 0, 4, random);
    int arcs = 2 + random.nextInt(4);
    IntVar[] x = new IntVar[arcs];
    IntVar[] y = new IntVar[arcs];
    int[] from = new int[arcs];
    int[] to = new int[arcs];
    int[] c = new int[arcs];
    int[] lit = new int[arcs];
    IntVar[] b = new IntVar[arcs];
    int[] v = new int[arcs];
    List<IntVar> bs = new ArrayList<>();
    for (int a = 0; a < arcs; a++) {
      from[a] = random.nextInt(nodes);
      do {
        to[a] = random.nextInt(nodes);
      } while (to[a] == from[a]);
      x[a] = node[from[a]];
      y[a] = node[to[a]];
      c[a] = random.nextInt(6) - 3;
      lit[a] = -1;
      if (random.nextBoolean()) {
        b[a] = new IntVar(store, "b" + a, 0, 1);
        v[a] = random.nextInt(2);
        lit[a] = nodes + bs.size();
        bs.add(b[a]);
      }
    }
    return new Model(
        new DifferenceCycles(x, y, c, b, v),
        t -> {
          for (int a = 0; a < arcs; a++) {
            if ((lit[a] < 0 || t[lit[a]] == v[a]) && t[from[a]] - t[to[a]] > c[a]) {
              return false;
            }
          }
          return true;
        },
        concat(node, bs.toArray(IntVar[]::new)));
  }

  /** x &lt;=_lex y (or &lt;_lex) for vectors of 1 to 4 variables, possibly of different lengths. */
  private static Model lexOrder(Store store, Random random) {
    int nx = 1 + random.nextInt(4);
    int ny = random.nextInt(4) == 0 ? 1 + random.nextInt(4) : nx;
    IntVar[] x = vars(store, "x", nx, 0, 3, random);
    IntVar[] y = vars(store, "y", ny, 0, 3, random);
    boolean lt = random.nextBoolean();
    return new Model(
        new org.jacop.constraints.LexOrder(x, y, lt),
        t -> {
          for (int i = 0; i < Math.min(nx, ny); i++) {
            if (t[i] != t[nx + i]) {
              return t[i] < t[nx + i];
            }
          }
          return nx < ny || (nx == ny && !lt);
        },
        concat(x, y));
  }

  /**
   * A random table of 2 to 4 columns, plain or with unary restrictions (short and smart tables).
   */
  /*
   * b[i] <=> (x <= t[i]) when atMost[i], b[i] <=> (x > t[i]) otherwise, an implied item only the
   * implication b[i] => comparison. Items with their own 0/1 variables reach domain consistency;
   * with a shared one (consistency.sharedOrder=true, only soundness then) they do not reason
   * across the items, by design.
   */
  private static final boolean SHARED_ORDER_LITERALS =
      Boolean.getBoolean("consistency.sharedOrder");

  private static Model channelOrder(Store store, Random random) {
    IntVar x = aVar(store, "x", -2, 5, random);
    int k = 2 + random.nextInt(3);
    IntVar[] own = bools(store, "b", k);
    IntVar[] b = new IntVar[k];
    int[] t = new int[k];
    boolean[] atMost = new boolean[k];
    boolean[] implied = new boolean[k];
    for (int i = 0; i < k; i++) {
      b[i] =
          SHARED_ORDER_LITERALS && i > 0 && random.nextInt(4) == 0 ? b[random.nextInt(i)] : own[i];
      t[i] = random.nextInt(8) - 2;
      atMost[i] = random.nextBoolean();
      implied[i] = random.nextInt(3) == 0;
    }
    IntVar[] vars = new IntVar[k + 1];
    System.arraycopy(own, 0, vars, 0, k);
    vars[k] = x;
    int[] index = new int[k];
    for (int i = 0; i < k; i++) {
      index[i] = Arrays.asList(own).indexOf(b[i]);
    }
    return new Model(
        new org.jacop.constraints.ChannelOrder(x, b, t, atMost, implied),
        a -> {
          for (int i = 0; i < k; i++) {
            boolean holds = atMost[i] ? a[k] <= t[i] : a[k] > t[i];
            boolean bi = a[index[i]] == 1;
            if (implied[i] ? bi && !holds : bi != holds) {
              return false;
            }
          }
          return true;
        },
        vars);
  }

  private static Model binaryBitTable(Store store, Random random) {
    IntVar[] x = vars(store, "x", 2, -1, 4, random);
    int[][] tuples = new int[1 + random.nextInt(12)][];
    for (int t = 0; t < tuples.length; t++) {
      tuples[t] = new int[] {random.nextInt(7) - 1, random.nextInt(7) - 1};
    }
    return new Model(
        new org.jacop.constraints.table.BinaryBitTable(x[0], x[1], tuples),
        t -> Arrays.stream(tuples).anyMatch(row -> row[0] == t[0] && row[1] == t[1]),
        x);
  }

  /*
   * index = the first k with the largest f[k](x[k]); with monotone, f[k] is a random
   * nondecreasing table over an interval of x[k] (values of x[k] outside it are not allowed), and
   * otherwise ArgMax over x itself.
   */
  private static Model argMaxMonotone(Store store, Random random, boolean monotone) {
    int n = 2 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 0, 4, random);
    IntVar index = aVar(store, "i", 0, n - 1, random);
    int[][] f = new int[n][];
    int[] first = new int[n];
    for (int k = 0; k < n && monotone; k++) {
      if (random.nextInt(4) == 0) {
        continue;
      }
      first[k] = random.nextInt(2);
      f[k] = new int[3 + random.nextInt(3)];
      int v = random.nextInt(3);
      for (int u = 0; u < f[k].length; u++) {
        v += random.nextInt(3) == 0 ? 0 : random.nextInt(3);
        f[k][u] = v;
      }
    }
    Constraint c = monotone ? new ArgMaxMonotone(x, f, first, index, -1) : new ArgMax(x, index, -1);
    return new Model(
        c,
        t -> {
          int best = -1;
          long bestValue = Long.MIN_VALUE;
          for (int k = 0; k < n; k++) {
            long value;
            if (f[k] == null) {
              value = t[k];
            } else if (t[k] < first[k] || t[k] >= first[k] + f[k].length) {
              return false;
            } else {
              value = f[k][t[k] - first[k]];
            }
            if (value > bestValue) {
              bestValue = value;
              best = k;
            }
          }
          return t[n] == best;
        },
        concat(x, new IntVar[] {index}));
  }

  /** Alternative or span of a master over 1 to 3 optional intervals. */
  private static Model optionalIntervals(Store store, Random random, boolean alternative) {
    int k = 1 + random.nextInt(3);
    IntVar p0 = aBool(store, "mp");
    IntVar s0 = aVar(store, "ms", 0, 3, random);
    IntVar d0 = aVar(store, "md", 0, 2, random);
    IntVar[] p = bools(store, "p", k);
    IntVar[] st = vars(store, "s", k, 0, 3, random);
    IntVar[] d = vars(store, "d", k, 0, 2, random);
    return new Model(
        alternative
            ? new org.jacop.constraints.Alternative(p0, s0, d0, p, st, d)
            : new org.jacop.constraints.Span(p0, s0, d0, p, st, d),
        t -> {
          int present = 0;
          int first = Integer.MAX_VALUE;
          int last = Integer.MIN_VALUE;
          boolean same = false;
          for (int i = 0; i < k; i++) {
            if (t[3 + i] == 1) {
              present++;
              first = Math.min(first, t[3 + k + i]);
              last = Math.max(last, t[3 + k + i] + t[3 + 2 * k + i]);
              same = t[3 + k + i] == t[1] && t[3 + 2 * k + i] == t[2];
            }
          }
          if (t[0] == 0) {
            return present == 0 && t[2] == 0;
          }
          return alternative
              ? present == 1 && same
              : present >= 1 && t[1] == first && t[1] + t[2] == last;
        },
        concat(new IntVar[] {p0, s0, d0}, p, st, d));
  }

  /** Two or three boxes in two dimensions, strict or not. */
  private static Model diffnK(Store store, Random random, boolean strict) {
    int k = 2 + random.nextInt(2);
    IntVar[][] origin = new IntVar[k][];
    IntVar[][] length = new IntVar[k][];
    for (int i = 0; i < k; i++) {
      origin[i] = vars(store, "o" + i + "_", 2, 0, 2, random);
      length[i] = vars(store, "l" + i + "_", 2, 0, 2, random);
    }
    return new Model(
        new org.jacop.constraints.diffn.DiffnK(origin, length, strict),
        t -> {
          for (int i = 0; i < k; i++) {
            for (int j = i + 1; j < k; j++) {
              boolean apart = false;
              boolean empty = false;
              for (int dim = 0; dim < 2; dim++) {
                int oi = t[4 * i + dim];
                int li = t[4 * i + 2 + dim];
                int oj = t[4 * j + dim];
                int lj = t[4 * j + 2 + dim];
                apart |= oi + li <= oj || oj + lj <= oi;
                empty |= li == 0 || lj == 0;
              }
              if (!apart && (strict || !empty)) {
                return false;
              }
            }
          }
          return true;
        },
        IntStream.range(0, k)
            .mapToObj(i -> concat(origin[i], length[i]))
            .flatMap(Arrays::stream)
            .toArray(IntVar[]::new));
  }

  /** Deviation (L1) or spread (L2) of 2 to 4 variables with a fixed sum. */
  private static Model deviation(Store store, Random random, boolean spread) {
    int n = 2 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    int sum = random.nextInt(3 * n + 1);
    IntVar d = aVar(store, "d", 0, spread ? 40 : 14, random);
    return new Model(
        spread
            ? new org.jacop.constraints.Spread(x, sum, d)
            : new org.jacop.constraints.Deviation(x, sum, d),
        t -> {
          int total = 0;
          long dev = 0;
          for (int i = 0; i < n; i++) {
            total += t[i];
            long e = (long) n * t[i] - sum;
            dev += spread ? e * e : Math.abs(e);
          }
          return total == sum && dev == t[n];
        },
        concat(x, new IntVar[] {d}));
  }

  /** A 2x2 or 2x3 0/1 matrix with row and column counts. */
  private static Model symmetricGcc(Store store, Random random) {
    int n = 2;
    int m = 2 + random.nextInt(2);
    IntVar[][] x = new IntVar[n][];
    for (int i = 0; i < n; i++) {
      x[i] = bools(store, "x" + i + "_", m);
    }
    IntVar[] rows = vars(store, "r", n, 0, m, random);
    IntVar[] cols = vars(store, "c", m, 0, n, random);
    return new Model(
        new org.jacop.constraints.SymmetricGCC(x, rows, cols),
        t -> {
          for (int i = 0; i < n; i++) {
            int c = 0;
            for (int j = 0; j < m; j++) {
              c += t[i * m + j];
            }
            if (c != t[n * m + i]) {
              return false;
            }
          }
          for (int j = 0; j < m; j++) {
            int c = 0;
            for (int i = 0; i < n; i++) {
              c += t[i * m + j];
            }
            if (c != t[n * m + n + j]) {
              return false;
            }
          }
          return true;
        },
        concat(x[0], x[1], rows, cols));
  }

  /** CostGCC of 2 or 3 variables over 2 or 3 values. */
  private static Model costGcc(Store store, Random random) {
    int n = 2 + random.nextInt(2);
    int m = 2 + random.nextInt(2);
    int offset = random.nextInt(2);
    IntVar[] x = vars(store, "x", n, offset, offset + m - 1, random);
    int[][] costs = new int[n][m];
    for (int[] row : costs) {
      for (int j = 0; j < m; j++) {
        row[j] = random.nextInt(4);
      }
    }
    IntVar[] counters = vars(store, "c", m, 0, n, random);
    IntVar cost = aVar(store, "cost", 0, 3 * n, random);
    return new Model(
        new org.jacop.constraints.CostGCC(x, costs, counters, cost, offset),
        t -> {
          int[] count = new int[m];
          int c = 0;
          for (int i = 0; i < n; i++) {
            int j = t[i] - offset;
            if (j < 0 || j >= m) {
              return false;
            }
            count[j]++;
            c += costs[i][j];
          }
          for (int j = 0; j < m; j++) {
            if (count[j] != t[n + j]) {
              return false;
            }
          }
          return c == t[n + m];
        },
        concat(x, counters, new IntVar[] {cost}));
  }

  /** A reservoir of 2 to 4 events within [min, max], starting at level 0. */
  private static Model reservoir(Store store, Random random) {
    int n = 2 + random.nextInt(3);
    IntVar[] times = vars(store, "t", n, 0, 3, random);
    int[] changes = random.ints(n, -2, 3).toArray();
    int min = -random.nextInt(3);
    int max = random.nextInt(4);
    return new Model(
        new org.jacop.constraints.cumulative.Reservoir(times, changes, min, max),
        t -> {
          for (int i = 0; i < n; i++) {
            int level = 0;
            for (int j = 0; j < n; j++) {
              if (t[j] <= t[i]) {
                level += changes[j];
              }
            }
            if (level < min || level > max) {
              return false;
            }
          }
          return 0 >= min && 0 <= max;
        },
        times);
  }

  /** Sequence over 3 to 6 variables, windows of 2 or 3. */
  private static Model sequence(Store store, Random random) {
    int n = 3 + random.nextInt(4);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    int q = 2 + random.nextInt(2);
    int lo = random.nextInt(2);
    int hi = lo + random.nextInt(q - lo + 1);
    int a = random.nextInt(3);
    int b = a + random.nextInt(2);
    return new Model(
        new org.jacop.constraints.Sequence(x, new IntervalDomain(a, b), q, lo, hi),
        t -> {
          for (int i = 0; i + q <= n; i++) {
            int c = 0;
            for (int j = i; j < i + q; j++) {
              c += t[j] >= a && t[j] <= b ? 1 : 0;
            }
            if (c < lo || c > hi) {
              return false;
            }
          }
          return true;
        },
        x);
  }

  /** Stretch over 3 to 6 variables with 2 or 3 values. */
  private static Model stretch(Store store, Random random) {
    int n = 3 + random.nextInt(4);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    int k = 2 + random.nextInt(2);
    int[] values = new int[k];
    int[] min = new int[k];
    int[] max = new int[k];
    for (int i = 0; i < k; i++) {
      values[i] = i;
      min[i] = 1 + random.nextInt(2);
      max[i] = min[i] + random.nextInt(3);
    }
    return new Model(
        new org.jacop.constraints.Stretch(values, min, max, x),
        t -> {
          int i = 0;
          while (i < n) {
            int v = t[i];
            if (v < 0 || v >= k) {
              return false;
            }
            int j = i;
            while (j < n && t[j] == v) {
              j++;
            }
            if (j - i < min[v] || j - i > max[v]) {
              return false;
            }
            i = j;
          }
          return true;
        },
        x);
  }

  /** Same (y a permutation of x) or UsedBy (y a sub-multiset of x). */
  private static Model same(Store store, Random random, boolean usedBy) {
    int n = 2 + random.nextInt(3);
    int m = usedBy ? 1 + random.nextInt(n) : n;
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    IntVar[] y = vars(store, "y", m, 0, 3, random);
    return new Model(
        usedBy ? new org.jacop.constraints.UsedBy(x, y) : new org.jacop.constraints.Same(x, y),
        t -> {
          int[] count = new int[8];
          for (int i = 0; i < n; i++) {
            count[t[i] + 2]++;
          }
          for (int j = 0; j < m; j++) {
            count[t[n + j] + 2]--;
          }
          for (int c : count) {
            if (c < 0 || !usedBy && c != 0) {
              return false;
            }
          }
          return true;
        },
        concat(x, y));
  }

  /** ElementBool: list[index - offset - 1] = value over a 0/1 list. */
  private static Model elementBool(Store store, Random random) {
    int k = 2 + random.nextInt(5);
    int[] list = new int[k];
    for (int i = 0; i < k; i++) {
      list[i] = random.nextInt(2);
    }
    int offset = random.nextInt(3) - 1;
    IntVar index = aVar(store, "i", -1, k + 2, random);
    IntVar value = aVar(store, "v", -1, 2, random);
    return new Model(
        new org.jacop.constraints.ElementBool(index, list, value, offset),
        t -> {
          int p = t[0] - offset - 1;
          return p >= 0 && p < k && list[p] == t[1];
        },
        new IntVar[] {index, value});
  }

  /** A system of 1 to 3 parity rows over 3 to 6 Booleans. */
  private static Model xorSystem(Store store, Random random) {
    int n = 3 + random.nextInt(4);
    IntVar[] b = bools(store, "b", n);
    int rows = 1 + random.nextInt(3);
    int[][] index = new int[rows][];
    IntVar[][] vars = new IntVar[rows][];
    int[] parity = new int[rows];
    for (int r = 0; r < rows; r++) {
      int len = 1 + random.nextInt(Math.min(4, n));
      index[r] = random.ints(len, 0, n).toArray();
      vars[r] = Arrays.stream(index[r]).mapToObj(i -> b[i]).toArray(IntVar[]::new);
      parity[r] = random.nextInt(2);
    }
    return new Model(
        new org.jacop.constraints.XorSystem(vars, parity),
        t -> {
          for (int r = 0; r < rows; r++) {
            int sum = 0;
            for (int i : index[r]) {
              sum += t[i];
            }
            if (sum % 2 != parity[r]) {
              return false;
            }
          }
          return true;
        },
        b);
  }

  /** Exact cover of 2 to 5 elements by 2 to 7 options. */
  private static Model exactCover(Store store, Random random) {
    int n = 2 + random.nextInt(4);
    int k = 2 + random.nextInt(6);
    int[][] sets = new int[k][];
    for (int o = 0; o < k; o++) {
      sets[o] = random.ints(0, n).distinct().limit(1 + random.nextInt(n)).sorted().toArray();
    }
    IntVar[] x =
        IntStream.range(0, k)
            .mapToObj(i -> pooled(new IntVar(store, "o" + i, 0, 1)))
            .toArray(IntVar[]::new);
    return new Model(
        new org.jacop.constraints.ExactCover(x, sets, n),
        t -> {
          int[] covered = new int[n];
          for (int o = 0; o < k; o++) {
            if (t[o] == 1) {
              for (int e : sets[o]) {
                covered[e]++;
              }
            }
          }
          return Arrays.stream(covered).allMatch(c -> c == 1);
        },
        x);
  }

  /** AmongVar: n counts the x equal to some y. */
  private static Model amongVar(Store store, Random random) {
    int nx = 1 + random.nextInt(3);
    int ny = 1 + random.nextInt(2);
    IntVar[] x = vars(store, "x", nx, 0, 3, random);
    IntVar[] y = vars(store, "y", ny, 0, 3, random);
    IntVar count = aVar(store, "n", 0, nx, random);
    return new Model(
        new org.jacop.constraints.AmongVar(x, y, count),
        t -> {
          int c = 0;
          for (int i = 0; i < nx; i++) {
            for (int j = 0; j < ny; j++) {
              if (t[i] == t[nx + j]) {
                c++;
                break;
              }
            }
          }
          return c == t[nx + ny];
        },
        concat(x, y, new IntVar[] {count}));
  }

  /** NoGood: not every x_i equals v_i. */
  private static Model noGood(Store store, Random random) {
    int n = 1 + random.nextInt(4);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    int[] v = random.ints(n, 0, 4).toArray();
    return new Model(
        new org.jacop.constraints.NoGood(x, v),
        t -> {
          for (int i = 0; i < n; i++) {
            if (t[i] != v[i]) {
              return true;
            }
          }
          return false;
        },
        x);
  }

  /** A positive or negative table of 1 to 12 rows over 2 to 4 variables. */
  private static Model table(Store store, Random random, String kind) {
    int n = 2 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    int rows = 1 + random.nextInt(12);
    int[][] tuples = new int[rows][n];
    for (int[] row : tuples) {
      for (int i = 0; i < n; i++) {
        row[i] = random.nextInt(5) - 1;
      }
    }
    java.util.Set<List<Integer>> rowSet = new java.util.HashSet<>();
    for (int[] row : tuples) {
      rowSet.add(Arrays.stream(row).boxed().toList());
    }
    Predicate<int[]> in = t -> rowSet.contains(Arrays.stream(t).limit(n).boxed().toList());
    IntVar b = kind.equals("reified") || kind.equals("implied") ? aBool(store, "b") : null;
    Object constraint =
        switch (kind) {
          case "table" -> new org.jacop.constraints.table.Table(x, tuples);
          case "simple" -> new org.jacop.constraints.table.SimpleTable(x, tuples);
          case "negative" -> new org.jacop.constraints.table.NegativeTable(x, tuples);
          case "mdd" -> new org.jacop.constraints.ExtensionalSupportMdd(x, tuples);
          case "str" -> new org.jacop.constraints.ExtensionalSupportStr(x, tuples);
          case "va" -> new org.jacop.constraints.ExtensionalSupportVa(x, tuples);
          case "conflict" -> new org.jacop.constraints.ExtensionalConflictVa(x, tuples);
          case "reified" -> new org.jacop.constraints.table.TableReified(x, tuples, b);
          default -> new org.jacop.constraints.table.TableReified(x, tuples, b, true);
        };
    Predicate<int[]> relation =
        switch (kind) {
          case "negative", "conflict" -> in.negate();
          case "reified" -> t -> (t[n] == 1) == in.test(t);
          case "implied" -> t -> t[n] == 0 || in.test(t);
          default -> in;
        };
    return new Model(constraint, relation, b == null ? x : concat(x, new IntVar[] {b}));
  }

  private static Model hybridTable(Store store, Random random, boolean restrictions) {
    int n = 2 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    int rows = 1 + random.nextInt(10);
    if (!restrictions) {
      int[][] tuples = new int[rows][n];
      for (int[] row : tuples) {
        for (int i = 0; i < n; i++) {
          row[i] = random.nextInt(5) - 1;
        }
      }
      return new Model(
          new org.jacop.constraints.table.HybridTable(x, tuples),
          t -> Arrays.stream(tuples).anyMatch(row -> Arrays.equals(row, t)),
          x);
    }
    org.jacop.constraints.table.Restriction[][] tuples =
        new org.jacop.constraints.table.Restriction[rows][n];
    List<List<java.util.function.IntPredicate>> accept = new ArrayList<>();
    for (int r = 0; r < rows; r++) {
      List<java.util.function.IntPredicate> row = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        int a = random.nextInt(5) - 1;
        int b = random.nextInt(5) - 1;
        switch (random.nextInt(6)) {
          case 0 -> {
            tuples[r][i] = org.jacop.constraints.table.Restriction.any();
            row.add(w -> true);
          }
          case 1 -> {
            tuples[r][i] = org.jacop.constraints.table.Restriction.ne(a);
            row.add(w -> w != a);
          }
          case 2 -> {
            tuples[r][i] = org.jacop.constraints.table.Restriction.le(a);
            row.add(w -> w <= a);
          }
          case 3 -> {
            tuples[r][i] = org.jacop.constraints.table.Restriction.ge(a);
            row.add(w -> w >= a);
          }
          case 4 -> {
            tuples[r][i] = org.jacop.constraints.table.Restriction.in(a, b);
            row.add(w -> w == a || w == b);
          }
          default -> {
            tuples[r][i] = org.jacop.constraints.table.Restriction.eq(a);
            row.add(w -> w == a);
          }
        }
      }
      accept.add(row);
    }
    return new Model(
        new org.jacop.constraints.table.HybridTable(x, tuples),
        t ->
            accept.stream()
                .anyMatch(row -> IntStream.range(0, n).allMatch(i -> row.get(i).test(t[i]))),
        x);
  }

  /** y = x[k] for the first k with b[k] = 1, some k must have b[k] = 1. */
  private static Model conditionalSelect(Store store, Random random) {
    int n = 1 + random.nextInt(4);
    IntVar[] b = bools(store, "b", n);
    IntVar[] x = vars(store, "x", n, 0, 4, random);
    IntVar y = aVar(store, "y", 0, 4, random);
    return new Model(
        new ConditionalSelect(b, x, y),
        t -> {
          for (int i = 0; i < n; i++) {
            if (t[i] == 1) {
              return t[2 * n] == t[n + i];
            }
          }
          return false;
        },
        concat(b, x, new IntVar[] {y}));
  }

  private static Model minMaxSimple(Store store, Random random, boolean min) {
    IntVar[] x = vars(store, "x", 3, -2, 4, random);
    Constraint con =
        min
            ? new org.jacop.constraints.MinSimple(x[0], x[1], x[2])
            : new org.jacop.constraints.MaxSimple(x[0], x[1], x[2]);
    return new Model(con, t -> t[2] == (min ? Math.min(t[0], t[1]) : Math.max(t[0], t[1])), x);
  }

  /** or(x) \/ or(not y) over 0/1 variables, 0 to 4 of each, at least one in all. */
  private static Model boolClause(Store store, Random random) {
    int nx = random.nextInt(5);
    int ny = (nx == 0 ? 1 : 0) + random.nextInt(4);
    IntVar[] x = bools(store, "x", nx);
    IntVar[] y = bools(store, "y", ny);
    return new Model(
        new org.jacop.constraints.BoolClause(x, y),
        t ->
            IntStream.range(0, nx).anyMatch(i -> t[i] == 1)
                || IntStream.range(0, ny).anyMatch(i -> t[nx + i] == 0),
        concat(x, y));
  }

  /** counter[j] = number of x equal to values[j]. */
  private static Model countValues(Store store, Random random) {
    int n = 2 + random.nextInt(3);
    IntVar[] x = vars(store, "x", n, 0, 3, random);
    int k = 1 + random.nextInt(3);
    int[] values = random.ints(0, 4).distinct().limit(k).sorted().toArray();
    IntVar[] counter = vars(store, "c", k, 0, n, random);
    return new Model(
        new org.jacop.constraints.CountValues(x, counter, values),
        t -> {
          for (int j = 0; j < k; j++) {
            int v = values[j];
            if (IntStream.range(0, n).filter(i -> t[i] == v).count() != t[n + j]) {
              return false;
            }
          }
          return true;
        },
        concat(x, counter));
  }

  /** seq_precede_chain(x), or value_precede_chain(c, x) for a random chain. */
  private static Model seqPrecedeChain(Store store, Random random, boolean valueChain) {
    int n = 2 + random.nextInt(4);
    IntVar[] x = vars(store, "x", n, -1, 4, random);
    int[] chain =
        valueChain ? random.ints(-1, 5).distinct().limit(2 + random.nextInt(3)).toArray() : null;
    java.util.function.IntUnaryOperator rank =
        v -> {
          if (chain == null) {
            return Math.max(0, v);
          }
          for (int i = 0; i < chain.length; i++) {
            if (chain[i] == v) {
              return i + 1;
            }
          }
          return 0;
        };
    return new Model(
        new org.jacop.constraints.SeqPrecedeChain(x, chain),
        t -> {
          int m = 0;
          for (int v : t) {
            int r = rank.applyAsInt(v);
            if (r > m + 1) {
              return false;
            }
            m = Math.max(m, r);
          }
          return true;
        },
        x);
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
                      if (!REPEATED) {
                        // a repeated variable may weaken a propagator; only soundness is checked
                        assertThat(result.level())
                            .as(result.toString())
                            .isGreaterThanOrEqualTo(c.reaches());
                      }
                    }));
  }
}
