/*
 * DomainOperationsBruteForceTest.java
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

package org.jacop.core;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.Random;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.stream.Stream;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Compares the set operations of the integer domain implementations with the same operations on
 * plain sets of integers, for random small domains with holes. Every result is also checked for a
 * consistent representation: its size and its values must agree.
 */
class DomainOperationsBruteForceTest {

  private static final int TRIALS = 2000;

  /**
   * The values of the random domains: a small range with few intervals, and a range of 64 values
   * with many intervals that reaches both ends of the bits of a SmallDenseDomain.
   */
  private record Scale(String name, int minValue, int maxValue, int maxRuns, int maxRunLength) {}

  private static final Scale SMALL = new Scale("small", 0, 12, 3, 4);

  private static final Scale WIDE = new Scale("wide", -30, 33, 8, 8);

  static Stream<Arguments> kinds() {
    Stream.Builder<Arguments> kinds = Stream.builder();
    for (Scale scale : new Scale[] {SMALL, WIDE}) {
      kinds.add(
          Arguments.of(
              "IntervalDomain " + scale.name(),
              scale,
              (Function<TreeSet<Integer>, IntDomain>) s -> interval(s)));
      kinds.add(
          Arguments.of(
              "SmallDenseDomain " + scale.name(),
              scale,
              (Function<TreeSet<Integer>, IntDomain>) s -> smallDense(s)));
    }
    return kinds.build();
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("kinds")
  void operationsMatchSets(String name, Scale scale, Function<TreeSet<Integer>, IntDomain> kind) {
    Random random = new Random(name.hashCode());
    for (int trial = 0; trial < TRIALS; trial++) {
      TreeSet<Integer> a = randomSet(random, scale);
      TreeSet<Integer> b = randomSet(random, scale);
      int lo = randomValue(random, scale);
      int hi = lo + random.nextInt(scale.maxValue() + 1 - lo);
      // values just outside the range of the domains are queried too
      int value = scale.minValue() - 2 + random.nextInt(scale.maxValue() - scale.minValue() + 5);
      TreeSet<Integer> range = range(lo, hi);
      String context = "a=" + a + " b=" + b + " range=" + lo + ".." + hi + " value=" + value;

      // the argument domain is given in every representation that can hold it
      for (IntDomain db : arguments(b)) {
        IntDomain da = kind.apply(a);
        String c = context + " argument " + db.getClass().getSimpleName();
        check(da.union(db), union(a, b), "union(dom) " + c);
        check(da.intersect(db), intersect(a, b), "intersect(dom) " + c);
        check(da.subtract(db), subtract(a, b), "subtract(dom) " + c);
        assertThat(da.isIntersecting(db))
            .as("isIntersecting(dom) " + c)
            .isEqualTo(!intersect(a, b).isEmpty());
        assertThat(da.contains(db)).as("contains(dom) " + c).isEqualTo(a.containsAll(b));
        assertThat(da.eq(db)).as("eq(dom) " + c).isEqualTo(a.equals(b));
        assertThat(da.sizeOfIntersection(db))
            .as("sizeOfIntersection(dom) " + c)
            .isEqualTo(intersect(a, b).size());

        IntDomain adapted = kind.apply(a);
        adapted.unionAdapt(db);
        check(adapted, union(a, b), "unionAdapt(dom) " + c);

        adapted = kind.apply(a);
        adapted.addDom(db);
        check(adapted, union(a, b), "addDom(dom) " + c);

        adapted = kind.apply(a);
        adapted.intersectAdapt(db);
        check(adapted, intersect(a, b), "intersectAdapt(dom) " + c);
      }

      IntDomain da = kind.apply(a);
      check(da.union(lo, hi), union(a, range), "union(min, max) " + context);
      // a SmallDenseDomain can only grow within 64 values, so the added value is within the scale
      check(da.union(lo), union(a, range(lo, lo)), "union(value) " + context);
      check(da.intersect(lo, hi), intersect(a, range), "intersect(min, max) " + context);
      check(da.subtract(lo, hi), subtract(a, range), "subtract(min, max) " + context);
      check(da.subtract(value), subtract(a, range(value, value)), "subtract(value) " + context);
      assertThat(da.isIntersecting(lo, hi))
          .as("isIntersecting(min, max) " + context)
          .isEqualTo(!intersect(a, range).isEmpty());
      assertThat(da.contains(lo, hi))
          .as("contains(min, max) " + context)
          .isEqualTo(a.containsAll(range));
      assertThat(da.contains(value)).as("contains(value) " + context).isEqualTo(a.contains(value));
      Integer next = a.higher(value);
      assertThat(da.nextValue(value))
          .as("nextValue " + context)
          .isEqualTo(next == null ? value : next);
      Integer previous = a.lower(value);
      assertThat(da.previousValue(value))
          .as("previousValue " + context)
          .isEqualTo(previous == null ? value : previous);

      checkStructure(da, a, context);

      IntDomain adapted = kind.apply(a);
      adapted.unionAdapt(lo, hi);
      check(adapted, union(a, range), "unionAdapt(min, max) " + context);

      adapted = kind.apply(a);
      adapted.intersectAdapt(lo, hi);
      check(adapted, intersect(a, range), "intersectAdapt(min, max) " + context);

      adapted = kind.apply(a);
      adapted.subtractAdapt(lo, hi);
      check(adapted, subtract(a, range), "subtractAdapt(min, max) " + context);

      adapted = kind.apply(a);
      adapted.subtractAdapt(value);
      check(adapted, subtract(a, range(value, value)), "subtractAdapt(value) " + context);
    }
  }

  /** The pruning operations of a variable's domain, followed by backtracking to the old domain. */
  @ParameterizedTest(name = "{0}")
  @MethodSource("kinds")
  void pruningMatchesSetsAndBacktracks(
      String name, Scale scale, Function<TreeSet<Integer>, IntDomain> kind) {
    Random random = new Random(name.hashCode() + 1);
    for (int trial = 0; trial < TRIALS; trial++) {
      TreeSet<Integer> a = randomSet(random, scale);
      TreeSet<Integer> b = randomSet(random, scale);
      int lo = randomValue(random, scale);
      int hi = lo + random.nextInt(scale.maxValue() + 1 - lo);
      int value = randomValue(random, scale);
      int shift = random.nextInt(5) - 2;
      TreeSet<Integer> range = range(lo, hi);
      TreeSet<Integer> shifted = new TreeSet<>();
      b.forEach(v -> shifted.add(v + shift));
      String context =
          "a=" + a + " b=" + b + " range=" + lo + ".." + hi + " value=" + value + " shift=" + shift;

      prune(
          kind, a, intersect(a, range), "in(min, max) " + context, (d, l, v) -> d.in(l, v, lo, hi));
      for (IntDomain db : arguments(b)) {
        prune(
            kind,
            a,
            intersect(a, b),
            "in(dom) " + context + " argument " + db.getClass().getSimpleName(),
            (d, l, v) -> d.in(l, v, db));
        prune(
            kind,
            a,
            intersect(a, shifted),
            "inShift " + context + " argument " + db.getClass().getSimpleName(),
            (d, l, v) -> d.inShift(l, v, db, shift));
      }
      prune(
          kind,
          a,
          subtract(a, range),
          "inComplement(min, max) " + context,
          (d, l, v) -> d.inComplement(l, v, lo, hi));
      prune(
          kind,
          a,
          subtract(a, range(value, value)),
          "inComplement(value) " + context,
          (d, l, v) -> d.inComplement(l, v, value));
      prune(
          kind,
          a,
          intersect(a, range(value, scale.maxValue())),
          "inMin " + context,
          (d, l, v) -> d.inMin(l, v, value));
      prune(
          kind,
          a,
          intersect(a, range(scale.minValue(), value)),
          "inMax " + context,
          (d, l, v) -> d.inMax(l, v, value));
      prune(
          kind,
          a,
          intersect(a, range(value, value)),
          "inValue " + context,
          (d, l, v) -> d.inValue(l, v, value));
    }
  }

  private interface Pruning {
    void apply(IntDomain domain, int level, IntVar var);
  }

  /**
   * Prunes a variable with domain a at a new store level, checks the result (an empty result must
   * fail), then removes the level and checks that the domain is a again.
   */
  private static void prune(
      Function<TreeSet<Integer>, IntDomain> kind,
      TreeSet<Integer> a,
      TreeSet<Integer> expected,
      String operation,
      Pruning pruning) {
    pruneAtNewLevel(kind, a, expected, operation, pruning);
    pruneAtSameLevel(kind, a, expected, operation, pruning);
  }

  /**
   * Prunes a variable whose domain has already been changed at the current level, so the domain may
   * be changed in place: the domain is a with one more value, which is removed first.
   */
  private static void pruneAtSameLevel(
      Function<TreeSet<Integer>, IntDomain> kind,
      TreeSet<Integer> a,
      TreeSet<Integer> expected,
      String operation,
      Pruning pruning) {
    Integer extra = null;
    for (int v = a.first() - 1; v <= a.last() + 1 && extra == null; v++) {
      if (!a.contains(v) && v - Math.min(v, a.first()) < 63 && Math.max(v, a.last()) - v < 63) {
        extra = v;
      }
    }
    if (extra == null) {
      return;
    }
    TreeSet<Integer> initial = union(a, range(extra, extra));
    Store store = new Store();
    IntVar x = new IntVar(store, "x", kind.apply(initial));
    store.setLevel(1);
    x.domain.inComplement(store.level, x, extra);
    check(x.domain, a, operation + " (same level) removal of " + extra);
    boolean failed = false;
    try {
      pruning.apply(x.domain, store.level, x);
    } catch (FailException e) {
      failed = true;
    }
    assertThat(failed).as(operation + " (same level) failure").isEqualTo(expected.isEmpty());
    if (!failed) {
      check(x.domain, expected, operation + " (same level)");
    }
    store.removeLevel(1);
    store.setLevel(0);
    check(x.domain, initial, operation + " (same level) after backtracking");
  }

  private static void pruneAtNewLevel(
      Function<TreeSet<Integer>, IntDomain> kind,
      TreeSet<Integer> a,
      TreeSet<Integer> expected,
      String operation,
      Pruning pruning) {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", kind.apply(a));
    store.setLevel(1);
    boolean failed = false;
    try {
      pruning.apply(x.domain, store.level, x);
    } catch (FailException e) {
      failed = true;
    }
    assertThat(failed).as(operation + " failure").isEqualTo(expected.isEmpty());
    if (!failed) {
      check(x.domain, expected, operation);
    }
    store.removeLevel(1);
    store.setLevel(0);
    check(x.domain, a, operation + " after backtracking");
  }

  private static void check(IntDomain domain, TreeSet<Integer> expected, String operation) {
    TreeSet<Integer> actual = new TreeSet<>();
    for (ValueEnumeration e = domain.valueEnumeration(); e.hasMoreElements(); ) {
      actual.add(e.nextElement());
    }
    assertThat(actual).as(operation + " gave " + domain).isEqualTo(expected);
    assertThat(domain.getSize()).as(operation + " size of " + domain).isEqualTo(expected.size());
    assertThat(domain.isEmpty())
        .as(operation + " isEmpty of " + domain)
        .isEqualTo(expected.isEmpty());
    if (!expected.isEmpty()) {
      assertThat(domain.min()).as(operation + " min of " + domain).isEqualTo(expected.first());
      assertThat(domain.max()).as(operation + " max of " + domain).isEqualTo(expected.last());
    }
  }

  /**
   * Checks the interval structure of a domain against its values: the intervals, the elements by
   * position and both enumerations.
   */
  private static void checkStructure(IntDomain domain, TreeSet<Integer> expected, String context) {
    java.util.List<Interval> runs = new java.util.ArrayList<>();
    for (int v : expected) {
      if (!runs.isEmpty() && runs.get(runs.size() - 1).max() == v - 1) {
        runs.set(runs.size() - 1, new Interval(runs.get(runs.size() - 1).min(), v));
      } else {
        runs.add(new Interval(v, v));
      }
    }
    assertThat(domain.noIntervals()).as("noIntervals " + context).isEqualTo(runs.size());
    java.util.List<Interval> enumerated = new java.util.ArrayList<>();
    for (IntervalEnumeration e = domain.intervalEnumeration(); e.hasMoreElements(); ) {
      enumerated.add(e.nextElement());
    }
    assertThat(enumerated).as("intervalEnumeration " + context).isEqualTo(runs);
    for (int i = 0; i < runs.size(); i++) {
      assertThat(domain.getInterval(i))
          .as("getInterval " + i + " " + context)
          .isEqualTo(runs.get(i));
      assertThat(domain.leftElement(i)).as("leftElement " + context).isEqualTo(runs.get(i).min());
      assertThat(domain.rightElement(i)).as("rightElement " + context).isEqualTo(runs.get(i).max());
    }
    int position = 0;
    for (int v : expected) {
      assertThat(domain.getElementAt(position++)).as("getElementAt " + context).isEqualTo(v);
    }
    assertThat(domain.toIntArray())
        .as("toIntArray " + context)
        .isEqualTo(expected.stream().mapToInt(Integer::intValue).toArray());
    if (domain instanceof SmallDenseDomain dense) {
      check(dense.toIntervalDomain(), expected, "toIntervalDomain " + context);
    }
  }

  /** The domain b in every representation able to hold it exactly. */
  private static IntDomain[] arguments(TreeSet<Integer> b) {
    if (b.last() - b.first() + 1 == b.size()) {
      return new IntDomain[] {interval(b), smallDense(b), new BoundDomain(b.first(), b.last())};
    }
    return new IntDomain[] {interval(b), smallDense(b)};
  }

  private static IntDomain interval(TreeSet<Integer> values) {
    IntervalDomain d = new IntervalDomain();
    values.forEach(v -> d.unionAdapt(v, v));
    return d;
  }

  private static IntDomain smallDense(TreeSet<Integer> values) {
    SmallDenseDomain d = new SmallDenseDomain();
    values.forEach(v -> d.unionAdapt(v, v));
    return d;
  }

  /**
   * A random non-empty subset of the values of the scale, made of a few runs so that it has holes.
   */
  private static TreeSet<Integer> randomSet(Random random, Scale scale) {
    TreeSet<Integer> set = new TreeSet<>();
    int runs = 1 + random.nextInt(scale.maxRuns());
    for (int r = 0; r < runs; r++) {
      int min = randomValue(random, scale);
      int max = Math.min(scale.maxValue(), min + random.nextInt(scale.maxRunLength()));
      set.addAll(range(min, max));
    }
    return set;
  }

  private static int randomValue(Random random, Scale scale) {
    return scale.minValue() + random.nextInt(scale.maxValue() - scale.minValue() + 1);
  }

  private static TreeSet<Integer> range(int min, int max) {
    TreeSet<Integer> set = new TreeSet<>();
    for (int v = min; v <= max; v++) {
      set.add(v);
    }
    return set;
  }

  private static TreeSet<Integer> union(TreeSet<Integer> a, TreeSet<Integer> b) {
    TreeSet<Integer> result = new TreeSet<>(a);
    result.addAll(b);
    return result;
  }

  private static TreeSet<Integer> intersect(TreeSet<Integer> a, TreeSet<Integer> b) {
    TreeSet<Integer> result = new TreeSet<>(a);
    result.retainAll(b);
    return result;
  }

  private static TreeSet<Integer> subtract(TreeSet<Integer> a, TreeSet<Integer> b) {
    TreeSet<Integer> result = new TreeSet<>(a);
    result.removeAll(b);
    return result;
  }
}
