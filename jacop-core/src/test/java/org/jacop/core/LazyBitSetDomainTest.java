/*
 * LazyBitSetDomainTest.java
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

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.function.Supplier;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.XneqC;
import org.junit.jupiter.api.Test;

/**
 * Compares a variable with a lazy bit set domain against the same variable with an interval domain
 * under random pruning, new levels and backtracking: values, events, stamps, previous domains and
 * constraint lists must be the same after every step.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class LazyBitSetDomainTest {

  /** A variable that records the events it reports. */
  static final class RecordingVar extends IntVar {
    final List<Integer> events = new ArrayList<>();

    RecordingVar(Store store, String name, IntDomain dom) {
      super(store, name, dom);
    }

    @Override
    public void domainHasChanged(int event) {
      events.add(event);
      super.domainHasChanged(event);
    }
  }

  /** One side of the comparison: a store and its variable. */
  static final class Side {
    final Store store = new Store();
    final RecordingVar x;
    final Constraint[] constraints = new Constraint[6];
    final Constraint[] searchConstraints = new Constraint[6];

    Side(IntDomain dom) {
      x = new RecordingVar(store, "x", dom);
      for (int i = 0; i < constraints.length; i++) {
        constraints[i] = new XneqC(x, 1000 + i);
        searchConstraints[i] = new XneqC(x, 2000 + i);
      }
    }
  }

  private interface Step {
    void apply(Side side);
  }

  @Test
  void randomPruningMatchesIntervalDomain() {
    Random random = new Random(7);
    for (int run = 0; run < 3000; run++) {
      int lo = random.nextInt(200) - 100;
      int hi = lo + 64 + random.nextInt(run % 3 == 0 ? 300 : 80);
      Side reference = new Side(new IntervalDomain(lo, hi));
      Side lazy = new Side(new LazyBitSetDomain(lo, hi));
      int level = 0;
      for (int step = 0; step < 60; step++) {
        int action = random.nextInt(20);
        String context = "run " + run + " step " + step + " level " + level;
        if (action < 4) {
          level++;
          reference.store.setLevel(level);
          lazy.store.setLevel(level);
          continue;
        }
        if (action < 7 && level > 0) {
          backtrack(reference, level);
          backtrack(lazy, level);
          level--;
          compare(reference, lazy, level, context + " after backtracking");
          continue;
        }
        Step pruning = randomStep(random, reference.x.domain);
        context += " " + pruning;
        boolean referenceFailed = apply(reference, pruning);
        boolean lazyFailed = apply(lazy, pruning);
        assertThat(lazyFailed).as(context + " failure").isEqualTo(referenceFailed);
        assertThat(lazy.x.events).as(context + " events").isEqualTo(reference.x.events);
        reference.x.events.clear();
        lazy.x.events.clear();
        if (referenceFailed) {
          if (level == 0) {
            break;
          }
          backtrack(reference, level);
          backtrack(lazy, level);
          level--;
          compare(reference, lazy, level, context + " after failure");
        } else {
          compare(reference, lazy, level, context);
        }
      }
    }
  }

  /** The result of a domain operation, or the exception it throws, as a string. */
  private static String outcome(Supplier<IntDomain> operation) {
    try {
      return operation.get().toString();
    } catch (IllegalArgumentException e) {
      return e.toString();
    }
  }

  @Test
  void otherDomainsTreatItAsTheSameValues() {
    Random random = new Random(11);
    for (int run = 0; run < 3000; run++) {
      int lo = random.nextInt(100) - 50;
      int hi = lo + 64 + random.nextInt(100);
      Side lazy = new Side(new LazyBitSetDomain(lo, hi));
      for (int step = 0; step < 8; step++) {
        IntervalDomain values = randomDomain(random, lo, hi);
        apply(lazy, s -> s.x.domain.in(s.store.level, s.x, values));
      }
      IntDomain argument = lazy.x.domain;
      IntervalDomain same = ((LazyBitSetDomain) argument).toIntervalDomain();
      IntervalDomain other = randomDomain(random, lo - 10, hi + 10);
      IntDomain[] receivers = {
        other,
        toSmallDense(randomDomain(random, lo + 10, lo + 70)),
        new BoundDomain(lo + 5, hi - 5),
        lazyOf(randomDomain(random, lo - 10, hi + 10)),
        lazyOf(new IntervalDomain(lo - random.nextInt(20), hi + random.nextInt(20)))
      };
      for (IntDomain receiver : receivers) {
        IntDomain reference =
            receiver instanceof LazyBitSetDomain l ? l.toIntervalDomain() : receiver;
        String context = "run " + run + " " + receiver + " with " + argument;
        assertThat(receiver.intersect(argument).toString())
            .as(context + " intersect")
            .isEqualTo(reference.intersect(same).toString());
        assertThat(outcome(() -> receiver.union(argument)))
            .as(context + " union")
            .isEqualTo(outcome(() -> reference.union(same)));
        assertThat(receiver.subtract(argument).toString())
            .as(context + " subtract")
            .isEqualTo(reference.subtract(same).toString());
        assertThat(receiver.contains(argument))
            .as(context + " contains")
            .isEqualTo(reference.contains(same));
        assertThat(receiver.isIntersecting(argument))
            .as(context + " isIntersecting")
            .isEqualTo(reference.isIntersecting(same));
        assertThat(receiver.eq(argument)).as(context + " eq").isEqualTo(reference.eq(same));
        assertThat(receiver.sizeOfIntersection(argument))
            .as(context + " sizeOfIntersection")
            .isEqualTo(reference.sizeOfIntersection(same));
        if (receiver instanceof LazyBitSetDomain) {
          IntDomain small = toSmallDense(randomDomain(random, lo + 10, lo + 70));
          for (IntDomain plainArgument : new IntDomain[] {same, small}) {
            String with = context + " plain argument " + plainArgument;
            assertThat(receiver.contains(plainArgument))
                .as(with + " contains")
                .isEqualTo(reference.contains(plainArgument));
            assertThat(receiver.isIntersecting(plainArgument))
                .as(with + " isIntersecting")
                .isEqualTo(reference.isIntersecting(plainArgument));
            assertThat(receiver.eq(plainArgument))
                .as(with + " eq")
                .isEqualTo(reference.eq(plainArgument));
            assertThat(receiver.sizeOfIntersection(plainArgument))
                .as(with + " sizeOfIntersection")
                .isEqualTo(reference.sizeOfIntersection(plainArgument));
          }
        }
        int shift = random.nextInt(5) - 2;
        for (int kind = 0; kind < 2; kind++) {
          Side withArgument =
              new Side(
                  receiver instanceof LazyBitSetDomain l
                      ? lazyOf(l.toIntervalDomain())
                      : receiver.cloneLight());
          Side withSame = new Side(reference.cloneLight());
          withArgument.store.setLevel(1);
          withSame.store.setLevel(1);
          Step a =
              kind == 0
                  ? s -> s.x.domain.in(1, s.x, argument)
                  : s -> s.x.domain.inShift(1, s.x, argument, shift);
          Step b =
              kind == 0
                  ? s -> s.x.domain.in(1, s.x, same)
                  : s -> s.x.domain.inShift(1, s.x, same, shift);
          assertThat(apply(withArgument, a))
              .as(context + " in " + kind)
              .isEqualTo(apply(withSame, b));
          assertThat(withArgument.x.domain.toString())
              .as(context + " in " + kind)
              .isEqualTo(withSame.x.domain.toString());
          assertThat(withArgument.x.events)
              .as(context + " in events " + kind)
              .isEqualTo(withSame.x.events);
        }
      }
    }
  }

  private static SmallDenseDomain toSmallDense(IntervalDomain d) {
    SmallDenseDomain result = new SmallDenseDomain();
    for (int i = 0; i < d.noIntervals(); i++) {
      result.unionAdapt(d.getInterval(i).min(), d.getInterval(i).max());
    }
    return result;
  }

  private static void backtrack(Side side, int level) {
    side.store.removeLevel(level);
    side.store.setLevel(level - 1);
  }

  private static boolean apply(Side side, Step step) {
    try {
      step.apply(side);
      return false;
    } catch (FailException e) {
      return true;
    }
  }

  private static Step randomStep(Random random, IntDomain current) {
    int min = current.min();
    int max = current.max();
    int width = max - min + 1;
    int a = min - 3 + random.nextInt(width + 6);
    int b = min - 3 + random.nextInt(width + 6);
    int lo = Math.min(a, b);
    int hi = Math.max(a, b);
    int kind = random.nextInt(17);
    return switch (kind) {
      case 0 -> named("inMin " + a, s -> s.x.domain.inMin(s.store.level, s.x, a));
      case 1 -> named("inMax " + a, s -> s.x.domain.inMax(s.store.level, s.x, a));
      case 2 -> named("in " + lo + ".." + hi, s -> s.x.domain.in(s.store.level, s.x, lo, hi));
      case 3 -> named("inValue " + a, s -> s.x.domain.inValue(s.store.level, s.x, a));
      case 4, 5, 6 ->
          named("inComplement " + a, s -> s.x.domain.inComplement(s.store.level, s.x, a));
      case 7, 8 -> {
        int h = Math.min(hi, lo + random.nextInt(6));
        yield named(
            "inComplement " + lo + ".." + h,
            s -> s.x.domain.inComplement(s.store.level, s.x, lo, h));
      }
      case 9, 10 -> {
        IntervalDomain d = randomDomain(random, min - 2, max + 2);
        yield named("in " + d, s -> s.x.domain.in(s.store.level, s.x, d));
      }
      case 11 -> {
        IntervalDomain d = randomDomain(random, min - 7, max - 3);
        yield named("inShift 5 " + d, s -> s.x.domain.inShift(s.store.level, s.x, d, 5));
      }
      case 13 -> {
        LazyBitSetDomain d = lazyOf(randomDomain(random, min - 9, max + 2));
        int shift = random.nextInt(9) - 4;
        yield named(
            "inShift " + shift + " lazy " + d,
            s -> s.x.domain.inShift(s.store.level, s.x, d, shift));
      }
      case 12 -> {
        int c = random.nextInt(6);
        int event = random.nextInt(3);
        yield named("put " + c + " " + event, s -> s.x.putModelConstraint(s.constraints[c], event));
      }
      case 14 -> {
        int c = random.nextInt(6);
        yield named("put search " + c, s -> s.x.putSearchConstraint(s.searchConstraints[c]));
      }
      case 15 -> {
        // through the domain: Var.removeConstraint drops a search constraint removal made at a
        // new level, for every domain type, because it removes the constraint again from the
        // domain object it read before the first removal installed a new one
        int c = random.nextInt(6);
        yield named(
            "remove search " + c,
            s -> {
              s.x.domain.removeSearchConstraint(s.store.level, s.x, s.searchConstraints[c]);
              s.store.recordChange(s.x);
            });
      }
      default -> {
        int c = random.nextInt(6);
        yield named("remove " + c, s -> s.x.removeConstraint(s.constraints[c]));
      }
    };
  }

  /** A lazy bit set domain with the values of d, with holes when d has them. */
  private static LazyBitSetDomain lazyOf(IntervalDomain d) {
    LazyBitSetDomain result = new LazyBitSetDomain(d.min(), d.max());
    result.setDomain(d);
    return result;
  }

  private static IntervalDomain randomDomain(Random random, int lo, int hi) {
    IntervalDomain d = new IntervalDomain();
    int v = lo + random.nextInt(4);
    while (v <= hi) {
      int end = Math.min(hi, v + random.nextInt(Math.max(1, (hi - lo) / 3)));
      d.unionAdapt(v, end);
      v = end + 2 + random.nextInt(Math.max(1, (hi - lo) / 4));
    }
    if (d.isEmpty()) {
      d.unionAdapt(lo, lo);
    }
    return d;
  }

  private static Step named(String name, Step step) {
    return new Step() {
      @Override
      public void apply(Side side) {
        step.apply(side);
      }

      @Override
      public String toString() {
        return name;
      }
    };
  }

  private static void compare(Side reference, Side lazy, int level, String context) {
    IntDomain r = reference.x.domain;
    IntDomain l = lazy.x.domain;
    assertThat(l.domainId()).as(context).isEqualTo(IntDomain.LAZY_BIT_SET_DOMAIN_ID);
    assertThat(l.toString()).as(context + " values").isEqualTo(r.toString());
    assertThat(l.checkInvariants()).as(context + " invariants").isNull();
    assertThat(l.getSize()).as(context + " size").isEqualTo(r.getSize());
    assertThat(l.min()).as(context + " min").isEqualTo(r.min());
    assertThat(l.max()).as(context + " max").isEqualTo(r.max());
    assertThat(l.singleton()).as(context + " singleton").isEqualTo(r.singleton());
    assertThat(l.noIntervals()).as(context + " intervals").isEqualTo(r.noIntervals());
    for (int i = 0; i < r.noIntervals(); i++) {
      assertThat(l.getInterval(i)).as(context + " interval " + i).isEqualTo(r.getInterval(i));
    }
    List<Integer> values = new ArrayList<>();
    for (ValueEnumeration e = l.valueEnumeration(); e.hasMoreElements(); ) {
      values.add(e.nextElement());
    }
    List<Integer> expected = new ArrayList<>();
    for (ValueEnumeration e = r.valueEnumeration(); e.hasMoreElements(); ) {
      expected.add(e.nextElement());
    }
    assertThat(values).as(context + " enumeration").isEqualTo(expected);
    for (int k = 0; k < r.getSize(); k += 1 + r.getSize() / 7) {
      assertThat(l.getElementAt(k)).as(context + " element " + k).isEqualTo(r.getElementAt(k));
    }
    for (int v = r.min() - 2; v <= r.max() + 2; v++) {
      assertThat(l.contains(v)).as(context + " contains " + v).isEqualTo(r.contains(v));
      assertThat(l.nextValue(v)).as(context + " next " + v).isEqualTo(r.nextValue(v));
      assertThat(l.previousValue(v)).as(context + " previous " + v).isEqualTo(r.previousValue(v));
    }
    assertThat(l.stamp).as(context + " stamp").isEqualTo(r.stamp);
    IntDomain rp = r.getPreviousDomain();
    IntDomain lp = l.getPreviousDomain();
    assertThat(lp == null).as(context + " previous domain null").isEqualTo(rp == null);
    if (rp != null) {
      assertThat(lp.toString()).as(context + " previous domain").isEqualTo(rp.toString());
    }
    assertThat(l.recentDomainPruning(level).toString())
        .as(context + " recent pruning")
        .isEqualTo(r.recentDomainPruning(level).toString());
    assertThat(l.modelConstraintsToEvaluate)
        .as(context + " constraint counts")
        .isEqualTo(r.modelConstraintsToEvaluate);
    for (int event = 0; event < 3; event++) {
      for (int i = 0; i < r.modelConstraintsToEvaluate[event]; i++) {
        assertThat(indexOf(lazy, l.modelConstraints[event][i]))
            .as(context + " constraint " + event + " " + i)
            .isEqualTo(indexOf(reference, r.modelConstraints[event][i]));
      }
    }
    compareSearchConstraints(reference, lazy, context);
  }

  private static void compareSearchConstraints(Side reference, Side lazy, String context) {
    IntDomain r = reference.x.domain;
    IntDomain l = lazy.x.domain;
    assertThat(l.searchConstraintsToEvaluate)
        .as(context + " search constraint count")
        .isEqualTo(r.searchConstraintsToEvaluate);
    for (int i = 0; i < r.searchConstraintsToEvaluate; i++) {
      assertThat(indexOf(lazy, l.searchConstraints.get(i)))
          .as(context + " search constraint " + i)
          .isEqualTo(indexOf(reference, r.searchConstraints.get(i)));
    }
  }

  private static int indexOf(Side side, Constraint c) {
    for (int i = 0; i < side.constraints.length; i++) {
      if (side.constraints[i] == c) {
        return i;
      }
      if (side.searchConstraints[i] == c) {
        return 100 + i;
      }
    }
    return -1;
  }
}
