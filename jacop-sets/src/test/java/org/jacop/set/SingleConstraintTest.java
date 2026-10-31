/*
 * SingleConstraintTest.java
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

package org.jacop.set;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.stream.IntStream;
import org.jacop.constraints.Constraint;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.set.SetImposeGroundingHarness.Case;
import org.jacop.set.SetImposeGroundingHarness.Spec;
import org.jacop.set.constraints.AintersectBeqC;
import org.jacop.set.constraints.AleB;
import org.jacop.set.constraints.AllDisjoint;
import org.jacop.set.constraints.AltB;
import org.jacop.set.constraints.AunionBeqC;
import org.jacop.set.constraints.CardA;
import org.jacop.set.constraints.CardAeqX;
import org.jacop.set.constraints.ChannelBoolSet;
import org.jacop.set.constraints.ChannelIntSet;
import org.jacop.set.constraints.ElementSet;
import org.jacop.set.constraints.ElementSetVariable;
import org.jacop.set.constraints.Match;
import org.jacop.set.constraints.PartitionSet;
import org.jacop.set.constraints.SetMirror;
import org.jacop.set.constraints.SumWeightedSet;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;
import org.junit.jupiter.api.Test;

/** Tests of single set constraints and of the set domain. */
class SingleConstraintTest {
  @Test
  void testBoundSetDomainInFailsWhenGlbLeavesLub() {

    Store store = new Store();
    SetVar x =
        new SetVar(
            store, "x", new BoundSetDomain(new IntervalDomain(1, 1), new IntervalDomain(1, 4)));
    store.setLevel(1);

    boolean failed = false;
    try {
      // The new lub {2..3} does not contain the current glb {1}.
      x.domain.in(1, x, new IntervalDomain(), new IntervalDomain(2, 3));
    } catch (FailException e) {
      failed = true;
    }
    assertThat(failed).isTrue();
  }

  @Test
  void testBoundSetDomainInUpdatesCardinality() {

    Store store = new Store();
    SetVar x =
        new SetVar(
            store, "x", new BoundSetDomain(new IntervalDomain(1, 1), new IntervalDomain(1, 4)));
    store.setLevel(1);
    x.domain.in(1, x, new IntervalDomain(1, 2), new IntervalDomain(1, 3));

    assertThat(x.dom().card().eq(new IntervalDomain(2, 3))).isTrue();

    // At the same level: glb {1..2} already has the maximal cardinality 2, so x = {1..2}.
    x.domain.inCardinality(1, x, 2, 2);
    store.setLevel(2);
    SetVar y =
        new SetVar(
            store, "y", new BoundSetDomain(new IntervalDomain(5, 5), new IntervalDomain(5, 7)));
    y.domain.inCardinality(2, y, 2, 2);
    y.domain.in(2, y, new IntervalDomain(5, 6), new IntervalDomain(5, 7));

    assertThat(x.singleton()).isTrue();
    assertThat(y.singleton()).isTrue();
    assertThat(y.dom().glb().eq(new IntervalDomain(5, 6))).isTrue();
  }

  @Test
  void testElementSetVariableWakesOnGlbChange() {

    // index = 1, so value = a. Growing the glb of a must reach value; the constraint used to be
    // registered with IntDomain.ANY, which for a set variable is the LUB event only.
    Store store = new Store();
    IntVar index = new IntVar(store, "index", 1, 1);
    SetVar a = new SetVar(store, "a", 1, 5);
    SetVar b = new SetVar(store, "b", 1, 5);
    SetVar value = new SetVar(store, "value", 1, 5);
    store.impose(new ElementSetVariable(index, new SetVar[] {a, b}, value));
    assertThat(store.consistency()).isTrue();

    store.setLevel(1);
    a.domain.inGlb(1, a, 3);

    assertThat(store.consistency()).isTrue();
    assertThat(value.dom().glb().contains(3)).isTrue();
  }

  @Test
  void testPartitionSetWakesOnCardinalityChange() {

    // Two sets of cardinality 1 cannot partition {1..4}. Only the cardinalities change, which
    // generates a CARDINALITY_EVENT that must reach constraints registered for ANY.
    Store store = new Store();
    SetVar x = new SetVar(store, "x", 1, 4);
    SetVar y = new SetVar(store, "y", 1, 4);
    IntVar card = new IntVar(store, "card", 0, 4);
    store.impose(new PartitionSet(new SetVar[] {x, y}, new IntervalDomain(1, 4)));
    store.impose(new CardAeqX(x, card));
    store.impose(new CardAeqX(y, card));
    assertThat(store.consistency()).isTrue();

    store.setLevel(1);
    card.domain.in(1, card, 1, 1);

    assertThat(store.consistency()).isFalse();
  }

  @Test
  void testAllDisjointIsBoundsConsistent() {

    // At every node of random dives, with backtracking, the lower and upper bounds of each set
    // are exactly the intersection and the union of the solutions, and a node fails exactly when
    // there is no solution.
    Random random = new Random(5);
    for (int trial = 0; trial < 1500; trial++) {
      Store store = new Store();
      int n = 2 + random.nextInt(3);
      SetVar[] s = new SetVar[n];
      for (int i = 0; i < n; i++) {
        s[i] = randomSetVar(store, random, "s" + i, 6);
      }
      store.impose(new AllDisjoint(s));
      boolean consistent = store.consistency();
      assertAllDisjointBounds(s, consistent, "trial " + trial + " root");
      for (int step = 0; consistent && step < 6; step++) {
        if (step == 3 && store.level > 0) {
          // Back to an earlier node, so the next call starts from a stale assignment.
          store.removeLevel(store.level);
          store.setLevel(store.level - 1);
        }
        SetVar x = s[random.nextInt(n)];
        IntDomain open = x.domain.lub().subtract(x.domain.glb());
        if (open.isEmpty()) {
          continue;
        }
        int[] values = open.toIntArray();
        int v = values[random.nextInt(values.length)];
        store.setLevel(store.level + 1);
        try {
          if (random.nextBoolean()) {
            x.domain.inGlb(store.level, x, v);
          } else {
            x.domain.inLubComplement(store.level, x, v);
          }
          consistent = store.consistency();
        } catch (FailException e) {
          consistent = false;
        }
        if (consistent) {
          assertAllDisjointBounds(s, true, "trial " + trial + " step " + step);
        }
      }
    }
  }

  @Test
  void testAllDisjointUsesCardinalities() {

    // Three sets of two elements in {1..6} cover it, so 6 must go to z, the only set that may
    // take it; pairwise disjointness alone does not see this.
    Store store = new Store();
    SetVar x = new SetVar(store, "x", new BoundSetDomain(new IntervalDomain(), dom(1, 2, 3, 4)));
    SetVar y = new SetVar(store, "y", new BoundSetDomain(new IntervalDomain(), dom(1, 2, 3, 4)));
    SetVar z = new SetVar(store, "z", new BoundSetDomain(new IntervalDomain(), dom(4, 5, 6)));
    for (SetVar v : new SetVar[] {x, y, z}) {
      v.domain.inCardinality(store.level, v, 2, 2);
    }
    store.impose(new AllDisjoint(new SetVar[] {x, y, z}));

    assertThat(store.consistency()).isTrue();
    assertThat(z.dom().glb().eq(dom(5, 6))).isTrue();
    assertThat(z.dom().lub().eq(dom(5, 6))).isTrue();
    assertThat(x.dom().lub().eq(dom(1, 2, 3, 4))).isTrue();
  }

  @Test
  void testAllDisjointReachesFixpoint() {

    Random random = new Random(6);
    int notAtFixpoint =
        countNotAtFixpoint(
            random,
            store -> {
              SetVar[] s = new SetVar[3];
              for (int i = 0; i < s.length; i++) {
                s[i] = randomSetVar(store, random, "s" + i, 5);
              }
              return new AllDisjoint(s);
            });

    assertThat(notAtFixpoint).isZero();
  }

  /** Compares the bounds of the sets with the union and intersection of all disjoint solutions. */
  private static void assertAllDisjointBounds(SetVar[] s, boolean consistent, String where) {
    int n = s.length;
    int[] union = new int[n];
    int[] inter = new int[n];
    Arrays.fill(inter, -1);
    int[] chosen = new int[n];
    boolean found = enumerateDisjoint(s, 0, 0, chosen, union, inter);
    String state = where + ": " + Arrays.toString(s);
    assertThat(consistent).as(state).isEqualTo(found);
    if (!found) {
      return;
    }
    for (int i = 0; i < n; i++) {
      assertThat(s[i].dom().lub().eq(maskToDomain(union[i]))).as(state + " lub of " + i).isTrue();
      assertThat(s[i].dom().glb().eq(maskToDomain(inter[i]))).as(state + " glb of " + i).isTrue();
    }
  }

  // Elements are 1..30; bit e - 1 of a mask stands for element e.
  private static boolean enumerateDisjoint(
      SetVar[] s, int i, int used, int[] chosen, int[] union, int[] inter) {
    if (i == s.length) {
      for (int j = 0; j < s.length; j++) {
        union[j] |= chosen[j];
        inter[j] &= chosen[j];
      }
      return true;
    }
    int glb = domainToMask(s[i].dom().glb());
    int lub = domainToMask(s[i].dom().lub());
    boolean found = false;
    for (int mask = lub; ; mask = (mask - 1) & lub) {
      if ((mask & glb) == glb
          && (mask & used) == 0
          && s[i].dom().card().contains(Integer.bitCount(mask))) {
        chosen[i] = mask;
        found |= enumerateDisjoint(s, i + 1, used | mask, chosen, union, inter);
      }
      if (mask == 0) {
        break;
      }
    }
    return found;
  }

  private static int domainToMask(IntDomain d) {
    int mask = 0;
    for (int v : d.toIntArray()) {
      mask |= 1 << (v - 1);
    }
    return mask;
  }

  private static IntDomain maskToDomain(int mask) {
    IntervalDomain d = new IntervalDomain();
    for (int e = 1; e <= 30; e++) {
      if ((mask & 1 << (e - 1)) != 0) {
        d.unionAdapt(e, e);
      }
    }
    return d;
  }

  @Test
  void testPartitionSetReachesFixpoint() {

    Random random = new Random(3);
    int notAtFixpoint =
        countNotAtFixpoint(
            random,
            store -> {
              SetVar[] s = new SetVar[3];
              for (int i = 0; i < s.length; i++) {
                s[i] = randomSetVar(store, random, "s" + i, 5);
              }
              return new PartitionSet(s, new IntervalDomain(1, 5));
            });

    assertThat(notAtFixpoint).isZero();
  }

  @Test
  void testChannelIntSetReachesFixpoint() {

    Random random = new Random(2);
    int notAtFixpoint =
        countNotAtFixpoint(
            random,
            store -> {
              int n = 4;
              IntVar[] x = new IntVar[n];
              SetVar[] s = new SetVar[n];
              for (int i = 0; i < n; i++) {
                IntDomain d = randomSet(random, 1, n, 0.6);
                if (d.isEmpty()) {
                  return null;
                }
                x[i] = new IntVar(store, "x" + i, d);
              }
              for (int i = 0; i < n; i++) {
                s[i] = randomSetVar(store, random, "s" + i, n);
              }
              return new ChannelIntSet(x, s, 1, 1);
            });

    assertThat(notAtFixpoint).isZero();
  }

  @Test
  void testElementSetPrunesValueWithSupportingIndexesOnly() {

    // Index 2 selects {5..6}, which does not fit into lub {1..4}; the bounds of value must be
    // computed from the remaining indexes 1 and 3 only.
    Store store = new Store();
    IntVar index = new IntVar(store, "index", 1, 3);
    IntDomain[] list = {
      new IntervalDomain(1, 2), new IntervalDomain(5, 6), new IntervalDomain(1, 3)
    };
    SetVar value =
        new SetVar(
            store, "value", new BoundSetDomain(new IntervalDomain(1, 1), new IntervalDomain(1, 4)));
    store.impose(new ElementSet(index, list, value));

    assertThat(store.consistency()).isTrue();
    assertThat(index.dom().eq(dom(1, 3))).isTrue();
    assertThat(value.dom().glb().eq(new IntervalDomain(1, 2))).isTrue();
    assertThat(value.dom().lub().eq(new IntervalDomain(1, 3))).isTrue();
  }

  @Test
  void testElementSetReachesFixpoint() {

    Random random = new Random(1);
    int notAtFixpoint =
        countNotAtFixpoint(
            random,
            store -> {
              IntDomain[] list = new IntDomain[4];
              for (int i = 0; i < list.length; i++) {
                list[i] = randomSet(random, 1, 4, 0.5);
              }
              IntDomain indexDomain = randomSet(random, 1, 4, 0.5);
              if (indexDomain.isEmpty()) {
                return null;
              }
              IntVar index = new IntVar(store, "index", indexDomain);
              return new ElementSet(index, list, randomSetVar(store, random, "value", 4));
            });

    assertThat(notAtFixpoint).isZero();
  }

  /**
   * Imposes many random instances of a constraint and counts those for which a second call of
   * consistency() after store.consistency() still changes a domain or fails.
   */
  private int countNotAtFixpoint(Random random, Function<Store, Constraint> factory) {

    int notAtFixpoint = 0;
    for (int trial = 0; trial < 3000; trial++) {
      Store store = new Store();
      Constraint constraint = factory.apply(store);
      if (constraint == null) {
        continue;
      }
      store.impose(constraint);
      if (!store.consistency()) {
        continue;
      }
      String before = domains(constraint);
      store.setLevel(store.level + 1);
      String after;
      try {
        constraint.consistency(store);
        after = domains(constraint);
      } catch (FailException e) {
        after = "fail";
      }
      if (!after.equals(before)) {
        notAtFixpoint++;
      }
    }
    return notAtFixpoint;
  }

  @Test
  void testSumWeightedSetUsesTheWeightsOfTheGivenElements() {

    // The constructor ignored elements and gave weights[i] to the i-th element of a.lub(), so
    // elements {4, 1, 2} with weights {5, 0, 3} on lub {1..4} failed with an index out of bounds,
    // and elements listed in another order than the lub got the wrong weights. An element of the
    // lub without a weight (3 here) is not allowed in the set.
    assertSumWeightedSetMatchesBruteForce(
        dom(1, 2, 3, 4), new int[] {4, 1, 2}, new int[] {5, 0, 3});
    assertSumWeightedSetMatchesBruteForce(dom(1, 2, 3), new int[] {3, 1, 2}, new int[] {1, 4, 2});

    Random random = new Random(4);
    for (int trial = 0; trial < 100; trial++) {
      IntDomain lub = randomSet(random, 1, 5, 0.7);
      int[] elements = randomSet(random, 1, 6, 0.6).toIntArray();
      int[] weights = random.ints(elements.length, 0, 5).toArray();
      for (int i = elements.length - 1; i > 0; i--) {
        int j = random.nextInt(i + 1);
        int e = elements[i];
        elements[i] = elements[j];
        elements[j] = e;
      }
      assertSumWeightedSetMatchesBruteForce(lub, elements, weights);
    }
  }

  @Test
  void testSumWeightedSetRejectsNegativeWeights() {

    // The pruning assumes that adding an element never decreases the sum.
    Store store = new Store();
    SetVar a = new SetVar(store, "a", new BoundSetDomain(new IntervalDomain(), dom(1, 2)));
    IntVar total = new IntVar(store, "total", -5, 5);

    assertThatThrownBy(() -> new SumWeightedSet(a, new int[] {1, 2}, new int[] {2, -1}, total))
        .isInstanceOf(IllegalArgumentException.class);
  }

  /**
   * Checks every assignment of the set (a subset of lub) and of the total: the constraint must
   * accept exactly the sets made of weighted elements whose weights add up to the total.
   */
  private static void assertSumWeightedSetMatchesBruteForce(
      IntDomain lub, int[] elements, int[] weights) {
    int[] lubValues = lub.toIntArray();
    int maxTotal = Arrays.stream(weights).sum() + 1;
    for (int mask = 0; mask < 1 << lubValues.length; mask++) {
      IntDomain set = new IntervalDomain();
      boolean allowed = true;
      int sum = 0;
      for (int i = 0; i < lubValues.length; i++) {
        if ((mask & 1 << i) != 0) {
          set.unionAdapt(lubValues[i], lubValues[i]);
          boolean weighted = false;
          for (int j = 0; j < elements.length; j++) {
            if (elements[j] == lubValues[i]) {
              sum += weights[j];
              weighted = true;
            }
          }
          allowed &= weighted;
        }
      }
      for (int t = 0; t <= maxTotal; t++) {
        Store store = new Store();
        SetVar a = new SetVar(store, "a", new BoundSetDomain(new IntervalDomain(), lub));
        IntVar total = new IntVar(store, "total", 0, maxTotal);
        store.impose(new SumWeightedSet(a, elements, weights, total));
        boolean accepted;
        try {
          a.domain.in(store.level, a, set, set);
          total.domain.in(store.level, total, t, t);
          accepted = store.consistency();
        } catch (FailException e) {
          accepted = false;
        }
        assertThat(accepted)
            .as(
                "lub %s, elements %s, weights %s, set %s, total %d",
                lub, Arrays.toString(elements), Arrays.toString(weights), set, t)
            .isEqualTo(allowed && sum == t);
      }
    }
  }

  private static String domains(Constraint constraint) {
    return Arrays.toString(constraint.arguments().stream().map(Var::toString).sorted().toArray());
  }

  private static SetVar randomSetVar(Store store, Random random, String name, int max) {
    IntDomain lub = randomSet(random, 1, max, 0.7);
    IntDomain glb = lub.intersect(randomSet(random, 1, max, 0.25));
    SetVar s = new SetVar(store, name, new BoundSetDomain(glb, lub));
    if (random.nextBoolean()) {
      int min = glb.getSize() + random.nextInt(lub.getSize() - glb.getSize() + 1);
      s.domain.inCardinality(store.level, s, min, min + random.nextInt(2));
    }
    return s;
  }

  @Test
  void testChannelBoolSetRejectsBadArguments() {
    Store store = new Store();
    SetVar s = new SetVar(store, "s", 0, 1);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar wide = new IntVar(store, "wide", -1, 2);

    // a repeated variable gave the solution s = {0} although b[0] = b[1]
    assertThatThrownBy(() -> new ChannelBoolSet(new IntVar[] {b, b}, s))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new ChannelBoolSet(new IntVar[] {wide, b}, s))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new ChannelBoolSet(new IntVar[] {b}, null))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testSetConstraintsRejectNullArguments() {
    Store store = new Store();
    SetVar a = new SetVar(store, "a", 1, 2);
    SetVar b = new SetVar(store, "b", 1, 2);
    IntVar x = new IntVar(store, "x", 0, 1);

    assertThatThrownBy(() -> new PartitionSet(new SetVar[] {a, b}, null))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new PartitionSet(new SetVar[] {a, null}, new IntervalDomain(1, 2)))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new ChannelIntSet(new IntVar[] {x, null}, new SetVar[] {a}))
        .isInstanceOf(IllegalArgumentException.class);
    assertThatThrownBy(() -> new ChannelIntSet(new IntVar[] {x}, new SetVar[] {null}))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @Test
  void testAunionBeqCSatisfiedWhenGround() {
    // satisfied() compared the hull of the domains of a and b, whose glb is the intersection
    Store store = new Store();
    SetVar a = new SetVar(store, "a", new BoundSetDomain(dom(1), dom(1)));
    SetVar b = new SetVar(store, "b", new BoundSetDomain(dom(2), dom(2)));
    SetVar c = new SetVar(store, "c", new BoundSetDomain(dom(1, 2), dom(1, 2)));
    AunionBeqC union = new AunionBeqC(a, b, c);
    store.impose(union);

    assertThat(store.consistency()).isTrue();
    assertThat(union.satisfied()).isTrue();
  }

  @Test
  void testCardARespectsHolesInCardinality() {
    // only the bounds 0..2 of the cardinality {0, 2} were used, so a set of size 1 was accepted
    SetImposeGroundingHarness.check(
        "CardA {0, 2}",
        random ->
            new Case(
                new Spec[] {Spec.setVar(new int[0], new int[] {1, 2, 3})},
                (store, x) -> {
                  CardA c = new CardA((SetVar) x[0], dom(0, 2));
                  store.impose(c);
                  return c;
                },
                t -> t.s(0).size() == 0 || t.s(0).size() == 2,
                ""),
        1);

    Store store = new Store();
    SetVar a = new SetVar(store, "a", new BoundSetDomain(dom(1), dom(1)));
    store.impose(new CardA(a, dom(0, 2)));
    assertThat(store.consistency()).isFalse();
  }

  @Test
  void testChannelBoolSetNotSatisfiedByElementOutsideRange() {
    // s = {0} has an element without a Boolean (the only index is -1 + 1 = 0, element -1)
    Store store = new Store();
    IntVar b = new IntVar(store, "b", 0, 0);
    SetVar s = new SetVar(store, "s", new BoundSetDomain(dom(0), dom(0)));
    ChannelBoolSet channel = new ChannelBoolSet(new IntVar[] {b}, s, -1);
    store.impose(channel);

    assertThat(channel.satisfied()).isFalse();
    assertThat(store.consistency()).isFalse();
  }

  @Test
  void testChannelIntSetWithDifferentOffsets() {
    // x[k] stands for index k + offsetInt and s[l] for index l + offsetSet; the propagation mixed
    // up the two offsets and threw IllegalStateException or ArrayIndexOutOfBoundsException
    int ni = 2;
    int ns = 3;
    int offsetInt = 1;
    int offsetSet = 3;
    SetImposeGroundingHarness.check(
        "ChannelIntSet offsets",
        random -> {
          Spec[] vars = new Spec[ni + ns];
          for (int i = 0; i < ni; i++) {
            vars[i] = Spec.intVar(2, 3, 4, 5, 6);
          }
          for (int j = 0; j < ns; j++) {
            vars[ni + j] = Spec.setVar(new int[0], new int[] {0, 1, 2, 3});
          }
          return new Case(
              vars,
              (store, x) -> {
                ChannelIntSet c =
                    new ChannelIntSet(
                        Arrays.copyOf(x, ni, IntVar[].class),
                        Arrays.copyOfRange(x, ni, ni + ns, SetVar[].class),
                        offsetInt,
                        offsetSet);
                store.impose(c);
                return c;
              },
              t -> {
                for (int i = 0; i < ni; i++) {
                  if (t.i(i) < offsetSet || t.i(i) >= offsetSet + ns) {
                    return false;
                  }
                }
                for (int j = 0; j < ns; j++) {
                  Set<Integer> expected = new TreeSet<>();
                  for (int i = 0; i < ni; i++) {
                    if (t.i(i) == j + offsetSet) {
                      expected.add(i + offsetInt);
                    }
                  }
                  if (!expected.equals(t.s(ni + j))) {
                    return false;
                  }
                }
                return true;
              },
              "");
        },
        1);
  }

  @Test
  void testElementSetSatisfiedWithIndexOutOfRange() {
    // satisfied() indexed the list with an index outside 1..list.length
    Store store = new Store();
    IntVar index = new IntVar(store, "index", 0, 0);
    SetVar value = new SetVar(store, "value", new BoundSetDomain(dom(1), dom(1)));
    ElementSet element = new ElementSet(index, new IntDomain[] {dom(1)}, value);
    store.impose(element);

    assertThat(element.satisfied()).isFalse();
    assertThat(store.consistency()).isFalse();
  }

  @Test
  void testSumWeightedSetSatisfiedWithElementWithoutWeight() {
    // satisfied() threw NullPointerException for an element of the set without a weight
    Store store = new Store();
    SetVar a = new SetVar(store, "a", new BoundSetDomain(dom(2), dom(2)));
    IntVar total = new IntVar(store, "total", 0, 0);
    SumWeightedSet sum = new SumWeightedSet(a, new int[] {1}, new int[] {1}, total);
    store.impose(sum);

    assertThat(sum.satisfied()).isFalse();
    assertThat(store.consistency()).isFalse();
  }

  @Test
  void testMatchReachesFixpoint() {
    // the general case completed the glb of a without checking the list against it, so the search
    // accepted a = {-1, 2, 3} with list [-1, 3, 2]; there is no solution
    SetImposeGroundingHarness.check(
        "Match",
        random ->
            new Case(
                new Spec[] {
                  Spec.setVar(new int[0], new int[] {-1, 0, 2, 3, 4}),
                  Spec.intVar(-1, 1, 4),
                  Spec.intVar(1, 3, 4),
                  Spec.intVar(0, 1, 2)
                },
                (store, x) -> {
                  Match c = new Match((SetVar) x[0], Arrays.copyOfRange(x, 1, 4, IntVar[].class));
                  store.impose(c);
                  return c;
                },
                t -> {
                  int[] e = t.elements(0);
                  return e.length == 3 && e[0] == t.i(1) && e[1] == t.i(2) && e[2] == t.i(3);
                },
                ""),
        1);
  }

  private static IntDomain randomSet(Random random, int min, int max, double probability) {
    IntervalDomain d = new IntervalDomain();
    for (int v = min; v <= max; v++) {
      if (random.nextDouble() < probability) {
        d.unionAdapt(v, v);
      }
    }
    return d;
  }

  private static IntDomain dom(int... values) {
    IntervalDomain d = new IntervalDomain();
    for (int v : values) {
      d.unionAdapt(v, v);
    }
    return d;
  }

  @Test
  void testLexOrderKeepsSetsThatMayStopBeforeALargerElement() {

    // a in [{1}..{1, 3}] can be {1}, a prefix of b = {1, 2}, so a <= b and a < b hold; the
    // constraints failed because 3, an element that a need not contain, is larger than 2.
    for (boolean strict : new boolean[] {false, true}) {
      Store store = new Store();
      SetVar a = new SetVar(store, "a", new BoundSetDomain(dom(1), dom(1, 3)));
      SetVar b = new SetVar(store, "b", new BoundSetDomain(dom(1, 2), dom(1, 2)));
      store.impose(strict ? new AltB(a, b) : new AleB(a, b));
      assertThat(store.consistency()).as(strict ? "AltB" : "AleB").isTrue();
      assertThat(a.domain.lub().contains(1)).isTrue();
    }
  }

  @Test
  void testLexOrderMatchesBruteForce() {

    // Propagation must keep every pair of sets in the domains that is ordered, and must fail on
    // fixed sets that are not ordered.
    Random random = new Random(5);
    for (int trial = 0; trial < 3000; trial++) {
      boolean strict = random.nextBoolean();
      Store store = new Store();
      SetVar a = randomSetVar(store, random, "a", 4);
      SetVar b = randomSetVar(store, random, "b", 4);
      store.impose(strict ? new AltB(a, b) : new AleB(a, b));
      boolean consistent = store.consistency();
      String context = (strict ? "AltB " : "AleB ") + a + " " + b;
      for (IntDomain x : subsets(a)) {
        for (IntDomain y : subsets(b)) {
          int order = lexCompare(x.toIntArray(), y.toIntArray());
          if (strict ? order < 0 : order <= 0) {
            assertThat(consistent).as("solution %s, %s removed: %s", x, y, context).isTrue();
            assertThat(inDomain(a, x) && inDomain(b, y))
                .as("solution %s, %s removed: %s", x, y, context)
                .isTrue();
          }
        }
      }
    }
    for (int[] x : allSubsets(3)) {
      for (int[] y : allSubsets(3)) {
        for (boolean strict : new boolean[] {false, true}) {
          Store store = new Store();
          SetVar a = new SetVar(store, "a", new BoundSetDomain(dom(x), dom(x)));
          SetVar b = new SetVar(store, "b", new BoundSetDomain(dom(y), dom(y)));
          store.impose(strict ? new AltB(a, b) : new AleB(a, b));
          int order = lexCompare(x, y);
          assertThat(store.consistency())
              .as("%s %s %s", Arrays.toString(x), strict ? "<" : "<=", Arrays.toString(y))
              .isEqualTo(strict ? order < 0 : order <= 0);
        }
      }
    }
  }

  @Test
  void testLexOrderPrunesEveryElementWithoutSupport() {

    // AleB and AltB enforce bounds consistency: after propagation every element of a lub that is
    // not in the glb belongs to some ordered pair and is missing from another, and with a
    // restricted cardinality both cardinality bounds are reached by ordered pairs. The old
    // propagator only removed the elements of lub(b) below min(lub(a)).
    Random random = new Random(11);
    for (int trial = 0; trial < 3000; trial++) {
      boolean strict = random.nextBoolean();
      Store store = new Store();
      SetVar a = randomSetVar(store, random, "a", 5);
      SetVar b = randomSetVar(store, random, "b", 5);
      String before = (strict ? "AltB " : "AleB ") + a + " " + b;
      boolean cardA = restrictsCardinality(a);
      boolean cardB = restrictsCardinality(b);
      store.impose(strict ? new AltB(a, b) : new AleB(a, b));
      if (!store.consistency()) {
        continue;
      }
      List<IntDomain[]> solutions = new ArrayList<>();
      for (IntDomain x : subsets(a)) {
        for (IntDomain y : subsets(b)) {
          int order = lexCompare(x.toIntArray(), y.toIntArray());
          if (strict ? order < 0 : order <= 0) {
            solutions.add(new IntDomain[] {x, y});
          }
        }
      }
      String context = before + " -> " + a + " " + b;
      assertThat(solutions).as("consistent without a solution: %s", context).isNotEmpty();
      SetVar[] vars = {a, b};
      for (int k = 0; k < 2; k++) {
        SetVar s = vars[k];
        int index = k;
        for (int v : s.domain.lub().subtract(s.domain.glb()).toIntArray()) {
          assertThat(solutions.stream().anyMatch(p -> p[index].contains(v)))
              .as("%d kept in %s: %s", v, s.id(), context)
              .isTrue();
          assertThat(solutions.stream().anyMatch(p -> !p[index].contains(v)))
              .as("%d kept out of the glb of %s: %s", v, s.id(), context)
              .isTrue();
        }
        if (k == 0 ? cardA : cardB) {
          for (int c : new int[] {s.domain.card().min(), s.domain.card().max()}) {
            assertThat(solutions.stream().anyMatch(p -> p[index].getSize() == c))
                .as("cardinality %d of %s: %s", c, s.id(), context)
                .isTrue();
          }
        }
      }
    }
  }

  private static boolean restrictsCardinality(SetVar s) {
    return s.domain.card().min() > s.domain.glb().getSize()
        || s.domain.card().max() < s.domain.lub().getSize();
  }

  /** Compares two sorted sets in the lexicographic order of their elements; a prefix is smaller. */
  private static int lexCompare(int[] x, int[] y) {
    for (int i = 0; i < Math.min(x.length, y.length); i++) {
      if (x[i] != y[i]) {
        return Integer.compare(x[i], y[i]);
      }
    }
    return Integer.compare(x.length, y.length);
  }

  private static boolean inDomain(SetVar s, IntDomain set) {
    return set.contains(s.domain.glb())
        && s.domain.lub().contains(set)
        && s.domain.card().contains(set.getSize());
  }

  /** The sets between the glb and the lub of a set variable with a cardinality in its domain. */
  private static List<IntDomain> subsets(SetVar s) {
    int[] lub = s.domain.lub().toIntArray();
    List<IntDomain> result = new ArrayList<>();
    for (int mask = 0; mask < 1 << lub.length; mask++) {
      IntDomain set = new IntervalDomain();
      for (int i = 0; i < lub.length; i++) {
        if ((mask & 1 << i) != 0) {
          set.unionAdapt(lub[i], lub[i]);
        }
      }
      if (set.contains(s.domain.glb()) && s.domain.card().contains(set.getSize())) {
        result.add(set);
      }
    }
    return result;
  }

  private static List<int[]> allSubsets(int max) {
    List<int[]> result = new ArrayList<>();
    for (int mask = 0; mask < 1 << max; mask++) {
      int m = mask;
      result.add(IntStream.rangeClosed(1, max).filter(v -> (m & 1 << v - 1) != 0).toArray());
    }
    return result;
  }

  /**
   * Under LCG, an intersection whose result reaches its maximum cardinality: what the result's
   * domain derives from it (the other elements out) is explained by the intersection, from the
   * cardinality bound and the element in. It was the generic reason.
   */
  @Test
  void intersectionExplainsWhatTheCardinalityDerives() {
    Store store = new Store();
    SetVar a = new SetVar(store, "a", 1, 3);
    SetVar b = new SetVar(store, "b", 1, 3);
    SetVar c = new SetVar(store, "c", 1, 3);
    AintersectBeqC intersect = new AintersectBeqC(a, b, c);
    store.impose(intersect);
    for (SetVar s : new SetVar[] {a, b, c}) {
      store.impose(new SetMirror(s));
    }
    assertThat(store.consistency()).isTrue();
    AtomicTrail trail = new AtomicTrail(store);
    store.setLevel(store.level + 1);
    c.domain.inCardinality(store.level, c, 0, 1);
    assertThat(store.consistency()).isTrue();
    store.setLevel(store.level + 1);
    a.domain.inGlb(store.level, a, new IntervalDomain(1, 1));
    b.domain.inGlb(store.level, b, new IntervalDomain(1, 1));
    assertThat(store.consistency()).isTrue();
    assertThat(c.domain.lub().contains(2)).isFalse();
    IntVar has2 = c.lcgMirror().member(2);
    int entry = trail.lastEntry(has2, trail.size());
    assertThat(trail.reason(entry)).isSameAs(intersect);
    EntryList reason = new EntryList();
    assertThat(intersect.explain(trail, entry, reason)).isTrue();
    IntVar[] cMirror = c.lcgMirror().mirrorVariables();
    assertThat(reasonVariables(trail, reason))
        .containsExactlyInAnyOrder(cMirror[cMirror.length - 1], c.lcgMirror().member(1));
    trail.detach();
  }

  /**
   * Under LCG, set_card fixes a set once its cardinality variable reaches the elements left: the
   * memberships are explained by that bound and the elements out, and the bound of the variable by
   * the set's cardinality. CardAeqX had no explanations of its own.
   */
  @Test
  void cardinalityEqualityHasItsOwnReasons() {
    Store store = new Store();
    SetVar a = new SetVar(store, "a", 1, 4);
    IntVar k = new IntVar(store, "k", 0, 4);
    CardAeqX card = new CardAeqX(a, k);
    store.impose(card);
    store.impose(new SetMirror(a));
    assertThat(store.consistency()).isTrue();
    AtomicTrail trail = new AtomicTrail(store);
    store.setLevel(store.level + 1);
    k.domain.inMin(store.level, k, 3);
    assertThat(store.consistency()).isTrue();
    store.setLevel(store.level + 1);
    a.domain.inLub(store.level, a, new IntervalDomain(1, 3));
    assertThat(store.consistency()).isTrue();
    assertThat(a.domain.glb().contains(1)).isTrue();
    EntryList reason = new EntryList();
    int explained = 0;
    for (int e = 0; e < trail.size(); e++) {
      if (trail.reason(e) == card) {
        reason.clear();
        assertThat(card.explain(trail, e, reason)).as(trail.atomString(e)).isTrue();
        explained++;
      }
    }
    assertThat(explained).isPositive();
    trail.detach();
  }

  /**
   * Under LCG, array_set_element with the index narrowed to sets that all hold an element: the
   * membership is explained by the excluded indexes, and an index whose set holds an element out of
   * the value by that element. ElementSet had no explanations of its own.
   */
  @Test
  void elementSetHasItsOwnReasons() {
    Store store = new Store();
    IntVar index = new IntVar(store, "index", 1, 3);
    SetVar value = new SetVar(store, "value", 1, 4);
    IntDomain[] sets = {
      new IntervalDomain(1, 2), new IntervalDomain(1, 3), new IntervalDomain(3, 4)
    };
    ElementSet element = new ElementSet(index, sets, value);
    store.impose(element);
    store.impose(new SetMirror(value));
    assertThat(store.consistency()).isTrue();
    AtomicTrail trail = new AtomicTrail(store);
    store.setLevel(store.level + 1);
    value.domain.inLub(store.level, value, new IntervalDomain(1, 3));
    assertThat(store.consistency()).isTrue();
    assertThat(index.domain.contains(3)).isFalse();
    assertThat(value.domain.glb().contains(1)).isTrue();
    EntryList reason = new EntryList();
    int explained = 0;
    for (int e = 0; e < trail.size(); e++) {
      if (trail.reason(e) == element) {
        reason.clear();
        assertThat(element.explain(trail, e, reason)).as(trail.atomString(e)).isTrue();
        explained++;
      }
    }
    assertThat(explained).isGreaterThanOrEqualTo(2);
    trail.detach();
  }

  private static List<IntVar> reasonVariables(AtomicTrail trail, EntryList reason) {
    List<IntVar> vars = new ArrayList<>();
    for (int k = 0; k < reason.size(); k++) {
      if (!vars.contains(trail.variable(reason.get(k)))) {
        vars.add(trail.variable(reason.get(k)));
      }
    }
    return vars;
  }
}
