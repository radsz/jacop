/*
 * MutationGapsTest.java
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Random;
import java.util.function.Function;
import org.jacop.constraints.AtLeast;
import org.jacop.constraints.AtMost;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.Max;
import org.jacop.constraints.Member;
import org.jacop.constraints.Min;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Xor;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.ExplanationChecker;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Checks the LCG explanations of Max, Min, Member and ElementInteger directly, outside a solver:
 * random narrowings of small domains, then every atom the constraint propagated is explained and
 * the reason is checked in a scratch store by {@link ExplanationChecker}, and so is the reason of a
 * failure. These are the gaps the mutation-testing pilot (osolpro docs/assessment/mutation-testing)
 * found: a reason literal dropped in {@code Member.disjoint}, {@code MaxExplanation.low} on the
 * mirrored (Min) side, {@code MaxExplanation.entry} and {@code explainFailure} claiming a reason
 * they did not build, and the index offset of {@code ElementExplanation}, which no generator made
 * non-zero. The tests also count the atoms explained: an explanation that falls back to the generic
 * reason is not wrong, only weaker, and only the count sees it.
 */
class MutationGapsTest {

  /**
   * Counts from one run of {@link #check}: atoms the constraint propagated, atoms its own
   * explanation explained and their reason literals, failures it explained and their literals.
   */
  private record Counts(
      int atoms, int explained, int literals, int failures, int failureLiterals) {}

  /**
   * Imposes a constraint built over fresh variables, narrows random domains in steps, then checks
   * the reasons of every atom the constraint propagated and of its failure.
   */
  private static Counts check(long seed, int instances, Function<Random, Instance> generator) {
    Random rnd = new Random(seed);
    int atoms = 0;
    int explained = 0;
    int literals = 0;
    int failures = 0;
    int failureLiterals = 0;
    for (int instance = 0; instance < instances; instance++) {
      Instance in = generator.apply(rnd);
      Store store = in.store;
      AtomicTrail trail = new AtomicTrail(store);
      Constraint c = in.constraint;
      boolean consistent;
      try {
        store.impose(c);
        consistent = store.consistency();
      } catch (FailException _) {
        consistent = false;
      }
      for (int step = 0; consistent && step < 6; step++) {
        store.setLevel(store.level + 1);
        try {
          // several narrowings before propagation, so the constraint sees failures too
          int k = 1 + rnd.nextInt(3);
          for (int d = 0; d < k; d++) {
            IntVar v = in.vars[rnd.nextInt(in.vars.length)];
            if (v.singleton()) {
              continue;
            }
            int a = v.min() + rnd.nextInt(v.max() - v.min() + 1);
            switch (rnd.nextInt(4)) {
              case 0 -> {
                if (v.domain.contains(a)) {
                  v.domain.in(store.level, v, a, a);
                }
              }
              case 1 -> v.domain.inComplement(store.level, v, a);
              case 2 -> v.domain.inMax(store.level, v, a);
              default -> v.domain.inMin(store.level, v, a);
            }
          }
          consistent = store.consistency();
        } catch (FailException _) {
          consistent = false;
        }
      }
      ExplanationChecker checker = new ExplanationChecker(trail);
      String where = "seed " + seed + " instance " + instance + " " + c;
      for (int e = 0; e < trail.size(); e++) {
        if (trail.reason(e) != c) {
          continue;
        }
        atoms++;
        EntryList reason = new EntryList();
        // the constraint's own explanation: AtomicTrail.explain would replay the constraint or
        // fall back to the generic reason, both valid, so a weaker explanation would go unseen
        if (((Explainable) c).explain(trail, e, reason)) {
          explained++;
          literals += reason.size();
        } else {
          reason = new EntryList();
          trail.explain(e, reason);
        }
        assertNull(checker.checkReason(e, reason), where + " atom " + trail.atomString(e));
      }
      if (!consistent && store.recentlyFailedConstraint == c) {
        EntryList reason = new EntryList();
        if (((Explainable) c).explainFailure(trail, reason)) {
          failures++;
          failureLiterals += reason.size();
          assertNull(checker.checkFailure(c, reason), where + " failure");
        }
      }
      trail.detach();
    }
    Counts n = new Counts(atoms, explained, literals, failures, failureLiterals);
    return n;
  }

  private record Instance(Store store, Constraint constraint, IntVar[] vars) {}

  /**
   * Explanation-size golden: the atoms explained by the constraint itself, their reason literals,
   * and the failures explained and their literals, over a fixed seed. A change that makes an
   * explanation fall back to the generic reason or give a longer reason fails here even though
   * every reason stays valid; update the numbers only for a change meant to alter the reasons.
   */
  private static void golden(
      Counts n, int explained, int literals, int failures, int failureLiterals) {
    assertEquals(
        new Counts(n.atoms, explained, literals, failures, failureLiterals),
        n,
        "explanation-size golden");
  }

  private static IntVar[] vars(Store store, Random rnd, int n, int lo, int hi) {
    IntVar[] x = new IntVar[n];
    for (int i = 0; i < n; i++) {
      int a = lo + rnd.nextInt(hi - lo + 1);
      int b = lo + rnd.nextInt(hi - lo + 1);
      x[i] = new IntVar(store, "x" + i, Math.min(a, b), Math.max(a, b));
    }
    return x;
  }

  private static IntVar[] withLast(IntVar[] x, IntVar y) {
    IntVar[] all = java.util.Arrays.copyOf(x, x.length + 1);
    all[x.length] = y;
    return all;
  }

  private static Instance maxOrMin(Random rnd, boolean isMax) {
    Store store = new Store();
    IntVar[] x = vars(store, rnd, 2 + rnd.nextInt(3), -4, 4);
    IntVar m = new IntVar(store, "m", -5, 5);
    // m in its own list now and then: the explanations give up there (inList) and must say so
    IntVar[] list = rnd.nextInt(4) == 0 ? withLast(x, m) : x;
    Constraint c = isMax ? new Max(list, m) : new Min(list, m);
    return new Instance(store, c, withLast(x, m));
  }

  @Test
  void maxReasonsImplyTheirAtoms() {
    Counts n = check(1, 1500, rnd -> maxOrMin(rnd, true));
    golden(n, 4482, 2452, 122, 260);
    assertTrue(n.atoms > 1000, "atoms " + n);
    assertTrue(n.failures > 50, "failures " + n);
  }

  @Test
  void minReasonsImplyTheirAtoms() {
    Counts n = check(2, 1500, rnd -> maxOrMin(rnd, false));
    golden(n, 4571, 2596, 90, 195);
    assertTrue(n.atoms > 1000, "atoms " + n);
    assertTrue(n.failures > 50, "failures " + n);
  }

  @Test
  void memberReasonsImplyTheirAtoms() {
    Counts n =
        check(
            3,
            1500,
            rnd -> {
              Store store = new Store();
              IntVar[] x = vars(store, rnd, 2 + rnd.nextInt(3), 0, 6);
              IntVar e = new IntVar(store, "e", 0, 6);
              return new Instance(store, new Member(x, e), withLast(x, e));
            });
    golden(n, 3626, 6447, 70, 297);
    assertTrue(n.atoms > 500, "atoms " + n);
    assertTrue(n.failures > 50, "failures " + n);
  }

  private static Instance element(Random rnd, boolean fast, boolean exactIndex) {
    Store store = new Store();
    int n = 2 + rnd.nextInt(5);
    int offset = rnd.nextInt(7) - 3;
    int[] list = new int[n];
    for (int j = 0; j < n; j++) {
      list[j] = rnd.nextInt(5);
    }
    // index values j + 1 + offset; a wider root domain makes the index reasons fall back
    int lo = 1 + offset - (exactIndex ? 0 : rnd.nextInt(2));
    int hi = n + offset + (exactIndex ? 0 : rnd.nextInt(2));
    IntVar index = new IntVar(store, "i", lo, hi);
    IntVar value = new IntVar(store, "v", -1, 5);
    Constraint c =
        fast
            ? new ElementIntegerFast(index, list, value, offset)
            : new ElementInteger(index, list, value, offset);
    return new Instance(store, c, new IntVar[] {index, value});
  }

  @Test
  void elementReasonsWithOffsets() {
    Counts exact = check(4, 1500, rnd -> element(rnd, false, true));
    golden(exact, 6012, 3033, 214, 519);
    assertTrue(exact.atoms > 1000, "atoms " + exact);
    assertTrue(exact.failures > 50, "failures " + exact);
    Counts wide = check(5, 1500, rnd -> element(rnd, false, false));
    golden(wide, 5314, 1879, 216, 534);
    assertTrue(wide.atoms > 1000, "atoms " + wide);
    assertTrue(wide.failures > 50, "failures " + wide);
    Counts fast = check(6, 1500, rnd -> element(rnd, true, false));
    golden(fast, 4029, 1923, 314, 731);
    assertTrue(fast.atoms > 1000, "atoms " + fast);
    assertTrue(fast.failures > 50, "failures " + fast);
  }

  /**
   * Not, Reified and Xor over AtMost and AtLeast against brute force: every solution of random
   * small models is enumerated by search. The negated propagator ({@code notConsistency}, at least
   * counter + 1 occurrences for AtMost) and its {@code reified} guard were covered by no oracle:
   * the brute-force harness only posts the counting constraints on their own.
   */
  @Test
  void negatedAndReifiedCountsAgainstBruteForce() {
    Random rnd = new Random(7);
    for (int trial = 0; trial < 600; trial++) {
      Store store = new Store();
      int n = 2 + rnd.nextInt(3);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i, 0, 2);
      }
      IntVar b = new IntVar(store, "b", 0, 1);
      int value = rnd.nextInt(3);
      int counter = rnd.nextInt(n + 1);
      boolean atMost = rnd.nextBoolean();
      PrimitiveConstraint count =
          atMost ? new AtMost(x, counter, value) : new AtLeast(x, counter, value);
      int wrap = rnd.nextInt(3);
      store.impose(
          switch (wrap) {
            case 0 -> new Not(count);
            case 1 -> new Reified(count, b);
            default -> new Xor(count, b);
          });
      IntVar[] all = withLast(x, b);
      long expected = 0;
      int[] t = new int[n + 1];
      for (int code = 0; code < Math.pow(3, n) * 2; code++) {
        int c = code;
        int occurrences = 0;
        for (int i = 0; i < n; i++) {
          t[i] = c % 3;
          c /= 3;
          if (t[i] == value) {
            occurrences++;
          }
        }
        t[n] = c;
        boolean holds = atMost ? occurrences <= counter : occurrences >= counter;
        boolean ok =
            switch (wrap) {
              case 0 -> !holds;
              case 1 -> holds == (t[n] == 1);
              default -> holds != (t[n] == 1);
            };
        if (ok) {
          expected++;
        }
      }
      DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
      search.setPrintInfo(false);
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      boolean found =
          search.labeling(
              store, new SimpleSelect<>(all, null, new IndomainRandom<>(rnd.nextInt())));
      long actual = found ? search.getSolutionListener().solutionsNo() : 0;
      assertEquals(
          expected,
          actual,
          "trial "
              + trial
              + (atMost ? " AtMost" : " AtLeast")
              + " wrap "
              + wrap
              + " value "
              + value
              + " counter "
              + counter
              + " n "
              + n);
    }
  }

  /**
   * Not(AtMost) and Not(AtLeast) reach domain consistency: after propagation every value left has a
   * support, and a failure means no tuple of the domains is a solution. A count of at least k
   * occurrences fixes all candidates once exactly k remain; nothing else checked that pruning.
   */
  @Test
  void negatedCountsAreDomainConsistent() {
    Random rnd = new Random(8);
    int pruned = 0;
    for (int trial = 0; trial < 2000; trial++) {
      Store store = new Store();
      int n = 2 + rnd.nextInt(3);
      IntVar[] x = new IntVar[n];
      for (int i = 0; i < n; i++) {
        x[i] = new IntVar(store, "x" + i);
        for (int v = 0; v <= 3; v++) {
          if (rnd.nextInt(3) != 0) {
            x[i].addDom(v, v);
          }
        }
        if (x[i].domain.isEmpty()) {
          x[i].addDom(rnd.nextInt(4), 3);
        }
      }
      int value = rnd.nextInt(4);
      int counter = rnd.nextInt(n + 1);
      boolean atMost = rnd.nextBoolean();
      int[][] before = new int[n][];
      for (int i = 0; i < n; i++) {
        before[i] = values(x[i]);
      }
      PrimitiveConstraint count =
          atMost ? new AtMost(x, counter, value) : new AtLeast(x, counter, value);
      String where = "trial " + trial + " Not " + count;
      boolean consistent;
      try {
        store.impose(new Not(count));
        consistent = store.consistency();
      } catch (FailException _) {
        consistent = false;
      }
      // supported[i] holds the values of x[i] in some solution over the domains before propagation
      @SuppressWarnings("unchecked")
      java.util.Set<Integer>[] supported = new java.util.Set[n];
      for (int i = 0; i < n; i++) {
        supported[i] = new java.util.TreeSet<>();
      }
      int[] index = new int[n];
      while (true) {
        int occurrences = 0;
        for (int i = 0; i < n; i++) {
          if (before[i][index[i]] == value) {
            occurrences++;
          }
        }
        if (atMost ? occurrences > counter : occurrences < counter) {
          for (int i = 0; i < n; i++) {
            supported[i].add(before[i][index[i]]);
          }
        }
        int k = 0;
        while (k < n && ++index[k] == before[k].length) {
          index[k] = 0;
          k++;
        }
        if (k == n) {
          break;
        }
      }
      if (!consistent) {
        assertTrue(supported[0].isEmpty(), where + ": failed with a solution");
        continue;
      }
      for (int i = 0; i < n; i++) {
        java.util.Set<Integer> left = new java.util.TreeSet<>();
        for (int v : values(x[i])) {
          left.add(v);
        }
        assertEquals(supported[i], left, where + " x" + i);
        if (left.size() < before[i].length) {
          pruned++;
        }
      }
    }
    assertTrue(pruned > 100, "prunings " + pruned);
  }

  /**
   * Max over a hole in m wider than MaxExplanation's 4096-value limit: the explanations give up
   * (return false) for m's upper bound and for the failure. Claiming success there would hand the
   * solver an incomplete reason, which the checker rejects.
   */
  @Test
  void maxGivesUpOverWideHoles() {
    for (boolean failure : new boolean[] {false, true}) {
      Store store = new Store();
      IntVar x = new IntVar(store, "x", 0, 12_000);
      IntVar y = new IntVar(store, "y", 0, 12_000);
      IntVar m = new IntVar(store, "m", 0, 3);
      m.addDom(10_000, 12_000);
      AtomicTrail trail = new AtomicTrail(store);
      Max c = new Max(new IntVar[] {x, y}, m);
      store.impose(c);
      assertTrue(store.consistency());
      store.setLevel(1);
      boolean consistent;
      try {
        if (failure) {
          x.domain.inMin(store.level, x, 4_000);
        }
        x.domain.inMax(store.level, x, 9_000);
        y.domain.inMax(store.level, y, 9_000);
        consistent = store.consistency();
      } catch (FailException _) {
        consistent = false;
      }
      assertEquals(!failure, consistent);
      ExplanationChecker checker = new ExplanationChecker(trail);
      if (failure) {
        assertTrue(store.recentlyFailedConstraint == c);
        EntryList reason = new EntryList();
        if (c.explainFailure(trail, reason)) {
          assertNull(checker.checkFailure(c, reason));
        }
        continue;
      }
      assertEquals(3, m.max());
      for (int e = 0; e < trail.size(); e++) {
        if (trail.reason(e) == c && trail.variable(e) == m) {
          EntryList reason = new EntryList();
          if (c.explain(trail, e, reason)) {
            assertNull(checker.checkReason(e, reason), trail.atomString(e));
          }
        }
      }
    }
  }

  private static int[] values(IntVar x) {
    int[] v = new int[x.getSize()];
    int k = 0;
    for (org.jacop.core.ValueEnumeration e = x.domain.valueEnumeration(); e.hasMoreElements(); ) {
      v[k++] = e.nextElement();
    }
    return v;
  }
}
