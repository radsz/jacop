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
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import org.jacop.constraints.AllDifferentLists;
import org.jacop.constraints.ArgMaxMonotone;
import org.jacop.constraints.AtLeast;
import org.jacop.constraints.AtMost;
import org.jacop.constraints.ChannelOrder;
import org.jacop.constraints.ConjunctionSum;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Max;
import org.jacop.constraints.MaxCliqueBound;
import org.jacop.constraints.Member;
import org.jacop.constraints.Min;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XmulYeqZSaturated;
import org.jacop.constraints.Xor;
import org.jacop.constraints.table.BinaryBitTable;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
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
   * explanation explained and their reason literals, failures it explained and their literals, and
   * the consistency calls of the stores ({@link Store#numberConsistencyCalls}).
   */
  private record Counts(
      int atoms, int explained, int literals, int failures, int failureLiterals, long calls) {}

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
    long calls = 0;
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
        if (in.relation != null) {
          // ExplanationChecker skips a constraint it cannot copy: brute force over the root box
          assertNull(bruteReason(trail, in, reason, e), where + " atom " + trail.atomString(e));
        }
      }
      if (!consistent && store.recentlyFailedConstraint == c) {
        EntryList reason = new EntryList();
        if (((Explainable) c).explainFailure(trail, reason)) {
          failures++;
          failureLiterals += reason.size();
          assertNull(checker.checkFailure(c, reason), where + " failure");
          if (in.relation != null) {
            assertNull(bruteReason(trail, in, reason, -1), where + " failure");
          }
        }
      }
      trail.detach();
      calls += store.numberConsistencyCalls;
    }
    return new Counts(atoms, explained, literals, failures, failureLiterals, calls);
  }

  /**
   * A constraint over fresh variables. The relation, when given, holds for the complete assignments
   * of vars (in their order) that satisfy the constraint, and the reasons are also checked by brute
   * force over the root box.
   */
  private record Instance(
      Store store, Constraint constraint, IntVar[] vars, Predicate<int[]> relation) {
    Instance(Store store, Constraint constraint, IntVar[] vars) {
      this(store, constraint, vars, null);
    }
  }

  /**
   * Checks by brute force that a reason implies its atom (or, for entry -1, a failure): no
   * assignment of the root domains of the instance's variables that meets the reason and breaks the
   * atom satisfies the relation.
   *
   * @return null when the reason holds, otherwise a description of a counterexample
   */
  private static String bruteReason(AtomicTrail trail, Instance in, EntryList reason, int entry) {
    IntVar[] all = in.vars;
    IntDomain[] dom = new IntDomain[all.length];
    for (int i = 0; i < all.length; i++) {
      dom[i] = trail.rootDomain(all[i]).cloneLight();
    }
    StringBuilder text = new StringBuilder();
    for (int k = 0; k < reason.size(); k++) {
      int f = reason.get(k);
      int i = Arrays.asList(all).indexOf(trail.variable(f));
      if (i < 0) {
        return "reason atom on a variable outside the instance: " + trail.atomString(f);
      }
      text.append(trail.atomString(f)).append(' ');
      int v = trail.value(f);
      int slack = reason.slack(k);
      dom[i] =
          switch (trail.kind(f)) {
            case AtomicTrail.GE -> dom[i].intersect(v - slack, IntDomain.MAX_INT);
            case AtomicTrail.LE -> dom[i].intersect(IntDomain.MIN_INT, v + slack);
            default -> dom[i].subtract(v);
          };
    }
    if (entry >= 0) {
      int i = Arrays.asList(all).indexOf(trail.variable(entry));
      if (i < 0) {
        return "atom on a variable outside the instance";
      }
      int v = trail.value(entry);
      dom[i] =
          switch (trail.kind(entry)) {
            case AtomicTrail.GE -> dom[i].intersect(IntDomain.MIN_INT, v - 1);
            case AtomicTrail.LE -> dom[i].intersect(v + 1, IntDomain.MAX_INT);
            default -> dom[i].intersect(v, v);
          };
    }
    int[][] values = new int[all.length][];
    for (int i = 0; i < all.length; i++) {
      if (dom[i].isEmpty()) {
        return null;
      }
      values[i] = new int[dom[i].getSize()];
      int k = 0;
      for (ValueEnumeration en = dom[i].valueEnumeration(); en.hasMoreElements(); ) {
        values[i][k++] = en.nextElement();
      }
    }
    int[] pos = new int[all.length];
    int[] t = new int[all.length];
    while (true) {
      for (int i = 0; i < all.length; i++) {
        t[i] = values[i][pos[i]];
      }
      if (in.relation.test(t)) {
        return "reason " + text + "does not imply it: " + Arrays.toString(t) + " is a solution";
      }
      int i = 0;
      while (i < all.length && ++pos[i] == values[i].length) {
        pos[i] = 0;
        i++;
      }
      if (i == all.length) {
        return null;
      }
    }
  }

  /**
   * Explanation-size golden: the atoms explained by the constraint itself, their reason literals,
   * and the failures explained and their literals, over a fixed seed. A change that makes an
   * explanation fall back to the generic reason or give a longer reason fails here even though
   * every reason stays valid; update the numbers only for a change meant to alter the reasons.
   *
   * <p>The consistency calls are a cost golden: a lost or extra wake-up, or a constraint that runs
   * itself again to reach its fixpoint, changes them while every pruning stays the same, which no
   * answer check sees (the "speed only" survivors of the mutation testing follow-up, osolpro
   * docs/assessment/mutation-testing-followup.md). Update them only for a change meant to alter
   * when the constraint runs.
   */
  private static void golden(
      Counts n, int explained, int literals, int failures, int failureLiterals, long calls) {
    assertEquals(
        new Counts(n.atoms, explained, literals, failures, failureLiterals, calls),
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
    golden(n, 4482, 2452, 122, 260, 4563);
    assertTrue(n.atoms > 1000, "atoms " + n);
    assertTrue(n.failures > 50, "failures " + n);
  }

  @Test
  void minReasonsImplyTheirAtoms() {
    Counts n = check(2, 1500, rnd -> maxOrMin(rnd, false));
    golden(n, 4571, 2596, 90, 195, 4659);
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
    golden(n, 3626, 6447, 70, 297, 5644);
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
    golden(exact, 6012, 3033, 214, 519, 3277);
    assertTrue(exact.atoms > 1000, "atoms " + exact);
    assertTrue(exact.failures > 50, "failures " + exact);
    Counts wide = check(5, 1500, rnd -> element(rnd, false, false));
    golden(wide, 5314, 1879, 216, 534, 3304);
    assertTrue(wide.atoms > 1000, "atoms " + wide);
    assertTrue(wide.failures > 50, "failures " + wide);
    Counts fast = check(6, 1500, rnd -> element(rnd, true, false));
    golden(fast, 4029, 1923, 314, 731, 3520);
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
        assertSame(c, store.recentlyFailedConstraint);
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

  // ---- the globals added on 2026-11-14/16, PIT run of osolpro benchmarks/mutation-testing ----

  private static IntVar[] holed(Store store, Random rnd, int n, int lo, int hi) {
    IntVar[] x = vars(store, rnd, n, lo, hi);
    for (IntVar v : x) {
      if (v.max() - v.min() >= 2 && rnd.nextBoolean()) {
        v.domain.subtractAdapt(v.min() + 1 + rnd.nextInt(v.max() - v.min() - 1));
      }
    }
    return x;
  }

  private static IntVar[] bools(Store store, int n, String name) {
    IntVar[] b = new IntVar[n];
    for (int i = 0; i < n; i++) {
      b[i] = new IntVar(store, name + i, 0, 1);
    }
    return b;
  }

  @Test
  void binaryBitTableReasons() {
    Counts n =
        check(
            11,
            1500,
            rnd -> {
              Store store = new Store();
              IntVar[] x = holed(store, rnd, 2, -1, 4);
              int[][] tuples = new int[2 + rnd.nextInt(8)][];
              for (int t = 0; t < tuples.length; t++) {
                tuples[t] = new int[] {rnd.nextInt(6) - 1, rnd.nextInt(6) - 1};
              }
              Set<Long> allowed = new HashSet<>();
              for (int[] t : tuples) {
                allowed.add(t[0] * 1000L + t[1]);
              }
              return new Instance(
                  store,
                  new BinaryBitTable(x[0], x[1], tuples),
                  x,
                  t -> allowed.contains(t[0] * 1000L + t[1]));
            });
    golden(n, 2044, 203, 665, 56, 1773);
  }

  @Test
  void argMaxMonotoneReasons() {
    Counts n =
        check(
            12,
            1500,
            rnd -> {
              Store store = new Store();
              int m = 2 + rnd.nextInt(3);
              IntVar[] q = vars(store, rnd, m, -1, 4);
              int[][] f = new int[m][];
              int[] first = new int[m];
              for (int k = 0; k < m; k++) {
                if (rnd.nextInt(4) == 0) {
                  continue;
                }
                first[k] = q[k].min() + rnd.nextInt(2) - 1;
                f[k] = new int[2 + rnd.nextInt(q[k].max() - q[k].min() + 2)];
                int v = rnd.nextInt(5) - 2;
                for (int i = 0; i < f[k].length; i++) {
                  v += rnd.nextInt(3);
                  f[k][i] = v;
                }
              }
              IntVar index = new IntVar(store, "i", 0, m + 1);
              // the position of the first largest value from 0 (offset -1); a value off its table
              // has
              // none
              Predicate<int[]> argMax =
                  t -> {
                    int best = -1;
                    long largest = Long.MIN_VALUE;
                    for (int k = 0; k < m; k++) {
                      long value;
                      if (f[k] == null) {
                        value = t[k];
                      } else {
                        int i = t[k] - first[k];
                        if (i < 0 || i >= f[k].length) {
                          return false;
                        }
                        value = f[k][i];
                      }
                      if (value > largest) {
                        largest = value;
                        best = k;
                      }
                    }
                    return t[m] == best;
                  };
              return new Instance(
                  store, new ArgMaxMonotone(q, f, first, index, -1), withLast(q, index), argMax);
            });
    golden(n, 3876, 2270, 53, 137, 4683);
  }

  @Test
  void allDifferentListsReasons() {
    Counts n =
        check(
            13,
            1500,
            rnd -> {
              Store store = new Store();
              IntVar[] x = holed(store, rnd, 5, 0, 2);
              IntVar[][] rows = {{x[0], x[1]}, {x[2], x[3]}, {x[4], x[rnd.nextInt(4)]}};
              int[][] except =
                  rnd.nextBoolean() ? new int[0][] : new int[][] {{rnd.nextInt(3), rnd.nextInt(3)}};
              return new Instance(store, new AllDifferentLists(rows, except), x);
            });
    golden(n, 940, 1626, 125, 328, 4531);
  }

  @Test
  void channelOrderReasons() {
    Counts n =
        check(
            14,
            1500,
            rnd -> {
              Store store = new Store();
              IntVar x = holed(store, rnd, 1, -2, 5)[0];
              int k = 2 + rnd.nextInt(3);
              // order literals, which may share a 0/1 variable
              IntVar[] own = bools(store, k, "b");
              IntVar[] b = new IntVar[k];
              int[] t = new int[k];
              boolean[] atMost = new boolean[k];
              boolean[] implied = new boolean[k];
              for (int i = 0; i < k; i++) {
                b[i] = i > 0 && rnd.nextInt(4) == 0 ? b[rnd.nextInt(i)] : own[i];
                t[i] = rnd.nextInt(7) - 2;
                atMost[i] = rnd.nextBoolean();
                implied[i] = rnd.nextInt(3) == 0;
              }
              return new Instance(
                  store, new ChannelOrder(x, b, t, atMost, implied), withLast(own, x));
            });
    golden(n, 3235, 1142, 207, 308, 2490);
  }

  @Test
  void conjunctionSumReasons() {
    Counts n =
        check(
            15,
            1500,
            rnd -> {
              Store store = new Store();
              IntVar[] x = holed(store, rnd, 2 + rnd.nextInt(3), 0, 3);
              int terms = 1 + rnd.nextInt(4);
              IntVar[][] tv = new IntVar[terms][];
              int[][] values = new int[terms][];
              boolean[][] eq = new boolean[terms][];
              int[] w = new int[terms];
              for (int t = 0; t < terms; t++) {
                int k = 1 + rnd.nextInt(2);
                tv[t] = new IntVar[k];
                values[t] = new int[k];
                eq[t] = new boolean[k];
                for (int l = 0; l < k; l++) {
                  tv[t][l] = x[rnd.nextInt(x.length)];
                  values[t][l] = rnd.nextInt(5) - 1;
                  eq[t][l] = rnd.nextInt(4) != 0;
                }
                w[t] = rnd.nextInt(4);
              }
              IntVar sum = new IntVar(store, "s", 0, 8);
              return new Instance(
                  store, new ConjunctionSum(tv, values, eq, w, sum), withLast(x, sum));
            });
    golden(n, 553, 286, 17, 42, 5469);
  }

  @Test
  void maxCliqueBoundReasons() {
    Counts n =
        check(
            16,
            1500,
            rnd -> {
              Store store = new Store();
              int k = 2 + rnd.nextInt(6);
              IntVar[] x = bools(store, k, "x");
              int[][] conflicts = new int[k][];
              double density = 0.2 + 0.6 * rnd.nextDouble();
              for (int i = 0; i < k; i++) {
                java.util.List<Integer> c = new java.util.ArrayList<>();
                for (int j = 0; j < k; j++) {
                  if (j != i && rnd.nextDouble() < density) {
                    c.add(j);
                  }
                }
                conflicts[i] = c.stream().mapToInt(Integer::intValue).toArray();
              }
              IntVar s = new IntVar(store, "s", 0, k);
              return new Instance(store, new MaxCliqueBound(x, conflicts, s), withLast(x, s));
            });
    golden(n, 4669, 3581, 66, 158, 5076);
  }

  /**
   * MaxCliqueBound over 65 to 140 vertices, so that its bit sets span several words: the reasons
   * index vertices by word and bit, which graphs of fewer than 64 vertices never exercise.
   */
  @Test
  void maxCliqueBoundReasonsOverSeveralWords() {
    Counts n =
        check(
            22,
            60,
            rnd -> {
              Store store = new Store();
              int k = 65 + rnd.nextInt(76);
              IntVar[] x = bools(store, k, "x");
              int[][] conflicts = new int[k][];
              double density = 0.5 + 0.45 * rnd.nextDouble();
              for (int i = 0; i < k; i++) {
                java.util.List<Integer> c = new java.util.ArrayList<>();
                for (int j = i + 1; j < k; j++) {
                  if (rnd.nextDouble() < density) {
                    c.add(j);
                  }
                }
                conflicts[i] = c.stream().mapToInt(Integer::intValue).toArray();
              }
              IntVar s = new IntVar(store, "s", 0, k);
              return new Instance(store, new MaxCliqueBound(x, conflicts, s), withLast(x, s));
            });
    golden(n, 4950, 4922, 0, 0, 208);
  }

  /** LinearForm explains the entailment of a reified linear constraint (all four relations). */
  @Test
  void reifiedLinearEntailmentReasons() {
    String[] relations = {"<=", ">=", "==", "!="};
    Counts n =
        check(
            17,
            1500,
            rnd -> {
              Store store = new Store();
              IntVar[] x = holed(store, rnd, 2 + rnd.nextInt(2), -2, 4);
              int[] w = new int[x.length];
              for (int i = 0; i < w.length; i++) {
                w[i] =
                    (rnd.nextInt(3) + 1)
                        * (rnd.nextBoolean() ? 1 : -1)
                        * (rnd.nextInt(3) == 0 ? 2 : 1);
              }
              IntVar b = new IntVar(store, "b", 0, 1);
              LinearInt sum = new LinearInt(x, w, relations[rnd.nextInt(4)], rnd.nextInt(9) - 4);
              return new Instance(store, new Reified(sum, b), withLast(x, b));
            });
    golden(n, 1522, 1213, 90, 217, 3304);
  }

  /**
   * MaxCliqueBound's search helpers, which the FlatZinc clique search uses and no test called: the
   * greedy clique is a clique of vertices that can still be 1 and cannot be extended by another
   * such vertex, and the branching vertex is a free one, -1 once every vertex is fixed.
   */
  @Test
  void maxCliqueSearchHelpers() {
    Random rnd = new Random(18);
    int extended = 0;
    for (int trial = 0; trial < 400; trial++) {
      Store store = new Store();
      int k = 2 + rnd.nextInt(70);
      IntVar[] x = bools(store, k, "x");
      boolean[][] conflict = new boolean[k][k];
      int[][] conflicts = new int[k][];
      double density = 0.1 + 0.8 * rnd.nextDouble();
      for (int i = 0; i < k; i++) {
        java.util.List<Integer> c = new java.util.ArrayList<>();
        for (int j = 0; j < k; j++) {
          if (j != i && rnd.nextDouble() < density) {
            c.add(j);
            conflict[i][j] = true;
            conflict[j][i] = true;
          }
        }
        conflicts[i] = c.stream().mapToInt(Integer::intValue).toArray();
      }
      IntVar s = new IntVar(store, "s", 0, k);
      MaxCliqueBound c = new MaxCliqueBound(x, conflicts, s);
      store.impose(c);
      assertTrue(store.consistency());
      // fix a few vertices to 0, so that the clique must avoid them
      store.setLevel(1);
      for (int f = rnd.nextInt(Math.max(1, k / 4)); f > 0; f--) {
        IntVar v = x[rnd.nextInt(k)];
        v.domain.in(store.level, v, 0, 0);
      }
      assertTrue(store.consistency());
      int[] clique = c.greedyClique();
      boolean[] in = new boolean[k];
      for (int a : clique) {
        assertTrue(x[a].max() > 0, "trial " + trial + ": vertex " + a + " is fixed to 0");
        assertTrue(!in[a], "trial " + trial + ": vertex " + a + " twice");
        in[a] = true;
        for (int b : clique) {
          assertTrue(!conflict[a][b], "trial " + trial + ": " + a + " and " + b + " conflict");
        }
      }
      for (int v = 0; v < k; v++) {
        if (in[v] || x[v].max() == 0) {
          continue;
        }
        boolean compatible = true;
        for (int a : clique) {
          compatible &= !conflict[v][a];
        }
        assertTrue(!compatible, "trial " + trial + ": the clique misses vertex " + v);
      }
      if (clique.length > 1) {
        extended++;
      }
      int b = c.branchVertex();
      if (b >= 0) {
        assertTrue(!x[b].singleton(), "trial " + trial + ": branching on fixed " + x[b]);
      } else {
        for (IntVar v : x) {
          assertTrue(v.singleton() || v.max() == 0, "trial " + trial + ": -1 with free " + v);
        }
      }
    }
    assertTrue(extended > 100, "cliques of two or more vertices: " + extended);
  }

  /**
   * ChannelOrder's reifications(), which the linear relaxation and presolve read in place of the
   * constraint, have exactly its solutions.
   */
  @Test
  void channelOrderReificationsHaveItsSolutions() {
    Random rnd = new Random(19);
    for (int trial = 0; trial < 300; trial++) {
      int k = 1 + rnd.nextInt(4);
      int[] t = new int[k];
      boolean[] atMost = new boolean[k];
      boolean[] implied = new boolean[k];
      for (int i = 0; i < k; i++) {
        t[i] = rnd.nextInt(7) - 2;
        atMost[i] = rnd.nextBoolean();
        implied[i] = rnd.nextInt(3) == 0;
      }
      long[] counts = new long[2];
      for (int way = 0; way < 2; way++) {
        Store store = new Store();
        IntVar x = new IntVar(store, "x", -3, 5);
        IntVar[] b = bools(store, k, "b");
        ChannelOrder c = new ChannelOrder(x, b, t, atMost, implied);
        if (way == 0) {
          store.impose(c);
        } else {
          for (Constraint r : c.reifications()) {
            store.impose(r);
          }
        }
        DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
        search.setPrintInfo(false);
        search.getSolutionListener().searchAll(true);
        search.getSolutionListener().recordSolutions(false);
        boolean found =
            search.labeling(
                store,
                new SimpleSelect<>(withLast(b, x), null, new IndomainRandom<>(rnd.nextInt())));
        counts[way] = found ? search.getSolutionListener().solutionsNo() : 0;
      }
      long expected = 0;
      for (int v = -3; v <= 5; v++) {
        long ways = 1;
        for (int i = 0; i < k; i++) {
          boolean holds = atMost[i] ? v <= t[i] : v > t[i];
          ways *= implied[i] && !holds ? 1 : implied[i] ? 2 : 1;
        }
        expected += ways;
      }
      String where = "trial " + trial + " t " + java.util.Arrays.toString(t);
      assertEquals(expected, counts[0], where + " ChannelOrder");
      assertEquals(expected, counts[1], where + " reifications");
    }
  }

  /**
   * satisfied() of ConjunctionSum and MaxCliqueBound on ground assignments, before propagation: the
   * LCG represolve and the FlatZinc component split drop a constraint that says it is satisfied, so
   * true must mean a solution, and a solution with every variable fixed must say true.
   */
  @Test
  void satisfiedOnGroundAssignments() {
    Random rnd = new Random(20);
    int claimed = 0;
    for (int trial = 0; trial < 3000; trial++) {
      Store store = new Store();
      int n = 2 + rnd.nextInt(4);
      IntVar[] x = vars(store, rnd, n, 0, 3);
      boolean clique = rnd.nextBoolean();
      boolean holds;
      Constraint c;
      IntVar s = new IntVar(store, "s", 0, 8);
      int[] a = new int[n];
      if (clique) {
        x = bools(store, n, "y");
        int[][] conflicts = new int[n][];
        boolean[][] conflict = new boolean[n][n];
        for (int i = 0; i < n; i++) {
          java.util.List<Integer> l = new java.util.ArrayList<>();
          for (int j = 0; j < n; j++) {
            if (j != i && rnd.nextInt(3) == 0) {
              l.add(j);
              conflict[i][j] = true;
              conflict[j][i] = true;
            }
          }
          conflicts[i] = l.stream().mapToInt(Integer::intValue).toArray();
        }
        c = new MaxCliqueBound(x, conflicts, s);
        int count = 0;
        boolean independent = true;
        for (int i = 0; i < n; i++) {
          a[i] = rnd.nextInt(2);
          count += a[i];
          for (int j = 0; j < i; j++) {
            independent &= !(conflict[i][j] && a[i] == 1 && a[j] == 1);
          }
        }
        // the sum is at most the size of a clique that holds the ones
        int sv = rnd.nextInt(n + 1);
        holds = independent && sv <= count;
        store.impose(c);
        store.setLevel(1);
        s.domain.in(store.level, s, sv, sv);
      } else {
        int terms = 1 + rnd.nextInt(4);
        IntVar[][] tv = new IntVar[terms][];
        int[][] values = new int[terms][];
        boolean[][] eq = new boolean[terms][];
        int[] w = new int[terms];
        for (int i = 0; i < n; i++) {
          a[i] = x[i].min() + rnd.nextInt(x[i].max() - x[i].min() + 1);
        }
        long total = 0;
        for (int t = 0; t < terms; t++) {
          int k = 1 + rnd.nextInt(2);
          tv[t] = new IntVar[k];
          values[t] = new int[k];
          eq[t] = new boolean[k];
          boolean all = true;
          for (int l = 0; l < k; l++) {
            int i = rnd.nextInt(n);
            tv[t][l] = x[i];
            values[t][l] = rnd.nextInt(4);
            eq[t][l] = rnd.nextInt(4) != 0;
            all &= (a[i] == values[t][l]) == eq[t][l];
          }
          w[t] = rnd.nextInt(4);
          if (all) {
            total += w[t];
          }
        }
        c = new ConjunctionSum(tv, values, eq, w, s);
        int lo = rnd.nextInt(6);
        holds = total <= lo;
        store.impose(c);
        store.setLevel(1);
        s.domain.in(store.level, s, lo, lo + rnd.nextInt(3));
      }
      for (int i = 0; i < n; i++) {
        x[i].domain.in(store.level, x[i], a[i], a[i]);
      }
      boolean said = ((org.jacop.api.SatisfiedPresent) c).satisfied();
      String where = "trial " + trial + " " + c + " " + java.util.Arrays.toString(a);
      assertEquals(holds, said, where);
      if (said) {
        claimed++;
      }
    }
    assertTrue(claimed > 300, "satisfied " + claimed);
  }

  /**
   * XmulYeqZSaturated (z = x * y clamped to JaCoP's integer range) against brute force near the
   * ends of the range, where the product saturates, and with x and y the same variable: every
   * solution is kept, a failure means there is none, and the values pruned over the fixed seed are
   * a golden, so a weaker propagation (a dropped bound of x, y or z) fails it too.
   */
  @Test
  void saturatedProductsAgainstBruteForce() {
    Random rnd = new Random(21);
    int max = org.jacop.core.IntDomain.MAX_INT;
    int min = org.jacop.core.IntDomain.MIN_INT;
    int[] scales = {1, 23_170, max / 3, max / 2};
    long pruned = 0;
    int failures = 0;
    for (int trial = 0; trial < 3000; trial++) {
      Store store = new Store();
      int sx = scales[rnd.nextInt(scales.length)] * (rnd.nextBoolean() ? 1 : -1);
      int sy = scales[rnd.nextInt(2)] * (rnd.nextBoolean() ? 1 : -1);
      IntVar x = new IntVar(store, "x");
      IntVar y = new IntVar(store, "y");
      int[] xs = new int[3 + rnd.nextInt(3)];
      int[] ys = new int[3 + rnd.nextInt(3)];
      for (int i = 0; i < xs.length; i++) {
        xs[i] = (int) Math.clamp((long) sx + rnd.nextInt(7) - 3, min, max);
        x.addDom(xs[i], xs[i]);
      }
      for (int i = 0; i < ys.length; i++) {
        ys[i] = (int) Math.clamp((long) sy + rnd.nextInt(7) - 3, min, max);
        y.addDom(ys[i], ys[i]);
      }
      boolean same = rnd.nextInt(4) == 0;
      if (same) {
        y = x;
      }
      IntVar z = new IntVar(store, "z");
      // some products, the ends of the range and a few other values
      int[] xv = values(x);
      int[] yv = values(y);
      for (int k = 0; k < 4; k++) {
        int p =
            XmulYeqZSaturated.saturatedProduct(
                xv[rnd.nextInt(xv.length)], yv[rnd.nextInt(yv.length)]);
        z.addDom(p, p);
      }
      int[] extra = {max, min, 0, max - 1, rnd.nextInt(2_000_001) - 1_000_000};
      for (int k = rnd.nextInt(3); k < extra.length; k += 1 + rnd.nextInt(2)) {
        z.addDom(extra[k], extra[k]);
      }
      int[] zv = values(z);
      java.util.Set<Integer> zs = new java.util.HashSet<>();
      for (int v : zv) {
        zs.add(v);
      }
      java.util.Set<Integer> sxs = new java.util.TreeSet<>();
      java.util.Set<Integer> sys = new java.util.TreeSet<>();
      java.util.Set<Integer> szs = new java.util.TreeSet<>();
      for (int a : xv) {
        for (int b : same ? new int[] {a} : yv) {
          int p = XmulYeqZSaturated.saturatedProduct(a, b);
          if (zs.contains(p)) {
            sxs.add(a);
            sys.add(b);
            szs.add(p);
          }
        }
      }
      int before = x.getSize() + (same ? 0 : y.getSize()) + z.getSize();
      boolean consistent;
      try {
        store.impose(new XmulYeqZSaturated(x, y, z));
        consistent = store.consistency();
      } catch (FailException _) {
        consistent = false;
      }
      String where = "trial " + trial + " x " + x + " y " + y + " z " + z + " same " + same;
      if (!consistent) {
        assertTrue(szs.isEmpty(), where + ": failed with a solution");
        failures++;
        continue;
      }
      for (int a : sxs) {
        assertTrue(x.domain.contains(a), where + ": lost x = " + a);
      }
      for (int b : sys) {
        assertTrue(y.domain.contains(b), where + ": lost y = " + b);
      }
      for (int p : szs) {
        assertTrue(z.domain.contains(p), where + ": lost z = " + p);
      }
      pruned += before - (x.getSize() + (same ? 0 : y.getSize()) + z.getSize());
    }
    assertEquals(6763, pruned, "values pruned (golden)");
    assertEquals(0, failures, "failures (golden)");
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
