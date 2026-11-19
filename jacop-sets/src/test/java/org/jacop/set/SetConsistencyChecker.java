/*
 * SetConsistencyChecker.java
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

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.function.Function;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.SetImposeGroundingHarness.Case;
import org.jacop.set.SetImposeGroundingHarness.Spec;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Measures the consistency set constraints reach, as {@code org.jacop.ConsistencyChecker} does for
 * integer constraints. Each case of {@link SetImposeGroundingTest} is imposed on small variables
 * and explored by random dives of decisions ({@code x = v}, {@code x != v}, {@code e in s}, {@code
 * e notin s}). After propagation at every node the box of current domains is enumerated: a solution
 * of the box before propagation that propagation removed is wrong pruning, as is a failure while a
 * solution exists, and {@code satisfied()} must not hold while a tuple of the box is no solution.
 * The case reports how many nodes are bound consistent (every element of a lub that is not in the
 * glb is in some solution and out of another, and every value of an integer variable has a
 * support). It is not in any profile; run it on demand:
 *
 * <pre>
 * mvn -Pnocs -pl jacop-sets test -Dtest=SetConsistencyChecker -Dsurefire.rerunFailingTestsCount=0 \
 *     -Dsetconsistency.instances=2000 -Dgrounding.cases=Match
 * </pre>
 */
class SetConsistencyChecker {

  private static final int INSTANCES = Integer.getInteger("setconsistency.instances", 300);

  private static final int MAX_BOX = 100_000;

  @ParameterizedTest(name = "{0}")
  @MethodSource("org.jacop.set.SetImposeGroundingTest#cases")
  void setConstraintsPruneSoundly(String name, Function<Random, Case> generator) {
    Random random = new Random(name.hashCode());
    long nodes = 0;
    long weak = 0;
    String firstWeak = null;
    List<String> errors = new ArrayList<>();
    for (int run = 0; run < INSTANCES && errors.size() < 3; run++) {
      Case c = generator.apply(random);
      Store store = new Store();
      Var[] x = new Var[c.vars().length];
      for (int i = 0; i < x.length; i++) {
        x[i] = create(store, i, c.vars()[i]);
      }
      Constraint constraint;
      try {
        constraint = c.impose().apply(store, x);
      } catch (IllegalArgumentException e) {
        continue;
      }
      List<String> path = new ArrayList<>();
      String start = show(x);
      List<int[]> before = box(c, x);
      boolean ok;
      try {
        ok = store.consistency();
      } catch (FailException e) {
        ok = false;
      }
      for (int depth = 0; depth < 12; depth++) {
        nodes++;
        String at = name + " run " + run + " " + c.description() + " " + start + " then " + path;
        String error = checkNode(c, x, before, ok, constraint, at);
        if (error != null) {
          errors.add(error);
          break;
        }
        if (!ok) {
          break;
        }
        String gap = gap(c, x);
        if (gap != null) {
          weak++;
          if (firstWeak == null) {
            firstWeak = at + ": " + gap;
          }
        }
        String decision = decide(store, x, random);
        if (decision == null) {
          break;
        }
        path.add(decision);
        before = box(c, x);
        try {
          ok = store.consistency();
        } catch (FailException e) {
          ok = false;
        }
      }
    }
    System.out.printf(
        "%-22s nodes %6d not bound consistent %6d%s%n",
        name, nodes, weak, firstWeak == null ? "" : "\n    e.g. " + firstWeak);
    assertThat(errors).isEmpty();
  }

  private static String checkNode(
      Case c, Var[] x, List<int[]> before, boolean ok, Constraint constraint, String at) {
    int solutionsBefore = 0;
    for (int[] t : before) {
      if (holds(c, t)) {
        solutionsBefore++;
      }
    }
    if (!ok) {
      return solutionsBefore > 0 ? at + ": failed with " + solutionsBefore + " solutions" : null;
    }
    List<int[]> now = box(c, x);
    int solutionsNow = 0;
    boolean allSolutions = true;
    for (int[] t : now) {
      if (holds(c, t)) {
        solutionsNow++;
      } else {
        allSolutions = false;
      }
    }
    if (solutionsNow < solutionsBefore) {
      return at + ": removed " + (solutionsBefore - solutionsNow) + " solutions, now " + show(x);
    }
    if (constraint instanceof SatisfiedPresent sp && !allSolutions && sp.satisfied()) {
      return at + ": satisfied() with a tuple that is no solution, " + show(x);
    }
    return null;
  }

  /** The first value of the current domains without a support, or null. */
  private static String gap(Case c, Var[] x) {
    List<int[]> solutions = new ArrayList<>();
    for (int[] t : box(c, x)) {
      if (holds(c, t)) {
        solutions.add(t);
      }
    }
    if (solutions.isEmpty()) {
      return "no solution left, " + show(x);
    }
    List<List<int[]>> values = values(c);
    for (int i = 0; i < x.length; i++) {
      final int var = i;
      if (x[i] instanceof IntVar v) {
        for (int value : elements(v.dom())) {
          if (solutions.stream().noneMatch(t -> values.get(var).get(t[var])[0] == value)) {
            return v.id() + " = " + value + " has no support, " + show(x);
          }
        }
      } else {
        SetVar s = (SetVar) x[i];
        for (int e : elements(s.dom().lub())) {
          if (s.dom().glb().contains(e)) {
            continue;
          }
          boolean in = solutions.stream().anyMatch(t -> contains(values.get(var).get(t[var]), e));
          boolean out = solutions.stream().anyMatch(t -> !contains(values.get(var).get(t[var]), e));
          if (!in || !out) {
            return e + (in ? " out of " : " in ") + s.id() + " has no support, " + show(x);
          }
        }
      }
    }
    return null;
  }

  private static String decide(Store store, Var[] x, Random random) {
    List<Integer> open = new ArrayList<>();
    for (int i = 0; i < x.length; i++) {
      if (!x[i].singleton()) {
        open.add(i);
      }
    }
    if (open.isEmpty()) {
      return null;
    }
    store.setLevel(store.level + 1);
    int i = open.get(random.nextInt(open.size()));
    if (x[i] instanceof IntVar v) {
      int[] vals = elements(v.dom());
      int value = vals[random.nextInt(vals.length)];
      if (random.nextBoolean()) {
        v.domain.in(store.level, v, value, value);
        return v.id() + "=" + value;
      }
      v.domain.inComplement(store.level, v, value);
      return v.id() + "!=" + value;
    }
    SetVar s = (SetVar) x[i];
    int[] free =
        Arrays.stream(elements(s.dom().lub())).filter(e -> !s.dom().glb().contains(e)).toArray();
    if (free.length == 0) {
      // only the cardinality is open
      return null;
    }
    int e = free[random.nextInt(free.length)];
    if (random.nextBoolean()) {
      s.domain.inGlb(store.level, s, e);
      return e + " in " + s.id();
    }
    s.domain.inLubComplement(store.level, s, e);
    return e + " notin " + s.id();
  }

  /** The tuples of the current domains, as indices into the values of each specification. */
  private static List<int[]> box(Case c, Var[] x) {
    List<List<int[]>> values = values(c);
    List<List<Integer>> allowed = new ArrayList<>();
    long size = 1;
    for (int i = 0; i < x.length; i++) {
      List<Integer> keep = new ArrayList<>();
      for (int k = 0; k < values.get(i).size(); k++) {
        if (inDomain(x[i], values.get(i).get(k))) {
          keep.add(k);
        }
      }
      allowed.add(keep);
      size *= Math.max(1, keep.size());
    }
    List<int[]> tuples = new ArrayList<>();
    if (size > MAX_BOX || allowed.stream().anyMatch(List::isEmpty)) {
      return tuples;
    }
    int[] t = new int[x.length];
    enumerate(allowed, 0, t, tuples);
    return tuples;
  }

  private static void enumerate(List<List<Integer>> allowed, int i, int[] t, List<int[]> out) {
    if (i == t.length) {
      out.add(t.clone());
      return;
    }
    for (int k : allowed.get(i)) {
      t[i] = k;
      enumerate(allowed, i + 1, t, out);
    }
  }

  private static boolean inDomain(Var v, int[] value) {
    if (v instanceof IntVar x) {
      return x.dom().contains(value[0]);
    }
    return setIn(((SetVar) v).dom(), value);
  }

  private static boolean setIn(SetDomain d, int[] value) {
    for (int e : elements(d.glb())) {
      if (!contains(value, e)) {
        return false;
      }
    }
    for (int e : value) {
      if (!d.lub().contains(e)) {
        return false;
      }
    }
    return d.card().contains(value.length);
  }

  private static boolean holds(Case c, int[] t) {
    List<List<int[]>> values = values(c);
    int[][] a = new int[t.length][];
    for (int i = 0; i < t.length; i++) {
      a[i] = values.get(i).get(t[i]);
    }
    return c.semantics().test(new SetImposeGroundingHarness.Assignment(a));
  }

  private static List<List<int[]>> values(Case c) {
    List<List<int[]>> values = new ArrayList<>();
    for (Spec s : c.vars()) {
      values.add(s.values());
    }
    return values;
  }

  private static Var create(Store store, int i, Spec spec) {
    if (!spec.isSet()) {
      return new IntVar(store, "x" + i, domain(spec.ints()));
    }
    return new SetVar(store, "s" + i, new BoundSetDomain(domain(spec.glb()), domain(spec.lub())));
  }

  private static IntDomain domain(int[] values) {
    IntervalDomain d = new IntervalDomain();
    for (int v : values) {
      d.unionAdapt(v, v);
    }
    return d;
  }

  private static int[] elements(IntDomain d) {
    List<Integer> l = new ArrayList<>();
    for (var e = d.valueEnumeration(); e.hasMoreElements(); ) {
      l.add(e.nextElement());
    }
    return l.stream().mapToInt(Integer::intValue).toArray();
  }

  private static boolean contains(int[] sorted, int e) {
    return Arrays.binarySearch(sorted, e) >= 0;
  }

  private static String show(Var[] x) {
    return Arrays.toString(x);
  }
}
