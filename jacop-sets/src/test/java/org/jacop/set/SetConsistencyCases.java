/*
 * SetConsistencyCases.java
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
import java.util.TreeSet;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Stream;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Var;
import org.jacop.set.SetImposeGroundingHarness.Assignment;
import org.jacop.set.SetImposeGroundingHarness.Case;
import org.jacop.set.SetImposeGroundingHarness.Spec;
import org.jacop.set.constraints.AdiffBeqC;
import org.jacop.set.constraints.AdisjointB;
import org.jacop.set.constraints.AeqB;
import org.jacop.set.constraints.AeqS;
import org.jacop.set.constraints.AinB;
import org.jacop.set.constraints.AinS;
import org.jacop.set.constraints.AintersectBeqC;
import org.jacop.set.constraints.AleB;
import org.jacop.set.constraints.AllDisjoint;
import org.jacop.set.constraints.AltB;
import org.jacop.set.constraints.AunionBeqC;
import org.jacop.set.constraints.EinA;
import org.jacop.set.constraints.SetMirror;
import org.jacop.set.constraints.SinA;
import org.jacop.set.constraints.XeqA;
import org.jacop.set.constraints.XinA;
import org.jacop.set.core.SetVar;
import org.junit.jupiter.params.provider.Arguments;

/**
 * The cases of {@link SetConsistencyChecker} for the set constraints that {@link
 * SetImposeGroundingTest} has no case for: the relations (alone, reified and negated), AllDisjoint,
 * XeqA, SetMirror, and constraints with a variable repeated in their scope.
 */
final class SetConsistencyCases {

  private static final String FILTER = System.getProperty("grounding.cases", "");

  private SetConsistencyCases() {}

  /** A relation between the variables of a case, as a constraint maker and its meaning. */
  private interface Maker {
    Constraint make(Var[] x);
  }

  static Stream<Arguments> cases() {
    List<Arguments> cases = new ArrayList<>();
    for (boolean strict : new boolean[] {false, true}) {
      String suffix = strict ? "Strict" : "";
      relation(
          cases,
          "AinB" + suffix,
          r -> new Spec[] {set(r), set(r)},
          x -> new AinB((SetVar) x[0], (SetVar) x[1], strict),
          t -> subset(t.s(0), t.s(1), strict));
      relation(
          cases,
          "XinA" + suffix,
          r -> new Spec[] {ints(r), set(r)},
          x -> new XinA((IntVar) x[0], (SetVar) x[1], strict),
          t -> subset(Set.of(t.i(0)), t.s(1), strict));
    }
    for (boolean strict : new boolean[] {false, true}) {
      String suffix = strict ? "Strict" : "";
      constant(cases, "AinS" + suffix, strict, 0);
      constant(cases, "SinA" + suffix, strict, 1);
      element(cases, "EinA" + suffix, strict);
    }
    constant(cases, "AeqS", false, 2);
    relation(
        cases,
        "AeqB",
        r -> new Spec[] {set(r), set(r)},
        x -> new AeqB((SetVar) x[0], (SetVar) x[1]),
        t -> t.s(0).equals(t.s(1)));
    relation(
        cases,
        "AleB",
        r -> new Spec[] {set(r), set(r)},
        x -> new AleB((SetVar) x[0], (SetVar) x[1]),
        t -> lex(t.elements(0), t.elements(1)) <= 0);
    relation(
        cases,
        "AltB",
        r -> new Spec[] {set(r), set(r)},
        x -> new AltB((SetVar) x[0], (SetVar) x[1]),
        t -> lex(t.elements(0), t.elements(1)) < 0);
    relation(
        cases,
        "AdisjointB",
        r -> new Spec[] {set(r), set(r)},
        x -> new AdisjointB((SetVar) x[0], (SetVar) x[1]),
        t -> disjoint(t.s(0), t.s(1)));
    relation(
        cases,
        "XeqA",
        r -> new Spec[] {ints(r), set(r)},
        x -> new XeqA((IntVar) x[0], (SetVar) x[1]),
        t -> t.s(1).equals(Set.of(t.i(0))));
    cases.add(
        Arguments.of(
            "AllDisjoint",
            (Function<Random, Case>)
                r -> {
                  int n = 1 + r.nextInt(3);
                  Spec[] vars = new Spec[n];
                  for (int i = 0; i < n; i++) {
                    vars[i] = set(r);
                  }
                  return new Case(
                      vars,
                      (store, x) -> {
                        Constraint c = new AllDisjoint(Arrays.copyOf(x, n, SetVar[].class));
                        store.impose(c);
                        return c;
                      },
                      t -> {
                        Set<Integer> seen = new HashSet<>();
                        for (int i = 0; i < n; i++) {
                          for (int e : t.elements(i)) {
                            if (!seen.add(e)) {
                              return false;
                            }
                          }
                        }
                        return true;
                      },
                      "n=" + n);
                }));
    cases.add(
        Arguments.of(
            "SetMirror",
            (Function<Random, Case>)
                r ->
                    new Case(
                        new Spec[] {set(r)},
                        (store, x) -> {
                          Constraint c = new SetMirror((SetVar) x[0]);
                          store.impose(c);
                          return c;
                        },
                        t -> true,
                        "")));
    repeated(cases);
    return cases.stream()
        .filter(
            a ->
                FILTER.isEmpty()
                    || Arrays.stream(FILTER.split(","))
                        .anyMatch(part -> a.get()[0].toString().contains(part)));
  }

  /** A relation alone, and reified with a Boolean and negated when it is primitive. */
  private static void relation(
      List<Arguments> cases,
      String name,
      Function<Random, Spec[]> vars,
      Maker maker,
      Predicate<Assignment> meaning) {
    cases.add(
        Arguments.of(
            name,
            (Function<Random, Case>)
                r ->
                    new Case(
                        vars.apply(r),
                        (store, x) -> {
                          Constraint c = maker.make(x);
                          store.impose(c);
                          return c;
                        },
                        meaning,
                        "")));
    if (name.contains("disjoint")) {
      // AdisjointB is no primitive constraint
      return;
    }
    cases.add(
        Arguments.of(
            "Reified" + name,
            (Function<Random, Case>)
                r -> {
                  Spec[] base = vars.apply(r);
                  Spec[] all = Arrays.copyOf(base, base.length + 1);
                  all[base.length] = Spec.intVar(0, 1);
                  int b = base.length;
                  return new Case(
                      all,
                      (store, x) -> {
                        Constraint c =
                            new Reified(
                                (PrimitiveConstraint) maker.make(Arrays.copyOf(x, b)),
                                (IntVar) x[b]);
                        store.impose(c);
                        return c;
                      },
                      t -> meaning.test(t) == (t.i(b) == 1),
                      "");
                }));
    cases.add(
        Arguments.of(
            "Not" + name,
            (Function<Random, Case>)
                r ->
                    new Case(
                        vars.apply(r),
                        (store, x) -> {
                          Constraint c = new Not((PrimitiveConstraint) maker.make(x));
                          store.impose(c);
                          return c;
                        },
                        meaning.negate(),
                        "")));
  }

  /** AinS (kind 0), SinA (kind 1) or AeqS (kind 2) with a random constant set. */
  private static void constant(List<Arguments> cases, String name, boolean strict, int kind) {
    for (String prefix : new String[] {"", "Reified", "Not"}) {
      cases.add(
          Arguments.of(
              prefix + name,
              (Function<Random, Case>)
                  r -> {
                    int[] s = values(r, 1, 5, r.nextInt(4));
                    IntDomain d = domain(s);
                    Set<Integer> c = toSet(s);
                    Maker maker =
                        x ->
                            switch (kind) {
                              case 0 -> new AinS((SetVar) x[0], d, strict);
                              case 1 -> new SinA(d, (SetVar) x[0], strict);
                              default -> new AeqS((SetVar) x[0], d);
                            };
                    Predicate<Assignment> meaning =
                        switch (kind) {
                          case 0 -> t -> subset(t.s(0), c, strict);
                          case 1 -> t -> subset(c, t.s(0), strict);
                          default -> t -> t.s(0).equals(c);
                        };
                    return wrap(prefix, new Spec[] {set(r)}, maker, meaning, "set=" + c);
                  }));
    }
  }

  /** EinA with a random element. */
  private static void element(List<Arguments> cases, String name, boolean strict) {
    for (String prefix : new String[] {"", "Reified", "Not"}) {
      cases.add(
          Arguments.of(
              prefix + name,
              (Function<Random, Case>)
                  r -> {
                    int e = 1 + r.nextInt(5);
                    return wrap(
                        prefix,
                        new Spec[] {set(r)},
                        x -> new EinA(e, (SetVar) x[0], strict),
                        t -> subset(Set.of(e), t.s(0), strict),
                        "element=" + e);
                  }));
    }
  }

  private static Case wrap(
      String prefix, Spec[] base, Maker maker, Predicate<Assignment> meaning, String description) {
    if (prefix.isEmpty()) {
      return new Case(
          base,
          (store, x) -> {
            Constraint c = maker.make(x);
            store.impose(c);
            return c;
          },
          meaning,
          description);
    }
    if (prefix.equals("Not")) {
      return new Case(
          base,
          (store, x) -> {
            Constraint c = new Not((PrimitiveConstraint) maker.make(x));
            store.impose(c);
            return c;
          },
          meaning.negate(),
          description);
    }
    Spec[] all = Arrays.copyOf(base, base.length + 1);
    int b = base.length;
    all[b] = Spec.intVar(0, 1);
    return new Case(
        all,
        (store, x) -> {
          Constraint c =
              new Reified((PrimitiveConstraint) maker.make(Arrays.copyOf(x, b)), (IntVar) x[b]);
          store.impose(c);
          return c;
        },
        t -> meaning.test(t) == (t.i(b) == 1),
        description);
  }

  /** Constraints with one set variable at several positions of their scope. */
  private static void repeated(List<Arguments> cases) {
    String[] ops = {"union", "intersect", "diff"};
    for (String op : ops) {
      for (int pattern = 0; pattern < 3; pattern++) {
        // the positions of a, b and c that hold the same variable
        int[] at =
            switch (pattern) {
              case 0 -> new int[] {0, 0, 1};
              case 1 -> new int[] {0, 1, 0};
              default -> new int[] {0, 1, 1};
            };
        int p = pattern;
        cases.add(
            Arguments.of(
                "Repeated" + op + p,
                (Function<Random, Case>)
                    r ->
                        new Case(
                            new Spec[] {set(r), set(r)},
                            (store, x) -> {
                              SetVar a = (SetVar) x[at[0]];
                              SetVar b = (SetVar) x[at[1]];
                              SetVar c = (SetVar) x[at[2]];
                              Constraint con =
                                  switch (op) {
                                    case "union" -> new AunionBeqC(a, b, c);
                                    case "intersect" -> new AintersectBeqC(a, b, c);
                                    default -> new AdiffBeqC(a, b, c);
                                  };
                              store.impose(con);
                              return con;
                            },
                            t -> {
                              Set<Integer> a = t.s(at[0]);
                              Set<Integer> b = t.s(at[1]);
                              Set<Integer> res = new TreeSet<>(a);
                              switch (op) {
                                case "union" -> res.addAll(b);
                                case "intersect" -> res.retainAll(b);
                                default -> res.removeAll(b);
                              }
                              return res.equals(t.s(at[2]));
                            },
                            "pattern=" + p)));
      }
    }
    relation(
        cases,
        "RepeatedAinB",
        r -> new Spec[] {set(r)},
        x -> new AinB((SetVar) x[0], (SetVar) x[0], false),
        t -> true);
    relation(
        cases,
        "RepeatedAinBStrict",
        r -> new Spec[] {set(r)},
        x -> new AinB((SetVar) x[0], (SetVar) x[0], true),
        t -> false);
    relation(
        cases,
        "RepeatedAeqB",
        r -> new Spec[] {set(r)},
        x -> new AeqB((SetVar) x[0], (SetVar) x[0]),
        t -> true);
    relation(
        cases,
        "RepeatedAleB",
        r -> new Spec[] {set(r)},
        x -> new AleB((SetVar) x[0], (SetVar) x[0]),
        t -> true);
    relation(
        cases,
        "RepeatedAltB",
        r -> new Spec[] {set(r)},
        x -> new AltB((SetVar) x[0], (SetVar) x[0]),
        t -> false);
    relation(
        cases,
        "RepeatedAdisjointB",
        r -> new Spec[] {set(r)},
        x -> new AdisjointB((SetVar) x[0], (SetVar) x[0]),
        t -> t.s(0).isEmpty());
    cases.add(
        Arguments.of(
            "RepeatedAllDisjoint",
            (Function<Random, Case>)
                r ->
                    new Case(
                        new Spec[] {set(r), set(r)},
                        (store, x) -> {
                          SetVar a = (SetVar) x[0];
                          SetVar b = (SetVar) x[1];
                          Constraint c = new AllDisjoint(new SetVar[] {a, b, a});
                          store.impose(c);
                          return c;
                        },
                        t -> t.s(0).isEmpty() && disjoint(t.s(0), t.s(1)),
                        "")));
  }

  private static Spec set(Random random) {
    int[] lub = values(random, 1, 5, random.nextInt(5));
    int[] glb = Arrays.stream(lub).filter(e -> random.nextInt(5) == 0).toArray();
    return Spec.setVar(glb, lub);
  }

  private static Spec ints(Random random) {
    return Spec.intVar(values(random, 0, 6, 1 + random.nextInt(3)));
  }

  /** Up to count distinct random values of min..max; at least one when count is positive. */
  private static int[] values(Random random, int min, int max, int count) {
    Set<Integer> s = new HashSet<>();
    for (int i = 0; i < count; i++) {
      s.add(min + random.nextInt(max - min + 1));
    }
    return s.stream().mapToInt(Integer::intValue).sorted().toArray();
  }

  private static IntDomain domain(int[] values) {
    IntervalDomain d = new IntervalDomain();
    for (int v : values) {
      d.unionAdapt(v, v);
    }
    return d;
  }

  private static Set<Integer> toSet(int[] values) {
    Set<Integer> s = new TreeSet<>();
    for (int v : values) {
      s.add(v);
    }
    return s;
  }

  private static boolean subset(Set<Integer> a, Set<Integer> b, boolean strict) {
    return b.containsAll(a) && (!strict || !a.equals(b));
  }

  private static boolean disjoint(Set<Integer> a, Set<Integer> b) {
    for (int e : a) {
      if (b.contains(e)) {
        return false;
      }
    }
    return true;
  }

  /** MiniZinc's order of sets: the lexicographic order of their sorted elements. */
  private static int lex(int[] a, int[] b) {
    for (int i = 0; i < Math.min(a.length, b.length); i++) {
      if (a[i] != b[i]) {
        return Integer.compare(a[i], b[i]);
      }
    }
    return Integer.compare(a.length, b.length);
  }
}
