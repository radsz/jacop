/*
 * SetPrimitiveGroundingCases.java
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
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Random;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.stream.Stream;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.set.SetPrimitiveGroundingHarness.Case;
import org.jacop.set.SetPrimitiveGroundingHarness.Spec;
import org.jacop.set.constraints.AdisjointB;
import org.jacop.set.constraints.AeqB;
import org.jacop.set.constraints.AeqS;
import org.jacop.set.constraints.AinB;
import org.jacop.set.constraints.AinS;
import org.jacop.set.constraints.AleB;
import org.jacop.set.constraints.AltB;
import org.jacop.set.constraints.EinA;
import org.jacop.set.constraints.SinA;
import org.jacop.set.constraints.XeqA;
import org.jacop.set.constraints.XinA;
import org.jacop.set.core.SetVar;
import org.junit.jupiter.params.provider.Arguments;

/**
 * Instance generators for {@link SetPrimitiveGroundingTest}, one per set constraint. Append new
 * generators at the end of {@link #cases()} so that parallel branches merge easily.
 */
final class SetPrimitiveGroundingCases {

  private SetPrimitiveGroundingCases() {}

  static Stream<Arguments> cases() {
    List<Arguments> cases = new ArrayList<>();

    // B14: set relations
    for (boolean strict : new boolean[] {false, true}) {
      String suffix = strict ? "Strict" : "";
      cases.add(
          Arguments.of(
              "AinB" + suffix,
              (Function<Random, Case>)
                  random ->
                      Case.primitive(
                          new Spec[] {set(random), set(random)},
                          x -> new AinB((SetVar) x[0], (SetVar) x[1], strict),
                          t -> subset(t[0], t[1], strict),
                          "strict=" + strict)));
      cases.add(
          Arguments.of(
              "AinS" + suffix,
              (Function<Random, Case>)
                  random -> {
                    SortedSet<Integer> s = constant(random);
                    return Case.primitive(
                        new Spec[] {set(random)},
                        x -> new AinS((SetVar) x[0], domain(s), strict),
                        t -> subset(t[0], s, strict),
                        "set=" + s + " strict=" + strict);
                  }));
      cases.add(
          Arguments.of(
              "EinA" + suffix,
              (Function<Random, Case>)
                  random -> {
                    int e = 1 + random.nextInt(6);
                    return Case.primitive(
                        new Spec[] {set(random)},
                        x -> new EinA(e, (SetVar) x[0], strict),
                        t -> subset(Collections.singleton(e), t[0], strict),
                        "element=" + e + " strict=" + strict);
                  }));
      cases.add(
          Arguments.of(
              "SinA" + suffix,
              (Function<Random, Case>)
                  random -> {
                    SortedSet<Integer> s = constant(random);
                    return Case.primitive(
                        new Spec[] {set(random)},
                        x -> new SinA(domain(s), (SetVar) x[0], strict),
                        t -> subset(s, t[0], strict),
                        "set=" + s + " strict=" + strict);
                  }));
      cases.add(
          Arguments.of(
              "XinA" + suffix,
              (Function<Random, Case>)
                  random ->
                      Case.primitive(
                          new Spec[] {ints(random), set(random)},
                          x -> new XinA((IntVar) x[0], (SetVar) x[1], strict),
                          t -> subset(Collections.singleton(t[0]), t[1], strict),
                          "strict=" + strict)));
    }
    cases.add(
        Arguments.of(
            "AeqB",
            (Function<Random, Case>)
                random ->
                    Case.primitive(
                        new Spec[] {set(random), set(random)},
                        x -> new AeqB((SetVar) x[0], (SetVar) x[1]),
                        t -> t[0].equals(t[1]),
                        "")));
    cases.add(
        Arguments.of(
            "AeqS",
            (Function<Random, Case>)
                random -> {
                  SortedSet<Integer> s = constant(random);
                  return Case.primitive(
                      new Spec[] {set(random)},
                      x -> new AeqS((SetVar) x[0], domain(s)),
                      t -> t[0].equals(s),
                      "set=" + s);
                }));
    cases.add(
        Arguments.of(
            "AleB",
            (Function<Random, Case>)
                random ->
                    Case.primitive(
                        new Spec[] {set(random), set(random)},
                        x -> new AleB((SetVar) x[0], (SetVar) x[1]),
                        t -> lexCompare(t[0], t[1]) <= 0,
                        "")));
    cases.add(
        Arguments.of(
            "AltB",
            (Function<Random, Case>)
                random ->
                    Case.primitive(
                        new Spec[] {set(random), set(random)},
                        x -> new AltB((SetVar) x[0], (SetVar) x[1]),
                        t -> lexCompare(t[0], t[1]) < 0,
                        "")));
    cases.add(
        Arguments.of(
            "AdisjointB",
            (Function<Random, Case>)
                random ->
                    Case.of(
                        new Spec[] {set(random), set(random)},
                        (store, x) -> store.impose(new AdisjointB((SetVar) x[0], (SetVar) x[1])),
                        t -> Collections.disjoint((SortedSet<?>) t[0], (SortedSet<?>) t[1]),
                        "")));
    cases.add(
        Arguments.of(
            "XeqA",
            (Function<Random, Case>)
                random ->
                    Case.primitive(
                        new Spec[] {ints(random), set(random)},
                        x -> new XeqA((IntVar) x[0], (SetVar) x[1]),
                        t -> t[1].equals(Collections.singleton(t[0])),
                        "")));

    return cases.stream();
  }

  /** A set variable over a few of the elements 1..5, sometimes with a cardinality range. */
  static Spec set(Random random) {
    List<Integer> lub = new ArrayList<>();
    for (int e = 1; e <= 5; e++) {
      if (random.nextInt(5) < 3) {
        lub.add(e);
      }
    }
    while (lub.size() > 4) {
      lub.remove(random.nextInt(lub.size()));
    }
    List<Integer> glb = new ArrayList<>();
    for (int e : lub) {
      if (random.nextInt(5) == 0) {
        glb.add(e);
      }
    }
    int[] l = lub.stream().mapToInt(Integer::intValue).toArray();
    int[] g = glb.stream().mapToInt(Integer::intValue).toArray();
    if (random.nextInt(4) == 0) {
      int min = g.length + random.nextInt(l.length - g.length + 1);
      int max = min + random.nextInt(l.length - min + 1);
      return Spec.set(g, l, min, max);
    }
    return Spec.set(g, l);
  }

  /** An int variable over a few of the values 0..6. */
  static Spec ints(Random random) {
    List<Integer> values = new ArrayList<>();
    for (int v = 0; v <= 6; v++) {
      if (random.nextInt(2) == 0) {
        values.add(v);
      }
    }
    if (values.isEmpty()) {
      values.add(random.nextInt(7));
    }
    return Spec.ints(values.stream().mapToInt(Integer::intValue).toArray());
  }

  /** A constant set over the elements 0..6, possibly empty. */
  static SortedSet<Integer> constant(Random random) {
    SortedSet<Integer> s = new TreeSet<>();
    for (int e = 0; e <= 6; e++) {
      if (random.nextInt(3) == 0) {
        s.add(e);
      }
    }
    return s;
  }

  static IntDomain domain(SortedSet<Integer> s) {
    IntervalDomain d = new IntervalDomain();
    for (int e : s) {
      d.unionAdapt(e, e);
    }
    return d;
  }

  static boolean subset(Object a, Object b, boolean strict) {
    java.util.Set<?> x = (java.util.Set<?>) a;
    java.util.Set<?> y = (java.util.Set<?>) b;
    return y.containsAll(x) && (!strict || y.size() > x.size());
  }

  /**
   * Lexicographic order of sets as sorted sequences: {} < {1} < {1, 2} < {1, 3} < {2}; a proper
   * prefix is smaller.
   */
  @SuppressWarnings("unchecked")
  static int lexCompare(Object a, Object b) {
    Iterator<Integer> x = ((SortedSet<Integer>) a).iterator();
    Iterator<Integer> y = ((SortedSet<Integer>) b).iterator();
    while (x.hasNext() && y.hasNext()) {
      int c = Integer.compare(x.next(), y.next());
      if (c != 0) {
        return c;
      }
    }
    return x.hasNext() ? 1 : y.hasNext() ? -1 : 0;
  }
}
