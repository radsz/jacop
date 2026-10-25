/*
 * SetImposeGroundingTest.java
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
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.set.SetImposeGroundingHarness.Case;
import org.jacop.set.SetImposeGroundingHarness.Spec;
import org.jacop.set.constraints.AdiffBeqC;
import org.jacop.set.constraints.AintersectBeqC;
import org.jacop.set.constraints.AunionBeqC;
import org.jacop.set.constraints.CardA;
import org.jacop.set.constraints.CardAeqX;
import org.jacop.set.constraints.ChannelBoolSet;
import org.jacop.set.constraints.ChannelIntSet;
import org.jacop.set.constraints.ElementSet;
import org.jacop.set.constraints.ElementSetVariable;
import org.jacop.set.constraints.Match;
import org.jacop.set.constraints.PartitionSet;
import org.jacop.set.constraints.SumWeightedSet;
import org.jacop.set.core.SetVar;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Imposes each set constraint with none, all and chosen subsets of its variables already ground or
 * partly decided (see {@link SetImposeGroundingHarness}) and compares all solutions with brute
 * force.
 *
 * <pre>
 * mvn -Pnocs -pl jacop-sets test -Dtest=SetImposeGroundingTest -Dsurefire.rerunFailingTestsCount=0 \
 *     -Dgrounding.cases=AunionBeqC,Match -Dgrounding.trials=200
 * </pre>
 */
class SetImposeGroundingTest {

  private static final int TRIALS = Integer.getInteger("grounding.trials", 40);

  /** Comma-separated parts of case names to run, e.g. {@code -Dgrounding.cases=Match}. */
  private static final String FILTER = System.getProperty("grounding.cases", "");

  static Stream<Arguments> cases() {
    List<Arguments> cases = new ArrayList<>();
    cases.add(Arguments.of("AunionBeqC", setOp("union")));
    cases.add(Arguments.of("AintersectBeqC", setOp("intersect")));
    cases.add(Arguments.of("AdiffBeqC", setOp("diff")));
    cases.add(Arguments.of("CardA", (Function<Random, Case>) SetImposeGroundingTest::cardA));
    cases.add(Arguments.of("CardAeqX", (Function<Random, Case>) SetImposeGroundingTest::cardAeqX));
    cases.add(
        Arguments.of(
            "ChannelBoolSet", (Function<Random, Case>) SetImposeGroundingTest::channelBoolSet));
    cases.add(
        Arguments.of(
            "ChannelIntSet", (Function<Random, Case>) SetImposeGroundingTest::channelIntSet));
    cases.add(
        Arguments.of("ElementSet", (Function<Random, Case>) SetImposeGroundingTest::elementSet));
    cases.add(
        Arguments.of(
            "ElementSetVariable",
            (Function<Random, Case>) SetImposeGroundingTest::elementSetVariable));
    cases.add(Arguments.of("Match", (Function<Random, Case>) SetImposeGroundingTest::match));
    cases.add(
        Arguments.of(
            "PartitionSet", (Function<Random, Case>) SetImposeGroundingTest::partitionSet));
    cases.add(Arguments.of("SumWeightedSet", sumWeightedSet(false)));
    cases.add(Arguments.of("SumWeightedSetCard", sumWeightedSet(true)));
    cases.add(
        Arguments.of(
            "SumWeightedSetLub", (Function<Random, Case>) SetImposeGroundingTest::sumWeightedLub));
    return cases.stream()
        .filter(
            a ->
                FILTER.isEmpty()
                    || Arrays.stream(FILTER.split(","))
                        .anyMatch(part -> a.get()[0].toString().contains(part)));
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("cases")
  void imposeWithGroundedVariables(String name, Function<Random, Case> generator) {
    SetImposeGroundingHarness.check(name, generator, TRIALS);
  }

  // ---------------------------------------------------------------- generators

  private static Function<Random, Case> setOp(String op) {
    return random -> {
      Spec[] vars = {set(random, 1, 4, 3), set(random, 1, 4, 3), set(random, 1, 4, 4)};
      return new Case(
          vars,
          (store, x) -> {
            SetVar a = (SetVar) x[0];
            SetVar b = (SetVar) x[1];
            SetVar c = (SetVar) x[2];
            Constraint constraint =
                switch (op) {
                  case "union" -> new AunionBeqC(a, b, c);
                  case "intersect" -> new AintersectBeqC(a, b, c);
                  default -> new AdiffBeqC(a, b, c);
                };
            store.impose(constraint);
            return constraint;
          },
          t -> {
            Set<Integer> r = new TreeSet<>(t.s(0));
            switch (op) {
              case "union" -> r.addAll(t.s(1));
              case "intersect" -> r.retainAll(t.s(1));
              default -> r.removeAll(t.s(1));
            }
            return r.equals(t.s(2));
          },
          op);
    };
  }

  private static Case cardA(Random random) {
    Spec[] vars = {set(random, 0, 5, 5)};
    int min = random.nextInt(5) - 1;
    int max = min + random.nextInt(4);
    int kind = random.nextInt(3);
    IntDomain card = new IntervalDomain(min, max);
    if (kind == 2 && max - min >= 2) {
      card.subtractAdapt(min + 1);
    }
    return new Case(
        vars,
        (store, x) -> {
          SetVar a = (SetVar) x[0];
          Constraint c =
              switch (kind) {
                case 0 -> new CardA(a, min);
                case 1 -> new CardA(a, min, max);
                default -> new CardA(a, card);
              };
          store.impose(c);
          return c;
        },
        t -> kind == 0 ? t.s(0).size() == min : card.contains(t.s(0).size()),
        "kind=" + kind + " card=" + (kind == 0 ? String.valueOf(min) : card.toString()));
  }

  private static Case cardAeqX(Random random) {
    Spec[] vars = {set(random, 0, 5, 4), Spec.intVar(values(random, -1, 5, 4))};
    return new Case(
        vars,
        (store, x) -> {
          Constraint c = new CardAeqX((SetVar) x[0], (IntVar) x[1]);
          store.impose(c);
          return c;
        },
        t -> t.s(0).size() == t.i(1),
        "");
  }

  private static Case channelBoolSet(Random random) {
    int n = 1 + random.nextInt(4);
    int offset = random.nextInt(5) - 2;
    Spec[] vars = new Spec[n + 1];
    for (int i = 0; i < n; i++) {
      vars[i] = random.nextInt(6) == 0 ? Spec.intVar(random.nextInt(2)) : Spec.intVar(0, 1);
    }
    // the lub sometimes holds elements outside offset..offset+n-1
    vars[n] = set(random, offset - 1, offset + n, 4);
    return new Case(
        vars,
        (store, x) -> {
          IntVar[] b = Arrays.copyOf(x, n, IntVar[].class);
          Constraint c = new ChannelBoolSet(b, (SetVar) x[n], offset);
          store.impose(c);
          return c;
        },
        t -> {
          Set<Integer> s = new TreeSet<>();
          for (int i = 0; i < n; i++) {
            if (t.i(i) == 1) {
              s.add(i + offset);
            }
          }
          return s.equals(t.s(n));
        },
        "offset=" + offset);
  }

  private static Case channelIntSet(Random random) {
    int ni = 1 + random.nextInt(3);
    int ns = 1 + random.nextInt(3);
    int offsetInt = random.nextInt(3);
    int offsetSet = random.nextInt(3);
    Spec[] vars = new Spec[ni + ns];
    for (int i = 0; i < ni; i++) {
      // the values of x index s, so they are around offsetSet
      vars[i] = Spec.intVar(values(random, offsetSet - 1, offsetSet + ns, 3));
    }
    for (int j = 0; j < ns; j++) {
      // the elements of s index x, so they are around offsetInt
      vars[ni + j] = set(random, offsetInt - 1, offsetInt + ni, 3);
    }
    return new Case(
        vars,
        (store, x) -> {
          IntVar[] xs = Arrays.copyOf(x, ni, IntVar[].class);
          SetVar[] ss = Arrays.copyOfRange(x, ni, ni + ns, SetVar[].class);
          Constraint c = new ChannelIntSet(xs, ss, offsetInt, offsetSet);
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
            for (int e : t.s(ni + j)) {
              if (e < offsetInt || e >= offsetInt + ni) {
                return false;
              }
            }
            for (int i = 0; i < ni; i++) {
              if ((t.i(i) == j + offsetSet) != t.s(ni + j).contains(i + offsetInt)) {
                return false;
              }
            }
          }
          return true;
        },
        "offsetInt=" + offsetInt + " offsetSet=" + offsetSet + " (x[i] = j <-> i in s[j])");
  }

  private static Case elementSet(Random random) {
    int k = 1 + random.nextInt(4);
    int offset = random.nextInt(3) - 1;
    IntDomain[] list = new IntDomain[k];
    for (int i = 0; i < k; i++) {
      list[i] = random.nextInt(4) == 0 ? new IntervalDomain() : domain(values(random, 1, 4, 3));
    }
    // indexes are 1-based plus offset; the index domain sometimes holds invalid indexes
    Spec[] vars = {Spec.intVar(values(random, offset, offset + k + 1, 4)), set(random, 1, 4, 4)};
    return new Case(
        vars,
        (store, x) -> {
          Constraint c = new ElementSet((IntVar) x[0], list, (SetVar) x[1], offset);
          store.impose(c);
          return c;
        },
        t -> {
          int i = t.i(0) - 1 - offset;
          return i >= 0 && i < k && toSet(list[i]).equals(t.s(1));
        },
        "offset=" + offset + " list=" + Arrays.toString(list));
  }

  private static Case elementSetVariable(Random random) {
    int k = 1 + random.nextInt(3);
    int offset = random.nextInt(3) - 1;
    Spec[] vars = new Spec[k + 2];
    vars[0] = Spec.intVar(values(random, offset, offset + k + 1, 3));
    for (int i = 0; i < k; i++) {
      vars[1 + i] = set(random, 1, 3, 3);
    }
    vars[k + 1] = set(random, 1, 3, 3);
    return new Case(
        vars,
        (store, x) -> {
          SetVar[] list = Arrays.copyOfRange(x, 1, k + 1, SetVar[].class);
          Constraint c = new ElementSetVariable((IntVar) x[0], list, (SetVar) x[k + 1], offset);
          store.impose(c);
          return c;
        },
        t -> {
          int i = t.i(0) - 1 - offset;
          return i >= 0 && i < k && t.s(1 + i).equals(t.s(k + 1));
        },
        "offset=" + offset);
  }

  private static Case match(Random random) {
    int n = random.nextInt(4);
    Spec[] vars = new Spec[n + 1];
    vars[0] = set(random, -1, 4, 5);
    for (int i = 0; i < n; i++) {
      vars[1 + i] = Spec.intVar(values(random, -1, 4, 3));
    }
    return new Case(
        vars,
        (store, x) -> {
          IntVar[] list = Arrays.copyOfRange(x, 1, n + 1, IntVar[].class);
          Constraint c = new Match((SetVar) x[0], list);
          store.impose(c);
          return c;
        },
        t -> {
          int[] e = t.elements(0);
          if (e.length != n) {
            return false;
          }
          for (int i = 0; i < n; i++) {
            if (e[i] != t.i(1 + i)) {
              return false;
            }
          }
          return true;
        },
        "n=" + n);
  }

  private static Case partitionSet(Random random) {
    int n = 1 + random.nextInt(3);
    int[] universe = values(random, 1, 4, random.nextInt(4));
    Spec[] vars = new Spec[n];
    for (int i = 0; i < n; i++) {
      // the lub sometimes holds elements outside the universe
      vars[i] = set(random, 0, 5, 4);
    }
    return new Case(
        vars,
        (store, x) -> {
          SetVar[] s = Arrays.copyOf(x, n, SetVar[].class);
          Constraint c = new PartitionSet(s, domain(universe));
          store.impose(c);
          return c;
        },
        t -> {
          Set<Integer> union = new TreeSet<>();
          int total = 0;
          for (int i = 0; i < n; i++) {
            union.addAll(t.s(i));
            total += t.s(i).size();
          }
          return total == union.size() && union.equals(toSet(domain(universe)));
        },
        "universe=" + Arrays.toString(universe));
  }

  private static Function<Random, Case> sumWeightedSet(boolean withCard) {
    return random -> {
      int k = 1 + random.nextInt(4);
      int[] elements = new int[k];
      int[] weights = new int[k];
      for (int i = 0; i < k; i++) {
        // elements may repeat; the weights of a repeated element add up
        elements[i] = random.nextInt(6) - 1;
        weights[i] = random.nextInt(5);
      }
      Map<Integer, Integer> weightOf = new HashMap<>();
      for (int i = 0; i < k; i++) {
        weightOf.merge(elements[i], weights[i], Integer::sum);
      }
      int cardMin = random.nextInt(3);
      int cardMax = cardMin + random.nextInt(3);
      // the lub sometimes holds elements without a weight, which are not allowed
      Spec[] vars = {set(random, -1, 4, 4), Spec.intVar(values(random, 0, 10, 5))};
      return new Case(
          vars,
          (store, x) -> {
            SetVar a = (SetVar) x[0];
            Constraint c = new SumWeightedSet(a, elements, weights, (IntVar) x[1]);
            store.impose(c);
            if (withCard) {
              store.impose(new CardA(a, cardMin, cardMax));
              // satisfied() of SumWeightedSet alone does not cover the cardinality
              return null;
            }
            return c;
          },
          t -> {
            int sum = 0;
            for (int e : t.s(0)) {
              if (!weightOf.containsKey(e)) {
                return false;
              }
              sum += weightOf.get(e);
            }
            int size = t.s(0).size();
            return sum == t.i(1) && (!withCard || size >= cardMin && size <= cardMax);
          },
          "elements="
              + Arrays.toString(elements)
              + " weights="
              + Arrays.toString(weights)
              + (withCard ? " card=" + cardMin + ".." + cardMax : ""));
    };
  }

  /** SumWeightedSet(a, total): the weight of each element of the lub is the element itself. */
  private static Case sumWeightedLub(Random random) {
    Spec[] vars = {set(random, 0, 4, 4), Spec.intVar(values(random, 0, 10, 6))};
    return new Case(
        vars,
        (store, x) -> {
          Constraint c = new SumWeightedSet((SetVar) x[0], (IntVar) x[1]);
          store.impose(c);
          return c;
        },
        t -> t.s(0).stream().mapToInt(Integer::intValue).sum() == t.i(1),
        "");
  }

  // ---------------------------------------------------------------- helpers

  /** A set variable with a random lub of up to maxSize elements of min..max and a small glb. */
  private static Spec set(Random random, int min, int max, int maxSize) {
    int[] lub = values(random, min, max, random.nextInt(maxSize + 1));
    int[] glb = Arrays.stream(lub).filter(e -> random.nextInt(5) == 0).toArray();
    return Spec.setVar(glb, lub);
  }

  /** Up to count distinct random values of min..max; at least one. */
  private static int[] values(Random random, int min, int max, int count) {
    Set<Integer> s = new HashSet<>();
    s.add(min + random.nextInt(max - min + 1));
    for (int i = 1; i < count; i++) {
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

  private static Set<Integer> toSet(IntDomain d) {
    Set<Integer> s = new TreeSet<>();
    IntStream.of(d.toIntArray()).forEach(s::add);
    return s;
  }
}
