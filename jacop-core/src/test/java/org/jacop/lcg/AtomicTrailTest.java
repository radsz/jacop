/*
 * AtomicTrailTest.java
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

package org.jacop.lcg;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.function.Function;
import java.util.function.Predicate;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.AtLeast;
import org.jacop.constraints.AtMost;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.Max;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Values;
import org.jacop.constraints.XdivYeqZ;
import org.jacop.constraints.XexpYeqZ;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmodYeqZ;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.diffn.Diffn;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.LazyBitSetDomain;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Tests the atomic trail: after every propagation the atoms rebuild every current domain from the
 * initial one, and both the generic and the explained reason of every propagated atom imply it
 * under the constraint's relation (checked by enumerating the box the reason allows).
 */
class AtomicTrailTest {

  private record Model(Constraint constraint, Predicate<int[]> relation, IntVar[] vars) {}

  private static IntVar newVar(Store store, String name, Random rnd) {
    IntVar x = new IntVar(store, name, -4 + rnd.nextInt(3), 3 + rnd.nextInt(3));
    for (int k = rnd.nextInt(3); k > 0; k--) {
      int v = x.min() + 1 + rnd.nextInt(Math.max(1, x.max() - x.min() - 1));
      if (v < x.max()) {
        x.domain.subtractAdapt(v);
        x.refreshBounds();
      }
    }
    return x;
  }

  private static List<Function<Store, Model>> models(Random rnd) {
    List<Function<Store, Model>> m = new ArrayList<>();
    m.add(
        s -> {
          IntVar[] v = {newVar(s, "x", rnd), newVar(s, "y", rnd), newVar(s, "z", rnd)};
          return new Model(new XplusYeqZ(v[0], v[1], v[2]), t -> t[0] + t[1] == t[2], v);
        });
    m.add(
        s -> {
          IntVar[] v = {newVar(s, "x", rnd), newVar(s, "y", rnd), newVar(s, "z", rnd)};
          return new Model(new XmulYeqZ(v[0], v[1], v[2]), t -> t[0] * t[1] == t[2], v);
        });
    m.add(
        s -> {
          IntVar[] v = {newVar(s, "x", rnd), newVar(s, "z", rnd)};
          return new Model(new XmulYeqZ(v[0], v[0], v[1]), t -> t[0] * t[0] == t[1], v);
        });
    m.add(
        s -> {
          IntVar[] v = {newVar(s, "x", rnd), new IntVar(s, "b", 0, 1), newVar(s, "z", rnd)};
          return new Model(new XmulYeqZ(v[0], v[1], v[2]), t -> t[0] * t[1] == t[2], v);
        });
    m.add(
        s -> {
          IntVar[] v = {newVar(s, "x", rnd), newVar(s, "y", rnd), newVar(s, "z", rnd)};
          return new Model(
              new XdivYeqZ(v[0], v[1], v[2]), t -> t[1] != 0 && t[0] / t[1] == t[2], v);
        });
    m.add(
        s -> {
          IntVar[] v = {newVar(s, "x", rnd), newVar(s, "y", rnd), newVar(s, "z", rnd)};
          return new Model(
              new XmodYeqZ(v[0], v[1], v[2]), t -> t[1] != 0 && t[0] % t[1] == t[2], v);
        });
    m.add(
        s -> {
          IntVar[] v = {newVar(s, "x", rnd), newVar(s, "y", rnd), newVar(s, "z", rnd)};
          return new Model(new XexpYeqZ(v[0], v[1], v[2]), AtomicTrailTest::pow, v);
        });
    m.add(
        s -> {
          IntVar[] v = {
            newVar(s, "a", rnd), newVar(s, "b", rnd), newVar(s, "c", rnd), newVar(s, "d", rnd)
          };
          int[] w = {2, -3, 1, 1};
          return new Model(
              new LinearInt(v, w, "<=", 1), t -> 2 * t[0] - 3 * t[1] + t[2] + t[3] <= 1, v);
        });
    m.add(
        s -> {
          IntVar[] v = {newVar(s, "a", rnd), newVar(s, "b", rnd), newVar(s, "c", rnd)};
          int[] w = {1, 2, -1};
          return new Model(new LinearInt(v, w, "==", 0), t -> t[0] + 2 * t[1] - t[2] == 0, v);
        });
    m.add(
        s -> {
          IntVar[] v = {
            newVar(s, "a", rnd), newVar(s, "b", rnd), newVar(s, "c", rnd), newVar(s, "d", rnd)
          };
          return new Model(new Alldistinct(v), AtomicTrailTest::distinct, v);
        });
    m.add(
        s -> {
          IntVar[] v = {
            newVar(s, "a", rnd), newVar(s, "b", rnd), newVar(s, "c", rnd), newVar(s, "d", rnd)
          };
          return new Model(new Alldiff(v), AtomicTrailTest::distinct, v);
        });
    m.add(
        s -> {
          IntVar[] v = {new IntVar(s, "i", 1, 5), newVar(s, "v", rnd)};
          int[] list = {3, -2, 0, 3, 1};
          return new Model(
              new ElementInteger(v[0], list, v[1], 0),
              t -> t[0] >= 1 && t[0] <= 5 && list[t[0] - 1] == t[1],
              v);
        });
    m.add(
        s -> {
          IntVar[] v = {newVar(s, "x", rnd), newVar(s, "y", rnd)};
          return new Model(new AbsXeqY(v[0], v[1], true), t -> Math.abs(t[0]) == t[1], v);
        });
    m.add(
        s -> {
          IntVar[] v = {
            newVar(s, "a", rnd), newVar(s, "b", rnd), newVar(s, "c", rnd), newVar(s, "m", rnd)
          };
          return new Model(
              new Max(new IntVar[] {v[0], v[1], v[2]}, v[3]),
              t -> Math.max(t[0], Math.max(t[1], t[2])) == t[3],
              v);
        });
    m.add(
        s -> {
          IntVar[] v = {newVar(s, "x", rnd), newVar(s, "y", rnd)};
          return new Model(new XneqY(v[0], v[1]), t -> t[0] != t[1], v);
        });
    m.add(
        s -> {
          IntVar[] v = {newVar(s, "x", rnd), newVar(s, "y", rnd), new BooleanVar(s, "b")};
          return new Model(
              new Reified(new XlteqY(v[0], v[1]), (BooleanVar) v[2]),
              t -> (t[0] <= t[1]) == (t[2] == 1),
              v);
        });
    m.add(
        s -> {
          IntVar[] v = {
            new BooleanVar(s, "a"),
            new BooleanVar(s, "b"),
            new BooleanVar(s, "c"),
            newVar(s, "x", rnd)
          };
          int[] w = {1, 2, 1, -1};
          return new Model(new LinearInt(v, w, "==", 0), t -> t[0] + 2 * t[1] + t[2] == t[3], v);
        });
    m.add(
        s -> {
          IntVar[] v = {
            newVar(s, "a", rnd), newVar(s, "b", rnd), newVar(s, "c", rnd), newVar(s, "d", rnd)
          };
          int[] d = {
            2 + rnd.nextInt(3), 2 + rnd.nextInt(3), 2 + rnd.nextInt(3), 2 + rnd.nextInt(3)
          };
          int[] r = {
            1 + rnd.nextInt(2), 1 + rnd.nextInt(2), 1 + rnd.nextInt(2), 1 + rnd.nextInt(2)
          };
          int limit = 2;
          IntVar[] durations = new IntVar[4];
          IntVar[] resources = new IntVar[4];
          for (int k = 0; k < 4; k++) {
            durations[k] = new IntVar(s, d[k], d[k]);
            resources[k] = new IntVar(s, r[k], r[k]);
          }
          Predicate<int[]> fits =
              t -> {
                for (int time = -10; time < 12; time++) {
                  int load = 0;
                  for (int k = 0; k < 4; k++) {
                    if (t[k] <= time && time < t[k] + d[k]) {
                      load += r[k];
                    }
                  }
                  if (load > limit) {
                    return false;
                  }
                }
                return true;
              };
          return new Model(
              new Cumulative(v, durations, resources, new IntVar(s, limit, limit)), fits, v);
        });
    m.add(
        s -> {
          IntVar[] v = {
            newVar(s, "a", rnd),
            newVar(s, "b", rnd),
            newVar(s, "c", rnd),
            new IntVar(s, "limit", 1, 2),
            new IntVar(s, "use", 1, 2)
          };
          int[] d = {2 + rnd.nextInt(3), 2 + rnd.nextInt(3), 2 + rnd.nextInt(3)};
          IntVar[] durations = new IntVar[3];
          IntVar[] resources = {v[4], new IntVar(s, 1, 1), new IntVar(s, 1, 1)};
          for (int k = 0; k < 3; k++) {
            durations[k] = new IntVar(s, d[k], d[k]);
          }
          Predicate<int[]> fits =
              t -> {
                for (int time = -10; time < 12; time++) {
                  int load = 0;
                  for (int k = 0; k < 3; k++) {
                    if (t[k] <= time && time < t[k] + d[k]) {
                      load += k == 0 ? t[4] : 1;
                    }
                  }
                  if (load > t[3]) {
                    return false;
                  }
                }
                return true;
              };
          return new Model(
              new Cumulative(Arrays.copyOf(v, 3), durations, resources, v[3]), fits, v);
        });
    m.add(
        s -> {
          // a variable duration and a variable resource use, tasks using most of the limit
          IntVar[] v = {
            newVar(s, "a", rnd),
            newVar(s, "b", rnd),
            newVar(s, "c", rnd),
            new IntVar(s, "length", 1, 4),
            new IntVar(s, "use", 1, 3)
          };
          int[] d = {0, 1 + rnd.nextInt(3), 1 + rnd.nextInt(3)};
          int[] r = {1 + rnd.nextInt(3), 0, 1 + rnd.nextInt(3)};
          IntVar[] durations = {v[3], new IntVar(s, d[1], d[1]), new IntVar(s, d[2], d[2])};
          IntVar[] resources = {new IntVar(s, r[0], r[0]), v[4], new IntVar(s, r[2], r[2])};
          Predicate<int[]> fits =
              t -> {
                for (int time = -10; time < 12; time++) {
                  int load = 0;
                  for (int k = 0; k < 3; k++) {
                    int length = k == 0 ? t[3] : d[k];
                    if (t[k] <= time && time < t[k] + length) {
                      load += k == 1 ? t[4] : r[k];
                    }
                  }
                  if (load > 3) {
                    return false;
                  }
                }
                return true;
              };
          return new Model(
              new Cumulative(Arrays.copyOf(v, 3), durations, resources, new IntVar(s, 3, 3)),
              fits,
              v);
        });
    m.add(
        s -> {
          IntVar[] v = {
            newVar(s, "a", rnd),
            newVar(s, "b", rnd),
            newVar(s, "c", rnd),
            new BooleanVar(s, "p"),
            new BooleanVar(s, "q"),
            new BooleanVar(s, "r")
          };
          int[] d = {2 + rnd.nextInt(3), 2 + rnd.nextInt(3), 2 + rnd.nextInt(3)};
          IntVar[] durations = new IntVar[3];
          IntVar[] resources = new IntVar[3];
          for (int k = 0; k < 3; k++) {
            durations[k] = new IntVar(s, d[k], d[k]);
            resources[k] = new IntVar(s, 1, 1);
          }
          Predicate<int[]> fits =
              t -> {
                for (int time = -10; time < 12; time++) {
                  int load = 0;
                  for (int k = 0; k < 3; k++) {
                    if (t[3 + k] == 1 && t[k] <= time && time < t[k] + d[k]) {
                      load++;
                    }
                  }
                  if (load > 1) {
                    return false;
                  }
                }
                return true;
              };
          return new Model(
              new CumulativeOptional(
                  Arrays.copyOf(v, 3),
                  durations,
                  resources,
                  new IntVar(s, 1, 1),
                  Arrays.copyOfRange(v, 3, 6)),
              fits,
              v);
        });
    m.add(
        s -> {
          IntVar[] v = {
            newVar(s, "a", rnd),
            newVar(s, "b", rnd),
            newVar(s, "c", rnd),
            newVar(s, "d", rnd),
            new IntVar(s, "n", 1, 4)
          };
          return new Model(
              new Values(Arrays.copyOf(v, 4), v[4]),
              t -> Arrays.stream(t, 0, 4).distinct().count() == t[4],
              v);
        });
    m.add(
        s -> {
          IntVar[] v = {
            newVar(s, "a", rnd), newVar(s, "b", rnd), newVar(s, "c", rnd), newVar(s, "d", rnd)
          };
          int counter = 1 + rnd.nextInt(2);
          int value = rnd.nextInt(3) - 1;
          return rnd.nextBoolean()
              ? new Model(
                  new AtMost(v, counter, value),
                  t -> Arrays.stream(t).filter(w -> w == value).count() <= counter,
                  v)
              : new Model(
                  new AtLeast(v, counter + 1, value),
                  t -> Arrays.stream(t).filter(w -> w == value).count() > counter,
                  v);
        });
    return m;
  }

  private static boolean distinct(int[] t) {
    for (int i = 0; i < t.length; i++) {
      for (int j = i + 1; j < t.length; j++) {
        if (t[i] == t[j]) {
          return false;
        }
      }
    }
    return true;
  }

  // x^y as MiniZinc's int_pow: 1 div x^-y for y < 0, none for x = 0 then
  private static boolean pow(int[] t) {
    if (t[1] < 0) {
      return t[0] != 0 && t[2] == (t[0] == 1 ? 1 : t[0] == -1 ? ((t[1] & 1) == 0 ? 1 : -1) : 0);
    }
    long p = 1;
    for (int i = 0; i < t[1]; i++) {
      p *= t[0];
    }
    return p == t[2];
  }

  /**
   * A start pushed past a compulsory part across a range whose values are all out already: the
   * reason is the compulsory part, not one removal per value (carpet-cutting had cumulative reasons
   * of 300 to 600 atoms this way).
   */
  @Test
  void cumulativeStartAcrossRemovedValuesCitesTheCompulsoryPart() {
    Store store = new Store();
    IntVar s = new IntVar(store, "s", 0, 300);
    IntVar b = new IntVar(store, "b", 50, 60);
    IntVar one = new IntVar(store, 1, 1);
    IntVar[] durations = {new IntVar(store, 10, 10), new IntVar(store, 60, 60)};
    AtomicTrail trail = new AtomicTrail(store);
    store.impose(new Cumulative(new IntVar[] {s, b}, durations, new IntVar[] {one, one}, one));
    store.setLevel(store.level + 1);
    s.domain.inMin(store.level, s, 51);
    for (int v = 52; v <= 105; v++) {
      s.domain.inComplement(store.level, s, v);
    }
    assertThat(store.consistency()).isTrue();
    assertThat(s.min()).isEqualTo(110);
    int entry = -1;
    for (int e = 0; e < trail.size(); e++) {
      if (trail.variable(e) == s && trail.kind(e) == AtomicTrail.GE && trail.value(e) == 110) {
        entry = e;
      }
    }
    assertThat(entry).isNotNegative();
    EntryList reason = new EntryList();
    trail.explain(entry, reason);
    reason.sortUnique(0);
    assertThat(reason.size()).isLessThanOrEqualTo(2);
    trail.detach();
  }

  @Test
  void atomsRebuildDomainsAndReasonsAreSound() {
    Random rnd = new Random(7);
    int checked = 0;
    for (int instance = 0; instance < 300; instance++) {
      for (Function<Store, Model> generator : models(rnd)) {
        checked += dive(generator, rnd);
      }
    }
    assertThat(checked).isGreaterThan(1000);
  }

  /**
   * Products over domains too wide to enumerate supports: their reasons come from the bounds and
   * must still imply the propagated atoms.
   */
  @Test
  void wideProductReasonsAreSound() {
    Random rnd = new Random(13);
    int checked = 0;
    for (int instance = 0; instance < 40; instance++) {
      int lo = -rnd.nextInt(2) * 150;
      checked +=
          dive(
              s -> {
                IntVar[] v = {
                  new IntVar(s, "x", lo, lo + 150),
                  new IntVar(s, "b", 0, 1),
                  new IntVar(s, "z", -160, 160)
                };
                return new Model(new XmulYeqZ(v[0], v[1], v[2]), t -> t[0] * t[1] == t[2], v);
              },
              rnd);
      checked +=
          dive(
              s -> {
                IntVar[] v = {new IntVar(s, "x", -150, 150), new IntVar(s, "z", 0, 400)};
                return new Model(new XmulYeqZ(v[0], v[0], v[1]), t -> t[0] * t[0] == t[1], v);
              },
              rnd);
    }
    assertThat(checked).isGreaterThan(100);
  }

  /**
   * y = |x| with x in -1,000,000..1,000,000: y >= 500,000 leaves x its bounds while a trail
   * records, instead of a gap of 999,999 values that would each be a {@code !=} atom (city-position
   * learnt clauses of thousands of literals). x moves past the gap once a bound falls in it.
   */
  @Test
  void absoluteValueGapIsNotRecordedValueByValue() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", -1_000_000, 1_000_000);
    IntVar y = new IntVar(store, "y", 0, 1_000_000);
    AtomicTrail trail = new AtomicTrail(store);
    store.impose(new AbsXeqY(x, y));
    assertThat(store.consistency()).isTrue();
    store.setLevel(store.level + 1);
    y.domain.inMin(store.level, y, 500_000);
    assertThat(store.consistency()).isTrue();
    assertThat(trail.size()).isLessThan(10);
    assertThat(x.getSize()).isEqualTo(2_000_001);
    store.setLevel(store.level + 1);
    x.domain.inMin(store.level, x, -10);
    assertThat(store.consistency()).isTrue();
    assertThat(x.min()).isEqualTo(500_000);
    trail.detach();
  }

  /**
   * x + y = z with x fixed: without a trail y takes the holes of z shifted, while a trail records
   * it keeps to the bounds, since each copied hole would be a {@code !=} atom of its own (celar
   * frequency differences made 280k SAT variables in 30 s). The solutions stay the same: y = 2
   * fails once y is fixed.
   */
  @Test
  void sumWithFixedTermKeepsToBoundsWhileRecording() {
    for (boolean recording : new boolean[] {false, true}) {
      Store store = new Store();
      IntVar x = new IntVar(store, "x", 3, 3);
      IntVar y = new IntVar(store, "y", 0, 20);
      IntVar z = new IntVar(store, "z", 0, 20);
      for (int v = 1; v <= 19; v += 2) {
        z.domain.inComplement(store.level, z, v);
      }
      AtomicTrail trail = recording ? new AtomicTrail(store) : null;
      store.impose(new XplusYeqZ(x, y, z));
      assertThat(store.consistency()).isTrue();
      assertThat(y.min()).isEqualTo(1);
      assertThat(y.max()).isEqualTo(17);
      assertThat(y.getSize()).isEqualTo(recording ? 17 : 9);
      assertThat(y.domain.contains(2)).isEqualTo(recording);
      if (trail != null) {
        store.setLevel(store.level + 1);
        y.domain.in(store.level, y, 2, 2);
        assertThat(store.consistency()).isFalse();
        trail.detach();
      }
    }
  }

  /**
   * x + 19 y - z = 19 (or_matching_orig): z has lost 19..84, and x != 9 with y >= 5 leaves 1..18
   * and 85 without a support, so domain consistency moves z from 1 to 86. The reason of z >= 86
   * must hold the holes 81..84, which have supports in the domains of x and y; it held only the
   * holes next to the bound, and admitted z = 81 (a wrong optimum under --lcg).
   */
  @Test
  void linearIntDomBoundReasonHoldsEveryHoleItSkips() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 19);
    IntVar y = new IntVar(store, "y", 1, 19);
    IntVar z = new IntVar(store, "z", 1, 361);
    AtomicTrail trail = new AtomicTrail(store);
    store.impose(new LinearIntDom(new IntVar[] {x, y, z}, new int[] {1, 19, -1}, "==", 19));
    assertThat(store.consistency()).isTrue();
    store.setLevel(store.level + 1);
    z.domain.in(store.level, z, new IntervalDomain(1, 361).subtract(19, 84));
    assertThat(store.consistency()).isTrue();
    store.setLevel(store.level + 1);
    x.domain.inComplement(store.level, x, 9);
    y.domain.inMin(store.level, y, 5);
    assertThat(store.consistency()).isTrue();
    assertThat(z.min()).isEqualTo(86);
    int zBound = -1;
    for (int e = 0; e < trail.size(); e++) {
      if (trail.variable(e) == z && trail.kind(e) == AtomicTrail.GE && trail.value(e) == 86) {
        zBound = e;
      }
    }
    EntryList reason = new EntryList();
    assertThat(trail.explain(zBound, reason)).isTrue();
    for (int u = 81; u <= 84; u++) {
      boolean excluded = false;
      for (int k = 0; k < reason.size(); k++) {
        int f = reason.get(k);
        if (trail.variable(f) == z
            && (trail.kind(f) == AtomicTrail.NE && trail.value(f) == u
                || trail.kind(f) == AtomicTrail.GE && trail.value(f) > u
                || trail.kind(f) == AtomicTrail.LE && trail.value(f) < u)) {
          excluded = true;
        }
      }
      assertThat(excluded)
          .as("z = %d (x = %d, y = 5) is excluded by the reason", u, u - 76)
          .isTrue();
    }
    trail.detach();
  }

  /**
   * x * b = z with x in 1..1000 and b in 0..1: z >= 500 propagates x >= 500, which removes more
   * values than supports are enumerated for. Its reason is z >= 500, not the generic one.
   */
  @Test
  void wideProductBoundHasItsOwnReason() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 1000);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar z = new IntVar(store, "z", 0, 1000);
    AtomicTrail trail = new AtomicTrail(store);
    store.impose(new XmulYeqZ(x, b, z));
    assertThat(store.consistency()).isTrue();
    store.setLevel(store.level + 1);
    z.domain.inMin(store.level, z, 500);
    assertThat(store.consistency()).isTrue();
    assertThat(x.min()).isEqualTo(500);
    int xBound = -1;
    int zBound = -1;
    for (int e = 0; e < trail.size(); e++) {
      if (trail.variable(e) == x && trail.kind(e) == AtomicTrail.GE) {
        xBound = e;
      }
      if (trail.variable(e) == z && trail.kind(e) == AtomicTrail.GE && trail.value(e) == 500) {
        zBound = e;
      }
    }
    EntryList reason = new EntryList();
    assertThat(trail.explain(xBound, reason)).isTrue();
    assertThat(reason.size()).isEqualTo(1);
    assertThat(reason.get(0)).isEqualTo(zBound);
    trail.detach();
  }

  /**
   * x * x = z with x in 0..1566 (gbac): z <= 10000 propagates x <= 100, explained by z <= 10000.
   */
  @Test
  void wideSquareBoundHasItsOwnReason() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 1566);
    IntVar z = new IntVar(store, "z", 0, 1566 * 1566);
    AtomicTrail trail = new AtomicTrail(store);
    store.impose(new XmulYeqZ(x, x, z));
    assertThat(store.consistency()).isTrue();
    store.setLevel(store.level + 1);
    z.domain.inMax(store.level, z, 10000);
    assertThat(store.consistency()).isTrue();
    assertThat(x.max()).isEqualTo(100);
    int xBound = -1;
    int zBound = -1;
    for (int e = 0; e < trail.size(); e++) {
      if (trail.variable(e) == x && trail.kind(e) == AtomicTrail.LE) {
        xBound = e;
      }
      if (trail.variable(e) == z && trail.kind(e) == AtomicTrail.LE && trail.value(e) == 10000) {
        zBound = e;
      }
    }
    EntryList reason = new EntryList();
    assertThat(trail.explain(xBound, reason)).isTrue();
    assertThat(reason.size()).isEqualTo(1);
    assertThat(reason.get(0)).isEqualTo(zBound);
    trail.detach();
  }

  /**
   * x + y + 2z <= 10 with x >= 1, then x >= 2, then y >= 4 propagating z <= 2: the bound z <= 2
   * needs x + y >= 5 only, so its reason cites x >= 1, the earlier and weaker entry of x.
   */
  @Test
  void linearReasonCitesTheEarliestBoundTheSlackAllows() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 5);
    IntVar y = new IntVar(store, "y", 0, 5);
    IntVar z = new IntVar(store, "z", 0, 5);
    AtomicTrail trail = new AtomicTrail(store);
    LinearInt sum = new LinearInt(new IntVar[] {x, y, z}, new int[] {1, 1, 2}, "<=", 10);
    store.impose(sum);
    assertThat(store.consistency()).isTrue();
    int[] steps = {1, 2};
    for (int v : steps) {
      store.setLevel(store.level + 1);
      x.domain.inMin(store.level, x, v);
      assertThat(store.consistency()).isTrue();
    }
    store.setLevel(store.level + 1);
    y.domain.inMin(store.level, y, 4);
    assertThat(store.consistency()).isTrue();
    assertThat(z.max()).isEqualTo(2);
    int zBound = -1;
    int xFirst = -1;
    for (int e = 0; e < trail.size(); e++) {
      if (trail.variable(e) == z && trail.kind(e) == AtomicTrail.LE && trail.value(e) == 2) {
        zBound = e;
      }
      if (trail.variable(e) == x && trail.kind(e) == AtomicTrail.GE && trail.value(e) == 1) {
        xFirst = e;
      }
    }
    assertThat(zBound).isNotNegative();
    assertThat(xFirst).isNotNegative();
    EntryList reason = new EntryList();
    assertThat(trail.explain(zBound, reason)).isTrue();
    List<Integer> cited = new ArrayList<>();
    for (int k = 0; k < reason.size(); k++) {
      cited.add(reason.get(k));
    }
    assertThat(cited).contains(xFirst).hasSize(2);
    trail.detach();
  }

  /**
   * 2a + b + c <= 1 fails with a, b, c >= 1, which leaves a slack of 2: it drops either a, or b and
   * c. The reason drops the two cheaper terms and cites a >= 1 alone.
   */
  @Test
  void linearReasonDropsTheCheapestTermsFirst() {
    Store store = new Store();
    IntVar a = new IntVar(store, "a", 0, 5);
    IntVar b = new IntVar(store, "b", 0, 5);
    IntVar c = new IntVar(store, "c", 0, 5);
    AtomicTrail trail = new AtomicTrail(store);
    for (IntVar v : new IntVar[] {a, b, c}) {
      store.setLevel(store.level + 1);
      v.domain.inMin(store.level, v, 1);
    }
    EntryList reason = new EntryList();
    assertThat(
            LinearExplanation.explainFailure(
                trail, new IntVar[] {a, b, c}, new long[] {2, 1, 1}, 1, true, false, reason))
        .isTrue();
    assertThat(reason.size()).isEqualTo(1);
    assertThat(trail.variable(reason.get(0))).isSameAs(a);
    trail.detach();
  }

  /**
   * 3x + y - x <= 4, an aggregated row with x at weights of both signs: after y >= 2, the bound x
   * <= 1 follows from 2x <= 4 - 2, and its checked reason is y >= 2.
   */
  @Test
  void checkedLinearReasonMergesAVariableOfBothSigns() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 5);
    IntVar y = new IntVar(store, "y", 0, 5);
    AtomicTrail trail = new AtomicTrail(store);
    store.setLevel(store.level + 1);
    y.domain.inMin(store.level, y, 2);
    x.domain.inMax(store.level, x, 1);
    int yBound = trail.size() - 2;
    int xBound = trail.size() - 1;
    assertThat(trail.variable(xBound)).isSameAs(x);
    IntVar[] vars = {x, y, x};
    long[] weights = {3, 1, -1};
    EntryList reason = new EntryList();
    assertThat(
            LinearExplanation.explainChecked(trail, xBound, vars, weights, 4, true, false, reason))
        .isTrue();
    assertThat(reason.size()).isEqualTo(1);
    assertThat(reason.get(0)).isEqualTo(yBound);
    // x <= 0 does not follow, so the checked reason refuses it
    store.setLevel(store.level + 1);
    x.domain.inMax(store.level, x, 0);
    reason = new EntryList();
    assertThat(
            LinearExplanation.explainChecked(
                trail, trail.size() - 1, vars, weights, 4, true, false, reason))
        .isFalse();
    trail.detach();
  }

  /**
   * 2^62 x + 2^62 y >= 0 with x = y = 1 holds, but its sum, 2^63, overflows a long to a negative
   * number: neither a failure nor a disentailment may be claimed.
   */
  @Test
  void linearReasonsRefuseSumsThatOverflow() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 1);
    IntVar y = new IntVar(store, "y", 0, 1);
    AtomicTrail trail = new AtomicTrail(store);
    store.setLevel(store.level + 1);
    x.domain.in(store.level, x, 1, 1);
    y.domain.in(store.level, y, 1, 1);
    IntVar[] vars = {x, y};
    long[] weights = {1L << 62, 1L << 62};
    EntryList reason = new EntryList();
    assertThat(LinearExplanation.explainFailure(trail, vars, weights, 0, false, true, reason))
        .isFalse();
    LinearForm violated = new LinearForm(vars, weights, -1, LinearForm.LE);
    assertThat(violated.explainEntailed(trail, trail.size(), reason)).isFalse();
    trail.detach();
  }

  @Test
  void holesAreRecordedOnceForEveryDomainClass() {
    Random rnd = new Random(11);
    int[] spans = {40, 600, LazyBitSetDomain.MAX_SPAN + 10};
    for (int run = 0; run < 300; run++) {
      Store store = new Store();
      int span = spans[run % spans.length];
      IntVar[] vars = new IntVar[2];
      IntDomain[] initial = new IntDomain[2];
      for (int i = 0; i < 2; i++) {
        vars[i] = new IntVar(store, "x" + i, -5, span - 5);
        for (int k = rnd.nextInt(4); k > 0; k--) {
          int lo = rnd.nextInt(span) - 5;
          vars[i].domain.inComplement(store.level, vars[i], lo, lo + rnd.nextInt(5));
        }
        initial[i] = vars[i].dom().cloneLight();
      }
      AtomicTrail trail = new AtomicTrail(store);
      for (int step = 0; step < 60; step++) {
        if (store.level > 0 && rnd.nextInt(4) == 0) {
          int target = rnd.nextInt(store.level);
          while (store.level > target) {
            store.removeLevel(store.level);
            store.setLevel(store.level - 1);
          }
        } else {
          store.setLevel(store.level + 1);
          IntVar x = vars[rnd.nextInt(2)];
          if (x.getSize() > 1) {
            prune(x, store, rnd);
          }
        }
        checkRebuildOnce(trail, vars, initial);
      }
      trail.detach();
    }
  }

  @Test
  void excludedBeforeCitesTheLatestEntryThatRemovesTheValue() {
    Random rnd = new Random(12);
    int[] spans = {40, 600, (1 << 16) + 10};
    for (int run = 0; run < 90; run++) {
      Store store = new Store();
      int span = spans[run % spans.length];
      IntVar[] vars = new IntVar[2];
      for (int i = 0; i < 2; i++) {
        vars[i] = new IntVar(store, "x" + i, -5, span - 5);
      }
      AtomicTrail trail = new AtomicTrail(store);
      EntryList out = new EntryList();
      for (int step = 0; step < 60; step++) {
        if (store.level > 0 && rnd.nextInt(4) == 0) {
          int target = rnd.nextInt(store.level);
          while (store.level > target) {
            store.removeLevel(store.level);
            store.setLevel(store.level - 1);
          }
        } else {
          store.setLevel(store.level + 1);
          IntVar x = vars[rnd.nextInt(2)];
          if (x.getSize() > 1) {
            prune(x, store, rnd);
          }
        }
        for (int probe = 0; probe < 40; probe++) {
          IntVar x = vars[rnd.nextInt(2)];
          int v = -6 + rnd.nextInt(Math.min(span, 800) + 2);
          int position = rnd.nextInt(trail.size() + 1);
          int expected = -1;
          for (int e = 0; e < position; e++) {
            if (trail.variable(e) == x && removes(trail, e, v)) {
              expected = e;
            }
          }
          out.clear();
          boolean inRoot = trail.rootDomain(x).contains(v);
          assertThat(trail.excludedBefore(x, v, position, out))
              .as("%s != %d before %d", x.id(), v, position)
              .isEqualTo(!inRoot || expected >= 0);
          assertThat(out.size()).isEqualTo(inRoot && expected >= 0 ? 1 : 0);
          if (out.size() == 1) {
            assertThat(out.get(0)).isEqualTo(expected);
          }
        }
      }
      trail.detach();
    }
  }

  @Test
  void entryIndexAgreesWithAMap() {
    Random rnd = new Random(13);
    EntryIndex index = new EntryIndex();
    java.util.Map<Long, Integer> expected = new java.util.HashMap<>();
    for (int step = 0; step < 200_000; step++) {
      int variable = rnd.nextInt(40);
      int value = rnd.nextInt(60) - 30;
      long k = ((long) variable << 32) | (value & 0xffffffffL);
      if (rnd.nextInt(3) == 0) {
        index.remove(variable, value);
        expected.remove(k);
      } else if (rnd.nextBoolean()) {
        index.put(variable, value, step);
        expected.put(k, step);
      }
      assertThat(index.get(variable, value)).isEqualTo(expected.getOrDefault(k, -1));
    }
    for (var e : expected.entrySet()) {
      assertThat(index.get((int) (e.getKey() >>> 32), (int) (long) e.getKey()))
          .isEqualTo(e.getValue());
    }
  }

  @Test
  void elementFailureCitesTheFewerAtoms() {
    Store store = new Store();
    int n = 200;
    int[] list = new int[n];
    for (int j = 0; j < n; j++) {
      list[j] = j % 4;
    }
    IntVar index = new IntVar(store, "index", 1, n);
    IntVar value = new IntVar(store, "value", 0, 3);
    AtomicTrail trail = new AtomicTrail(store);
    store.setLevel(store.level + 1);
    for (int c = 0; c < 3; c++) {
      value.domain.inComplement(store.level, value, c);
    }
    // the index leaves out every position of constant 3 and 40 positions of constant 0
    store.setLevel(store.level + 1);
    for (int j = 0; j < n; j++) {
      if (list[j] == 3 || list[j] == 0 && j < 160) {
        index.domain.inComplement(store.level, index, j + 1);
      }
    }
    EntryList out = new EntryList();
    assertThat(ElementExplanation.explainFailure(trail, index, list, value, 0, out)).isTrue();
    // at most 3 atoms of the value and 50 of the index, against 90 of the index first
    assertThat(out.size()).isLessThanOrEqualTo(53);
    for (int j = 0; j < n; j++) {
      boolean covered = false;
      for (int k = 0; k < out.size(); k++) {
        int e = out.get(k);
        covered |=
            trail.variable(e) == index && removes(trail, e, j + 1)
                || trail.variable(e) == value && removes(trail, e, list[j]);
      }
      assertThat(covered).as("position %d", j).isTrue();
    }
    trail.detach();
  }

  private static boolean removes(AtomicTrail trail, int e, int v) {
    int a = trail.value(e);
    return switch (trail.kind(e)) {
      case AtomicTrail.GE -> a > v;
      case AtomicTrail.LE -> a < v;
      default -> a == v;
    };
  }

  // removes a value, a range or values outside a set, or raises a bound, at the current level
  private static void prune(IntVar x, Store store, Random rnd) {
    int a = x.min() + rnd.nextInt(Math.min(x.max() - x.min() + 1, 700));
    int b = a + rnd.nextInt(6);
    switch (rnd.nextInt(5)) {
      case 0 -> x.domain.inComplement(store.level, x, x.dom().nextValue(a));
      case 1 -> {
        if (x.min() < a || b < x.max()) {
          x.domain.inComplement(store.level, x, a, b);
        }
      }
      case 2 -> {
        IntDomain keep = x.dom().subtract(a, b);
        keep = keep.subtract(a + 20, b + 20);
        if (!keep.isEmpty()) {
          x.domain.in(store.level, x, keep);
        }
      }
      case 3 -> x.domain.inMin(store.level, x, Math.min(x.dom().nextValue(a), x.max()));
      default -> x.domain.inMax(store.level, x, Math.max(x.min(), b - 30));
    }
  }

  // rebuilds the domains from the entries, each of which must remove a value
  private static void checkRebuildOnce(AtomicTrail trail, IntVar[] vars, IntDomain[] initial) {
    for (int i = 0; i < vars.length; i++) {
      IntDomain d = initial[i];
      for (int e = 0; e < trail.size(); e++) {
        if (trail.variable(e) == vars[i]) {
          IntDomain next = apply(d, trail, e);
          assertThat(next.getSize()).as("entry %s", trail.atomString(e)).isLessThan(d.getSize());
          d = next;
        }
      }
      assertThat(d.eq(vars[i].dom())).as("%s rebuilt %s", vars[i], d).isTrue();
    }
  }

  private static int dive(Function<Store, Model> generator, Random rnd) {
    Store store = new Store();
    Model model = generator.apply(store);
    IntDomain[] initial = new IntDomain[model.vars.length];
    for (int i = 0; i < initial.length; i++) {
      initial[i] = model.vars[i].dom().cloneLight();
    }
    AtomicTrail trail = new AtomicTrail(store);
    store.impose(model.constraint);
    int checked = 0;
    int base = store.level;
    for (int depth = 0; depth < 8; depth++) {
      store.setLevel(store.level + 1);
      if (depth > 0) {
        decide(model.vars, rnd);
      }
      boolean ok = store.consistency();
      if (!ok) {
        if (store.recentlyFailedConstraint == model.constraint) {
          checkFailure(trail, model, initial);
          checked++;
        }
        break;
      }
      checkRebuild(trail, model.vars, initial);
      checked += checkReasons(trail, model, initial);
    }
    while (store.level > base) {
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
      checkRebuild(trail, model.vars, initial);
    }
    trail.detach();
    return checked;
  }

  private static void decide(IntVar[] vars, Random rnd) {
    IntVar x = vars[rnd.nextInt(vars.length)];
    if (x.singleton()) {
      return;
    }
    int v = x.min() + rnd.nextInt(x.max() - x.min() + 1);
    Store store = x.getStore();
    switch (rnd.nextInt(4)) {
      case 0 -> {
        if (x.domain.contains(v)) {
          x.domain.in(store.level, x, v, v);
        }
      }
      case 1 -> {
        if (x.domain.contains(v) && !x.singleton()) {
          x.domain.inComplement(store.level, x, v);
        }
      }
      case 2 -> x.domain.inMax(store.level, x, Math.max(v, x.min()));
      default -> x.domain.inMin(store.level, x, Math.min(v, x.max()));
    }
  }

  private static IntDomain apply(IntDomain d, AtomicTrail trail, int entry) {
    int v = trail.value(entry);
    return switch (trail.kind(entry)) {
      case AtomicTrail.GE -> d.intersect(v, IntDomain.MAX_INT);
      case AtomicTrail.LE -> d.intersect(IntDomain.MIN_INT, v);
      default -> d.subtract(v);
    };
  }

  private static void checkRebuild(AtomicTrail trail, IntVar[] vars, IntDomain[] initial) {
    for (int i = 0; i < vars.length; i++) {
      IntDomain d = initial[i];
      for (int e = 0; e < trail.size(); e++) {
        if (trail.variable(e) == vars[i]) {
          d = apply(d, trail, e);
        }
      }
      assertThat(d.eq(vars[i].dom())).as("%s rebuilt %s", vars[i], d).isTrue();
    }
  }

  private static int checkReasons(AtomicTrail trail, Model model, IntDomain[] initial) {
    EntryList reason = new EntryList();
    int checked = 0;
    for (int e = 0; e < trail.size(); e++) {
      if (trail.reason(e) != model.constraint) {
        continue;
      }
      reason.clear();
      trail.genericReason(e, reason);
      checkImplied(trail, model, initial, e, reason);
      reason.clear();
      trail.explain(e, reason);
      checkImplied(trail, model, initial, e, reason);
      checked++;
    }
    return checked;
  }

  private static void checkFailure(AtomicTrail trail, Model model, IntDomain[] initial) {
    EntryList reason = new EntryList();
    trail.explainFailure(model.constraint, reason);
    IntDomain[] box = initial.clone();
    for (int k = 0; k < reason.size(); k++) {
      int r = reason.get(k);
      int i = indexOf(model.vars, trail.variable(r));
      box[i] = apply(box[i], trail, r);
    }
    assertThat(anySolution(box, 0, new int[box.length], model.relation))
        .as("the failure reason of %s has a solution", model.constraint)
        .isFalse();
  }

  private static boolean anySolution(IntDomain[] box, int i, int[] t, Predicate<int[]> relation) {
    if (i == box.length) {
      return relation.test(t);
    }
    for (int v = box[i].min(); v <= box[i].max(); v++) {
      if (box[i].contains(v)) {
        t[i] = v;
        if (anySolution(box, i + 1, t, relation)) {
          return true;
        }
      }
    }
    return false;
  }

  private static void checkImplied(
      AtomicTrail trail, Model model, IntDomain[] initial, int e, EntryList reason) {
    {
      IntDomain[] box = initial.clone();
      for (int k = 0; k < reason.size(); k++) {
        int r = reason.get(k);
        assertThat(r).isLessThan(e);
        int i = indexOf(model.vars, trail.variable(r));
        box[i] = apply(box[i], trail, r);
      }
      int target = indexOf(model.vars, trail.variable(e));
      int[] t = new int[box.length];
      assertThat(enumerate(box, 0, t, model.relation, trail, e, target))
          .as("reason of %s does not imply it", trail.atomString(e))
          .isTrue();
    }
  }

  private static boolean enumerate(
      IntDomain[] box,
      int i,
      int[] t,
      Predicate<int[]> relation,
      AtomicTrail trail,
      int e,
      int target) {
    if (i == box.length) {
      if (!relation.test(t)) {
        return true;
      }
      int v = trail.value(e);
      return switch (trail.kind(e)) {
        case AtomicTrail.GE -> t[target] >= v;
        case AtomicTrail.LE -> t[target] <= v;
        default -> t[target] != v;
      };
    }
    if (box[i].isEmpty()) {
      return true;
    }
    for (int v = box[i].min(); v <= box[i].max(); v++) {
      if (box[i].contains(v)) {
        t[i] = v;
        if (!enumerate(box, i + 1, t, relation, trail, e, target)) {
          return false;
        }
      }
    }
    return true;
  }

  private static int indexOf(IntVar[] vars, IntVar x) {
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] == x) {
        return i;
      }
    }
    throw new IllegalStateException(x + " is not in the model");
  }

  /**
   * Unary resources whose start windows, set at one level, leave no schedule. The time table and
   * the energy of windows miss some of these failures, which went to the generic reason; the unary
   * rules explain them by a task they push past its latest start. Every failure has an explanation
   * of its own, and no schedule fits the bounds it cites.
   */
  @Test
  void unaryFailuresHaveTheirOwnSoundExplanation() {
    Random rnd = new Random(5);
    int failures = 0;
    for (int it = 0; it < 20000; it++) {
      int n = 3 + rnd.nextInt(3);
      int[] d = new int[n];
      int[] lo = new int[n];
      int[] hi = new int[n];
      for (int i = 0; i < n; i++) {
        d[i] = 1 + rnd.nextInt(5);
        lo[i] = rnd.nextInt(10);
        hi[i] = lo[i] + rnd.nextInt(6);
      }
      Store store = new Store();
      IntVar[] s = new IntVar[n];
      IntVar[] durations = new IntVar[n];
      IntVar[] resources = new IntVar[n];
      for (int i = 0; i < n; i++) {
        s[i] = new IntVar(store, "s" + i, 0, 20);
        durations[i] = new IntVar(store, d[i], d[i]);
        resources[i] = new IntVar(store, 1, 1);
      }
      CumulativeUnary unary = new CumulativeUnary(s, durations, resources, new IntVar(store, 1, 1));
      store.impose(unary);
      assertThat(store.consistency()).isTrue();
      AtomicTrail trail = new AtomicTrail(store);
      store.setLevel(store.level + 1);
      boolean consistent;
      try {
        for (int i = 0; i < n; i++) {
          s[i].domain.in(store.level, s[i], lo[i], hi[i]);
        }
        consistent = store.consistency();
      } catch (FailException e) {
        consistent = false;
      }
      if (consistent || store.recentlyFailedConstraint != unary) {
        trail.detach();
        continue;
      }
      failures++;
      EntryList reason = new EntryList();
      assertThat(unary.explainFailure(trail, reason)).as("instance %d", it).isTrue();
      // the bounds cited, from the starts' initial domains 0..20
      int[] min = new int[n];
      int[] max = new int[n];
      Arrays.fill(max, 20);
      for (int k = 0; k < reason.size(); k++) {
        int e = reason.get(k);
        for (int i = 0; i < n; i++) {
          if (trail.variable(e) == s[i]) {
            if (trail.kind(e) == AtomicTrail.GE) {
              min[i] = Math.max(min[i], trail.value(e));
            } else if (trail.kind(e) == AtomicTrail.LE) {
              max[i] = Math.min(max[i], trail.value(e));
            }
          }
        }
      }
      assertThat(schedules(min, max, d, new int[n], 0)).as("instance %d", it).isFalse();
      trail.detach();
    }
    assertThat(failures).isGreaterThan(100);
  }

  // whether the tasks fit on one machine with starts within [min, max]
  private static boolean schedules(int[] min, int[] max, int[] d, int[] start, int i) {
    if (i == d.length) {
      return true;
    }
    for (int t = min[i]; t <= max[i]; t++) {
      boolean free = true;
      for (int k = 0; k < i && free; k++) {
        free = t + d[i] <= start[k] || start[k] + d[k] <= t;
      }
      if (free) {
        start[i] = t;
        if (schedules(min, max, d, start, i + 1)) {
          return true;
        }
      }
    }
    return false;
  }

  /**
   * nvalue and at_most removals with reasons of their own: the variables fixed to other values
   * (gfd-schedule had a million generic reasons of 64 atoms from these two constraints).
   */
  @Test
  void nvalueAndAtMostRemovalsHaveTheirOwnReason() {
    Store store = new Store();
    IntVar[] x = new IntVar[5];
    for (int i = 0; i < x.length; i++) {
      x[i] = new IntVar(store, "x" + i, 0, 6);
    }
    IntVar n = new IntVar(store, "n", 0, 2);
    Constraint values = new Values(x, n);
    Constraint atMost = new AtMost(x, 1, 5);
    store.impose(values);
    store.impose(atMost);
    assertThat(store.consistency()).isTrue();
    AtomicTrail trail = new AtomicTrail(store);
    store.setLevel(store.level + 1);
    x[0].domain.in(store.level, x[0], 1, 1);
    x[1].domain.in(store.level, x[1], 5, 5);
    x[2].domain.inComplement(store.level, x[2], 3);
    assertThat(store.consistency()).isTrue();
    assertThat(x[2].dom().toString()).isEqualTo("1");
    int explained = 0;
    EntryList reason = new EntryList();
    for (int e = 0; e < trail.size(); e++) {
      Constraint c = trail.reason(e);
      if (c == values || c == atMost) {
        reason.clear();
        assertThat(c instanceof Explainable own && own.explain(trail, e, reason))
            .as("%s for %s", c, trail.atomString(e))
            .isTrue();
        explained++;
      }
    }
    assertThat(explained).isGreaterThanOrEqualTo(6);
    trail.detach();
  }

  /**
   * A bound of a variable over sparse values (cubes, as in routing-flexible) moves past a root hole
   * wider than 4096 values: the linear reason needs no atom for the hole and stays its own (it was
   * the generic reason).
   */
  @Test
  void linearBoundAcrossAWideRootHoleHasItsOwnReason() {
    Store store = new Store();
    IntervalDomain cubes = new IntervalDomain();
    for (int k = 0; k <= 100; k++) {
      cubes.unionAdapt(k * k * k, k * k * k);
    }
    IntVar x = new IntVar(store, "x", cubes);
    IntVar z = new IntVar(store, "z", 0, 100);
    LinearInt sum = new LinearInt(new IntVar[] {x, z}, new int[] {1, 1}, "<=", 1_000_010);
    store.impose(sum);
    assertThat(store.consistency()).isTrue();
    AtomicTrail trail = new AtomicTrail(store);
    store.setLevel(store.level + 1);
    z.domain.inMin(store.level, z, 20);
    assertThat(store.consistency()).isTrue();
    assertThat(x.max()).isEqualTo(99 * 99 * 99);
    int entry = trail.lastEntry(x, trail.size());
    assertThat(trail.reason(entry)).isSameAs(sum);
    EntryList reason = new EntryList();
    assertThat(sum.explain(trail, entry, reason)).isTrue();
    assertThat(reason.size()).isEqualTo(1);
    assertThat(trail.variable(reason.get(0))).isSameAs(z);
    trail.detach();
  }

  /**
   * The diffn profile rule: a and b, of height 1 and width 2, both at x = 0 in a strip of height 2,
   * leave no room at x in 0..1 for r, whose x already lost 2. The rule removes 0..1 and the domain
   * moves on to 3, so the reason of x >= 3 cites the hole x != 2 besides the bounds of a and b
   * (pillars-and-planks, cargo).
   */
  @Test
  void diffnProfileReasonCitesTheHolesItsBoundSkipped() {
    Store store = new Store();
    IntVar rx = new IntVar(store, "rx", 0, 5);
    IntVar ax = new IntVar(store, "ax", 0, 3);
    IntVar bx = new IntVar(store, "bx", 0, 3);
    IntVar[] x = {rx, ax, bx};
    IntVar[] y = new IntVar[3];
    for (int i = 0; i < 3; i++) {
      y[i] = new IntVar(store, "y" + i, 0, 1);
    }
    IntVar one = new IntVar(store, 1, 1);
    IntVar two = new IntVar(store, 2, 2);
    AtomicTrail trail = new AtomicTrail(store);
    store.impose(new Diffn(x, y, new IntVar[] {one, two, two}, new IntVar[] {one, one, one}));
    assertThat(store.consistency()).isTrue();
    store.setLevel(store.level + 1);
    rx.domain.inComplement(store.level, rx, 2);
    assertThat(store.consistency()).isTrue();
    store.setLevel(store.level + 1);
    ax.domain.inMax(store.level, ax, 0);
    bx.domain.inMax(store.level, bx, 0);
    assertThat(store.consistency()).isTrue();
    assertThat(rx.min()).isEqualTo(3);
    int bound = -1;
    int hole = -1;
    for (int e = 0; e < trail.size(); e++) {
      if (trail.variable(e) == rx && trail.kind(e) == AtomicTrail.GE && trail.value(e) == 3) {
        bound = e;
      }
      if (trail.variable(e) == rx && trail.kind(e) == AtomicTrail.NE && trail.value(e) == 2) {
        hole = e;
      }
    }
    assertThat(bound).isNotNegative();
    assertThat(hole).isNotNegative();
    EntryList reason = new EntryList();
    assertThat(trail.explain(bound, reason)).isTrue();
    List<Integer> cited = new ArrayList<>();
    for (int k = 0; k < reason.size(); k++) {
      cited.add(reason.get(k));
    }
    assertThat(cited).contains(hole);
    trail.detach();
  }
}
