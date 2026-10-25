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
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Max;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
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
}
