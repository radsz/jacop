/*
 * SetLcgFuzzTest.java
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

package org.jacop.jasat.lcg;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.fail;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.Predicate;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.search.IndomainMin;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
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
import org.jacop.set.constraints.CardA;
import org.jacop.set.constraints.CardAeqX;
import org.jacop.set.constraints.ChannelBoolSet;
import org.jacop.set.constraints.ChannelIntSet;
import org.jacop.set.constraints.EinA;
import org.jacop.set.constraints.ElementSet;
import org.jacop.set.constraints.ElementSetVariable;
import org.jacop.set.constraints.Match;
import org.jacop.set.constraints.PartitionSet;
import org.jacop.set.constraints.SetMirror;
import org.jacop.set.constraints.SinA;
import org.jacop.set.constraints.SumWeightedSet;
import org.jacop.set.constraints.XeqA;
import org.jacop.set.constraints.XinA;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMax;
import org.jacop.set.search.IndomainSetMin;
import org.jacop.set.search.OutdomainSetSelect;
import org.junit.jupiter.api.Test;

/**
 * Lazy clause generation on random small models of set variables: the set constraints that explain
 * their own prunings (AleB, AltB, AllDisjoint, CardAeqX, ChannelBoolSet, EinA, ElementSet,
 * ElementSetVariable, PartitionSet, XinA, the set mirror and the set search's element choice) and
 * the other set constraints, mixed with integer constraints, with the sets mirrored as the front
 * end mirrors them. Most constraints hold on a hidden assignment, so most models have solutions.
 *
 * <p>{@code agreesWithBruteForceOnRandomSetModels}: LCG with checked explanations must agree with a
 * brute-force enumeration over all assignments of the sets and the integer variables: the same
 * satisfiability, the same optimum, every solution a solution, and for satisfaction the same set of
 * solutions when it enumerates. {@code reasonsHoldOnRandomDives}: random dives over the
 * memberships, cardinalities and integer variables, and every reason of every atom and failure is
 * checked by {@link org.jacop.lcg.ExplanationChecker} and, since the checker cannot copy some set
 * constraints (the mirror among them), by brute force over the constraint's relation.
 *
 * <p>The number of models is set by {@code setlcg.fuzz.runs} (default 500) and {@code
 * setlcg.fuzz.dives} (default 20000), the first seed by {@code setlcg.fuzz.seed}. With {@code
 * setlcg.fuzz.repeated=true} a third of the set positions of a constraint repeat a set already
 * there; with {@code setlcg.fuzz.large=true} the models are larger and depth-first search is the
 * reference when the brute force is too large; with {@code setlcg.fuzz.focus} set to a
 * comma-separated list of the cases of {@code post}, two constraints in three are drawn from those
 * cases. A failure names the seed, which rebuilds the same model.
 */
class SetLcgFuzzTest {

  private static final int RUNS = Integer.getInteger("setlcg.fuzz.runs", 500);

  private static final int SEED = Integer.getInteger("setlcg.fuzz.seed", 1);

  private static final boolean REPEATED = Boolean.getBoolean("setlcg.fuzz.repeated");

  private static final int[] FOCUS = cases(System.getProperty("setlcg.fuzz.focus"));

  // with setlcg.fuzz.large=true the models are larger, and depth-first search over the sets is the
  // reference when the brute force is too large
  private static final boolean LARGE = Boolean.getBoolean("setlcg.fuzz.large");

  private static final boolean VERBOSE = Boolean.getBoolean("setlcg.fuzz.verbose");

  // the elements of the sets lie in LOW..LOW+9; bit e - LOW of a mask is element e
  private static final int LOW = -1;

  private static final int CASES = 32;

  // brute-force nodes after which a model is skipped
  private static final long BRUTE_LIMIT = 4_000_000;

  private static int[] cases(String s) {
    if (s == null || s.isBlank()) {
      return null;
    }
    return Arrays.stream(s.split(",")).mapToInt(c -> Integer.parseInt(c.trim())).toArray();
  }

  /** An assignment of the model's integer variables (values) and sets (masks). */
  record Assignment(int[] ints, long[] sets) {}

  /** A relation of the model on some of its variables, for the brute force. */
  private record Check(int[] intVars, int[] setVars, Predicate<Assignment> holds) {}

  private static final class TooLarge extends RuntimeException {
    private static final long serialVersionUID = 1L;

    TooLarge() {
      super(null, null, false, false);
    }
  }

  /** A random model; built twice from the same seed when needed. */
  static final class Model {
    final Store store = new Store();
    final Random rnd;
    final List<IntVar> ints = new ArrayList<>();
    final List<SetVar> sets = new ArrayList<>();
    final List<Check> checks = new ArrayList<>();
    final Map<Object, Check> relations = new java.util.IdentityHashMap<>();
    final List<String> posted = new ArrayList<>();
    IntVar objective;
    int[] objectiveVars;
    int[] objectiveWeights;
    boolean mirrorFirst;
    int annotation;
    final List<Integer> values = new ArrayList<>();

    Model(long seed) {
      rnd = new Random(seed);
      int universe = LARGE ? 5 + rnd.nextInt(4) : 3 + rnd.nextInt(4);
      int base = LOW + rnd.nextInt(3);
      boolean sparse = rnd.nextInt(4) == 0;
      for (int v = base; values.size() < universe && v <= LOW + 9; v++) {
        if (!sparse || rnd.nextBoolean()) {
          values.add(v);
        }
      }
      int nSets = LARGE ? 3 + rnd.nextInt(4) : 2 + rnd.nextInt(4);
      for (int i = 0; i < nSets; i++) {
        IntervalDomain lub = new IntervalDomain();
        IntervalDomain glb = new IntervalDomain();
        boolean ground = rnd.nextInt(10) == 0;
        boolean withGlb = rnd.nextInt(3) == 0;
        for (int v : values) {
          if (rnd.nextInt(5) > 0) {
            lub.unionAdapt(v, v);
            if (ground ? rnd.nextBoolean() : withGlb && rnd.nextInt(4) == 0) {
              glb.unionAdapt(v, v);
            }
          }
        }
        SetVar s =
            new SetVar(store, "s" + i, new BoundSetDomain(glb, ground ? glb.cloneLight() : lub));
        sets.add(s);
      }
      int nInts = 1 + rnd.nextInt(3);
      for (int i = 0; i < nInts; i++) {
        ints.add(new IntVar(store, "x" + i, randomDomain(-1, 6)));
      }
      int nBools = rnd.nextInt(3);
      for (int i = 0; i < nBools; i++) {
        ints.add(new BooleanVar(store, "b" + i));
      }
      int n = LARGE ? 4 + rnd.nextInt(6) : 2 + rnd.nextInt(6);
      for (int k = 0; k < n; k++) {
        int c =
            FOCUS != null && rnd.nextInt(3) > 0
                ? FOCUS[rnd.nextInt(FOCUS.length)]
                : rnd.nextInt(CASES);
        post(c);
      }
      if (rnd.nextInt(4) > 0) {
        objective();
      }
      mirrorFirst = rnd.nextBoolean();
      annotation = rnd.nextInt(5);
    }

    IntervalDomain randomDomain(int lo, int hi) {
      IntervalDomain d = new IntervalDomain();
      int from = lo + rnd.nextInt(3);
      int to = hi - rnd.nextInt(3);
      for (int v = from; v <= to; v++) {
        if (rnd.nextInt(4) > 0) {
          d.unionAdapt(v, v);
        }
      }
      if (d.isEmpty()) {
        d.unionAdapt(from, from);
      }
      return d;
    }

    // a set between the bounds of set a: with up true, the lower bound and some of the open
    // elements, else the upper bound less some of them; sometimes one element is changed
    IntDomain between(int a, boolean up) {
      IntDomain glb = s(a).domain.glb();
      IntDomain lub = s(a).domain.lub();
      IntervalDomain d = new IntervalDomain();
      for (var e = lub.valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        if (glb.contains(v) || (up ? rnd.nextInt(3) == 0 : rnd.nextInt(3) > 0)) {
          d.unionAdapt(v, v);
        }
      }
      if (rnd.nextInt(6) == 0) {
        int v = LOW + rnd.nextInt(7);
        return d.contains(v) ? d.subtract(v) : d.union(v);
      }
      return d;
    }

    IntDomain randomSet() {
      IntervalDomain d = new IntervalDomain();
      for (int v = LOW; v <= LOW + 6; v++) {
        if (values.contains(v) ? rnd.nextInt(2) == 0 : rnd.nextInt(8) == 0) {
          d.unionAdapt(v, v);
        }
      }
      return d;
    }

    int set(List<Integer> picked) {
      if (REPEATED && !picked.isEmpty() && rnd.nextInt(3) == 0) {
        int s = picked.get(rnd.nextInt(picked.size()));
        picked.add(s);
        return s;
      }
      int s = rnd.nextInt(sets.size());
      picked.add(s);
      return s;
    }

    int[] setList(int min, int max) {
      int k = min + rnd.nextInt(max - min + 1);
      List<Integer> picked = new ArrayList<>();
      int[] r = new int[k];
      if (!REPEATED && k <= sets.size()) {
        List<Integer> all = new ArrayList<>();
        for (int i = 0; i < sets.size(); i++) {
          all.add(i);
        }
        java.util.Collections.shuffle(all, rnd);
        for (int i = 0; i < k; i++) {
          r[i] = all.get(i);
        }
        return r;
      }
      for (int i = 0; i < k; i++) {
        r[i] = set(picked);
      }
      return r;
    }

    int[] twoSets() {
      List<Integer> picked = new ArrayList<>();
      int a = set(picked);
      int b = a;
      if (REPEATED && rnd.nextInt(3) == 0) {
        return new int[] {a, a};
      }
      while (b == a && sets.size() > 1) {
        b = rnd.nextInt(sets.size());
      }
      return new int[] {a, b};
    }

    int intVar() {
      return rnd.nextInt(ints.size());
    }

    int newInt(String name, IntDomain d) {
      ints.add(new IntVar(store, name + ints.size(), d));
      return ints.size() - 1;
    }

    int newBool() {
      ints.add(new BooleanVar(store, "c" + ints.size()));
      return ints.size() - 1;
    }

    SetVar s(int i) {
      return sets.get(i);
    }

    IntVar x(int i) {
      return ints.get(i);
    }

    // a hidden assignment: a constraint it violates is left out nine times in ten, so that most
    // models have solutions and need search
    final List<Long> hiddenSets = new ArrayList<>();
    final List<Integer> hiddenInts = new ArrayList<>();

    Assignment hidden() {
      while (hiddenSets.size() < sets.size()) {
        SetVar s = sets.get(hiddenSets.size());
        long m = mask(s.domain.glb());
        for (var e = s.domain.lub().valueEnumeration(); e.hasMoreElements(); ) {
          int v = e.nextElement();
          if (rnd.nextBoolean()) {
            m |= bit(v);
          }
        }
        hiddenSets.add(m);
      }
      while (hiddenInts.size() < ints.size()) {
        IntDomain d = ints.get(hiddenInts.size()).dom();
        int k = rnd.nextInt(d.getSize());
        var e = d.valueEnumeration();
        int v = e.nextElement();
        for (int i = 0; i < k; i++) {
          v = e.nextElement();
        }
        hiddenInts.add(v);
      }
      return new Assignment(
          hiddenInts.stream().mapToInt(Integer::intValue).toArray(),
          hiddenSets.stream().mapToLong(Long::longValue).toArray());
    }

    void add(Object c, int[] intVars, int[] setVars, Predicate<Assignment> holds) {
      if (!holds.test(hidden()) && rnd.nextInt(3) > 0) {
        return;
      }
      posted.add(c.toString());
      checks.add(new Check(intVars, setVars, holds));
      if (c instanceof org.jacop.constraints.Constraint con) {
        relations.put(con, new Check(intVars, setVars, holds));
        store.impose(con);
      }
    }

    /** A primitive set constraint with its relation, for reification and negation. */
    private record Prim(
        PrimitiveConstraint c, int[] intVars, int[] setVars, Predicate<Assignment> holds) {}

    Prim primitive() {
      int[] ab = twoSets();
      int a = ab[0];
      int b = ab[1];
      switch (rnd.nextInt(9)) {
        case 0:
          {
            boolean strict = rnd.nextBoolean();
            return new Prim(
                new AinB(s(a), s(b), strict),
                new int[0],
                ab,
                t -> (t.sets[a] & ~t.sets[b]) == 0 && (!strict || t.sets[a] != t.sets[b]));
          }
        case 1:
          return new Prim(new AeqB(s(a), s(b)), new int[0], ab, t -> t.sets[a] == t.sets[b]);
        case 2:
          {
            int e = LOW + rnd.nextInt(7);
            boolean strict = rnd.nextInt(3) == 0;
            return new Prim(
                new EinA(e, s(a), strict),
                new int[0],
                new int[] {a},
                t -> has(t.sets[a], e) && (!strict || Long.bitCount(t.sets[a]) >= 2));
          }
        case 3:
          {
            int x = intVar();
            boolean strict = rnd.nextInt(3) == 0;
            return new Prim(
                new XinA(x(x), s(a), strict),
                new int[] {x},
                new int[] {a},
                t -> has(t.sets[a], t.ints[x]) && (!strict || Long.bitCount(t.sets[a]) >= 2));
          }
        case 4:
          return new Prim(
              new AleB(s(a), s(b)), new int[0], ab, t -> lex(t.sets[a], t.sets[b]) <= 0);
        case 5:
          return new Prim(new AltB(s(a), s(b)), new int[0], ab, t -> lex(t.sets[a], t.sets[b]) < 0);
        case 6:
          {
            IntDomain d = rnd.nextInt(3) == 0 ? randomSet() : between(a, true);
            long m = mask(d);
            boolean strict = rnd.nextInt(3) == 0;
            return new Prim(
                new AinS(s(a), d, strict),
                new int[0],
                new int[] {a},
                t -> (t.sets[a] & ~m) == 0 && (!strict || t.sets[a] != m));
          }
        case 7:
          {
            IntDomain d = rnd.nextInt(3) == 0 ? randomSet() : between(a, false);
            long m = mask(d);
            boolean strict = rnd.nextInt(3) == 0;
            return new Prim(
                new SinA(d, s(a), strict),
                new int[0],
                new int[] {a},
                t -> (m & ~t.sets[a]) == 0 && (!strict || t.sets[a] != m));
          }
        default:
          {
            IntDomain d = rnd.nextInt(4) == 0 ? randomSet() : between(a, rnd.nextBoolean());
            long m = mask(d);
            return new Prim(new AeqS(s(a), d), new int[0], new int[] {a}, t -> t.sets[a] == m);
          }
      }
    }

    void post(int c) {
      switch (c) {
        case 0, 1, 2, 3, 4, 5, 6:
          {
            // the primitive set constraints, alone
            Prim p = primitive();
            add(p.c, p.intVars, p.setVars, p.holds);
            break;
          }
        case 7:
          {
            int[] l = setList(2, 4);
            SetVar[] v = new SetVar[l.length];
            for (int i = 0; i < l.length; i++) {
              v[i] = s(l[i]);
            }
            add(
                new AllDisjoint(v),
                new int[0],
                l,
                t -> {
                  for (int i = 0; i < l.length; i++) {
                    for (int j = i + 1; j < l.length; j++) {
                      if ((t.sets[l[i]] & t.sets[l[j]]) != 0) {
                        return false;
                      }
                    }
                  }
                  return true;
                });
            break;
          }
        case 8, 9:
          {
            int a = rnd.nextInt(sets.size());
            int x = rnd.nextInt(3) == 0 ? intVar() : newInt("card", randomDomain(-1, 5));
            add(
                new CardAeqX(s(a), x(x)),
                new int[] {x},
                new int[] {a},
                t -> Long.bitCount(t.sets[a]) == t.ints[x]);
            break;
          }
        case 10:
          {
            int a = rnd.nextInt(sets.size());
            int len0 = 1 + rnd.nextInt(5);
            int offset0 = LOW + rnd.nextInt(3);
            if (rnd.nextBoolean() && !s(a).domain.lub().isEmpty()) {
              // the Booleans cover the upper bound, or one element less
              offset0 = s(a).domain.lub().min() + rnd.nextInt(2);
              len0 = Math.max(1, s(a).domain.lub().max() - offset0 + 1 - rnd.nextInt(2));
            }
            int len = len0;
            int offset = offset0;
            int[] bi = new int[len];
            IntVar[] bv = new IntVar[len];
            for (int i = 0; i < len; i++) {
              bi[i] = rnd.nextInt(4) == 0 && i > 0 ? bi[rnd.nextInt(i)] : newBool();
              bv[i] = x(bi[i]);
            }
            add(
                new ChannelBoolSet(bv, s(a), offset),
                bi,
                new int[] {a},
                t -> {
                  long m = 0;
                  for (int i = 0; i < len; i++) {
                    if (t.ints[bi[i]] == 1) {
                      m |= bit(i + offset);
                    }
                  }
                  return t.sets[a] == m;
                });
            break;
          }
        case 11:
          {
            int a = rnd.nextInt(sets.size());
            int len = 1 + rnd.nextInt(4);
            int offset = rnd.nextInt(3) - 1;
            IntDomain[] list = new IntDomain[len];
            long[] m = new long[len];
            for (int i = 0; i < len; i++) {
              list[i] = rnd.nextInt(3) == 0 ? randomSet() : between(a, rnd.nextBoolean());
              m[i] = mask(list[i]);
            }
            int x = rnd.nextBoolean() ? intVar() : newInt("idx", randomDomain(-1, len + 1));
            add(
                new ElementSet(x(x), list, s(a), offset),
                new int[] {x},
                new int[] {a},
                t -> {
                  int i = t.ints[x] - 1 - offset;
                  return i >= 0 && i < len && t.sets[a] == m[i];
                });
            break;
          }
        case 12, 13:
          {
            int[] l = setList(1, 3);
            int len = l.length;
            int a = rnd.nextInt(sets.size());
            int offset = rnd.nextInt(3) - 1;
            SetVar[] v = new SetVar[len];
            for (int i = 0; i < len; i++) {
              v[i] = s(l[i]);
            }
            int x = rnd.nextBoolean() ? intVar() : newInt("idx", randomDomain(-1, len + 1));
            int[] all = Arrays.copyOf(l, len + 1);
            all[len] = a;
            add(
                new ElementSetVariable(x(x), v, s(a), offset),
                new int[] {x},
                all,
                t -> {
                  int i = t.ints[x] - 1 - offset;
                  return i >= 0 && i < len && t.sets[a] == t.sets[l[i]];
                });
            break;
          }
        case 14:
          {
            int[] l = setList(2, 3);
            IntDomain u = randomSet();
            if (rnd.nextInt(3) > 0) {
              // a universe within the union of the upper bounds
              IntDomain union = new IntervalDomain();
              for (int i : l) {
                union = union.union(s(i).domain.lub());
              }
              u =
                  union.intersect(
                      rnd.nextBoolean() ? union : randomSet().union(union.subtract(randomSet())));
            }
            long um = mask(u);
            SetVar[] v = new SetVar[l.length];
            for (int i = 0; i < l.length; i++) {
              v[i] = s(l[i]);
            }
            add(
                new PartitionSet(v, u),
                new int[0],
                l,
                t -> {
                  long union = 0;
                  for (int i = 0; i < l.length; i++) {
                    if ((union & t.sets[l[i]]) != 0) {
                      return false;
                    }
                    union |= t.sets[l[i]];
                  }
                  return union == um;
                });
            break;
          }
        case 15, 16:
          {
            int a = rnd.nextInt(sets.size());
            int x = rnd.nextInt(3) == 0 ? newInt("e", randomDomain(-1, 6)) : intVar();
            boolean strict = rnd.nextInt(4) == 0;
            add(
                new XinA(x(x), s(a), strict),
                new int[] {x},
                new int[] {a},
                t -> has(t.sets[a], t.ints[x]) && (!strict || Long.bitCount(t.sets[a]) >= 2));
            break;
          }
        case 17:
          {
            int[] l = setList(3, 3);
            int a = l[0];
            int b = l[1];
            int d = l[2];
            int op = rnd.nextInt(3);
            Object con =
                switch (op) {
                  case 0 -> new AunionBeqC(s(a), s(b), s(d));
                  case 1 -> new AintersectBeqC(s(a), s(b), s(d));
                  default -> new AdiffBeqC(s(a), s(b), s(d));
                };
            add(
                con,
                new int[0],
                l,
                t -> {
                  long r =
                      switch (op) {
                        case 0 -> t.sets[a] | t.sets[b];
                        case 1 -> t.sets[a] & t.sets[b];
                        default -> t.sets[a] & ~t.sets[b];
                      };
                  return t.sets[d] == r;
                });
            break;
          }
        case 18:
          {
            int[] ab = twoSets();
            add(
                new AdisjointB(s(ab[0]), s(ab[1])),
                new int[0],
                ab,
                t -> (t.sets[ab[0]] & t.sets[ab[1]]) == 0);
            break;
          }
        case 19:
          {
            int a = rnd.nextInt(sets.size());
            int lo = rnd.nextInt(3);
            int hi = lo + rnd.nextInt(3);
            add(
                new CardA(s(a), lo, hi),
                new int[0],
                new int[] {a},
                t -> Long.bitCount(t.sets[a]) >= lo && Long.bitCount(t.sets[a]) <= hi);
            break;
          }
        case 20:
          {
            int a = rnd.nextInt(sets.size());
            List<Integer> el = new ArrayList<>();
            for (int v = LOW; v <= LOW + 6; v++) {
              if (s(a).domain.lub().contains(v) ? rnd.nextInt(8) > 0 : rnd.nextInt(4) == 0) {
                el.add(v);
              }
            }
            int[] elements = el.stream().mapToInt(Integer::intValue).toArray();
            int[] weights = new int[elements.length];
            for (int i = 0; i < weights.length; i++) {
              weights[i] = rnd.nextInt(4);
            }
            int x = newInt("w", randomDomain(0, 8));
            add(
                new SumWeightedSet(s(a), elements, weights, x(x)),
                new int[] {x},
                new int[] {a},
                t -> {
                  long m = t.sets[a];
                  int sum = 0;
                  for (int i = 0; i < elements.length; i++) {
                    if (has(m, elements[i])) {
                      sum += weights[i];
                      m &= ~bit(elements[i]);
                    }
                  }
                  return m == 0 && sum == t.ints[x];
                });
            break;
          }
        case 21:
          {
            int a = rnd.nextInt(sets.size());
            int len = 1 + rnd.nextInt(3);
            int[] xi = new int[len];
            IntVar[] xv = new IntVar[len];
            for (int i = 0; i < len; i++) {
              xi[i] = rnd.nextBoolean() ? intVar() : newInt("m", randomDomain(-1, 6));
              xv[i] = x(xi[i]);
            }
            add(
                new Match(s(a), xv),
                xi,
                new int[] {a},
                t -> {
                  long m = 0;
                  for (int i = 0; i < len; i++) {
                    if (i > 0 && t.ints[xi[i]] <= t.ints[xi[i - 1]]) {
                      return false;
                    }
                    if (t.ints[xi[i]] < LOW || t.ints[xi[i]] > LOW + 9) {
                      return false;
                    }
                    m |= bit(t.ints[xi[i]]);
                  }
                  return m == t.sets[a];
                });
            break;
          }
        case 22:
          {
            int[] l = setList(1, 3);
            int lenX = 1 + rnd.nextInt(3);
            int offInt = rnd.nextInt(2);
            int offSet = rnd.nextInt(2);
            int[] xi = new int[lenX];
            IntVar[] xv = new IntVar[lenX];
            for (int i = 0; i < lenX; i++) {
              xi[i] = newInt("ch", randomDomain(-1, 4));
              xv[i] = x(xi[i]);
            }
            SetVar[] v = new SetVar[l.length];
            for (int i = 0; i < l.length; i++) {
              v[i] = s(l[i]);
            }
            add(
                new ChannelIntSet(xv, v, offInt, offSet),
                xi,
                l,
                t -> {
                  long[] want = new long[l.length];
                  for (int k = 0; k < lenX; k++) {
                    int j = t.ints[xi[k]] - offSet;
                    if (j < 0 || j >= l.length) {
                      return false;
                    }
                    want[j] |= bit(k + offInt);
                  }
                  for (int j = 0; j < l.length; j++) {
                    if (t.sets[l[j]] != want[j]) {
                      return false;
                    }
                  }
                  return true;
                });
            break;
          }
        case 23:
          {
            int a = rnd.nextInt(sets.size());
            int x = intVar();
            add(
                new XeqA(x(x), s(a)),
                new int[] {x},
                new int[] {a},
                t -> t.sets[a] == bitOrNone(t.ints[x]));
            break;
          }
        case 24, 25:
          {
            Prim p = primitive();
            int b =
                rnd.nextBoolean() && ints.stream().anyMatch(v -> v.min() >= 0 && v.max() <= 1)
                    ? boolIndex()
                    : newBool();
            int[] iv = Arrays.copyOf(p.intVars, p.intVars.length + 1);
            iv[p.intVars.length] = b;
            add(new Reified(p.c, x(b)), iv, p.setVars, t -> p.holds.test(t) == (t.ints[b] == 1));
            break;
          }
        case 26:
          {
            Prim p = primitive();
            add(new Not(p.c), p.intVars, p.setVars, t -> !p.holds.test(t));
            break;
          }
        case 27, 28:
          {
            // a linear relation on integer variables, cardinalities and memberships
            int k = 2 + rnd.nextInt(2);
            int[] xi = new int[k];
            IntVar[] xv = new IntVar[k];
            int[] w = new int[k];
            for (int i = 0; i < k; i++) {
              xi[i] = intVar();
              xv[i] = x(xi[i]);
              w[i] = rnd.nextInt(5) - 2;
              if (w[i] == 0) {
                w[i] = 1;
              }
            }
            String rel = new String[] {"==", "!=", "<=", ">=", "<", ">"}[rnd.nextInt(6)];
            int rhs = rnd.nextInt(7) - 2;
            add(
                new LinearInt(xv, w, rel, rhs),
                xi,
                new int[0],
                t -> {
                  int sum = 0;
                  for (int i = 0; i < k; i++) {
                    sum += w[i] * t.ints[xi[i]];
                  }
                  return switch (rel) {
                    case "==" -> sum == rhs;
                    case "!=" -> sum != rhs;
                    case "<=" -> sum <= rhs;
                    case ">=" -> sum >= rhs;
                    case "<" -> sum < rhs;
                    default -> sum > rhs;
                  };
                });
            break;
          }
        case 29:
          {
            int a = intVar();
            int b = intVar();
            if (a == b) {
              break;
            }
            add(new XneqY(x(a), x(b)), new int[] {a, b}, new int[0], t -> t.ints[a] != t.ints[b]);
            break;
          }
        case 30:
          {
            int a = intVar();
            int b = intVar();
            int d = intVar();
            add(
                new XplusYeqZ(x(a), x(b), x(d)),
                new int[] {a, b, d},
                new int[0],
                t -> t.ints[a] + t.ints[b] == t.ints[d]);
            break;
          }
        default:
          {
            List<Integer> bools = new ArrayList<>();
            for (int i = 0; i < ints.size(); i++) {
              if (x(i).min() >= 0 && x(i).max() <= 1) {
                bools.add(i);
              }
            }
            if (bools.size() < 2) {
              break;
            }
            int[] bi = bools.stream().mapToInt(Integer::intValue).toArray();
            IntVar[] bv = new IntVar[bi.length];
            for (int i = 0; i < bi.length; i++) {
              bv[i] = x(bi[i]);
            }
            int need = rnd.nextInt(bi.length + 1);
            String rel = new String[] {"==", "<=", ">="}[rnd.nextInt(3)];
            IntVar count = new IntVar(store, need, need);
            add(
                new SumBool(bv, rel, count),
                bi,
                new int[0],
                t -> {
                  int sum = 0;
                  for (int i : bi) {
                    sum += t.ints[i];
                  }
                  return rel.equals("==")
                      ? sum == need
                      : rel.equals("<=") ? sum <= need : sum >= need;
                });
            break;
          }
      }
    }

    int boolIndex() {
      List<Integer> bools = new ArrayList<>();
      for (int i = 0; i < ints.size(); i++) {
        if (x(i).min() >= 0 && x(i).max() <= 1) {
          bools.add(i);
        }
      }
      return bools.get(rnd.nextInt(bools.size()));
    }

    void objective() {
      // cardinalities of some sets (new CardAeqX) and integer variables
      int k = 1 + rnd.nextInt(3);
      int[] xi = new int[k];
      int[] w = new int[k];
      for (int i = 0; i < k; i++) {
        if (rnd.nextBoolean()) {
          int a = rnd.nextInt(sets.size());
          int x = newInt("oc", new IntervalDomain(0, 10));
          int fa = a;
          int fx = x;
          add(
              new CardAeqX(s(a), x(x)),
              new int[] {x},
              new int[] {a},
              t -> Long.bitCount(t.sets[fa]) == t.ints[fx]);
          xi[i] = x;
        } else {
          xi[i] = intVar();
        }
        w[i] = rnd.nextInt(7) - 3;
      }
      int bound = 0;
      IntVar[] xv = new IntVar[k + 1];
      int[] wv = new int[k + 1];
      for (int i = 0; i < k; i++) {
        xv[i] = x(xi[i]);
        wv[i] = w[i];
        bound += Math.abs(w[i]) * Math.max(Math.abs(xv[i].min()), Math.abs(xv[i].max()));
      }
      objective = new IntVar(store, "obj", -bound, bound);
      xv[k] = objective;
      wv[k] = -1;
      store.impose(new LinearInt(xv, wv, "==", 0));
      posted.add("objective " + Arrays.toString(w) + " " + Arrays.toString(xi));
      objectiveVars = xi;
      objectiveWeights = w;
    }

    int objectiveValue(Assignment t) {
      int sum = 0;
      for (int i = 0; i < objectiveVars.length; i++) {
        sum += objectiveWeights[i] * t.ints[objectiveVars[i]];
      }
      return sum;
    }

    boolean holds(Assignment t) {
      for (Check c : checks) {
        if (!c.holds.test(t)) {
          return false;
        }
      }
      return true;
    }

    String describe() {
      StringBuilder s = new StringBuilder();
      for (SetVar v : sets) {
        s.append(v).append('\n');
      }
      for (IntVar v : ints) {
        s.append(v).append('\n');
      }
      for (String c : posted) {
        s.append(c).append('\n');
      }
      s.append("mirrorFirst=").append(mirrorFirst).append(" annotation=").append(annotation);
      return s.toString();
    }
  }

  static long bit(int e) {
    return 1L << (e - LOW);
  }

  static long bitOrNone(int e) {
    return e < LOW || e > LOW + 40 ? -1 : bit(e);
  }

  static boolean has(long m, int e) {
    return e >= LOW && e <= LOW + 40 && (m & bit(e)) != 0;
  }

  static long mask(IntDomain d) {
    long m = 0;
    for (var e = d.valueEnumeration(); e.hasMoreElements(); ) {
      m |= bit(e.nextElement());
    }
    return m;
  }

  // the lexicographic order of the sorted elements: negative when a is before b
  static int lex(long a, long b) {
    while (a != 0 && b != 0) {
      long la = Long.lowestOneBit(a);
      long lb = Long.lowestOneBit(b);
      if (la != lb) {
        return la < lb ? -1 : 1;
      }
      a &= ~la;
      b &= ~lb;
    }
    if (a == 0 && b == 0) {
      return 0;
    }
    return a == 0 ? -1 : 1;
  }

  /** The brute force: solutions (when collect) and the optimum, over the model's root domains. */
  static final class Brute {
    final Model model;
    final int nSets;
    final int[][] setChoices;
    final int[][] intChoices;
    final List<List<Check>> due = new ArrayList<>();
    final Set<String> solutions = new HashSet<>();
    final boolean collect;
    long nodes;
    boolean found;
    int best = Integer.MAX_VALUE;
    long[] sv;
    int[] iv;

    Brute(Model model, boolean collect) {
      this.model = model;
      this.collect = collect;
      nSets = model.sets.size();
      setChoices = new int[nSets][];
      int n = nSets + model.ints.size();
      for (int i = 0; i < n; i++) {
        due.add(new ArrayList<>());
      }
      for (Check c : model.checks) {
        int last = -1;
        for (int s : c.setVars) {
          last = Math.max(last, s);
        }
        for (int x : c.intVars) {
          last = Math.max(last, nSets + x);
        }
        due.get(Math.max(last, 0)).add(c);
      }
      intChoices = new int[model.ints.size()][];
      for (int i = 0; i < intChoices.length; i++) {
        IntDomain d = model.ints.get(i).dom();
        intChoices[i] = new int[d.getSize()];
        int k = 0;
        for (var e = d.valueEnumeration(); e.hasMoreElements(); ) {
          intChoices[i][k++] = e.nextElement();
        }
      }
      sv = new long[nSets];
      iv = new int[model.ints.size()];
    }

    void run() {
      Assignment t = new Assignment(iv, sv);
      go(0, t);
    }

    private void go(int p, Assignment t) {
      if (++nodes > BRUTE_LIMIT) {
        throw new TooLarge();
      }
      int n = nSets + iv.length;
      if (p == n) {
        found = true;
        if (model.objective != null) {
          best = Math.min(best, model.objectiveValue(t));
        }
        if (collect) {
          solutions.add(key(t));
        }
        return;
      }
      if (p < nSets) {
        SetVar s = model.sets.get(p);
        long glb = mask(s.domain.glb());
        long lub = mask(s.domain.lub());
        long open = lub & ~glb;
        // every subset of the open elements
        long sub = 0;
        do {
          sv[p] = glb | sub;
          if (ok(p, t)) {
            go(p + 1, t);
          }
          sub = (sub - open) & open;
        } while (sub != 0);
      } else {
        int i = p - nSets;
        for (int v : intChoices[i]) {
          iv[i] = v;
          if (ok(p, t)) {
            go(p + 1, t);
          }
        }
      }
    }

    private boolean ok(int p, Assignment t) {
      for (Check c : due.get(p)) {
        if (!c.holds.test(t)) {
          return false;
        }
      }
      return true;
    }
  }

  static String key(Assignment t) {
    return Arrays.toString(t.ints) + Arrays.toString(t.sets);
  }

  // the store's current (fixed) values
  static Assignment current(Model model) {
    int[] iv = new int[model.ints.size()];
    for (int i = 0; i < iv.length; i++) {
      IntVar x = model.ints.get(i);
      if (!x.singleton()) {
        throw new AssertionError("not fixed at a solution: " + x);
      }
      iv[i] = x.value();
    }
    long[] sv = new long[model.sets.size()];
    for (int i = 0; i < sv.length; i++) {
      SetVar s = model.sets.get(i);
      if (!s.singleton()) {
        throw new AssertionError("not fixed at a solution: " + s);
      }
      sv[i] = mask(s.dom().glb());
    }
    return new Assignment(iv, sv);
  }

  static final Map<String, long[]> STATISTICS = new TreeMap<>();

  /** Runs one seed; returns 1 for SAT, 0 for UNSAT, -1 when skipped. */
  static int runSeed(long seed) {
    Model ref;
    try {
      ref = new Model(seed);
    } catch (FailException | IllegalArgumentException e) {
      // a constraint failed when it was imposed, or its constructor rejects a repeated variable
      return -1;
    }
    Brute brute = new Brute(ref, ref.objective == null);
    try {
      brute.run();
    } catch (TooLarge e) {
      if (!LARGE) {
        return -1;
      }
      brute = dfs(seed);
      if (brute == null) {
        return -1;
      }
    }
    Model model = new Model(seed);
    String where = "seed " + seed + "\n" + model.describe();
    List<String> found = new ArrayList<>();
    int status;
    int value = 0;
    try {
      boolean consistent = true;
      if (model.mirrorFirst) {
        mirror(model);
      }
      consistent = model.store.consistency();
      if (!model.mirrorFirst && consistent) {
        mirror(model);
        consistent = model.store.consistency();
      }
      if (!consistent) {
        status = CdclSolver.UNSAT;
      } else {
        LcgSolver solver = new LcgSolver(model.store);
        solver.setChecking(true);
        solver.sat().setExternalReasonKeep(1 + (int) (seed % 3));
        annotate(solver, model, seed);
        int[] best = {Integer.MAX_VALUE};
        solver.onSolution(
            () -> {
              Assignment t = current(model);
              if (!model.holds(t)) {
                throw new AssertionError("LCG solution is no solution: " + key(t));
              }
              found.add(key(t));
              if (model.objective != null) {
                best[0] = model.objectiveValue(t);
                if (model.objective.value() != best[0]) {
                  throw new AssertionError("objective " + model.objective + " != " + best[0]);
                }
              }
            });
        boolean enumerate = model.objective == null && brute.solutions.size() <= 500;
        if (enumerate) {
          List<IntVar> shown = new ArrayList<>(model.ints);
          for (SetVar s : model.sets) {
            if (s.lcgMirror() != null) {
              shown.addAll(Arrays.asList(s.lcgMirror().mirrorVariables()));
            }
          }
          assertThat(solver.setEnumeration(shown)).as(where).isTrue();
        }
        status = model.objective == null ? solver.solve() : solver.minimize(model.objective);
        if (model.objective != null && status == CdclSolver.SAT) {
          value = solver.value(model.objective);
          assertThat(best[0]).as(where).isEqualTo(value);
        }
        if (enumerate) {
          // the enumeration ends with UNSAT once every solution is found
          assertThat(new HashSet<>(found)).as(where).isEqualTo(brute.solutions);
          assertThat(found).as(where).doesNotHaveDuplicates();
          status = found.isEmpty() ? CdclSolver.UNSAT : CdclSolver.SAT;
        }
        synchronized (STATISTICS) {
          solver
              .explanationStatistics()
              .forEach((k, v) -> STATISTICS.merge(k, v.clone(), SetLcgFuzzTest::add));
        }
      }
    } catch (RuntimeException | AssertionError e) {
      throw new AssertionError(where, e);
    }
    assertThat(status).as(where).isNotEqualTo(CdclSolver.UNKNOWN);
    assertThat(status == CdclSolver.SAT).as(where).isEqualTo(brute.found);
    if (model.objective != null && brute.found) {
      assertThat(value).as(where).isEqualTo(brute.best);
    }
    return brute.found ? 1 : 0;
  }

  /**
   * The reference by depth-first search over the sets and the integer variables, or null on
   * time-out.
   */
  static Brute dfs(long seed) {
    Model model = new Model(seed);
    Brute r = new Brute(model, model.objective == null);
    if (!model.store.consistency()) {
      return r;
    }
    List<SetVar> open = new ArrayList<>(model.sets);
    List<SelectChoicePoint<? extends Var>> selects = new ArrayList<>();
    selects.add(new SimpleSelect<>(open.toArray(new SetVar[0]), null, new IndomainSetMin<>()));
    selects.add(new SimpleSelect<>(model.ints.toArray(new IntVar[0]), null, new IndomainMin<>()));
    if (model.objective != null) {
      selects.add(new SimpleSelect<>(new IntVar[] {model.objective}, null, new IndomainMin<>()));
    }
    org.jacop.search.SequenceSelect select = new org.jacop.search.SequenceSelect(selects);
    org.jacop.search.DepthFirstSearch<Var> search = new org.jacop.search.DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setTimeOut(5);
    Brute out = r;
    search.setSolutionListener(
        new org.jacop.search.SimpleSolutionListener<Var>() {
          @Override
          public boolean executeAfterSolution(
              org.jacop.search.Search<Var> s, SelectChoicePoint<Var> sel) {
            Assignment t = current(model);
            if (!model.holds(t)) {
              throw new AssertionError("DFS solution is no solution: " + key(t));
            }
            out.found = true;
            if (out.collect) {
              out.solutions.add(key(t));
            }
            return super.executeAfterSolution(s, sel);
          }
        });
    if (model.objective == null) {
      search.getSolutionListener().searchAll(true);
      search.getSolutionListener().recordSolutions(false);
      search.getSolutionListener().setSolutionLimit(501);
      search.labeling(model.store, select);
    } else {
      boolean found = search.labeling(model.store, select, model.objective);
      if (found) {
        r.best = search.getCostValue();
      }
    }
    if (search.timeOutOccured) {
      return null;
    }
    return r;
  }

  static void mirror(Model model) {
    for (int i = 0; i < model.sets.size(); i++) {
      SetVar s = model.sets.get(i);
      if (!s.singleton() && s.lcgMirror() == null) {
        SetMirror m = new SetMirror(s);
        model.relations.put(m, new Check(new int[0], new int[] {i}, t -> true));
        model.store.impose(m);
      }
    }
  }

  /**
   * Checks a reason by brute force over the root domains of the constraint's variables (the
   * memberships and cardinality of a mirrored set): no assignment satisfies the relation, the
   * reason and the negated atom (entry -1: a failure). Null when it holds or the constraint has no
   * relation here.
   */
  static String bruteReason(
      Model model,
      org.jacop.lcg.AtomicTrail trail,
      org.jacop.constraints.Constraint c,
      org.jacop.lcg.EntryList reason,
      int entry) {
    Check chk = model.relations.get(c);
    if (chk == null) {
      return null;
    }
    Map<IntVar, IntDomain> dom = new java.util.IdentityHashMap<>();
    int[] ints = Arrays.stream(chk.intVars).distinct().toArray();
    int[] sets = Arrays.stream(chk.setVars).distinct().toArray();
    for (int i : ints) {
      dom.put(model.ints.get(i), trail.rootDomain(model.ints.get(i)).cloneLight());
    }
    for (int i : sets) {
      SetMirror m = model.sets.get(i).lcgMirror();
      if (m != null) {
        for (IntVar v : m.mirrorVariables()) {
          dom.put(v, trail.rootDomain(v).cloneLight());
        }
      }
    }
    StringBuilder text = new StringBuilder();
    for (int k = 0; k < reason.size(); k++) {
      int f = reason.get(k);
      IntVar x = trail.variable(f);
      if (!dom.containsKey(x)) {
        return "reason atom on a variable outside the constraint: " + trail.atomString(f);
      }
      text.append(trail.atomString(f)).append(' ');
      int v = trail.value(f);
      int slack = reason.slack(k);
      dom.put(
          x,
          switch (trail.kind(f)) {
            case org.jacop.lcg.AtomicTrail.GE -> dom.get(x).intersect(v - slack, IntDomain.MAX_INT);
            case org.jacop.lcg.AtomicTrail.LE -> dom.get(x).intersect(IntDomain.MIN_INT, v + slack);
            default -> dom.get(x).subtract(v);
          });
    }
    if (entry >= 0) {
      IntVar x = trail.variable(entry);
      if (!dom.containsKey(x)) {
        return "atom on a variable outside the constraint";
      }
      int v = trail.value(entry);
      dom.put(
          x,
          switch (trail.kind(entry)) {
            case org.jacop.lcg.AtomicTrail.GE -> dom.get(x).intersect(IntDomain.MIN_INT, v - 1);
            case org.jacop.lcg.AtomicTrail.LE -> dom.get(x).intersect(v + 1, IntDomain.MAX_INT);
            default -> dom.get(x).intersect(v, v);
          });
    }
    // the choices: an integer variable's values, or a set's memberships
    List<long[]> choices = new ArrayList<>();
    for (int i : ints) {
      IntDomain d = dom.get(model.ints.get(i));
      long[] values = new long[d.getSize()];
      int k = 0;
      for (var e = d.valueEnumeration(); e.hasMoreElements(); ) {
        values[k++] = e.nextElement();
      }
      choices.add(values);
    }
    for (int i : sets) {
      SetVar sv = model.sets.get(i);
      SetMirror m = sv.lcgMirror();
      List<Long> masks = new ArrayList<>();
      if (m == null) {
        masks.add(mask(sv.domain.glb()));
      } else {
        int[] el = m.elements();
        long base = 0;
        for (int e = LOW; e <= LOW + 40; e++) {
          if (m.inRootGlb(e)) {
            base |= bit(e);
          }
        }
        IntDomain card = dom.get(m.cardinality());
        for (int bits = 0; bits < 1 << el.length; bits++) {
          long mk = base;
          boolean ok = true;
          for (int j = 0; j < el.length && ok; j++) {
            int b = bits >> j & 1;
            ok = dom.get(m.member(el[j])).contains(b);
            if (b == 1) {
              mk |= bit(el[j]);
            }
          }
          if (ok && card.contains(Long.bitCount(mk))) {
            masks.add(mk);
          }
        }
      }
      choices.add(masks.stream().mapToLong(Long::longValue).toArray());
    }
    long total = 1;
    for (long[] ch : choices) {
      if (ch.length == 0) {
        return null;
      }
      total *= ch.length;
      if (total > 2_000_000) {
        return null;
      }
    }
    int[] iv = new int[model.ints.size()];
    long[] svals = new long[model.sets.size()];
    Assignment t = new Assignment(iv, svals);
    int[] pos = new int[choices.size()];
    while (true) {
      for (int k = 0; k < ints.length; k++) {
        iv[ints[k]] = (int) choices.get(k)[pos[k]];
      }
      for (int k = 0; k < sets.length; k++) {
        svals[sets[k]] = choices.get(ints.length + k)[pos[ints.length + k]];
      }
      if (chk.holds.test(t)) {
        return "reason " + text + "does not imply it: " + key(t) + " is a solution";
      }
      int k = 0;
      while (k < pos.length && ++pos[k] == choices.get(k).length) {
        pos[k] = 0;
        k++;
      }
      if (k == pos.length) {
        return null;
      }
    }
  }

  @SuppressWarnings({"unchecked", "rawtypes"})
  static void annotate(LcgSolver solver, Model model, long seed) {
    List<SetVar> open = new ArrayList<>();
    for (SetVar s : model.sets) {
      if (!s.singleton()) {
        open.add(s);
      }
    }
    if (open.isEmpty() || model.annotation >= 3) {
      return;
    }
    SetVar[] v = open.toArray(new SetVar[0]);
    SelectChoicePoint<? extends Var> select =
        switch (model.annotation) {
          case 0 -> new SimpleSelect<>(v, null, new IndomainSetMin<>());
          case 1 -> new OutdomainSetSelect<>(v, null, new IndomainSetMin<>());
          default -> new OutdomainSetSelect<>(v, null, new IndomainSetMax<>());
        };
    solver.setAnnotation(select, seed % 2 == 0);
    solver.setAnnotationChrono(seed / 2 % 2 == 0 ? 0 : -1);
  }

  private static long[] add(long[] a, long[] b) {
    for (int i = 0; i < a.length; i++) {
      a[i] += b[i];
    }
    return a;
  }

  private static final int DIVES = Integer.getInteger("setlcg.fuzz.dives", 20000);

  // per class: atoms explained by the class itself, atoms with another reason (replay or generic),
  // failures explained, failures not, explanations the checker could not copy
  static final Map<String, long[]> DIVE_COUNTS = new TreeMap<>();

  /**
   * Random dives over the memberships, cardinalities and integer variables of the random models,
   * mirrored as the front end mirrors them: at every node every atom propagated is explained by its
   * constraint and the reason is checked by {@link ExplanationChecker}, and so is the reason of a
   * failure. This checks every reason, not only those a conflict needs.
   */
  @Test
  void reasonsHoldOnRandomDives() {
    long checked = 0;
    for (int run = 0; run < DIVES; run++) {
      long seed = SEED + (long) run;
      checked += dive(seed);
    }
    if (DIVES >= 1000 || VERBOSE) {
      System.out.printf("set lcg dives: %d runs, %d reasons checked%n", DIVES, checked);
      DIVE_COUNTS.forEach(
          (k, v) ->
              System.out.printf(
                  "  %-24s own=%d other=%d failOwn=%d failOther=%d skipped=%d%n",
                  k, v[0], v[1], v[2], v[3], v[4]));
    }
    assertThat(checked).isPositive();
  }

  static long dive(long seed) {
    Model model;
    try {
      model = new Model(seed);
    } catch (FailException | IllegalArgumentException e) {
      return 0;
    }
    String where = "seed " + seed + "\n" + model.describe();
    Random rnd = new Random(seed * 7 + 1);
    Store store = model.store;
    try {
      if (model.mirrorFirst) {
        mirror(model);
      }
      if (!store.consistency()) {
        return 0;
      }
      mirror(model);
      if (!store.consistency()) {
        return 0;
      }
    } catch (FailException e) {
      return 0;
    }
    List<IntVar> decide = new ArrayList<>(model.ints);
    for (SetVar sv : model.sets) {
      if (sv.lcgMirror() != null) {
        decide.addAll(Arrays.asList(sv.lcgMirror().mirrorVariables()));
      }
    }
    if (decide.isEmpty()) {
      return 0;
    }
    org.jacop.lcg.AtomicTrail trail = new org.jacop.lcg.AtomicTrail(store);
    org.jacop.lcg.ExplanationChecker checker = new org.jacop.lcg.ExplanationChecker(trail);
    long checked = 0;
    try {
      int depth = 1 + rnd.nextInt(8);
      boolean consistent = true;
      for (int step = 0; consistent && step < depth; step++) {
        store.setLevel(store.level + 1);
        int before = trail.size();
        try {
          int k = 1 + rnd.nextInt(2);
          for (int d = 0; d < k; d++) {
            IntVar v = decide.get(rnd.nextInt(decide.size()));
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
        } catch (FailException e) {
          consistent = false;
        }
        for (int e = before; e < trail.size(); e++) {
          org.jacop.constraints.Constraint c = trail.reason(e);
          if (c == null) {
            continue;
          }
          org.jacop.lcg.EntryList reason = new org.jacop.lcg.EntryList();
          boolean own = trail.explain(e, reason);
          long skipped = checker.skipped;
          String problem = checker.checkReason(e, reason);
          if (problem == null) {
            problem = bruteReason(model, trail, c, reason, e);
          }
          if (problem != null) {
            fail(where + "\nwrong reason of " + trail.atomString(e) + ": " + problem);
          }
          checked++;
          count(c, own ? 0 : 1, checker.skipped > skipped);
        }
        if (!consistent && store.recentlyFailedConstraint instanceof org.jacop.lcg.Explainable x) {
          org.jacop.constraints.Constraint c = store.recentlyFailedConstraint;
          org.jacop.lcg.EntryList reason = new org.jacop.lcg.EntryList();
          boolean own = x.explainFailure(trail, reason);
          if (own) {
            long skipped = checker.skipped;
            String problem = checker.checkFailure(c, reason);
            if (problem == null) {
              problem = bruteReason(model, trail, c, reason, -1);
            }
            if (problem != null) {
              fail(where + "\nwrong failure reason: " + problem);
            }
            checked++;
            count(c, 2, checker.skipped > skipped);
          } else {
            count(c, 3, false);
          }
        }
      }
    } catch (RuntimeException e) {
      throw new AssertionError(where, e);
    } finally {
      trail.detach();
    }
    return checked;
  }

  private static void count(org.jacop.constraints.Constraint c, int kind, boolean skipped) {
    String name = c.getClass().getSimpleName();
    synchronized (DIVE_COUNTS) {
      long[] v = DIVE_COUNTS.computeIfAbsent(name, k -> new long[5]);
      v[kind]++;
      if (skipped) {
        v[4]++;
      }
    }
  }

  @Test
  void agreesWithBruteForceOnRandomSetModels() {
    int sat = 0;
    int unsat = 0;
    int skipped = 0;
    for (int run = 0; run < RUNS; run++) {
      long seed = SEED + (long) run;
      int r = runSeed(seed);
      if (r < 0) {
        skipped++;
      } else if (r == 0) {
        unsat++;
      } else {
        sat++;
      }
      if (VERBOSE && (run + 1) % 10000 == 0) {
        System.out.printf("set lcg fuzz: %d runs%n", run + 1);
      }
    }
    if (RUNS >= 1000 || VERBOSE) {
      System.out.printf(
          "set lcg fuzz: %d runs, %d sat, %d unsat, %d skipped%n", RUNS, sat, unsat, skipped);
      STATISTICS.forEach(
          (k, v) ->
              System.out.printf(
                  "  %-24s reasons=%d generic=%d failures=%d generic=%d%n",
                  k, v[0], v[1], v[3], v[4]));
    }
    assertThat(sat).isPositive();
    assertThat(unsat).isPositive();
  }
}
