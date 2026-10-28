/*
 * WakeUpFixpointTest.java
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

package org.jacop;

import static org.assertj.core.api.Assertions.fail;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.AllEqual;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.AlldifferentExcept;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Among;
import org.jacop.constraints.AmongVar;
import org.jacop.constraints.And;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.AndBoolVector;
import org.jacop.constraints.ArgMax;
import org.jacop.constraints.ArgMin;
import org.jacop.constraints.AtLeast;
import org.jacop.constraints.AtMost;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.ChannelImply;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Conditional;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.CountBounds;
import org.jacop.constraints.CountVar;
import org.jacop.constraints.Decreasing;
import org.jacop.constraints.Distance;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.ElementIntegerFast;
import org.jacop.constraints.ElementVariable;
import org.jacop.constraints.ElementVariableFast;
import org.jacop.constraints.Eq;
import org.jacop.constraints.EqBool;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.IfThenBool;
import org.jacop.constraints.IfThenElse;
import org.jacop.constraints.Implies;
import org.jacop.constraints.In;
import org.jacop.constraints.Increasing;
import org.jacop.constraints.IncreasingNValue;
import org.jacop.constraints.LexOrder;
import org.jacop.constraints.LinearBool;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.Max;
import org.jacop.constraints.MaxSimple;
import org.jacop.constraints.Member;
import org.jacop.constraints.Min;
import org.jacop.constraints.MinSimple;
import org.jacop.constraints.NoGood;
import org.jacop.constraints.Not;
import org.jacop.constraints.Or;
import org.jacop.constraints.OrBoolSimple;
import org.jacop.constraints.OrBoolVector;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.ValuePrecede;
import org.jacop.constraints.Values;
import org.jacop.constraints.XdivYeqZ;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XexpYeqZ;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XgtY;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XgteqY;
import org.jacop.constraints.XltC;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmodYeqZ;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XmulYeqC;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.Xor;
import org.jacop.constraints.XorBool;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusClteqZImplied;
import org.jacop.constraints.XplusCneqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XplusYgtC;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

/**
 * Checks that a constraint is woken on every change its methods use: at every node of random dives
 * the store must be at the fixpoint that a fresh store reaches when the same constraint is imposed
 * on the current domains. A constraint that is not woken on an event it needs, or that does not
 * propagate its own pruning, prunes later than it could, for example Implies(b, x >= 6) setting b
 * to 0 only once x is fixed. Each trial imposes a primitive constraint, a constraint composed of
 * primitive ones (Reified, Implies, Not, Xor, Eq, And, Or, IfThen, IfThenElse) or a global
 * constraint over a few small variables with holes.
 *
 * <p>The number of trials per kind is {@code wakeup.trials} (default 3000).
 */
class WakeUpFixpointTest {

  private static final int TRIALS = Integer.getInteger("wakeup.trials", 3000);

  private static final int INTS = 4;
  private static final int BOOLS = 4;
  private static final int REIFS = 3;
  private static final String[] RELATIONS = {"==", "!=", "<", "<=", ">", ">="};

  /** Builds the constraint of a trial over the integer, Boolean and reification variables. */
  private interface Builder {
    Constraint build(IntVar[] x, IntVar[] b, IntVar[] r);
  }

  /** Builds a primitive constraint, which can be nested. */
  private interface PrimitiveBuilder extends Builder {
    @Override
    PrimitiveConstraint build(IntVar[] x, IntVar[] b, IntVar[] r);
  }

  @Test
  void primitiveConstraintsReachTheFreshFixpoint() {
    check(1, random -> new Generator(random).primitive());
  }

  @Test
  void composedConstraintsReachTheFreshFixpoint() {
    check(2, random -> new Generator(random).composed(1));
  }

  @Test
  void nestedComposedConstraintsReachTheFreshFixpoint() {
    check(3, random -> new Generator(random).composed(2));
  }

  @Test
  void globalConstraintsReachTheFreshFixpoint() {
    check(4, random -> new Generator(random).global());
  }

  private interface Source {
    Builder next(Random random);
  }

  private static void check(long kind, Source source) {
    for (int trial = 0; trial < TRIALS; trial++) {
      long seed = kind * 1_000_000 + trial;
      Random random = new Random(seed);
      Builder builder = source.next(random);
      IntDomain[] domains = initialDomains(random);
      Store store = new Store();
      IntVar[][] v = variables(store, domains);
      Constraint c;
      try {
        c = builder.build(v[0], v[1], v[2]);
        store.impose(c);
      } catch (IllegalArgumentException e) {
        continue; // arguments the constraint rejects
      }
      List<IntVar> all = new ArrayList<>();
      for (IntVar[] group : v) {
        Collections.addAll(all, group);
      }
      StringBuilder path = new StringBuilder();
      boolean consistent = consistency(store);
      for (int step = 0; consistent && step < 10; step++) {
        String missed = missedPruning(builder, v);
        if (missed != null) {
          fail("seed %d, %s, path%s: a fresh store prunes %s", seed, c, path, missed);
        }
        IntVar x = all.get(random.nextInt(all.size()));
        if (x.singleton()) {
          continue;
        }
        int value = x.min() + random.nextInt(x.max() - x.min() + 1);
        int decision = random.nextInt(4);
        path.append(' ').append(x.id()).append(new String[] {"=", "!=", "<=", ">="}[decision]);
        path.append(value);
        store.setLevel(store.level + 1);
        try {
          switch (decision) {
            case 0 -> x.domain.in(store.level, x, value, value);
            case 1 -> x.domain.inComplement(store.level, x, value);
            case 2 -> x.domain.inMax(store.level, x, value);
            default -> x.domain.inMin(store.level, x, value);
          }
          consistent = store.consistency();
        } catch (FailException e) {
          consistent = false;
        }
      }
    }
  }

  private static boolean consistency(Store store) {
    try {
      return store.consistency();
    } catch (FailException e) {
      return false;
    }
  }

  private static IntDomain[] initialDomains(Random random) {
    IntDomain[] domains = new IntDomain[INTS + BOOLS + REIFS];
    for (int i = 0; i < INTS; i++) {
      int lo = random.nextInt(3) - 2;
      IntDomain d = new IntervalDomain(lo, lo + 3 + random.nextInt(4));
      if (random.nextBoolean()) {
        d = d.subtract(lo + 1 + random.nextInt(2));
      }
      domains[i] = d;
    }
    for (int i = INTS; i < domains.length; i++) {
      domains[i] = new IntervalDomain(0, 1);
    }
    return domains;
  }

  private static IntVar[][] variables(Store store, IntDomain[] domains) {
    IntVar[][] v = {new IntVar[INTS], new IntVar[BOOLS], new IntVar[REIFS]};
    String[] names = {"x", "b", "r"};
    int n = 0;
    for (int g = 0; g < v.length; g++) {
      for (int i = 0; i < v[g].length; i++) {
        v[g][i] = new IntVar(store, names[g] + i, domains[n++].cloneLight());
      }
    }
    return v;
  }

  /**
   * Imposes the constraint again in a fresh store over the current domains and returns what that
   * store prunes beyond the current domains, or null if nothing.
   */
  private static String missedPruning(Builder builder, IntVar[][] v) {
    List<IntDomain> current = new ArrayList<>();
    for (IntVar[] group : v) {
      for (IntVar x : group) {
        current.add(x.dom().cloneLight());
      }
    }
    Store fresh = new Store();
    IntVar[][] w = variables(fresh, current.toArray(new IntDomain[0]));
    boolean consistent;
    try {
      fresh.impose(builder.build(w[0], w[1], w[2]));
      consistent = fresh.consistency();
    } catch (FailException e) {
      consistent = false;
    }
    if (!consistent) {
      return "a failure at " + domains(v);
    }
    StringBuilder pruned = new StringBuilder();
    for (int g = 0; g < v.length; g++) {
      for (int i = 0; i < v[g].length; i++) {
        if (!w[g][i].dom().eq(v[g][i].dom())) {
          pruned.append(' ').append(v[g][i].id()).append(": ").append(v[g][i].dom());
          pruned.append(" -> ").append(w[g][i].dom());
        }
      }
    }
    return pruned.isEmpty() ? null : pruned + " at " + domains(v);
  }

  private static String domains(IntVar[][] v) {
    StringBuilder s = new StringBuilder();
    for (IntVar[] group : v) {
      for (IntVar x : group) {
        s.append(x).append(' ');
      }
    }
    return s.toString().trim();
  }

  /** Draws the parameters of a constraint up front, so that it can be built again identically. */
  private static final class Generator {

    private final Random random;

    Generator(Random random) {
      this.random = random;
    }

    private int[] distinct(int n, int k) {
      List<Integer> all = new ArrayList<>();
      for (int i = 0; i < n; i++) {
        all.add(i);
      }
      Collections.shuffle(all, random);
      int[] picked = new int[k];
      for (int i = 0; i < k; i++) {
        picked[i] = all.get(i);
      }
      return picked;
    }

    private int nonZero(int bound) {
      int w = random.nextInt(2 * bound + 1) - bound;
      return w == 0 ? 1 : w;
    }

    PrimitiveBuilder primitive() {
      int[] p = distinct(INTS, 3);
      int i = p[0];
      int j = p[1];
      int k = p[2];
      int[] q = distinct(BOOLS, 3);
      int u = q[0];
      int v = q[1];
      int w = q[2];
      int c = random.nextInt(7) - 2;
      String rel = RELATIONS[random.nextInt(RELATIONS.length)];
      int w1 = nonZero(2);
      int w2 = nonZero(2);
      int w3 = random.nextInt(3) + 1;
      int count = random.nextInt(3);
      return switch (random.nextInt(43)) {
        case 0 -> (x, b, r) -> new XeqC(x[i], c);
        case 1 -> (x, b, r) -> new XneqC(x[i], c);
        case 2 -> (x, b, r) -> new XltC(x[i], c);
        case 3 -> (x, b, r) -> new XlteqC(x[i], c);
        case 4 -> (x, b, r) -> new XgtC(x[i], c);
        case 5 -> (x, b, r) -> new XgteqC(x[i], c);
        case 6 -> (x, b, r) -> new XeqY(x[i], x[j]);
        case 7 -> (x, b, r) -> new XneqY(x[i], x[j]);
        case 8 -> (x, b, r) -> new XltY(x[i], x[j]);
        case 9 -> (x, b, r) -> new XlteqY(x[i], x[j]);
        case 10 -> (x, b, r) -> new XgtY(x[i], x[j]);
        case 11 -> (x, b, r) -> new XgteqY(x[i], x[j]);
        case 12 -> (x, b, r) -> new XplusCeqZ(x[i], c, x[j]);
        case 13 -> (x, b, r) -> new XplusYeqZ(x[i], x[j], x[k]);
        case 14 -> (x, b, r) -> new XplusYeqC(x[i], x[j], c);
        case 15 -> (x, b, r) -> new XplusYlteqZ(x[i], x[j], x[k]);
        case 16 -> (x, b, r) -> new XplusYgtC(x[i], x[j], c);
        case 17 -> (x, b, r) -> new XplusClteqZ(x[i], c, x[j]);
        case 18 -> (x, b, r) -> new XplusCneqZ(x[i], c, x[j]);
        case 19 -> (x, b, r) -> new XmulCeqZ(x[i], w1, x[j]);
        case 20 -> (x, b, r) -> new XmulYeqC(x[i], x[j], c);
        case 21 -> (x, b, r) -> new AbsXeqY(x[i], x[j]);
        case 22 -> (x, b, r) -> new Distance(x[i], x[j], x[k]);
        case 23 -> (x, b, r) -> new SumBool(new IntVar[] {b[u], b[v], b[w]}, rel, x[i]);
        case 24 -> (x, b, r) -> new SumInt(new IntVar[] {x[i], x[j]}, rel, x[k]);
        case 25 ->
            (x, b, r) -> new LinearInt(new IntVar[] {x[i], x[j]}, new int[] {w1, w2}, rel, c);
        case 26 ->
            (x, b, r) ->
                new LinearInt(new IntVar[] {x[i], x[j], x[k]}, new int[] {w1, w2, w3}, rel, c);
        case 27 ->
            (x, b, r) -> new LinearIntDom(new IntVar[] {x[i], x[j]}, new int[] {w1, w2}, rel, c);
        case 28 ->
            (x, b, r) -> {
              IntervalDomain d = new IntervalDomain(c, c + 1);
              d.unionAdapt(c + 3, c + 4);
              return new In(x[i], d);
            };
        case 29 -> (x, b, r) -> new AndBoolVector(new IntVar[] {b[u], b[v]}, b[w]);
        case 30 -> (x, b, r) -> new OrBoolVector(new IntVar[] {b[u], b[v]}, b[w]);
        case 31 -> (x, b, r) -> new XorBool(new IntVar[] {b[u], b[v]}, b[w]);
        case 32 -> (x, b, r) -> new EqBool(new IntVar[] {b[u], b[v]}, b[w]);
        case 33 -> (x, b, r) -> new BoolClause(new IntVar[] {b[u], b[v]}, new IntVar[] {b[w]});
        case 34 -> (x, b, r) -> new Member(new IntVar[] {x[j], x[k]}, x[i]);
        case 35 -> (x, b, r) -> new AllEqual(new IntVar[] {x[i], x[j], x[k]});
        case 36 -> (x, b, r) -> new AtLeast(new IntVar[] {x[i], x[j], x[k]}, count, c);
        case 37 -> (x, b, r) -> new AtMost(new IntVar[] {x[i], x[j], x[k]}, count, c);
        case 38 -> (x, b, r) -> new IfThenBool(b[u], b[v], b[w]);
        case 39 -> (x, b, r) -> new AndBoolSimple(b[u], b[v], b[w]);
        case 40 -> (x, b, r) -> new OrBoolSimple(b[u], b[v], b[w]);
        case 41 -> (x, b, r) -> new XplusClteqZImplied(b[u], x[i], c, x[j]);
        default -> (x, b, r) -> new XorBool(new IntVar[] {b[u], b[v], b[w]}, b[(w + 1) % BOOLS]);
      };
    }

    PrimitiveBuilder composed(int depth) {
      if (depth == 0 || random.nextInt(3) == 0) {
        return primitive();
      }
      int k = random.nextInt(REIFS);
      PrimitiveBuilder c1 = composed(depth - 1);
      PrimitiveBuilder c2 = composed(depth - 1);
      return switch (random.nextInt(9)) {
        case 0 -> (x, b, r) -> new Reified(c1.build(x, b, r), r[k]);
        case 1 -> (x, b, r) -> new Implies(r[k], c1.build(x, b, r));
        case 2 -> (x, b, r) -> new Not(c1.build(x, b, r));
        case 3 -> (x, b, r) -> new Xor(c1.build(x, b, r), r[k]);
        case 4 -> (x, b, r) -> new Eq(c1.build(x, b, r), c2.build(x, b, r));
        case 5 -> (x, b, r) -> new And(c1.build(x, b, r), c2.build(x, b, r));
        case 6 -> (x, b, r) -> new Or(c1.build(x, b, r), c2.build(x, b, r));
        case 7 -> (x, b, r) -> new IfThen(c1.build(x, b, r), c2.build(x, b, r));
        default -> {
          PrimitiveBuilder c3 = composed(depth - 1);
          yield (x, b, r) ->
              new IfThenElse(c1.build(x, b, r), c2.build(x, b, r), c3.build(x, b, r));
        }
      };
    }

    Builder global() {
      int[] p = distinct(INTS, 4);
      int i = p[0];
      int j = p[1];
      int k = p[2];
      int l = p[3];
      int[] q = distinct(BOOLS, 3);
      int u = q[0];
      int v = q[1];
      int w = q[2];
      int c = random.nextInt(5) - 1;
      int[] list = new int[4];
      for (int n = 0; n < list.length; n++) {
        list[n] = random.nextInt(5) - 2;
      }
      String rel = new String[] {"==", "<=", ">="}[random.nextInt(3)];
      int element = (l + 1) % INTS == i ? j : (l + 1) % INTS;
      return switch (random.nextInt(37)) {
        case 0 -> (x, b, r) -> new XmulYeqZ(x[i], x[j], x[k]);
        case 1 -> (x, b, r) -> new XdivYeqZ(x[i], x[j], x[k]);
        case 2 -> (x, b, r) -> new XmodYeqZ(x[i], x[j], x[k]);
        case 3 -> (x, b, r) -> new XexpYeqZ(x[i], x[j], x[k]);
        case 4 -> (x, b, r) -> new XmulYeqZ(x[i], x[i], x[j]);
        case 5 -> (x, b, r) -> new Alldistinct(new IntVar[] {x[i], x[j], x[k]});
        case 6 -> (x, b, r) -> new Alldifferent(new IntVar[] {x[i], x[j], x[k]});
        case 7 -> (x, b, r) -> new Alldiff(new IntVar[] {x[i], x[j], x[k]});
        case 8 -> (x, b, r) -> new Count(new IntVar[] {x[i], x[j], x[k]}, x[l], c);
        case 9 -> (x, b, r) -> new CountBounds(new IntVar[] {x[i], x[j], x[k]}, c, 1, 2);
        case 10 -> (x, b, r) -> new CountVar(new IntVar[] {x[i], x[j]}, x[k], x[l]);
        case 11 -> (x, b, r) -> new Max(new IntVar[] {x[i], x[j], x[k]}, x[l]);
        case 12 -> (x, b, r) -> new Min(new IntVar[] {x[i], x[j], x[k]}, x[l]);
        case 13 -> (x, b, r) -> new MaxSimple(x[i], x[j], x[k]);
        case 14 -> (x, b, r) -> new MinSimple(x[i], x[j], x[k]);
        case 15 -> (x, b, r) -> new ArgMax(new IntVar[] {x[i], x[j], x[k]}, x[l], 0);
        case 16 -> (x, b, r) -> new ArgMin(new IntVar[] {x[i], x[j], x[k]}, x[l], 0);
        case 17 ->
            (x, b, r) ->
                new Among(new IntVar[] {x[i], x[j], x[k]}, new IntervalDomain(c, c + 1), x[l]);
        case 18 -> (x, b, r) -> new AmongVar(new IntVar[] {x[i], x[j]}, new IntVar[] {x[k]}, x[l]);
        case 19 -> (x, b, r) -> new ElementInteger(x[i], list, x[j], -1);
        case 20 -> (x, b, r) -> new ElementIntegerFast(x[i], list, x[j], -1);
        case 21 ->
            (x, b, r) -> new ElementVariable(x[i], new IntVar[] {x[j], x[k], x[l]}, x[element], -1);
        case 22 ->
            (x, b, r) ->
                new ElementVariableFast(x[i], new IntVar[] {x[j], x[k], x[l]}, x[element], -1);
        case 23 -> (x, b, r) -> new Values(new IntVar[] {x[i], x[j], x[k]}, x[l]);
        case 24 -> (x, b, r) -> new Increasing(new IntVar[] {x[i], x[j], x[k]});
        case 25 -> (x, b, r) -> new Decreasing(new IntVar[] {x[i], x[j], x[k]}, c > 0);
        case 26 ->
            (x, b, r) -> new LexOrder(new IntVar[] {x[i], x[j]}, new IntVar[] {x[k], x[l]}, c > 0);
        case 27 ->
            (x, b, r) ->
                new LinearBool(new IntVar[] {b[u], b[v], b[w]}, new int[] {1, 2, 1}, rel, x[i]);
        case 28 ->
            (x, b, r) ->
                new ChannelReif(x[i], new IntVar[] {b[u], b[v], b[w]}, new int[] {c - 1, c, c + 1});
        case 29 ->
            (x, b, r) ->
                new ChannelImply(
                    x[i], new IntVar[] {b[u], b[v], b[w]}, new int[] {c - 1, c, c + 1});
        case 30 -> (x, b, r) -> new SumWeight(new IntVar[] {x[i], x[j]}, new int[] {2, -1}, x[k]);
        case 31 ->
            (x, b, r) ->
                new AlldifferentExcept(new IntVar[] {x[i], x[j], x[k]}, new IntervalDomain(0, 0));
        case 32 -> (x, b, r) -> new ValuePrecede(0, 1, new IntVar[] {x[i], x[j], x[k]});
        case 33 -> (x, b, r) -> new IncreasingNValue(new IntVar[] {x[i], x[j], x[k]}, x[l]);
        case 34 -> (x, b, r) -> new NoGood(new IntVar[] {x[i], x[j]}, new int[] {c, c + 1});
        case 35 -> (x, b, r) -> new AbsXeqY(x[i], x[j], true);
        default -> {
          PrimitiveBuilder c1 = composed(1);
          PrimitiveBuilder c2 = composed(1);
          yield (x, b, r) ->
              new Conditional(
                  new IntVar[] {r[0], r[1]},
                  new PrimitiveConstraint[] {c1.build(x, b, r), c2.build(x, b, r)});
        }
      };
    }
  }
}
