/*
 * RedundantConstraints.java
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

package org.jacop.presolve;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.AbstractReifiedConstraint;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearBool;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumWeight;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;

/**
 * Rules 3 and 4 of presolve: linear canonicalisation, and duplicate and dominated constraints.
 *
 * <p>Every constraint that states a linear relation (it has a {@link LinearForm}) is put in a
 * canonical form over the domains of the moment: fixed variables are moved into the constant,
 * repeated variables merged, {@code >=} turned into {@code <=}, coefficients of 0/1 variables in a
 * {@code <=} strengthened (CP-SAT's {@code TryToReduceCoefficients}), all coefficients divided by
 * their GCD (rounding the constant of a {@code <=} down), the variables sorted and the sign chosen
 * so the first coefficient is positive. The canonical form has the same integer solutions as the
 * constraint within its domains, so constraints with the same left-hand side bound the same sum:
 *
 * <ul>
 *   <li>an equality makes the bounds over the same sum redundant; equalities with different
 *       constants, or bounds that cross, make the problem infeasible;
 *   <li>of the upper bounds only the tightest is needed, and of the lower bounds the tightest;
 *   <li>a disequality outside the bounds is entailed, and a disequality with the constant of an
 *       equality is infeasible;
 *   <li>an equality whose constant the GCD does not divide is infeasible, and such a disequality is
 *       entailed.
 * </ul>
 *
 * <p>Equal equalities and disequalities of different classes are all kept, since their propagators
 * differ in strength ({@code XeqY} prunes values, {@code LinearInt} bounds); a {@code <=}
 * propagator computes the bounds that every propagator of an equivalent relation computes, so any
 * one of them represents its bound. Reified and implied linear constraints with the same control
 * variable, the same class and the same canonical relation are duplicates.
 *
 * <p>The rule only leaves constraints out; it never builds a constraint, so the propagators kept
 * are those FlatZinc or the model chose. It is idempotent: on the constraints it keeps it finds
 * nothing.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class RedundantConstraints {

  /**
   * The constraints left out and why.
   *
   * @param duplicates constraints equal to one kept.
   * @param dominated constraints implied by the ones kept and the domains.
   */
  record Result(List<Constraint> duplicates, List<Constraint> dominated) {

    /**
     * Returns every constraint left out.
     *
     * @return the duplicates, then the dominated constraints.
     */
    List<Constraint> removed() {
      List<Constraint> all = new ArrayList<>(duplicates);
      all.addAll(dominated);
      return all;
    }
  }

  // the shape of a canonical relation over its left-hand side
  private enum Kind {
    UPPER, // lhs <= c
    LOWER, // lhs >= c
    EQ,
    NE,
    TRUE, // entailed within the domains
    FALSE // infeasible within the domains
  }

  /** A sorted left-hand side: variable ordinals and coefficients, the first one positive. */
  private record Lhs(int[] vars, long[] weights) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Lhs l && Arrays.equals(vars, l.vars) && Arrays.equals(weights, l.weights);
    }

    @Override
    public int hashCode() {
      return 31 * Arrays.hashCode(vars) + Arrays.hashCode(weights);
    }

    @Override
    public String toString() {
      return "Lhs[vars=" + Arrays.toString(vars) + ", weights=" + Arrays.toString(weights) + "]";
    }
  }

  private record Canonical(Lhs lhs, Kind kind, long c) {}

  private record Member(Constraint constraint, Kind kind, long c) {}

  // key of a reified or implied linear constraint
  private record ReifiedKey(Class<?> outer, int control, Class<?> inner, Canonical relation) {}

  /** The rule: leaves out of the child the constraints that the others imply. */
  static final Rule RULE =
      new Rule() {
        @Override
        public void apply(Context context) {
          find(context.constraints()).removed().forEach(context::remove);
        }

        @Override
        public Timing timing() {
          // pairs of constraints over the same variables
          return Timing.MEDIUM;
        }
      };

  private final Map<Var, Integer> ordinals = new IdentityHashMap<>();

  private final List<Var> byOrdinal = new ArrayList<>();

  private RedundantConstraints() {}

  /**
   * Finds the constraints that the others imply.
   *
   * @param constraints the constraints, attached in a store at a fixpoint, in a deterministic
   *     order.
   * @return the constraints to leave out.
   * @throws FailException if the constraints are infeasible within the domains.
   */
  static Result find(List<Constraint> constraints) {
    return new RedundantConstraints().run(constraints);
  }

  private Result run(List<Constraint> constraints) {
    List<Constraint> duplicates = new ArrayList<>();
    List<Constraint> dominated = new ArrayList<>();
    Map<Lhs, List<Member>> groups = new LinkedHashMap<>();
    Set<ReifiedKey> reified = new HashSet<>();

    for (Constraint c : constraints) {
      if ((c.getClass() == Reified.class || c.getClass() == Implies.class)
          && ((AbstractReifiedConstraint) c).c instanceof Constraint inner) {
        Canonical relation = canonical(linearForm(inner));
        IntVar b = ((AbstractReifiedConstraint) c).b;
        if (relation != null && relation.lhs() != null && !b.singleton()) {
          if (!reified.add(new ReifiedKey(c.getClass(), ordinal(b), inner.getClass(), relation))) {
            duplicates.add(c);
          }
        }
        continue;
      }
      Canonical f = canonical(linearForm(c));
      if (f == null) {
        continue;
      }
      switch (f.kind()) {
        case TRUE -> dominated.add(c);
        case FALSE -> throw Store.failException;
        default ->
            groups
                .computeIfAbsent(f.lhs(), k -> new ArrayList<>())
                .add(new Member(c, f.kind(), f.c()));
      }
    }

    for (List<Member> group : groups.values()) {
      if (group.size() > 1) {
        reduce(group, duplicates, dominated);
      }
    }
    return new Result(duplicates, dominated);
  }

  /** Keeps what a group of relations over one left-hand side needs. */
  private static void reduce(
      List<Member> group, List<Constraint> duplicates, List<Constraint> dominated) {
    long lo = Long.MIN_VALUE;
    long hi = Long.MAX_VALUE;
    Long value = null;
    for (Member m : group) {
      switch (m.kind()) {
        case UPPER -> hi = Math.min(hi, m.c());
        case LOWER -> lo = Math.max(lo, m.c());
        case EQ -> {
          if (value != null && value != m.c()) {
            throw Store.failException;
          }
          value = m.c();
        }
        default -> {}
      }
    }
    boolean equality = value != null;
    if (equality) {
      lo = Math.max(lo, value);
      hi = Math.min(hi, value);
    }
    if (lo > hi) {
      throw Store.failException;
    }

    Member upper = null;
    Member lower = null;
    Map<Class<?>, Member> equalities = new HashMap<>();
    Map<List<Object>, Member> disequalities = new HashMap<>();
    for (Member m : group) {
      Constraint c = m.constraint();
      switch (m.kind()) {
        case EQ -> {
          if (equalities.putIfAbsent(c.getClass(), m) != null) {
            duplicates.add(c);
          }
        }
        case UPPER -> {
          if (equality || m.c() != hi) {
            dominated.add(c);
          } else if (upper == null) {
            upper = m;
          } else {
            duplicates.add(c);
          }
        }
        case LOWER -> {
          if (equality || m.c() != lo) {
            dominated.add(c);
          } else if (lower == null) {
            lower = m;
          } else {
            duplicates.add(c);
          }
        }
        default -> { // NE
          if (m.c() < lo || m.c() > hi) {
            dominated.add(c);
          } else if (lo == hi) {
            throw Store.failException;
          } else if (disequalities.putIfAbsent(List.of(c.getClass(), m.c()), m) != null) {
            duplicates.add(c);
          }
        }
      }
    }
  }

  /**
   * Returns the linear relation a constraint states, or null if it does not state one.
   *
   * @param c a constraint.
   * @return the linear form, or null.
   */
  static LinearForm linearForm(Constraint c) {
    if (c instanceof LinearExplainable e) {
      return e.linearForm();
    }
    if (c instanceof LinearInt l) {
      return l.linearForm();
    }
    if (c instanceof SumWeight s) {
      return s.linearForm();
    }
    if (c instanceof LinearBool b) {
      return b.linearForm();
    }
    return null;
  }

  /** The canonical form of a linear relation, or null if it has none (overflow). */
  private Canonical canonical(LinearForm f) {
    if (f == null) {
      return null;
    }
    try {
      return canonicalExact(f);
    } catch (ArithmeticException e) {
      return null;
    }
  }

  private Canonical canonicalExact(LinearForm f) {
    int relation = f.relation();
    long c = f.c();
    Map<IntVar, Long> merged = new IdentityHashMap<>();
    List<IntVar> order = new ArrayList<>();
    for (int i = 0; i < f.vars().length; i++) {
      IntVar v = f.vars()[i];
      long w = f.weights()[i];
      if (w == 0) {
        continue;
      }
      if (v.singleton()) {
        c = Math.subtractExact(c, Math.multiplyExact(w, (long) v.value()));
      } else {
        Long before = merged.put(v, Math.addExact(merged.getOrDefault(v, 0L), w));
        if (before == null) {
          order.add(v);
        }
      }
    }
    order.removeIf(v -> merged.get(v) == 0L);
    if (relation == LinearForm.GE) {
      // sum >= c is -sum <= -c
      merged.replaceAll((v, w) -> -w);
      c = Math.negateExact(c);
      relation = LinearForm.LE;
    }

    int n = order.size();
    if (n == 0) {
      boolean holds =
          switch (relation) {
            case LinearForm.LE -> 0 <= c;
            case LinearForm.EQ -> 0 == c;
            default -> 0 != c;
          };
      return new Canonical(null, holds ? Kind.TRUE : Kind.FALSE, 0);
    }

    for (IntVar v : order) {
      ordinal(v);
    }
    order.sort((a, b) -> Integer.compare(ordinals.get(a), ordinals.get(b)));
    int[] vars = new int[n];
    long[] w = new long[n];
    for (int i = 0; i < n; i++) {
      vars[i] = ordinals.get(order.get(i));
      w[i] = merged.get(order.get(i));
    }

    if (relation == LinearForm.LE) {
      long max = 0;
      long min = 0;
      for (int i = 0; i < n; i++) {
        IntVar v = order.get(i);
        long a = Math.multiplyExact(w[i], (long) v.min());
        long b = Math.multiplyExact(w[i], (long) v.max());
        max = Math.addExact(max, Math.max(a, b));
        min = Math.addExact(min, Math.min(a, b));
      }
      if (max <= c) {
        return new Canonical(null, Kind.TRUE, 0);
      }
      if (min > c) {
        return new Canonical(null, Kind.FALSE, 0);
      }
      c = strengthen(order, w, c, max);
    }

    long g = 0;
    for (long a : w) {
      g = gcd(g, Math.abs(a));
    }
    if (g > 1) {
      if (relation == LinearForm.LE) {
        c = Math.floorDiv(c, g);
      } else if (c % g != 0) {
        return new Canonical(null, relation == LinearForm.EQ ? Kind.FALSE : Kind.TRUE, 0);
      } else {
        c /= g;
      }
      for (int i = 0; i < n; i++) {
        w[i] /= g;
      }
    }

    Kind kind =
        switch (relation) {
          case LinearForm.LE -> Kind.UPPER;
          case LinearForm.EQ -> Kind.EQ;
          default -> Kind.NE;
        };
    if (w[0] < 0) {
      for (int i = 0; i < n; i++) {
        w[i] = -w[i];
      }
      c = Math.negateExact(c);
      if (kind == Kind.UPPER) {
        kind = Kind.LOWER;
      }
    }
    return new Canonical(new Lhs(vars, w), kind, c);
  }

  /**
   * Coefficient strengthening of {@code sum w[i]*x[i] <= c} on its 0/1 variables: when the
   * constraint holds whatever the other variables are as soon as a 0/1 variable takes the value
   * that lowers the sum, its coefficient (and for a positive one the constant) shrinks by the
   * slack, which keeps the same integer solutions. The slack {@code max - c} does not change.
   *
   * @return the new constant; the coefficients are changed in place.
   */
  private static long strengthen(List<IntVar> x, long[] w, long c, long max) {
    for (int i = 0; i < w.length; i++) {
      IntVar v = x.get(i);
      if (v.min() != 0 || v.max() != 1) {
        continue;
      }
      if (w[i] > 0 && max - w[i] < c) {
        long d = c - (max - w[i]);
        w[i] -= d;
        c -= d;
        max -= d;
      } else if (w[i] < 0 && max + w[i] < c) {
        w[i] += c - (max + w[i]);
      }
    }
    return c;
  }

  private int ordinal(Var v) {
    return ordinals.computeIfAbsent(
        v,
        k -> {
          byOrdinal.add(k);
          return ordinals.size();
        });
  }

  /**
   * Returns the canonical form of a linear relation, for tests: an entailed relation is {@code 0 ==
   * 0}, an infeasible one {@code 0 == 1}.
   *
   * @param f a linear relation over variables at a fixpoint.
   * @return the canonical relation, or null if it has none.
   */
  static LinearForm canonicalForm(LinearForm f) {
    RedundantConstraints r = new RedundantConstraints();
    Canonical c = r.canonical(f);
    if (c == null) {
      return null;
    }
    return switch (c.kind()) {
      case TRUE -> new LinearForm(new IntVar[0], new long[0], 0, LinearForm.EQ);
      case FALSE -> new LinearForm(new IntVar[0], new long[0], 1, LinearForm.EQ);
      default -> {
        int[] vars = c.lhs().vars();
        IntVar[] x = new IntVar[vars.length];
        for (int i = 0; i < x.length; i++) {
          x[i] = (IntVar) r.byOrdinal.get(vars[i]);
        }
        int relation =
            switch (c.kind()) {
              case UPPER -> LinearForm.LE;
              case LOWER -> LinearForm.GE;
              case EQ -> LinearForm.EQ;
              default -> LinearForm.NE;
            };
        yield new LinearForm(x, c.lhs().weights().clone(), c.c(), relation);
      }
    };
  }

  private static long gcd(long a, long b) {
    while (b != 0) {
      long t = a % b;
      a = b;
      b = t;
    }
    return a;
  }
}
