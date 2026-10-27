/*
 * ImpliedConstraints.java
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
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import org.jacop.constraints.Alldiff;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Var;

/**
 * Presolve rule: constraints implied by all-different constraints, posted next to them.
 *
 * <p>The values of {@code n} pairwise different variables are {@code n} different values of the
 * union of their domains, so their sum is at least the sum of the {@code n} smallest values of that
 * union and at most the sum of the {@code n} largest (Choco's {@code
 * PreProcessing.impliedConstraints}). When the union has exactly {@code n} values the variables are
 * a permutation of it and the two bounds meet: the sum is a constant.
 *
 * <p>A bound is posted only when it is tighter than the one the variables' own bounds already give
 * (the sum of their minima or of their maxima), so an all-different whose variables have disjoint
 * domains gets nothing. The posted constraints are implied by the model and keep every solution, so
 * the rule is sound for finding all solutions as well.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class ImpliedConstraints {

  /** Fewest variables of an all-different that gets implied constraints. */
  static final int MIN_VARIABLES = 3;

  private ImpliedConstraints() {}

  /**
   * Returns the constraints implied by the all-different constraints among the given ones. They are
   * not imposed.
   *
   * @param constraints constraints of a store at a fixpoint.
   * @return the implied constraints, in the order of the all-different constraints.
   */
  public static List<Constraint> of(List<? extends Constraint> constraints) {
    List<Constraint> implied = new ArrayList<>();
    // an all-different posted twice, for example as Alldiff and as the Alldistinct implied by a
    // circuit, implies the same sums once
    Set<List<IntVar>> seen = new HashSet<>();
    for (Constraint c : constraints) {
      IntVar[] vars = allDifferentVariables(c);
      if (vars != null && seen.add(List.of(vars))) {
        sumBounds(vars, implied);
      }
    }
    return implied;
  }

  /**
   * The variables of an all-different constraint, in store order, or null if the constraint is not
   * one. Subclasses of {@link Alldifferent} other than {@link Alldiff} relax the constraint (all
   * different except some values) and are left out.
   */
  private static IntVar[] allDifferentVariables(Constraint c) {
    Class<?> k = c.getClass();
    if (k != Alldistinct.class && k != Alldiff.class && k != Alldifferent.class) {
      return null;
    }
    IntVar[] vars = new IntVar[c.arguments().size()];
    int n = 0;
    for (Var v : c.arguments()) {
      vars[n++] = (IntVar) v;
    }
    Arrays.sort(vars, Comparator.comparingInt(Var::index).thenComparing(Var::id));
    return vars;
  }

  /** Adds the sum bounds implied by {@code vars} being pairwise different. */
  static void sumBounds(IntVar[] vars, List<Constraint> implied) {
    int n = vars.length;
    if (n < MIN_VARIABLES) {
      return;
    }
    IntDomain union = new IntervalDomain();
    long sumMin = 0;
    long sumMax = 0;
    for (IntVar v : vars) {
      union = union.union(v.dom());
      sumMin += v.min();
      sumMax += v.max();
    }
    if (union.getSize() < n) {
      // pigeonhole: the all-different itself fails, nothing to imply
      return;
    }
    long lb = smallest(union, n);
    long ub = largest(union, n);
    if (lb < Integer.MIN_VALUE || ub > Integer.MAX_VALUE) {
      return;
    }
    int[] ones = new int[n];
    Arrays.fill(ones, 1);
    if (lb == ub) {
      implied.add(new LinearInt(vars, ones, "==", (int) lb));
      return;
    }
    if (lb > sumMin) {
      implied.add(new LinearInt(vars, ones, ">=", (int) lb));
    }
    if (ub < sumMax) {
      implied.add(new LinearInt(vars, ones, "<=", (int) ub));
    }
  }

  /** Sum of the {@code n} smallest values of a domain with at least {@code n} values. */
  static long smallest(IntDomain d, int n) {
    long sum = 0;
    int left = n;
    for (int i = 0; i < d.noIntervals() && left > 0; i++) {
      long a = d.leftElement(i);
      long take = Math.min(left, (long) d.rightElement(i) - a + 1);
      sum += take * a + take * (take - 1) / 2;
      left -= (int) take;
    }
    return sum;
  }

  /** Sum of the {@code n} largest values of a domain with at least {@code n} values. */
  static long largest(IntDomain d, int n) {
    long sum = 0;
    int left = n;
    for (int i = d.noIntervals() - 1; i >= 0 && left > 0; i--) {
      long b = d.rightElement(i);
      long take = Math.min(left, b - d.leftElement(i) + 1);
      sum += take * b - take * (take - 1) / 2;
      left -= (int) take;
    }
    return sum;
  }
}
