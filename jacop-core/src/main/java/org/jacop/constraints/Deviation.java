/*
 * Deviation.java
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

package org.jacop.constraints;

import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.IntVar;

/**
 * Deviation constraint: x[0] + ... + x[n-1] = s and d = |a * x[0] - b| + ... + |a * x[n-1] - b|.
 * The default a = n and b = s give the deviation constraint of Schaus, Deville, Dupont and
 * R&eacute;gin ("The Deviation Constraint", CPAIOR 2007; "Bound-Consistent Deviation Constraint",
 * CP 2007): d = sum of |n * x[i] - s|, n times the L1 distance of x to its mean s / n, which is an
 * integer also when the mean is fractional. It balances loads, as in the balanced academic
 * curriculum problem, where the sum of absolute values posted term by term does not see that the
 * loads must add up to s.
 *
 * <p>Pruning is bounds consistent on the integer intervals of x for d &ge; deviation (see {@link
 * AbstractBalance}). The least cost of a set of variables with a given sum comes from the marginal
 * costs of raising one variable by one: going from v to v + 1 costs -a while a * (v + 1) &le; b, +a
 * once a * v &ge; b, and a - 2 * (b mod a) for the one v in between when a does not divide b. Each
 * variable has at most three groups of steps from its minimum, and taking the cheapest steps first
 * gives the least cost in constant time from the number of steps of each group.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class Deviation extends AbstractBalance implements Copyable<Deviation> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  // b = q * a + r with 0 <= r < a
  private final long q;
  private final long r;

  // steps of each variable from its minimum costing -a and a - 2r (the others cost +a), their
  // totals, and the cost of all variables at their minima
  private final long[] down;
  private final long[] middle;
  private long downs;
  private long middles;
  private long base;

  /**
   * It constructs the deviation constraint sum of x = s, d = sum of |n * x[i] - s|.
   *
   * @param x the balanced variables.
   * @param sum the sum of x.
   * @param deviation the deviation, n times the sum of the distances of x[i] to the mean.
   */
  public Deviation(IntVar[] x, int sum, IntVar deviation) {
    this(x, x.length, sum, sum, deviation);
  }

  /**
   * It constructs the deviation constraint sum of x = s, d = sum of |a * x[i] - b|.
   *
   * @param x the balanced variables.
   * @param a the positive multiplier of each x[i].
   * @param b the value a * x[i] is compared with.
   * @param sum the sum of x.
   * @param deviation the sum of |a * x[i] - b|.
   */
  public Deviation(IntVar[] x, int a, int b, int sum, IntVar deviation) {
    super(x, a, b, sum, deviation);
    this.numberId = idNumber.incrementAndGet();
    this.q = Math.floorDiv(b, a);
    this.r = Math.floorMod(b, a);
    this.down = new long[n];
    this.middle = new long[n];
  }

  @Override
  long term(long v) {
    return Math.abs(a * v - b);
  }

  @Override
  void prepare() {
    downs = 0;
    middles = 0;
    base = 0;
    for (int i = 0; i < n; i++) {
      down[i] = Math.max(0, Math.min(hi[i], q) - lo[i]);
      middle[i] = r > 0 && lo[i] <= q && q < hi[i] ? 1 : 0;
      downs += down[i];
      middles += middle[i];
      base += term(lo[i]);
    }
  }

  @Override
  long least(int skip, long t) {
    long steps = t - sumLo;
    long d = downs;
    long m = middles;
    long result = base;
    if (skip >= 0) {
      steps += lo[skip];
      d -= down[skip];
      m -= middle[skip];
      result -= term(lo[skip]);
    }
    long taken = Math.min(steps, d);
    result -= a * taken;
    steps -= taken;
    taken = Math.min(steps, m);
    result += (a - 2 * r) * taken;
    steps -= taken;
    return result + a * steps;
  }

  @Override
  public String toString() {
    return id() + " : Deviation" + describe();
  }

  @Override
  public Deviation copy(VarMap map) {
    return new Deviation(map.get(x), a, b, sum, map.get(cost));
  }
}
