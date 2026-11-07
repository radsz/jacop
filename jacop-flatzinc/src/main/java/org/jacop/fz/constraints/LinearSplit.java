/*
 * LinearSplit.java
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

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Consumer;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearBool;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.Sum;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.SumWeight;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.LinearForm;

/**
 * Splits a long linear constraint into sums of blocks for lazy clause generation. The explanation
 * of a bound a linear constraint propagates cites a bound of every other term, so a sum of n terms
 * gives reasons and learnt clauses of about n literals however little the propagation needed. A sum
 * of n terms becomes blocks of about sqrt(n) terms, each defining a new variable, and the sum of
 * those variables: a reason then cites about sqrt(n) bounds, of terms or of block sums, and the
 * block sums let a learnt clause speak of a whole block. Bounds propagation over the blocks prunes
 * the terms' bounds as the flat sum does.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class LinearSplit {

  private LinearSplit() {}

  /**
   * Returns the constraint that replaces c, after imposing its blocks, or null when c is not split:
   * limit is 0, c is not a sum, a weighted sum or a pseudo-Boolean constraint, its relation is
   * {@code !=}, it has at most {@code limit} terms, or a block sum does not fit an integer domain.
   *
   * <p>The objective's definition is split too. Kept whole, on-call-rostering 20s-200d took 25 to
   * 54 s instead of 2 to 4 s on 5 of 6 seeds, and 2DBinPacking Class6_60_3 was proved on none of 6
   * seeds instead of 3; only cutstock type04_TEST9 found its first solution more often (6 of 6
   * seeds against 3).
   *
   * @param store the store the blocks are imposed in
   * @param c the constraint
   * @param limit the most terms a constraint keeps
   * @param defined receives the variable of each block sum, which its block defines
   * @return the sum of the blocks with c's relation and right-hand side, or null
   */
  static Constraint split(Store store, Constraint c, int limit, Consumer<IntVar> defined) {
    LinearForm f = form(c);
    if (limit <= 0 || f == null || f.relation() == LinearForm.NE || f.vars().length <= limit) {
      return null;
    }
    IntVar[] x = f.vars();
    long[] w = f.weights();
    int n = x.length;
    if (f.c() < IntDomain.MIN_INT || f.c() > IntDomain.MAX_INT) {
      return null;
    }
    for (long wi : w) {
      if (Math.abs(wi) > IntDomain.MAX_INT) {
        return null;
      }
    }
    int size = (int) Math.ceil(Math.sqrt(n));
    List<IntVar> sums = new ArrayList<>();
    List<Constraint> blocks = new ArrayList<>();
    List<IntVar> blockSums = new ArrayList<>();
    for (int from = 0; from < n; from += size) {
      int to = Math.min(n, from + size);
      if (to - from == 1 && w[from] == 1) {
        sums.add(x[from]);
        continue;
      }
      long lo = 0;
      long hi = 0;
      IntVar[] bv = new IntVar[to - from + 1];
      int[] bw = new int[to - from + 1];
      for (int i = from; i < to; i++) {
        long p = w[i] * x[i].min();
        long q = w[i] * x[i].max();
        lo += Math.min(p, q);
        hi += Math.max(p, q);
        bv[i - from] = x[i];
        bw[i - from] = (int) w[i];
      }
      if (lo < IntDomain.MIN_INT || hi > IntDomain.MAX_INT) {
        return null;
      }
      IntVar s = new IntVar(store, (int) lo, (int) hi);
      bv[to - from] = s;
      bw[to - from] = -1;
      sums.add(s);
      blockSums.add(s);
      LinearInt block = new LinearInt(bv, bw, "==", 0);
      // a block's failure weighs its terms, not the block sum, which no search branches on first
      block.setWeightedVariables(Arrays.copyOfRange(x, from, to));
      blocks.add(block);
    }
    for (Constraint b : blocks) {
      store.impose(b);
    }
    blockSums.forEach(defined);
    IntVar[] top = sums.toArray(new IntVar[0]);
    int[] ones = new int[top.length];
    Arrays.fill(ones, 1);
    String rel =
        switch (f.relation()) {
          case LinearForm.LE -> "<=";
          case LinearForm.GE -> ">=";
          default -> "==";
        };
    LinearInt sum = new LinearInt(top, ones, rel, (int) f.c());
    // dom/wdeg weighs the terms when the sum of the blocks fails, as when the unsplit constraint
    // fails; with only the block sums weighed, cutstock type04_TEST9 found no solution in 60 s
    sum.setWeightedVariables(x);
    return sum;
  }

  // the linear relation of a sum, weighted sum or pseudo-Boolean constraint, else null
  private static LinearForm form(Constraint c) {
    if (c.getClass() == LinearInt.class) {
      return ((LinearInt) c).linearForm();
    }
    return switch (c) {
      case LinearBool b -> b.linearForm();
      case SumWeight s -> s.linearForm();
      case SumInt s -> s.linearForm();
      case SumBool s -> s.linearForm();
      case Sum s -> s.linearForm();
      default -> null;
    };
  }
}
