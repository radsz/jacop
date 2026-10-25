/*
 * SeqPrecedeChain.java
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

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;

/**
 * It defines Sequence Precedence Chain constraint for integers.
 *
 * <p>The constraint requires that i precedes i+1 in the array x for all positive i (i > 0).
 *
 * <p>With a value chain c = [c1, ..., ck] it requires that c[i] precedes c[i+1] in x for all i
 * (value_precede_chain). Value c[i] then plays the role of i and every value outside c the role of
 * 0, as in the mapping of value_precede_chain onto seq_precede_chain by Gange and Stuckey.
 *
 * <p>The non-incremental algorithm is based on paper "Sequential Precede Chain for value symmetry
 * elimination " by Graeme Gange and Peter J. Stuckey, Proc. International Conference on Principles
 * and Practice of Constraint Programming * (CP'2018). It is domain consistent.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class SeqPrecedeChain extends Constraint implements Copyable<SeqPrecedeChain> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** It specifies lists of variables for the constraint. */
  final IntVar[] x;

  final int n;

  final int[] first;
  final int[] last;

  /** The value chain, chain[r - 1] has rank r; null when value v has rank v (seq_precede_chain). */
  final int[] chain;

  /** The values of the chain. */
  IntDomain chainValues;

  /** rankAtMost[r]: the values of rank at most r (values outside the chain have rank 0). */
  IntDomain[] rankAtMost;

  /** rankAtLeast[r]: the values of rank at least r, for r >= 1. */
  IntDomain[] rankAtLeast;

  /**
   * It constructs SeqPrecedeChain.
   *
   * @param x list of arguments x's.
   */
  public SeqPrecedeChain(IntVar[] x) {
    this(x, null);
  }

  /**
   * It constructs SeqPrecedeChain.
   *
   * @param x list of arguments x's.
   */
  public SeqPrecedeChain(List<? extends IntVar> x) {
    this(x.toArray(IntVar[]::new));
  }

  /**
   * It constructs value_precede_chain(c, x): c[i] precedes c[i+1] in x for every i.
   *
   * @param x list of arguments x's.
   * @param c the chain of values, all different; null gives seq_precede_chain(x).
   */
  public SeqPrecedeChain(IntVar[] x, int[] c) {

    checkInputForNullness("x", x);

    this.numberId = idNumber.incrementAndGet();

    this.n = x.length;
    this.x = Arrays.copyOf(x, n);

    first = new int[n + 1];
    last = new int[n + 1];

    if (c == null || isIdentity(c, x)) {
      chain = null;
    } else {
      chain = Arrays.copyOf(c, c.length);
      Set<Integer> seen = new HashSet<>();
      for (int v : chain) {
        if (!seen.add(v)) {
          throw new IllegalArgumentException(
              "SeqPrecedeChain: the values of the chain must differ");
        }
      }
      buildRankDomains();
    }

    queueIndex = 1;

    setScope(Arrays.stream(x));
  }

  /**
   * It constructs value_precede_chain(c, x): c[i] precedes c[i+1] in x for every i.
   *
   * @param x list of arguments x's.
   * @param c the chain of values, all different.
   */
  public SeqPrecedeChain(List<? extends IntVar> x, int[] c) {
    this(x.toArray(IntVar[]::new), c);
  }

  /** The chain 1..k behaves as seq_precede_chain when no variable can exceed k. */
  private static boolean isIdentity(int[] c, IntVar[] x) {
    for (int i = 0; i < c.length; i++) {
      if (c[i] != i + 1) {
        return false;
      }
    }
    for (IntVar v : x) {
      if (v.max() > c.length) {
        return false;
      }
    }
    return true;
  }

  private void buildRankDomains() {
    int k = chain.length;
    chainValues = new IntervalDomain();
    for (int v : chain) {
      chainValues.unionAdapt(v, v);
    }
    rankAtMost = new IntDomain[k + 1];
    rankAtLeast = new IntDomain[k + 2];
    // values outside the chain have rank 0
    IntDomain atMost =
        new IntervalDomain(IntDomain.MIN_INT, IntDomain.MAX_INT).subtract(chainValues);
    rankAtMost[0] = atMost;
    for (int r = 1; r <= k; r++) {
      atMost = atMost.union(chain[r - 1]);
      rankAtMost[r] = atMost;
    }
    IntDomain atLeast = new IntervalDomain();
    rankAtLeast[k + 1] = atLeast;
    for (int r = k; r >= 1; r--) {
      atLeast = atLeast.union(chain[r - 1]);
      rankAtLeast[r] = atLeast;
    }
  }

  @Override
  public void consistency(Store store) {

    Arrays.fill(first, 0);
    Arrays.fill(last, n + 1);

    if (chain == null) {
      int low = forwardPass(store);
      backwardPass(store, low);
    } else {
      int low = forwardPassChain(store);
      backwardPassChain(store, low);
    }
  }

  private int forwardPass(Store store) {
    int up = 0;
    int low = 0;
    for (int i = 1; i < n + 1; i++) {
      IntVar xi = x[i - 1];

      if (xi.max() > up + 1) {
        xi.domain.inMax(store.level, xi, up + 1);
      }
      if (xi.max() == up + 1) {
        up++;
        first[up] = i;
      }
      if (low < xi.min()) {
        last[xi.min()] = i;
        low = xi.min();
      }
    }
    return low;
  }

  private void backwardPass(Store store, int low) {
    for (int i = n; i >= 1; i--) {
      IntVar xi = x[i - 1];

      if (first[low] == i) {
        xi.domain.inMin(store.level, xi, low);
      }
      if (i <= last[low] && xi.domain.contains(low)) {
        last[low] = i;
        low--;
        if (low < 0) {
          break;
        }
      }
    }
  }

  /** forwardPass with ranks: up is the highest rank the prefix can reach. */
  private int forwardPassChain(Store store) {
    int k = chain.length;
    int up = 0;
    int low = 0;
    for (int i = 1; i < n + 1; i++) {
      IntVar xi = x[i - 1];

      if (up < k) {
        IntDomain allowed = rankAtMost[up + 1];
        if (!allowed.contains(xi.domain)) {
          xi.domain.in(store.level, xi, allowed);
        }
        if (xi.domain.contains(chain[up])) {
          up++;
          first[up] = i;
        }
      }
      int m = rankMin(xi);
      if (low < m) {
        last[m] = i;
        low = m;
      }
    }
    return low;
  }

  /** backwardPass with ranks; rank 0 (values outside the chain) needs no support. */
  private void backwardPassChain(Store store, int low) {
    for (int i = n; i >= 1 && low > 0; i--) {
      IntVar xi = x[i - 1];

      if (first[low] == i && !rankAtLeast[low].contains(xi.domain)) {
        xi.domain.in(store.level, xi, rankAtLeast[low]);
      }
      if (i <= last[low] && xi.domain.contains(chain[low - 1])) {
        last[low] = i;
        low--;
      }
    }
  }

  /** The smallest rank x can take. */
  private int rankMin(IntVar v) {
    if (!chainValues.contains(v.domain)) {
      return 0;
    }
    for (int r = 1; r <= chain.length; r++) {
      if (v.domain.contains(chain[r - 1])) {
        return r;
      }
    }
    return 0; // not reached: a non-empty domain inside the chain has a rank
  }

  @Override
  public String toString() {

    StringBuilder resultString = new StringBuilder(id());

    resultString.append(" : SeqPrecedeChain([");
    int lx = x.length;
    for (int i = 0; i < lx; i++) {
      resultString.append(x[i]);
      if (i < lx - 1) {
        resultString.append(", ");
      }
    }
    resultString.append("]");
    if (chain != null) {
      resultString.append(", ").append(Arrays.toString(chain));
    }
    resultString.append(")");

    return resultString.toString();
  }

  @Override
  public SeqPrecedeChain copy(VarMap map) {
    return chain == null ? new SeqPrecedeChain(map.get(x)) : new SeqPrecedeChain(map.get(x), chain);
  }
}
