/*
 * GlobalConstraints.java
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

package org.jacop.fz.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.core.IntVar;
import org.jacop.fz.FzConsole;

/**
 * It gives a bin packing constraint the counters of a closed global cardinality constraint over the
 * same bin variables, so that {@link Binpacking} reasons on the number of items of each bin (bin
 * packing with cardinality, Schaus et al. CP 2012; Derval, Régin and Schaus, Constraints 2018).
 * Models such as the balanced academic curriculum write the two constraints separately.
 *
 * <p>The system property {@code org.jacop.fz.binPackingCardinality=false} turns it off.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
final class BinPackingCardinality {

  // the arguments of one bin packing constraint and the constraint built from them; a plain class,
  // since a record would compare its arrays by identity
  private static final class Packing {
    final IntVar[] bin;
    final IntVar[] load;
    final int[] w;
    final int minBin;
    final Constraint posted;

    Packing(IntVar[] bin, IntVar[] load, int[] w, int minBin, Constraint posted) {
      this.bin = bin;
      this.load = load;
      this.w = w;
      this.minBin = minBin;
      this.posted = posted;
    }
  }

  private final Support support;

  // what a cardinality constraint says about the number of variables taking each value
  private static final class Counts {
    final Map<Integer, IntVar> counter;
    final Map<Integer, int[]> bounds;
    final boolean closed;

    Counts(Map<Integer, IntVar> counter, Map<Integer, int[]> bounds, boolean closed) {
      this.counter = counter;
      this.bounds = bounds;
      this.closed = closed;
    }
  }

  // the variables of a cardinality constraint -> its counts
  private final Map<List<IntVar>, Counts> counts = new HashMap<>();

  private final List<Packing> packings = new ArrayList<>();

  BinPackingCardinality(Support support) {
    this.support = support;
  }

  static boolean enabled() {
    return Boolean.parseBoolean(System.getProperty("org.jacop.fz.binPackingCardinality", "true"));
  }

  /**
   * It records the counters of a closed global cardinality constraint: x takes only the values of
   * counterOf, and counterOf.get(v) is the number of variables of x equal to v.
   */
  void addCounters(IntVar[] x, Map<Integer, IntVar> counterOf) {
    counts.putIfAbsent(
        Arrays.asList(x.clone()), new Counts(new HashMap<>(counterOf), Map.of(), true));
  }

  /**
   * It records the bounds of a cardinality constraint: bounds.get(v) holds the least and the
   * largest number of variables of x equal to v.
   */
  void addBounds(IntVar[] x, Map<Integer, int[]> bounds) {
    Map<Integer, int[]> copy = new HashMap<>();
    bounds.forEach((v, b) -> copy.put(v, b.clone()));
    counts.putIfAbsent(Arrays.asList(x.clone()), new Counts(Map.of(), copy, false));
  }

  /** It builds a bin packing constraint, to be posted with the delayed constraints. */
  Constraint binPacking(IntVar[] bin, IntVar[] load, int[] w, int minBin) {
    Constraint c =
        Binpacking.builder().bin(bin).load(load).w(w).minBin(minBin).lbPruning(true).build();
    packings.add(new Packing(bin.clone(), load, w.clone(), minBin, c));
    return c;
  }

  /**
   * It replaces each delayed bin packing constraint whose bin variables are those of a closed
   * global cardinality constraint by one with the counters as the numbers of items of the bins.
   */
  void attach() {
    if (!enabled()) {
      return;
    }
    int found = 0;
    for (Packing p : packings) {
      Counts c = counts.get(Arrays.asList(p.bin));
      if (c == null) {
        continue;
      }
      int n = p.bin.length;
      IntVar[] card = new IntVar[p.load.length];
      for (int j = 0; j < card.length; j++) {
        int v = p.minBin + j;
        IntVar counter = c.counter.get(v);
        int[] b = c.bounds.get(v);
        if (counter != null) {
          card[j] = counter;
        } else if (b != null && Math.max(0, b[0]) <= Math.min(n, b[1])) {
          card[j] = new IntVar(support.store, Math.max(0, b[0]), Math.min(n, b[1]));
        } else if (b != null) {
          card = null; // no solution; the cardinality constraint fails
          break;
        } else {
          // closed: no variable takes a value without a counter, so such a bin is empty
          card[j] = new IntVar(support.store, 0, c.closed ? 0 : n);
        }
      }
      if (card == null) {
        continue;
      }
      Constraint withCard;
      try {
        withCard =
            Binpacking.builder()
                .bin(p.bin)
                .load(p.load)
                .w(p.w)
                .minBin(p.minBin)
                .lbPruning(true)
                .card(card)
                .build();
      } catch (IllegalArgumentException e) {
        continue; // a counter is also a bin or load variable
      }
      for (int i = 0; i < support.delayedConstraints.size(); i++) {
        if (support.delayedConstraints.get(i) == p.posted) {
          support.delayedConstraints.set(i, withCard);
          found++;
          break;
        }
      }
    }
    if (support.options.debug() && found > 0) {
      FzConsole.println("% bin packing with cardinality: " + found + " constraints");
    }
  }
}
