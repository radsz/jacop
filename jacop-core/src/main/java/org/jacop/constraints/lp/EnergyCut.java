/*
 * EnergyCut.java
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

package org.jacop.constraints.lp;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Energy cuts of a resource over the start times of its tasks (the mean busy time relaxation).
 *
 * <p>A task j of duration {@code d_j} and usage {@code r_j} has energy {@code e_j = d_j r_j} and
 * mean busy time {@code s_j + d_j / 2}. The usage of a set S of tasks never exceeds the capacity C
 * and starts no earlier than {@code t = min est_j}, so the energy-weighted mean busy times are at
 * least those of a schedule that runs at full capacity from t: {@code sum e_j (s_j + d_j / 2) >= t
 * E + E^2 / (2 C)} with {@code E = sum e_j}. Times 2C, in integers: {@code sum 2 C e_j s_j >= 2 C t
 * E + E^2 - C sum e_j d_j}. It holds for every S, so the separation sorts the tasks by their LP
 * mean busy times and tries each prefix, and each suffix after a release date, keeping the most
 * violated one. The earliest starts are the root bounds, so the cuts are global.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class EnergyCut {

  private final int[] column;
  private final long[] dur;
  private final long[] energy;
  private final long[] est;
  private final long cap;

  /**
   * Creates the separator of one resource.
   *
   * @param column the column of the start of each task
   * @param dur the duration of each task
   * @param use the usage of each task
   * @param est the earliest start of each task at the root
   * @param cap the capacity
   */
  EnergyCut(int[] column, long[] dur, long[] use, long[] est, long cap) {
    this.column = column;
    this.dur = dur;
    this.energy = new long[column.length];
    for (int j = 0; j < column.length; j++) {
      energy[j] = Math.multiplyExact(dur[j], use[j]);
    }
    this.est = est;
    this.cap = cap;
  }

  /**
   * Adds the most violated energy cut of the LP solution, if any.
   *
   * @param value the LP solution by column
   * @param found the cuts found
   */
  void separate(double[] value, List<MirCut> found) {
    int n = column.length;
    Integer[] order = new Integer[n];
    for (int j = 0; j < n; j++) {
      order[j] = j;
    }
    Arrays.sort(
        order,
        (p, q) -> {
          double a = value[column[p]] + dur[p] / 2.0;
          double b = value[column[q]] + dur[q] / 2.0;
          return a != b ? Double.compare(a, b) : Integer.compare(p, q);
        });
    // the prefixes of the order, from each release date: only the tasks released at t or later
    long[] releases = Arrays.stream(est).distinct().sorted().toArray();
    MirCut best = null;
    for (long t : releases) {
      List<Integer> set = new ArrayList<>();
      for (int p = 0; p < n; p++) {
        int j = order[p];
        if (est[j] >= t) {
          set.add(j);
          if (set.size() >= 2) {
            MirCut c = cut(set, t, value);
            if (c != null && (best == null || c.efficacy > best.efficacy)) {
              best = c;
            }
          }
        }
      }
    }
    if (best != null) {
      found.add(best);
    }
  }

  // -sum 2 C e_j s_j <= -(2 C t E + E^2 - C sum e_j d_j), over increasing columns
  private MirCut cut(List<Integer> set, long t, double[] value) {
    try {
      long e = 0;
      long ed = 0;
      for (int j : set) {
        e = Math.addExact(e, energy[j]);
        ed = Math.addExact(ed, Math.multiplyExact(energy[j], dur[j]));
      }
      long right =
          Math.subtractExact(
              Math.addExact(
                  Math.multiplyExact(Math.multiplyExact(2 * cap, t), e), Math.multiplyExact(e, e)),
              Math.multiplyExact(cap, ed));
      int[] cs = new int[set.size()];
      long[] ws = new long[set.size()];
      Integer[] bycol = set.toArray(new Integer[0]);
      Arrays.sort(bycol, (p, q) -> Integer.compare(column[p], column[q]));
      for (int k = 0; k < bycol.length; k++) {
        cs[k] = column[bycol[k]];
        ws[k] = -Math.multiplyExact(2 * cap, energy[bycol[k]]);
      }
      for (int k = 1; k < cs.length; k++) {
        if (cs[k] == cs[k - 1]) {
          return null; // two tasks share a start variable
        }
      }
      long g = 0;
      for (long w : ws) {
        g = gcd(g, Math.abs(w));
      }
      // the weights are multiples of g, so the right side rounds up when divided by it
      for (int k = 0; k < ws.length; k++) {
        ws[k] /= g;
      }
      long rhs = -Math.ceilDiv(right, g);
      return MirCut.row(cs, ws, rhs, value);
    } catch (ArithmeticException _) {
      return null;
    }
  }

  private static long gcd(long a, long b) {
    while (b != 0) {
      long r = a % b;
      a = b;
      b = r;
    }
    return a;
  }
}
