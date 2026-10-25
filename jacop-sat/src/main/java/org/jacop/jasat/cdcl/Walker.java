/*
 * Walker.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.cdcl;

import java.util.Arrays;
import java.util.SplittableRandom;

/**
 * ProbSAT local search (Balint and Schoening 2012) used for rephasing, as CaDiCaL's walk: starting
 * from the saved phases, it flips variables of random falsified clauses, chosen with a probability
 * that falls exponentially with their break count, and keeps the assignment that falsifies the
 * fewest clauses. Literals are internal ({@code 2*var+sign}).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class Walker {

  // ProbSAT break bases by average clause length (CaDiCaL's fitted values)
  private static final double[] BASES = {2.0, 2.0, 2.0, 2.5, 3.7, 5.1, 7.3};

  private final int[] lits;
  private final int[] start;
  private final int numClauses;
  private final int[][] occ;
  private final int[] occSize;
  private final byte[] sign;
  private final byte[] best;
  private final int[] trueCount;
  private final int[] unsat;
  private final int[] unsatPos;
  private int numUnsat;
  private int bestUnsat;
  private final double[] weight = new double[64];
  private double[] score = new double[16];
  private final SplittableRandom random;

  /**
   * Creates a walker.
   *
   * @param numVars the number of variables
   * @param lits the literals of all clauses, one after the other
   * @param start where clause i starts in lits; start[numClauses] is the end
   * @param numClauses the number of clauses
   * @param phases the starting value of each variable, as a sign (0 true, 1 false)
   * @param seed the random seed
   */
  Walker(int numVars, int[] lits, int[] start, int numClauses, byte[] phases, long seed) {
    this.lits = lits;
    this.start = start;
    this.numClauses = numClauses;
    random = new SplittableRandom(seed);
    sign = Arrays.copyOf(phases, numVars);
    occSize = new int[2 * numVars];
    for (int k = 0; k < start[numClauses]; k++) {
      occSize[lits[k]]++;
    }
    occ = new int[2 * numVars][];
    for (int l = 0; l < 2 * numVars; l++) {
      occ[l] = new int[occSize[l]];
      occSize[l] = 0;
    }
    for (int i = 0; i < numClauses; i++) {
      for (int k = start[i]; k < start[i + 1]; k++) {
        occ[lits[k]][occSize[lits[k]]++] = i;
      }
    }
    trueCount = new int[numClauses];
    unsat = new int[numClauses];
    unsatPos = new int[numClauses];
    for (int i = 0; i < numClauses; i++) {
      for (int k = start[i]; k < start[i + 1]; k++) {
        if (isTrue(lits[k])) {
          trueCount[i]++;
        }
      }
      if (trueCount[i] == 0) {
        addUnsat(i);
      }
    }
    double length = numClauses == 0 ? 3 : (double) start[numClauses] / numClauses;
    double base = BASES[Math.min(BASES.length - 1, (int) Math.round(length))];
    for (int b = 0; b < weight.length; b++) {
      weight[b] = Math.pow(base, -b);
    }
    best = Arrays.copyOf(sign, numVars);
    bestUnsat = numUnsat;
  }

  /**
   * Walks until no clause is falsified or the effort is spent.
   *
   * @param effort the number of literal visits allowed
   * @return the least number of falsified clauses seen
   */
  int run(long effort) {
    long spent = 0;
    while (numUnsat > 0 && spent < effort) {
      int c = unsat[random.nextInt(numUnsat)];
      int from = start[c];
      int size = start[c + 1] - from;
      if (score.length < size) {
        score = new double[2 * size];
      }
      double sum = 0;
      for (int k = 0; k < size; k++) {
        int breaks = breakCount(lits[from + k] ^ 1);
        spent += occSize[lits[from + k] ^ 1];
        sum += weight[Math.min(breaks, weight.length - 1)];
        score[k] = sum;
      }
      double r = random.nextDouble() * sum;
      int k = 0;
      while (k < size - 1 && score[k] <= r) {
        k++;
      }
      flip(lits[from + k] >> 1);
      spent += occSize[lits[from + k]] + occSize[lits[from + k] ^ 1];
      if (numUnsat < bestUnsat) {
        bestUnsat = numUnsat;
        System.arraycopy(sign, 0, best, 0, sign.length);
      }
    }
    return bestUnsat;
  }

  /** The best assignment found, as signs. */
  byte[] best() {
    return best;
  }

  private boolean isTrue(int lit) {
    return sign[lit >> 1] == (lit & 1);
  }

  /** The clauses that the true literal t alone satisfies. */
  private int breakCount(int t) {
    int n = 0;
    int[] o = occ[t];
    for (int i = occSize[t] - 1; i >= 0; i--) {
      if (trueCount[o[i]] == 1) {
        n++;
      }
    }
    return n;
  }

  private void flip(int v) {
    int t = 2 * v + sign[v];
    sign[v] ^= 1;
    int[] o = occ[t];
    for (int i = occSize[t] - 1; i >= 0; i--) {
      if (--trueCount[o[i]] == 0) {
        addUnsat(o[i]);
      }
    }
    int f = t ^ 1;
    o = occ[f];
    for (int i = occSize[f] - 1; i >= 0; i--) {
      if (trueCount[o[i]]++ == 0) {
        removeUnsat(o[i]);
      }
    }
  }

  private void addUnsat(int c) {
    unsatPos[c] = numUnsat;
    unsat[numUnsat++] = c;
  }

  private void removeUnsat(int c) {
    int last = unsat[--numUnsat];
    unsat[unsatPos[c]] = last;
    unsatPos[last] = unsatPos[c];
  }
}
