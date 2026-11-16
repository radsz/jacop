/*
 * JumpSearch.java
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
import java.util.function.BooleanSupplier;

/**
 * Weighted constraint-violation local search for clauses, in the style of Feasibility Jump
 * (Luteberget and Sartor, Feasibility Jump: an LP-free Lagrangian MIP heuristic, Mathematical
 * Programming Computation 15, 2023), the first-solution local search of CP-SAT. For a clause a
 * variable's jump is its flip, so the search is a clause-weighting method of the breakout kind
 * (Morris, The breakout method for escaping from local minima, AAAI 1993): every clause has a
 * weight, the score of a variable is the weight of the falsified clauses its flip satisfies minus
 * the weight of the clauses it alone satisfies; the best of a sample of the variables with a
 * positive score is flipped, and at a local minimum the weight of every falsified clause rises by
 * one and the best variable of a random falsified clause is flipped. The search restarts from a
 * random assignment, with fresh weights, after a number of flips that follows the Luby sequence
 * (Luby, Sinclair and Zuckerman, Optimal speedup of Las Vegas algorithms, Information Processing
 * Letters 47, 1993): a single run on the hard satisfiable instances it is meant for gets stuck far
 * more often than a series of short ones.
 *
 * <p>Literals are internal ({@code 2*var+sign}, sign 0 for the positive literal). A search keeps
 * its state between calls of {@link #run}, so that the solver can give it its share of the time in
 * slices.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class JumpSearch {

  /** Flips of the first run; later runs take multiples of it along the Luby sequence. */
  static final long RESTART_UNIT = 100_000;

  // variables of the good list sampled for the best flip
  private static final int SAMPLE = 16;

  private final int numVars;
  private final int[] lits;
  private final int[] start;
  private final int numClauses;
  private final int[][] occ;
  private final byte[] sign;
  private final int[] trueCount;
  // the exclusive or of the true variables of a clause: its true variable when it has one only
  private final int[] trueVars;
  private final long[] weight;
  private final long[] score;
  private final int[] unsat;
  private final int[] unsatPos;
  private int numUnsat;
  private final int[] good;
  private final int[] goodPos;
  private int numGood;
  private final SplittableRandom random;

  private long flips;
  private long ticks;
  private long nextRestart = RESTART_UNIT;
  private int restarts;
  private int bestUnsat = Integer.MAX_VALUE;

  /**
   * Creates a search over the given clauses, none of them empty.
   *
   * @param numVars the number of variables
   * @param lits the literals of all clauses, one after the other
   * @param start where clause i starts in lits; start[numClauses] is the end
   * @param numClauses the number of clauses
   * @param phases the starting value of each variable, as a sign (0 true, 1 false)
   * @param seed the random seed
   */
  JumpSearch(int numVars, int[] lits, int[] start, int numClauses, byte[] phases, long seed) {
    this.numVars = numVars;
    this.lits = lits;
    this.start = start;
    this.numClauses = numClauses;
    random = new SplittableRandom(seed);
    sign = Arrays.copyOf(phases, numVars);
    int[] size = new int[2 * numVars];
    for (int k = 0; k < start[numClauses]; k++) {
      size[lits[k]]++;
    }
    occ = new int[2 * numVars][];
    for (int l = 0; l < 2 * numVars; l++) {
      occ[l] = new int[size[l]];
      size[l] = 0;
    }
    for (int c = 0; c < numClauses; c++) {
      for (int k = start[c]; k < start[c + 1]; k++) {
        occ[lits[k]][size[lits[k]]++] = c;
      }
    }
    trueCount = new int[numClauses];
    trueVars = new int[numClauses];
    weight = new long[numClauses];
    unsat = new int[numClauses];
    unsatPos = new int[numClauses];
    score = new long[numVars];
    good = new int[numVars];
    goodPos = new int[numVars];
    reset();
  }

  /**
   * Searches until no clause is falsified, the ticks are spent or stop says so.
   *
   * @param tickLimit the ticks (visited occurrences and literals) this call may spend
   * @param stop checked every 256 flips; true stops the search
   * @return whether the assignment satisfies every clause
   */
  boolean run(long tickLimit, BooleanSupplier stop) {
    long end = tickLimit > Long.MAX_VALUE - ticks ? Long.MAX_VALUE : ticks + tickLimit;
    while (numUnsat > 0) {
      if ((flips & 255) == 0 && (ticks >= end || stop.getAsBoolean())) {
        return false;
      }
      if (flips >= nextRestart) {
        restarts++;
        nextRestart = flips + RESTART_UNIT * luby(restarts);
        for (int v = 0; v < numVars; v++) {
          sign[v] = (byte) random.nextInt(2);
        }
        reset();
      }
      flip(pick());
      flips++;
      bestUnsat = Math.min(bestUnsat, numUnsat);
    }
    return true;
  }

  /** The current assignment, as signs (0 true, 1 false); a model when {@link #run} said so. */
  byte[] signs() {
    return sign;
  }

  /** The flips so far. */
  long flips() {
    return flips;
  }

  /** The work so far: occurrences and literals visited. */
  long ticks() {
    return ticks;
  }

  /** The restarts so far. */
  int restarts() {
    return restarts;
  }

  /** The fewest falsified clauses seen. */
  int bestUnsat() {
    return bestUnsat;
  }

  /**
   * The i-th term (from 0) of the Luby sequence 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8 ...
   *
   * @param i the index
   * @return the term
   */
  static long luby(int i) {
    long x = i;
    long size = 1;
    int seq = 0;
    while (size < x + 1) {
      seq++;
      size = 2 * size + 1;
    }
    while (size - 1 != x) {
      size = (size - 1) >> 1;
      seq--;
      x = x % size;
    }
    return 1L << seq;
  }

  // weights back to one, counts, scores and lists from the signs
  private void reset() {
    numUnsat = 0;
    numGood = 0;
    Arrays.fill(score, 0);
    Arrays.fill(goodPos, -1);
    Arrays.fill(weight, 1);
    for (int c = 0; c < numClauses; c++) {
      int n = 0;
      int x = 0;
      for (int k = start[c]; k < start[c + 1]; k++) {
        if (isTrue(lits[k])) {
          n++;
          x ^= lits[k] >> 1;
        }
      }
      trueCount[c] = n;
      trueVars[c] = x;
      if (n == 0) {
        addUnsat(c);
        for (int k = start[c]; k < start[c + 1]; k++) {
          score[lits[k] >> 1]++;
        }
      } else if (n == 1) {
        score[x]--;
      }
    }
    ticks += start[numClauses];
    for (int v = 0; v < numVars; v++) {
      updateGood(v);
    }
    bestUnsat = Math.min(bestUnsat, numUnsat);
  }

  private int pick() {
    int best = -1;
    long bestScore = 0;
    if (numGood > 0) {
      boolean all = numGood <= SAMPLE;
      int samples = all ? numGood : SAMPLE;
      for (int s = 0; s < samples; s++) {
        int v = good[all ? s : random.nextInt(numGood)];
        if (best < 0 || score[v] > bestScore) {
          best = v;
          bestScore = score[v];
        }
      }
      return best;
    }
    // a local minimum: the falsified clauses weigh more, then the best variable of one of them
    for (int i = 0; i < numUnsat; i++) {
      int c = unsat[i];
      weight[c]++;
      for (int k = start[c]; k < start[c + 1]; k++) {
        addScore(lits[k] >> 1, 1);
      }
      ticks += start[c + 1] - start[c];
    }
    int c = unsat[random.nextInt(numUnsat)];
    for (int k = start[c]; k < start[c + 1]; k++) {
      int v = lits[k] >> 1;
      if (best < 0 || score[v] > bestScore) {
        best = v;
        bestScore = score[v];
      }
    }
    return best;
  }

  private void flip(int v) {
    int t = 2 * v + sign[v]; // true now, false after the flip
    sign[v] ^= 1;
    score[v] = -score[v];
    int[] o = occ[t];
    for (int c : o) {
      int n = --trueCount[c];
      trueVars[c] ^= v;
      if (n == 0) {
        addUnsat(c);
        for (int k = start[c]; k < start[c + 1]; k++) {
          int u = lits[k] >> 1;
          if (u != v) {
            addScore(u, weight[c]);
          }
        }
        ticks += start[c + 1] - start[c];
      } else if (n == 1) {
        addScore(trueVars[c], -weight[c]);
      }
    }
    o = occ[t ^ 1];
    for (int c : o) {
      int n = ++trueCount[c];
      trueVars[c] ^= v;
      if (n == 1) {
        removeUnsat(c);
        for (int k = start[c]; k < start[c + 1]; k++) {
          int u = lits[k] >> 1;
          if (u != v) {
            addScore(u, -weight[c]);
          }
        }
        ticks += start[c + 1] - start[c];
      } else if (n == 2) {
        addScore(trueVars[c] ^ v, weight[c]);
      }
    }
    ticks += occ[t].length + occ[t ^ 1].length;
    updateGood(v);
  }

  private boolean isTrue(int lit) {
    return sign[lit >> 1] == (lit & 1);
  }

  private void addScore(int v, long delta) {
    score[v] += delta;
    updateGood(v);
  }

  private void updateGood(int v) {
    if (score[v] > 0) {
      if (goodPos[v] < 0) {
        goodPos[v] = numGood;
        good[numGood++] = v;
      }
    } else if (goodPos[v] >= 0) {
      int last = good[--numGood];
      good[goodPos[v]] = last;
      goodPos[last] = goodPos[v];
      goodPos[v] = -1;
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
