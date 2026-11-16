/*
 * MaxSatLocalSearch.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * preservation of specified reasonable legal notices and author attributions
 * in accordance with Section 7 of this License.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.search.ls;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.SplittableRandom;
import java.util.function.BooleanSupplier;

/**
 * Local search for weighted partial MaxSAT: hard clauses, and soft clauses with positive weights
 * whose falsified weights sum to the cost. It follows SATLike (Lei and Cai, Solving (weighted)
 * partial MaxSAT through satisfiability testing, SAT 2018; Cai and Lei, Old techniques in new ways:
 * clause weighting, unit propagation and hybridization for maximum satisfiability, Artificial
 * Intelligence 287, 2020): every clause has a dynamic weight, the score of a variable is the weight
 * of the clauses its flip satisfies minus the weight of those it falsifies, a variable with a
 * positive score is flipped, the best of a sample of them (best from multiple selections, Cai
 * 2015), and at a local optimum the weights of the falsified hard clauses rise by a step, those of
 * the falsified soft clauses by one up to a bound proportional to their weight, and a variable of a
 * random falsified clause, hard ones first, is flipped.
 *
 * <p>Literals are {@code 2 * v} (variable v true) and {@code 2 * v + 1} (v false).
 */
public final class MaxSatLocalSearch {

  private final int n;
  private final int[][] clauses;
  // clauses [0, hard) are hard, the others soft
  private final int hard;
  private final long[] weight;
  private final long[] dynamic;
  private final long[] limit;
  private final int[] satCount;
  private final int[] satVar;
  // per variable, the clauses it is in, and whether it is positive there
  private final int[][] occurs;
  private final boolean[][] positive;
  private final boolean[] value;
  private final long[] score;
  private final long[] stamp;
  private final int[] falseHard;
  private final int[] falseHardAt;
  private int falseHards;
  private final int[] falseSoft;
  private final int[] falseSoftAt;
  private int falseSofts;
  private final int[] good;
  private final int[] goodAt;
  private int goods;
  // the weight of the falsified soft clauses
  private long cost;
  private long best = Long.MAX_VALUE;
  private boolean[] bestValue;
  private final SplittableRandom random;
  private long steps;
  private long improvements;
  private int lowestHard = Integer.MAX_VALUE;

  private long hardStep = 1;
  private double smoothing = 0.01;
  private int sample = 15;

  /**
   * A search over the given clauses.
   *
   * @param vars the number of variables
   * @param hardClauses the hard clauses
   * @param softClauses the soft clauses
   * @param softWeights the weight of each soft clause, positive
   * @param softBound the bound of the dynamic weight of a soft clause of average weight
   * @param seed the seed of the random choices
   */
  public MaxSatLocalSearch(
      int vars,
      List<int[]> hardClauses,
      List<int[]> softClauses,
      long[] softWeights,
      long softBound,
      long seed) {
    n = vars;
    List<int[]> all = new ArrayList<>();
    List<Long> ws = new ArrayList<>();
    for (int[] c : hardClauses) {
      int[] s = simplify(c);
      if (s != null) {
        all.add(s);
        ws.add(0L);
      }
    }
    hard = all.size();
    long total = 0;
    int softs = 0;
    for (int k = 0; k < softClauses.size(); k++) {
      int[] s = simplify(softClauses.get(k));
      if (s != null && softWeights[k] > 0) {
        all.add(s);
        ws.add(softWeights[k]);
        total += softWeights[k];
        softs++;
      }
    }
    clauses = all.toArray(new int[0][]);
    int m = clauses.length;
    weight = new long[m];
    dynamic = new long[m];
    limit = new long[m];
    double average = softs == 0 ? 1 : (double) total / softs;
    for (int c = 0; c < m; c++) {
      weight[c] = ws.get(c);
      dynamic[c] = 1;
      limit[c] =
          c < hard ? Long.MAX_VALUE : Math.max(1, Math.round(softBound * weight[c] / average));
    }
    int[] count = new int[n];
    for (int[] c : clauses) {
      for (int lit : c) {
        count[lit >> 1]++;
      }
    }
    occurs = new int[n][];
    positive = new boolean[n][];
    for (int v = 0; v < n; v++) {
      occurs[v] = new int[count[v]];
      positive[v] = new boolean[count[v]];
    }
    Arrays.fill(count, 0);
    for (int c = 0; c < m; c++) {
      for (int lit : clauses[c]) {
        int v = lit >> 1;
        occurs[v][count[v]] = c;
        positive[v][count[v]++] = (lit & 1) == 0;
      }
    }
    satCount = new int[m];
    satVar = new int[m];
    value = new boolean[n];
    score = new long[n];
    stamp = new long[n];
    falseHard = new int[m];
    falseHardAt = new int[m];
    falseSoft = new int[m];
    falseSoftAt = new int[m];
    good = new int[n];
    goodAt = new int[n];
    random = new SplittableRandom(seed);
  }

  // the clause without repeated literals, or null when it is a tautology
  private static int[] simplify(int[] c) {
    int[] s = c.clone();
    Arrays.sort(s);
    int k = 0;
    for (int i = 0; i < s.length; i++) {
      if (k > 0 && s[k - 1] == s[i]) {
        continue;
      }
      if (k > 0 && (s[k - 1] ^ 1) == s[i]) {
        return null;
      }
      s[k++] = s[i];
    }
    return Arrays.copyOf(s, k);
  }

  /** Sets the step by which the weight of a falsified hard clause rises at a local optimum. */
  public MaxSatLocalSearch hardStep(long step) {
    hardStep = step;
    return this;
  }

  /** Sets the probability of smoothing the soft weights at a local optimum. */
  public MaxSatLocalSearch smoothing(double p) {
    smoothing = p;
    return this;
  }

  /** Sets the number of good variables sampled for each flip. */
  public MaxSatLocalSearch sample(int t) {
    sample = t;
    return this;
  }

  private boolean isTrue(int lit) {
    return value[lit >> 1] == ((lit & 1) == 0);
  }

  /**
   * Starts from the given assignment, keeping the dynamic weights.
   *
   * @param start the value of each variable
   */
  public void start(boolean[] start) {
    System.arraycopy(start, 0, value, 0, n);
    Arrays.fill(score, 0);
    falseHards = 0;
    falseSofts = 0;
    goods = 0;
    cost = 0;
    for (int c = 0; c < clauses.length; c++) {
      int sc = 0;
      for (int lit : clauses[c]) {
        if (isTrue(lit)) {
          sc++;
          satVar[c] = lit >> 1;
        }
      }
      satCount[c] = sc;
      if (sc == 0) {
        falsify(c);
        for (int lit : clauses[c]) {
          score[lit >> 1] += dynamic[c];
        }
      } else if (sc == 1) {
        score[satVar[c]] -= dynamic[c];
      }
    }
    for (int v = 0; v < n; v++) {
      if (score[v] > 0) {
        goodAt[v] = goods;
        good[goods++] = v;
      }
    }
    record();
  }

  private void falsify(int c) {
    if (c < hard) {
      falseHardAt[c] = falseHards;
      falseHard[falseHards++] = c;
    } else {
      falseSoftAt[c] = falseSofts;
      falseSoft[falseSofts++] = c;
      cost += weight[c];
    }
  }

  private void satisfy(int c) {
    if (c < hard) {
      int last = falseHard[--falseHards];
      falseHard[falseHardAt[c]] = last;
      falseHardAt[last] = falseHardAt[c];
    } else {
      int last = falseSoft[--falseSofts];
      falseSoft[falseSoftAt[c]] = last;
      falseSoftAt[last] = falseSoftAt[c];
      cost -= weight[c];
    }
  }

  private void addScore(int v, long d) {
    long old = score[v];
    long now = old + d;
    score[v] = now;
    if (old <= 0 && now > 0) {
      goodAt[v] = goods;
      good[goods++] = v;
    } else if (old > 0 && now <= 0) {
      int last = good[--goods];
      good[goodAt[v]] = last;
      goodAt[last] = goodAt[v];
    }
  }

  private void flip(int v) {
    boolean now = !value[v];
    value[v] = now;
    int[] occ = occurs[v];
    boolean[] pos = positive[v];
    for (int k = 0; k < occ.length; k++) {
      int c = occ[k];
      long w = dynamic[c];
      if (pos[k] == now) {
        int s = ++satCount[c];
        if (s == 1) {
          for (int lit : clauses[c]) {
            addScore(lit >> 1, -w);
          }
          addScore(v, -w);
          satVar[c] = v;
          satisfy(c);
        } else if (s == 2) {
          addScore(satVar[c], w);
        }
      } else {
        int s = --satCount[c];
        if (s == 0) {
          for (int lit : clauses[c]) {
            addScore(lit >> 1, w);
          }
          addScore(v, w);
          falsify(c);
        } else if (s == 1) {
          for (int lit : clauses[c]) {
            if (isTrue(lit)) {
              satVar[c] = lit >> 1;
              addScore(lit >> 1, -w);
              break;
            }
          }
        }
      }
    }
    stamp[v] = steps;
  }

  // the dynamic weights at a local optimum: smoothed, or raised on the falsified clauses
  private void updateWeights() {
    if (random.nextDouble() < smoothing) {
      for (int c = 0; c < clauses.length; c++) {
        long d = c < hard ? hardStep : 1;
        if (satCount[c] > 0 && dynamic[c] > d) {
          dynamic[c] -= d;
          if (satCount[c] == 1) {
            addScore(satVar[c], d);
          }
        }
      }
      return;
    }
    for (int k = 0; k < falseHards; k++) {
      int c = falseHard[k];
      dynamic[c] += hardStep;
      for (int lit : clauses[c]) {
        addScore(lit >> 1, hardStep);
      }
    }
    for (int k = 0; k < falseSofts; k++) {
      int c = falseSoft[k];
      if (dynamic[c] < limit[c]) {
        dynamic[c]++;
        for (int lit : clauses[c]) {
          addScore(lit >> 1, 1);
        }
      }
    }
  }

  // the best variable of a sample of the good ones, the least recently flipped on ties
  private int sampleGood() {
    int bestVar = -1;
    if (goods <= sample) {
      for (int k = 0; k < goods; k++) {
        bestVar = better(good[k], bestVar);
      }
    } else {
      for (int k = 0; k < sample; k++) {
        bestVar = better(good[random.nextInt(goods)], bestVar);
      }
    }
    return bestVar;
  }

  private int better(int v, int than) {
    if (than < 0 || score[v] > score[than] || (score[v] == score[than] && stamp[v] < stamp[than])) {
      return v;
    }
    return than;
  }

  private void record() {
    if (falseHards == 0 && cost < best) {
      best = cost;
      if (bestValue == null) {
        bestValue = new boolean[n];
      }
      System.arraycopy(value, 0, bestValue, 0, n);
      improvements++;
    }
  }

  /**
   * Flips variables until the cost is zero, the steps are taken, or stop says so.
   *
   * @param maxSteps the number of flips
   * @param stop checked every 1024 flips
   * @return the best cost of an assignment satisfying the hard clauses, Long.MAX_VALUE for none
   */
  public long run(long maxSteps, BooleanSupplier stop) {
    for (long s = 0; s < maxSteps; s++) {
      if (falseHards == 0 && falseSofts == 0) {
        break;
      }
      if ((s & 1023) == 0 && stop.getAsBoolean()) {
        break;
      }
      steps++;
      int v;
      if (goods > 0) {
        v = sampleGood();
      } else {
        updateWeights();
        int c =
            falseHards > 0
                ? falseHard[random.nextInt(falseHards)]
                : falseSoft[random.nextInt(falseSofts)];
        v = -1;
        for (int lit : clauses[c]) {
          v = better(lit >> 1, v);
        }
      }
      flip(v);
      if (falseHards < lowestHard) {
        lowestHard = falseHards;
      }
      if (falseHards == 0 && cost < best) {
        record();
      }
    }
    return best;
  }

  /**
   * Whether the counts, scores, lists and cost agree with the current assignment, recomputed from
   * the clauses (for tests).
   */
  boolean consistent() {
    long[] sc = new long[n];
    long c0 = 0;
    int fh = 0;
    int fs = 0;
    for (int c = 0; c < clauses.length; c++) {
      int count = 0;
      int sv = -1;
      for (int lit : clauses[c]) {
        if (isTrue(lit)) {
          count++;
          sv = lit >> 1;
        }
      }
      if (count != satCount[c] || (count == 1 && sv != satVar[c])) {
        return false;
      }
      if (count == 0) {
        for (int lit : clauses[c]) {
          sc[lit >> 1] += dynamic[c];
        }
        if (c < hard) {
          fh++;
        } else {
          fs++;
          c0 += weight[c];
        }
      } else if (count == 1) {
        sc[sv] -= dynamic[c];
      }
    }
    int g = 0;
    for (int v = 0; v < n; v++) {
      if (sc[v] != score[v]) {
        return false;
      }
      g += sc[v] > 0 ? 1 : 0;
    }
    return c0 == cost && fh == falseHards && fs == falseSofts && g == goods;
  }

  /** The best cost, Long.MAX_VALUE when no assignment satisfied the hard clauses. */
  public long bestCost() {
    return best;
  }

  /** The best assignment, or null. */
  public boolean[] bestAssignment() {
    return bestValue;
  }

  /** Sets every dynamic weight back to one; call {@link #start} next. */
  public void resetWeights() {
    Arrays.fill(dynamic, 1);
  }

  /** Forgets the best assignment, so that the next run records its own from the start. */
  public void forgetBest() {
    best = Long.MAX_VALUE;
  }

  /** The cost of the current assignment, counting only soft clauses. */
  public long cost() {
    return cost;
  }

  /** The fewest hard clauses an assignment of the runs so far falsified. */
  public int lowestFalsifiedHard() {
    return Math.min(lowestHard, falseHards);
  }

  /** The number of hard clauses the current assignment falsifies. */
  public int falsifiedHard() {
    return falseHards;
  }

  /** Statistics: the flips taken. */
  public long steps() {
    return steps;
  }

  /** Statistics: the better assignments recorded. */
  public long improvements() {
    return improvements;
  }

  /** The number of variables. */
  public int variables() {
    return n;
  }

  /** The number of hard clauses kept. */
  public int hardClauses() {
    return hard;
  }

  /** The number of soft clauses kept. */
  public int softClauses() {
    return clauses.length - hard;
  }
}
