/*
 * Factorizer.java
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
import java.util.PriorityQueue;

/**
 * Bounded variable addition (BVA) on the irredundant clauses at level 0: it replaces a grid of
 * clauses {@code f_p ∨ R_i} (factors {@code f_1..f_k}, quotients {@code R_1..R_n}) by {@code x ∨
 * f_p} and {@code ¬x ∨ R_i} on a fresh variable {@code x}, which turns {@code k·n} clauses into
 * {@code k+n}. Resolution on {@code x} gives the removed clauses back, so the new formula projected
 * on the old variables is the old one: a model of the new formula is a model of the old one, and
 * nothing has to be extended. Large at-most-one cliques, for example, shrink from quadratic to
 * linear size and the solver learns over the fresh variables.
 *
 * <p>The method is that of Manthey, Heule and Biere, "Automated reencoding of Boolean formulas",
 * HVC 2012 (SimpleBVA), in the form of Kissat's {@code factor}: one factor literal is taken at a
 * time, in order of most occurrences, and the next factor is the literal that completes the most
 * quotients of the last one; ties go to the literal with more occurrences, as in Haberlandt, Green
 * and Heule, "Effective auxiliary variables via structured reencoding", SAT 2023 (SBVA) without the
 * three-hop score. The grid with the largest clause reduction is applied. Only clauses with at most
 * {@link #SIZE_LIMIT} literals take part.
 *
 * <p>Each step is in the DRAT proof as RAT additions: {@code x ∨ f_p} first, which are RAT on the
 * fresh {@code x}, then {@code ¬x ∨ R_i}, whose resolvents on {@code ¬x} are the clauses still in
 * the formula, and the deletion of those clauses last. Literals are internal ({@code 2*var+sign}).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class Factorizer {

  /** Clauses longer than this do not take part. */
  static final int SIZE_LIMIT = 5;

  // effort (clause and occurrence visits) of one run
  static final long EFFORT_LIMIT = 1_000_000_000L;

  private static final int FACTOR = 1;
  private static final int QUOTIENT = 2;
  private static final int NOUNTED = 4;

  private final ProofOutput proof;
  private final int initialVars;
  private final long effortLimit;
  private long deadline = Long.MAX_VALUE;
  private int numVars;

  private int[][] clauses;
  private boolean[] dead;
  private int[] stamp; // per clause: used in this round of matching
  private int round;
  private int numClauses;
  private int live;

  private int[][] occ;
  private int[] occSize;
  private int[] count; // live occurrences per literal
  private int[] mark;
  private int[] tally; // per literal: how many quotients it completes
  private boolean[] tried;
  private long effort;
  private int fresh;
  private long removedClauses;

  // the long clauses that do not take part, given back unchanged
  private int[][] passive = new int[16][];
  private int numPassive;

  private final PriorityQueue<long[]> schedule =
      new PriorityQueue<>(
          (a, b) -> a[0] != b[0] ? Long.compare(b[0], a[0]) : Long.compare(a[1], b[1]));

  /** One factor literal with the clauses holding it, matched to the ones of the factor before. */
  private static final class Quotient {
    final int factor;
    int[] clauses = new int[8];
    int[] matches = new int[8];
    int size;
    Quotient prev;
    int id;

    Quotient(int factor) {
      this.factor = factor;
    }

    void push(int clause, int match) {
      if (size == clauses.length) {
        clauses = Arrays.copyOf(clauses, 2 * size);
        matches = Arrays.copyOf(matches, 2 * size);
      }
      clauses[size] = clause;
      matches[size++] = match;
    }
  }

  /**
   * Creates a factorizer over the given clauses, which must have at least two literals, no
   * duplicate literal, no tautology, and no assigned literal.
   *
   * @param numVars the number of variables
   * @param input the clauses
   * @param numInput how many of them are used
   * @param proof the DRAT output, or null
   * @param effortLimit the effort allowed
   */
  Factorizer(int numVars, int[][] input, int numInput, ProofOutput proof, long effortLimit) {
    this.numVars = numVars;
    this.initialVars = numVars;
    this.proof = proof;
    this.effortLimit = effortLimit;
    int lits = 2 * numVars;
    count = new int[lits];
    // candidate clauses: a long clause whose literals all occur at least twice (two rounds, as in
    // Kissat), so a literal in only one clause never gets an occurrence list
    int[] small = new int[lits];
    for (int i = 0; i < numInput; i++) {
      int[] c = input[i];
      if (c.length <= SIZE_LIMIT) {
        for (int l : c) {
          small[l]++;
        }
      }
    }
    boolean[] keep = new boolean[numInput];
    for (int r = 0; r < 2; r++) {
      int[] next = new int[lits];
      for (int i = 0; i < numInput; i++) {
        int[] c = input[i];
        keep[i] = c.length <= SIZE_LIMIT && (c.length == 2 || allTwice(c, small));
        if (keep[i]) {
          for (int l : c) {
            next[l]++;
          }
        }
      }
      small = next;
    }
    int n = 0;
    for (int i = 0; i < numInput; i++) {
      if (keep[i]) {
        n++;
      }
    }
    clauses = new int[Math.max(16, n + n / 4)][];
    dead = new boolean[clauses.length];
    stamp = new int[clauses.length];
    occ = new int[lits][];
    occSize = new int[lits];
    mark = new int[lits];
    tally = new int[lits];
    tried = new boolean[lits];
    for (int l = 0; l < lits; l++) {
      occ[l] = small[l] == 0 ? null : new int[small[l]];
    }
    for (int i = 0; i < numInput; i++) {
      if (keep[i]) {
        add(input[i]);
      } else {
        if (numPassive == passive.length) {
          passive = Arrays.copyOf(passive, 2 * numPassive);
        }
        passive[numPassive++] = input[i];
      }
    }
  }

  private static boolean allTwice(int[] c, int[] small) {
    for (int l : c) {
      if (small[l] < 2) {
        return false;
      }
    }
    return true;
  }

  /** Stops the run at this System.nanoTime(). */
  void setDeadline(long deadline) {
    this.deadline = deadline;
  }

  private int add(int[] c) {
    if (numClauses == clauses.length) {
      int cap = 2 * numClauses;
      clauses = Arrays.copyOf(clauses, cap);
      dead = Arrays.copyOf(dead, cap);
      stamp = Arrays.copyOf(stamp, cap);
    }
    int id = numClauses++;
    clauses[id] = c;
    live++;
    for (int l : c) {
      if (occ[l] == null) {
        occ[l] = new int[4];
      } else if (occSize[l] == occ[l].length) {
        occ[l] = Arrays.copyOf(occ[l], 2 * occSize[l]);
      }
      occ[l][occSize[l]++] = id;
      count[l]++;
    }
    return id;
  }

  private void remove(int id) {
    dead[id] = true;
    live--;
    for (int l : clauses[id]) {
      count[l]--;
    }
  }

  /** Drops the dead clauses from an occurrence list. */
  private void flush(int lit) {
    int[] o = occ[lit];
    if (o == null || occSize[lit] == count[lit]) {
      return;
    }
    int j = 0;
    for (int i = 0; i < occSize[lit]; i++) {
      if (!dead[o[i]]) {
        o[j++] = o[i];
      }
    }
    effort += occSize[lit];
    occSize[lit] = j;
  }

  private void schedule(int lit) {
    if (count[lit] > 1 && !tried[lit]) {
      schedule.add(new long[] {count[lit], lit});
    }
  }

  /**
   * Runs bounded variable addition until no grid reduces the clauses or the effort is spent.
   *
   * @return the number of fresh variables
   */
  int run() {
    for (int l = 0; l < 2 * numVars; l++) {
      schedule(l);
    }
    while (!schedule.isEmpty() && effort < effortLimit) {
      long[] top = schedule.poll();
      int first = (int) top[1];
      if (tried[first] || count[first] != top[0]) {
        continue; // stale entry, or tried already
      }
      tried[first] = true;
      if ((effort & 0xff) == 0 && System.nanoTime() > deadline) {
        break;
      }
      Quotient q = firstQuotient(first);
      if (q.size < 2) {
        clearMarks(q);
        continue;
      }
      while (effort < effortLimit) {
        int next = nextFactor(q);
        if (next < 0) {
          break;
        }
        q = factorizeNext(q, next);
      }
      Quotient best = best(q);
      if (best != null && effort < effortLimit) {
        apply(best);
      }
      clearMarks(q);
    }
    return fresh;
  }

  private void clearMarks(Quotient q) {
    for (Quotient p = q; p != null; p = p.prev) {
      mark[p.factor] = 0;
    }
  }

  private Quotient firstQuotient(int factor) {
    flush(factor);
    Quotient q = new Quotient(factor);
    mark[factor] = FACTOR;
    for (int i = 0; i < occSize[factor]; i++) {
      q.push(occ[factor][i], i);
    }
    effort += occSize[factor];
    return q;
  }

  /**
   * Marks the literals of clause c other than the factors with QUOTIENT and returns the one with
   * the fewest occurrences, or -1 when c holds more than one factor.
   */
  private int markQuotient(int[] c) {
    int factors = 0;
    int min = -1;
    for (int l : c) {
      if ((mark[l] & FACTOR) != 0) {
        factors++;
      } else {
        mark[l] |= QUOTIENT;
        if (min < 0 || count[l] < count[min]) {
          min = l;
        }
      }
    }
    return factors == 1 ? min : -1;
  }

  private void unmarkQuotient(int[] c) {
    for (int l : c) {
      mark[l] &= ~QUOTIENT;
    }
  }

  /** The literal that completes the most clauses of the last quotient, or -1 if fewer than 2. */
  private int nextFactor(Quotient last) {
    round++;
    int[] counted = new int[16];
    int numCounted = 0;
    int[] nounted = new int[8];
    for (int i = 0; i < last.size; i++) {
      int[] c = clauses[last.clauses[i]];
      effort++;
      int min = markQuotient(c);
      if (min >= 0) {
        flush(min);
        int numNounted = 0;
        int[] o = occ[min];
        effort += occSize[min];
        for (int k = 0; k < occSize[min]; k++) {
          int d = o[k];
          if (d == last.clauses[i] || stamp[d] == round || clauses[d].length != c.length) {
            continue;
          }
          int next = -1;
          boolean fits = true;
          for (int l : clauses[d]) {
            int m = mark[l];
            if ((m & QUOTIENT) != 0) {
              continue;
            }
            if ((m & (FACTOR | NOUNTED)) != 0 || next >= 0) {
              fits = false;
              break;
            }
            next = l;
          }
          if (!fits || next < 0 || (next >> 1) >= initialVars) {
            continue;
          }
          mark[next] |= NOUNTED;
          if (numNounted == nounted.length) {
            nounted = Arrays.copyOf(nounted, 2 * numNounted);
          }
          nounted[numNounted++] = next;
          stamp[d] = round;
          if (tally[next]++ == 0) {
            if (numCounted == counted.length) {
              counted = Arrays.copyOf(counted, 2 * numCounted);
            }
            counted[numCounted++] = next;
          }
        }
        for (int k = 0; k < numNounted; k++) {
          mark[nounted[k]] &= ~NOUNTED;
        }
      }
      unmarkQuotient(c);
    }
    int best = -1;
    int bestTally = 0;
    for (int k = 0; k < numCounted; k++) {
      int l = counted[k];
      int t = tally[l];
      if (t > bestTally || t == bestTally && count[l] > count[best]) {
        best = l;
        bestTally = t;
      }
    }
    for (int k = 0; k < numCounted; k++) {
      tally[counted[k]] = 0;
    }
    return bestTally < 2 ? -1 : best;
  }

  private Quotient factorizeNext(Quotient last, int next) {
    round++;
    Quotient q = new Quotient(next);
    q.prev = last;
    q.id = last.id + 1;
    mark[next] = FACTOR;
    for (int i = 0; i < last.size; i++) {
      int[] c = clauses[last.clauses[i]];
      effort++;
      int min = markQuotient(c);
      if (min >= 0) {
        int[] o = occ[min];
        effort += occSize[min];
        for (int k = 0; k < occSize[min]; k++) {
          int d = o[k];
          if (dead[d]
              || d == last.clauses[i]
              || stamp[d] == round
              || clauses[d].length != c.length) {
            continue;
          }
          boolean fits = true;
          for (int l : clauses[d]) {
            if ((mark[l] & QUOTIENT) == 0 && l != next) {
              fits = false;
              break;
            }
          }
          if (fits) {
            q.push(d, i);
            stamp[d] = round;
            break;
          }
        }
      }
      unmarkQuotient(c);
    }
    return q;
  }

  /** The quotient whose grid removes the most clauses, or null when none removes any. */
  private static Quotient best(Quotient last) {
    Quotient best = null;
    long bestReduction = 0;
    for (Quotient q = last; q != null; q = q.prev) {
      long factors = q.id + 1L;
      long reduction = q.size * factors - (q.size + factors);
      if (reduction > 0 && reduction >= bestReduction) {
        best = q; // ties go to the earlier quotient, the one with more clauses
        bestReduction = reduction;
      }
    }
    return best;
  }

  private void apply(Quotient q) {
    // keep in every quotient only the rows that reach q
    for (Quotient p = q; p.prev != null; p = p.prev) {
      Quotient prev = p.prev;
      for (int i = 0; i < p.size; i++) {
        int j = p.matches[i];
        prev.clauses[i] = prev.clauses[j];
        prev.matches[i] = prev.matches[j];
      }
      prev.size = p.size;
    }
    int x = 2 * numVars;
    growVars();
    fresh++;
    for (Quotient p = q; p != null; p = p.prev) {
      int[] divider = {x, p.factor};
      if (proof != null) {
        proof.add(divider, 0, 2);
      }
      add(divider);
      tried[p.factor] = false;
    }
    for (int i = 0; i < q.size; i++) {
      int[] c = clauses[q.clauses[i]];
      int[] r = new int[c.length];
      r[0] = x ^ 1;
      int k = 1;
      for (int l : c) {
        if (l != q.factor) {
          r[k++] = l;
          tried[l] = false;
        }
      }
      if (proof != null) {
        proof.add(r, 0, r.length);
      }
      add(r);
    }
    for (Quotient p = q; p != null; p = p.prev) {
      for (int i = 0; i < p.size; i++) {
        int id = p.clauses[i];
        if (proof != null) {
          proof.delete(clauses[id], 0, clauses[id].length);
        }
        remove(id);
        removedClauses++;
      }
    }
    for (Quotient p = q; p != null; p = p.prev) {
      schedule(p.factor);
      schedule(p.factor ^ 1);
    }
    for (int i = 0; i < q.size; i++) {
      for (int l : clauses[q.clauses[i]]) {
        schedule(l);
      }
    }
    schedule(x);
    schedule(x ^ 1);
  }

  private void growVars() {
    numVars++;
    int lits = 2 * numVars;
    if (lits > count.length) {
      int cap = Math.max(lits, count.length + count.length / 2);
      count = Arrays.copyOf(count, cap);
      occ = Arrays.copyOf(occ, cap);
      occSize = Arrays.copyOf(occSize, cap);
      mark = Arrays.copyOf(mark, cap);
      tally = Arrays.copyOf(tally, cap);
      tried = Arrays.copyOf(tried, cap);
    }
  }

  /** The number of variables, the fresh ones included. */
  int numVars() {
    return numVars;
  }

  /** The number of fresh variables added. */
  int numFresh() {
    return fresh;
  }

  /** The number of clauses removed (the ones added not subtracted). */
  long removedClauses() {
    return removedClauses;
  }

  /** The effort spent. */
  long effort() {
    return effort;
  }

  /**
   * The clauses after the run: the ones that took part and are left, the added ones, and the long
   * ones unchanged.
   *
   * @return the clauses
   */
  int[][] clauses() {
    int[][] out = new int[live + numPassive][];
    int n = 0;
    for (int i = 0; i < numClauses; i++) {
      if (!dead[i]) {
        out[n++] = clauses[i];
      }
    }
    System.arraycopy(passive, 0, out, n, numPassive);
    return out;
  }
}
