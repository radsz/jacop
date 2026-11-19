/*
 * Eliminator.java
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

/**
 * Subsumption, self-subsuming strengthening and bounded variable elimination on the irredundant
 * clauses at level 0, as in MiniSat's SimpSolver. Literals are internal ({@code 2*var+sign}).
 *
 * <p>A variable is eliminated when the non-tautological resolvents on it outnumber the clauses they
 * replace by at most a bound and none is longer than a limit. The bound follows the schedule 0, 1,
 * 2, 4, 8, 16 of Kissat's {@code eliminatebound} (Biere, Järvisalo, Kiesl, "Preprocessing in SAT
 * Solving", Handbook of Satisfiability, 2nd ed., 2021): within a run it rises up to a given maximum
 * each time a round eliminates nothing, and {@link CdclSolver} raises it by one step between runs.
 * After the first round only the variables whose clauses changed are tried again. The removed
 * clauses go on an extension stack, from which {@link #extend} completes a model of the simplified
 * formula.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class Eliminator {

  // the bounds an elimination may add over the clauses it removes, raised in this order
  private static final int[] BOUNDS = {0, 1, 2, 4, 8, 16};
  // variables with more occurrences in one polarity are not tried
  private static final int OCC_LIMIT = 1000;
  // clauses longer than this are not used to subsume others
  private static final int SUBSUME_LIMIT = 100;
  // effort (literals visited) allowed in one run
  private static final long EFFORT_LIMIT = 300_000_000L;

  private static final int[] NO_OCCURRENCES = new int[0];

  private final int numVars;
  private final boolean[] frozen;
  // the longest resolvent an elimination may add
  private final int resolventLimit;
  // the largest bound to raise to
  private final int maxBound;
  // the bound in use: resolvents may outnumber the clauses they replace by this many
  private int bound;
  // variables whose clauses changed since they were last tried
  private final boolean[] touched;
  // whether to look for gate definitions, the extractor over the current clause array, and how
  // many eliminations used a gate
  private final boolean useGates;
  private GateExtractor gates;
  private int[][] gatesOver;
  private int numGateEliminations;
  private final ProofOutput proof;

  private int[][] clauses;
  private long[] sigs;
  private int numClauses;
  private final int[][] occ;
  private final int[] occSize;
  private final byte[] value;
  private int[] units = new int[16];
  private int numUnits;
  private int unitHead;
  private final boolean[] eliminated;
  private int[] stack = new int[64];
  private int stackSize;
  private int[] queue = new int[64];
  private int queueHead;
  private int queueSize;
  private boolean[] queued;
  private final int[] mark;
  private int stamp;
  private long effort;
  private boolean unsat;
  private int numEliminated;

  /**
   * An eliminator as in MiniSat: bound 0, resolvents of at most 20 literals, no gates.
   *
   * @param numVars the number of variables
   * @param input the clauses
   * @param numInput how many of them are used
   * @param frozen the variables that must not be eliminated
   * @param proof the DRAT output, or null
   */
  Eliminator(int numVars, int[][] input, int numInput, boolean[] frozen, ProofOutput proof) {
    this(numVars, input, numInput, frozen, proof, 0, 0, 20, false);
  }

  /**
   * Creates an eliminator with a bound schedule and gates over the given clauses, which must have
   * at least two literals, no duplicate literal, no tautology, and no assigned literal.
   *
   * @param numVars the number of variables
   * @param input the clauses
   * @param numInput how many of them are used
   * @param frozen the variables that must not be eliminated
   * @param proof the DRAT output, or null
   * @param bound the bound to start from (see {@link #bound()})
   * @param maxBound the largest bound to raise to when a round eliminates nothing
   * @param resolventLimit the longest resolvent an elimination may add
   * @param useGates whether to resolve only gate clauses against the others when a variable is the
   *     output of a gate
   */
  Eliminator(
      int numVars,
      int[][] input,
      int numInput,
      boolean[] frozen,
      ProofOutput proof,
      int bound,
      int maxBound,
      int resolventLimit,
      boolean useGates) {
    this.useGates = useGates;
    this.numVars = numVars;
    this.frozen = frozen;
    this.bound = Math.min(bound, maxBound);
    this.maxBound = maxBound;
    this.resolventLimit = resolventLimit;
    touched = new boolean[numVars];
    this.proof = proof;
    clauses = new int[Math.max(16, numInput + numInput / 2)][];
    sigs = new long[clauses.length];
    queued = new boolean[clauses.length];
    occ = new int[2 * numVars][];
    occSize = new int[2 * numVars];
    value = new byte[2 * numVars];
    eliminated = new boolean[numVars];
    mark = new int[2 * numVars];
    int[] count = new int[2 * numVars];
    for (int i = 0; i < numInput; i++) {
      for (int l : input[i]) {
        count[l]++;
      }
    }
    // a literal of no clause shares the empty list: under LCG most literals (order and value atoms)
    // are in no clause of the root database, and a list of four for each of them took 3.9 GB on
    // MagicSquare-mdd-10 (XCSP 2023)
    for (int l = 0; l < 2 * numVars; l++) {
      occ[l] = count[l] == 0 ? NO_OCCURRENCES : new int[count[l]];
    }
    for (int i = 0; i < numInput; i++) {
      add(input[i]);
    }
  }

  /** Returns the effort spent so far, in literals and occurrences visited. */
  long effort() {
    return effort;
  }

  /**
   * Runs subsumption and elimination.
   *
   * @return false when the formula is unsatisfiable
   */
  boolean run() {
    for (int i = 0; i < numClauses; i++) {
      enqueue(i);
    }
    subsumeQueue();
    Arrays.fill(touched, true);
    while (!unsat && effort < EFFORT_LIMIT) {
      int[] vars = candidates();
      int before = numEliminated;
      for (int v : vars) {
        if (unsat || effort >= EFFORT_LIMIT) {
          break;
        }
        if (tryEliminate(v)) {
          subsumeQueue();
        }
      }
      if (numEliminated > before) {
        continue;
      }
      if (unsat || effort >= EFFORT_LIMIT || bound >= maxBound) {
        break;
      }
      // nothing left at this bound: raise it and try every variable again
      bound = nextBound(bound, maxBound);
      Arrays.fill(touched, true);
    }
    return !unsat;
  }

  /**
   * The bound after the given one in the schedule 0, 1, 2, 4, 8, 16, capped at maxBound.
   *
   * @param bound the bound
   * @param maxBound the cap
   * @return the next bound
   */
  static int nextBound(int bound, int maxBound) {
    for (int b : BOUNDS) {
      if (b > bound) {
        return Math.min(b, maxBound);
      }
    }
    return maxBound;
  }

  /** The number of eliminations that resolved only gate clauses against the others. */
  int numGateEliminations() {
    return numGateEliminations;
  }

  /** Whether the run tried every candidate within its effort limit. */
  boolean completed() {
    return !unsat && effort < EFFORT_LIMIT;
  }

  /** The bound reached, from which the next run starts. */
  int bound() {
    return bound;
  }

  /** The remaining clauses, units excluded. */
  int[][] clauses() {
    int n = 0;
    for (int i = 0; i < numClauses; i++) {
      if (clauses[i] != null) {
        n++;
      }
    }
    int[][] out = new int[n][];
    n = 0;
    for (int i = 0; i < numClauses; i++) {
      if (clauses[i] != null) {
        out[n++] = clauses[i];
      }
    }
    return out;
  }

  /** The units found. */
  int[] units() {
    return Arrays.copyOf(units, numUnits);
  }

  /** The eliminated variables. */
  boolean[] eliminated() {
    return eliminated;
  }

  /** The number of eliminated variables. */
  int numEliminated() {
    return numEliminated;
  }

  /** The extension stack: each clause with its eliminated literal first, then its size. */
  int[] stack() {
    return Arrays.copyOf(stack, stackSize);
  }

  /**
   * Completes a model of the simplified formula into a model of the original one.
   *
   * @param stack the extension stack
   * @param model the model by variable, changed in place
   */
  static void extend(int[] stack, boolean[] model) {
    int i = stack.length;
    while (i > 0) {
      int size = stack[i - 1];
      int start = i - 1 - size;
      boolean satisfied = false;
      for (int k = start; k < i - 1 && !satisfied; k++) {
        int l = stack[k];
        satisfied = model[l >> 1] == ((l & 1) == 0);
      }
      if (!satisfied) {
        int pivot = stack[start];
        model[pivot >> 1] = (pivot & 1) == 0;
      }
      i = start;
    }
  }

  // ------------------------------------------------------------------------------ occurrences

  private int add(int[] c) {
    if (numClauses == clauses.length) {
      int n = 2 * clauses.length;
      clauses = Arrays.copyOf(clauses, n);
      sigs = Arrays.copyOf(sigs, n);
      queued = Arrays.copyOf(queued, n);
    }
    int i = numClauses++;
    clauses[i] = c;
    sigs[i] = signature(c);
    for (int l : c) {
      addOcc(l, i);
    }
    return i;
  }

  private static long signature(int[] c) {
    long s = 0;
    for (int l : c) {
      s |= 1L << ((l >> 1) & 63);
    }
    return s;
  }

  private void addOcc(int l, int i) {
    touched[l >> 1] = true;
    int[] o = occ[l];
    if (occSize[l] == o.length) {
      o = Arrays.copyOf(o, Math.max(4, 2 * o.length));
      occ[l] = o;
    }
    o[occSize[l]++] = i;
  }

  private void removeOcc(int l, int i) {
    touched[l >> 1] = true;
    int[] o = occ[l];
    int n = occSize[l];
    effort += n;
    for (int k = 0; k < n; k++) {
      if (o[k] == i) {
        o[k] = o[n - 1];
        occSize[l] = n - 1;
        return;
      }
    }
  }

  /** Removes clause i, writing its deletion to the proof. */
  private void delete(int i) {
    int[] c = clauses[i];
    if (proof != null) {
      proof.delete(c, 0, c.length);
    }
    for (int l : c) {
      removeOcc(l, i);
    }
    clauses[i] = null;
  }

  private void enqueue(int i) {
    if (queued[i] || clauses[i].length > SUBSUME_LIMIT) {
      return;
    }
    if (queueSize == queue.length) {
      queue = Arrays.copyOf(queue, 2 * queue.length);
    }
    queue[queueSize++] = i;
    queued[i] = true;
  }

  // ------------------------------------------------------------------------------- subsumption

  private void subsumeQueue() {
    while (queueHead < queueSize && !unsat && effort < EFFORT_LIMIT) {
      int i = queue[queueHead++];
      queued[i] = false;
      if (clauses[i] != null) {
        subsume(i);
      }
      propagateUnits();
    }
    propagateUnits();
    for (int k = queueHead; k < queueSize; k++) {
      queued[queue[k]] = false;
    }
    queueHead = 0;
    queueSize = 0;
  }

  /** Removes the clauses that clause i subsumes and strengthens those it resolves into. */
  private void subsume(int i) {
    int[] c = clauses[i];
    int best = c[0];
    for (int l : c) {
      if (occSize[l] + occSize[l ^ 1] < occSize[best] + occSize[best ^ 1]) {
        best = l;
      }
    }
    newStamp();
    for (int l : c) {
      mark[l] = stamp;
    }
    for (int polarity = 0; polarity < 2; polarity++) {
      int l = best ^ polarity;
      // the scan of the occurrence list counts too: on long lists whose clauses the signatures
      // reject it is the whole cost (DiamondFree of XCSP 2022, millions of clauses of 5 literals
      // over 4,830 variables, scanned for hours under an effort that only counted compared clauses)
      effort += occSize[l];
      int[] list = Arrays.copyOf(occ[l], occSize[l]);
      for (int j : list) {
        if (j == i || clauses[j] == null || clauses[i] == null) {
          continue;
        }
        int[] d = clauses[j];
        if (d.length < c.length || (sigs[i] & ~sigs[j]) != 0) {
          continue;
        }
        effort += d.length;
        int same = 0;
        int flipped = -1;
        int flips = 0;
        for (int x : d) {
          if (mark[x] == stamp) {
            same++;
          } else if (mark[x ^ 1] == stamp) {
            flipped = x;
            flips++;
          }
        }
        if (same == c.length) {
          delete(j);
        } else if (same == c.length - 1 && flips == 1) {
          strengthen(j, flipped);
        }
      }
    }
  }

  /** Removes literal l from clause i. */
  private void strengthen(int i, int l) {
    int[] d = clauses[i];
    int[] s = new int[d.length - 1];
    int n = 0;
    for (int x : d) {
      if (x != l) {
        s[n++] = x;
      }
    }
    if (proof != null) {
      proof.add(s, 0, s.length);
      proof.delete(d, 0, d.length);
    }
    removeOcc(l, i);
    if (s.length == 1) {
      removeOcc(s[0], i);
      clauses[i] = null;
      unit(s[0]);
      return;
    }
    clauses[i] = s;
    sigs[i] = signature(s);
    enqueue(i);
  }

  private void unit(int l) {
    if (value[l] > 0) {
      return;
    }
    if (value[l] < 0) {
      unsat = true;
      return;
    }
    value[l] = 1;
    value[l ^ 1] = -1;
    if (numUnits == units.length) {
      units = Arrays.copyOf(units, 2 * units.length);
    }
    units[numUnits++] = l;
  }

  /** Removes the clauses satisfied by the units and the false literals from the others. */
  private void propagateUnits() {
    while (unitHead < numUnits && !unsat) {
      int l = units[unitHead++];
      while (occSize[l] > 0) {
        delete(occ[l][occSize[l] - 1]);
      }
      while (occSize[l ^ 1] > 0 && !unsat) {
        strengthen(occ[l ^ 1][occSize[l ^ 1] - 1], l ^ 1);
      }
    }
  }

  private void newStamp() {
    if (++stamp == Integer.MAX_VALUE) {
      Arrays.fill(mark, 0);
      stamp = 1;
    }
  }

  // ------------------------------------------------------------------------------- elimination

  /** The touched variables to try, fewest resolution pairs first; clears their marks. */
  private int[] candidates() {
    long[] keys = new long[numVars];
    int n = 0;
    for (int v = 0; v < numVars; v++) {
      if (!touched[v]) {
        continue;
      }
      touched[v] = false;
      int p = occSize[2 * v];
      int q = occSize[2 * v + 1];
      if (!frozen[v] && !eliminated[v] && value[2 * v] == 0 && p + q > 0) {
        keys[n++] = (long) p * q << 32 | v;
      }
    }
    Arrays.sort(keys, 0, n);
    int[] vars = new int[n];
    for (int i = 0; i < n; i++) {
      vars[i] = (int) keys[i];
    }
    return vars;
  }

  private boolean tryEliminate(int v) {
    int pos = 2 * v;
    int neg = pos + 1;
    if (value[pos] != 0 || occSize[pos] > OCC_LIMIT || occSize[neg] > OCC_LIMIT) {
      return false;
    }
    int np = occSize[pos];
    int nn = occSize[neg];
    if (np + nn == 0) {
      return false;
    }
    int[] ps = Arrays.copyOf(occ[pos], np);
    int[] ns = Arrays.copyOf(occ[neg], nn);
    // with a gate on v, only resolvents of a gate clause with a non-gate clause are needed: those
    // of two gate clauses are tautologies and those of two other clauses are implied (Een, Biere,
    // "Effective Preprocessing in SAT through Variable and Clause Elimination", SAT 2005)
    boolean[] gp = null;
    boolean[] gn = null;
    if (useGates) {
      GateExtractor.Gate g = gate(pos);
      if (g != null) {
        int[] defining = g.clauses.clone();
        Arrays.sort(defining);
        gp = new boolean[np];
        gn = new boolean[nn];
        for (int k = 0; k < np; k++) {
          gp[k] = Arrays.binarySearch(defining, ps[k]) >= 0;
        }
        for (int k = 0; k < nn; k++) {
          gn[k] = Arrays.binarySearch(defining, ns[k]) >= 0;
        }
      }
    }
    int resolvents = 0;
    for (int i = 0; i < np; i++) {
      for (int j = 0; j < nn; j++) {
        if (gp != null && gp[i] == gn[j]) {
          continue;
        }
        int size = resolventSize(clauses[ps[i]], clauses[ns[j]], v);
        if (size < 0) {
          continue;
        }
        if (size > resolventLimit || ++resolvents > np + nn + bound) {
          return false;
        }
      }
    }
    int[] found = new int[16];
    int numFound = 0;
    for (int i = 0; i < np; i++) {
      for (int j = 0; j < nn; j++) {
        if (gp != null && gp[i] == gn[j]) {
          continue;
        }
        int[] r = resolvent(clauses[ps[i]], clauses[ns[j]], v);
        if (r == null) {
          continue;
        }
        if (proof != null) {
          proof.add(r, 0, r.length);
        }
        if (r.length == 1) {
          if (numFound == found.length) {
            found = Arrays.copyOf(found, 2 * numFound);
          }
          found[numFound++] = r[0];
        } else {
          enqueue(add(r));
        }
      }
    }
    if (gp != null) {
      numGateEliminations++;
    }
    for (int a : ps) {
      save(clauses[a], pos);
      delete(a);
    }
    for (int b : ns) {
      save(clauses[b], neg);
      delete(b);
    }
    eliminated[v] = true;
    numEliminated++;
    for (int k = 0; k < numFound; k++) {
      unit(found[k]);
    }
    propagateUnits();
    return true;
  }

  /** A gate with output pos or its negation (an OR gate on pos), or null. */
  private GateExtractor.Gate gate(int pos) {
    if (gates == null || gatesOver != clauses) {
      gates = new GateExtractor(clauses, occ, occSize, numVars);
      gatesOver = clauses;
    }
    long before = gates.effort;
    GateExtractor.Gate g = gates.find(pos);
    if (g == null) {
      g = gates.find(pos ^ 1);
    }
    effort += gates.effort - before;
    return g;
  }

  /** Pushes clause c on the extension stack with its literal of the eliminated variable first. */
  private void save(int[] c, int pivot) {
    int need = c.length + 1;
    if (stackSize + need > stack.length) {
      stack = Arrays.copyOf(stack, Math.max(stackSize + need, 2 * stack.length));
    }
    stack[stackSize++] = pivot;
    for (int l : c) {
      if (l != pivot) {
        stack[stackSize++] = l;
      }
    }
    stack[stackSize++] = c.length;
  }

  /** The size of the resolvent of a (with v) and b (with not v), or -1 if it is a tautology. */
  private int resolventSize(int[] a, int[] b, int v) {
    effort += a.length + b.length;
    newStamp();
    for (int l : a) {
      mark[l] = stamp;
    }
    int size = a.length - 1;
    for (int l : b) {
      if (l >> 1 == v || mark[l] == stamp) {
        continue;
      }
      if (mark[l ^ 1] == stamp) {
        return -1;
      }
      size++;
    }
    return size;
  }

  private int[] resolvent(int[] a, int[] b, int v) {
    int size = resolventSize(a, b, v);
    if (size < 0) {
      return null;
    }
    int[] r = new int[size];
    int n = 0;
    for (int l : a) {
      if (l >> 1 != v) {
        r[n++] = l;
      }
    }
    for (int l : b) {
      if (l >> 1 != v && mark[l] != stamp) {
        r[n++] = l;
      }
    }
    return r;
  }
}
