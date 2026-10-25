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
 * <p>A variable is eliminated when the non-tautological resolvents on it are no more than the
 * clauses they replace and none is longer than {@link #RESOLVENT_LIMIT}. The removed clauses go on
 * an extension stack, from which {@link #extend} completes a model of the simplified formula.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class Eliminator {

  // the longest resolvent an elimination may add
  private static final int RESOLVENT_LIMIT = 20;
  // variables with more occurrences in one polarity are not tried
  private static final int OCC_LIMIT = 1000;
  // clauses longer than this are not used to subsume others
  private static final int SUBSUME_LIMIT = 100;
  // effort (literals visited) allowed in one run
  private static final long EFFORT_LIMIT = 300_000_000L;

  private final int numVars;
  private final boolean[] frozen;
  private final DratWriter proof;

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
   * Creates an eliminator over the given clauses, which must have at least two literals, no
   * duplicate literal, no tautology, and no assigned literal.
   *
   * @param numVars the number of variables
   * @param input the clauses
   * @param numInput how many of them are used
   * @param frozen the variables that must not be eliminated
   * @param proof the DRAT output, or null
   */
  Eliminator(int numVars, int[][] input, int numInput, boolean[] frozen, DratWriter proof) {
    this.numVars = numVars;
    this.frozen = frozen;
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
    for (int l = 0; l < 2 * numVars; l++) {
      occ[l] = new int[Math.max(4, count[l])];
    }
    for (int i = 0; i < numInput; i++) {
      add(input[i]);
    }
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
    for (int round = 0; round < 3 && !unsat && effort < EFFORT_LIMIT; round++) {
      int before = numEliminated;
      for (int v : candidates()) {
        if (unsat || effort >= EFFORT_LIMIT) {
          break;
        }
        if (tryEliminate(v)) {
          subsumeQueue();
        }
      }
      if (numEliminated == before) {
        break;
      }
    }
    return !unsat;
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
    int[] o = occ[l];
    if (occSize[l] == o.length) {
      o = Arrays.copyOf(o, 2 * o.length);
      occ[l] = o;
    }
    o[occSize[l]++] = i;
  }

  private void removeOcc(int l, int i) {
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

  /** The variables to try, fewest resolution pairs first. */
  private int[] candidates() {
    long[] keys = new long[numVars];
    int n = 0;
    for (int v = 0; v < numVars; v++) {
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
    int resolvents = 0;
    for (int a : ps) {
      for (int b : ns) {
        int size = resolventSize(clauses[a], clauses[b], v);
        if (size < 0) {
          continue;
        }
        if (size > RESOLVENT_LIMIT || ++resolvents > np + nn) {
          return false;
        }
      }
    }
    int[] found = new int[16];
    int numFound = 0;
    for (int a : ps) {
      for (int b : ns) {
        int[] r = resolvent(clauses[a], clauses[b], v);
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
