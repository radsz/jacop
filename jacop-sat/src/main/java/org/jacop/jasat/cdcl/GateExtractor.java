/*
 * GateExtractor.java
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
 * Finds the clauses that define a literal as a gate of other literals: an equivalence, an AND gate
 * (an OR gate is the AND gate of the negated output), an if-then-else gate or an XOR gate, the gate
 * kinds of Kissat's gate extraction and of clausal congruence closure (Een and Biere, "Effective
 * Preprocessing in SAT through Variable and Clause Elimination", SAT 2005; Biere, Fazekas, Fleury
 * and Froleyks, "Clausal Congruence Closure", SAT 2024).
 *
 * <p>The clauses are given as in {@link Eliminator}: arrays of internal literals ({@code
 * 2*var+sign}), null for a deleted clause, with exact occurrence lists of clause indices per
 * literal. No clause holds an assigned literal, a duplicate literal or a tautology. The extractor
 * only reads them; it may be used again after the caller changed them.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class GateExtractor {

  /** The output is equivalent to its single input. */
  static final int EQUIV = 1;

  /** The output is the conjunction of its input literals. */
  static final int AND = 2;

  /** The output is the if-then-else of its inputs: condition, then literal, else literal. */
  static final int ITE = 3;

  /** The output is the exclusive or of its inputs, which are positive literals. */
  static final int XOR = 4;

  /** The largest number of inputs of an XOR gate looked for (2^k clauses define it). */
  static final int MAX_XOR_INPUTS = 4;

  // occurrence lists longer than this are not scanned for the ternary and XOR gates
  private static final int OCC_LIMIT = 1000;
  // the largest AND gate (number of inputs) looked for
  private static final int MAX_AND_INPUTS = 1000;

  /** A gate found by {@link #find}. */
  static final class Gate {

    /** EQUIV, AND, ITE or XOR. */
    final int kind;

    /** The output literal. */
    final int output;

    /**
     * The inputs: the literal of EQUIV; the literals of AND, sorted; condition, then and else
     * literal of ITE; the positive input literals of XOR, sorted.
     */
    final int[] inputs;

    /** The indices of the clauses that define the gate. */
    final int[] clauses;

    Gate(int kind, int output, int[] inputs, int[] clauses) {
      this.kind = kind;
      this.output = output;
      this.inputs = inputs;
      this.clauses = clauses;
    }

    @Override
    public String toString() {
      String[] names = {"?", "EQUIV", "AND", "ITE", "XOR"};
      return names[kind] + "(" + output + " <- " + Arrays.toString(inputs) + ")";
    }
  }

  private final int[][] clauses;
  private final int[][] occ;
  private final int[] occSize;
  // per literal: the stamp when it was marked, and the clause that marked it
  private final int[] mark;
  private final int[] markClause;
  private int stamp;

  /** Literals visited so far, a measure of the work done. */
  long effort;

  /**
   * Creates an extractor over clauses and their occurrence lists.
   *
   * @param clauses the clauses, null for a deleted one
   * @param occ per literal, the indices of the clauses holding it in the first occSize entries
   * @param occSize per literal, the length of its occurrence list
   * @param numVars the number of variables
   */
  GateExtractor(int[][] clauses, int[][] occ, int[] occSize, int numVars) {
    this.clauses = clauses;
    this.occ = occ;
    this.occSize = occSize;
    mark = new int[2 * numVars];
    markClause = new int[2 * numVars];
  }

  /**
   * Finds a gate with the given output literal: an equivalence, an AND gate, an ITE gate or an XOR
   * gate, tried in this order. An XOR gate is found on the output's variable, and its output is the
   * literal of that variable that equals the exclusive or of the positive inputs, which may be the
   * negation of {@code output}. For an OR gate, ask for the negated output.
   *
   * @param output the output literal
   * @return the gate, or null if none is found
   */
  Gate find(int output) {
    Gate g = findEquivalence(output);
    if (g == null) {
      g = findAnd(output);
    }
    if (g == null) {
      g = findIte(output);
    }
    if (g == null) {
      g = findXor(output);
    }
    return g;
  }

  /**
   * Finds the binary clauses (-o | a) and (o | -a).
   *
   * @param o the output literal
   * @return the gate o = a, or null
   */
  Gate findEquivalence(int o) {
    newStamp();
    int[] list = occ[o ^ 1];
    for (int k = 0; k < occSize[o ^ 1]; k++) {
      int[] c = clauses[list[k]];
      if (c.length == 2) {
        int a = c[0] == (o ^ 1) ? c[1] : c[0];
        mark[a] = stamp;
        markClause[a] = list[k];
      }
    }
    effort += occSize[o ^ 1];
    list = occ[o];
    for (int k = 0; k < occSize[o]; k++) {
      int[] c = clauses[list[k]];
      if (c.length == 2) {
        int b = c[0] == o ? c[1] : c[0];
        if (mark[b ^ 1] == stamp) {
          effort += k;
          return new Gate(EQUIV, o, new int[] {b ^ 1}, new int[] {markClause[b ^ 1], list[k]});
        }
      }
    }
    effort += occSize[o];
    return null;
  }

  /**
   * Finds the binary clauses (-o | a_i) and a clause (o | -a_1 | ... | -a_n) with n at least 2.
   *
   * @param o the output literal
   * @return the gate o = a_1 &amp; ... &amp; a_n, or null
   */
  Gate findAnd(int o) {
    newStamp();
    int[] list = occ[o ^ 1];
    int binaries = 0;
    for (int k = 0; k < occSize[o ^ 1]; k++) {
      int[] c = clauses[list[k]];
      if (c.length == 2) {
        int a = c[0] == (o ^ 1) ? c[1] : c[0];
        mark[a] = stamp;
        markClause[a] = list[k];
        binaries++;
      }
    }
    effort += occSize[o ^ 1];
    if (binaries < 2) {
      return null;
    }
    list = occ[o];
    for (int k = 0; k < occSize[o]; k++) {
      int[] c = clauses[list[k]];
      if (c.length < 3 || c.length - 1 > binaries || c.length - 1 > MAX_AND_INPUTS) {
        continue;
      }
      effort += c.length;
      boolean all = true;
      for (int i = 0; i < c.length && all; i++) {
        all = c[i] == o || mark[c[i] ^ 1] == stamp;
      }
      if (all) {
        int[] inputs = new int[c.length - 1];
        int[] defining = new int[c.length];
        int n = 0;
        for (int l : c) {
          if (l != o) {
            inputs[n] = l ^ 1;
            defining[n++] = markClause[l ^ 1];
          }
        }
        defining[n] = list[k];
        Arrays.sort(inputs);
        return new Gate(AND, o, inputs, defining);
      }
    }
    return null;
  }

  /**
   * Finds the ternary clauses (-o | -c | t), (-o | c | e), (o | -c | -t) and (o | c | -e) where the
   * variables of o, c, t and e differ.
   *
   * @param o the output literal
   * @return the gate o = c ? t : e with c a positive literal, or null
   */
  Gate findIte(int o) {
    int n = occSize[o ^ 1];
    if (n < 2 || n > OCC_LIMIT || occSize[o] < 2 || occSize[o] > OCC_LIMIT) {
      return null;
    }
    // the pairs (literal, clause) of the ternary clauses with -o, sorted by literal: a clause with
    // -c
    // and one with c sit in the adjacent groups of 2c and 2c + 1, so only such pairs are tried
    int[] list = ternaries(o ^ 1);
    long[] keys = new long[2 * list.length];
    int m = 0;
    for (int i = 0; i < list.length; i++) {
      for (int l : clauses[list[i]]) {
        if (l != (o ^ 1)) {
          keys[m++] = (long) l << 32 | i;
        }
      }
    }
    Arrays.sort(keys, 0, m);
    effort += m;
    int p = 0;
    while (p < m) {
      int c = (int) (keys[p] >>> 32);
      int q = p;
      while (q < m && (int) (keys[q] >>> 32) == c) {
        q++;
      }
      if ((c & 1) != 0) {
        p = q;
        continue;
      }
      // keys[p..q) hold c; keys[q..r) hold -c
      int r = q;
      while (r < m && (int) (keys[r] >>> 32) == (c ^ 1)) {
        r++;
      }
      for (int i = q; i < r; i++) {
        int ci = list[(int) keys[i]];
        int t = other(clauses[ci], o ^ 1, c ^ 1);
        for (int j = p; j < q; j++) {
          int cj = list[(int) keys[j]];
          int e = other(clauses[cj], o ^ 1, c);
          effort++;
          if (t >> 1 == e >> 1) {
            continue;
          }
          int k1 = ternary(o, c ^ 1, t ^ 1);
          if (k1 < 0) {
            break;
          }
          int k2 = ternary(o, c, e ^ 1);
          if (k2 < 0) {
            continue;
          }
          return new Gate(ITE, o, new int[] {c, t, e}, new int[] {ci, cj, k1, k2});
        }
      }
      p = r;
    }
    return null;
  }

  /**
   * Finds 2^k clauses of k + 1 literals over the variable of o and k other variables, with the same
   * parity of negative literals, k from 2 to {@link #MAX_XOR_INPUTS}.
   *
   * @param o a literal of the output variable
   * @return the gate, or null
   */
  Gate findXor(int o) {
    int pos = o & ~1;
    if (occSize[pos] > OCC_LIMIT || occSize[pos + 1] > OCC_LIMIT) {
      return null;
    }
    if (occSize[pos] + occSize[pos + 1] < 4) {
      return null;
    }
    // the variable sets of the candidate clauses of both signs, sorted, so that a base clause is
    // only tried when its variable set has enough clauses, and each set only once (the scan of
    // both occurrence lists per base clause took a sixth of the run on Hamming CNFs)
    long[] sets = variableSets(pos);
    boolean[] tried = new boolean[sets.length];
    int[] list = occ[o];
    for (int k = 0; k < occSize[o]; k++) {
      int[] base = clauses[list[k]];
      int size = base.length;
      if (size < 3 || size > MAX_XOR_INPUTS + 1) {
        continue;
      }
      int need = 1 << (size - 1);
      long key = variableSet(base);
      int at = Arrays.binarySearch(sets, key);
      int first = at < 0 ? 0 : runStart(sets, at);
      if (at < 0 || tried[first] || runEnd(sets, at) - first < need) {
        continue;
      }
      Gate g = xorOn(base, pos, need);
      if (g != null) {
        return g;
      }
      // this set has no XOR on it: the other clauses over it need not be tried
      tried[first] = true;
    }
    return null;
  }

  /** The keys of the variable sets of the clauses of 3 to MAX_XOR_INPUTS + 1 literals on pos. */
  private long[] variableSets(int pos) {
    long[] keys = new long[occSize[pos] + occSize[pos + 1]];
    int n = 0;
    for (int side = 0; side < 2; side++) {
      int[] list = occ[pos + side];
      for (int k = 0; k < occSize[pos + side]; k++) {
        int[] c = clauses[list[k]];
        effort++;
        if (c.length >= 3 && c.length <= MAX_XOR_INPUTS + 1) {
          keys[n++] = variableSet(c);
        }
      }
    }
    keys = Arrays.copyOf(keys, n);
    Arrays.sort(keys);
    return keys;
  }

  /**
   * A key of the variables of a clause, its size and the parity of its negative literals, which all
   * clauses of one XOR share; different sets may share a key, which only costs a needless try.
   */
  private static long variableSet(int[] c) {
    long key = c.length;
    int parity = 0;
    for (int l : c) {
      long z = ((l >>> 1) + 1) * 0x9E3779B97F4A7C15L;
      key += z ^ (z >>> 29);
      parity ^= l & 1;
    }
    return (key << 1 | parity) & Long.MAX_VALUE;
  }

  /** The first position of the keys equal to the one at position at of the sorted keys. */
  private static int runStart(long[] keys, int at) {
    int lo = at;
    while (lo > 0 && keys[lo - 1] == keys[at]) {
      lo--;
    }
    return lo;
  }

  /** The position after the last key equal to the one at position at of the sorted keys. */
  private static int runEnd(long[] keys, int at) {
    int hi = at + 1;
    while (hi < keys.length && keys[hi] == keys[at]) {
      hi++;
    }
    return hi;
  }

  // the XOR gate on the variables of base, if all its 2^(size-1) clauses are there
  private Gate xorOn(int[] base, int pos, int need) {
    int size = base.length;
    // the variables of base, output variable first; marks give each its bit
    int[] vars = new int[size];
    vars[0] = pos;
    int nv = 1;
    newStamp();
    mark[pos] = stamp;
    markClause[pos] = 0;
    for (int l : base) {
      int p = l & ~1;
      if (p != pos) {
        mark[p] = stamp;
        markClause[p] = nv;
        vars[nv++] = p;
      }
    }
    int parity = 0;
    for (int l : base) {
      parity ^= l & 1;
    }
    int[] found = new int[need];
    int numFound = 0;
    boolean[] seen = new boolean[1 << size];
    for (int side = 0; side < 2; side++) {
      int[] list = occ[pos + side];
      for (int k = 0; k < occSize[pos + side]; k++) {
        int[] c = clauses[list[k]];
        effort++;
        if (c.length != size) {
          continue;
        }
        int pattern = 0;
        int par = 0;
        boolean match = true;
        for (int i = 0; i < size && match; i++) {
          int p = c[i] & ~1;
          match = mark[p] == stamp;
          pattern |= (c[i] & 1) << markClause[p];
          par ^= c[i] & 1;
        }
        if (!match || par != parity || seen[pattern]) {
          continue;
        }
        seen[pattern] = true;
        found[numFound++] = list[k];
        if (numFound == need) {
          // the clauses forbid the assignments whose number of true variables has the parity
          // of their negative literals: x_out ^ inputs = 1 ^ parity
          int[] inputs = Arrays.copyOfRange(vars, 1, size);
          Arrays.sort(inputs);
          int output = parity == 1 ? pos : pos + 1;
          return new Gate(XOR, output, inputs, found);
        }
      }
    }
    return null;
  }

  // the literal of a ternary clause besides a and b
  private static int other(int[] c, int a, int b) {
    for (int l : c) {
      if (l != a && l != b) {
        return l;
      }
    }
    return -1;
  }

  // the index of a ternary clause with literals a, b and c (in any order), or -1
  // the ternary clauses with literal l
  private int[] ternaries(int l) {
    int[] list = occ[l];
    int count = 0;
    for (int k = 0; k < occSize[l]; k++) {
      if (clauses[list[k]].length == 3) {
        count++;
      }
    }
    effort += occSize[l];
    int[] result = new int[count];
    count = 0;
    for (int k = 0; k < occSize[l]; k++) {
      if (clauses[list[k]].length == 3) {
        result[count++] = list[k];
      }
    }
    return result;
  }

  private int ternary(int a, int b, int c) {
    int best = a;
    if (occSize[b] < occSize[best]) {
      best = b;
    }
    if (occSize[c] < occSize[best]) {
      best = c;
    }
    int[] list = occ[best];
    for (int k = 0; k < occSize[best]; k++) {
      int[] d = clauses[list[k]];
      effort++;
      if (d.length == 3 && contains(d, a) && contains(d, b) && contains(d, c)) {
        return list[k];
      }
    }
    return -1;
  }

  private static boolean contains(int[] c, int l) {
    for (int x : c) {
      if (x == l) {
        return true;
      }
    }
    return false;
  }

  private void newStamp() {
    if (++stamp == Integer.MAX_VALUE) {
      Arrays.fill(mark, 0);
      stamp = 1;
    }
  }
}
