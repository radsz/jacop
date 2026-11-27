/*
 * DistinctOutputs.java
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

package org.jacop.fz;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.floats.core.FloatVar;
import org.jacop.search.DecisionListener;

/**
 * Prints each assignment of the output once under -a and -n N of a satisfaction model whose search
 * annotation decides variables that are not printed: the depth-first search would otherwise print
 * the same output again for each assignment of them that completes it.
 *
 * <p>Each solution has an exact key, the values of the printed variables in the order of the output
 * (an integer or Boolean packed in the bits of its root domain, a set by its value, a float by the
 * bounds of its box), and a solution whose key was printed before is neither printed nor counted. A
 * packed key costs its words and two ints of the hash table: 16 bytes for up to 64 bits of output.
 *
 * <p>In the depth-first search of the annotation and of the outputs ({@link #track}) it also
 * follows the decisions. Two leaves with the same output part at a decision on a variable that is
 * not printed, since a decision on a printed variable gives it different values on its two sides.
 * When every printed variable is fixed at such a decision, except the untouched outputs that the
 * search labels last and enumerates in full below each completion, all the leaves below it print
 * the same output: once one is found, its other branches are not searched, as the completion of the
 * variables that the annotation leaves out stops at its first solution. Otherwise only the leaves
 * below the highest such decision on the current path can repeat each other, so the keys are kept
 * while that decision is on the path, and none when there is none: a search that decides the
 * printed variables first keeps no key.
 */
final class DistinctOutputs<T extends Var> implements DecisionListener<T> {

  // the printed variables, in the order of the output
  private final Var[] printed;
  // the smallest value and the number of bits of each printed integer, -1 bits for another kind
  private final int[] low;
  private final int[] bits;
  // the words of a packed key, or -1 when some printed variable is not an integer
  private final int words;

  private final PackedKeys packed;
  private Set<String> texts;

  // the printed variables of the searched store, which decisions are on (null: no tracking)
  private Set<Var> printedInSearch;
  // those that must be fixed for every leaf below a decision to print the same output
  private Var[] determining;
  private int unfixedHint;

  // the level of the highest decision on the path on a variable that is not printed while some
  // printed variable is not fixed, and the number of that decision (-1 level: none)
  private int scopeLevel = -1;
  private long scope;
  private long scopes;
  // the scope whose keys are kept
  private long keptScope = -1;
  // the level of the highest decision on the path below which every leaf prints the same output,
  // and the leaves found before it (-1 level: none)
  private int sameLevel = -1;
  private long sameLeaves;
  // the leaves found, printed or not
  private long leaves;
  // the right branches not searched since all their leaves print an output printed already
  private long skipped;
  // the leaves not printed since their output was, and the most keys kept at once
  private long repeated;
  private long peakKeys;

  /**
   * Creates the keys of the given printed variables; their domains now bound their values.
   *
   * @param printed the printed variables, in the order of the output
   */
  DistinctOutputs(Var[] printed) {
    this.printed = printed;
    low = new int[printed.length];
    bits = new int[printed.length];
    long total = 0;
    boolean ints = true;
    for (int i = 0; i < printed.length; i++) {
      if (printed[i] instanceof IntVar x) {
        low[i] = x.min();
        long span = (long) x.max() - x.min();
        bits[i] = 64 - Long.numberOfLeadingZeros(span);
        total += bits[i];
      } else {
        bits[i] = -1;
        ints = false;
      }
    }
    words = ints ? (int) ((total + 63) / 64) : -1;
    packed = ints ? new PackedKeys(words) : null;
  }

  /**
   * Follows the decisions of the given searches, the annotation and the search of the outputs.
   *
   * @param searchedPrinted the printed variables of the searched store
   * @param last the untouched printed variables that the search labels last, below the completion
   */
  void track(Collection<Var> searchedPrinted, Set<Var> last) {
    printedInSearch = Collections.newSetFromMap(new IdentityHashMap<>());
    printedInSearch.addAll(searchedPrinted);
    determining = searchedPrinted.stream().filter(v -> !last.contains(v)).toArray(Var[]::new);
  }

  /** Whether the decisions are followed. */
  boolean tracking() {
    return printedInSearch != null;
  }

  /**
   * The statistics: the right branches not searched since their leaves print an output printed
   * already, the leaves not printed since their output was, and the most keys kept at once.
   *
   * @return the lines of the statistics
   */
  String statistics() {
    return "\n%%%mzn-stat: repeatedOutputBranches="
        + skipped
        + "\n%%%mzn-stat: repeatedOutputs="
        + repeated
        + "\n%%%mzn-stat: peakOutputKeys="
        + peakKeys;
  }

  /**
   * Takes a solution of the store and tells whether its output is printed for the first time. The
   * printed variables are fixed (but for the untouched outputs of the eliminated values).
   *
   * @param eliminated the values of printed variables that the store does not hold
   * @return true if the solution is to be printed and counted
   */
  boolean firstTime(Map<Var, Integer> eliminated) {
    leaves++;
    if (tracking()) {
      if (scopeLevel < 0) {
        // no earlier leaf shares a decision on a hidden variable with this one, and no later
        clear();
        return true;
      }
      if (scope != keptScope) {
        clear();
        keptScope = scope;
      }
    }
    long[] key = packed == null ? null : packedKey(eliminated);
    boolean first;
    if (key != null) {
      first = packed.add(key);
    } else {
      if (texts == null) {
        texts = new HashSet<>();
      }
      first = texts.add(textKey(eliminated));
    }
    if (!first) {
      repeated++;
    }
    peakKeys =
        Math.max(
            peakKeys, (packed == null ? 0 : packed.size()) + (texts == null ? 0 : texts.size()));
    return first;
  }

  private void clear() {
    if (packed != null) {
      packed.clear();
    }
    if (texts != null && !texts.isEmpty()) {
      texts = null;
    }
  }

  private long[] packedKey(Map<Var, Integer> eliminated) {
    long[] key = new long[words];
    int at = 0;
    for (int i = 0; i < printed.length; i++) {
      Integer e = eliminated.get(printed[i]);
      int value;
      if (e != null) {
        value = e;
      } else if (printed[i] instanceof IntVar x && x.singleton()) {
        value = x.value();
      } else {
        return null;
      }
      long offset = (long) value - low[i];
      if (offset < 0 || 64 - Long.numberOfLeadingZeros(offset) > bits[i]) {
        // outside the root domain (an eliminated value): the key is the text of the values
        return null;
      }
      for (int b = 0; b < bits[i]; b++, at++) {
        if ((offset >>> b & 1) != 0) {
          key[at >>> 6] |= 1L << (at & 63);
        }
      }
    }
    return key;
  }

  private String textKey(Map<Var, Integer> eliminated) {
    StringBuilder s = new StringBuilder();
    for (Var v : printed) {
      Integer e = eliminated.get(v);
      if (e != null) {
        s.append(e);
      } else if (v instanceof IntVar x && x.singleton()) {
        s.append(x.value());
      } else if (v instanceof FloatVar f) {
        // the box itself, not its print, which rounds
        s.append(Double.doubleToLongBits(f.min()))
            .append(':')
            .append(Double.doubleToLongBits(f.max()));
      } else {
        s.append(v.dom());
      }
      s.append(',');
    }
    return s.toString();
  }

  @Override
  public void leftDecision(T var, PrimitiveConstraint choice, int level) {
    // a decision at a level leaves the nodes of that level and below that the path had
    if (scopeLevel >= level) {
      scopeLevel = -1;
    }
    if (sameLevel >= level) {
      sameLevel = -1;
    }
    if (sameLevel >= 0 || onPrinted(var, choice)) {
      return;
    }
    if (determined()) {
      sameLevel = level;
      sameLeaves = leaves;
    } else if (scopeLevel < 0) {
      scopeLevel = level;
      scope = scopes++;
    }
  }

  @Override
  public boolean rightDecision(T var, PrimitiveConstraint choice, int level) {
    if (scopeLevel > level) {
      scopeLevel = -1;
    }
    if (sameLevel > level) {
      sameLevel = -1;
    }
    // below such a decision only the untouched outputs can be open, and their other values print
    // other outputs
    if (sameLevel >= 0 && leaves > sameLeaves && !onPrinted(var, choice)) {
      skipped++;
      return false;
    }
    return true;
  }

  // whether the two sides of the decision differ in a printed variable
  private boolean onPrinted(T var, PrimitiveConstraint choice) {
    if (var != null) {
      return printedInSearch.contains(var);
    }
    Set<Var> args = choice.arguments();
    return !args.isEmpty() && printedInSearch.containsAll(args);
  }

  // whether every printed variable that the leaves below can differ in is fixed
  private boolean determined() {
    int n = determining.length;
    for (int k = 0; k < n; k++) {
      int i = (unfixedHint + k) % n;
      Var v = determining[i];
      boolean fixed = v instanceof FloatVar f ? f.min() == f.max() : v.singleton();
      if (!fixed) {
        unfixedHint = i;
        return false;
      }
    }
    return true;
  }

  /**
   * A set of keys of a fixed number of words, by open addressing over one array of words: a key
   * costs its words and two ints of the table.
   */
  private static final class PackedKeys {
    private final int width;
    private long[] pool;
    private int size;
    // the index plus one of the key in each slot, 0 for an empty slot
    private int[] table;
    // a key of no word (every printed variable has one value) was added
    private boolean empty;

    PackedKeys(int width) {
      this.width = width;
      pool = new long[width * 16];
      table = new int[32];
    }

    boolean add(long[] key) {
      if (width == 0) {
        boolean added = !empty;
        empty = true;
        return added;
      }
      int mask = table.length - 1;
      int slot = hash(key, 0) & mask;
      while (table[slot] != 0) {
        if (same(table[slot] - 1, key)) {
          return false;
        }
        slot = (slot + 1) & mask;
      }
      if ((long) (size + 1) * width > pool.length) {
        pool = Arrays.copyOf(pool, (int) Math.min(Integer.MAX_VALUE - 8, 2L * pool.length));
      }
      System.arraycopy(key, 0, pool, size * width, width);
      table[slot] = ++size;
      if (2L * size > table.length) {
        rehash();
      }
      return true;
    }

    private boolean same(int index, long[] key) {
      int at = index * width;
      for (int i = 0; i < width; i++) {
        if (pool[at + i] != key[i]) {
          return false;
        }
      }
      return true;
    }

    private int hash(long[] words, int from) {
      long h = 0x9E3779B97F4A7C15L;
      for (int i = 0; i < width; i++) {
        h = (h ^ words[from + i]) * 0xBF58476D1CE4E5B9L;
        h ^= h >>> 31;
      }
      return (int) (h ^ h >>> 32);
    }

    private void rehash() {
      int[] grown = new int[table.length * 2];
      int mask = grown.length - 1;
      for (int index = 0; index < size; index++) {
        int slot = hash(pool, index * width) & mask;
        while (grown[slot] != 0) {
          slot = (slot + 1) & mask;
        }
        grown[slot] = index + 1;
      }
      table = grown;
    }

    int size() {
      return width == 0 ? (empty ? 1 : 0) : size;
    }

    void clear() {
      empty = false;
      if (size == 0) {
        return;
      }
      size = 0;
      if (table.length > 1024) {
        // a large table is given back: a scope of few keys would clear it again and again
        pool = new long[width * 16];
        table = new int[32];
      } else {
        Arrays.fill(table, 0);
      }
    }
  }
}
