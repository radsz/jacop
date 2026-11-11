/*
 * SubproblemCensus.java
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
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.search;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Assignment;
import org.jacop.constraints.ChannelOrder;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;

/**
 * Measurement only: counts search nodes whose remaining subproblem was met before, after Chu,
 * Garcia de la Banda and Stuckey, "Automatically exploiting subproblem equivalence in constraint
 * programming", CPAIOR 2010, and "Exploiting subproblem dominance in constraint programming",
 * Constraints 17(1), 2012. Nothing is pruned.
 *
 * <p>The key of a node, taken at the fixpoint before its decision, hashes the domains of the
 * unfixed variables of the model's constraints and the projection of each constraint that still has
 * an unfixed variable: the fixed partial sum of a linear constraint, the set of used values of an
 * alldifferent, whether a clause of the SAT solver is satisfied, and for any other constraint the
 * values of its fixed variables (exact, so never more repeats than the true projection). The
 * objective variable's domain is left out of the key and kept beside it: a node repeats a stored
 * one only when its objective domain lies inside the stored one.
 *
 * <p>Two counts. "Done": the key belongs to a node whose subtree was explored to the end (depth
 * first search without cut-offs) or refuted (LCG: a conflict at the node's own decision level), so
 * a cache would fail the node soundly. "Seen": the key belongs to any earlier node off the current
 * path, an upper bound for LCG, whose search leaves subtrees by backjumps and restarts. For each,
 * the nodes inside the subtree of an outermost repeated node are the nodes a cache would save.
 *
 * <p>Turned on by the system property {@code jacop.census=true}; prints one line per engine to
 * standard error at exit.
 */
public final class SubproblemCensus {

  /** Whether the census runs (system property {@code jacop.census}). */
  public static final boolean ON = Boolean.getBoolean("jacop.census");

  /**
   * Check of the keys only (system property {@code jacop.census.prune}): depth first search fails
   * the nodes that repeat an explored one, so its result can be compared with a run without it.
   */
  public static final boolean PRUNE = Boolean.getBoolean("jacop.census.prune");

  private static final Map<String, SubproblemCensus> ALL = new LinkedHashMap<>();

  static {
    if (ON) {
      Runtime.getRuntime().addShutdownHook(new Thread(SubproblemCensus::printAll));
    }
  }

  /**
   * Returns the census of an engine, made at the first call.
   *
   * @param engine the engine's name, for example "dfs" or "lcg"
   * @return the census
   */
  public static synchronized SubproblemCensus of(String engine) {
    return ALL.computeIfAbsent(engine, SubproblemCensus::new);
  }

  private static synchronized void printAll() {
    for (SubproblemCensus c : ALL.values()) {
      System.err.println(c.report());
    }
    System.err.flush();
  }

  private static final int LINEAR = 0;
  private static final int ALLDIFF = 1;
  private static final int GENERIC = 2;
  private static final int ASSIGNMENT = 3;

  private final String engine;
  private boolean ready;

  // the model
  private int[] kind;
  private Var[][] scope;
  private long[][] weight;
  private SatisfiedPresent[] check;
  // whether the constraint, once a single variable of it is unfixed, leaves no more than that
  // variable's domain says: its propagator removes every value without support
  private boolean[] absorbed;
  private int[] split;
  private IntVar[][] clausePos;
  private IntVar[][] clauseNeg;
  private Var[] vars;
  private IntVar objective;
  private int linearCount;
  private int alldiffCount;
  private int genericCount;

  // the open nodes, innermost last
  private long[] stackH1 = new long[64];
  private long[] stackH2 = new long[64];
  private long[] stackObj = new long[64];
  private int[] stackLevel = new int[64];
  private boolean[] stackComplete = new boolean[64];
  private int size;
  // the position of the outermost open repeated node, or -1
  private int doneHitAt = -1;
  private int seenHitAt = -1;

  private final KeyTable done = new KeyTable();
  private final KeyTable seen = new KeyTable();

  // counts
  private long nodes;
  private long doneHits;
  private long doneSaved;
  private long seenHits;
  private long seenSaved;
  private long recorded;
  private long keyNanos;
  private int maxSize;

  private SubproblemCensus(String engine) {
    this.engine = engine;
  }

  /**
   * Whether the model was taken.
   *
   * @return true after {@link #init}
   */
  public boolean ready() {
    return ready;
  }

  /**
   * Takes the model: the constraints of the store (not those marked implied), the given extra
   * constraints, and clauses kept outside the store.
   *
   * @param store the store
   * @param extra constraints not in the store, or null
   * @param clauses clauses as pairs {positive, negative} of 0/1 variables, or null
   * @param objective the variable the search minimises, or null
   */
  public void init(
      Store store, Iterable<Constraint> extra, List<IntVar[][]> clauses, IntVar objective) {
    if (ready) {
      return;
    }
    ready = true;
    this.objective = objective;
    Set<Constraint> cs = new LinkedHashSet<>(store.getConstraints());
    cs.addAll(store.unlistedConstraints());
    if (extra != null) {
      for (Constraint c : extra) {
        cs.add(c);
      }
    }
    List<Constraint> model = new ArrayList<>();
    for (Constraint c : cs) {
      // LP relaxations are implied by the rows they relax; a channel's state at a fixpoint is
      // given by the domain of its integer variable
      String name = c.getClass().getName();
      if (!store.isImplied(c)
          && !name.startsWith("org.jacop.constraints.lp.")
          && !(c instanceof ChannelReif)
          && !(c instanceof ChannelOrder)) {
        model.add(c);
      }
    }
    int n = model.size();
    this.model = model.toArray(new Constraint[0]);
    kind = new int[n];
    scope = new Var[n][];
    weight = new long[n][];
    check = new SatisfiedPresent[n];
    absorbed = new boolean[n];
    split = new int[n];
    Map<Var, Boolean> all = new IdentityHashMap<>();
    for (int k = 0; k < n; k++) {
      Constraint c = model.get(k);
      LinearForm f = linearForm(c);
      absorbed[k] = absorbs(c);
      check[k] = c instanceof SatisfiedPresent sp ? sp : null;
      IntVar[][] xd = c instanceof Assignment ? assignmentArrays(c) : null;
      if (xd != null) {
        kind[k] = ASSIGNMENT;
        split[k] = xd[0].length;
        Var[] both = new Var[xd[0].length + xd[1].length];
        System.arraycopy(xd[0], 0, both, 0, xd[0].length);
        System.arraycopy(xd[1], 0, both, xd[0].length, xd[1].length);
        scope[k] = both;
        alldiffCount++;
      } else if (f != null) {
        kind[k] = LINEAR;
        scope[k] = f.vars();
        weight[k] = f.weights();
        linearCount++;
      } else {
        kind[k] = c instanceof Alldifferent || c instanceof Alldistinct ? ALLDIFF : GENERIC;
        if (kind[k] == ALLDIFF) {
          alldiffCount++;
        } else {
          genericCount++;
        }
        scope[k] = c.arguments().toArray(new Var[0]);
      }
      for (Var v : scope[k]) {
        all.put(v, Boolean.TRUE);
      }
    }
    int m = clauses == null ? 0 : clauses.size();
    clausePos = new IntVar[m][];
    clauseNeg = new IntVar[m][];
    for (int k = 0; k < m; k++) {
      clausePos[k] = clauses.get(k)[0];
      clauseNeg[k] = clauses.get(k)[1];
      for (Var v : clausePos[k]) {
        all.put(v, Boolean.TRUE);
      }
      for (Var v : clauseNeg[k]) {
        all.put(v, Boolean.TRUE);
      }
    }
    if (objective != null) {
      all.remove(objective);
    }
    vars = all.keySet().toArray(new Var[0]);
  }

  private static IntVar[][] assignmentArrays(Constraint c) {
    try {
      java.lang.reflect.Field fx = Assignment.class.getDeclaredField("x");
      java.lang.reflect.Field fd = Assignment.class.getDeclaredField("d");
      fx.setAccessible(true);
      fd.setAccessible(true);
      return new IntVar[][] {(IntVar[]) fx.get(c), (IntVar[]) fd.get(c)};
    } catch (ReflectiveOperationException | RuntimeException _) {
      return null;
    }
  }

  private boolean entailed(int k) {
    SatisfiedPresent sp = check[k];
    if (sp == null) {
      return false;
    }
    try {
      return sp.satisfied();
    } catch (RuntimeException _) {
      return false;
    }
  }

  private static LinearForm linearForm(Constraint c) {
    try {
      if (c instanceof LinearExplainable le) {
        return le.linearForm();
      }
      java.lang.reflect.Method m = c.getClass().getMethod("linearForm");
      return m.getReturnType() == LinearForm.class ? (LinearForm) m.invoke(c) : null;
    } catch (ReflectiveOperationException | RuntimeException _) {
      return null;
    }
  }

  private static boolean absorbs(Constraint c) {
    String name = c.getClass().getName();
    return c instanceof PrimitiveConstraint
        || name.startsWith("org.jacop.constraints.table.")
        || name.startsWith("org.jacop.constraints.ExtensionalSupport")
        || name.startsWith("org.jacop.constraints.Element");
  }

  // ------------------------------------------------------------------------------------- keys

  private long h1;
  private long h2;

  private void feed(long x) {
    if (category == skip) {
      return;
    }
    h1 = (h1 ^ mix(x)) * 0x9E3779B97F4A7C15L;
    h2 = Long.rotateLeft(h2 + mix(x ^ 0x5DEECE66DL), 27) * 0xC2B2AE3D27D4EB4FL;
  }

  private static long mix(long z) {
    z = (z ^ (z >>> 33)) * 0xff51afd7ed558ccdL;
    z = (z ^ (z >>> 33)) * 0xc4ceb9fe1a85ec53L;
    return z ^ (z >>> 33);
  }

  private static long mix2(long z) {
    z = (z ^ (z >>> 30)) * 0xbf58476d1ce4e5b9L;
    z = (z ^ (z >>> 27)) * 0x94d049bb133111ebL;
    return z ^ (z >>> 31);
  }

  // diagnosis: the key without one category of parts (domains, linear, alldifferent, other
  // constraints, clauses), set by the system property jacop.census.debug
  private static final boolean DEBUG = Boolean.getBoolean("jacop.census.debug");
  private int category;
  private int skip = -1;
  private final KeyTable[] without = new KeyTable[5];
  private final long[] withoutHits = new long[5];
  private final Map<String, Long> oneOpen = new java.util.TreeMap<>();
  private Constraint[] model;

  private void diagnose() {
    for (int c = 0; c < 5; c++) {
      skip = c;
      key();
      if (without[c] == null) {
        without[c] = new KeyTable();
      }
      if (without[c].get(h1, h2) != KeyTable.ABSENT) {
        withoutHits[c]++;
      } else {
        without[c].put(h1, h2, 0);
      }
    }
    skip = -1;
  }

  private void key() {
    h1 = 0x243F6A8885A308D3L;
    h2 = 0x13198A2E03707344L;
    category = 0;
    for (int i = 0; i < vars.length; i++) {
      Var v = vars[i];
      if (v.singleton()) {
        continue;
      }
      feed(i);
      if (v instanceof IntVar x) {
        IntDomain d = x.dom();
        int min = d.min();
        int max = d.max();
        int sz = d.getSize();
        feed(((long) min << 32) ^ (max & 0xffffffffL));
        if (sz != max - min + 1) {
          feed(sz);
          int n = d.noIntervals();
          for (int k = 0; k < n; k++) {
            feed(((long) d.leftElement(k) << 32) ^ (d.rightElement(k) & 0xffffffffL));
          }
        }
      } else {
        feed(v.dom().toString().hashCode());
      }
    }
    for (int k = 0; k < kind.length; k++) {
      category = kind[k] == LINEAR ? 1 : kind[k] == GENERIC ? 3 : 2;
      project(k);
    }
    category = 4;
    for (int k = 0; k < clausePos.length; k++) {
      int state = clause(k);
      if (state >= 0) {
        feed(-1L - k);
        feed(state);
      }
    }
  }

  /** Returns -1 when the clause has no unfixed variable, otherwise 1 if satisfied, 0 if not. */
  private int clause(int k) {
    boolean open = false;
    boolean sat = false;
    for (IntVar x : clausePos[k]) {
      if (!x.singleton()) {
        open = true;
      } else if (x.value() == 1) {
        sat = true;
      }
    }
    for (IntVar x : clauseNeg[k]) {
      if (!x.singleton()) {
        open = true;
      } else if (x.value() == 0) {
        sat = true;
      }
    }
    return open ? (sat ? 1 : 0) : -1;
  }

  private void project(int k) {
    Var[] s = scope[k];
    if (kind[k] != ALLDIFF && kind[k] != ASSIGNMENT && open(s) && entailed(k)) {
      return;
    }
    switch (kind[k]) {
      case ASSIGNMENT -> {
        long s1 = 0;
        long s2 = 0;
        boolean open = false;
        for (int i = 0; i < s.length; i++) {
          IntVar x = (IntVar) s[i];
          if (!x.singleton()) {
            open = true;
          } else if (i < split[k]) {
            s1 += mix(x.value());
          } else {
            s2 += mix2(x.value());
          }
        }
        if (open) {
          feed(k);
          feed(s1);
          feed(s2);
        }
      }
      case LINEAR -> {
        long[] w = weight[k];
        long partial = 0;
        boolean open = false;
        for (int i = 0; i < s.length; i++) {
          IntVar x = (IntVar) s[i];
          if (x.singleton()) {
            partial += w[i] * x.value();
          } else {
            open = true;
          }
        }
        if (open) {
          feed(k);
          feed(partial);
        }
      }
      case ALLDIFF -> {
        int lo = Integer.MAX_VALUE;
        int hi = Integer.MIN_VALUE;
        for (Var v : s) {
          IntVar x = (IntVar) v;
          if (!x.singleton()) {
            lo = Math.min(lo, x.min());
            hi = Math.max(hi, x.max());
          }
        }
        if (lo <= hi) {
          long s1 = 0;
          long s2 = 0;
          for (Var v : s) {
            IntVar x = (IntVar) v;
            if (x.singleton() && x.value() >= lo && x.value() <= hi) {
              s1 += mix(x.value());
              s2 += mix2(x.value());
            }
          }
          feed(k);
          feed(s1);
          feed(s2);
        }
      }
      default -> {
        int unfixed = 0;
        for (Var v : s) {
          if (!v.singleton()) {
            unfixed++;
          }
        }
        if (unfixed == 1 && absorbed[k]) {
          return;
        }
        if (DEBUG && skip < 0) {
          if (unfixed > 0 && unfixed < s.length) {
            String name =
                model[k].getClass().getSimpleName()
                    + "/"
                    + s.length
                    + "/"
                    + unfixed
                    + (check[k] == null ? "/noSat" : "");
            oneOpen.merge(name, 1L, Long::sum);
          }
        }
        boolean open = false;
        for (Var v : s) {
          if (!v.singleton()) {
            open = true;
            break;
          }
        }
        if (open) {
          feed(k);
          for (int i = 0; i < s.length; i++) {
            Var v = s[i];
            if (v.singleton()) {
              feed(i);
              feed(v instanceof IntVar x ? x.value() : v.dom().toString().hashCode());
            }
          }
        }
      }
    }
  }

  private static boolean open(Var[] s) {
    for (Var v : s) {
      if (!v.singleton()) {
        return true;
      }
    }
    return false;
  }

  private long objectiveRange() {
    if (objective == null) {
      return range(Integer.MIN_VALUE, Integer.MAX_VALUE);
    }
    return range(objective.min(), objective.max());
  }

  private static long range(int lo, int hi) {
    return ((long) lo << 32) | (hi & 0xffffffffL);
  }

  private static boolean inside(long inner, long outer) {
    return (int) (inner >> 32) >= (int) (outer >> 32) && (int) inner <= (int) outer;
  }

  // ------------------------------------------------------------------------------------ events

  /**
   * A node at a fixpoint, before its decision.
   *
   * @param level the decision level of the node (LCG), or 0 (depth first search)
   * @return whether the node repeats one whose subtree was explored or refuted
   */
  public boolean enter(int level) {
    long t = System.nanoTime();
    if (DEBUG) {
      diagnose();
    }
    key();
    long k1 = h1;
    long k2 = h2;
    long obj = objectiveRange();
    nodes++;
    if (size == stackH1.length) {
      grow();
    }
    long stored = done.get(k1, k2);
    boolean doneHit = stored != KeyTable.ABSENT && inside(obj, stored);
    boolean seenHit = seen.get(k1, k2) != KeyTable.ABSENT;
    if (doneHit) {
      doneHits++;
      if (doneHitAt < 0) {
        doneHitAt = size;
      }
    }
    if (seenHit) {
      seenHits++;
      if (seenHitAt < 0) {
        seenHitAt = size;
      }
    }
    if (doneHitAt >= 0) {
      doneSaved++;
    }
    if (seenHitAt >= 0) {
      seenSaved++;
    }
    stackH1[size] = k1;
    stackH2[size] = k2;
    stackObj[size] = obj;
    stackLevel[size] = level;
    stackComplete[size] = true;
    size++;
    maxSize = Math.max(maxSize, size);
    keyNanos += System.nanoTime() - t;
    return doneHit;
  }

  private void grow() {
    int n = stackH1.length * 2;
    stackH1 = java.util.Arrays.copyOf(stackH1, n);
    stackH2 = java.util.Arrays.copyOf(stackH2, n);
    stackObj = java.util.Arrays.copyOf(stackObj, n);
    stackLevel = java.util.Arrays.copyOf(stackLevel, n);
    stackComplete = java.util.Arrays.copyOf(stackComplete, n);
  }

  /**
   * Depth first search left the innermost open node.
   *
   * @param objectiveMax the largest objective value a better solution may have now, or {@link
   *     Integer#MAX_VALUE}
   */
  public void exit(int objectiveMax) {
    if (size == 0) {
      return;
    }
    size--;
    if (stackComplete[size]) {
      long obj = stackObj[size];
      int hi = Math.min((int) obj, objectiveMax);
      record(stackH1[size], stackH2[size], range((int) (obj >> 32), hi));
    }
    seen.put(stackH1[size], stackH2[size], 0);
    popped();
  }

  private void popped() {
    if (doneHitAt >= size) {
      doneHitAt = -1;
    }
    if (seenHitAt >= size) {
      seenHitAt = -1;
    }
  }

  private void record(long k1, long k2, long obj) {
    long old = done.get(k1, k2);
    if (old == KeyTable.ABSENT || (int) obj > (int) old) {
      done.put(k1, k2, obj);
      recorded++;
    }
  }

  /**
   * Depth first search stopped exploring part of the open nodes' subtrees (time-out, restart,
   * skipped branches, a solution that ends the search): none of them is complete.
   */
  public void cut() {
    for (int i = size - 1; i >= 0 && stackComplete[i]; i--) {
      stackComplete[i] = false;
    }
  }

  /**
   * LCG backjumps to a level; a conflict at the current level refutes the nodes taken at it.
   *
   * @param from the decision level before the backjump
   * @param to the decision level after it
   * @param conflict whether a conflict led to the backjump
   * @param objectiveMax the largest objective value a better solution may have now, or {@link
   *     Integer#MAX_VALUE}
   */
  public void backjump(int from, int to, boolean conflict, int objectiveMax) {
    if (conflict) {
      for (int i = size - 1; i >= 0 && stackLevel[i] >= from; i--) {
        long obj = stackObj[i];
        record(stackH1[i], stackH2[i], range((int) (obj >> 32), Math.min((int) obj, objectiveMax)));
      }
    }
    while (size > 0 && stackLevel[size - 1] > to) {
      size--;
      seen.put(stackH1[size], stackH2[size], 0);
    }
    popped();
  }

  private String report() {
    return String.format(
            "%%%% census engine=%s nodes=%d doneHits=%d doneSaved=%d seenHits=%d seenSaved=%d"
                + " recorded=%d keys=%d maxDepth=%d keyMs=%d vars=%d linear=%d alldiff=%d"
                + " generic=%d clauses=%d objective=%s",
            engine,
            nodes,
            doneHits,
            doneSaved,
            seenHits,
            seenSaved,
            recorded,
            seen.size(),
            maxSize,
            keyNanos / 1_000_000,
            vars == null ? 0 : vars.length,
            linearCount,
            alldiffCount,
            genericCount,
            clausePos == null ? 0 : clausePos.length,
            objective != null)
        + (DEBUG
            ? " without(dom,lin,alldiff,generic,clause)="
                + java.util.Arrays.toString(withoutHits)
                + " oneOpenNotEntailed="
                + oneOpen
            : "");
  }

  /** Open addressing table of 128-bit keys with a long value; full tables stop taking keys. */
  static final class KeyTable {
    static final long ABSENT = Long.MIN_VALUE;
    private static final int MAX_CAPACITY = 1 << 24;
    private long[] k1 = new long[1 << 12];
    private long[] k2 = new long[1 << 12];
    private long[] val = new long[1 << 12];
    private int count;

    int size() {
      return count;
    }

    private int slot(long a, long b) {
      int mask = k1.length - 1;
      int i = (int) mix(a ^ b) & mask;
      while (true) {
        if (k1[i] == 0 && k2[i] == 0) {
          return i;
        }
        if (k1[i] == a && k2[i] == b) {
          return i;
        }
        i = (i + 1) & mask;
      }
    }

    long get(long a, long b) {
      a |= 1;
      int i = slot(a, b);
      return k1[i] == 0 && k2[i] == 0 ? ABSENT : val[i];
    }

    void put(long a, long b, long v) {
      a |= 1;
      int i = slot(a, b);
      if (k1[i] == 0 && k2[i] == 0) {
        if (count * 4L >= k1.length * 3L) {
          if (k1.length >= MAX_CAPACITY) {
            return;
          }
          rehash();
          i = slot(a, b);
        }
        k1[i] = a;
        k2[i] = b;
        count++;
      }
      val[i] = v;
    }

    private void rehash() {
      long[] o1 = k1;
      long[] o2 = k2;
      long[] ov = val;
      k1 = new long[o1.length * 2];
      k2 = new long[o1.length * 2];
      val = new long[o1.length * 2];
      for (int j = 0; j < o1.length; j++) {
        if (o1[j] != 0 || o2[j] != 0) {
          int i = slot(o1[j], o2[j]);
          k1[i] = o1[j];
          k2[i] = o2[j];
          val[i] = ov[j];
        }
      }
    }
  }
}
