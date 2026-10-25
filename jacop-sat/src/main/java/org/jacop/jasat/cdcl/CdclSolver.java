/*
 * CdclSolver.java
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
 * A CDCL SAT solver built on flat arrays.
 *
 * <p>Literals are internal integers {@code 2*var + sign} (sign 1 for a negative literal); the
 * public API takes DIMACS literals (variables from 1, negative for negation). Clauses of three or
 * more literals live in one {@code int[]} arena: a header (size, flags with LBD, activity, saved
 * search position) followed by the literals. Binary clauses are kept only in the watch lists. Every
 * watch entry is a pair (blocker literal, clause reference), with {@link #BINARY} as the reference
 * of a binary clause.
 *
 * <p>Search: first-UIP learning with recursive minimisation, LBD, EVSIDS with phase saving,
 * alternating focused mode (Glucose-style LBD restarts) and stable mode (Luby restarts), a
 * three-tier learnt clause database with periodic reduction, optional DRAT proof output, and
 * solving under assumptions.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class CdclSolver {

  /** Result of {@link #solve}: satisfiable. */
  public static final int SAT = 10;

  /** Result of {@link #solve}: unsatisfiable (under the assumptions, if any). */
  public static final int UNSAT = 20;

  /** Result of {@link #solve}: stopped by a limit or {@link #interrupt()}. */
  public static final int UNKNOWN = 0;

  static final int BINARY = -1;
  private static final int NO_CONFLICT = -1;
  private static final int BINARY_CONFLICT = -2;
  private static final int NO_REASON = -1;
  // reason of a unit clause asserted above level 0: true in every model, so analysis skips it
  private static final int UNIT_REASON = Integer.MIN_VALUE;

  // clause header
  private static final int SIZE = 0;
  private static final int META = 1;
  private static final int ACT = 2;
  private static final int POS = 3;
  private static final int HEADER = 4;

  // META bits; LBD in the bits from LBD_SHIFT
  private static final int LEARNT_FLAG = 1;
  private static final int DELETED = 2;
  private static final int USED = 4;
  private static final int VIVIFIED = 32;
  private static final int TIER_SHIFT = 3;
  private static final int TIER_MASK = 3 << TIER_SHIFT;
  private static final int LBD_SHIFT = 8;
  private static final int MAX_LBD = 255;

  private static final int TIER_CORE = 0;
  private static final int TIER_MID = 1;
  private static final int TIER_LOCAL = 2;
  private static final int CORE_LBD = 2;
  private static final int MID_LBD = 6;

  // --- variables and assignment
  private int numVars;
  private byte[] vals = new byte[0];
  private int[] level = new int[0];
  private int[] reason = new int[0];
  private byte[] savedSign = new byte[0];
  private byte[] targetSign = new byte[0];
  private byte[] bestSign = new byte[0];
  private int bestAssigned;
  private long nextRephase = REPHASE_INTERVAL;
  private int rephases;
  // local search in the rephasing cycle (Walker)
  private boolean walking = true;
  private long propagationsAtWalk;
  private int walks;
  long walkNanos;
  // chronological backtracking is used in this search (solve() without assumptions)
  private boolean chrono;
  // backtrack chronologically when a backjump would undo more levels than this; negative: never
  private int chronoLimit = 100;
  private int targetAssigned;
  private double[] activity = new double[0];
  private byte[] seen = new byte[0];
  private final VarHeap order = new VarHeap();

  private int[] trail = new int[0];
  // position of each assigned variable on the trail
  private int[] trailPos = new int[0];
  private int trailSize;
  private int qhead;
  private int[] trailLim = new int[16];
  private int decisionLevel;

  // --- clauses
  private int[] mem = new int[1 << 16];
  private int memSize;
  private int wasted;
  private int[] originals = new int[64];
  private int numOriginals;
  private int[] learnts = new int[64];
  private int numLearnts;
  private int[][] watches = new int[0][];
  private int[] watchSize = new int[0];
  private boolean ok = true;

  // --- conflict and analysis scratch
  private int conflictRef;
  private int conflictLit0;
  private int conflictLit1;
  private int[] learnt = new int[16];
  private int learntSize;
  private int[] stack = new int[16];
  private int[] toClear = new int[16];
  private int toClearSize;
  private int[] levelStamp = new int[16];
  private int stamp;
  // all-UIP shrinking (Fleury and Biere 2020): marks of one level's block, and the sort keys
  private boolean shrink = true;
  private int[] shrinkMark = new int[0];
  private int shrinkStamp;
  private long[] shrinkKeys = new long[16];

  // --- heuristics
  private double varInc = 1;
  private double varDecay = 0.8;
  private float claInc = 1;
  private static final float CLA_DECAY = 0.999f;
  private boolean stable;
  private long modeSwitchAt = 1000;
  private int modePhases;
  private long conflictsAtRestart;
  private int lubyIndex;
  private long lubyLimit;
  private final int[] lbdQueue = new int[50];
  private int lbdQueueSize;
  private int lbdQueueHead;
  private long lbdQueueSum;
  private long lbdSum;
  private final int[] trailQueue = new int[5000];
  private int trailQueueSize;
  private int trailQueueHead;
  private long trailQueueSum;
  private long nextReduce = 2000;
  private int reduceBase = 2000;
  private int reduceInc = 300;
  // vivification of learnt clauses at the next restart, after each reduction
  private boolean vivification = true;
  private boolean vivifyDue;
  private long propagationsAtVivify;
  private int[] vivifyLits = new int[16];
  private static final long REPHASE_INTERVAL = 1000;
  private int simplifyAssigns = -1;

  // --- driven by an external search (the CP solver): see "External search" below
  private int[] units = new int[16];
  private int numUnits;
  private int[] pending = new int[16];
  private int pendingSize;
  private int pendingLbd;
  private boolean hasPending;
  private boolean pendingAttached;
  private int pendingRef;
  private int lastAssumedLevel;
  private int[] originalBinaries = new int[16];
  private int numOriginalBinaries;

  // --- variable elimination before the first search (see Eliminator)
  private boolean elimination = true;
  private boolean eliminationTried;
  private boolean externalUsed;
  private boolean[] eliminatedVar = new boolean[0];
  private int numEliminated;
  private int[] extension = new int[0];

  // --- assumptions and model
  private int[] assumptions = new int[0];
  private int[] failed = new int[0];
  private boolean[] model = new boolean[0];

  // --- limits, proof, statistics
  private volatile boolean interrupted;
  private long deadline = Long.MAX_VALUE;
  private long conflictLimit = Long.MAX_VALUE;
  private DratWriter proof;

  /** Number of conflicts so far. */
  public long conflicts;

  /** Number of decisions so far. */
  public long decisions;

  /** Number of propagated literals so far. */
  public long propagations;

  /** Number of restarts so far. */
  public long restarts;

  /** Number of learnt clause database reductions so far. */
  public long reductions;

  /** Creates an empty solver. */
  public CdclSolver() {
    // arrays grow with the variables
  }

  // ----------------------------------------------------------------------------------------- API

  /**
   * Makes sure variables 1..n exist.
   *
   * @param n the largest DIMACS variable
   */
  public void ensureVars(int n) {
    if (n <= numVars) {
      return;
    }
    int cap = reason.length;
    if (n > cap) {
      int c = Math.max(n, 2 * cap);
      vals = Arrays.copyOf(vals, 2 * c);
      level = Arrays.copyOf(level, c);
      reason = Arrays.copyOf(reason, c);
      savedSign = Arrays.copyOf(savedSign, c);
      targetSign = Arrays.copyOf(targetSign, c);
      bestSign = Arrays.copyOf(bestSign, c);
      activity = Arrays.copyOf(activity, c);
      seen = Arrays.copyOf(seen, c);
      trail = Arrays.copyOf(trail, c);
      trailPos = Arrays.copyOf(trailPos, c);
      shrinkMark = Arrays.copyOf(shrinkMark, c);
      eliminatedVar = Arrays.copyOf(eliminatedVar, c);
      watches = Arrays.copyOf(watches, 2 * c);
      watchSize = Arrays.copyOf(watchSize, 2 * c);
    }
    order.grow(n, activity);
    Arrays.fill(reason, numVars, n, NO_REASON);
    // initial phase true (sign 0), as in CaDiCaL
    Arrays.fill(savedSign, numVars, n, (byte) 0);
    Arrays.fill(targetSign, numVars, n, (byte) -1);
    Arrays.fill(bestSign, numVars, n, (byte) 0);
    // the arrays hold at least n variables here (SonarCloud does not see it)
    for (int l = 2 * numVars; l < 2 * n; l++) {
      watches[l] = new int[4]; // NOSONAR
    }
    for (int v = numVars; v < n; v++) {
      order.insert(v);
    }
    numVars = n;
  }

  /**
   * Returns the number of variables.
   *
   * @return the largest DIMACS variable in use
   */
  public int numVars() {
    return numVars;
  }

  /**
   * Adds a clause of DIMACS literals. The solver must not be in the middle of a search.
   *
   * @param lits the literals (no terminating 0)
   * @return false when the formula is now known to be unsatisfiable
   */
  public boolean addClause(int... lits) {
    return addClause(lits, lits.length);
  }

  /**
   * Adds a clause given by the first {@code n} DIMACS literals of {@code lits}.
   *
   * @param lits the literals (no terminating 0)
   * @param n how many of them form the clause
   * @return false when the formula is now known to be unsatisfiable
   */
  public boolean addClause(int[] lits, int n) {
    if (!ok) {
      return false;
    }
    backtrack(0);
    int maxVar = 0;
    for (int i = 0; i < n; i++) {
      if (lits[i] == 0) {
        throw new IllegalArgumentException("0 is not a literal");
      }
      maxVar = Math.max(maxVar, Math.abs(lits[i]));
    }
    ensureVars(maxVar);
    for (int i = 0; i < n && numEliminated > 0; i++) {
      if (eliminatedVar[Math.abs(lits[i]) - 1]) {
        restoreEliminated();
      }
    }
    int[] c = new int[n];
    for (int i = 0; i < n; i++) {
      c[i] = toLit(lits[i]);
    }
    Arrays.sort(c);
    int size = 0;
    boolean changed = false;
    for (int i = 0; i < n; i++) {
      int l = c[i];
      if (vals[l] > 0 || (size > 0 && c[size - 1] == (l ^ 1))) {
        return true; // satisfied at level 0, or a tautology
      }
      if (vals[l] < 0 || (size > 0 && c[size - 1] == l)) {
        changed |= vals[l] < 0;
        continue;
      }
      c[size++] = l;
    }
    if (changed && proof != null) {
      proof.add(c, 0, size);
    }
    if (size == 0) {
      ok = false;
      return false;
    }
    if (size == 1) {
      assign(c[0], NO_REASON);
      if (propagate() != NO_CONFLICT) {
        ok = false;
        if (proof != null) {
          proof.add(c, 0, 0);
        }
      }
      return ok;
    }
    if (size == 2) {
      addOriginalBinary(c[0], c[1]);
      return true;
    }
    int ref = allocate(c, size, false, 0);
    originals = push(originals, numOriginals++, ref);
    attach(ref);
    return true;
  }

  /**
   * Solves the formula.
   *
   * @return {@link #SAT}, {@link #UNSAT} or {@link #UNKNOWN}
   */
  public int solve() {
    return solve(new int[0]);
  }

  /**
   * Solves the formula under assumptions (DIMACS literals that must hold in this call only).
   *
   * @param assumed the assumptions
   * @return {@link #SAT}, {@link #UNSAT} or {@link #UNKNOWN}; after UNSAT with assumptions, {@link
   *     #failedAssumptions()} gives a subset of them that is enough for unsatisfiability
   */
  public int solve(int... assumed) {
    failed = new int[0];
    if (!ok) {
      return UNSAT;
    }
    int maxVar = 0;
    for (int a : assumed) {
      maxVar = Math.max(maxVar, Math.abs(a));
    }
    ensureVars(maxVar);
    assumptions = new int[assumed.length];
    for (int i = 0; i < assumed.length; i++) {
      assumptions[i] = toLit(assumed[i]);
      if (eliminatedVar[assumptions[i] >> 1]) {
        restoreEliminated();
      }
    }
    interrupted = false;
    backtrack(0);
    if (elimination && !eliminationTried && conflicts == 0 && !externalUsed && numUnits == 0) {
      eliminationTried = true;
      if (!eliminate()) {
        return UNSAT;
      }
    }
    chrono = chronoLimit >= 0 && assumptions.length == 0;
    int result;
    try {
      result = search();
    } finally {
      chrono = false;
    }
    if (result == SAT) {
      model = new boolean[numVars];
      for (int v = 0; v < numVars; v++) {
        model[v] = vals[2 * v] > 0;
      }
      Eliminator.extend(extension, model);
    }
    backtrack(0);
    return result;
  }

  /**
   * Returns the value of a variable in the last model.
   *
   * @param variable a DIMACS variable
   * @return true when the variable is true in the model found by the last SAT answer
   */
  public boolean modelValue(int variable) {
    return model[variable - 1];
  }

  /**
   * Returns the failed assumptions of the last UNSAT answer under assumptions.
   *
   * @return DIMACS literals, a subset of the assumptions that together are unsatisfiable
   */
  public int[] failedAssumptions() {
    return failed.clone();
  }

  /**
   * Asks a running {@link #solve} to stop and return {@link #UNKNOWN}; safe from another thread.
   */
  public void interrupt() {
    interrupted = true;
  }

  /**
   * Sets a wall-clock deadline for {@link #solve}.
   *
   * @param nanoTime a {@link System#nanoTime()} value, or {@link Long#MAX_VALUE} for none
   */
  public void setDeadline(long nanoTime) {
    deadline = nanoTime;
  }

  /**
   * Limits the total number of conflicts.
   *
   * @param limit the conflict count at which {@link #solve} returns {@link #UNKNOWN}
   */
  public void setConflictLimit(long limit) {
    conflictLimit = limit;
  }

  /**
   * Sets when {@link #solve} backtracks chronologically (one level) instead of backjumping, as in
   * CaDiCaL. It is used only by solve calls without assumptions, never by the external-search
   * methods, which keep every literal at the level it was assigned at.
   *
   * @param limit the backjump length above which search backtracks one level, 0 for always, or a
   *     negative number for never (default 100)
   */
  public void setChronoLimit(int limit) {
    chronoLimit = limit;
  }

  /**
   * Turns all-UIP shrinking of learnt clauses on or off (on by default).
   *
   * @param on whether to shrink
   */
  public void setShrink(boolean on) {
    shrink = on;
  }

  /**
   * Turns bounded variable elimination and subsumption before the first search on or off (on by
   * default). It runs in the first {@link #solve} call, never once the external-search methods are
   * used, and keeps the variables of that call's assumptions. A clause or an assumption added later
   * on an eliminated variable brings all removed clauses back.
   *
   * @param on whether to eliminate
   */
  public void setElimination(boolean on) {
    elimination = on;
  }

  /**
   * Writes a DRAT proof of every derived and deleted clause. Set it before adding clauses.
   *
   * @param writer the proof output, or null for none
   */
  public void setProof(DratWriter writer) {
    proof = writer;
  }

  /**
   * Returns whether the formula is still possibly satisfiable.
   *
   * @return false once the empty clause has been derived
   */
  public boolean isOk() {
    return ok;
  }

  // ---------------------------------------------------------------------------------- literals

  private static int toLit(int dimacs) {
    return dimacs > 0 ? 2 * (dimacs - 1) : 2 * (-dimacs - 1) + 1;
  }

  static int toDimacs(int lit) {
    return (lit & 1) == 0 ? (lit >> 1) + 1 : -((lit >> 1) + 1);
  }

  private static int[] push(int[] a, int size, int x) {
    if (size == a.length) {
      a = Arrays.copyOf(a, 2 * a.length + 1);
    }
    a[size] = x;
    return a;
  }

  // ---------------------------------------------------------------------------------- clauses

  private int allocate(int[] lits, int size, boolean isLearnt, int lbd) {
    int need = HEADER + size;
    if (memSize + need > mem.length) {
      mem = Arrays.copyOf(mem, Math.max(memSize + need, mem.length + (mem.length >> 1)));
    }
    int ref = memSize;
    mem[ref + SIZE] = size;
    int tier = lbd <= CORE_LBD ? TIER_CORE : lbd <= MID_LBD ? TIER_MID : TIER_LOCAL;
    mem[ref + META] =
        (isLearnt ? LEARNT_FLAG : 0) | (tier << TIER_SHIFT) | (Math.min(lbd, MAX_LBD) << LBD_SHIFT);
    mem[ref + ACT] = Float.floatToRawIntBits(0f);
    mem[ref + POS] = 2;
    System.arraycopy(lits, 0, mem, ref + HEADER, size);
    memSize += need;
    return ref;
  }

  private void addWatch(int lit, int blocker, int ref) {
    int[] ws = watches[lit];
    int n = watchSize[lit];
    if (n + 2 > ws.length) {
      ws = Arrays.copyOf(ws, 2 * ws.length);
      watches[lit] = ws;
    }
    ws[n] = blocker;
    ws[n + 1] = ref;
    watchSize[lit] = n + 2;
  }

  private void attach(int ref) {
    int l0 = mem[ref + HEADER];
    int l1 = mem[ref + HEADER + 1];
    addWatch(l0, l1, ref);
    addWatch(l1, l0, ref);
  }

  private void addBinary(int a, int b) {
    addWatch(a, b, BINARY);
    addWatch(b, a, BINARY);
  }

  private boolean isLocked(int ref) {
    int l0 = mem[ref + HEADER];
    return vals[l0] > 0 && reason[l0 >> 1] == ref;
  }

  private void deleteClause(int ref) {
    int size = mem[ref + SIZE];
    if (proof != null) {
      proof.delete(mem, ref + HEADER, size);
    }
    mem[ref + META] |= DELETED;
    wasted += HEADER + size;
  }

  private static int lbdOf(int meta) {
    return meta >>> LBD_SHIFT;
  }

  private static int tierOf(int meta) {
    return (meta & TIER_MASK) >> TIER_SHIFT;
  }

  // ------------------------------------------------------------------------------ assignment

  private void assign(int lit, int why) {
    assignAt(lit, why, decisionLevel);
  }

  /** Assigns at a level that may be below the current one (chronological backtracking). */
  private void assignAt(int lit, int why, int lvl) {
    int v = lit >> 1;
    vals[lit] = 1;
    vals[lit ^ 1] = -1;
    level[v] = lvl;
    reason[v] = why;
    trailPos[v] = trailSize;
    trail[trailSize++] = lit;
  }

  private void newDecisionLevel() {
    if (decisionLevel == trailLim.length) {
      trailLim = Arrays.copyOf(trailLim, 2 * trailLim.length);
    }
    trailLim[decisionLevel++] = trailSize;
  }

  private void backtrack(int target) {
    if (decisionLevel <= target) {
      return;
    }
    int start = trailLim[target];
    int kept = start;
    for (int i = start; i < trailSize; i++) {
      int lit = trail[i];
      int v = lit >> 1;
      if (level[v] <= target) {
        // assigned out of order below the target level (chronological backtracking): stays
        trailPos[v] = kept;
        trail[kept++] = lit;
        continue;
      }
      vals[lit] = 0;
      vals[lit ^ 1] = 0;
      savedSign[v] = (byte) (lit & 1);
      order.insert(v);
    }
    trailSize = kept;
    qhead = start;
    decisionLevel = target;
    lastAssumedLevel = Math.min(lastAssumedLevel, target);
    reassertUnits();
  }

  // ----------------------------------------------------------------------------- propagation

  private int propagate() {
    int conflict = NO_CONFLICT;
    final byte[] vals = this.vals;
    final int[] mem = this.mem;
    while (qhead < trailSize) {
      int falseLit = trail[qhead++] ^ 1;
      propagations++;
      int[] ws = watches[falseLit];
      int n = watchSize[falseLit];
      int i = 0;
      int j = 0;
      while (i < n) {
        int blocker = ws[i];
        int ref = ws[i + 1];
        i += 2;
        int bv = vals[blocker];
        if (bv > 0) {
          ws[j++] = blocker;
          ws[j++] = ref;
          continue;
        }
        if (ref == BINARY) {
          ws[j++] = blocker;
          ws[j++] = ref;
          if (bv < 0) {
            conflict = BINARY_CONFLICT;
            conflictLit0 = blocker;
            conflictLit1 = falseLit;
            break;
          }
          if (chrono) {
            assignAt(blocker, -2 - falseLit, level[falseLit >> 1]);
          } else {
            assign(blocker, -2 - falseLit);
          }
          continue;
        }
        int lits = ref + HEADER;
        if (mem[lits] == falseLit) {
          mem[lits] = mem[lits + 1];
          mem[lits + 1] = falseLit;
        }
        int first = mem[lits];
        int fv = vals[first];
        if (first != blocker && fv > 0) {
          ws[j++] = first;
          ws[j++] = ref;
          continue;
        }
        int size = mem[ref + SIZE];
        int pos = mem[ref + POS];
        int k = pos;
        int found = -1;
        for (; k < size; k++) {
          if (vals[mem[lits + k]] >= 0) {
            found = k;
            break;
          }
        }
        if (found < 0) {
          for (k = 2; k < pos; k++) {
            if (vals[mem[lits + k]] >= 0) {
              found = k;
              break;
            }
          }
        }
        if (found >= 0) {
          mem[ref + POS] = found;
          int w = mem[lits + found];
          mem[lits + 1] = w;
          mem[lits + found] = falseLit;
          addWatch(w, first, ref);
          continue;
        }
        ws[j++] = first;
        ws[j++] = ref;
        if (fv < 0) {
          conflict = ref;
          break;
        }
        if (chrono) {
          int lvl = 0;
          for (k = 1; k < size; k++) {
            lvl = Math.max(lvl, level[mem[lits + k] >> 1]);
          }
          assignAt(first, ref, lvl);
        } else {
          assign(first, ref);
        }
      }
      if (conflict != NO_CONFLICT) {
        while (i < n) {
          ws[j++] = ws[i++];
        }
        watchSize[falseLit] = j;
        qhead = trailSize;
        conflictRef = conflict;
        return conflict;
      }
      watchSize[falseLit] = j;
    }
    return NO_CONFLICT;
  }

  // -------------------------------------------------------------------------------- analysis

  private void addLearnt(int lit) {
    if (learntSize == learnt.length) {
      learnt = Arrays.copyOf(learnt, 2 * learnt.length + 16);
    }
    learnt[learntSize++] = lit;
  }

  private void markClear(int v) {
    if (toClearSize == toClear.length) {
      toClear = Arrays.copyOf(toClear, 2 * toClear.length);
    }
    toClear[toClearSize++] = v;
  }

  private void bumpVar(int v) {
    if ((activity[v] += varInc) > 1e100) {
      for (int i = 0; i < numVars; i++) {
        activity[i] *= 1e-100;
      }
      varInc *= 1e-100;
    }
    order.increased(v);
  }

  private void bumpClause(int ref) {
    float a = Float.intBitsToFloat(mem[ref + ACT]) + claInc;
    mem[ref + ACT] = Float.floatToRawIntBits(a);
    if (a > 1e20f) {
      for (int i = 0; i < numLearnts; i++) {
        int r = learnts[i];
        mem[r + ACT] = Float.floatToRawIntBits(Float.intBitsToFloat(mem[r + ACT]) * 1e-20f);
      }
      claInc *= 1e-20f;
    }
  }

  private int computeLbd(int[] a, int from, int size) {
    if (++stamp == Integer.MAX_VALUE) {
      Arrays.fill(levelStamp, 0);
      stamp = 1;
    }
    int lbd = 0;
    for (int i = from; i < from + size; i++) {
      int l = level[a[i] >> 1];
      if (l >= levelStamp.length) {
        levelStamp = Arrays.copyOf(levelStamp, 2 * l + 2);
      }
      if (levelStamp[l] != stamp) {
        levelStamp[l] = stamp;
        lbd++;
      }
    }
    return lbd;
  }

  /** Marks a learnt clause used in a conflict; recomputes its LBD and promotes it if smaller. */
  private void touchLearnt(int ref) {
    int meta = mem[ref + META];
    bumpClause(ref);
    meta |= USED;
    int tier = tierOf(meta);
    if (tier != TIER_CORE) {
      int lbd = computeLbd(mem, ref + HEADER, mem[ref + SIZE]);
      if (lbd < lbdOf(meta)) {
        int newTier = lbd <= CORE_LBD ? TIER_CORE : lbd <= MID_LBD ? TIER_MID : tier;
        meta = (meta & ((1 << LBD_SHIFT) - 1) & ~TIER_MASK) | (newTier << TIER_SHIFT);
        meta |= lbd << LBD_SHIFT;
      }
    }
    mem[ref + META] = meta;
  }

  /** First-UIP analysis of the current conflict into {@code learnt}; returns the backjump level. */
  /**
   * Under chronological backtracking the conflict clause may have no literal, or only one, at the
   * current level. Backtracks to the conflict level; when a single literal is at that level, it
   * backtracks one more level and asserts that literal with the conflict clause as reason. Returns
   * true when no clause has to be learnt (conflictLit0 then holds a literal false at level 0 if the
   * conflict is at level 0).
   */
  private boolean conflictNeedsNoLearning() {
    int ref = conflictRef;
    int size;
    int lits;
    if (ref == BINARY_CONFLICT) {
      size = 2;
      lits = -1;
    } else {
      size = mem[ref + SIZE];
      lits = ref + HEADER;
    }
    int maxLevel = 0;
    int count = 0;
    int forced = -1;
    for (int k = 0; k < size; k++) {
      int lit = lits < 0 ? (k == 0 ? conflictLit0 : conflictLit1) : mem[lits + k];
      int l = level[lit >> 1];
      if (l > maxLevel) {
        maxLevel = l;
        count = 1;
        forced = lit;
      } else if (l == maxLevel) {
        count++;
      }
    }
    if (maxLevel == 0) {
      backtrack(0);
      conflictLit0 = lits < 0 ? conflictLit0 : mem[lits];
      return true;
    }
    if (count > 1) {
      if (maxLevel < decisionLevel) {
        backtrack(maxLevel);
      }
      return false;
    }
    backtrack(maxLevel - 1);
    if (lits < 0) {
      int other = forced == conflictLit0 ? conflictLit1 : conflictLit0;
      assignAt(forced, -2 - other, level[other >> 1]);
    } else {
      rewatch(ref);
      int lvl = 0;
      for (int k = 1; k < size; k++) {
        lvl = Math.max(lvl, level[mem[lits + k] >> 1]);
      }
      assignAt(mem[lits], ref, lvl);
    }
    return true;
  }

  private int analyze() {
    learntSize = 0;
    addLearnt(0);
    toClearSize = 0;
    int pathCount = 0;
    int p = -1;
    int index = trailSize - 1;
    int ref = conflictRef;
    do {
      if (p == -1 && ref == BINARY_CONFLICT) {
        pathCount += analyzeLit(conflictLit0) + analyzeLit(conflictLit1);
      } else if (ref < NO_REASON) {
        pathCount += analyzeLit(-2 - ref);
      } else {
        if ((mem[ref + META] & LEARNT_FLAG) != 0) {
          touchLearnt(ref);
        }
        int lits = ref + HEADER;
        int size = mem[ref + SIZE];
        for (int k = p == -1 ? 0 : 1; k < size; k++) {
          pathCount += analyzeLit(mem[lits + k]);
        }
      }
      while (seen[trail[index] >> 1] == 0 || level[trail[index] >> 1] != decisionLevel) {
        index--;
      }
      p = trail[index--];
      ref = reason[p >> 1];
      seen[p >> 1] = 0;
      pathCount--;
    } while (pathCount > 0);
    learnt[0] = p ^ 1;

    // recursive minimisation
    int abstractLevels = 0;
    for (int i = 1; i < learntSize; i++) {
      abstractLevels |= 1 << (level[learnt[i] >> 1] & 31);
    }
    int j = 1;
    for (int i = 1; i < learntSize; i++) {
      int v = learnt[i] >> 1;
      if (reason[v] == NO_REASON || !redundant(learnt[i], abstractLevels)) {
        learnt[j++] = learnt[i];
      }
    }
    learntSize = j;
    if (shrink && learntSize > 2) {
      shrinkLearnt();
    }

    for (int i = 0; i < toClearSize; i++) {
      seen[toClear[i]] = 0;
    }
    seen[learnt[0] >> 1] = 0;

    if (learntSize == 1) {
      return 0;
    }
    int maxIndex = 1;
    for (int i = 2; i < learntSize; i++) {
      if (level[learnt[i] >> 1] > level[learnt[maxIndex] >> 1]) {
        maxIndex = i;
      }
    }
    int tmp = learnt[1];
    learnt[1] = learnt[maxIndex];
    learnt[maxIndex] = tmp;
    return level[learnt[1] >> 1];
  }

  /**
   * Replaces the literals of each lower level of the learnt clause by a single UIP of that level
   * when the level's implications reach it using only literals already in the clause (or implied by
   * it) at lower levels.
   */
  private void shrinkLearnt() {
    int n = learntSize - 1;
    if (shrinkKeys.length < n) {
      shrinkKeys = new long[2 * n];
    }
    for (int i = 0; i < n; i++) {
      int lit = learnt[i + 1];
      shrinkKeys[i] = (long) level[lit >> 1] << 32 | lit;
    }
    Arrays.sort(shrinkKeys, 0, n);
    int j = 1;
    int end = n;
    while (end > 0) {
      int lvl = (int) (shrinkKeys[end - 1] >>> 32);
      int start = end - 1;
      while (start > 0 && (int) (shrinkKeys[start - 1] >>> 32) == lvl) {
        start--;
      }
      int uip = end - start > 1 ? blockUip(lvl, start, end) : -1;
      if (uip >= 0) {
        learnt[j++] = uip ^ 1;
      } else {
        for (int i = start; i < end; i++) {
          learnt[j++] = (int) shrinkKeys[i];
        }
      }
      end = start;
    }
    learntSize = j;
  }

  /** The trail literal that is a UIP of the block shrinkKeys[start, end) at level lvl, or -1. */
  private int blockUip(int lvl, int start, int end) {
    if (++shrinkStamp == Integer.MAX_VALUE) {
      Arrays.fill(shrinkMark, 0);
      shrinkStamp = 1;
    }
    int open = end - start;
    int index = 0;
    for (int i = start; i < end; i++) {
      int v = (int) shrinkKeys[i] >> 1;
      shrinkMark[v] = shrinkStamp;
      index = Math.max(index, trailPos[v]);
    }
    for (; ; index--) {
      int t = trail[index];
      int v = t >> 1;
      if (shrinkMark[v] != shrinkStamp || level[v] != lvl) {
        continue;
      }
      if (--open == 0) {
        return t;
      }
      int r = reason[v];
      if (r == NO_REASON || r == UNIT_REASON) {
        return -1;
      }
      if (r < NO_REASON) {
        open += shrinkStep(-2 - r, lvl);
      } else {
        int lits = r + HEADER;
        int size = mem[r + SIZE];
        for (int k = 1; k < size && open >= 0; k++) {
          open += shrinkStep(mem[lits + k], lvl);
        }
      }
      if (open < 0) {
        return -1;
      }
    }
  }

  /**
   * One antecedent literal of a block implication: 1 when it is a new literal at the block's level,
   * 0 when it is covered, and a large negative number when the block cannot be shrunk.
   */
  private int shrinkStep(int q, int lvl) {
    int v = q >> 1;
    int l = level[v];
    if (l == lvl) {
      if (shrinkMark[v] == shrinkStamp) {
        return 0;
      }
      shrinkMark[v] = shrinkStamp;
      return 1;
    }
    return l == 0 || seen[v] != 0 ? 0 : Integer.MIN_VALUE / 2;
  }

  /** Marks the variable of a reason literal; returns 1 when it is at the conflict level. */
  private int analyzeLit(int q) {
    int v = q >> 1;
    if (seen[v] != 0 || level[v] == 0 || reason[v] == UNIT_REASON) {
      return 0;
    }
    seen[v] = 1;
    markClear(v);
    bumpVar(v);
    if (level[v] >= decisionLevel) {
      return 1;
    }
    addLearnt(q);
    return 0;
  }

  /** Whether literal p of the learnt clause is implied by the other literals (MiniSat's test). */
  private boolean redundant(int p, int abstractLevels) {
    int top = toClearSize;
    int sp = 0;
    stack = push(stack, sp++, p);
    while (sp > 0) {
      int v = stack[--sp] >> 1;
      int r = reason[v];
      if (r < NO_REASON) {
        int q = -2 - r;
        if (!redundantStep(q, abstractLevels)) {
          return undo(top);
        }
        if (seen[q >> 1] == 0 && level[q >> 1] > 0 && reason[q >> 1] != UNIT_REASON) {
          seen[q >> 1] = 1;
          markClear(q >> 1);
          stack = push(stack, sp++, q);
        }
        continue;
      }
      int lits = r + HEADER;
      int size = mem[r + SIZE];
      for (int k = 1; k < size; k++) {
        int q = mem[lits + k];
        int qv = q >> 1;
        if (seen[qv] != 0 || level[qv] == 0 || reason[qv] == UNIT_REASON) {
          continue;
        }
        if (!redundantStep(q, abstractLevels)) {
          return undo(top);
        }
        seen[qv] = 1;
        markClear(qv);
        stack = push(stack, sp++, q);
      }
    }
    return true;
  }

  private boolean redundantStep(int q, int abstractLevels) {
    int v = q >> 1;
    if (seen[v] != 0 || level[v] == 0 || reason[v] == UNIT_REASON) {
      return true;
    }
    return reason[v] != NO_REASON && ((1 << (level[v] & 31)) & abstractLevels) != 0;
  }

  private boolean undo(int top) {
    for (int i = top; i < toClearSize; i++) {
      seen[toClear[i]] = 0;
    }
    toClearSize = top;
    return false;
  }

  /** Collects the assumptions responsible for {@code p} being false into {@code failed}. */
  private void analyzeFinal(int p) {
    int[] out = new int[assumptions.length];
    int n = 0;
    out[n++] = toDimacs(p ^ 1);
    if (decisionLevel == 0) {
      failed = Arrays.copyOf(out, n);
      return;
    }
    seen[p >> 1] = 1;
    for (int i = trailSize - 1; i >= trailLim[0]; i--) {
      int x = trail[i] >> 1;
      if (seen[x] == 0) {
        continue;
      }
      int r = reason[x];
      if (r == UNIT_REASON) {
        seen[x] = 0;
        continue;
      }
      if (r == NO_REASON) {
        out[n++] = toDimacs(trail[i]);
      } else if (r < NO_REASON) {
        int q = -2 - r;
        if (level[q >> 1] > 0) {
          seen[q >> 1] = 1;
        }
      } else {
        for (int k = 1; k < mem[r + SIZE]; k++) {
          int q = mem[r + HEADER + k];
          if (level[q >> 1] > 0) {
            seen[q >> 1] = 1;
          }
        }
      }
      seen[x] = 0;
    }
    seen[p >> 1] = 0;
    failed = Arrays.copyOf(out, n);
  }

  // ------------------------------------------------------------------------- external search

  /*
   * External search: another solver (JaCoP's CP search) makes the decisions. It opens levels with
   * newLevel(), assigns literals with assume(), runs propagateUnits(), and moves back with
   * backtrackTo(). A conflict is analysed into a pending clause; the caller backtracks until
   * pendingFalsified() is false and then calls addPendingClause(), which learns the clause,
   * asserts its literal if it is unit and propagates. Clauses can be added at any level with
   * addClauseLive(). Units learnt above level 0 are kept and re-asserted after every backtrack.
   */

  /**
   * Creates fresh variables.
   *
   * @param count how many
   * @return the first new DIMACS variable; the new ones are consecutive
   */
  public int newVariables(int count) {
    int first = numVars + 1;
    ensureVars(numVars + count);
    return first;
  }

  /**
   * Returns the current decision level.
   *
   * @return the number of open levels
   */
  public int decisionLevel() {
    return decisionLevel;
  }

  /** Opens a new decision level. */
  public void newLevel() {
    useExternally();
    newDecisionLevel();
  }

  /**
   * Returns the value of a literal under the current assignment.
   *
   * @param lit a DIMACS literal of an existing variable
   * @return 1 when true, -1 when false, 0 when unassigned
   */
  public int value(int lit) {
    return vals[toLit(lit)];
  }

  /**
   * Assigns an unassigned literal at the current level, without a reason (as a decision). Call
   * {@link #propagateUnits()} afterwards.
   *
   * @param lit a DIMACS literal whose variable is unassigned
   */
  public void assume(int lit) {
    int l = toLit(lit);
    if (vals[l] != 0) {
      throw new IllegalStateException("literal " + lit + " is already assigned");
    }
    if (decisionLevel == 0 || lastAssumedLevel >= decisionLevel) {
      throw new IllegalStateException("assume needs a new level for every literal (newLevel())");
    }
    lastAssumedLevel = decisionLevel;
    assign(l, NO_REASON);
  }

  /**
   * Returns the number of assigned literals.
   *
   * @return the size of the trail
   */
  public int trailSize() {
    return trailSize;
  }

  /**
   * Returns an assigned literal in assignment order.
   *
   * @param i a position below {@link #trailSize()}
   * @return the DIMACS literal assigned at that position
   */
  public int trailLiteral(int i) {
    return toDimacs(trail[i]);
  }

  /**
   * Unit propagation. On a conflict, the conflict is analysed into the pending clause.
   *
   * @return false on a conflict
   */
  public boolean propagateUnits() {
    useExternally();
    if (!ok) {
      setPending(learnt, 0, true);
      return false;
    }
    if (propagate() == NO_CONFLICT) {
      return true;
    }
    conflicts++;
    if (decisionLevel == 0) {
      ok = false;
      if (proof != null) {
        proof.add(learnt, 0, 0);
      }
      setPending(learnt, 0, true);
      return false;
    }
    if (!conflictAtCurrentLevel()) {
      // possible when units re-asserted after a backtrack conflict with lower levels: the
      // conflicting clause itself waits until the caller has backtracked below it
      if (conflictRef == BINARY_CONFLICT) {
        setPending(new int[] {conflictLit0, conflictLit1}, 2, true);
        pendingRef = BINARY;
      } else {
        rewatch(conflictRef);
        setPendingCopy(mem, conflictRef + HEADER, mem[conflictRef + SIZE]);
        pendingRef = conflictRef;
      }
      return false;
    }
    analyze();
    setPending(learnt, learntSize, false);
    pendingLbd = learntSize <= 2 ? learntSize : computeLbd(learnt, 0, learntSize);
    varInc /= varDecay;
    claInc /= CLA_DECAY;
    return false;
  }

  /**
   * Backtracks to a level; units learnt above level 0 are asserted again at that level.
   *
   * @param level the level to keep, at most {@link #decisionLevel()}
   */
  public void backtrackTo(int level) {
    backtrack(level);
  }

  /**
   * Returns whether a clause waits to be learnt (after a conflict, or a clause added while false).
   *
   * @return true when there is a pending clause
   */
  public boolean hasPendingClause() {
    return hasPending;
  }

  /**
   * Returns whether the pending clause is false under the current assignment, so the search must
   * backtrack further before {@link #addPendingClause()}.
   *
   * @return true when every literal of the pending clause is false (always, for the empty clause)
   */
  public boolean pendingFalsified() {
    if (!hasPending) {
      return false;
    }
    for (int i = 0; i < pendingSize; i++) {
      if (vals[pending[i]] >= 0) {
        return false;
      }
    }
    return true;
  }

  /**
   * Returns the pending clause.
   *
   * @return its DIMACS literals
   */
  public int[] pendingClause() {
    int[] c = new int[pendingSize];
    for (int i = 0; i < pendingSize; i++) {
      c[i] = toDimacs(pending[i]);
    }
    return c;
  }

  /**
   * Learns the pending clause, asserts its literal when it is unit, and propagates. The pending
   * clause must not be falsified.
   *
   * @return false on a conflict (which leaves a new pending clause)
   */
  public boolean addPendingClause() {
    if (!hasPending) {
      return propagateUnits();
    }
    if (pendingFalsified()) {
      throw new IllegalStateException("the pending clause is still false");
    }
    hasPending = false;
    int[] c = Arrays.copyOf(pending, pendingSize);
    int ref = pendingRef;
    if (!pendingAttached && proof != null) {
      proof.add(c, 0, c.length);
    }
    if (c.length == 1) {
      if (!pendingAttached) {
        addUnit(c[0]);
      }
    } else {
      orderForWatches(c);
      if (c.length == 2) {
        if (!pendingAttached) {
          addBinary(c[0], c[1]);
        }
        ref = BINARY;
      } else if (!pendingAttached) {
        ref = allocate(c, c.length, true, pendingLbd);
        learnts = push(learnts, numLearnts++, ref);
        attach(ref);
        bumpClause(ref);
      }
      assertIfUnit(c, ref);
    }
    if (conflicts >= nextReduce) {
      nextReduce = conflicts + reduceBase + (long) reduceInc * ++reductions;
      reduceDb();
    }
    return propagateUnits();
  }

  /**
   * Adds a clause at any level, without backtracking. If the clause is unit under the current
   * assignment its literal is asserted (call {@link #propagateUnits()} next); if it is false, it
   * becomes the pending clause and false is returned.
   *
   * @param lits DIMACS literals
   * @param n how many of them form the clause
   * @return false when the clause is false under the current assignment
   */
  public boolean addClauseLive(int[] lits, int n) {
    useExternally();
    if (decisionLevel == 0) {
      boolean result = addClause(lits, n);
      if (!result) {
        setPending(learnt, 0, true);
      }
      return result;
    }
    if (!ok) {
      setPending(learnt, 0, true);
      return false;
    }
    int maxVar = 0;
    for (int i = 0; i < n; i++) {
      maxVar = Math.max(maxVar, Math.abs(lits[i]));
    }
    ensureVars(maxVar);
    int[] c = new int[n];
    for (int i = 0; i < n; i++) {
      c[i] = toLit(lits[i]);
    }
    Arrays.sort(c);
    int size = 0;
    for (int i = 0; i < n; i++) {
      int l = c[i];
      boolean fixed = vals[l] != 0 && level[l >> 1] == 0;
      if ((fixed && vals[l] > 0) || (size > 0 && c[size - 1] == (l ^ 1))) {
        return true; // satisfied at level 0, or a tautology
      }
      if ((fixed && vals[l] < 0) || (size > 0 && c[size - 1] == l)) {
        continue;
      }
      c[size++] = l;
    }
    c = Arrays.copyOf(c, size);
    if (size == 0) {
      ok = false;
      setPending(c, 0, true);
      return false;
    }
    if (size == 1) {
      addUnit(c[0]);
      if (vals[c[0]] < 0) {
        setPending(c, 1, true);
        return false;
      }
      return true;
    }
    orderForWatches(c);
    int ref = BINARY;
    if (size == 2) {
      addOriginalBinary(c[0], c[1]);
    } else {
      ref = allocate(c, size, false, 0);
      originals = push(originals, numOriginals++, ref);
      attach(ref);
    }
    if (vals[c[0]] < 0) {
      setPending(c, size, true);
      pendingRef = ref;
      return false;
    }
    assertIfUnit(c, ref);
    return true;
  }

  /**
   * Writes the original clauses (and the units fixed at level 0) in DIMACS format.
   *
   * @param out the destination
   * @throws java.io.IOException if writing fails
   */
  public void writeDimacs(java.io.Writer out) throws java.io.IOException {
    restoreEliminated();
    int fixed = 0;
    for (int i = 0; i < trailSize && level[trail[i] >> 1] == 0; i++) {
      fixed++;
    }
    out.write(
        "p cnf "
            + numVars
            + " "
            + (fixed + numUnits + numOriginalBinaries / 2 + numOriginals)
            + "\n");
    for (int i = 0; i < fixed; i++) {
      out.write(toDimacs(trail[i]) + " 0\n");
    }
    for (int i = 0; i < numUnits; i++) {
      out.write(toDimacs(units[i]) + " 0\n");
    }
    for (int i = 0; i < numOriginalBinaries; i += 2) {
      out.write(toDimacs(originalBinaries[i]) + " " + toDimacs(originalBinaries[i + 1]) + " 0\n");
    }
    for (int i = 0; i < numOriginals; i++) {
      int ref = originals[i];
      StringBuilder line = new StringBuilder();
      for (int k = 0; k < mem[ref + SIZE]; k++) {
        line.append(toDimacs(mem[ref + HEADER + k])).append(' ');
      }
      out.write(line.append("0\n").toString());
    }
  }

  private boolean conflictAtCurrentLevel() {
    if (conflictRef == BINARY_CONFLICT) {
      return atCurrentLevel(conflictLit0) || atCurrentLevel(conflictLit1);
    }
    for (int k = 0; k < mem[conflictRef + SIZE]; k++) {
      if (atCurrentLevel(mem[conflictRef + HEADER + k])) {
        return true;
      }
    }
    return false;
  }

  private boolean atCurrentLevel(int lit) {
    int v = lit >> 1;
    return level[v] == decisionLevel && reason[v] != UNIT_REASON;
  }

  /** Copies an arena clause into the pending clause (attached). */
  private void setPendingCopy(int[] from, int offset, int size) {
    setPending(Arrays.copyOfRange(from, offset, offset + size), size, true);
  }

  /** Moves the watches of an arena clause to its best literals (see orderForWatches). */
  private void rewatch(int ref) {
    int lits = ref + HEADER;
    removeWatch(mem[lits], ref);
    removeWatch(mem[lits + 1], ref);
    int[] c = Arrays.copyOfRange(mem, lits, lits + mem[ref + SIZE]);
    orderForWatches(c);
    System.arraycopy(c, 0, mem, lits, c.length);
    mem[ref + POS] = 2;
    attach(ref);
  }

  private void removeWatch(int lit, int ref) {
    int[] ws = watches[lit];
    int n = watchSize[lit];
    for (int i = 0; i < n; i += 2) {
      if (ws[i + 1] == ref) {
        System.arraycopy(ws, i + 2, ws, i, n - i - 2);
        watchSize[lit] = n - 2;
        return;
      }
    }
  }

  private void setPending(int[] lits, int size, boolean attached) {
    if (pending.length < size) {
      pending = new int[size];
    }
    System.arraycopy(lits, 0, pending, 0, size);
    pendingSize = size;
    pendingAttached = attached;
    pendingRef = NO_REASON;
    hasPending = true;
  }

  private void addOriginalBinary(int a, int b) {
    addBinary(a, b);
    originalBinaries = push(originalBinaries, numOriginalBinaries++, a);
    originalBinaries = push(originalBinaries, numOriginalBinaries++, b);
  }

  /** A unit clause: fixed now at level 0, or kept and re-asserted after backtracking. */
  private void addUnit(int l) {
    if (decisionLevel > 0) {
      units = push(units, numUnits++, l);
    }
    if (vals[l] == 0) {
      assign(l, decisionLevel > 0 ? UNIT_REASON : NO_REASON);
    }
  }

  private void reassertUnits() {
    for (int i = 0; i < numUnits; i++) {
      int u = units[i];
      if (vals[u] == 0) {
        assign(u, decisionLevel > 0 ? UNIT_REASON : NO_REASON);
      } else if (vals[u] < 0 && !hasPending) {
        setPending(new int[] {u}, 1, true);
      }
    }
    if (decisionLevel == 0 && numUnits > 0) {
      int j = 0;
      for (int i = 0; i < numUnits; i++) {
        if (vals[units[i]] <= 0) {
          units[j++] = units[i];
        }
      }
      numUnits = j;
    }
  }

  /**
   * Moves the two best literals to the front: true, then unassigned, then false at the highest
   * level.
   */
  private void orderForWatches(int[] c) {
    for (int pos = 0; pos < 2 && pos < c.length; pos++) {
      int best = pos;
      for (int i = pos + 1; i < c.length; i++) {
        if (watchScore(c[i]) > watchScore(c[best])) {
          best = i;
        }
      }
      int t = c[pos];
      c[pos] = c[best];
      c[best] = t;
    }
  }

  private int watchScore(int l) {
    int v = vals[l];
    return v > 0 ? Integer.MAX_VALUE : v == 0 ? Integer.MAX_VALUE - 1 : level[l >> 1];
  }

  /**
   * Asserts c[0] when it is unassigned and the rest of the clause is false. For a clause in the
   * arena, ref is its reference and the literal order is read from the arena.
   */
  private void assertIfUnit(int[] c, int ref) {
    int[] lits = c;
    int from = 0;
    int size = c.length;
    if (ref >= 0) {
      lits = mem;
      from = ref + HEADER;
      size = mem[ref + SIZE];
      if (vals[lits[from]] == 0 && vals[lits[from + 1]] > 0) {
        return;
      }
      // the arena keeps the watch order; make sure the best literal is watched first
      if (watchScore(lits[from + 1]) > watchScore(lits[from])) {
        return; // two non-false literals or already satisfied
      }
    }
    if (vals[lits[from]] != 0) {
      return;
    }
    for (int i = from + 1; i < from + size; i++) {
      if (vals[lits[i]] >= 0) {
        return;
      }
    }
    assign(lits[from], ref >= 0 ? ref : ref == BINARY ? -2 - lits[from + 1] : NO_REASON);
  }

  // ---------------------------------------------------------------------------------- search

  private int search() {
    if (propagate() != NO_CONFLICT) {
      ok = false;
      if (proof != null) {
        proof.add(learnt, 0, 0);
      }
      return UNSAT;
    }
    while (true) {
      int confl = propagate();
      if (confl != NO_CONFLICT) {
        conflicts++;
        if (decisionLevel == 0) {
          ok = false;
          if (proof != null) {
            proof.add(learnt, 0, 0);
          }
          return UNSAT;
        }
        if (chrono && conflictNeedsNoLearning()) {
          if (decisionLevel == 0 && vals[conflictLit0] < 0) {
            ok = false;
            if (proof != null) {
              proof.add(learnt, 0, 0);
            }
            return UNSAT;
          }
          continue;
        }
        trailQueuePush(trailSize);
        updateTargetAndBest();
        int btLevel = analyze();
        if (chrono && learntSize > 1 && decisionLevel - btLevel > chronoLimit) {
          btLevel = decisionLevel - 1;
        }
        backtrack(btLevel);
        learnClause();
        varInc /= varDecay;
        claInc /= CLA_DECAY;
        if (!stable && varDecay < 0.95 && conflicts % 5000 == 0) {
          varDecay += 0.01;
        }
        if (conflicts >= conflictLimit || interrupted || System.nanoTime() > deadline) {
          return UNKNOWN;
        }
        continue;
      }
      if (shouldRestart()) {
        restart();
        if (vivifyDue && !vivify()) {
          return UNSAT;
        }
        continue;
      }
      if (conflicts >= nextReduce) {
        nextReduce = conflicts + reduceBase + (long) reduceInc * ++reductions;
        reduceDb();
        vivifyDue = vivification;
      }
      if (decisionLevel == 0 && trailSize != simplifyAssigns) {
        simplifyDb();
      }
      int next = -1;
      while (decisionLevel < assumptions.length) {
        int a = assumptions[decisionLevel];
        if (vals[a] > 0) {
          newDecisionLevel();
        } else if (vals[a] < 0) {
          analyzeFinal(a ^ 1);
          return UNSAT;
        } else {
          next = a;
          break;
        }
      }
      if (next == -1) {
        next = pickBranch();
        if (next == -1) {
          return SAT;
        }
        if ((++decisions & 1023) == 0 && (interrupted || System.nanoTime() > deadline)) {
          return UNKNOWN;
        }
      }
      newDecisionLevel();
      assign(next, NO_REASON);
    }
  }

  private int pickBranch() {
    while (!order.isEmpty()) {
      int v = order.removeMax();
      if (vals[2 * v] == 0 && !eliminatedVar[v]) {
        return 2 * v + (stable && targetSign[v] >= 0 ? targetSign[v] : savedSign[v]);
      }
    }
    return -1;
  }

  /**
   * Target phases (CaDiCaL): in stable mode, remember the signs of the longest conflict-free
   * assignment seen since the last restart, and prefer them in decisions.
   */
  private void updateTargetAndBest() {
    int assigned = trailLim[decisionLevel - 1];
    if (stable && assigned > targetAssigned) {
      targetAssigned = assigned;
      for (int i = 0; i < assigned; i++) {
        targetSign[trail[i] >> 1] = (byte) (trail[i] & 1);
      }
    }
    if (assigned > bestAssigned) {
      bestAssigned = assigned;
      for (int i = 0; i < assigned; i++) {
        bestSign[trail[i] >> 1] = (byte) (trail[i] & 1);
      }
    }
  }

  /**
   * Rephasing (CaDiCaL without random walks): every so often the saved phases are reset to the
   * original phase (true), the inverted one, or the best assignment seen since the last rephase, in
   * the order O, I, then B, O, B, I repeated.
   */
  private void rephase() {
    rephases++;
    nextRephase = conflicts + REPHASE_INTERVAL * rephases;
    String cycle = walking ? "BWOBWI" : "BOBI";
    char kind =
        rephases <= 2 ? "OI".charAt(rephases - 1) : cycle.charAt((rephases - 3) % cycle.length());
    switch (kind) {
      case 'O' -> Arrays.fill(savedSign, 0, numVars, (byte) 0);
      case 'I' -> Arrays.fill(savedSign, 0, numVars, (byte) 1);
      case 'W' -> {
        System.arraycopy(bestSign, 0, savedSign, 0, numVars);
        walk();
      }
      default -> System.arraycopy(bestSign, 0, savedSign, 0, numVars);
    }
    System.arraycopy(savedSign, 0, targetSign, 0, numVars);
    targetAssigned = 0;
    bestAssigned = 0;
  }

  /** Runs the Walker on the irredundant clauses from the saved phases and saves its best phases. */
  private void walk() {
    long begin = System.nanoTime();
    int[] lits = new int[1024];
    int[] start = new int[numOriginals + numOriginalBinaries / 2 + 1];
    int n = 0;
    int size = 0;
    for (int i = 0; i < numOriginals; i++) {
      int ref = originals[i];
      if ((mem[ref + META] & DELETED) != 0) {
        continue;
      }
      int len = mem[ref + SIZE];
      if (size + len > lits.length) {
        lits = Arrays.copyOf(lits, Math.max(size + len, 2 * lits.length));
      }
      int from = size;
      boolean satisfied = false;
      for (int k = 0; k < len && !satisfied; k++) {
        int l = mem[ref + HEADER + k];
        satisfied = vals[l] > 0;
        if (vals[l] == 0) {
          lits[size++] = l;
        }
      }
      if (satisfied) {
        size = from;
      } else {
        start[n++] = from;
      }
    }
    for (int i = 0; i < numOriginalBinaries; i += 2) {
      int a = originalBinaries[i];
      int b = originalBinaries[i + 1];
      if (vals[a] == 0 && vals[b] == 0) {
        if (size + 2 > lits.length) {
          lits = Arrays.copyOf(lits, 2 * lits.length + 2);
        }
        start[n++] = size;
        lits[size++] = a;
        lits[size++] = b;
      }
    }
    start[n] = size;
    byte[] phases = Arrays.copyOf(savedSign, numVars);
    for (int i = 0; i < trailSize; i++) {
      phases[trail[i] >> 1] = (byte) (trail[i] & 1); // fixed at level 0
    }
    Walker walker = new Walker(numVars, lits, start, n, phases, ++walks);
    walker.run(10_000_000L + (propagations - propagationsAtWalk) / 5);
    propagationsAtWalk = propagations;
    System.arraycopy(walker.best(), 0, savedSign, 0, numVars);
    walkNanos += System.nanoTime() - begin;
  }

  /**
   * Turns local search in the rephasing cycle on or off (on by default).
   *
   * @param on whether to walk
   */
  public void setWalk(boolean on) {
    walking = on;
  }

  private void learnClause() {
    int lbd;
    if (learntSize == 1) {
      lbd = 1;
      if (proof != null) {
        proof.add(learnt, 0, 1);
      }
      assign(learnt[0], NO_REASON);
    } else if (learntSize == 2) {
      lbd = 2;
      if (proof != null) {
        proof.add(learnt, 0, 2);
      }
      addBinary(learnt[0], learnt[1]);
      assignAt(learnt[0], -2 - learnt[1], level[learnt[1] >> 1]);
    } else {
      lbd = computeLbd(learnt, 0, learntSize);
      if (proof != null) {
        proof.add(learnt, 0, learntSize);
      }
      int ref = allocate(learnt, learntSize, true, lbd);
      learnts = push(learnts, numLearnts++, ref);
      attach(ref);
      bumpClause(ref);
      assignAt(learnt[0], ref, level[learnt[1] >> 1]);
    }
    lbdSum += lbd;
    lbdQueueSum += lbd;
    if (lbdQueueSize == lbdQueue.length) {
      lbdQueueSum -= lbdQueue[lbdQueueHead];
    } else {
      lbdQueueSize++;
    }
    lbdQueue[lbdQueueHead] = lbd;
    lbdQueueHead = (lbdQueueHead + 1) % lbdQueue.length;
  }

  private void trailQueuePush(int size) {
    trailQueueSum += size;
    if (trailQueueSize == trailQueue.length) {
      trailQueueSum -= trailQueue[trailQueueHead];
    } else {
      trailQueueSize++;
    }
    trailQueue[trailQueueHead] = size;
    trailQueueHead = (trailQueueHead + 1) % trailQueue.length;
    // Glucose restart blocking: a much longer trail than usual suggests we are close to a model
    if (!stable
        && conflicts > 10000
        && lbdQueueSize == lbdQueue.length
        && trailQueueSize == trailQueue.length
        && size > 1.4 * trailQueueSum / trailQueueSize) {
      lbdQueueSize = 0;
      lbdQueueSum = 0;
    }
  }

  private boolean shouldRestart() {
    if (decisionLevel <= assumptions.length) {
      return false;
    }
    if (conflicts >= modeSwitchAt || conflicts >= nextRephase) {
      return true; // mode switches and rephasing happen at restarts, which may be rare otherwise
    }
    if (stable) {
      return conflicts - conflictsAtRestart >= lubyLimit;
    }
    return lbdQueueSize == lbdQueue.length
        && conflicts > 0
        && (double) lbdQueueSum / lbdQueueSize * 0.8 > (double) lbdSum / conflicts;
  }

  private void restart() {
    restarts++;
    backtrack(0);
    conflictsAtRestart = conflicts;
    targetAssigned = 0;
    lbdQueueSize = 0;
    lbdQueueSum = 0;
    if (conflicts >= nextRephase) {
      rephase();
    }
    if (conflicts >= modeSwitchAt) {
      stable = !stable;
      modePhases++;
      modeSwitchAt = conflicts + 1000L * (modePhases / 2 + 1) * (modePhases / 2 + 1);
      lubyIndex = 0;
    }
    if (stable) {
      lubyLimit = 512L * luby(++lubyIndex);
    }
  }

  /** The i-th element (from 1) of the Luby sequence 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, ... */
  static long luby(int i) {
    int x = i - 1;
    int size = 1;
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

  // ------------------------------------------------------------------------- clause database

  private void reduceDb() {
    long[] keys = new long[numLearnts];
    int candidates = 0;
    for (int i = 0; i < numLearnts; i++) {
      int ref = learnts[i];
      int meta = mem[ref + META];
      int tier = tierOf(meta);
      if (tier == TIER_CORE || isLocked(ref)) {
        mem[ref + META] = meta & ~USED;
        continue;
      }
      if ((meta & USED) != 0) {
        mem[ref + META] = meta & ~USED;
        continue;
      }
      if (tier == TIER_MID) {
        mem[ref + META] = (meta & ~TIER_MASK) | (TIER_LOCAL << TIER_SHIFT);
        continue;
      }
      long act = Float.floatToRawIntBits(Float.intBitsToFloat(mem[ref + ACT])) >>> 8;
      keys[candidates++] = ((long) (MAX_LBD - lbdOf(meta)) << 55) | (act << 32) | i;
    }
    Arrays.sort(keys, 0, candidates);
    for (int c = 0; c < candidates / 2; c++) {
      deleteClause(learnts[(int) keys[c]]);
    }
    purge();
  }

  /** The number of variables eliminated now. */
  int eliminatedCount() {
    return numEliminated;
  }

  /** The external-search methods keep every variable: eliminated ones are brought back. */
  private void useExternally() {
    externalUsed = true;
    restoreEliminated();
  }

  /**
   * Runs the Eliminator on the irredundant clauses at level 0 (before any conflict, so there are no
   * learnt clauses) and replaces them by its result.
   *
   * @return false when the formula is unsatisfiable
   */
  private boolean eliminate() {
    if (propagate() != NO_CONFLICT) {
      return refuted();
    }
    boolean[] frozen = new boolean[numVars];
    for (int a : assumptions) {
      frozen[a >> 1] = true;
    }
    int[][] input = new int[numOriginals + numOriginalBinaries / 2][];
    int n = 0;
    for (int i = 0; i < numOriginals; i++) {
      int ref = originals[i];
      int size = mem[ref + SIZE];
      if ((mem[ref + META] & DELETED) != 0) {
        continue;
      }
      int[] c = new int[size];
      int k = 0;
      boolean satisfied = false;
      for (int j = 0; j < size && !satisfied; j++) {
        int l = mem[ref + HEADER + j];
        satisfied = vals[l] > 0;
        if (vals[l] == 0) {
          c[k++] = l;
        }
      }
      if (satisfied) {
        continue;
      }
      if (k < size) {
        c = Arrays.copyOf(c, k);
        if (proof != null) {
          proof.add(c, 0, k);
        }
      }
      input[n++] = c;
    }
    for (int i = 0; i < numOriginalBinaries; i += 2) {
      int a = originalBinaries[i];
      int b = originalBinaries[i + 1];
      if (vals[a] <= 0 && vals[b] <= 0) {
        input[n++] = new int[] {a, b};
      }
    }
    Eliminator e = new Eliminator(numVars, input, n, frozen, proof);
    boolean sat = e.run();
    for (int i = 0; i < numOriginals; i++) {
      int ref = originals[i];
      if ((mem[ref + META] & DELETED) == 0) {
        mem[ref + META] |= DELETED;
        wasted += HEADER + mem[ref + SIZE];
      }
    }
    for (int i = 0; i < trailSize; i++) {
      reason[trail[i] >> 1] = NO_REASON;
    }
    numOriginalBinaries = 0;
    Arrays.fill(watchSize, 0);
    purge();
    if (!sat) {
      return refuted();
    }
    for (int[] c : e.clauses()) {
      if (c.length == 2) {
        addOriginalBinary(c[0], c[1]);
      } else {
        int ref = allocate(c, c.length, false, 0);
        originals = push(originals, numOriginals++, ref);
        attach(ref);
      }
    }
    boolean[] gone = e.eliminated();
    for (int v = 0; v < numVars; v++) {
      eliminatedVar[v] = gone[v];
    }
    numEliminated = e.numEliminated();
    extension = e.stack();
    for (int u : e.units()) {
      if (vals[u] < 0) {
        return refuted();
      }
      if (vals[u] == 0) {
        assign(u, NO_REASON);
      }
    }
    if (propagate() != NO_CONFLICT) {
      return refuted();
    }
    return true;
  }

  private boolean refuted() {
    ok = false;
    if (proof != null) {
      proof.add(learnt, 0, 0);
    }
    return false;
  }

  /** Adds back every clause removed by elimination, so all variables are free again. */
  private void restoreEliminated() {
    if (numEliminated == 0) {
      return;
    }
    int[] ext = extension;
    extension = new int[0];
    numEliminated = 0;
    for (int v = 0; v < numVars; v++) {
      if (eliminatedVar[v]) {
        eliminatedVar[v] = false;
        order.insert(v);
      }
    }
    int i = ext.length;
    while (i > 0 && ok) {
      int size = ext[i - 1];
      int start = i - 1 - size;
      int[] c = new int[size];
      for (int k = 0; k < size; k++) {
        c[k] = toDimacs(ext[start + k]);
      }
      if (proof != null) {
        proof.add(ext, start, size);
      }
      addClause(c, size);
      i = start;
    }
  }

  /**
   * Vivifies the learnt clauses of the core and middle tiers (Luo et al. 2017, as in CaDiCaL) at
   * level 0: the negations of a clause's literals are decided one by one, and the clause is cut
   * after a conflict or a literal of it that becomes true, and loses its literals that become
   * false. Each clause is tried once, within a tenth of the propagations of the search since the
   * last round.
   *
   * @return false when the formula is found unsatisfiable
   */
  private boolean vivify() {
    vivifyDue = false;
    if (propagate() != NO_CONFLICT) {
      return refuted();
    }
    long budget = propagations + Math.max(20_000, (propagations - propagationsAtVivify) / 10);
    boolean wasChrono = chrono;
    chrono = false;
    int[] candidates = new int[numLearnts];
    int n = 0;
    for (int i = numLearnts - 1; i >= 0; i--) {
      int meta = mem[learnts[i] + META];
      if ((meta & (DELETED | VIVIFIED)) == 0 && tierOf(meta) != TIER_LOCAL) {
        candidates[n++] = learnts[i];
      }
    }
    boolean result = true;
    for (int i = 0; i < n && propagations < budget && result; i++) {
      result = vivifyClause(candidates[i]);
    }
    chrono = wasChrono;
    propagationsAtVivify = propagations;
    purge();
    return result;
  }

  private boolean vivifyClause(int ref) {
    int meta = mem[ref + META];
    mem[ref + META] = meta | VIVIFIED;
    int size = mem[ref + SIZE];
    int lits = ref + HEADER;
    for (int k = 0; k < size; k++) {
      if (vals[mem[lits + k]] > 0) {
        return true; // satisfied at level 0: simplifyDb removes it
      }
    }
    if (vivifyLits.length < 2 * size) {
      vivifyLits = new int[4 * size];
    }
    // propagation reorders the clause in the arena, so its literals are copied first
    int[] d = vivifyLits;
    System.arraycopy(mem, lits, d, size, size);
    int n = 0;
    for (int k = 0; k < size; k++) {
      int l = d[size + k];
      if (vals[l] < 0) {
        continue;
      }
      d[n++] = l;
      if (vals[l] > 0) {
        break;
      }
      newDecisionLevel();
      assign(l ^ 1, NO_REASON);
      if (propagate() != NO_CONFLICT) {
        break;
      }
    }
    backtrack(0);
    if (n == size) {
      return true;
    }
    if (proof != null) {
      proof.add(d, 0, n);
    }
    if (n == 0) {
      return refuted();
    }
    deleteClause(ref);
    if (n == 1) {
      assign(d[0], NO_REASON);
      return propagate() == NO_CONFLICT || refuted();
    }
    if (n == 2) {
      addBinary(d[0], d[1]);
      return true;
    }
    int copy = allocate(d, n, true, Math.min(lbdOf(meta), n - 1));
    mem[copy + META] |= VIVIFIED;
    mem[copy + ACT] = mem[ref + ACT];
    learnts = push(learnts, numLearnts++, copy);
    attach(copy);
    return true;
  }

  /** Reduces the learnt clauses after this many conflicts and then more often, for tests. */
  void setReduceBase(int conflicts) {
    reduceBase = conflicts;
    reduceInc = Math.max(1, conflicts * 3 / 20);
    nextReduce = conflicts;
  }

  /**
   * Turns vivification of learnt clauses on or off (on by default).
   *
   * @param on whether to vivify
   */
  public void setVivification(boolean on) {
    vivification = on;
  }

  /** Removes satisfied clauses at level 0. */
  private void simplifyDb() {
    for (int pass = 0; pass < 2; pass++) {
      int[] list = pass == 0 ? originals : learnts;
      int n = pass == 0 ? numOriginals : numLearnts;
      for (int i = 0; i < n; i++) {
        int ref = list[i];
        if ((mem[ref + META] & DELETED) != 0) {
          continue;
        }
        int size = mem[ref + SIZE];
        for (int k = 0; k < size; k++) {
          if (vals[mem[ref + HEADER + k]] > 0) {
            int v = mem[ref + HEADER] >> 1;
            if (reason[v] == ref) {
              reason[v] = NO_REASON;
            }
            deleteClause(ref);
            break;
          }
        }
      }
    }
    purge();
    simplifyAssigns = trailSize;
  }

  /**
   * Drops deleted clauses from the clause lists and watches, compacting the arena if worthwhile.
   */
  private void purge() {
    numOriginals = filterDeleted(originals, numOriginals);
    numLearnts = filterDeleted(learnts, numLearnts);
    if (wasted > memSize / 2) {
      compact();
      return;
    }
    for (int lit = 0; lit < 2 * numVars; lit++) {
      int[] ws = watches[lit];
      int n = watchSize[lit];
      int j = 0;
      for (int i = 0; i < n; i += 2) {
        int ref = ws[i + 1];
        if (ref == BINARY || (mem[ref + META] & DELETED) == 0) {
          ws[j++] = ws[i];
          ws[j++] = ref;
        }
      }
      watchSize[lit] = j;
    }
  }

  private int filterDeleted(int[] list, int n) {
    int j = 0;
    for (int i = 0; i < n; i++) {
      if ((mem[list[i] + META] & DELETED) == 0) {
        list[j++] = list[i];
      }
    }
    return j;
  }

  /** Copies the live clauses into a fresh arena and remaps every reference. */
  private void compact() {
    int[] to = new int[Math.max(1 << 16, (memSize - wasted) * 3 / 2)];
    int top = 0;
    int off = 0;
    while (off < memSize) {
      int size = mem[off + SIZE];
      int len = HEADER + size;
      if ((mem[off + META] & DELETED) == 0) {
        System.arraycopy(mem, off, to, top, len);
        mem[off + ACT] = top; // forwarding address
        top += len;
      }
      off += len;
    }
    for (int i = 0; i < numOriginals; i++) {
      originals[i] = mem[originals[i] + ACT];
    }
    for (int i = 0; i < numLearnts; i++) {
      learnts[i] = mem[learnts[i] + ACT];
    }
    for (int i = 0; i < trailSize; i++) {
      int v = trail[i] >> 1;
      int r = reason[v];
      if (r >= 0) {
        reason[v] = (mem[r + META] & DELETED) == 0 ? mem[r + ACT] : NO_REASON;
      }
    }
    for (int lit = 0; lit < 2 * numVars; lit++) {
      int[] ws = watches[lit];
      int n = watchSize[lit];
      int j = 0;
      for (int i = 0; i < n; i += 2) {
        int ref = ws[i + 1];
        if (ref == BINARY) {
          ws[j++] = ws[i];
          ws[j++] = ref;
        } else if ((mem[ref + META] & DELETED) == 0) {
          ws[j++] = ws[i];
          ws[j++] = mem[ref + ACT];
        }
      }
      watchSize[lit] = j;
    }
    mem = to;
    memSize = top;
    wasted = 0;
  }
}
