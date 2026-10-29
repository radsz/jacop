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
import java.util.SplittableRandom;

/**
 * A CDCL SAT solver built on flat arrays.
 *
 * <p>Literals are internal integers {@code 2*var + sign} (sign 1 for a negative literal); the
 * public API takes DIMACS literals (variables from 1, negative for negation). Clauses of three or
 * more literals live in one {@code int[]} arena: a header (size, flags with LBD, activity, saved
 * search position) followed by the literals. Binary clauses are kept only in their own watch lists
 * (the other literal), which propagation visits first. Every watch entry of a longer clause is a
 * pair (blocker literal, clause reference); {@link #BINARY} is the reference of a binary clause
 * where a reason or a conflict needs one.
 *
 * <p>Search: first-UIP learning with recursive minimisation, LBD, EVSIDS with phase saving,
 * alternating focused mode (restarts when the fast LBD average exceeds the slow one) and stable
 * mode (Luby restarts), a three-tier learnt clause database with periodic reduction, optional DRAT
 * proof output, and solving under assumptions.
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
  // reason of a literal the external propagator implied, asked for only when analysis needs it
  private static final int EXTERNAL_REASON = Integer.MIN_VALUE + 1;

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
  private static final int TEMPORARY =
      64; // an external reason, deleted when its variable is unassigned
  private static final int TIER_SHIFT = 3;
  private static final int TIER_MASK = 3 << TIER_SHIFT;
  private static final int LBD_SHIFT = 8;
  private static final int MAX_LBD = 255;

  private static final int TIER_CORE = 0;
  private static final int TIER_MID = 1;
  private static final int TIER_LOCAL = 2;
  private int coreLbd = 2;
  private int midLbd = 6;

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
  private int[][] binWatches = new int[0][];
  private int[] binSize = new int[0];
  private boolean ok = true;

  // --- conflict and analysis scratch
  private int conflictRef;
  private int conflictLit0;
  private int conflictLit1;
  private int[] learnt = new int[16];
  private int[] dimacsLearnt = new int[16];
  // semantic UIP: open conflict-level literals per integer variable of the external propagator
  private int[] groupOpen = new int[16];
  private int groupsOpen;
  private int ungroupedOpen;
  private int[] frontier = new int[16];
  private int learntSize;
  private int[] toClear = new int[16];
  private int toClearSize;
  private int[] levelStamp = new int[16];
  private int stamp;
  // all-UIP shrinking (Fleury and Biere 2020): marks of one level's block, and the sort keys
  private boolean shrink = true;
  private int[] shrinkMark = new int[0];
  private int shrinkStamp;
  // the depth of the minimisation's search, as CaDiCaL's minimizedepth
  private static final int MINIMIZE_DEPTH = 1000;
  // variables found not redundant during this conflict's minimisation (poisoned), by stamp
  private int[] poisonMark = new int[0];
  private int poisonStamp;
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
  // exponential moving averages of the LBD (CaDiCaL), used when emaRestarts is on
  private boolean emaRestarts = true;
  private boolean restartsOn = true;
  private double emaFast;
  private double emaSlow;
  private double emaFastBeta = 1;
  private double emaSlowBeta = 1;
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
  // learnt binary clauses, which live only in the watch lists, kept for inprocessing
  private int[] learntBinaries = new int[16];
  private int numLearntBinaries;

  // --- variable elimination before the first search (see Eliminator)
  private boolean elimination = true;
  private boolean eliminationTried;
  private boolean externalUsed;
  private boolean[] eliminatedVar = new boolean[0];
  private int numEliminated;
  private int[] extension = new int[0];
  // elimination rounds during search, at restarts
  private long nextElimination = 5000;
  private int eliminationInterval = 5000;
  private int eliminationRounds;
  private long seed;

  // --- external propagator (see ExternalPropagator)
  private ExternalPropagator external;
  private int externalReasonKeep = 2;
  private boolean[] observed = new boolean[0];
  // the trail prefix whose observed assignments the propagator has seen
  private int notified;
  // the propagator is told about levels and assignments (only in the search of solve())
  private boolean notifying;
  private int[] queuedExternal;
  // variables observed after they were assigned, notified at the next propagation
  private int[] lateObserved = new int[4];
  private int numLateObserved;

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

  /** Statistics: literals of the learnt clauses, after minimisation. */
  public long learntLiterals;

  /** Statistics: learnt literals the external propagator removed as implied by others. */
  public long semanticallyRemoved;

  /** Statistics: conflicts whose analysis stopped at a semantic UIP before the first UIP. */
  public long semanticUips;

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
      poisonMark = Arrays.copyOf(poisonMark, c);
      eliminatedVar = Arrays.copyOf(eliminatedVar, c);
      observed = Arrays.copyOf(observed, c);
      watches = Arrays.copyOf(watches, 2 * c);
      watchSize = Arrays.copyOf(watchSize, 2 * c);
      binWatches = Arrays.copyOf(binWatches, 2 * c);
      binSize = Arrays.copyOf(binSize, 2 * c);
    }
    order.grow(n, activity);
    Arrays.fill(reason, numVars, n, NO_REASON);
    // initial phase true (sign 0), as in CaDiCaL
    Arrays.fill(savedSign, numVars, n, (byte) 0);
    Arrays.fill(targetSign, numVars, n, (byte) -1);
    Arrays.fill(bestSign, numVars, n, (byte) 0);
    if (seed != 0) {
      // a different initial decision order for each seed
      SplittableRandom random = new SplittableRandom(seed + numVars);
      for (int v = numVars; v < n; v++) {
        activity[v] = random.nextDouble() * 1e-3; // NOSONAR: activity holds n variables, see above
      }
    }
    // the arrays hold at least n variables here (SonarCloud does not see it)
    for (int l = 2 * numVars; l < 2 * n; l++) {
      watches[l] = new int[4]; // NOSONAR
      binWatches[l] = new int[2]; // NOSONAR
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
    // chronological backtracking would assign literals below the current level, which the level
    // notifications of an external propagator cannot express
    chrono = chronoLimit >= 0 && assumptions.length == 0 && external == null;
    notifying = external != null;
    int result;
    try {
      result = search();
      if (result == SAT) {
        model = new boolean[numVars];
        for (int v = 0; v < numVars; v++) {
          model[v] = vals[2 * v] > 0;
        }
        Eliminator.extend(extension, model);
      }
      backtrack(0);
    } finally {
      chrono = false;
      notifying = false;
      queuedExternal = null;
    }
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
   * Returns the wall-clock deadline of {@link #solve}.
   *
   * @return a {@link System#nanoTime()} value, or {@link Long#MAX_VALUE} for none
   */
  public long deadline() {
    return deadline;
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
   * Sets the size up to which an external propagator's reasons are kept as learnt clauses once
   * conflict analysis has asked for them (2 by default: binary reasons are kept). Larger reasons
   * are temporary: they live while their literal stays assigned, unwatched, and are deleted when it
   * is unassigned.
   *
   * @param size the largest reason kept, at least 2
   */
  public void setExternalReasonKeep(int size) {
    externalReasonKeep = Math.max(2, size);
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
    int tier = lbd <= coreLbd ? TIER_CORE : lbd <= midLbd ? TIER_MID : TIER_LOCAL;
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
    addBinWatch(a, b);
    addBinWatch(b, a);
  }

  private void addBinWatch(int lit, int other) {
    int[] ws = binWatches[lit];
    int n = binSize[lit];
    if (n == ws.length) {
      ws = Arrays.copyOf(ws, 2 * n + 2);
      binWatches[lit] = ws;
    }
    ws[n] = other;
    binSize[lit] = n + 1;
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
    if (notifying) {
      external.notifyNewDecisionLevel();
    }
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
      int r = reason[v];
      if (r >= 0 && (mem[r + META] & TEMPORARY) != 0) {
        mem[r + META] |= DELETED;
        wasted += HEADER + mem[r + SIZE];
        reason[v] = NO_REASON;
      }
      savedSign[v] = (byte) (lit & 1);
      order.insert(v);
    }
    trailSize = kept;
    qhead = start;
    decisionLevel = target;
    notified = Math.min(notified, kept);
    if (notifying) {
      external.notifyBacktrack(target);
    }
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
      int[] bs = binWatches[falseLit];
      for (int b = binSize[falseLit] - 1; b >= 0; b--) {
        int other = bs[b];
        int ov = vals[other];
        if (ov > 0) {
          continue;
        }
        if (ov < 0) {
          qhead = trailSize;
          conflictRef = BINARY_CONFLICT;
          conflictLit0 = other;
          conflictLit1 = falseLit;
          return BINARY_CONFLICT;
        }
        if (chrono) {
          assignAt(other, -2 - falseLit, level[falseLit >> 1]);
        } else {
          assign(other, -2 - falseLit);
        }
      }
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
        int newTier = lbd <= coreLbd ? TIER_CORE : lbd <= midLbd ? TIER_MID : tier;
        meta = (meta & ((1 << LBD_SHIFT) - 1) & ~TIER_MASK) | (newTier << TIER_SHIFT);
        meta |= lbd << LBD_SHIFT;
      }
    }
    mem[ref + META] = meta;
  }

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
      int lit;
      if (lits >= 0) {
        lit = mem[lits + k];
      } else {
        lit = k == 0 ? conflictLit0 : conflictLit1;
      }
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

  /**
   * Returns the reason of an assigned variable, first asking the external propagator for it when
   * the variable was implied by it: the clause is then kept as a learnt one up to {@link
   * #setExternalReasonKeep} literals, and is temporary beyond.
   */
  private int reasonRef(int v) {
    int r = reason[v];
    if (r != EXTERNAL_REASON) {
      return r;
    }
    int lit = vals[2 * v] > 0 ? 2 * v : 2 * v + 1;
    int[] dimacs = external.reason(toDimacs(lit));
    int[] c = new int[dimacs.length];
    int size = 0;
    boolean found = false;
    for (int d : dimacs) {
      int l = toLit(d);
      if (l == lit) {
        found = true;
      } else if (vals[l] >= 0 || trailPos[l >> 1] > trailPos[v]) {
        throw new IllegalStateException(
            "reason of " + toDimacs(lit) + " has " + d + " not false before it");
      }
      c[size++] = l;
    }
    if (!found) {
      throw new IllegalStateException("reason does not contain " + toDimacs(lit));
    }
    Arrays.sort(c, 0, size);
    int n = 0;
    for (int i = 0; i < size; i++) {
      if (n == 0 || c[n - 1] != c[i]) {
        c[n++] = c[i];
      }
    }
    c = Arrays.copyOf(c, n);
    if (n == 1) {
      r = UNIT_REASON;
    } else {
      orderForWatches(c);
      if (n == 2) {
        addLearntBinary(c[0], c[1]);
        notifyKept(c, n);
        r = -2 - c[1];
      } else if (n <= externalReasonKeep) {
        r = allocate(c, n, true, n);
        learnts = push(learnts, numLearnts++, r);
        attach(r);
        notifyKept(c, n);
      } else {
        r = allocate(c, n, false, n);
        mem[r + META] |= TEMPORARY;
      }
    }
    reason[v] = r;
    return r;
  }

  private void notifyKept(int[] c, int n) {
    if (notifying) {
      for (int i = 0; i < n; i++) {
        external.notifyKeptLiteral(toDimacs(c[i]));
      }
    }
  }

  /** First-UIP analysis of the current conflict into {@code learnt}; returns the backjump level. */
  private int analyze() {
    learntSize = 0;
    addLearnt(0);
    toClearSize = 0;
    int pathCount = 0;
    int p = -1;
    int index = trailSize - 1;
    int ref = conflictRef;
    do {
      if (ref == UNIT_REASON) {
        // an external reason without other literals: p holds in every model
      } else if (p == -1 && ref == BINARY_CONFLICT) {
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
      if (notifying && pathCount >= 2 && groupsOpen == 1 && ungroupedOpen == 0) {
        int uip = semanticUip(index, pathCount);
        if (uip >= 0) {
          p = uip;
          break;
        }
      }
      p = trail[index--];
      ref = reasonRef(p >> 1);
      seen[p >> 1] = 0;
      pathCount--;
      if (notifying) {
        closeFrontier(p >> 1);
      }
    } while (pathCount > 0);
    learnt[0] = p ^ 1;

    // recursive minimisation
    if (++poisonStamp == Integer.MAX_VALUE) {
      Arrays.fill(poisonMark, 0);
      poisonStamp = 1;
    }
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
    if (notifying && learntSize > 1) {
      minimizeExternally();
    }

    for (int i = 0; i < toClearSize; i++) {
      seen[toClear[i]] = 0;
    }
    seen[learnt[0] >> 1] = 0;
    learntLiterals += learntSize;
    if (notifying) {
      for (int i = 0; i < learntSize; i++) {
        external.notifyLearntLiteral(toDimacs(learnt[i]));
      }
    }

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

  /** Counts a conflict-level literal of the analysis under its integer variable. */
  private void openFrontier(int v) {
    int g = external.integerVariable(v + 1);
    if (g < 0) {
      ungroupedOpen++;
      return;
    }
    if (g >= groupOpen.length) {
      groupOpen = Arrays.copyOf(groupOpen, Math.max(2 * groupOpen.length, g + 1));
    }
    if (groupOpen[g]++ == 0) {
      groupsOpen++;
    }
  }

  /** Uncounts a conflict-level literal resolved away by the analysis. */
  private void closeFrontier(int v) {
    int g = external.integerVariable(v + 1);
    if (g < 0) {
      ungroupedOpen--;
    } else if (--groupOpen[g] == 0) {
      groupsOpen--;
    }
  }

  /**
   * A semantic UIP: when the open conflict-level literals are all atoms of one integer variable,
   * the external propagator may name a true conflict-level literal equivalent to their conjunction,
   * which then cuts the conflict like a UIP (the 1UIP over integer variables of Pumpkin's CPIP).
   * Returns that literal, with the analysis state cleared, or -1.
   */
  private int semanticUip(int index, int open) {
    if (frontier.length < open) {
      frontier = new int[2 * open];
    }
    int n = 0;
    for (int t = index; n < open; t--) {
      int v = trail[t] >> 1;
      if (seen[v] != 0 && level[v] == decisionLevel) {
        frontier[n++] = toDimacs(trail[t]);
      }
    }
    int d = external.semanticUip(frontier, n);
    if (d == 0) {
      return -1;
    }
    int lit = toLit(d);
    if (vals[lit] <= 0 || level[lit >> 1] != decisionLevel) {
      return -1;
    }
    for (int k = 0; k < n; k++) {
      int v = Math.abs(frontier[k]) - 1;
      seen[v] = 0;
      closeFrontier(v);
    }
    semanticUips++;
    return lit;
  }

  /** Lets the external propagator remove learnt literals that imply others it knows about. */
  private void minimizeExternally() {
    if (dimacsLearnt.length < learntSize) {
      dimacsLearnt = new int[learnt.length];
    }
    for (int i = 0; i < learntSize; i++) {
      dimacsLearnt[i] = toDimacs(learnt[i]);
    }
    int kept = external.minimizeLearnt(dimacsLearnt, learntSize);
    if (kept < learntSize) {
      semanticallyRemoved += learntSize - kept;
      for (int i = 0; i < kept; i++) {
        learnt[i] = toLit(dimacsLearnt[i]);
      }
      learntSize = kept;
    }
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
      int r = reasonRef(v);
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
      if (notifying) {
        openFrontier(v);
      }
      return 1;
    }
    addLearnt(q);
    return 0;
  }

  /**
   * Whether literal p of the learnt clause is implied by the other literals (MiniSat's test). The
   * search is depth first and remembers both outcomes for the rest of the conflict, as CaDiCaL
   * does: a literal shown removable is marked seen, and one that is not is poisoned. MiniSat
   * forgets the failures, so every learnt literal could walk the same implication graph again;
   * under LCG each step asks for a lazy explanation, and city-position spent over 30 s in one
   * minimisation.
   */
  private boolean redundant(int p, int abstractLevels) {
    return antecedentsRemovable(p >> 1, abstractLevels, 0);
  }

  private boolean antecedentsRemovable(int v, int abstractLevels, int depth) {
    int r = reasonRef(v);
    if (r == UNIT_REASON) {
      return true;
    }
    if (r < NO_REASON) {
      return removable(-2 - r, abstractLevels, depth + 1);
    }
    int size = mem[r + SIZE];
    for (int k = 1; k < size; k++) {
      // mem is read again each time: explaining an antecedent may reallocate it
      if (!removable(mem[r + HEADER + k], abstractLevels, depth + 1)) {
        return false;
      }
    }
    return true;
  }

  private boolean removable(int q, int abstractLevels, int depth) {
    int v = q >> 1;
    if (seen[v] != 0 || level[v] == 0 || reason[v] == UNIT_REASON) {
      return true;
    }
    if (poisonMark[v] == poisonStamp
        || reason[v] == NO_REASON
        || ((1 << (level[v] & 31)) & abstractLevels) == 0
        || depth > MINIMIZE_DEPTH) {
      return false;
    }
    if (antecedentsRemovable(v, abstractLevels, depth)) {
      seen[v] = 1;
      markClear(v);
      return true;
    }
    poisonMark[v] = poisonStamp;
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
      int r = reasonRef(x);
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
          addLearntBinary(c[0], c[1]);
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
      nextReduce = conflicts + reduceBase + reduceInc * ++reductions;
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

  private void addLearntBinary(int a, int b) {
    addBinary(a, b);
    learntBinaries = push(learntBinaries, numLearntBinaries++, a);
    learntBinaries = push(learntBinaries, numLearntBinaries++, b);
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
      int confl = propagateAll();
      if (!ok) {
        return UNSAT;
      }
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
        if (wasted > (1 << 20) && wasted > memSize / 2) {
          purge(); // temporary external reasons freed by the backtrack
        }
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
        if (conflicts >= nextElimination
            && elimination
            && eliminationInterval > 0
            && !externalUsed
            && numUnits == 0) {
          nextElimination = conflicts + (long) eliminationInterval * ++eliminationRounds;
          if (!eliminate()) {
            return UNSAT;
          }
        }
        continue;
      }
      if (conflicts >= nextReduce) {
        nextReduce = conflicts + reduceBase + reduceInc * ++reductions;
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
      if (next == -1 && external != null) {
        int d = external.decide();
        if (d != 0 && Math.abs(d) <= numVars) {
          int l = toLit(d);
          next = vals[l] == 0 && !eliminatedVar[l >> 1] ? l : -1;
        }
      }
      if (next == -1) {
        next = pickBranch();
        if (next == -1) {
          if (external != null && !modelAccepted()) {
            continue;
          }
          return SAT;
        }
      }
      // under an external propagator one decision can take milliseconds: read the clock on each
      if (((++decisions & 1023) == 0 || external != null)
          && (interrupted || System.nanoTime() > deadline)) {
        return UNKNOWN;
      }
      newDecisionLevel();
      assign(next, NO_REASON);
    }
  }

  /** Asks the external propagator to check the complete assignment. */
  private boolean modelAccepted() {
    int[] m = new int[numVars];
    for (int v = 0; v < numVars; v++) {
      m[v] = vals[2 * v] > 0 ? v + 1 : -(v + 1);
    }
    if (external.checkModel(m)) {
      return true;
    }
    queuedExternal = external.externalClause();
    if (queuedExternal == null) {
      throw new IllegalStateException("the propagator rejected a model without giving a clause");
    }
    return false;
  }

  /**
   * Unit propagation together with the external propagator: its clauses and propagations are taken
   * one at a time, each followed by unit propagation, until neither has more.
   *
   * @return a conflict (as {@link #propagate}), or NO_CONFLICT; ok is false when the formula is
   *     found unsatisfiable
   */
  private int propagateAll() {
    while (true) {
      int confl = propagate();
      if (confl != NO_CONFLICT || external == null) {
        return confl;
      }
      for (int i = 0; i < numLateObserved; i++) {
        int v = lateObserved[i];
        if (vals[2 * v] != 0 && trailPos[v] < notified) {
          int l = 2 * v + (vals[2 * v] > 0 ? 0 : 1);
          external.notifyAssignment(toDimacs(l), level[v] == 0);
        }
      }
      numLateObserved = 0;
      for (; notified < trailSize; notified++) {
        int l = trail[notified];
        if (observed[l >> 1]) {
          external.notifyAssignment(toDimacs(l), level[l >> 1] == 0);
        }
      }
      int[] c = queuedExternal;
      queuedExternal = null;
      if (c == null) {
        c = external.externalClause();
      }
      int implied = -1;
      if (c == null) {
        int lit = external.propagate();
        while (lit != 0 && vals[toLit(lit)] > 0) {
          lit = external.propagate();
        }
        if (lit == 0) {
          return NO_CONFLICT;
        }
        implied = toLit(lit);
        if (vals[implied] == 0) {
          assign(implied, EXTERNAL_REASON);
          continue;
        }
        c = external.reason(lit);
      }
      confl = addExternal(c, implied);
      if (confl != NO_CONFLICT || !ok) {
        return confl;
      }
    }
  }

  /**
   * Adds a clause from the external propagator during search: a reason of the literal implied (kept
   * as a learnt clause) or, with implied = -1, a clause it adds (kept as an original one).
   * Backtracks when the clause is false below the current level, and asserts it when it is unit.
   *
   * @return a conflict, with at least two literals at the (new) current level, or NO_CONFLICT
   */
  private int addExternal(int[] dimacs, int implied) {
    int[] c = new int[dimacs.length];
    for (int i = 0; i < c.length; i++) {
      if (dimacs[i] == 0 || Math.abs(dimacs[i]) > numVars) {
        throw new IllegalArgumentException("literal " + dimacs[i] + " of an external clause");
      }
      c[i] = toLit(dimacs[i]);
      if (eliminatedVar[c[i] >> 1]) {
        throw new IllegalStateException("external clause on unobserved eliminated variable");
      }
    }
    Arrays.sort(c);
    int size = 0;
    for (int l : c) {
      if (size > 0 && c[size - 1] == (l ^ 1)) {
        return NO_CONFLICT; // a tautology
      }
      if (size == 0 || c[size - 1] != l) {
        c[size++] = l;
      }
    }
    c = Arrays.copyOf(c, size);
    if (implied >= 0) {
      boolean found = false;
      for (int l : c) {
        found |= l == implied;
        if (l != implied && vals[l] >= 0) {
          throw new IllegalStateException("reason of " + toDimacs(implied) + " is not unit");
        }
      }
      if (!found) {
        throw new IllegalStateException("reason does not contain " + toDimacs(implied));
      }
    }
    if (proof != null) {
      proof.add(c, 0, size);
    }
    if (implied >= 0) {
      notifyKept(c, size);
    }
    if (size <= 1) {
      backtrack(0);
      if (size == 0 || vals[c[0]] < 0) {
        ok = false;
      } else if (vals[c[0]] == 0) {
        assign(c[0], NO_REASON);
      }
      return NO_CONFLICT;
    }
    orderForWatches(c);
    int ref = BINARY;
    if (size == 2) {
      if (implied >= 0) {
        addLearntBinary(c[0], c[1]);
      } else {
        addOriginalBinary(c[0], c[1]);
      }
    } else if (implied >= 0) {
      ref = allocate(c, size, true, size);
      learnts = push(learnts, numLearnts++, ref);
      attach(ref);
    } else {
      ref = allocate(c, size, false, 0);
      originals = push(originals, numOriginals++, ref);
      attach(ref);
    }
    int top = level[c[0] >> 1];
    if (vals[c[0]] > 0 || vals[c[1]] >= 0) {
      return NO_CONFLICT;
    }
    if (vals[c[0]] == 0) {
      assign(c[0], ref == BINARY ? -2 - c[1] : ref);
      return NO_CONFLICT;
    }
    if (top == 0) {
      ok = false;
      return NO_CONFLICT;
    }
    if (level[c[1] >> 1] < top) {
      // only c[0] is false at its level: it is implied one level lower
      backtrack(top - 1);
      assign(c[0], ref == BINARY ? -2 - c[1] : ref);
      return NO_CONFLICT;
    }
    backtrack(top);
    qhead = trailSize;
    conflictRef = ref == BINARY ? BINARY_CONFLICT : ref;
    conflictLit0 = c[0];
    conflictLit1 = c[1];
    return conflictRef;
  }

  /**
   * Connects an external propagator to the following {@link #solve} calls (one at a time). Its
   * variables must be declared with {@link #observe}. Chronological backtracking is off while it is
   * connected.
   *
   * @param propagator the propagator, or null to disconnect
   */
  public void connect(ExternalPropagator propagator) {
    backtrack(0);
    external = propagator;
    notified = 0;
  }

  /**
   * Declares a variable that the external propagator observes: it is never eliminated, and its
   * assignments are notified.
   *
   * @param variable a DIMACS variable
   */
  public void observe(int variable) {
    ensureVars(variable);
    if (eliminatedVar[variable - 1]) {
      restoreEliminated();
    }
    int v = variable - 1;
    if (!observed[v] && vals[2 * v] != 0 && trailPos[v] < notified) {
      lateObserved = push(lateObserved, numLateObserved++, v);
    }
    observed[v] = true;
  }

  /**
   * Takes an unassigned variable that occurs in no clause out of the decisions, so its index can be
   * given to another variable with {@link #reuse}. The caller keeps it out of clauses meanwhile.
   *
   * @param variable a DIMACS variable
   */
  public void retire(int variable) {
    int v = variable - 1;
    if (vals[2 * v] != 0 || binSize[2 * v] != 0 || binSize[2 * v + 1] != 0) {
      throw new IllegalStateException(
          "variable " + variable + " is assigned or in a binary clause");
    }
    order.remove(v);
  }

  /**
   * Gives a retired variable a fresh start, as if it were new: no activity, the initial phase and a
   * place among the decisions.
   *
   * @param variable a DIMACS variable passed to {@link #retire}
   */
  public void reuse(int variable) {
    int v = variable - 1;
    reason[v] = NO_REASON;
    activity[v] = 0;
    savedSign[v] = 0;
    targetSign[v] = -1;
    bestSign[v] = 0;
    order.insert(v);
  }

  /**
   * Tells whether the solver writes a proof, in which a variable keeps one meaning.
   *
   * @return true with a proof writer
   */
  public boolean hasProof() {
    return proof != null;
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
    Walker walker = new Walker(numVars, lits, start, n, phases, ++walks + 1_000_003L * seed);
    walker.run(10_000_000L + (propagations - propagationsAtWalk) / 5);
    propagationsAtWalk = propagations;
    System.arraycopy(walker.best(), 0, savedSign, 0, numVars);
    walkNanos += System.nanoTime() - begin;
  }

  /**
   * Sets the random seed, which changes the initial decision order and the local search. Set it
   * before adding clauses; 0 (the default) keeps the order of the variables.
   *
   * @param seed the seed
   */
  public void setSeed(long seed) {
    this.seed = seed;
  }

  /**
   * Sets how often elimination runs again during search, after its first run before the search.
   *
   * @param conflicts the conflicts before the first round (later rounds are further apart), or 0
   *     for no rounds during search (default 5000)
   */
  public void setEliminationInterval(int conflicts) {
    eliminationInterval = conflicts;
    nextElimination = conflicts;
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
      addLearntBinary(learnt[0], learnt[1]);
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
    emaFastBeta *= 1 - 0.03;
    emaSlowBeta *= 1 - 1e-5;
    emaFast += (lbd - emaFast) * 0.03;
    emaSlow += (lbd - emaSlow) * 1e-5;
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
    if (!restartsOn || decisionLevel <= assumptions.length) {
      return false;
    }
    if (conflicts >= modeSwitchAt || conflicts >= nextRephase) {
      return true; // mode switches and rephasing happen at restarts, which may be rare otherwise
    }
    if (stable) {
      return conflicts - conflictsAtRestart >= lubyLimit;
    }
    if (emaRestarts) {
      double fast = emaFast / (1 - emaFastBeta);
      double slow = emaSlow / (1 - emaSlowBeta);
      return conflicts - conflictsAtRestart >= 2 && fast > 1.1 * slow;
    }
    return lbdQueueSize == lbdQueue.length
        && conflicts > 0
        && (double) lbdQueueSum / lbdQueueSize * 0.8 > (double) lbdSum / conflicts;
  }

  private void restart() {
    restarts++;
    backtrack(0);
    if (external != null) {
      external.notifyRestart();
    }
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
    boolean[] frozen = Arrays.copyOf(observed, numVars);
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
    boolean[] gone = e.eliminated();
    numOriginalBinaries = 0;
    Arrays.fill(watchSize, 0);
    Arrays.fill(binSize, 0);
    if (sat) {
      keepLearnts(gone);
    }
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
    for (int v = 0; v < numVars; v++) {
      eliminatedVar[v] |= gone[v];
    }
    numEliminated += e.numEliminated();
    int[] removed = e.stack();
    int old = extension.length;
    extension = Arrays.copyOf(extension, old + removed.length);
    System.arraycopy(removed, 0, extension, old, removed.length);
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

  /**
   * After elimination: deletes the learnt clauses on eliminated variables or satisfied at level 0
   * and attaches the others again (all watch lists were cleared).
   */
  private void keepLearnts(boolean[] gone) {
    for (int i = 0; i < numLearnts; i++) {
      int ref = learnts[i];
      if ((mem[ref + META] & DELETED) != 0) {
        continue;
      }
      int size = mem[ref + SIZE];
      int lits = ref + HEADER;
      boolean drop = false;
      for (int k = 0; k < size && !drop; k++) {
        int l = mem[lits + k];
        drop = gone[l >> 1] || vals[l] > 0;
      }
      if (drop) {
        deleteClause(ref);
        continue;
      }
      int[] c = Arrays.copyOfRange(mem, lits, lits + size);
      orderForWatches(c);
      System.arraycopy(c, 0, mem, lits, size);
      mem[ref + POS] = 2;
      attach(ref);
    }
    int j = 0;
    for (int i = 0; i < numLearntBinaries; i += 2) {
      int a = learntBinaries[i];
      int b = learntBinaries[i + 1];
      if (gone[a >> 1] || gone[b >> 1] || vals[a] > 0 || vals[b] > 0) {
        if (proof != null) {
          proof.delete(learntBinaries, i, 2);
        }
        continue;
      }
      addBinary(a, b);
      learntBinaries[j++] = a;
      learntBinaries[j++] = b;
    }
    numLearntBinaries = j;
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
    boolean wasNotifying = notifying;
    notifying = false; // the probing levels of vivification are internal
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
    notifying = wasNotifying;
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
      addLearntBinary(d[0], d[1]);
      return true;
    }
    int copy = allocate(d, n, true, Math.min(lbdOf(meta), n - 1));
    mem[copy + META] |= VIVIFIED;
    mem[copy + ACT] = mem[ref + ACT];
    learnts = push(learnts, numLearnts++, copy);
    attach(copy);
    return true;
  }

  /**
   * Sets the LBD limits of the learnt clause tiers: clauses up to {@code core} are kept for good,
   * those up to {@code mid} survive a reduction while they are used (2 and 6 by default).
   *
   * @param core the largest LBD of the core tier
   * @param mid the largest LBD of the middle tier, at least {@code core}
   */
  public void setTierLimits(int core, int mid) {
    coreLbd = core;
    midLbd = Math.max(core, mid);
  }

  /** Reduces the learnt clauses after this many conflicts and then more often, for tests. */
  void setReduceBase(int conflicts) {
    reduceBase = conflicts;
    reduceInc = Math.max(1, conflicts * 3 / 20);
    nextReduce = conflicts;
    eliminationInterval = 2 * conflicts;
    nextElimination = eliminationInterval;
  }

  /**
   * Turns vivification of learnt clauses on or off (on by default).
   *
   * @param on whether to vivify
   */
  public void setVivification(boolean on) {
    vivification = on;
  }

  /**
   * Chooses the restart rule in focused mode: CaDiCaL's fast and slow moving averages of the LBD
   * (the default) or Glucose's queue of the last 50 LBDs.
   *
   * @param on whether to use the moving averages
   */
  public void setEmaRestarts(boolean on) {
    emaRestarts = on;
  }

  /**
   * Turns restarts on or off (on by default). Without restarts the search only backjumps, so
   * decisions given by an external propagator are kept in their order down each branch.
   *
   * @param on false to never restart
   */
  public void setRestarts(boolean on) {
    restartsOn = on;
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
        if ((mem[ref + META] & DELETED) == 0) {
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
        if ((mem[ref + META] & DELETED) == 0) {
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
