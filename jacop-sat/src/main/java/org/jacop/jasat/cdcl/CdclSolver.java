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
import java.util.function.LongSupplier;

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

  // clause header: three ints, the saved search position shares META with the flags and the LBD
  private static final int SIZE = 0;
  private static final int META = 1;
  private static final int ACT = 2;
  private static final int HEADER = 3;

  // META bits; LBD in the bits from LBD_SHIFT, the saved search position from POS_SHIFT
  private static final int LEARNT_FLAG = 1;
  private static final int DELETED = 2;
  private static final int USED = 4;
  private static final int VIVIFIED = 32;
  // set only in the old arena by compact(), on a clause already copied to the new one
  private static final int MOVED = 64;
  private static final int TIER_SHIFT = 3;
  private static final int TIER_MASK = 3 << TIER_SHIFT;
  private static final int LBD_SHIFT = 8;
  private static final int MAX_LBD = 255;
  private static final int POS_SHIFT = 16;
  private static final int MAX_POS = 0xFFFF;
  private static final int NOT_POS = (1 << POS_SHIFT) - 1;
  // META of a fresh clause: the search for a replacement watch starts at the third literal
  private static final int POS_START = 2 << POS_SHIFT;

  private static final int TIER_CORE = 0;
  private static final int TIER_MID = 1;
  private static final int TIER_LOCAL = 2;
  private int coreLbd = 2;
  private int midLbd = 6;

  // --- variables and assignment
  private int numVars;
  private byte[] vals = new byte[0];
  // per variable v, one record of VREC ints at v << 2: its decision level, reason, trail position
  // and the seen mark of conflict analysis and minimisation (0 or 1). An assignment writes one
  // cache line, and analysis reads one line per variable instead of one per array (as Kissat's
  // struct assigned and CaDiCaL's Var). 16 bytes keep a record inside one line.
  private static final int LEVEL = 0;
  private static final int REASON = 1;
  private static final int TPOS = 2;
  private static final int SEEN = 3;
  private static final int VREC = 4;
  private int[] vdata = new int[0];
  private byte[] savedSign = new byte[0];
  private byte originalSign; // the initial phase: 0 for true, 1 for false
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
  // feasibility-jump local search (JumpSearch): its share of the solver's clock, its search, the
  // formula it was built for, its time so far and where the clock started
  private double jumpShare = DEFAULT_JUMP_SHARE;
  private JumpSearch jumper;
  // the formula of the local search when bounded variable addition is undone in it
  private JumpSearch.Unfactored jumpUnfactored;
  private long jumpSignature = -1;
  private int jumperClauses;
  private static final boolean JUMP_DEBUG = Boolean.getBoolean("jacop.jasat.jumpDebug");
  private long jumpStart = Long.MIN_VALUE;
  private long jumpWork;
  long jumpNanos;
  int jumpCalls;
  int jumpModels;
  // the model of the local search that the decisions follow, until a conflict
  private byte[] jumpPhases;
  private boolean jumpSolved;

  // chronological backtracking is used in this search (solve() without assumptions)
  private boolean chrono;
  // backtrack chronologically when a backjump would undo more levels than this; negative: never
  private int chronoLimit = 100;
  // with an external propagator, backtrack one level instead of backjumping when the backjump
  // would undo more levels than this, asserting the learnt literal at the level kept; negative:
  // never
  private int lazyChronoLimit = -1;
  // the conflicts that backtracked one level instead of backjumping
  public long lazyChronoBacktracks;
  private int targetAssigned;
  private double[] activity = new double[0];

  /** Whether the analysed variables besides the learnt ones go to the external propagator. */
  private boolean analysedNotify;

  /** Per variable: the conflict stamp of the last {@link #notifyAnalysed} that named it. */
  private int[] analysedMark = new int[0];

  private int analysedStamp;

  private final VarHeap order = new VarHeap();

  // --- the VMTF decision queue of focused mode (CaDiCaL, Kissat), used when vmtf is on: a doubly
  // linked list of the variables in the order of their last bump, the most recent last. Each
  // variable carries the stamp of its last bump, and qSearch is a variable from which every later
  // one in the queue is assigned (or eliminated), so a decision walks back from it.
  private boolean vmtf;
  private int[] qPrev = new int[0];
  private int[] qNext = new int[0];
  private long[] qStamp = new long[0];
  private int qFirst = -1;
  private int qLast = -1;
  private int qSearch = -1;
  private long qBumped;
  private int[] qToBump = new int[16];
  private int qToBumpSize;
  private long[] qKeys = new long[16];

  private int[] trail = new int[0];
  private int trailSize;
  private int qhead;
  private int[] trailLim = new int[16];
  // qhead when each level was opened: the external search may open a level before propagating
  // (units asserted again by a backtrack), and those literals are propagated again after a
  // backtrack to the level they were assigned at
  private int[] qheadLim = new int[16];
  private int decisionLevel;

  // --- clauses
  private int[] mem = new int[1 << 16];
  private int memSize;
  private int wasted;

  // --- temporary external reasons: a stack beside the arena, with the arena's clause layout and
  // the variable explained in META. A reason refers to one as STACK_REF + its offset. It is dead
  // once its variable has another reason; dead ones are popped off the top, or compacted away.
  private static final int STACK_REF = 1 << 30;
  private int[] rstack = new int[1 << 12];
  private int rtop;
  private int rwasted;
  // start offset of each reason on the stack, bottom first
  private int[] rstarts = new int[64];
  private int numRstarts;
  // the literals of the reason being taken from the external propagator
  private int[] reasonBuf = new int[16];
  private int[] originals = new int[64];
  private int numOriginals;
  private int[] learnts = new int[64];
  private int numLearnts;
  // the watch lists of a literal no clause has watched yet (empty: the end in slot 0 is 1), shared
  // and never written
  private static final int[] NO_WATCHES = {1};
  private static final long[] NO_LONG_WATCHES = {1};

  // per literal: slot 0 holds the end of the list, then one long per watched clause from slot 1,
  // the clause in the high half and the blocking literal in the low half (see watch): a visit reads
  // and keeps a watch with one load and one store, and the end shares a cache line with the array
  // header, so adding a watch touches one line fewer
  private long[][] watches = new long[0][];
  // per literal: slot 0 holds the end of the list, then the other literals of binary clauses
  private int[][] binWatches = new int[0][];
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
  private boolean stableForGood;
  private long conflictsAtRestart;
  private int lubyIndex;
  private long lubyLimit;
  // conflicts of one unit of the Luby sequence in stable mode
  private static final long LUBY_UNIT = Long.getLong("jacop.jasat.lubyUnit", 512L);
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
  // A reduction is also made, at most every MEMORY_REDUCE_GAP conflicts, when the learnt clauses
  // take more than LEARNT_HEAP_SHARE of the heap: under lazy clause generation a diagram given as
  // clauses (MagicSquare-mdd-10, XCSP 2023: 4.4 million literals) made learnt clauses of 4,000
  // literals on average, mostly in the core tier, and 6,000 conflicts ran a 6 GB heap out of memory
  // (12 GB a little later) when the arena of 870 MB grew by half; the growth needs the old and the
  // new arena at once.
  private static final double LEARNT_HEAP_SHARE = 1.0 / 16;
  private static final int MEMORY_REDUCE_GAP = 16;
  private long learntBudget =
      (long) (LEARNT_HEAP_SHARE * Runtime.getRuntime().maxMemory()) / Integer.BYTES;
  private long nextMemoryCheck;
  // the bytes that elimination and local search may take for their copies of the clauses
  private long copyBudget = Runtime.getRuntime().maxMemory() / 4;
  // vivification of learnt clauses at the next restart, after each reduction
  private boolean vivification = true;
  private boolean vivifyDue;
  private long propagationsAtVivify;
  private int[] vivifyLits = new int[16];
  // scheduled vivification of irredundant clauses and of every learnt tier (Li et al. 2020,
  // Kissat 4): used without an external propagator, which keeps the learnt-only rounds above
  private boolean vivifySorted = !"false".equals(System.getProperty("jacop.jasat.vivifySorted"));
  private boolean vivifyIrredundant = !"false".equals(System.getProperty("jacop.jasat.vivifyIrr"));
  // effort of a round in per mille of the propagations of the search since the last round
  private int vivifyEffort = Integer.getInteger("jacop.jasat.vivifyEffort", 100);
  // relative effort of the core, middle and local learnt tiers and of the irredundant clauses
  private final int[] vivifyWeights = {
    Integer.getInteger("jacop.jasat.vivifyCore", 3),
    Integer.getInteger("jacop.jasat.vivifyMid", 3),
    Integer.getInteger("jacop.jasat.vivifyLocal", 1),
    Integer.getInteger("jacop.jasat.vivifyIrrWeight", 3)
  };
  private boolean vivifyKeepPhases =
      !"false".equals(System.getProperty("jacop.jasat.vivifyKeepPhases"));
  private boolean vivifyRetry = !"false".equals(System.getProperty("jacop.jasat.vivifyRetry"));
  private boolean vivifyDropImplied =
      !"false".equals(System.getProperty("jacop.jasat.vivifyDropImplied"));
  private boolean vivifyInstantiate = !"false".equals(System.getProperty("jacop.jasat.vivifyInst"));
  private static final int TIER_IRREDUNDANT = 3;
  // rounds of irredundant vivification skipped after rounds that strengthened under 1 %
  private int vivifyIrrDelay;
  private int vivifyIrrSkip;
  // the clause being vivified, which propagation skips; -1 outside vivification
  private int ignoredRef = -1;
  // backtracking leaves the saved phases alone (vivification probes are not search)
  private boolean keepPhases;
  // per literal: 1 while it is a literal of the clause being vivified
  private byte[] vivifyMark = new byte[0];
  // per variable: analysed by the conflict analysis of vivification
  private boolean[] vivifySeen = new boolean[0];
  private int[] vivifyAnalysed = new int[16];
  private int numVivifyAnalysed;
  private int[] vivifyOut = new int[16];
  private int numVivifyOut;
  private int[] vivifyCounts = new int[0];
  // sorted keys of the original binary clauses, built for the irredundant round
  private long[] originalBinaryKeys;

  /** Vivification statistics: candidates tried. */
  public long vivifyTried;

  /** Vivification statistics: irredundant candidates tried. */
  public long vivifyTriedIrredundant;

  /** Vivification statistics: time spent in scheduled vivification rounds. */
  public long vivifyNanos;

  /** Vivification statistics: decisions reused from the previous candidate's probe. */
  public long vivifyReused;

  /** Vivification statistics: decisions made by probes. */
  public long vivifyProbes;

  /** Vivification statistics: clauses strengthened (literals removed). */
  public long vivifyStrengthened;

  /** Vivification statistics: irredundant clauses strengthened. */
  public long vivifyStrengthenedIrredundant;

  /** Vivification statistics: clauses removed as subsumed, implied or asymmetric tautologies. */
  public long vivifyRemoved;

  /** Vivification statistics: irredundant clauses removed. */
  public long vivifyRemovedIrredundant;

  private static final long REPHASE_INTERVAL = 1000;

  /**
   * The default share of the solver's clock given to the feasibility-jump local search ({@link
   * #setJumpShare}), system property {@code jacop.jasat.jump}.
   */
  public static final double DEFAULT_JUMP_SHARE =
      Double.parseDouble(System.getProperty("jacop.jasat.jump", "0.1"));

  // the shortest slice of the local search worth starting, in nanoseconds of the clock
  private static final long MIN_JUMP_SLICE = 20_000_000L;

  // ticks of the local search (visited occurrences and literals) that count as one unit of work:
  // the search visits 35 to 155 million a second (tree-decomposition, sgen of SAT Comp 2024),
  // the virtual clock counts 2 million units of work a second
  private static final long JUMP_TICKS_PER_WORK = 32;
  private int simplifyAssigns = -1;
  // propagations before the next simplification, as MiniSat's simpDB_props: a pass costs about the
  // size of the arena and the watch lists, so it waits for as much propagation work
  private long simplifyProps;

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
  // clauses added or asserted above the level where they became unit: a watch is true (or
  // asserted) at a higher level than the other, false, watch, so a backtrack between the two
  // levels leaves them unit without a watch to visit; triples (reference, literal, literal), the
  // literals only for a binary clause (reference BINARY), checked again after each backtrack
  private int[] lowWatched = new int[24];
  private int numLowWatched;
  private boolean lowWatchedDue;

  // --- lucky assignments before the first search (see lucky())
  private boolean lucky = true;
  private boolean luckyTried;

  /** Statistics: time spent in the lucky assignments, in nanoseconds. */
  public long luckyNanos;

  /**
   * Statistics: the lucky assignment that found a model ("all-true", "all-false", "forward-false",
   * "forward-true", "backward-false", "backward-true"), or null when none did.
   */
  public String luckyFound;

  // --- variable elimination before the first search (see Eliminator)
  private boolean elimination = true;
  // equivalent-literal substitution before elimination (see Congruence), and congruence closure
  // on gates in it
  private boolean substitution = !"false".equals(System.getProperty("jacop.jasat.substitute"));
  private boolean congruence = !"false".equals(System.getProperty("jacop.jasat.congruence"));
  // gate extraction runs again at a later elimination only if the last one found a gate
  private boolean gatesPaid = true;

  /** Statistics: variables replaced by an equivalent literal. */
  public long substitutedVars;

  /** Statistics: equivalences found in the binary implication graph. */
  public long sccEquivalences;

  /** Statistics: equivalences found by congruence closure. */
  public long gateEquivalences;

  /** Statistics: gates extracted for congruence closure. */
  public long gatesFound;

  /** Statistics: time spent in substitution and congruence closure. */
  public long substitutionNanos;

  private boolean eliminationTried;
  private boolean externalUsed;
  private boolean[] eliminatedVar = new boolean[0];
  private int numEliminated;
  private int[] extension = new int[0];
  // elimination rounds during search, at restarts
  private long nextElimination = 5000;
  private int eliminationInterval = 5000;
  private int eliminationRounds;
  // the elimination bound reached so far, the largest one, and the longest resolvent
  private int eliminationBound;
  private int maxEliminationBound = 16;
  private int resolventLimit = 100;
  private boolean eliminationGates = true;
  int gateEliminations;
  // time spent in elimination
  long eliminationNanos;
  // after a round that eliminated nothing: the root trail and irredundant clause counts it saw;
  // the next round during search waits until one of them grows
  private boolean eliminationFruitless;
  private int eliminationTrail;
  private int eliminationOriginals;
  private long seed;

  // inprocessing statistics per round on standard output
  private static final boolean VERBOSE = Boolean.getBoolean("jacop.jasat.verbose");

  // --- SAT sweeping (see Sweeper), at each elimination round
  private boolean sweeping;
  private boolean[] sweepDone = new boolean[0];
  private int sweepCompleted;
  private long propagationsAtSweep;
  private static final long SWEEP_FIRST_EFFORT =
      Long.getLong("jacop.jasat.sweepFirst", 100_000_000);
  private static final long SWEEP_MIN_EFFORT = Long.getLong("jacop.jasat.sweepMin", 20_000_000);
  private int sweepRounds;
  private int sweepDelay;
  private int sweepDelayLimit;
  private static final int SWEEP_EFFORT_PER_MILLE = 100;

  // --- failed-literal probing, at each elimination round
  private boolean probing;
  private int probeCursor;
  private long propagationsAtProbe;
  private static final long PROBE_MIN_EFFORT = 1_000_000;
  private static final int PROBE_EFFORT_PER_MILLE = 50;

  /** Statistics: propagations of failed-literal probing, not counted in {@link #propagations}. */
  public long probePropagations;

  /** Statistics: literals probed. */
  public long probedLiterals;

  /** Statistics: failed literals found by probing (each gives a unit). */
  public long failedLiterals;

  /** Statistics: units implied by both a probed literal and its negation. */
  public long liftedUnits;

  /** Statistics: equivalences found by probing both signs of a literal. */
  public long probeEquivalences;

  /** Statistics: time spent probing, in nanoseconds. */
  public long probeNanos;

  /** Statistics: units found by SAT sweeping. */
  public long sweepUnits;

  /** Statistics: literal equivalences found by SAT sweeping. */
  public long sweepEquivalences;

  /** Statistics: variables swept. */
  public long sweptVariables;

  /** Statistics: time spent sweeping, in nanoseconds. */
  public long sweepNanos;

  // --- bounded variable addition before the first elimination (see Factorizer)
  private boolean factoring;
  private boolean factored;
  // the variables above this one are fresh variables of the factorizer
  private int factorBase = Integer.MAX_VALUE;
  private long factorEffort = Factorizer.EFFORT_LIMIT;
  // restoreEliminated adds back clauses on fresh variables too
  private boolean restoring;

  /** Statistics: fresh variables added by bounded variable addition. */
  public int factoredVars;

  /** Statistics: clauses removed by bounded variable addition, net of the added ones. */
  public long factoredClauses;

  /** Statistics: time spent in bounded variable addition. */
  public long factorNanos;

  /** Statistics: effort spent in bounded variable addition (see {@link #setFactorEffort}). */
  public long factorWork;

  // --- external propagator (see ExternalPropagator)
  private ExternalPropagator external;
  private int externalReasonKeep = 2;
  // the next decision below the first one is notified to the external propagator as a top
  // decision too
  private boolean notifyNext;
  private boolean[] observed = new boolean[0];
  // the trail prefix whose observed assignments the propagator has seen
  private int notified;
  // the propagator is told about levels and assignments (only in the search of solve())
  private boolean notifying;
  private int[] queuedExternal;
  // learnt clauses up to this size and LBD go to the propagator's notifyLearnt (0: none)
  private int exportSize;
  private int exportLbd;
  // variables observed after they were assigned, notified at the next propagation
  private int[] lateObserved = new int[4];
  private int numLateObserved;

  // --- assumptions and model
  private int[] assumptions = new int[0];
  // all assumptions on decision level 1, kept at restarts (Hickey and Bacchus, SAT 2019); otherwise
  // assumption i is the decision of level i + 1
  private boolean assumptionsOnOneLevel = true;
  // the decision levels the assumptions take: 1 (or 0 without assumptions) on one level
  private int assumptionLevels;
  // on one level: the index of the next assumption to take on level 1
  private int assumptionNext;
  private int[] failed = new int[0];
  private boolean[] model = new boolean[0];

  // --- limits, proof, statistics
  private volatile boolean interrupted;
  // set by cancel(): every later solve() stops at once as well
  private volatile boolean cancelled;
  // set when propagateAll stopped at the deadline before reaching a fixpoint
  private boolean outOfTime;
  private long deadline = Long.MAX_VALUE;
  // the work (see work()) at which solve stops, and the work of the external propagator
  private long workLimit = Long.MAX_VALUE;
  private LongSupplier externalWork = () -> 0;
  private long conflictLimit = Long.MAX_VALUE;
  private ProofOutput proof;
  // the root facts at the start of the trail that the proof has as units of their own
  private int rootFactsLogged;
  // tests: check the propagation invariants at every fixpoint (see checkFixpoint)
  private boolean checking = Boolean.getBoolean("jacop.jasat.check");

  /** Number of conflicts so far. */
  public long conflicts;

  /** Number of decisions so far. */
  public long decisions;

  /** Number of propagated literals so far. */
  public long propagations;

  /** Number of restarts so far. */
  public long restarts;

  /**
   * Statistics: the decision levels of the conflicts that were analysed, summed. Divided by the
   * conflicts, the mean depth of a conflict.
   */
  public long conflictLevels;

  /**
   * Statistics: the levels the first-UIP clauses of the analysed conflicts jump back over, summed
   * (before any chronological backtracking shortens a jump). A search that learns nothing useful
   * jumps back about one level per conflict, as depth-first search without learning does.
   */
  public long backjumpLevels;

  /**
   * Statistics: the deepest decision level the search opened, assumption levels included. Probing
   * and clause vivification open levels of their own; they do not count.
   */
  public int peakDecisionLevel;

  /** Number of learnt clause database reductions so far. */
  public long reductions;

  /** Statistics: reductions of the learnt clauses made because they took too much of the heap. */
  public long memoryReductions;

  /** Statistics: literals of the learnt clauses, after minimisation. */
  public long learntLiterals;

  /** Statistics: learnt literals the external propagator removed as implied by others. */
  public long semanticallyRemoved;

  /** Statistics: conflicts whose analysis stopped at a semantic UIP before the first UIP. */
  public long semanticUips;

  /**
   * Statistics: the LBD of the learnt clauses, summed.
   *
   * @return the sum of the LBDs of the clauses learnt so far
   */
  public long lbdSum() {
    return lbdSum;
  }

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
    int cap = vdata.length / VREC;
    if (n > cap) {
      int c = Math.max(n, 2 * cap);
      vals = Arrays.copyOf(vals, 2 * c);
      vdata = Arrays.copyOf(vdata, VREC * c);
      savedSign = Arrays.copyOf(savedSign, c);
      targetSign = Arrays.copyOf(targetSign, c);
      bestSign = Arrays.copyOf(bestSign, c);
      activity = Arrays.copyOf(activity, c);
      analysedMark = Arrays.copyOf(analysedMark, c);
      trail = Arrays.copyOf(trail, c);
      shrinkMark = Arrays.copyOf(shrinkMark, c);
      poisonMark = Arrays.copyOf(poisonMark, c);
      eliminatedVar = Arrays.copyOf(eliminatedVar, c);
      observed = Arrays.copyOf(observed, c);
      watches = Arrays.copyOf(watches, 2 * c);
      binWatches = Arrays.copyOf(binWatches, 2 * c);
    }
    if (qPrev.length < n || qNext.length < n || qStamp.length < n) { // grown together
      int c = Math.max(n, 2 * qPrev.length);
      qPrev = Arrays.copyOf(qPrev, c);
      qNext = Arrays.copyOf(qNext, c);
      qStamp = Arrays.copyOf(qStamp, c);
    }
    order.grow(n, activity);
    for (int v = n - 1; v >= numVars; v--) {
      queueAppend(v); // the first variable last, so decided first
      qSearch = v;
    }
    for (int v = numVars; v < n; v++) {
      vdata[v << 2 | REASON] = NO_REASON;
    }
    // the initial phase, true (sign 0) by default as in CaDiCaL
    Arrays.fill(savedSign, numVars, n, originalSign);
    Arrays.fill(targetSign, numVars, n, (byte) -1);
    Arrays.fill(bestSign, numVars, n, originalSign);
    if (seed != 0) {
      // a different initial decision order for each seed
      SplittableRandom random = new SplittableRandom(seed + numVars);
      for (int v = numVars; v < n; v++) {
        activity[v] = random.nextDouble() * 1e-3; // NOSONAR: activity holds n variables, see above
      }
    }
    // a literal gets its watch lists when a clause first watches it: under LCG most literals are
    // atoms in no clause, and four small arrays each filled a 3 GB heap on a 4096-variable alldiff
    Arrays.fill(watches, 2 * numVars, 2 * n, NO_LONG_WATCHES);
    Arrays.fill(binWatches, 2 * numVars, 2 * n, NO_WATCHES);
    for (int v = numVars; v < n; v++) {
      order.insert(v);
    }
    numVars = n;
  }

  /**
   * Returns the number of literals assigned at decision level 0: the root facts, which learnt units
   * add to during search.
   *
   * @return the number of root literals.
   */
  public int rootAssignments() {
    return decisionLevel == 0 ? trailSize : trailLim[0];
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
    if (!restoring) {
      checkNotFresh(maxVar);
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
    checkNotFresh(maxVar);
    ensureVars(maxVar);
    assumptions = new int[assumed.length];
    for (int i = 0; i < assumed.length; i++) {
      assumptions[i] = toLit(assumed[i]);
      if (eliminatedVar[assumptions[i] >> 1]) {
        restoreEliminated();
      }
    }
    assumptionLevels = assumptionsOnOneLevel ? Math.min(1, assumptions.length) : assumptions.length;
    interrupted = cancelled;
    outOfTime = false;
    backtrack(0);
    // lucky assignments before and after elimination (Kissat's luckyearly and luckylate), in the
    // first plain search only
    boolean luckyNow =
        lucky && !luckyTried && assumptions.length == 0 && external == null && !externalUsed;
    luckyTried |= luckyNow;
    int luckyResult = luckyNow ? lucky() : UNKNOWN;
    if (luckyResult == UNSAT) {
      return UNSAT;
    }
    if (luckyResult == UNKNOWN
        && elimination
        && !eliminationTried
        && conflicts == 0
        && !externalUsed
        && numUnits == 0) {
      eliminationTried = true;
      if (!eliminate()) {
        return UNSAT;
      }
      if (luckyNow && numEliminated > 0) {
        luckyResult = lucky();
        if (luckyResult == UNSAT) {
          return UNSAT;
        }
      }
    }
    // chronological backtracking would assign literals below the current level, which the level
    // notifications of an external propagator cannot express
    chrono = chronoLimit >= 0 && assumptions.length == 0 && external == null;
    notifying = external != null;
    int result;
    try {
      result = luckyResult == SAT ? SAT : search();
      if (result == SAT && luckyResult != SAT && jumpPhases != null) {
        jumpSolved = true;
      }
      if (result == SAT) {
        model = new boolean[numVars];
        for (int v = 0; v < numVars; v++) {
          model[v] = vals[2 * v] > 0;
        }
        Eliminator.extend(extension, model);
      }
      backtrack(0);
    } finally {
      jumpPhases = null;
      chrono = false;
      notifying = false;
      queuedExternal = null;
    }
    return result;
  }

  /**
   * Probes a literal at the root: assigns it at a new level and propagates, the external propagator
   * included, then goes back to the root. Nothing is learnt.
   *
   * @param lit a DIMACS literal
   * @return the literals it implies, in the order assigned; null when it leads to a conflict, so
   *     its negation holds in every solution; empty when it is already true at the root, or when
   *     the deadline stops the propagation of the root
   */
  public int[] probe(int lit) {
    if (!ok) {
      return null;
    }
    ensureVars(Math.abs(lit));
    backtrack(0);
    int l = toLit(lit);
    if (vals[l] != 0) {
      return vals[l] > 0 ? new int[0] : null;
    }
    notifying = external != null;
    try {
      // the root first, as a search starts, so that only the literal's consequences are undone
      if (propagateAll() != NO_CONFLICT) {
        ok = false;
        return null;
      }
      if (outOfTime) {
        // the root is not at its fixpoint: a decision now would take the rest of the root's
        // consequences to its level, and they would be undone with it
        outOfTime = false;
        return new int[0];
      }
      if (vals[l] != 0) {
        return vals[l] > 0 ? new int[0] : null;
      }
      newDecisionLevel();
      int start = trailSize;
      assign(l, NO_REASON);
      int conflict = propagateAll();
      if (decisionLevel == 0) {
        // a clause of the external propagator asserted a literal at the root and undid the
        // probe's level: the literal implies nothing more than the root, and a conflict now is
        // one of the root, which refutes the formula
        if (conflict != NO_CONFLICT) {
          ok = false;
        }
        return ok ? new int[0] : null;
      }
      if (conflict != NO_CONFLICT || !ok) {
        backtrack(0);
        return null;
      }
      int[] implied = new int[trailSize - start - 1];
      for (int i = start + 1; i < trailSize; i++) {
        implied[i - start - 1] = toDimacs(trail[i]);
      }
      backtrack(0);
      return implied;
    } finally {
      notifying = false;
      queuedExternal = null;
    }
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
   * Stops a running {@link #solve}, as {@link #interrupt()}, and every later call of it, which
   * returns {@link #UNKNOWN}; safe from another thread.
   */
  public void cancel() {
    cancelled = true;
    interrupted = true;
  }

  /** Takes back {@link #cancel()}: later calls of {@link #solve} run again. */
  public void uncancel() {
    cancelled = false;
    interrupted = false;
  }

  /**
   * Whether the clock of the solver is virtual (system property {@code jacop.virtualClock}): {@link
   * #now} then counts {@link #work}, {@link #VIRTUAL_WORK_PER_MS} per millisecond, instead of
   * reading the system clock, so that a run with a time limit stops at the same point and makes the
   * same choices whatever the load of the machine. It is meant for benchmarks that compare two
   * versions of the search: the wall time a run takes then differs from its limit.
   */
  public static final boolean VIRTUAL_CLOCK = Boolean.getBoolean("jacop.virtualClock");

  /**
   * The work that counts as one millisecond of the virtual clock (system property {@code
   * jacop.lcg.workPerMs}, the same rate at which lazy clause generation turns time shares into
   * work).
   */
  public static final long VIRTUAL_WORK_PER_MS = Long.getLong("jacop.lcg.workPerMs", 2_000);

  /**
   * Returns the time of the solver's clock: {@link System#nanoTime()}, or under {@link
   * #VIRTUAL_CLOCK} the work done so far in nanoseconds of the virtual clock. Deadlines and other
   * times given to the solver are times of this clock.
   *
   * @return the time in nanoseconds
   */
  public long now() {
    if (virtualClock) {
      return work() * 1_000_000L / VIRTUAL_WORK_PER_MS;
    }
    return System.nanoTime();
  }

  /**
   * Returns a clock that goes on reading like {@link #now} once the solver has stopped, without
   * holding the solver: the virtual clock keeps the solver's own work as it is now and goes on
   * counting the external work. The caller can then drop the solver and its clauses.
   *
   * @return the clock, in nanoseconds
   */
  public LongSupplier stoppedClock() {
    LongSupplier work = externalWork;
    if (!virtualClock) {
      return System::nanoTime;
    }
    long own = propagations;
    return () -> (own + work.getAsLong()) * 1_000_000L / VIRTUAL_WORK_PER_MS;
  }

  /**
   * Turns the virtual clock of this solver on or off; it is on by default under {@link
   * #VIRTUAL_CLOCK}. Set it before the deadline, which is a time of {@link #now}.
   *
   * @param on true for the virtual clock, false for {@link System#nanoTime()}
   */
  public void setVirtualClock(boolean on) {
    virtualClock = on;
  }

  private boolean virtualClock = VIRTUAL_CLOCK;

  /**
   * Runs an action once, at the first check of the deadline at or after the given time of {@link
   * #now}; the action may {@link #interrupt} the search. Under {@link #VIRTUAL_CLOCK} it takes the
   * place of a thread that sleeps, whose wake-up would depend on the machine.
   *
   * @param nanoTime the time of {@link #now} at which the action runs
   * @param action the action
   */
  public void setAlarm(long nanoTime, Runnable action) {
    alarmAt = nanoTime;
    alarm = action;
  }

  private long alarmAt = Long.MAX_VALUE;
  private Runnable alarm;

  // the deadline check of the search loop: runs a due alarm first, which may stop the search
  private boolean pastDeadline() {
    long now = now();
    if (now >= alarmAt) {
      alarmAt = Long.MAX_VALUE;
      alarm.run();
    }
    return interrupted || now > deadline;
  }

  /**
   * Sets a deadline for {@link #solve}, a time of {@link #now}.
   *
   * @param nanoTime a time of {@link #now}, or {@link Long#MAX_VALUE} for none
   */
  public void setDeadline(long nanoTime) {
    deadline = nanoTime;
  }

  /**
   * Returns the deadline of {@link #solve}.
   *
   * @return a time of {@link #now}, or {@link Long#MAX_VALUE} for none
   */
  public long deadline() {
    return deadline;
  }

  /**
   * Limits the work of {@link #solve}, a measure of the search that does not depend on the clock:
   * the propagated literals plus the external propagator's work (see {@link #setExternalWork}). It
   * is checked at conflicts and decisions, so a search stops at the same point in every run.
   *
   * @param limit the work at which {@link #solve} returns {@link #UNKNOWN}, or {@link
   *     Long#MAX_VALUE} for none
   */
  public void setWorkLimit(long limit) {
    workLimit = limit;
  }

  /**
   * Returns the limit of the work.
   *
   * @return the work at which {@link #solve} returns {@link #UNKNOWN}
   */
  public long workLimit() {
    return workLimit;
  }

  /**
   * Sets the external propagator's share of {@link #work}.
   *
   * @param work its work so far, which never decreases
   */
  public void setExternalWork(LongSupplier work) {
    externalWork = work;
  }

  /**
   * Returns the work so far: the propagated literals plus the external propagator's work.
   *
   * @return the work so far
   */
  public long work() {
    return propagations + externalWork.getAsLong() + jumpWork;
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
   * Returns the limit of the total number of conflicts.
   *
   * @return the conflict count at which {@link #solve} returns {@link #UNKNOWN}
   */
  public long conflictLimit() {
    return conflictLimit;
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
   * Sets when {@link #solve}, with an external propagator and without assumptions, backtracks one
   * level instead of backjumping. The learnt clause's asserting literal is then assigned at the
   * level kept, above the levels of the clause's other literals, and the clause is remembered so
   * that a later backtrack between those levels asserts it again (the missed lower implications of
   * A. Nadel and V. Ryvchin, "Chronological Backtracking", SAT 2018, LNCS 10929, handled lazily, as
   * in A. Möhle and A. Biere, "Backing Backtracking", SAT 2019, LNCS 11628). The literals are not
   * assigned out of order, which the level notifications of the external propagator could not
   * express. A search that follows a fixed order of decisions otherwise redoes, after each
   * backjump, every decision between the backjump level and the conflict.
   *
   * @param limit the backjump length above which search backtracks one level, 0 for always, or a
   *     negative number for never (default)
   */
  public void setLazyChronoLimit(int limit) {
    lazyChronoLimit = limit;
  }

  /**
   * Sets where {@link #solve} puts its assumptions. On one level (the default), all of them are
   * assigned at decision level 1, in order and each propagated before the next, and restarts go
   * back to level 1, so the assumptions and their consequences are not propagated again after every
   * restart (R. Hickey and F. Bacchus, "Speeding Up Assumption-Based SAT", SAT 2019, LNCS 11628). A
   * conflict at level 1 makes the assumptions unsatisfiable, with the assumptions it depends on as
   * the core. Restarts that vivify or eliminate still go back to level 0. Otherwise each assumption
   * is the decision of its own level, as in MiniSat, and restarts go back to level 0. Assigning all
   * of them before propagating, as the paper does, made LCG explanations about seven times longer
   * on ptv and is not done.
   *
   * @param on whether the assumptions share one decision level
   */
  public void setAssumptionsOnOneLevel(boolean on) {
    assumptionsOnOneLevel = on;
  }

  /**
   * Sets whether the external propagator hears, through {@link
   * ExternalPropagator#notifyAnalysedLiteral}, of every variable a conflict analysis resolved or
   * minimised away besides the learnt clause's ones, as MiniSat bumps them (N. Eén, N. Sörensson,
   * An Extensible SAT-solver, SAT 2003). Off by default.
   *
   * @param on whether to tell the propagator of the analysed variables
   */
  public void setAnalysedNotify(boolean on) {
    analysedNotify = on;
  }

  /**
   * Notifies the next decision below the first one under the assumptions to the external propagator
   * too, with {@link ExternalPropagator#notifyTopDecision}: for a propagator that could not use the
   * decision it was told about (a split on a variable it does not share). Decisions on assumptions
   * are never notified.
   */
  public void notifyNextDecision() {
    notifyNext = true;
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
   * Passes each clause learnt from now on that has at most the given size and LBD to the external
   * propagator's {@link ExternalPropagator#notifyLearnt}, for other solvers to import.
   *
   * @param size the largest clause passed; 0 turns it off
   * @param lbd the largest LBD passed
   */
  public void setLearntExport(int size, int lbd) {
    exportSize = Math.max(0, size);
    exportLbd = lbd;
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
   * Turns SAT sweeping on or off (off by default). When on, each elimination round (see {@link
   * #setElimination}) first sweeps variables as Kissat does (see {@link Sweeper}): the clauses
   * around a variable are solved by a small sub-solver to find units and equivalent literals, which
   * are added as unit and binary clauses. It spends about a tenth of the propagations of the search
   * since the last round.
   *
   * @param on whether to sweep
   */
  public void setSweeping(boolean on) {
    sweeping = on;
  }

  /**
   * Turns failed-literal probing on or off (off by default). When on, each elimination round (see
   * {@link #setElimination}) first probes the roots of the binary implication graph at level 0: a
   * literal whose propagation conflicts gives the unit of the conflict's first UIP; the literals
   * implied by both signs of a probed variable are units, and a literal implied by one sign whose
   * negation the other sign implies is equivalent to it (added as binary clauses).
   *
   * @param on whether to probe
   */
  public void setProbing(boolean on) {
    probing = on;
  }

  /**
   * Turns equivalent-literal substitution on or off: before each variable elimination, the
   * equivalences of the binary implication graph and, with {@link #setCongruence}, of congruent
   * gates replace their literals (see {@link Congruence}). On by default (system property {@code
   * jacop.jasat.substitute}); it runs only where elimination runs.
   *
   * @param on whether to substitute
   */
  public void setSubstitution(boolean on) {
    substitution = on;
  }

  /**
   * Turns congruence closure on AND, XOR and ITE gates in the substitution on or off. On by default
   * (system property {@code jacop.jasat.congruence}).
   *
   * @param on whether to look for congruent gates
   */
  public void setCongruence(boolean on) {
    congruence = on;
  }

  /**
   * Turns bounded variable addition on or off (off by default). It runs once, in the first {@link
   * #solve} call, just before the first variable elimination (so only with elimination on), and it
   * adds fresh variables above {@link #numInputVars()}: a model of the new formula is one of the
   * input formula on the input variables. A clause or an assumption on a variable above them is an
   * error afterwards, so it suits one-shot solving such as {@link CdclMain}, not a caller that adds
   * variables between calls. See {@link Factorizer}.
   *
   * @param on whether to add variables
   */
  public void setFactoring(boolean on) {
    factoring = on;
  }

  /**
   * Sets the effort (clause and occurrence visits) bounded variable addition may spend.
   *
   * @param effort the effort limit
   */
  public void setFactorEffort(long effort) {
    factorEffort = effort;
  }

  /**
   * Returns the number of variables of the input formula: {@link #numVars()} without the fresh
   * variables of bounded variable addition.
   *
   * @return the largest input DIMACS variable
   */
  public int numInputVars() {
    return Math.min(numVars, factorBase);
  }

  private void checkNotFresh(int maxVar) {
    if (maxVar > factorBase) {
      throw new IllegalStateException(
          "variable " + maxVar + " is a fresh variable of bounded variable addition");
    }
  }

  /**
   * Writes a proof of every derived and deleted clause, such as a {@link DratWriter}. Set it before
   * adding clauses.
   *
   * @param writer the proof output, or null for none
   */
  public void setProof(ProofOutput writer) {
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

  /**
   * Returns the DIMACS literal of an internal literal, as a {@link ProofOutput} gets them.
   *
   * @param lit the internal literal
   * @return its DIMACS literal
   */
  public static int toDimacs(int lit) {
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
        (isLearnt ? LEARNT_FLAG : 0)
            | (tier << TIER_SHIFT)
            | (Math.min(lbd, MAX_LBD) << LBD_SHIFT)
            | POS_START;
    mem[ref + ACT] = Float.floatToRawIntBits(0f);
    System.arraycopy(lits, 0, mem, ref + HEADER, size);
    memSize += need;
    return ref;
  }

  /** A watch of clause ref with a blocking literal, as stored in the watch lists. */
  private static long watch(int blocker, int ref) {
    return (long) ref << 32 | blocker;
  }

  private static int watchRef(long w) {
    return (int) (w >>> 32);
  }

  private static int watchBlocker(long w) {
    return (int) w;
  }

  private void addWatch(int lit, int blocker, int ref) {
    long[] ws = watches[lit];
    int n = (int) ws[0];
    if (n == ws.length) {
      ws = Arrays.copyOf(ws, Math.max(3, 2 * n - 1));
      watches[lit] = ws;
    }
    ws[n] = watch(blocker, ref);
    ws[0] = n + 1L;
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
    int n = ws[0];
    if (n == ws.length) {
      ws = Arrays.copyOf(ws, 2 * n + 1);
      binWatches[lit] = ws;
    }
    ws[n] = other;
    ws[0] = n + 1;
  }

  private boolean isLocked(int ref) {
    int l0 = mem[ref + HEADER];
    return vals[l0] > 0 && varReason(l0 >> 1) == ref;
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
    return (meta >>> LBD_SHIFT) & MAX_LBD;
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
    int r = (lit >> 1) << 2;
    vals[lit] = 1;
    vals[lit ^ 1] = -1;
    vdata[r | LEVEL] = lvl;
    vdata[r | REASON] = why;
    vdata[r | TPOS] = trailSize;
    trail[trailSize++] = lit;
  }

  /**
   * Returns the decisions of the current assignment: the literals assigned without a reason above
   * the root, in the order of the trail.
   *
   * @return the decision literals, in DIMACS form
   */
  public int[] decisionLiterals() {
    int[] out = new int[decisionLevel];
    int n = 0;
    for (int k = decisionLevel == 0 ? trailSize : trailLim[0]; k < trailSize; k++) {
      int lit = trail[k];
      if (varReason(lit >> 1) == NO_REASON && litLevel(lit) > 0) {
        if (n == out.length) {
          out = Arrays.copyOf(out, 2 * n + 1);
        }
        out[n++] = toDimacs(lit);
      }
    }
    return Arrays.copyOf(out, n);
  }

  /** The decision level of variable v (meaningful while v is assigned). */
  private int varLevel(int v) {
    return vdata[v << 2 | LEVEL];
  }

  /** The decision level of the variable of internal literal lit. */
  private int litLevel(int lit) {
    return vdata[(lit >> 1) << 2 | LEVEL];
  }

  /** The reason of variable v: NO_REASON, UNIT_REASON, a clause reference or a stack reference. */
  private int varReason(int v) {
    return vdata[v << 2 | REASON];
  }

  /** The position of variable v on the trail (meaningful while v is assigned). */
  private int varTrailPos(int v) {
    return vdata[v << 2 | TPOS];
  }

  private void newDecisionLevel() {
    if (decisionLevel >= trailLim.length) {
      trailLim = Arrays.copyOf(trailLim, 2 * decisionLevel + 2);
      qheadLim = Arrays.copyOf(qheadLim, trailLim.length);
    }
    qheadLim[decisionLevel] = qhead;
    trailLim[decisionLevel++] = trailSize;
    if (notifying) {
      external.notifyNewDecisionLevel();
    }
  }

  /** Opens a decision level of the search and records the peak depth. */
  private void newSearchLevel() {
    newDecisionLevel();
    if (decisionLevel > peakDecisionLevel) {
      peakDecisionLevel = decisionLevel;
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
      if (varLevel(v) <= target) {
        // assigned out of order below the target level (chronological backtracking): stays
        vdata[v << 2 | TPOS] = kept;
        trail[kept++] = lit;
        continue;
      }
      vals[lit] = 0;
      vals[lit ^ 1] = 0;
      int r = varReason(v);
      if (r >= STACK_REF) {
        rwasted += HEADER + rstack[r - STACK_REF + SIZE];
        vdata[v << 2 | REASON] = NO_REASON;
        if (proof != null) {
          proof.delete(rstack, r - STACK_REF + HEADER, rstack[r - STACK_REF + SIZE]);
        }
      }
      if (!keepPhases) {
        savedSign[v] = (byte) (lit & 1);
      }
      order.insert(v);
      if (qSearch < 0 || qStamp[v] > qStamp[qSearch]) {
        qSearch = v;
      }
    }
    trailSize = kept;
    qhead = Math.min(start, qheadLim[target]);
    decisionLevel = target;
    if (rwasted > 0) {
      releaseReasons();
    }
    notified = Math.min(notified, kept);
    if (notifying) {
      external.notifyBacktrack(target);
    }
    lastAssumedLevel = Math.min(lastAssumedLevel, target);
    reassertUnits();
    lowWatchedDue = numLowWatched > 0;
  }

  // ----------------------------------------------------------------------------- propagation

  private int propagate() {
    if (lowWatchedDue) {
      lowWatchedDue = false;
      int c = propagateLowWatched();
      if (c != NO_CONFLICT) {
        return c;
      }
    }
    int conflict = NO_CONFLICT;
    final byte[] localVals = this.vals;
    final int[] localMem = this.mem;
    while (qhead < trailSize) {
      int falseLit = trail[qhead++] ^ 1;
      propagations++;
      int[] bs = binWatches[falseLit];
      for (int b = bs[0] - 1; b > 0; b--) {
        int other = bs[b];
        int ov = localVals[other];
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
          assignAt(other, -2 - falseLit, litLevel(falseLit));
        } else {
          assign(other, -2 - falseLit);
        }
      }
      long[] ws = watches[falseLit];
      int n = (int) ws[0];
      int i = 1;
      int j = 1;
      while (i < n) {
        long wt = ws[i++];
        int blocker = watchBlocker(wt);
        if (localVals[blocker] > 0) {
          if (j != i - 1) {
            ws[j] = wt; // kept in place while no watch has left the list
          }
          j++;
          continue;
        }
        int ref = watchRef(wt);
        if (ref == ignoredRef) {
          // the clause vivification is testing takes no part in its probes
          ws[j++] = wt;
          continue;
        }
        int lits = ref + HEADER;
        if (localMem[lits] == falseLit) {
          localMem[lits] = localMem[lits + 1];
          localMem[lits + 1] = falseLit;
        }
        int first = localMem[lits];
        int fv = localVals[first];
        if (first != blocker && fv > 0) {
          ws[j++] = watch(first, ref);
          continue;
        }
        int size = localMem[ref + SIZE];
        int meta = localMem[ref + META];
        int pos = meta >>> POS_SHIFT;
        int k = pos;
        int found = -1;
        for (; k < size; k++) {
          if (localVals[localMem[lits + k]] >= 0) {
            found = k;
            break;
          }
        }
        if (found < 0) {
          for (k = 2; k < pos; k++) {
            if (localVals[localMem[lits + k]] >= 0) {
              found = k;
              break;
            }
          }
        }
        if (found >= 0) {
          // a position past 16 bits (clauses over 65,535 literals) keeps the old start
          if (found != pos && found <= MAX_POS) {
            localMem[ref + META] = (meta & NOT_POS) | (found << POS_SHIFT);
          }
          int w = localMem[lits + found];
          localMem[lits + 1] = w;
          localMem[lits + found] = falseLit;
          addWatch(w, first, ref);
          continue;
        }
        ws[j++] = watch(first, ref);
        if (fv < 0) {
          conflict = ref;
          break;
        }
        if (chrono) {
          // no level is above the current one: stop at the first literal there (usually falseLit)
          int lvl = 0;
          for (k = 1; k < size && lvl < decisionLevel; k++) {
            lvl = Math.max(lvl, litLevel(localMem[lits + k]));
          }
          assignAt(first, ref, lvl);
        } else {
          assign(first, ref);
        }
      }
      if (conflict != NO_CONFLICT) {
        if (j == i) {
          // nothing moved: the rest of the list stays as it is
          j = n;
        } else {
          while (i < n) {
            ws[j++] = ws[i++];
          }
        }
        if (j != n) {
          ws[0] = j;
        }
        qhead = trailSize;
        conflictRef = conflict;
        return conflict;
      }
      if (j != n) {
        ws[0] = j;
      }
    }
    return NO_CONFLICT;
  }

  /**
   * Remembers a clause whose two watched literals a and b are one true and one false at a lower
   * level: after a backtrack between the two levels it is unit, and no watch would visit it.
   */
  private void noteLowWatched(int ref, int a, int b) {
    int t = vals[a] > 0 ? a : b;
    int f = t == a ? b : a;
    if (vals[t] <= 0 || vals[f] >= 0 || litLevel(t) <= litLevel(f)) {
      return;
    }
    if (numLowWatched + 3 > lowWatched.length) {
      lowWatched = Arrays.copyOf(lowWatched, 2 * lowWatched.length);
    }
    lowWatched[numLowWatched++] = ref;
    lowWatched[numLowWatched++] = ref == BINARY ? a : -1;
    lowWatched[numLowWatched++] = ref == BINARY ? b : -1;
  }

  /** As noteLowWatched for a clause of the arena, or a binary one given by its two literals. */
  private void noteLowWatched(int ref, int[] c) {
    if (ref >= 0) {
      noteLowWatched(ref, mem[ref + HEADER], mem[ref + HEADER + 1]);
    } else if (c.length == 2) {
      noteLowWatched(BINARY, c[0], c[1]);
    }
  }

  /**
   * After a backtrack, visits the clauses of noteLowWatched: one that became unit asserts its
   * literal, one whose false watch has a replacement is watched again, and one still at risk is
   * kept.
   *
   * @return a conflict, or NO_CONFLICT
   */
  private int propagateLowWatched() {
    int j = 0;
    int conflict = NO_CONFLICT;
    for (int i = 0; i < numLowWatched; i += 3) {
      int ref = lowWatched[i];
      int a = lowWatched[i + 1];
      int b = lowWatched[i + 2];
      if (conflict == NO_CONFLICT) {
        if (ref >= 0) {
          if ((mem[ref + META] & DELETED) != 0) {
            continue;
          }
          conflict = visitLowWatched(ref);
          a = mem[ref + HEADER];
          b = mem[ref + HEADER + 1];
        } else {
          conflict = visitLowWatched(a, b);
        }
        if (conflict == NO_CONFLICT && !atRisk(a, b)) {
          continue;
        }
      }
      lowWatched[j++] = ref;
      lowWatched[j++] = ref >= 0 ? -1 : a;
      lowWatched[j++] = ref >= 0 ? -1 : b;
    }
    numLowWatched = j;
    if (conflict != NO_CONFLICT) {
      qhead = trailSize;
    }
    return conflict;
  }

  private boolean atRisk(int a, int b) {
    int t = vals[a] > 0 ? a : b;
    int f = t == a ? b : a;
    return vals[t] > 0 && vals[f] < 0 && litLevel(t) > litLevel(f);
  }

  private int visitLowWatched(int a, int b) {
    if (vals[a] < 0 && vals[b] < 0) {
      conflictRef = BINARY_CONFLICT;
      conflictLit0 = a;
      conflictLit1 = b;
      return BINARY_CONFLICT;
    }
    if (vals[a] < 0 && vals[b] == 0) {
      assign(b, -2 - a);
    } else if (vals[b] < 0 && vals[a] == 0) {
      assign(a, -2 - b);
    }
    return NO_CONFLICT;
  }

  private int visitLowWatched(int ref) {
    int lits = ref + HEADER;
    int size = mem[ref + SIZE];
    // both watches may be false: literals can be assigned between the backtrack and this visit
    for (int w = 0; w < 2; w++) {
      int falseLit = mem[lits + w];
      if (vals[falseLit] >= 0) {
        continue;
      }
      for (int k = 2; k < size; k++) {
        int l = mem[lits + k];
        if (vals[l] >= 0) {
          mem[lits + w] = l;
          mem[lits + k] = falseLit;
          removeWatch(falseLit, ref);
          addWatch(l, mem[lits + 1 - w], ref);
          break;
        }
      }
    }
    int w0 = mem[lits];
    int w1 = mem[lits + 1];
    if (vals[w0] < 0 && vals[w1] < 0) {
      conflictRef = ref;
      return ref;
    }
    if (vals[w0] < 0) {
      // the false watch second, as propagate keeps it
      mem[lits] = w1;
      mem[lits + 1] = w0;
    }
    if (vals[mem[lits]] == 0 && vals[mem[lits + 1]] < 0) {
      assign(mem[lits], ref);
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
    if (queueInUse()) {
      if (qToBumpSize == qToBump.length) {
        qToBump = Arrays.copyOf(qToBump, 2 * qToBumpSize);
      }
      qToBump[qToBumpSize++] = v; // and bumped in the heap too, for the next stable phase
    }
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
      int l = litLevel(a[i]);
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
        meta = (meta & ~(MAX_LBD << LBD_SHIFT) & ~TIER_MASK) | (newTier << TIER_SHIFT);
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
      int l = litLevel(lit);
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
      assignAt(forced, -2 - other, litLevel(other));
    } else {
      rewatch(ref);
      int lvl = 0;
      for (int k = 1; k < size; k++) {
        lvl = Math.max(lvl, litLevel(mem[lits + k]));
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
    int r = varReason(v);
    if (r != EXTERNAL_REASON) {
      return r;
    }
    int lit = vals[2 * v] > 0 ? 2 * v : 2 * v + 1;
    int[] dimacs = external.reason(toDimacs(lit));
    if (dimacs.length > reasonBuf.length) {
      reasonBuf = new int[Math.max(dimacs.length, 2 * reasonBuf.length)];
    }
    int[] c = reasonBuf;
    int size = 0;
    boolean found = false;
    for (int d : dimacs) {
      int l = toLit(d);
      if (l == lit) {
        found = true;
      } else if (vals[l] >= 0 || varTrailPos(l >> 1) > varTrailPos(v)) {
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
    if (proof != null) {
      proof.add(c, 0, n);
    }
    if (n == 1) {
      r = UNIT_REASON;
    } else {
      orderForWatches(c, n);
      if (n <= externalReasonKeep && notifying && REASON_UNKEPT && hasUnkeptLiteral(c, n)) {
        // kept, it would make the literal permanent and lengthen the chain of its variable
        unkeptReasons++;
        r = pushReason(v, c, n);
      } else if (n == 2) {
        addLearntBinary(c[0], c[1]);
        notifyKept(c, n);
        noteLowWatched(BINARY, c[0], c[1]);
        r = -2 - c[1];
      } else if (n <= externalReasonKeep) {
        r = allocate(c, n, true, n);
        learnts = push(learnts, numLearnts++, r);
        attach(r);
        notifyKept(c, n);
        noteLowWatched(r, c[0], c[1]);
      } else {
        r = pushReason(v, c, n);
      }
    }
    vdata[v << 2 | REASON] = r;
    return r;
  }

  /** Whether one of the first n literals of c is one the external propagator does not keep. */
  private boolean hasUnkeptLiteral(int[] c, int n) {
    for (int i = 0; i < n; i++) {
      if (external.unkept((c[i] >> 1) + 1)) {
        return true;
      }
    }
    return false;
  }

  private void notifyKept(int[] c, int n) {
    if (notifying) {
      for (int i = 0; i < n; i++) {
        external.notifyKeptLiteral(toDimacs(c[i]));
      }
    }
  }

  /** Pushes the temporary reason of variable v on the reason stack; returns its reference. */
  private int pushReason(int v, int[] lits, int size) {
    int need = HEADER + size;
    if (rtop + need > rstack.length) {
      rstack = Arrays.copyOf(rstack, Math.max(rtop + need, 2 * rstack.length));
    }
    int off = rtop;
    rstack[off + SIZE] = size;
    rstack[off + META] = v;
    System.arraycopy(lits, 0, rstack, off + HEADER, size);
    rtop += need;
    rstarts = push(rstarts, numRstarts++, off);
    return STACK_REF + off;
  }

  private boolean reasonLive(int off) {
    return varReason(rstack[off + META]) == STACK_REF + off;
  }

  /**
   * Frees the reasons of unassigned variables: pops the dead ones off the top of the stack, and
   * compacts the stack once most of it is dead.
   */
  private void releaseReasons() {
    while (numRstarts > 0 && !reasonLive(rstarts[numRstarts - 1])) {
      int off = rstarts[--numRstarts];
      rwasted -= rtop - off;
      rtop = off;
    }
    if (numRstarts == 0) {
      rtop = 0;
      rwasted = 0;
    } else if (rwasted > rtop / 2) {
      int top = 0;
      int j = 0;
      for (int i = 0; i < numRstarts; i++) {
        int off = rstarts[i];
        if (reasonLive(off)) {
          int len = HEADER + rstack[off + SIZE];
          System.arraycopy(rstack, off, rstack, top, len);
          vdata[rstack[top + META] << 2 | REASON] = STACK_REF + top;
          rstarts[j++] = top;
          top += len;
        }
      }
      numRstarts = j;
      rtop = top;
      rwasted = 0;
    }
  }

  /** The array holding reason clause r: the arena, or the reason stack. */
  private int[] reasonArena(int r) {
    return r >= STACK_REF ? rstack : mem;
  }

  /** The offset of reason clause r in {@link #reasonArena}. */
  private static int reasonOffset(int r) {
    return r >= STACK_REF ? r - STACK_REF : r;
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
      } else if (ref >= STACK_REF) {
        int lits = ref - STACK_REF + HEADER;
        int size = rstack[lits - HEADER + SIZE];
        for (int k = p == -1 ? 0 : 1; k < size; k++) {
          pathCount += analyzeLit(rstack[lits + k]);
        }
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
      while (vdata[(trail[index] >> 1) << 2 | SEEN] == 0
          || litLevel(trail[index]) != decisionLevel) {
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
      vdata[(p >> 1) << 2 | SEEN] = 0;
      pathCount--;
      if (notifying) {
        closeFrontier(p >> 1);
      }
    } while (pathCount > 0);
    learnt[0] = p ^ 1;
    if (notifying && EXPAND_UNKEPT) {
      expandLearnt();
    }

    int analysedEnd = toClearSize;

    // recursive minimisation
    if (++poisonStamp == Integer.MAX_VALUE) {
      Arrays.fill(poisonMark, 0);
      poisonStamp = 1;
    }
    int abstractLevels = 0;
    for (int i = 1; i < learntSize; i++) {
      abstractLevels |= 1 << (litLevel(learnt[i]) & 31);
    }
    int j = 1;
    for (int i = 1; i < learntSize; i++) {
      int v = learnt[i] >> 1;
      if (varReason(v) == NO_REASON || !redundant(learnt[i], abstractLevels)) {
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
      vdata[toClear[i] << 2 | SEEN] = 0;
    }
    vdata[(learnt[0] >> 1) << 2 | SEEN] = 0;
    learntLiterals += learntSize;
    if (notifying) {
      for (int i = 0; i < learntSize; i++) {
        external.notifyLearntLiteral(toDimacs(learnt[i]));
      }
      if (analysedNotify) {
        notifyAnalysed(analysedEnd);
      }
    }

    bumpQueue();
    if (learntSize == 1) {
      return 0;
    }
    int maxIndex = 1;
    for (int i = 2; i < learntSize; i++) {
      if (litLevel(learnt[i]) > litLevel(learnt[maxIndex])) {
        maxIndex = i;
      }
    }
    int tmp = learnt[1];
    learnt[1] = learnt[maxIndex];
    learnt[maxIndex] = tmp;
    return litLevel(learnt[1]);
  }

  static final boolean EXPAND_UNKEPT = Boolean.getBoolean("jacop.lcg.expandUnkept");
  static final boolean REASON_UNKEPT =
      !"false".equals(System.getProperty("jacop.lcg.reasonUnkept"));

  /** Statistics: learnt clause literals replaced by their reasons in {@link #expandLearnt}. */
  public long expandedLiterals;

  /** Statistics: short reasons used once instead of kept, for an unkept literal. */
  public long unkeptReasons;

  /**
   * Replaces the lower-level literals of the learnt clause that the external propagator does not
   * keep ({@link ExternalPropagator#unkept}) by the other literals of their reasons, recursively,
   * as CP-SAT expands integer reasons to Boolean ones: the clause stays implied and asserting. A
   * budget bounds the work; literals left when it runs out stay in the clause.
   */
  private void expandLearnt() {
    int budget = 4 * learntSize + 64;
    int i = 1;
    while (i < learntSize && budget > 0) {
      int q = learnt[i];
      int v = q >> 1;
      int why = varReason(v);
      if (why == NO_REASON || why == UNIT_REASON || !external.unkept(v + 1)) {
        i++;
        continue;
      }
      budget--;
      expandedLiterals++;
      learnt[i] = learnt[--learntSize];
      int r = reasonRef(v);
      if (r == UNIT_REASON) {
        continue;
      }
      if (r < NO_REASON) {
        expandLit(-2 - r);
        continue;
      }
      int off = reasonOffset(r);
      int size = reasonArena(r)[off + SIZE];
      for (int k = 1; k < size; k++) {
        expandLit(reasonArena(r)[off + HEADER + k]);
      }
    }
  }

  private void expandLit(int q) {
    int v = q >> 1;
    if (vdata[v << 2 | SEEN] != 0 || varLevel(v) == 0 || varReason(v) == UNIT_REASON) {
      return;
    }
    vdata[v << 2 | SEEN] = 1;
    markClear(v);
    addLearnt(q);
  }

  /**
   * Tells the external propagator of the variables the analysis met that are not in the learnt
   * clause: the first {@code end} of {@code toClear}, the variables resolved before minimisation.
   */
  private void notifyAnalysed(int end) {
    if (++analysedStamp == Integer.MAX_VALUE) {
      Arrays.fill(analysedMark, 0);
      analysedStamp = 1;
    }
    int stamp = analysedStamp;
    for (int i = 0; i < learntSize; i++) {
      analysedMark[learnt[i] >> 1] = stamp;
    }
    for (int i = 0; i < end; i++) {
      notifyAnalysedVar(toClear[i], stamp);
    }
  }

  private void notifyAnalysedVar(int v, int stamp) {
    if (analysedMark[v] != stamp && varLevel(v) > 0) {
      analysedMark[v] = stamp;
      external.notifyAnalysedLiteral(v + 1);
    }
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
      if (vdata[v << 2 | SEEN] != 0 && varLevel(v) == decisionLevel) {
        frontier[n++] = toDimacs(trail[t]);
      }
    }
    int d = external.semanticUip(frontier, n);
    if (d == 0) {
      return -1;
    }
    int lit = toLit(d);
    if (vals[lit] <= 0 || litLevel(lit) != decisionLevel) {
      return -1;
    }
    for (int k = 0; k < n; k++) {
      int v = Math.abs(frontier[k]) - 1;
      vdata[v << 2 | SEEN] = 0;
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
      shrinkKeys[i] = (long) litLevel(lit) << 32 | lit;
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
      index = Math.max(index, varTrailPos(v));
    }
    for (; ; index--) {
      int t = trail[index];
      int v = t >> 1;
      if (shrinkMark[v] != shrinkStamp || varLevel(v) != lvl) {
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
        int[] m = reasonArena(r);
        int lits = reasonOffset(r) + HEADER;
        int size = m[lits - HEADER + SIZE];
        for (int k = 1; k < size && open >= 0; k++) {
          open += shrinkStep(m[lits + k], lvl);
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
    int l = varLevel(v);
    if (l == lvl) {
      if (shrinkMark[v] == shrinkStamp) {
        return 0;
      }
      shrinkMark[v] = shrinkStamp;
      return 1;
    }
    return l == 0 || vdata[v << 2 | SEEN] != 0 ? 0 : Integer.MIN_VALUE / 2;
  }

  /** Marks the variable of a reason literal; returns 1 when it is at the conflict level. */
  private int analyzeLit(int q) {
    int v = q >> 1;
    if (vdata[v << 2 | SEEN] != 0 || varLevel(v) == 0 || varReason(v) == UNIT_REASON) {
      return 0;
    }
    vdata[v << 2 | SEEN] = 1;
    markClear(v);
    bumpVar(v);
    if (varLevel(v) >= decisionLevel) {
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
    int off = reasonOffset(r);
    int size = reasonArena(r)[off + SIZE];
    for (int k = 1; k < size; k++) {
      // the array is read again each time: explaining an antecedent may reallocate it
      if (!removable(reasonArena(r)[off + HEADER + k], abstractLevels, depth + 1)) {
        return false;
      }
    }
    return true;
  }

  private boolean removable(int q, int abstractLevels, int depth) {
    int v = q >> 1;
    if (vdata[v << 2 | SEEN] != 0 || varLevel(v) == 0 || varReason(v) == UNIT_REASON) {
      return true;
    }
    if (poisonMark[v] == poisonStamp
        || varReason(v) == NO_REASON
        || ((1 << (varLevel(v) & 31)) & abstractLevels) == 0
        || depth > MINIMIZE_DEPTH) {
      return false;
    }
    if (antecedentsRemovable(v, abstractLevels, depth)) {
      vdata[v << 2 | SEEN] = 1;
      markClear(v);
      return true;
    }
    poisonMark[v] = poisonStamp;
    return false;
  }

  /**
   * Takes the next assumption on decision level 1, which it opens first when the search is at the
   * root. The assumptions are taken in order, each propagated before the next, so that a false one
   * is found as early as on levels of their own.
   *
   * @return the assumption to assign, -1 when all of them hold, or -2 when one is false; {@link
   *     #failedAssumptions()} then gives the assumptions responsible
   */
  private int nextAssumption() {
    if (decisionLevel == 0) {
      newSearchLevel();
      assumptionNext = 0;
    }
    while (assumptionNext < assumptions.length) {
      int a = assumptions[assumptionNext++];
      if (vals[a] < 0) {
        analyzeFinal(a ^ 1);
        return -2;
      }
      if (vals[a] == 0) {
        return a;
      }
    }
    return -1;
  }

  /**
   * Collects the assumptions responsible for the conflict at level 1, where they are the only
   * decisions, into {@code failed}.
   */
  private void analyzeFinalConflict() {
    int ref = conflictRef;
    if (ref == UNIT_REASON) {
      failed = new int[assumptions.length]; // a conflict without literals: all of them, to be safe
      for (int i = 0; i < assumptions.length; i++) {
        failed[i] = toDimacs(assumptions[i]);
      }
      return;
    }
    if (ref == BINARY_CONFLICT) {
      markFinal(conflictLit0);
      markFinal(conflictLit1);
    } else if (ref < NO_REASON) {
      markFinal(-2 - ref);
    } else if (ref >= STACK_REF) {
      int lits = ref - STACK_REF + HEADER;
      int size = rstack[lits - HEADER + SIZE];
      for (int k = 0; k < size; k++) {
        markFinal(rstack[lits + k]);
      }
    } else {
      int lits = ref + HEADER;
      int size = mem[ref + SIZE];
      for (int k = 0; k < size; k++) {
        markFinal(mem[lits + k]);
      }
    }
    int[] out = new int[assumptions.length];
    failed = Arrays.copyOf(out, collectFinal(out, 0));
  }

  /** Collects the assumptions responsible for {@code p} being false into {@code failed}. */
  private void analyzeFinal(int p) {
    int[] out = new int[assumptions.length + 1];
    out[0] = toDimacs(p ^ 1);
    if (decisionLevel == 0) {
      failed = Arrays.copyOf(out, 1);
      return;
    }
    markFinal(p);
    failed = Arrays.copyOf(out, collectFinal(out, 1));
  }

  private void markFinal(int q) {
    if (litLevel(q) > 0) {
      vdata[(q >> 1) << 2 | SEEN] = 1;
    }
  }

  /**
   * Walks the trail above the root back from its end, through the reasons of the marked variables,
   * adds the decisions (the assumptions) it reaches to {@code out} and clears the marks.
   *
   * @return the number of literals in {@code out}
   */
  private int collectFinal(int[] out, int n) {
    for (int i = trailSize - 1; i >= trailLim[0]; i--) {
      int x = trail[i] >> 1;
      if (vdata[x << 2 | SEEN] == 0) {
        continue;
      }
      int r = reasonRef(x);
      if (r == NO_REASON) {
        out[n++] = toDimacs(trail[i]);
      } else if (r != UNIT_REASON && r < NO_REASON) {
        markFinal(-2 - r);
      } else if (r != UNIT_REASON) {
        int[] m = reasonArena(r);
        int off = reasonOffset(r);
        for (int k = 1; k < m[off + SIZE]; k++) {
          markFinal(m[off + HEADER + k]);
        }
      }
      vdata[x << 2 | SEEN] = 0;
    }
    return n;
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
    newSearchLevel();
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
   * Returns the decision level of an assigned literal.
   *
   * @param lit a DIMACS literal whose variable is assigned
   * @return the level it was assigned at
   */
  public int levelOf(int lit) {
    return varLevel(Math.abs(lit) - 1);
  }

  /**
   * Returns the position of a literal's variable on the trail.
   *
   * @param lit a DIMACS literal
   * @return its position, or -1 when the variable is unassigned
   */
  public int trailPosition(int lit) {
    return vals[toLit(lit)] == 0 ? -1 : varTrailPos(Math.abs(lit) - 1);
  }

  /**
   * Returns how an assigned literal got its value: 0 a decision or an assumption, 1 a unit, 2 a
   * binary clause, 3 a learnt clause (or a kept external reason), 4 an original clause, 5 the
   * external propagator.
   *
   * @param lit the literal, in DIMACS form
   * @return the kind of its reason
   */
  public int reasonKind(int lit) {
    int r = varReason(Math.abs(lit) - 1);
    if (r == NO_REASON) {
      return 0;
    }
    if (r == UNIT_REASON) {
      return 1;
    }
    if (r == EXTERNAL_REASON || r >= STACK_REF) {
      return 5;
    }
    if (r < NO_REASON) {
      return 2;
    }
    return (mem[r + META] & LEARNT_FLAG) != 0 ? 3 : 4;
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
      if (checking) {
        checkFixpoint();
      }
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
      noteLowWatched(ref, c);
    }
    if (conflicts >= nextReduce) {
      nextReduce = conflicts + reduceBase + reduceInc * ++reductions;
      reduceDb();
    } else if (learntsTooLarge()) {
      reduceForMemory();
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
      boolean fixed = vals[l] != 0 && litLevel(l) == 0;
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
    noteLowWatched(ref, c);
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
    for (int i = 0; i < trailSize && litLevel(trail[i]) == 0; i++) {
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
    int[] arena = reasonArena(conflictRef);
    int off = reasonOffset(conflictRef);
    for (int k = 0; k < arena[off + SIZE]; k++) {
      if (atCurrentLevel(arena[off + HEADER + k])) {
        return true;
      }
    }
    return false;
  }

  private boolean atCurrentLevel(int lit) {
    int v = lit >> 1;
    return varLevel(v) == decisionLevel && varReason(v) != UNIT_REASON;
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
    mem[ref + META] = (mem[ref + META] & NOT_POS) | POS_START;
    attach(ref);
  }

  private void removeWatch(int lit, int ref) {
    long[] ws = watches[lit];
    int n = (int) ws[0];
    for (int i = 1; i < n; i++) {
      if (watchRef(ws[i]) == ref) {
        System.arraycopy(ws, i + 1, ws, i, n - i - 1);
        ws[0] = n - 1L;
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
    orderForWatches(c, c.length);
  }

  /** {@link #orderForWatches(int[])} on the first size literals of c. */
  private void orderForWatches(int[] c, int size) {
    for (int pos = 0; pos < 2 && pos < size; pos++) {
      int best = pos;
      for (int i = pos + 1; i < size; i++) {
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
    if (v > 0) {
      return Integer.MAX_VALUE;
    }
    return v == 0 ? Integer.MAX_VALUE - 1 : litLevel(l);
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
      if (outOfTime) {
        outOfTime = false;
        return UNKNOWN;
      }
      if (confl != NO_CONFLICT) {
        conflicts++;
        jumpPhases = null;
        if (decisionLevel == 0) {
          ok = false;
          if (proof != null) {
            proof.add(learnt, 0, 0);
          }
          return UNSAT;
        }
        if (assumptionsOnOneLevel && decisionLevel == 1 && assumptions.length > 0) {
          // only the assumptions are decided at level 1: together with the root they are refuted
          analyzeFinalConflict();
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
        conflictLevels += decisionLevel;
        backjumpLevels += decisionLevel - btLevel;
        if (chrono && learntSize > 1 && decisionLevel - btLevel > chronoLimit) {
          btLevel = decisionLevel - 1;
        }
        boolean lazy =
            !chrono
                && lazyChronoLimit >= 0
                && assumptions.length == 0
                && learntSize > 1
                && decisionLevel - btLevel > lazyChronoLimit;
        if (lazy) {
          btLevel = decisionLevel - 1;
          lazyChronoBacktracks++;
        }
        backtrack(btLevel);
        learnClause(lazy);
        if (wasted > (1 << 20) && wasted > memSize / 2) {
          purge(); // temporary external reasons freed by the backtrack
        }
        varInc /= varDecay;
        claInc /= CLA_DECAY;
        if (!stable && varDecay < 0.95 && conflicts % 5000 == 0) {
          varDecay += 0.01;
        }
        if (conflicts >= conflictLimit
            || interrupted
            || pastDeadline()
            || workLimit != Long.MAX_VALUE && work() >= workLimit) {
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
          if (eliminationDue() && !eliminate()) {
            return UNSAT;
          }
        }
        continue;
      }
      if (conflicts >= nextReduce) {
        nextReduce = conflicts + reduceBase + reduceInc * ++reductions;
        reduceDb();
        vivifyDue = vivification;
      } else if (learntsTooLarge()) {
        reduceForMemory();
      }
      if (decisionLevel == 0 && trailSize != simplifyAssigns && propagations >= simplifyProps) {
        simplifyDb();
      }
      if (checking) {
        checkFixpoint();
      }
      int next = -1;
      if (assumptionsOnOneLevel
          && decisionLevel <= 1
          && (decisionLevel == 0 || assumptionNext < assumptions.length)
          && assumptions.length > 0) {
        int a = nextAssumption();
        if (a == -2) {
          return UNSAT;
        }
        if (a >= 0) {
          assign(a, NO_REASON);
          continue;
        }
      }
      while (!assumptionsOnOneLevel && decisionLevel < assumptions.length) {
        int a = assumptions[decisionLevel];
        if (vals[a] > 0) {
          newSearchLevel();
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
      // the external propagator may hold a model whatever the unassigned variables take
      boolean complete =
          next == -1 && external != null && external.modelComplete() && clausesSatisfied();
      if (next == -1) {
        next = complete ? -1 : pickBranch();
        if (next == -1 && external != null && !complete) {
          int d = external.decideLast();
          if (d != 0 && Math.abs(d) <= numVars) {
            int l = toLit(d);
            next = vals[l] == 0 && !eliminatedVar[l >> 1] ? l : -1;
          }
        }
        if (next == -1) {
          if (external != null && !modelAccepted()) {
            continue;
          }
          return SAT;
        }
      }
      // under an external propagator one decision can take milliseconds: read the clock on each
      if (((++decisions & 1023) == 0 || external != null) && pastDeadline()) {
        return UNKNOWN;
      }
      if (workLimit != Long.MAX_VALUE && work() >= workLimit) {
        return UNKNOWN;
      }
      if ((decisionLevel == assumptionLevels || notifyNext && decisionLevel > assumptionLevels)
          && external != null) {
        notifyNext = false;
        external.notifyTopDecision(toDimacs(next));
      }
      newSearchLevel();
      assign(next, NO_REASON);
    }
  }

  /**
   * Returns whether every clause of the solver, unit, binary, original or learnt, has a true
   * literal under the current assignment, so that any values of the unassigned variables extend it
   * to a model of the clauses.
   *
   * @return true when every clause is satisfied
   */
  public boolean clausesSatisfied() {
    for (int i = 0; i < numUnits; i++) {
      if (vals[units[i]] <= 0) {
        return false;
      }
    }
    for (int[] binaries : new int[][] {originalBinaries, learntBinaries}) {
      int n = binaries == originalBinaries ? numOriginalBinaries : numLearntBinaries;
      for (int i = 0; i < n; i += 2) {
        if (vals[binaries[i]] <= 0 && vals[binaries[i + 1]] <= 0) {
          return false;
        }
      }
    }
    for (int[] refs : new int[][] {originals, learnts}) {
      int n = refs == originals ? numOriginals : numLearnts;
      for (int i = 0; i < n; i++) {
        int ref = refs[i];
        if ((mem[ref + META] & DELETED) != 0) {
          continue;
        }
        boolean satisfied = false;
        for (int k = 0, size = mem[ref + SIZE]; k < size && !satisfied; k++) {
          satisfied = vals[mem[ref + HEADER + k]] > 0;
        }
        if (!satisfied) {
          return false;
        }
      }
    }
    return true;
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
  private static final int ROUND_CLOCK_MASK =
      Integer.getInteger("jacop.jasat.roundClockMask", 1023);

  // propagateAll reads the clock every CLOCK_ROUNDS + 1 rounds of the external propagator
  private static final int CLOCK_ROUNDS = 63;

  private int propagateAll() {
    for (int rounds = 1; ; rounds++) {
      int confl = propagate();
      if (confl != NO_CONFLICT || external == null) {
        return confl;
      }
      // an external propagator can take many rounds to reach a fixpoint (bounds that creep by one
      // value at a time between constraints), so the clock is read here too, not only per decision.
      // A round can be slow: on vrp-submission toy_D (arrival times up to 460,588) under the
      // core-guided probe 1,024 rounds took minutes, the probe kept the whole -t 600 s run and
      // found no solution, which branch and bound finds in 0.2 s
      if ((rounds & CLOCK_ROUNDS) == 0 && pastDeadline()) {
        outOfTime = true;
        return NO_CONFLICT;
      }
      for (int i = 0; i < numLateObserved; i++) {
        int v = lateObserved[i];
        if (vals[2 * v] != 0 && varTrailPos(v) < notified) {
          int l = 2 * v + (vals[2 * v] > 0 ? 0 : 1);
          external.notifyAssignment(toDimacs(l), varLevel(v) == 0);
        }
      }
      numLateObserved = 0;
      for (; notified < trailSize; notified++) {
        int l = trail[notified];
        if (observed[l >> 1]) {
          external.notifyAssignment(toDimacs(l), litLevel(l) == 0);
        }
      }
      int[] c = queuedExternal;
      queuedExternal = null;
      if (c == null) {
        c = external.externalClause();
      }
      int implied = -1;
      if (c == null) {
        c = external.importedClause();
        if (c != null) {
          implied = IMPORTED;
        }
      }
      if (c == null) {
        int lit = external.propagate();
        while (lit != 0 && vals[toLit(lit)] > 0) {
          lit = external.propagate();
        }
        if (lit == 0) {
          // a propagation cut by the deadline is no fixpoint: no decision and no model follow
          if (external.propagationCut()) {
            outOfTime = true;
          }
          return NO_CONFLICT;
        }
        implied = toLit(lit);
        if (vals[implied] == 0) {
          assign(implied, EXTERNAL_REASON);
          if (proof != null && decisionLevel == 0) {
            // conflict analysis never asks for the reasons of root facts, which a proof needs
            reasonRef(implied >> 1);
          }
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
  // the implied literal of addExternal for a clause learnt elsewhere, added as a learnt clause
  private static final int IMPORTED = -2;

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
    boolean temporary = false;
    if (implied >= 0 && size > 1 && REASON_UNKEPT && hasUnkeptLiteral(c, size)) {
      orderForWatches(c);
      temporary = temporaryFits(c);
    }
    if (implied >= 0 && !temporary) {
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
    if (temporary) {
      unkeptReasons++;
      return externalTemporary(c, size);
    }
    int ref = BINARY;
    if (size == 2) {
      if (implied >= 0 || implied == IMPORTED) {
        addLearntBinary(c[0], c[1]);
      } else {
        addOriginalBinary(c[0], c[1]);
      }
    } else if (implied >= 0 || implied == IMPORTED) {
      ref = allocate(c, size, true, size);
      learnts = push(learnts, numLearnts++, ref);
      attach(ref);
    } else {
      ref = allocate(c, size, false, 0);
      originals = push(originals, numOriginals++, ref);
      attach(ref);
    }
    int top = litLevel(c[0]);
    if (vals[c[0]] > 0 || vals[c[1]] >= 0) {
      noteLowWatched(ref, c);
      return NO_CONFLICT;
    }
    if (vals[c[0]] == 0) {
      assign(c[0], ref == BINARY ? -2 - c[1] : ref);
      noteLowWatched(ref, c);
      return NO_CONFLICT;
    }
    if (top == 0) {
      ok = false;
      return NO_CONFLICT;
    }
    if (litLevel(c[1]) < top) {
      // only c[0] is false at its level: it is implied one level lower
      backtrack(top - 1);
      assign(c[0], ref == BINARY ? -2 - c[1] : ref);
      noteLowWatched(ref, c);
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
   * Whether a reason clause with an unkept literal, ordered for watches, can be used once without
   * being kept: it is satisfied or not unit (and is dropped), asserts its first literal, or is a
   * conflict at the current level.
   */
  private boolean temporaryFits(int[] c) {
    if (vals[c[0]] > 0 || vals[c[1]] >= 0) {
      return true; // dropped
    }
    // a backtrack would release transient literals created above its level, which this clause,
    // not being kept, does not link: those clauses are kept as before
    return vals[c[0]] == 0 || litLevel(c[0]) == decisionLevel && litLevel(c[1]) == decisionLevel;
  }

  /**
   * Uses a reason clause that {@link #temporaryFits} once, as a temporary reason or conflict on the
   * reason stack, instead of keeping it.
   */
  private int externalTemporary(int[] c, int size) {
    if (vals[c[0]] > 0 || vals[c[1]] >= 0) {
      return NO_CONFLICT;
    }
    if (vals[c[0]] == 0) {
      assign(c[0], pushReason(c[0] >> 1, c, size));
      return NO_CONFLICT;
    }
    qhead = trailSize;
    conflictRef = pushReason(c[0] >> 1, c, size);
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
    if (!observed[v] && vals[2 * v] != 0 && varTrailPos(v) < notified) {
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
    if (vals[2 * v] != 0 || binWatches[2 * v][0] != 1 || binWatches[2 * v + 1][0] != 1) {
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
    vdata[v << 2 | REASON] = NO_REASON;
    activity[v] = 0;
    savedSign[v] = originalSign;
    targetSign[v] = -1;
    bestSign[v] = originalSign;
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

  /**
   * Turns the lucky assignments before the first search on or off (on by default). They run in the
   * first {@link #solve} without assumptions and without an external propagator, before variable
   * elimination and again after it.
   *
   * @param on whether to try the lucky assignments
   */
  public void setLucky(boolean on) {
    lucky = on;
  }

  /**
   * Lucky assignments, as Kissat's lucky.c (Biere and Fleury, "Gimsatul, IsaSAT and Kissat entering
   * the SAT Competition 2022", Proc. SAT Competition 2022): formulas from applications are often
   * satisfied by a trivial assignment. First the solver checks whether every irredundant clause has
   * a positive (negative) literal that is not false at the root, so that setting all variables true
   * (false) satisfies the formula. Otherwise it decides the variables in input order, forward then
   * backward, all false and then all true, with propagation after each decision; on a conflict it
   * flips the last decision once and gives the pass up when the flipped one conflicts too. Unlike
   * Kissat, a first decision that fails does not become a root unit: when no pass finds a model,
   * the saved phases, the watches, the order of the clause literals and the propagation count are
   * put back as they were, so the search that follows is exactly the one without lucky assignments
   * (root units changed the search by luck on SAT instances, waerden 9 -> 95 s).
   *
   * @return {@link #SAT} with every variable assigned, {@link #UNSAT} when the root propagation
   *     refutes the formula, {@link #UNKNOWN} at the root when no assignment was lucky
   */
  private int lucky() {
    long begin = System.nanoTime();
    try {
      if (propagate() != NO_CONFLICT) {
        return refutedAtRoot();
      }
      // the passes move watches and reorder clause literals: a failed attempt puts them back, so
      // that the search afterwards is the one without lucky assignments, units aside
      byte[] phases = Arrays.copyOf(savedSign, numVars);
      int[] arena = Arrays.copyOf(mem, memSize);
      long[][] watched = new long[2 * numVars][];
      for (int l = 0; l < 2 * numVars; l++) {
        watched[l] = Arrays.copyOf(watches[l], (int) watches[l][0]);
      }
      long props = propagations;
      int result = UNKNOWN;
      if (noClauseWithoutSign(0)) {
        result = luckyPass(true, 0, "all-true");
      }
      if (result == UNKNOWN && noClauseWithoutSign(1)) {
        result = luckyPass(true, 1, "all-false");
      }
      if (result == UNKNOWN) {
        result = luckyPass(true, 1, "forward-false");
      }
      if (result == UNKNOWN) {
        result = luckyPass(true, 0, "forward-true");
      }
      if (result == UNKNOWN) {
        result = luckyPass(false, 1, "backward-false");
      }
      if (result == UNKNOWN) {
        result = luckyPass(false, 0, "backward-true");
      }
      if (result == UNKNOWN) {
        System.arraycopy(phases, 0, savedSign, 0, numVars);
        System.arraycopy(arena, 0, mem, 0, arena.length);
        restoreWatches(watched);
        propagations = props;
      }
      return result;
    } finally {
      luckyNanos += System.nanoTime() - begin;
    }
  }

  /** Puts back the watch lists copied by {@link #lucky()}; slot 0 of each copy holds its length. */
  private void restoreWatches(long[][] watched) {
    for (int l = 0; l < 2 * numVars; l++) {
      int n = watched[l].length;
      if (watches[l].length < n) {
        watches[l] = watched[l];
      } else {
        System.arraycopy(watched[l], 0, watches[l], 0, n);
      }
    }
  }

  /**
   * Whether every irredundant clause has a literal of the sign (0 positive, 1 negative) that is not
   * false at the root.
   */
  private boolean noClauseWithoutSign(int sign) {
    for (int i = 0; i < numOriginals; i++) {
      int ref = originals[i];
      if ((mem[ref + META] & DELETED) != 0) {
        continue;
      }
      boolean found = false;
      for (int k = 0, size = mem[ref + SIZE]; k < size && !found; k++) {
        int l = mem[ref + HEADER + k];
        found = (l & 1) == sign && vals[l] >= 0;
      }
      if (!found) {
        return false;
      }
    }
    for (int i = 0; i < numOriginalBinaries; i += 2) {
      int a = originalBinaries[i];
      int b = originalBinaries[i + 1];
      if (((a & 1) != sign || vals[a] < 0) && ((b & 1) != sign || vals[b] < 0)) {
        return false;
      }
    }
    return true;
  }

  /**
   * One lucky pass: decides each unassigned variable in input order (forward) or in reverse order
   * with the literal of the sign, propagating after each decision.
   *
   * @return SAT when every variable got a value without a conflict left, UNKNOWN (back at the root)
   *     otherwise
   */
  private int luckyPass(boolean forward, int sign, String name) {
    for (int k = 0; k < numVars; k++) {
      int v = forward ? k : numVars - 1 - k;
      if (vals[2 * v] != 0 || eliminatedVar[v]) {
        continue;
      }
      if ((k & 1023) == 0 && pastDeadline()) {
        backtrack(0);
        return UNKNOWN;
      }
      int lit = 2 * v + sign;
      newDecisionLevel();
      assign(lit, NO_REASON);
      if (propagate() == NO_CONFLICT) {
        continue;
      }
      backtrack(decisionLevel - 1);
      newDecisionLevel();
      assign(lit ^ 1, NO_REASON);
      if (propagate() != NO_CONFLICT) {
        backtrack(0);
        return UNKNOWN;
      }
    }
    luckyFound = name;
    return SAT;
  }

  /** The root propagation found a conflict: the formula is refuted. */
  private int refutedAtRoot() {
    ok = false;
    if (proof != null) {
      proof.add(learnt, 0, 0);
    }
    return UNSAT;
  }

  /**
   * Sets the initial phase of the variables, which rephasing also returns to: true as in CaDiCaL
   * (the default), or false as in MiniSat and CP-SAT.
   *
   * @param positive true for the positive literal
   */
  public void setInitialPhase(boolean positive) {
    originalSign = (byte) (positive ? 0 : 1);
    Arrays.fill(savedSign, 0, numVars, originalSign);
    Arrays.fill(bestSign, 0, numVars, originalSign);
  }

  private int pickBranch() {
    if (queueInUse()) {
      return pickFromQueue();
    }
    while (!order.isEmpty()) {
      int v = order.removeMax();
      if (vals[2 * v] == 0 && !eliminatedVar[v]) {
        if (jumpPhases != null && v < jumpPhases.length) {
          return 2 * v + jumpPhases[v];
        }
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
      case 'O' -> Arrays.fill(savedSign, 0, numVars, originalSign);
      case 'I' -> Arrays.fill(savedSign, 0, numVars, (byte) (1 - originalSign));
      case 'W' -> {
        System.arraycopy(bestSign, 0, savedSign, 0, numVars);
        if (walkFits()) {
          walk();
        }
      }
      default -> System.arraycopy(bestSign, 0, savedSign, 0, numVars);
    }
    if (jumpShare > 0 && external == null && assumptions.length == 0 && decisionLevel == 0) {
      jump();
    }
    System.arraycopy(savedSign, 0, targetSign, 0, numVars);
    targetAssigned = 0;
    bestAssigned = 0;
  }

  /** Runs the Walker on the irredundant clauses from the saved phases and saves its best phases. */
  private void walk() {
    long begin = System.nanoTime();
    int[][] formula = rootFormula();
    int[] lits = formula[0];
    int[] start = formula[1];
    int n = start.length - 1;
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
   * The irredundant clauses at the root, without their false literals and without the satisfied
   * ones: the literals one after the other, and where each clause starts (its last entry is the
   * end).
   */
  private int[][] rootFormula() {
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
    return new int[][] {lits, Arrays.copyOf(start, n + 1)};
  }

  /**
   * Gives the feasibility-jump local search (Luteberget and Sartor 2023, see {@link JumpSearch})
   * its share of the solver's clock since the first call, on the irredundant clauses at the root.
   * The search is kept between calls while that formula stays the same. When it satisfies every
   * clause, the decisions follow its assignment until the next conflict, so that they descend to a
   * model without one (learnt clauses follow from the formula), and the eliminated variables are
   * extended as for any model; it also becomes the saved and best phases.
   */
  private void jump() {
    long now = now();
    if (jumpStart == Long.MIN_VALUE) {
      jumpStart = now;
    }
    long slice = (long) (jumpShare * (now - jumpStart)) - jumpNanos;
    if (slice < MIN_JUMP_SLICE) {
      return;
    }
    long begin = now;
    long signature =
        (((long) trailSize * 31 + eliminatedCount()) * 31 + numOriginals) * 31
            + numOriginalBinaries
            + 1_000_003L * numVars;
    boolean rebuilt = jumper == null || signature != jumpSignature;
    if (rebuilt) {
      int[][] formula = rootFormula();
      if (formula[1].length == 1) {
        return;
      }
      int[] lits = formula[0];
      int[] start = formula[1];
      int clauses = start.length - 1;
      jumpUnfactored = null;
      if (factorBase < numVars) {
        jumpUnfactored =
            JumpSearch.unfactor(
                lits, start, clauses, factorBase, numVars, 4L * start[clauses] + 1_000_000);
        if (jumpUnfactored != null) {
          lits = jumpUnfactored.lits;
          start = jumpUnfactored.start;
          clauses = jumpUnfactored.numClauses;
        }
      }
      jumper =
          new JumpSearch(
              numVars,
              lits,
              start,
              clauses,
              Arrays.copyOf(savedSign, numVars),
              jumpCalls + 7_000_003L * seed);
      jumpSignature = signature;
      jumperClauses = clauses;
    }
    jumpCalls++;
    long end = begin + slice;
    long workBefore = jumpWork;
    long ticksBefore = jumper.ticks();
    // the stop check also counts the ticks as work, which moves the virtual clock
    boolean model =
        jumper.run(
            Long.MAX_VALUE,
            () -> {
              jumpWork = workBefore + (jumper.ticks() - ticksBefore) / JUMP_TICKS_PER_WORK;
              return interrupted || now() >= end || now() > deadline;
            });
    jumpWork = workBefore + (jumper.ticks() - ticksBefore) / JUMP_TICKS_PER_WORK;
    jumpNanos += now() - begin;
    if (JUMP_DEBUG) {
      System.out.printf(
          "c jump call %d rebuilt %b clauses %d slice %.3f s flips %d ticks %d restarts %d best %d%n",
          jumpCalls,
          rebuilt,
          jumperClauses,
          slice / 1e9,
          jumper.flips(),
          jumper.ticks(),
          jumper.restarts(),
          jumper.bestUnsat());
    }
    if (model) {
      jumpModels++;
      byte[] signs = Arrays.copyOf(jumper.signs(), numVars);
      if (jumpUnfactored != null) {
        jumpUnfactored.extend(signs);
      }
      System.arraycopy(signs, 0, savedSign, 0, numVars);
      System.arraycopy(signs, 0, bestSign, 0, numVars);
      // decisions follow these phases until a conflict: vivification and phase saving may change
      // the saved phases before the descent
      jumpPhases = signs;
    }
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
   * Sets the largest bound of variable elimination: an elimination may add this many clauses more
   * than it removes. The bound is 0 in the first run before the search and rises through 1, 2, 4, 8
   * and 16 up to this one with each complete run during search (default 16; 0 never adds clauses).
   *
   * @param bound the largest bound
   */
  public void setMaxEliminationBound(int bound) {
    maxEliminationBound = Math.max(0, bound);
  }

  /**
   * Turns gate detection in variable elimination on or off (on by default). When a variable is the
   * output of an AND, OR, ITE, XOR gate or an equivalence, only the resolvents of its defining
   * clauses with the others are added.
   *
   * @param on whether to use gates
   */
  public void setEliminationGates(boolean on) {
    eliminationGates = on;
  }

  /**
   * Sets the longest resolvent variable elimination may add (default 100).
   *
   * @param literals the limit
   */
  public void setResolventLimit(int literals) {
    resolventLimit = Math.max(2, literals);
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

  /**
   * Sets the share of the solver's clock given to the feasibility-jump local search, which looks
   * for a model of the clauses at rephasing points of a search without assumptions and without an
   * external propagator, and hands a model it finds to the search as phases ({@link
   * #DEFAULT_JUMP_SHARE} by default).
   *
   * @param share the share, from 0 (off) to below 1
   */
  public void setJumpShare(double share) {
    if (!(share >= 0 && share < 1)) {
      throw new IllegalArgumentException("jump share must be in [0, 1): " + share);
    }
    jumpShare = share;
  }

  /**
   * Returns how many times the feasibility-jump local search found a model of the clauses.
   *
   * @return the number of models it found
   */
  public int jumpModels() {
    return jumpModels;
  }

  /**
   * Returns whether a model of the feasibility-jump local search led the search to its model.
   *
   * @return whether the last model came from the local search
   */
  public boolean jumpSolved() {
    return jumpSolved;
  }

  /**
   * Learns the clause of the last conflict and asserts its first literal. When lazy, the solver
   * backtracked one level only: the literal is asserted at the current level, above the level of
   * the rest of the clause, and the clause is remembered with noteLowWatched, so that a later
   * backtrack below the current level asserts it again.
   */
  private void learnClause(boolean lazy) {
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
      if (lazy) {
        assign(learnt[0], -2 - learnt[1]);
        noteLowWatched(BINARY, learnt[0], learnt[1]);
      } else {
        assignAt(learnt[0], -2 - learnt[1], litLevel(learnt[1]));
      }
    } else {
      lbd = computeLbd(learnt, 0, learntSize);
      if (proof != null) {
        proof.add(learnt, 0, learntSize);
      }
      int ref = allocate(learnt, learntSize, true, lbd);
      learnts = push(learnts, numLearnts++, ref);
      attach(ref);
      bumpClause(ref);
      if (lazy) {
        assign(learnt[0], ref);
        noteLowWatched(ref, learnt[0], learnt[1]);
      } else {
        assignAt(learnt[0], ref, litLevel(learnt[1]));
      }
    }
    if (learntSize <= exportSize && lbd <= exportLbd && external != null) {
      int[] dimacs = new int[learntSize];
      for (int i = 0; i < learntSize; i++) {
        dimacs[i] = toDimacs(learnt[i]);
      }
      external.notifyLearnt(dimacs, lbd);
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
    if (forcedRestartAt != Long.MAX_VALUE && decisionLevel > 0 && now() >= forcedRestartAt) {
      forcedRestartAt = Long.MAX_VALUE;
      forcedRestart = true;
      return true;
    }
    if (!restartsOn || decisionLevel <= assumptionLevels) {
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
    // vivification and elimination work at the root; other restarts keep the assumption level
    boolean root =
        forcedRestart || vivifyDue || conflicts >= nextElimination && elimination && !externalUsed;
    forcedRestart = false;
    backtrack(root ? 0 : Math.min(decisionLevel, assumptionLevels));
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
      if (stableForGood && stable) {
        modeSwitchAt = Long.MAX_VALUE;
      }
      lubyIndex = 0;
    }
    if (stable) {
      lubyLimit = LUBY_UNIT * luby(++lubyIndex);
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

  /**
   * Whether the learnt clauses take more than their share of the heap, checked only once the arena
   * is that large and at most every k * MEMORY_REDUCE_GAP conflicts after the (k - 1)-th memory
   * reduction. A memory reduction deletes learnt clauses of every tier, so a gap that stays fixed
   * can delete the clauses the search needs again and again: with decisions in a fixed order a
   * satisfiable formula then ran millions of conflicts without an answer. A gap that grows lets the
   * search finish, and the learnt clauses grow by at most the clauses of one gap over the budget.
   */
  private boolean learntsTooLarge() {
    if (conflicts < nextMemoryCheck || memSize - wasted <= learntBudget) {
      return false;
    }
    nextMemoryCheck = conflicts + MEMORY_REDUCE_GAP * (memoryReductions + 1);
    return learntInts() > learntBudget;
  }

  /** The ints that the learnt clauses take in the arena. */
  private long learntInts() {
    long ints = 0;
    for (int i = 0; i < numLearnts; i++) {
      ints += HEADER + mem[learnts[i] + SIZE];
    }
    return ints;
  }

  /**
   * It deletes the longest learnt clauses that are not the reason of an assignment, whatever their
   * tier, until the learnt clauses take half of their budget. Long clauses of a low LBD stay in the
   * core tier for good, so the scheduled reductions never delete them: under lazy clause generation
   * over a diagram given as clauses they were the clauses of tens of thousands of literals that
   * filled the heap.
   */
  private void reduceForMemory() {
    memoryReductions++;
    long ints = learntInts();
    long[] keys = new long[numLearnts];
    int candidates = 0;
    for (int i = 0; i < numLearnts; i++) {
      int ref = learnts[i];
      if (!isLocked(ref)) {
        keys[candidates++] = ((long) mem[ref + SIZE] << 32) | i;
      }
    }
    Arrays.sort(keys, 0, candidates);
    for (int c = candidates - 1; c >= 0 && ints > learntBudget / 2; c--) {
      int ref = learnts[(int) keys[c]];
      ints -= HEADER + mem[ref + SIZE];
      deleteClause(ref);
    }
    purge();
  }

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

  /** The number of learnt clauses of three or more literals kept now. */
  int learntCount() {
    return numLearnts;
  }

  /** The size of the clause arena in ints, deleted clauses not yet collected included. */
  int arenaSize() {
    return memSize;
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
   * Whether the copies that elimination makes of the original clauses fit in a quarter of the heap:
   * the clauses as arrays, the eliminator's own lists and its occurrence lists, about three times
   * the clauses. Under lazy clause generation a diagram or table posted as clauses gives tens of
   * millions of them, and the copies ran a 6 GB heap out of memory on MagicSquare-mdd-10 (XCSP
   * 2023); elimination is then skipped. The heap size, not the free heap, decides, so that the run
   * does not depend on the garbage collector.
   */
  private boolean eliminationFits() {
    long clauses = numOriginals + numOriginalBinaries / 2L;
    long need = 3 * (24 * clauses + 4 * (originalLiterals() + numOriginalBinaries)) + 48L * numVars;
    return need < copyBudget;
  }

  /**
   * Whether the copy of the original clauses that the local search walks on fits in a quarter of
   * the heap: their literals and starts, an occurrence list for each literal of a clause and its
   * arrays per variable.
   */
  private boolean walkFits() {
    long clauses = numOriginals + numOriginalBinaries / 2L;
    long literals = originalLiterals() + numOriginalBinaries;
    long need = 8 * literals + 4 * clauses + 48L * numVars;
    return need < copyBudget;
  }

  /** The literals of the original clauses that are not binary. */
  private long originalLiterals() {
    long literals = 0;
    for (int i = 0; i < numOriginals; i++) {
      literals += mem[originals[i] + SIZE];
    }
    return literals;
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
    if (probing && !probe()) {
      return false;
    }
    if (!eliminationFits()) {
      return true;
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
    boolean sat = true;
    if (factoring && !factored) {
      factored = true;
      long begin = System.nanoTime();
      Factorizer f = new Factorizer(numVars, input, n, proof, factorEffort);
      f.setDeadline(deadline);
      if (f.run() > 0) {
        input = f.clauses();
        factoredClauses = n - (long) input.length;
        n = input.length;
        factorBase = numVars;
        factoredVars = f.numFresh();
        ensureVars(f.numVars());
        frozen = Arrays.copyOf(frozen, numVars);
      }
      factorWork = f.effort();
      factorNanos = System.nanoTime() - begin;
    }
    Sweeper sw = null;
    if (sweeping) {
      sw = sweep(input, n, frozen);
      if (sw.unsat()) {
        return refuted();
      }
      input = sw.clauses();
      n = input.length;
    }
    Congruence cc = null;
    if (substitution) {
      long t0 = System.nanoTime();
      cc = new Congruence(numVars, input, n, frozen, proof);
      cc.gatesOn = congruence && gatesPaid;
      sat = cc.run();
      gatesPaid = cc.gatesOn && cc.andGates + cc.xorGates + cc.iteGates > 0;
      substitutionNanos += System.nanoTime() - t0;
      if (sat) {
        input = cc.clauses();
        n = input.length;
        substitutedVars += cc.numSubstituted();
        sccEquivalences += cc.sccEquivalences;
        gateEquivalences += cc.gateEquivalences;
        gatesFound += cc.andGates + cc.xorGates + cc.iteGates;
      }
    }
    long elimBegin = System.nanoTime();
    // with an external propagator (lazy clause generation) elimination stays as in MiniSat
    int[][] elimInput = sat ? input : new int[0][];
    int elimCount = sat ? n : 0;
    Eliminator.Limits limits =
        new Eliminator.Limits(eliminationBound, eliminationBound, resolventLimit, eliminationGates);
    Eliminator e =
        external != null
            ? new Eliminator(numVars, elimInput, elimCount, frozen, proof)
            : new Eliminator(numVars, elimInput, elimCount, frozen, proof, limits);
    sat = sat && e.run();
    gateEliminations += e.numGateEliminations();
    // the bound rises by one step after each complete run, so the first run before the search
    // adds no clauses and later runs during search add more (Kissat's eliminatebound schedule)
    eliminationFruitless = e.numEliminated() == 0 && eliminationBound >= maxEliminationBound;
    if (e.completed()) {
      eliminationBound = Eliminator.nextBound(eliminationBound, maxEliminationBound);
    }
    eliminationNanos += System.nanoTime() - elimBegin;
    for (int i = 0; i < numOriginals; i++) {
      int ref = originals[i];
      if ((mem[ref + META] & DELETED) == 0) {
        mem[ref + META] |= DELETED;
        wasted += HEADER + mem[ref + SIZE];
      }
    }
    for (int i = 0; i < trailSize; i++) {
      if (proof != null && i >= rootFactsLogged) {
        // the root facts outlive their reasons, which elimination and keepLearnts may delete
        proof.add(trail, i, 1);
      }
      vdata[(trail[i] >> 1) << 2 | REASON] = NO_REASON;
    }
    rootFactsLogged = Math.max(rootFactsLogged, trailSize);
    boolean[] gone = e.eliminated();
    if (sw != null) {
      boolean[] replaced = sw.substituted();
      for (int v = 0; v < replaced.length; v++) {
        gone[v] |= replaced[v];
      }
    }
    if (cc != null && sat) {
      boolean[] replaced = cc.substituted();
      // bounded variable addition may have added variables after the substitution
      for (int v = 0; v < replaced.length; v++) {
        gone[v] |= replaced[v];
      }
    }
    numOriginalBinaries = 0;
    for (int lit = 0; lit < 2 * numVars; lit++) {
      if (watches[lit][0] != 1) {
        watches[lit][0] = 1;
      }
      if (binWatches[lit][0] != 1) {
        binWatches[lit][0] = 1;
      }
    }
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
    // the substitutions before the eliminations, in their order: a model is extended backwards
    if (sw != null) {
      numEliminated += sw.numSubstituted();
      appendExtension(sw.stack());
    }
    if (cc != null) {
      numEliminated += cc.numSubstituted();
      appendExtension(cc.stack());
    }
    appendExtension(e.stack());
    int[] none = new int[0];
    for (int[] found :
        new int[][] {sw == null ? none : sw.units(), cc == null ? none : cc.units(), e.units()}) {
      for (int u : found) {
        if (vals[u] < 0) {
          return refuted();
        }
        if (vals[u] == 0) {
          assign(u, NO_REASON);
        }
      }
    }
    if (propagate() != NO_CONFLICT) {
      return refuted();
    }
    eliminationTrail = trailSize;
    eliminationOriginals = numOriginals + numOriginalBinaries;
    return true;
  }

  /**
   * Failed-literal probing at level 0 (see {@link #setProbing}), within a twentieth of the
   * propagations of the search since the last round. Each probe is a decision at level 1 followed
   * by unit propagation; a conflict is analysed as in search, which at level 1 gives a unit (the
   * first UIP). The roots of the binary implication graph (literals with binary implications and no
   * binary clause implying them) are probed in turn from where the last round stopped, and the
   * negation of a root too, which gives units implied by both signs (lifting) and equivalent
   * literals. References: I. Lynce, J. Marques-Silva, "Probing-Based Preprocessing Techniques for
   * Propositional Satisfiability", ICTAI 2003; M. J. H. Heule, M. Järvisalo, A. Biere, "Efficient
   * CNF Simplification Based on Binary Implication Graphs", SAT 2011.
   *
   * @return false when the formula is unsatisfiable
   */
  private boolean probe() {
    if (propagate() != NO_CONFLICT) {
      return refuted();
    }
    long start = System.nanoTime();
    long propagationsBefore = propagations;
    long budget =
        propagations
            + Math.max(
                PROBE_MIN_EFFORT,
                (propagations - propagationsAtProbe) * PROBE_EFFORT_PER_MILLE / 1000);
    boolean wasChrono = chrono;
    chrono = false;
    boolean wasNotifying = notifying;
    notifying = false; // the probing levels are internal
    // probing must not move the saved phases: when it finds nothing, the search stays as it was
    byte[] phases = Arrays.copyOf(savedSign, numVars);
    if (probeMark.length < 2 * numVars) {
      probeMark = new int[2 * numVars];
      probeStamp = 0;
    }
    int result = 0;
    int tried = 0;
    try {
      while (tried < numVars && propagations < budget && result >= 0 && !pastDeadline()) {
        int v = probeCursor;
        probeCursor = (probeCursor + 1) % numVars;
        tried++;
        if (eliminatedVar[v]) {
          continue;
        }
        for (int sign = 0; sign < 2 && result >= 0 && vals[2 * v] == 0; sign++) {
          int p = 2 * v + sign;
          // a root: p has binary implications and no binary clause implies it
          if (binWatches[p ^ 1][0] != 1 && binWatches[p][0] == 1) {
            result = probeRoot(p);
          }
        }
      }
    } finally {
      chrono = wasChrono;
      notifying = wasNotifying;
      System.arraycopy(phases, 0, savedSign, 0, numVars);
    }
    probePropagations += propagations - propagationsBefore;
    propagations = propagationsBefore; // the search's schedules count its own propagations
    propagationsAtProbe = propagations;
    probeNanos += System.nanoTime() - start;
    return result >= 0 && (propagate() == NO_CONFLICT || refuted());
  }

  // probing: literals implied by the last probe, and marks of those implied by the first sign
  private int[] probeImplied = new int[16];
  private int[] probeFirst = new int[16];
  private int[] probeMark = new int[0];
  private int probeStamp;

  /**
   * Probes a root and its negation.
   *
   * @return 0, or -1 when the formula is unsatisfiable
   */
  private int probeRoot(int p) {
    probedLiterals++;
    int n = probeLiteral(p);
    if (n < 0) {
      return n == -1 ? 0 : -1;
    }
    if (probeFirst.length < n) {
      probeFirst = new int[2 * n];
    }
    System.arraycopy(probeImplied, 0, probeFirst, 0, n);
    if (++probeStamp == Integer.MAX_VALUE) {
      Arrays.fill(probeMark, 0);
      probeStamp = 1;
    }
    for (int i = 0; i < n; i++) {
      probeMark[probeFirst[i]] = probeStamp;
    }
    int m = probeLiteral(p ^ 1);
    if (m < 0) {
      return m == -1 ? 0 : -1;
    }
    int[] c = new int[2];
    for (int i = 0; i < m; i++) {
      int q = probeImplied[i];
      if (vals[q] != 0) {
        continue; // an earlier lifted unit implied it
      }
      if (probeMark[q] == probeStamp) {
        // p -> q and -p -> q: q holds
        liftedUnits++;
        if (proof != null) {
          c[0] = p ^ 1;
          c[1] = q;
          proof.add(c, 0, 2);
          c[0] = p;
          proof.add(c, 0, 2);
          proof.add(c, 1, 1);
          c[0] = p ^ 1;
          proof.delete(c, 0, 2);
          c[0] = p;
          proof.delete(c, 0, 2);
        }
        assign(q, NO_REASON);
        if (propagate() != NO_CONFLICT) {
          refuted();
          return -1;
        }
      } else if (probeMark[q ^ 1] == probeStamp && (q >> 1) != (p >> 1)) {
        // p -> -q and -p -> q: q is the negation of p
        probeEquivalences++;
        if (proof != null) {
          c[0] = p;
          c[1] = q;
          proof.add(c, 0, 2);
          c[0] = p ^ 1;
          c[1] = q ^ 1;
          proof.add(c, 0, 2);
        }
        addOriginalBinary(p, q);
        addOriginalBinary(p ^ 1, q ^ 1);
      }
    }
    return 0;
  }

  /**
   * Probes one literal at level 1 and goes back to level 0.
   *
   * @return the number of literals it implies, in {@code probeImplied}; -1 when it failed and the
   *     unit learnt from the conflict holds now; -2 when the formula is unsatisfiable
   */
  private int probeLiteral(int p) {
    newDecisionLevel();
    int start = trailSize;
    assign(p, NO_REASON);
    if (propagate() != NO_CONFLICT) {
      failedLiterals++;
      analyze();
      backtrack(0);
      int[] u = learntSize == 1 ? learnt : new int[] {p ^ 1};
      if (proof != null) {
        proof.add(u, 0, 1);
      }
      if (vals[u[0]] == 0) {
        assign(u[0], NO_REASON);
      }
      if (vals[u[0]] < 0 || propagate() != NO_CONFLICT) {
        refuted();
        return -2;
      }
      return -1;
    }
    int n = trailSize - start - 1;
    if (probeImplied.length < n) {
      probeImplied = new int[2 * n];
    }
    System.arraycopy(trail, start + 1, probeImplied, 0, n);
    backtrack(0);
    return n;
  }

  private void appendExtension(int[] removed) {
    int old = extension.length;
    extension = Arrays.copyOf(extension, old + removed.length);
    System.arraycopy(removed, 0, extension, old, removed.length);
  }

  /**
   * SAT sweeping (see {@link Sweeper}) of the irredundant clauses given to elimination, in the
   * order of fewest occurrences first, continuing from where the last round stopped. Its effort is
   * a tenth of the propagations of the search since the last round.
   *
   * @return the sweeper, with the clauses, units and substitutions it found
   */
  private Sweeper sweep(int[][] input, int n, boolean[] frozen) {
    long start = System.nanoTime();
    if (sweepDelay > 0) {
      // the last rounds found almost nothing: skip rounds, as Kissat's sweep delay
      sweepDelay--;
      return new Sweeper(numVars, input, n, frozen, proof, 0, sweepCompleted);
    }
    // the first round, before any search, gets a fixed effort: equivalences found then pay most
    long budget =
        Math.max(
            sweepRounds++ == 0 ? SWEEP_FIRST_EFFORT : SWEEP_MIN_EFFORT,
            (propagations - propagationsAtSweep) * SWEEP_EFFORT_PER_MILLE / 1000);
    Sweeper s = new Sweeper(numVars, input, n, frozen, proof, budget, sweepCompleted);
    if (sweepDone.length < numVars) {
      sweepDone = Arrays.copyOf(sweepDone, numVars);
    }
    long[] keys = new long[numVars];
    int m = 0;
    for (int v = 0; v < numVars; v++) {
      if (vals[2 * v] != 0 || eliminatedVar[v] || sweepDone[v]) {
        continue;
      }
      int occ = s.candidate(v);
      if (occ < 0) {
        sweepDone[v] = true;
        continue;
      }
      keys[m++] = (long) occ << 32 | v;
    }
    Arrays.sort(keys, 0, m);
    int[] order = new int[m];
    for (int i = 0; i < m; i++) {
      order[i] = (int) keys[i];
    }
    int swept = s.run(order, m, sweepDone);
    if (swept == m && !s.unsat()) {
      sweepCompleted++;
      Arrays.fill(sweepDone, false);
    }
    sweptVariables += s.swept;
    sweepUnits += s.units().length;
    sweepEquivalences += s.equivalences;
    if (s.units().length + s.equivalences < s.swept / 1000.0) {
      sweepDelayLimit = Math.min(2 * sweepDelayLimit + 1, 64);
      sweepDelay = sweepDelayLimit;
    } else {
      sweepDelayLimit = 0;
    }
    propagationsAtSweep = propagations;
    sweepNanos += System.nanoTime() - start;
    if (VERBOSE) {
      System.out.printf(
          "c sweep round at %d conflicts: swept %d of %d, %d units, %d equivalences, %d substituted,"
              + " %.2f s%n",
          conflicts,
          s.swept,
          m,
          s.units().length,
          s.equivalences,
          s.numSubstituted(),
          (System.nanoTime() - start) / 1e9);
    }
    return s;
  }

  /**
   * Whether an elimination round during search can find more than the last one: it eliminated
   * something, or new root facts or irredundant clauses appeared since.
   */
  private boolean eliminationDue() {
    return external != null
        || !eliminationFruitless
        || trailSize > eliminationTrail
        || numOriginals + numOriginalBinaries != eliminationOriginals;
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
      mem[ref + META] = (mem[ref + META] & NOT_POS) | POS_START;
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
        if (qStamp[v] < 0) {
          queueAppend(v);
        }
      }
    }
    qSearch = qLast; // eliminated variables were passed over
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
      restoring = true;
      try {
        addClause(c, size);
      } finally {
        restoring = false;
      }
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
    if (vivifySorted && !externalUsed && external == null) {
      return vivifyScheduled();
    }
    return vivifyLearntsOnce();
  }

  private boolean vivifyLearntsOnce() {
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
    // unwatched at once: the next propagation, of d[0] or of the next clause tried, must not use
    // it as a reason, which would keep pointing at a deleted clause
    removeWatch(mem[lits], ref);
    removeWatch(mem[lits + 1], ref);
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
   * Vivifies clauses at level 0 on a sorted schedule (Li, Xiao, Luo, Manyà, Lü, Li, "Clause
   * vivification by unit propagation in CDCL SAT solvers", Artificial Intelligence 279, 2020; Luo,
   * Li, Xiao, Manyà, Lü, "An effective learnt clause minimization approach for CDCL SAT solvers",
   * IJCAI 2017; the schedule of Kissat 4 and CaDiCaL 2: Biere, Faller, Fazekas, Fleury, Froleyks,
   * Pollitt, "CaDiCaL, Gimsatul, IsaSAT and Kissat entering the SAT Competition 2024", SAT
   * Competition 2024 solver descriptions). Each learnt tier and the irredundant clauses get a share
   * of a budget of propagations. A candidate's literals are sorted by their number of occurrences
   * in the round's candidates, and the candidates lexicographically on those counts, so that
   * consecutive candidates share their first decisions and the probe reuses them. The negation of
   * each literal is decided in turn, with the candidate itself left out of propagation; a conflict
   * or a candidate literal that becomes true is analysed back to the decisions, and the candidate
   * is replaced by the decisions involved, removed when another clause subsumes it or when it
   * follows from irredundant clauses alone, or strengthened by instantiation (deciding its last
   * literal true). Clauses not tried yet go first; once all were, all are tried again.
   *
   * @return false when the formula is found unsatisfiable
   */
  private boolean vivifyScheduled() {
    long t0 = System.nanoTime();
    boolean result = vivifyScheduledRound();
    vivifyNanos += System.nanoTime() - t0;
    return result;
  }

  private boolean vivifyScheduledRound() {
    vivifyDue = false;
    if (propagate() != NO_CONFLICT) {
      return refuted();
    }
    long total = Math.max(20_000, (propagations - propagationsAtVivify) * vivifyEffort / 1000);
    boolean wasChrono = chrono;
    chrono = false;
    boolean wasNotifying = notifying;
    notifying = false;
    keepPhases = vivifyKeepPhases;
    if (vivifyMark.length < 2 * numVars) {
      vivifyMark = new byte[2 * numVars];
      vivifySeen = new boolean[numVars];
      vivifyCounts = new int[2 * numVars];
    }
    boolean irredundant = vivifyIrredundant && numOriginals > 0;
    if (irredundant && vivifyIrrSkip > 0) {
      vivifyIrrSkip--;
      irredundant = false;
    }
    long sum = 0;
    for (int t = 0; t < 4; t++) {
      if (t < TIER_IRREDUNDANT || irredundant) {
        sum += vivifyWeights[t];
      }
    }
    boolean result = true;
    long limit = propagations;
    for (int t = 0; t < 4 && result && sum > 0; t++) {
      if (t == TIER_IRREDUNDANT && !irredundant || vivifyWeights[t] == 0) {
        continue;
      }
      limit += total * vivifyWeights[t] / sum;
      long tried = vivifyTried;
      long changed = vivifyStrengthenedIrredundant + vivifyRemovedIrredundant;
      result = vivifyRound(t, limit);
      if (t == TIER_IRREDUNDANT && result) {
        long n = vivifyTried - tried;
        long k = vivifyStrengthenedIrredundant + vivifyRemovedIrredundant - changed;
        if (n > 0 && 100 * k < n) {
          vivifyIrrSkip = ++vivifyIrrDelay;
        } else {
          vivifyIrrDelay /= 2;
        }
      }
    }
    ignoredRef = -1;
    backtrack(0);
    keepPhases = false;
    chrono = wasChrono;
    notifying = wasNotifying;
    originalBinaryKeys = null;
    propagationsAtVivify = propagations;
    purge();
    return result;
  }

  /** One round over the learnt clauses of a tier, or over the irredundant clauses. */
  private boolean vivifyRound(int tier, long limit) {
    backtrack(0);
    int[] list = tier == TIER_IRREDUNDANT ? originals : learnts;
    int n = tier == TIER_IRREDUNDANT ? numOriginals : numLearnts;
    int[] cand = new int[n];
    int m = 0;
    int untried = 0;
    for (int i = 0; i < n; i++) {
      int ref = list[i];
      int meta = mem[ref + META];
      if ((meta & DELETED) != 0
          || tier != TIER_IRREDUNDANT && tierOf(meta) != tier
          || !vivifyCandidate(ref)) {
        continue;
      }
      cand[m++] = ref;
      if ((meta & VIVIFIED) == 0) {
        untried++;
      }
    }
    if (m == 0) {
      return true;
    }
    if (untried == 0 && !vivifyRetry) {
      return true;
    }
    if (untried == 0) {
      for (int i = 0; i < m; i++) {
        mem[cand[i] + META] &= ~VIVIFIED;
      }
    }
    if (tier == TIER_IRREDUNDANT && originalBinaryKeys == null) {
      buildOriginalBinaryKeys();
    }
    // occurrences of the unassigned literals in the candidates
    int[] counts = vivifyCounts;
    int total = 0;
    for (int i = 0; i < m; i++) {
      int ref = cand[i];
      int size = mem[ref + SIZE];
      for (int k = 0; k < size; k++) {
        int l = mem[ref + HEADER + k];
        if (vals[l] == 0) {
          counts[l]++;
          total++;
        }
      }
    }
    // each candidate's unassigned literals, most frequent first
    int[] sorted = new int[total];
    int[] start = new int[m + 1];
    long[] keys = new long[16];
    int top = 0;
    for (int i = 0; i < m; i++) {
      int ref = cand[i];
      int size = mem[ref + SIZE];
      if (keys.length < size) {
        keys = new long[2 * size];
      }
      int q = 0;
      for (int k = 0; k < size; k++) {
        int l = mem[ref + HEADER + k];
        if (vals[l] == 0) {
          keys[q++] = ((long) (Integer.MAX_VALUE - counts[l]) << 32) | l;
        }
      }
      Arrays.sort(keys, 0, q);
      start[i] = top;
      for (int k = 0; k < q; k++) {
        sorted[top++] = (int) keys[k];
      }
    }
    start[m] = top;
    // candidates in order: untried first, then lexicographically by the counts (larger first),
    // shorter first on equal prefixes
    int[] order = new int[m];
    for (int i = 0; i < m; i++) {
      order[i] = i;
    }
    int[] buffer = new int[m];
    mergeSortCandidates(order, buffer, 0, m, cand, sorted, start, counts);
    for (int i = 0; i < m; i++) {
      int ref = cand[i];
      int size = mem[ref + SIZE];
      for (int k = 0; k < size; k++) {
        counts[mem[ref + HEADER + k]] = 0;
      }
    }
    boolean result = true;
    for (int i = 0; i < m && result && propagations < limit; i++) {
      int c = order[i];
      result = vivifyClauseSorted(cand[c], sorted, start[c], start[c + 1] - start[c]);
    }
    return result;
  }

  /**
   * Whether a clause is worth a probe: not satisfied at level 0, with three unassigned literals.
   */
  private boolean vivifyCandidate(int ref) {
    int size = mem[ref + SIZE];
    int free = 0;
    for (int k = 0; k < size; k++) {
      int v = vals[mem[ref + HEADER + k]];
      if (v > 0) {
        return false;
      }
      if (v == 0) {
        free++;
      }
    }
    return free > 2;
  }

  private void buildOriginalBinaryKeys() {
    long[] k = new long[numOriginalBinaries / 2];
    for (int i = 0; i + 1 < numOriginalBinaries; i += 2) {
      k[i / 2] = binaryKey(originalBinaries[i], originalBinaries[i + 1]);
    }
    Arrays.sort(k);
    originalBinaryKeys = k;
  }

  private static long binaryKey(int a, int b) {
    return a < b ? ((long) a << 32) | b : ((long) b << 32) | a;
  }

  private boolean isOriginalBinary(int a, int b) {
    return originalBinaryKeys != null
        && Arrays.binarySearch(originalBinaryKeys, binaryKey(a, b)) >= 0;
  }

  private void mergeSortCandidates(
      int[] a, int[] buf, int from, int to, int[] cand, int[] sorted, int[] start, int[] counts) {
    if (to - from < 2) {
      return;
    }
    int mid = (from + to) >>> 1;
    mergeSortCandidates(a, buf, from, mid, cand, sorted, start, counts);
    mergeSortCandidates(a, buf, mid, to, cand, sorted, start, counts);
    if (compareCandidates(a[mid - 1], a[mid], cand, sorted, start, counts) <= 0) {
      return;
    }
    System.arraycopy(a, from, buf, from, to - from);
    int i = from;
    int j = mid;
    for (int k = from; k < to; k++) {
      if (j >= to
          || i < mid && compareCandidates(buf[i], buf[j], cand, sorted, start, counts) <= 0) {
        a[k] = buf[i++];
      } else {
        a[k] = buf[j++];
      }
    }
  }

  /** Negative when candidate x goes before candidate y. */
  private int compareCandidates(int x, int y, int[] cand, int[] sorted, int[] start, int[] counts) {
    boolean tx = (mem[cand[x] + META] & VIVIFIED) == 0;
    boolean ty = (mem[cand[y] + META] & VIVIFIED) == 0;
    if (tx != ty) {
      return tx ? -1 : 1;
    }
    int p = start[x];
    int e = start[x + 1];
    int q = start[y];
    int f = start[y + 1];
    while (p < e && q < f) {
      int a = sorted[p++];
      int b = sorted[q++];
      if (counts[a] != counts[b]) {
        return counts[a] > counts[b] ? -1 : 1;
      }
      if (a != b) {
        return a < b ? -1 : 1;
      }
    }
    if ((e - p) != (f - q)) {
      return p < e ? 1 : -1;
    }
    return Integer.compare(x, y);
  }

  /**
   * Vivifies one clause whose literals, unassigned at the round's start, are sorted[from, from +
   * len): reuses the decisions of the previous probe that match, decides the negations of the
   * others, analyses, and changes the clause.
   *
   * @return false when the formula is found unsatisfiable
   */
  private boolean vivifyClauseSorted(int ref, int[] sorted, int from, int len) {
    int meta = mem[ref + META];
    if ((meta & DELETED) != 0) {
      return true;
    }
    mem[ref + META] = meta | VIVIFIED;
    boolean learntClause = (meta & LEARNT_FLAG) != 0;
    if (vivifyLits.length < len) {
      vivifyLits = new int[2 * len];
    }
    int[] lits = vivifyLits;
    int k = 0;
    for (int i = 0; i < len; i++) {
      int l = sorted[from + i];
      if (vals[l] != 0 && litLevel(l) == 0) {
        if (vals[l] > 0) {
          return true; // satisfied by a unit found in this round
        }
        continue;
      }
      lits[k++] = l;
    }
    if (k <= 2) {
      return true;
    }
    vivifyTried++;
    if (!learntClause) {
      vivifyTriedIrredundant++;
    }
    if (isLocked(ref)) {
      backtrack(litLevel(mem[ref + HEADER]) - 1);
    }
    for (int i = 0; i < k; i++) {
      vivifyMark[lits[i]] = 1;
    }
    ignoredRef = ref;
    int implied = -1;
    int conflict = NO_CONFLICT;
    int level = 0;
    probe:
    for (int i = 0; i < k; i++) {
      int l = lits[i];
      if (vals[l] != 0 && litLevel(l) <= level) {
        if (vals[l] > 0) {
          implied = l;
          break;
        }
        continue;
      }
      if (level < decisionLevel) {
        if (trail[trailLim[level]] == (l ^ 1)) {
          level++;
          vivifyReused++;
          continue;
        }
        backtrack(level);
      }
      newDecisionLevel();
      assign(l ^ 1, NO_REASON);
      level++;
      vivifyProbes++;
      int p = trailSize;
      conflict = propagate();
      if (conflict != NO_CONFLICT) {
        break;
      }
      for (; p < trailSize; p++) {
        if (vivifyMark[trail[p]] == 1) {
          implied = trail[p];
          break probe;
        }
      }
    }
    backtrack(level);
    if (implied >= 0) {
      // the candidate literal implied first
      for (int i = 0; i < k; i++) {
        int l = lits[i];
        if (vals[l] > 0 && varTrailPos(l >> 1) < varTrailPos(implied >> 1)) {
          implied = l;
        }
      }
    }
    boolean result = true;
    boolean changed = false;
    if (conflict != NO_CONFLICT || implied >= 0) {
      int analysis = vivifyAnalyse(ref, learntClause, conflict, implied);
      if (conflict != NO_CONFLICT) {
        backtrack(decisionLevel - 1);
      }
      changed = true;
      if (analysis == ANALYSIS_SUBSUMED) {
        removeVivified(ref, learntClause);
      } else if (analysis != ANALYSIS_UNKNOWN && numVivifyOut < mem[ref + SIZE]) {
        result = replaceVivified(ref, meta, vivifyOut, numVivifyOut);
      } else if (analysis != ANALYSIS_UNKNOWN
          && (learntClause && implied >= 0 && vivifyDropImplied
              || !learntClause && analysis == ANALYSIS_IRREDUNDANT)) {
        removeVivified(ref, learntClause);
      } else {
        changed = false;
      }
      clearVivifyAnalysis();
    }
    if (!changed
        && implied < 0
        && vivifyInstantiate
        && level == k
        && decisionLevel == k - (conflict != NO_CONFLICT ? 1 : 0)) {
      // instantiation: with the other literals false, the last literal true leads to a conflict
      backtrack(k - 1);
      int last = lits[k - 1];
      newDecisionLevel();
      assign(last, NO_REASON);
      vivifyProbes++;
      if (propagate() != NO_CONFLICT) {
        backtrack(k - 2);
        changed = true;
        result = replaceVivified(ref, meta, lits, k - 1);
      } else {
        backtrack(k - 2);
      }
    }
    for (int i = 0; i < k; i++) {
      vivifyMark[lits[i]] = 0;
    }
    ignoredRef = -1;
    if (!changed && result) {
      reestablishWatches(ref);
    }
    return result;
  }

  private static final int ANALYSIS_UNKNOWN = 0;
  private static final int ANALYSIS_SUBSUMED = 1;
  // the derivation used only irredundant clauses
  private static final int ANALYSIS_IRREDUNDANT = 2;
  // the derivation used a learnt clause
  private static final int ANALYSIS_REDUNDANT = 3;

  /**
   * Analyses a vivification conflict, or the implication of the candidate literal implied, back to
   * the decisions; vivifyOut gets the candidate literals the derivation needs.
   */
  private int vivifyAnalyse(int candidate, boolean learntCandidate, int conflict, int implied) {
    numVivifyOut = 0;
    numVivifyAnalysed = 0;
    boolean redundant = false;
    if (implied >= 0) {
      vivifySeen[implied >> 1] = true;
      pushVivifyAnalysed(implied ^ 1);
      vivifyOut = push(vivifyOut, numVivifyOut++, implied);
    } else if (conflict == BINARY_CONFLICT) {
      int a = conflictLit0;
      int b = conflictLit1;
      boolean original = isOriginalBinary(a, b);
      redundant = !original;
      if (vivifyMark[a] == 1 && vivifyMark[b] == 1 && (original || learntCandidate)) {
        return ANALYSIS_SUBSUMED;
      }
      analyseFalse(a);
      analyseFalse(b);
    } else {
      int size = mem[conflict + SIZE];
      boolean learnt = (mem[conflict + META] & LEARNT_FLAG) != 0;
      redundant = learnt;
      boolean subsumes = true;
      for (int j = 0; j < size; j++) {
        int l = mem[conflict + HEADER + j];
        if (vivifyMark[l] != 1) {
          subsumes = false;
        }
        analyseFalse(l);
      }
      if (subsumes && (!learnt || learntCandidate)) {
        return ANALYSIS_SUBSUMED;
      }
    }
    for (int i = 0; i < numVivifyAnalysed; i++) {
      int f = vivifyAnalysed[i];
      int t = f ^ 1;
      int r = varReason(t >> 1);
      if (r == NO_REASON) {
        vivifyOut = push(vivifyOut, numVivifyOut++, f);
      } else if (r <= -2 && r > EXTERNAL_REASON) {
        int other = -2 - r;
        boolean original = isOriginalBinary(t, other);
        if (!original) {
          redundant = true;
        }
        if (vivifyMark[t] == 1 && vivifyMark[other] == 1 && (original || learntCandidate)) {
          return ANALYSIS_SUBSUMED;
        }
        analyseFalse(other);
      } else if (r >= 0 && r < STACK_REF) {
        int size = mem[r + SIZE];
        boolean learnt = (mem[r + META] & LEARNT_FLAG) != 0;
        if (learnt) {
          redundant = true;
        }
        boolean subsumes = true;
        for (int j = 0; j < size; j++) {
          int l = mem[r + HEADER + j];
          if (vivifyMark[l] != 1) {
            subsumes = false;
          }
          if (l != t) {
            analyseFalse(l);
          }
        }
        if (subsumes && (!learnt || learntCandidate)) {
          return ANALYSIS_SUBSUMED;
        }
      } else {
        return ANALYSIS_UNKNOWN; // a reason vivification does not know
      }
    }
    return redundant ? ANALYSIS_REDUNDANT : ANALYSIS_IRREDUNDANT;
  }

  /** Queues a false literal above level 0 for the vivification analysis. */
  private void analyseFalse(int l) {
    int v = l >> 1;
    if (vivifySeen[v] || varLevel(v) == 0) {
      return;
    }
    vivifySeen[v] = true;
    pushVivifyAnalysed(l);
  }

  private void pushVivifyAnalysed(int l) {
    vivifyAnalysed = push(vivifyAnalysed, numVivifyAnalysed++, l);
  }

  private void clearVivifyAnalysis() {
    for (int i = 0; i < numVivifyAnalysed; i++) {
      vivifySeen[vivifyAnalysed[i] >> 1] = false;
    }
    numVivifyAnalysed = 0;
  }

  /** Removes a vivified clause (subsumed, implied, or an asymmetric tautology). */
  private void removeVivified(int ref, boolean learntClause) {
    removeWatch(mem[ref + HEADER], ref);
    removeWatch(mem[ref + HEADER + 1], ref);
    deleteClause(ref);
    vivifyRemoved++;
    if (!learntClause) {
      vivifyRemovedIrredundant++;
    }
  }

  /**
   * Replaces a vivified clause by the shorter clause lits[0, n), which the formula implies.
   *
   * @return false when the formula is found unsatisfiable
   */
  private boolean replaceVivified(int ref, int meta, int[] lits, int n) {
    boolean learntClause = (meta & LEARNT_FLAG) != 0;
    vivifyStrengthened++;
    if (!learntClause) {
      vivifyStrengthenedIrredundant++;
    }
    if (n == 0) {
      return refuted();
    }
    if (proof != null) {
      proof.add(lits, 0, n);
    }
    removeWatch(mem[ref + HEADER], ref);
    removeWatch(mem[ref + HEADER + 1], ref);
    deleteClause(ref);
    if (n <= 2) {
      backtrack(0);
      if (n == 1) {
        assign(lits[0], NO_REASON);
        return propagate() == NO_CONFLICT || refuted();
      }
      if (learntClause) {
        addLearntBinary(lits[0], lits[1]);
      } else {
        addOriginalBinary(lits[0], lits[1]);
      }
      return true;
    }
    int copy = allocate(lits, n, learntClause, learntClause ? Math.min(lbdOf(meta), n - 1) : 0);
    mem[copy + META] |= VIVIFIED;
    mem[copy + ACT] = mem[ref + ACT];
    if (learntClause) {
      learnts = push(learnts, numLearnts++, copy);
    } else {
      originals = push(originals, numOriginals++, copy);
    }
    bestWatchFirst(copy, 0);
    bestWatchFirst(copy, 1);
    attach(copy);
    reestablishWatches(copy);
    return true;
  }

  /** Moves the best watch among the literals from position at onwards to that position. */
  private void bestWatchFirst(int ref, int at) {
    int lits = ref + HEADER;
    int size = mem[ref + SIZE];
    int best = at;
    int bestLevel = -1;
    for (int k = at; k < size; k++) {
      int l = mem[lits + k];
      if (vals[l] >= 0) {
        best = k;
        break;
      }
      int lv = litLevel(l);
      if (lv > bestLevel) {
        bestLevel = lv;
        best = k;
      }
    }
    int x = mem[lits + at];
    mem[lits + at] = mem[lits + best];
    mem[lits + best] = x;
  }

  /**
   * Backtracks until the watches of a clause satisfy the invariant again: the probe that skipped
   * it, or its new literals, can leave it unit, false, or true above a false watch.
   */
  private void reestablishWatches(int ref) {
    if (decisionLevel == 0) {
      return;
    }
    int first = mem[ref + HEADER];
    int second = mem[ref + HEADER + 1];
    int fv = vals[first];
    int sv = vals[second];
    if (fv >= 0 && sv >= 0) {
      return;
    }
    int fl = fv != 0 ? litLevel(first) : 0;
    int sl = sv != 0 ? litLevel(second) : 0;
    int target;
    if (fv < 0 && sv == 0) {
      target = fl;
    } else if (fv < 0 && sv > 0) {
      if (fl >= sl) {
        return;
      }
      target = fl;
    } else if (sv < 0 && fv == 0) {
      target = sl;
    } else if (sv < 0 && fv > 0) {
      if (sl >= fl) {
        return;
      }
      target = sl;
    } else {
      target = Math.min(fl, sl);
    }
    backtrack(Math.max(0, target - 1));
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
  /**
   * Sets the size, in ints of the clause arena, past which the learnt clauses are reduced before
   * their next scheduled reduction, for tests; by default 1/16 of the heap.
   *
   * @param ints the size
   */
  void setLearntBudget(long ints) {
    learntBudget = ints;
  }

  /**
   * Sets the bytes that elimination and local search may take for their copies of the clauses, for
   * tests; by default a quarter of the heap. Past it they are skipped.
   *
   * @param bytes the budget
   */
  void setCopyBudget(long bytes) {
    copyBudget = bytes;
  }

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
   * Decides in focused mode by the VMTF queue (variable move-to-front, Ryan's thesis 2004; as in
   * CaDiCaL and Kissat, Biere and Fröhlich, "Evaluating CDCL Variable Scoring Schemes", SAT 2015)
   * instead of the activity heap, which then serves stable mode only (off by default). The
   * variables of a conflict analysis move to the end of the queue in their old order, and a
   * decision takes the most recently moved unassigned variable; the queue starts with the first
   * variable at its end. A stable phase leaves the queue of the next focused phase as it was, while
   * focused mode still bumps the activities, so the heap of the next stable phase keeps learning
   * (CaDiCaL and Kissat bump only the heuristic of the mode: on the 90 CNFs of the SAT screen that
   * solved 38 instead of 41 at 240 s). Ignored under an external propagator.
   *
   * @param on whether focused mode uses the queue
   */
  public void setVmtf(boolean on) {
    vmtf = on;
    qSearch = qLast;
  }

  /**
   * The decision of the queue: the last unassigned variable from qSearch back, at its saved sign.
   */
  private int pickFromQueue() {
    int v = qSearch;
    while (v >= 0 && (vals[2 * v] != 0 || eliminatedVar[v])) {
      int pv = qPrev[v];
      if (eliminatedVar[v]) {
        queueUnlink(v); // walked over by every later decision otherwise
        qStamp[v] = -1;
      }
      v = pv;
    }
    qSearch = v;
    return v < 0 ? -1 : 2 * v + savedSign[v];
  }

  private boolean queueInUse() {
    return vmtf && !stable && external == null;
  }

  private void queueAppend(int v) {
    qPrev[v] = qLast;
    qNext[v] = -1;
    if (qLast >= 0) {
      qNext[qLast] = v;
    } else {
      qFirst = v;
    }
    qLast = v;
    qStamp[v] = ++qBumped;
  }

  private void queueUnlink(int v) {
    int pv = qPrev[v];
    int nv = qNext[v];
    if (pv >= 0) {
      qNext[pv] = nv;
    } else {
      qFirst = nv;
    }
    if (nv >= 0) {
      qPrev[nv] = pv;
    } else {
      qLast = pv;
    }
    if (qSearch == v) {
      qSearch = pv;
    }
  }

  /** Sorts qKeys so that the low 26 bits of qKeys[i] index qToBump by increasing stamp. */
  private void sortBumped(int n) {
    if (qKeys.length < n) {
      qKeys = new long[Math.max(n, 2 * qKeys.length)];
    }
    for (int i = 0; i < n; i++) {
      qKeys[i] = qStamp[qToBump[i]] << 26 | i;
    }
    if (n >= 1 << 26) {
      Arrays.sort(qToBump, 0, n); // too many for the keys: any order is still correct
      for (int i = 0; i < n; i++) {
        qKeys[i] = i;
      }
    } else {
      Arrays.sort(qKeys, 0, n);
    }
  }

  /** Moves the analysed variables to the end of the queue, in the order of their old stamps. */
  private void bumpQueue() {
    int n = qToBumpSize;
    if (n == 0) {
      return;
    }
    qToBumpSize = 0;
    if (qBumped + n >= 1L << 37) {
      long renumbered = 0; // renumber along the queue before the stamps outgrow the sort keys
      for (int v = qFirst; v >= 0; v = qNext[v]) {
        qStamp[v] = ++renumbered;
      }
      qBumped = renumbered;
    }
    sortBumped(n);
    for (int i = 0; i < n; i++) {
      int v = qToBump[(int) (qKeys[i] & ((1 << 26) - 1))];
      if (v != qLast) {
        queueUnlink(v);
        queueAppend(v);
      } else {
        qStamp[v] = ++qBumped;
      }
      if (vals[2 * v] == 0) {
        qSearch = v;
      }
    }
  }

  /**
   * Keeps the search in stable mode once it gets there (off by default): the first focused phase
   * runs as usual, and from the first switch on, restarts follow only the Luby sequence. An
   * external propagator pays for every restart with its own propagation from level 0.
   *
   * @param on whether to stay in stable mode after the first switch
   */
  public void setStableForGood(boolean on) {
    stableForGood = on;
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

  // a restart to the root at this time, also without restarts (see restartAt)
  private long forcedRestartAt = Long.MAX_VALUE;
  private boolean forcedRestart;

  /**
   * Restarts the search once, back to level 0, at the first decision after the given time, also
   * when restarts are off.
   *
   * @param nanoTime the time, as {@link #now} gives it.
   */
  public void restartAt(long nanoTime) {
    forcedRestartAt = nanoTime;
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
            if (varReason(v) == ref) {
              vdata[v << 2 | REASON] = NO_REASON;
              if (proof != null && vals[mem[ref + HEADER]] > 0 && varLevel(v) == 0) {
                // the root fact outlives its reason in the proof as well
                proof.add(mem, ref + HEADER, 1);
              }
            }
            deleteClause(ref);
            break;
          }
        }
      }
    }
    purge();
    simplifyAssigns = trailSize;
    // the arena counted with one more int per clause, as with the earlier four-int header, so the
    // simplification schedule (and the search) stays as it was
    simplifyProps = propagations + memSize - wasted + numOriginals + numLearnts + 2L * numVars;
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
      long[] ws = watches[lit];
      int n = (int) ws[0];
      int j = 1;
      for (int i = 1; i < n; i++) {
        if ((mem[watchRef(ws[i]) + META] & DELETED) == 0) {
          ws[j++] = ws[i];
        }
      }
      if (j != n) {
        ws[0] = j;
      }
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
    // watched clauses first, in the order propagation visits them: the watch lists of the most
    // active variables first, each list's clauses side by side (CaDiCaL's arena moving)
    long[] byActivity = new long[numVars];
    for (int v = 0; v < numVars; v++) {
      byActivity[v] = (long) Float.floatToRawIntBits((float) Math.log1p(activity[v])) << 32 | v;
    }
    Arrays.sort(byActivity);
    for (int o = numVars - 1; o >= 0; o--) {
      int v = (int) byActivity[o];
      for (int lit = 2 * v; lit <= 2 * v + 1; lit++) {
        long[] ws = watches[lit];
        int n = (int) ws[0];
        for (int i = 1; i < n; i++) {
          top = moveClause(watchRef(ws[i]), to, top);
        }
      }
    }
    int off = 0;
    while (off < memSize) {
      int len = HEADER + mem[off + SIZE];
      top = moveClause(off, to, top);
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
      int r = varReason(v);
      if (r >= 0 && r < STACK_REF) {
        vdata[v << 2 | REASON] = (mem[r + META] & DELETED) == 0 ? mem[r + ACT] : NO_REASON;
      }
    }
    for (int lit = 0; lit < 2 * numVars; lit++) {
      long[] ws = watches[lit];
      int n = (int) ws[0];
      int j = 1;
      for (int i = 1; i < n; i++) {
        int ref = watchRef(ws[i]);
        if ((mem[ref + META] & DELETED) == 0) {
          ws[j++] = watch(watchBlocker(ws[i]), mem[ref + ACT]);
        }
      }
      if (j != n) {
        ws[0] = j;
      }
    }
    int j = 0;
    for (int i = 0; i < numLowWatched; i += 3) {
      int ref = lowWatched[i];
      if (ref < 0 || (mem[ref + META] & DELETED) == 0) {
        lowWatched[j++] = ref < 0 ? ref : mem[ref + ACT];
        lowWatched[j++] = lowWatched[i + 1];
        lowWatched[j++] = lowWatched[i + 2];
      }
    }
    numLowWatched = j;
    mem = to;
    memSize = top;
    wasted = 0;
  }

  /**
   * Copies a live clause of the arena to {@code to} at {@code top} unless it is deleted or already
   * moved, and leaves its new reference in its old ACT field.
   *
   * @return the new top of {@code to}
   */
  private int moveClause(int ref, int[] to, int top) {
    int meta = mem[ref + META];
    if ((meta & (DELETED | MOVED)) != 0) {
      return top;
    }
    int len = HEADER + mem[ref + SIZE];
    System.arraycopy(mem, ref, to, top, len);
    mem[ref + META] = meta | MOVED;
    mem[ref + ACT] = top; // forwarding address
    return top + len;
  }

  // ---------------------------------------------------------------------------- self-check

  /** Tests: checks the propagation invariants at every fixpoint (before a decision). */
  void setChecking(boolean on) {
    checking = on;
  }

  /**
   * Checks, at a unit propagation fixpoint, that no clause is false or unit, that every attached
   * clause is watched by its first two literals, and that every reason clause holds its literal
   * first with the other literals false earlier on the trail and at no higher level.
   *
   * @throws IllegalStateException with the first violation found
   */
  void checkFixpoint() {
    if (!ok || hasPending) {
      return;
    }
    if (qhead != trailSize) {
      throw new IllegalStateException("fixpoint with " + (trailSize - qhead) + " literals queued");
    }
    for (int i = 0; i < trailSize; i++) {
      int lit = trail[i];
      int v = lit >> 1;
      if (vals[lit] <= 0 || vals[lit ^ 1] >= 0 || varTrailPos(v) != i) {
        throw new IllegalStateException("trail entry " + i + " inconsistent: " + toDimacs(lit));
      }
      if (varLevel(v) > decisionLevel) {
        throw new IllegalStateException(toDimacs(lit) + " above the decision level");
      }
      int at = 0;
      while (at < decisionLevel && trailLim[at] <= i) {
        at++;
      }
      if (varLevel(v) > at || (!chrono && varLevel(v) != at)) {
        throw new IllegalStateException(
            toDimacs(lit) + " at level " + varLevel(v) + " but in the trail of level " + at);
      }
      checkReason(lit, i);
    }
    int assigned = 0;
    for (int v = 0; v < numVars; v++) {
      if (vals[2 * v] != 0) {
        assigned++;
      }
      if (vals[2 * v] != -vals[2 * v + 1]) {
        throw new IllegalStateException("values of variable " + (v + 1) + " inconsistent");
      }
    }
    if (assigned != trailSize) {
      throw new IllegalStateException(assigned + " variables assigned, trail " + trailSize);
    }
    markWatched();
    for (int pass = 0; pass < 2; pass++) {
      int[] list = pass == 0 ? originals : learnts;
      int n = pass == 0 ? numOriginals : numLearnts;
      for (int i = 0; i < n; i++) {
        int ref = list[i];
        if ((mem[ref + META] & DELETED) != 0) {
          continue;
        }
        checkWatched(ref);
        checkClause(mem, ref + HEADER, mem[ref + SIZE], pass == 0 ? "original" : "learnt");
      }
    }
    for (int l = 0; l < 2 * numVars; l++) {
      for (int i = 1; i < watches[l][0]; i++) {
        watchedMarks[watchRef(watches[l][i])] = 0;
      }
    }
    int[] pair = new int[2];
    for (int l = 0; l < 2 * numVars; l++) {
      for (int b = 1; b < binWatches[l][0]; b++) {
        pair[0] = l;
        pair[1] = binWatches[l][b];
        checkClause(pair, 0, 2, "binary");
      }
    }
  }

  // per clause reference, bit k set when the clause is in the watch list of its k-th literal
  private int[] watchedMarks = new int[0];

  /**
   * Marks every clause found in the watch list of its first or second literal, in one pass over the
   * watch lists, so that checking all clauses stays linear when a watch list is long.
   */
  private void markWatched() {
    if (watchedMarks.length < mem.length) {
      watchedMarks = new int[mem.length];
    }
    for (int l = 0; l < 2 * numVars; l++) {
      for (int i = 1; i < watches[l][0]; i++) {
        int ref = watchRef(watches[l][i]);
        for (int k = 0; k < 2 && ref + HEADER + k < mem.length; k++) {
          if (mem[ref + HEADER + k] == l) {
            watchedMarks[ref] |= 1 << k;
          }
        }
      }
    }
  }

  private void checkWatched(int ref) {
    for (int k = 0; k < 2; k++) {
      if ((watchedMarks[ref] & 1 << k) == 0) {
        throw new IllegalStateException(
            "clause "
                + clauseText(mem, ref + HEADER, mem[ref + SIZE])
                + " not watched by "
                + toDimacs(mem[ref + HEADER + k]));
      }
    }
  }

  private void checkClause(int[] lits, int from, int size, String kind) {
    int open = 0;
    int unassigned = -1;
    for (int k = from; k < from + size; k++) {
      int l = lits[k];
      if (eliminatedVar[l >> 1]) {
        throw new IllegalStateException(
            kind + " clause " + clauseText(lits, from, size) + " on an eliminated variable");
      }
      if (vals[l] > 0) {
        return;
      }
      if (vals[l] == 0) {
        open++;
        unassigned = l;
      }
    }
    if (open == 0) {
      throw new IllegalStateException(
          kind + " clause " + clauseText(lits, from, size) + " false at the fixpoint");
    }
    if (open == 1) {
      throw new IllegalStateException(
          kind
              + " clause "
              + clauseText(lits, from, size)
              + " unit at the fixpoint (implies "
              + toDimacs(unassigned)
              + ", decision level "
              + decisionLevel
              + ")");
    }
  }

  private void checkReason(int lit, int pos) {
    int v = lit >> 1;
    int r = varReason(v);
    if (r == NO_REASON || r == UNIT_REASON || r == EXTERNAL_REASON) {
      return;
    }
    if (r < NO_REASON) {
      int other = -2 - r;
      boolean found = false;
      for (int b = 1; b < binWatches[lit][0] && !found; b++) {
        found = binWatches[lit][b] == other;
      }
      if (!found) {
        throw new IllegalStateException(
            "binary reason " + toDimacs(lit) + " " + toDimacs(other) + " is not a clause");
      }
      checkAntecedent(lit, other, pos);
      return;
    }
    int[] a = reasonArena(r);
    int off = reasonOffset(r);
    if (r >= STACK_REF ? a[off + META] != v : (a[off + META] & DELETED) != 0) {
      throw new IllegalStateException("reason of " + toDimacs(lit) + " deleted");
    }
    if (a[off + HEADER] != lit) {
      throw new IllegalStateException(
          "reason "
              + clauseText(a, off + HEADER, a[off + SIZE])
              + " of "
              + toDimacs(lit)
              + " does not hold it first");
    }
    for (int k = 1; k < a[off + SIZE]; k++) {
      checkAntecedent(lit, a[off + HEADER + k], pos);
    }
  }

  private void checkAntecedent(int lit, int q, int pos) {
    int u = q >> 1;
    if (vals[q] >= 0 || varTrailPos(u) >= pos || varLevel(u) > litLevel(lit)) {
      throw new IllegalStateException(
          "reason of " + toDimacs(lit) + " has " + toDimacs(q) + " not false before it");
    }
  }

  private static String clauseText(int[] lits, int from, int size) {
    StringBuilder b = new StringBuilder("(");
    for (int k = from; k < from + size; k++) {
      b.append(k > from ? " " : "").append(toDimacs(lits[k]));
    }
    return b.append(')').toString();
  }
}
