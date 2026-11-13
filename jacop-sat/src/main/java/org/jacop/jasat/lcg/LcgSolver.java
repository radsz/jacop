/*
 * LcgSolver.java
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

package org.jacop.jasat.lcg;

import java.io.IOException;
import java.io.OutputStream;
import java.io.UncheckedIOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SplittableRandom;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.function.IntSupplier;
import java.util.function.LongConsumer;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Alldistinct;
import org.jacop.constraints.Circuit;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.constraints.lp.LinearRelaxation;
import org.jacop.constraints.regular.LayeredGraphConstraint;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.jasat.cdcl.ExternalPropagator;
import org.jacop.jasat.cdcl.VarHeap;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.ClauseModel;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.ExplanationChecker;
import org.jacop.lcg.ExplanationMinimality;
import org.jacop.lcg.ImpliedClauses;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.Mirrored;
import org.jacop.lcg.MirroredChoice;
import org.jacop.lcg.PbModel;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.free.SharedSolution;
import org.jacop.search.lns.AdaptiveLns;

/**
 * Lazy clause generation with JaSAT: the constraints of a store propagate as an external propagator
 * of {@link CdclSolver}, whose conflict analysis learns from their explanations.
 *
 * <p>The atoms of the store's {@link AtomicTrail} are the solver's literals {@code [x >= v]} and
 * {@code [x = v]}, created lazily when an atom, a reason or a decision first needs one. Each new
 * {@code [x >= v]} is linked by clauses to the nearest ones of its variable and each {@code [x =
 * v]} to {@code [x >= v]} and {@code [x >= v + 1]}. The store level follows the solver's decision
 * level. When the solver assigns literals they are applied to the domains and the store propagates;
 * every atom it records goes back to the solver with its explanation as reason, and a failure
 * becomes a conflict clause of the explanations. When every literal is assigned and a variable is
 * not fixed, the solver branches on {@code [x <= min]} of the unfixed variable with the smallest
 * domain.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LcgSolver implements ExternalPropagator {

  private static final int GE_KIND = 0;
  private static final int EQ_KIND = 1;

  private final Store store;
  private final CdclSolver sat = new CdclSolver();
  private final AtomicTrail trail;
  private final int baseLevel;
  private boolean rootFailed;

  /**
   * Whether the property {@code jacop.lcg.fullFixpoint} is set; it then decides {@link
   * #setFullFixpoint} for every model.
   */
  public static final boolean FULL_FIXPOINT_SET =
      System.getProperty("jacop.lcg.fullFixpoint") != null;

  /**
   * Runs the store to its fixpoint before clauses propagate again; false returns to the clauses
   * after each pruning.
   */
  private boolean fullFixpoint =
      Boolean.parseBoolean(System.getProperty("jacop.lcg.fullFixpoint", "true"));

  // per variable (by trail id): the root domain and the literals created so far (value -> variable)
  private IntVar[] vars = new IntVar[0];
  private IntDomain[] root = new IntDomain[0];
  private final LiteralMap[] ge;
  private final LiteralMap[] eq;
  // the literals of ge linked to their neighbours by binary clauses; the others are transient
  private final LiteralMap[] linked;

  /**
   * Releases the literals created only to push a bound, as in Chuffed's lazy literals with the
   * unused ones collected: such a literal is in no clause, and when the level it was created at is
   * backtracked, its variable is given to the next new literal. The literals of a variable then
   * stay few, so a bound change no longer runs down a long chain of binary clauses.
   */
  private static final boolean RELEASE =
      !"false".equals(System.getProperty("jacop.lcg.releaseLiterals"));

  // per DIMACS variable: true while a transient literal, in no clause and not linked
  private boolean[] transientLit = new boolean[16];
  // the transient literals by the decision level they were created at
  private int[] transients = new int[64];
  private int[] transientLevel = new int[64];
  private int numTransients;
  // released DIMACS variables, given to the next new literals
  private int[] free = new int[16];
  private int numFree;
  // linked literals the domains imply, with the entries that imply them, pushed first
  private int[] impliedLits = new int[16];
  private int[] impliedEntries = new int[16];
  private int numImplied;

  /** Statistics: transient literals released. */
  public long literalsReleased;

  /**
   * The solver variables in use above which a value removal with no literal of its own is kept out
   * of the solver: a clause that would cite it cites its explanation instead. Each solver variable
   * costs a few hundred bytes, and an alldiff over 4096 variables of 4096 values removes 8.4
   * million values on one branch, more than a 3 GB heap holds. The system property {@code
   * jacop.lcg.literalBudget} sets it; by default one variable per 1 KB of the maximum heap.
   */
  private long literalBudget =
      Long.getLong("jacop.lcg.literalBudget", Runtime.getRuntime().maxMemory() / 1024);

  /** Statistics: value removals kept out of the solver (see {@link #literalBudget}). */
  public long deferredAtoms;

  private final EntryList scratchEntries = new EntryList();

  /** Statistics: literals [x >= v] linked to their neighbours. */
  public long boundLiterals;

  /** Statistics: literals [x = v]. */
  public long equalityLiterals;

  /** Statistics: transient literals, created to push an atom and released unless kept. */
  public long transientLiterals;

  /** Statistics: solver variables that are not atoms, such as outputs of encodings. */
  public long auxiliaryVariables;

  // per DIMACS variable: its variable's trail id, kind and value
  private int[] litVar = new int[16];
  private byte[] litKind = new byte[16];
  private int[] litValue = new int[16];
  // semantic minimisation: learnt literals sorted by variable, and those removed
  private long[] minimizeKeys = new long[16];
  private boolean[] minimizeRemoved = new boolean[16];

  // clauses linking new literals, added through externalClause
  private final ArrayDeque<int[]> structural = new ArrayDeque<>();

  // SAT assignments not yet applied to the domains
  private int[] pending = new int[64];
  private int numPending;

  // per trail entry recorded while applying a solver literal: that literal
  private int[] cause = new int[64];

  private int pushed; // trail entries below are true in the solver
  private boolean failed;
  private int[] pushedReason;
  // buffers of conflict and reason: the atoms to explain, those in the solver, other literals,
  // and stamps of the entries explained and of the clause's literals (by 2 * variable + sign)
  private final EntryList failureAtoms = new EntryList();
  private final EntryList conflictInSolver = new EntryList();
  private final EntryList conflictLits = new EntryList();
  private final EntryList reasonEntries = new EntryList();
  private int[] entryStamp = new int[64];
  // the slack of each entry in the current conflict, valid where entryStamp has its stamp
  private int[] entrySlack = new int[64];
  private int[] litStamp = new int[64];
  private int stamp;
  private int[] propagated = new int[16]; // per DIMACS variable pushed as an atom: its entry
  private int[] solution;
  private Runnable onSolution;
  // takes the objective's bound at the root each time minimize leaves the root with a better one
  private LongConsumer onBound;
  private long lastBound = Long.MIN_VALUE;
  private ExplanationChecker checker;
  private final Map<String, long[]> explanationCounts = new TreeMap<>();

  // every this many explanations one is minimised (see ExplanationChecker#minimise), 0 for none
  private final int minimality = Integer.getInteger("jacop.lcg.minimality", 0);
  private ExplanationMinimality minimiser;
  private long untilMinimised;
  private final Map<String, long[]> minimalityCounts = new TreeMap<>();

  // cut-based conflict analysis of linear failures (LinearConflict): "stats" only counts what it
  // derives, "learn" also imposes each learnt sum at the root, the next time the search is there
  private final String linearMode = System.getProperty("jacop.lcg.linear", "off");
  private LinearConflict linear;
  private final List<LinearForm> learntLinear = new ArrayList<>();
  private final Set<LinearForm> learntSeen = new HashSet<>();
  private final int linearLimit = Integer.getInteger("jacop.lcg.linearLimit", 20_000);

  /** Learnt linear sums imposed. */
  public long linearImposed;

  /** Statistics: reasons the solver asked for. */
  public long reasons;

  /** Statistics: literals of those reasons. */
  public long reasonLiterals;

  /** Statistics: solutions found by {@link #minimize}. */
  public long solutions;

  /** Statistics: atoms propagated to the solver. */
  public long atomsPropagated;

  /** Statistics: reason literals replaced by a weaker literal the solver already has. */
  public long liftedLiterals;

  // cite a weaker existing literal for a lifted bound, unless -Djacop.lcg.liftLiterals=false
  private final boolean liftLiterals =
      !"false".equals(System.getProperty("jacop.lcg.liftLiterals"));

  /** Statistics: distinct literals pushed as atoms. */
  public long atomLiterals;

  /** Statistics: distinct literals pushed as atoms that occur in a learnt clause. */
  public long atomLiteralsLearnt;

  // per DIMACS variable: 1 once pushed as an atom, 2 once it also occurred in a learnt clause
  private byte[] atomUse = new byte[16];

  /** Statistics: failures of the constraints turned into conflict clauses. */
  public long constraintConflicts;

  /**
   * Statistics: decisions made on integer variables, by activity or when every literal was
   * assigned.
   */
  public long searchDecisions;

  /** Statistics: activity decisions on late variables (see {@link #setLateVariables}). */
  public long lateDecisions;

  /** Statistics: the late variables (see {@link #setLateVariables}). */
  public long lateVariables;

  /** Statistics: the unfixed 0/1 variables at the start, late ones included. */
  public long booleanVariables;

  /** Statistics: the unfixed variables at the start that are not 0/1, late ones included. */
  public long wideVariables;

  /** Statistics: decisions taken from the model's search annotation. */
  public long annotationDecisions;

  // the selection that starts the activity runs of fixed search with restarts, or null
  private SelectChoicePoint<? extends Var> activityGuide;

  /** Statistics: decisions taken from the selection that starts the activity runs. */
  public long guideDecisions;

  /** How decisions are made outside the runs of the search annotation. */
  public enum Branching {
    /** On the most active integer variable, by the activity of its literals in learnt clauses. */
    ACTIVITY,
    /** The SAT solver's own decisions on literals, by their activity and saved phases. */
    LITERALS,
    /**
     * As LITERALS, but as ACTIVITY from {@link #AUTO_CONFLICTS} conflicts to the first solution.
     */
    AUTO,
    /**
     * Runs take turns at each restart: with an annotation under free search, the annotation
     * (completed by ACTIVITY), then LITERALS, then ACTIVITY; without one, LITERALS and ACTIVITY.
     */
    ALTERNATE
  }

  /** Restarts under fixed search: how the runs between restarts branch. */
  public enum FixedRestarts {
    /** No restarts: the annotation is followed down each branch, as without learning. */
    OFF,
    /** Every run follows the annotation from its first variable, with the learnt clauses kept. */
    REPLAY,
    /** Runs take turns at each restart: the annotation, then activity branching. */
    ALTERNATE,
    /**
     * Runs take turns at each restart: the annotation, the SAT solver's own decisions on literals,
     * then activity branching, as {@link Branching#ALTERNATE} does under free search.
     */
    TURNS
  }

  /** Conflicts without a solution after which {@link Branching#AUTO} uses activity branching. */
  public static final long AUTO_CONFLICTS = 1000;

  private Branching branching =
      Branching.valueOf(System.getProperty("jacop.lcg.branching", "activity").toUpperCase());
  // whether decisions are on the most active variable, now
  private boolean activityBranching = branching == Branching.ACTIVITY;
  private long runs; // restarts so far, for the turns of Branching.ALTERNATE
  // whether a run that improved the best solution keeps its turn at the next restart
  private boolean keepImprovingRun;
  private boolean improvedInRun;
  private final String valueChoice = System.getProperty("jacop.lcg.value", "split");
  // last-conflict branching, on unless -Djacop.lcg.lastConflict=false
  private final boolean lastConflict =
      !"false".equals(System.getProperty("jacop.lcg.lastConflict"));
  private int decisionVar = -1; // the variable of the last activity decision
  private int conflictVar = -1; // the variable to branch on next, after a conflict
  private long backtrackConflicts;
  // semantic minimisation of learnt clauses, on unless -Djacop.lcg.semantic=false
  private final boolean semantic = !"false".equals(System.getProperty("jacop.lcg.semantic"));
  // semantic UIPs in conflict analysis, on unless -Djacop.lcg.semanticUip=false
  private final boolean semanticUip = !"false".equals(System.getProperty("jacop.lcg.semanticUip"));
  private final double[] activity;
  // the variables by activity; with Booleans first only the 0/1 ones, the others in wide, which
  // is branched on only once every 0/1 variable is fixed, as in CP-SAT's default search
  private final VarHeap heap = new VarHeap();
  private final VarHeap wide = new VarHeap();
  // Booleans first unless -Djacop.lcg.booleansFirst=false, which keeps every variable in heap
  private boolean split = !"false".equals(System.getProperty("jacop.lcg.booleansFirst"));
  // whether the runs of activity branching take turns with and without Booleans first
  private boolean booleansFirstTurns;
  // variables branched on only when every variable of heap and wide is fixed (defined variables)
  private final VarHeap lateHeap = new VarHeap();
  private final boolean[] late;
  // variables that no constraint uses: never branched on, at their least value in a solution
  private final boolean[] unused;
  private double activityInc = 1;
  // per integer variable: the conflict count at its last bump
  private long[] bumpedAt = new long[0];
  private long activityConflicts;
  // variables taken off the heap because they were fixed, with the decision level at the time
  private int[] popped = new int[16];
  private int[] poppedLevel = new int[16];
  private int numPopped;
  // the values of the last solution, preferred in decisions
  private int[] phase;
  // target phases of activity branching (CaDiCaL's target phases over integer values): the values
  // of the variables fixed at the conflict with the longest SAT trail since the last restart, taken
  // until the first solution gives its values. On under free search (-f) by default;
  // -Djacop.lcg.targetPhase=true|false turns it on or off in every mode.
  static final String TARGET_PHASE = System.getProperty("jacop.lcg.targetPhase");
  private int[] targetValue;
  private boolean[] targetSet;
  private int targetTrail;

  /** Statistics: snapshots of target phases (see {@code jacop.lcg.targetPhase}). */
  public long targetSnapshots;

  /** Statistics: activity decisions that took a target phase's value. */
  public long targetDecisions;

  // the model's search annotation: used in every run, or in every other run when free
  private SelectChoicePoint<? extends Var> annotation;
  private boolean freeSearch;
  // the annotation's index (see SelectChoicePoint#getIndex) after its decisions, with the decision
  // level each was taken at: its variables before the index are fixed while that level stands, so
  // the next decision starts there instead of scanning the fixed variables again. ANNOTATION_DONE
  // marks a level where it had fixed all its variables
  private int[] annotationIndex = new int[16];
  private int[] annotationLevel = new int[16];
  private int numAnnotationIndices;
  private static final int ANNOTATION_DONE = -1;
  private boolean annotationRun;
  // restarts under fixed search, see setFixedRestarts
  private FixedRestarts fixedRestarts = FixedRestarts.OFF;
  // restarts wait for the first solution
  private boolean restartsAfterSolution;

  private double lowerBoundShare;
  private long lowerBoundBudget;

  /** Statistics: runs of objective lower-bound search. */
  public long lowerBoundRuns;

  /** Statistics: lower-bound runs that raised the lower bound. */
  public long lowerBoundRaised;

  // objective shaving: a lower-bound run assumes the objective at most its lower bound plus this
  // step minus one; the step doubles when the run proves that impossible and halves when the run
  // runs out of conflicts. 0 turns shaving off: each run assumes the lower bound itself
  private long shaveStep;
  private boolean shaving;
  // the factor by which the lower-bound runs' share grows after a round without a better solution
  private double shaveGrowth = 1;

  // dichotomic bound search: the relative gap below which it gives way to branch and bound; 0 = off
  private double bisectGap;

  /** Statistics: probes of dichotomic bound search. */
  public long bisectProbes;

  /** Statistics: solutions found elsewhere whose values activity branching took up. */
  public long sharedPhases;

  /** Statistics: probes of dichotomic bound search that proved their half empty. */
  public long bisectRaised;

  /** Statistics: probes of dichotomic bound search that ran out of conflicts. */
  public long bisectLimits;

  // the variable minimised by branch and bound, or -1
  private int objective = -1;
  private int[] best;
  // after the core phase, branch and bound starts from the activity before it, unless
  // -Djacop.lcg.coreRestore=false
  private static final boolean CORE_RESTORE =
      !"false".equals(System.getProperty("jacop.lcg.coreRestore"));
  // the core phase gives its time to branch and bound when it has no solution of its own by this
  // share of
  // its time; 0 turns it off. With the restore it scored 21.3 against 14.7 and 24.3 against 12.7 on
  // the Challenge sample in two pairings, and 21.8 against 22.2 and 22.9 against 21.1 on the
  // OR-Tools set; either alone lost.
  private static final double CORE_NO_SOLUTION =
      Double.parseDouble(System.getProperty("jacop.lcg.coreNoSolution", "0.33"));
  private double coreShare;
  private long coreBudget;
  private long coreCallLimit;
  private double coreDelayShare;
  private long coreDelayBudget;
  private double coreProbeShare;
  // the core-guided phase runs only without a solution of the branch and bound before it
  private boolean coresWithoutSolutionOnly;
  private boolean coreMode; // solutions under assumptions end the search instead of bounding it
  // the run's time limit in milliseconds as given, 0 for none: the core-guided phase and the branch
  // and bound before it take their shares of its work (see WORK_PER_MS), not of the clock
  private long timeLimitMillis;
  // the work (CdclSolver#work) at which the core-guided schedule counts the run as over
  private long workEnd = Long.MAX_VALUE;
  private CoreSearch coreSearch;
  // the conflict limit set before minimize, which its phases keep
  private long conflictCap = Long.MAX_VALUE;
  // the objective value of the best solution found outside this solver, and the last one imported
  private IntSupplier sharedBound;
  private int importedBound = Integer.MAX_VALUE;

  // the best solution found elsewhere, whose values activity branching takes up with its bound
  private SharedSolution sharedPhase;
  // a shared bound at or below the objective's smallest value: no better solution exists
  private boolean sharedBoundUnreachable;

  private AdaptiveLns lns;
  private double lnsShare;
  private long lnsConflicts;
  private int[] lnsIds;

  /** Runs in large neighbourhoods. */
  public long lnsRuns;

  /** Runs in large neighbourhoods that improved the best solution. */
  public long lnsImproved;

  // clauses shared with solvers of the same model in other threads (null: none)
  private SharedClauses shared;
  private int sharedSource;
  // per variable its number in the shared clauses (-1: not shared), and the reverse
  private int[] sharedId;
  private int[] sharedLocal;
  // the root bounds last published
  private int[] publishedMin;
  private int[] publishedMax;
  private int sharedRead;
  private final List<int[]> exportBatch = new ArrayList<>();
  private final ArrayDeque<int[]> imports = new ArrayDeque<>();

  /** Learnt clauses given to the solvers of other threads. */
  public long clausesExported;

  /** Root bounds given to the solvers of other threads, as unit clauses. */
  public long boundsExported;

  /** Clauses of other threads' solvers added to this one. */
  public long clausesImported;

  /** Clauses of other threads' solvers left out: satisfied at the root or on missing literals. */
  public long clausesSkipped;

  /**
   * Builds the solver for the constraints imposed in a store. The store is propagated first; its
   * domains then are the root facts.
   *
   * @param store the store with its variables and constraints
   */
  public LcgSolver(Store store) {
    this.store = store;
    rootFailed = !store.consistency();
    if (rootFailed) {
      failedAtRoot = store.recentlyFailedConstraint;
    }
    this.baseLevel = store.level; // consistency may raise the level after impositions
    trail = new AtomicTrail(store);
    if (liftLiterals) {
      trail.setWeakerBounds(this::weakest);
    }
    // reasons of up to three literals stay as clauses; with the full fixpoint this scored 22.8
    // against 20.2 on the OR-Tools set and 18.9 against 19.1 on the Challenge sample, and proved
    // one more instance in each
    sat.setExternalReasonKeep(Integer.getInteger("jacop.lcg.reasonKeep", 3));
    sat.setExternalWork(() -> WORK_PER_CALL * store.numberConsistencyCalls);
    // learnt clauses keep longer in LCG, where a level holds many atoms: core up to LBD 3, middle
    // up to 8 scored 19.4 against 15.6 for 2 and 6 on the Challenge sample, in four pairings
    sat.setTierLimits(3, 8);
    // activity bumps every variable the conflict analysis met, not only the learnt clause's
    // (MiniSat): 600 s wide set, default mode 22 better / 9 worse, -f 19 / 14
    sat.setAnalysedNotify(!"learnt".equals(System.getProperty("jacop.lcg.bump", "seen")));
    // after the first 1,000 conflicts in focused mode, stable mode for good: restarts are far
    // rarer, and each costs the CP propagation back down. Under --lcg -f, on the 123 mznbench
    // instances with at least 2,000 conflicts in 60 s, 23 better and 13 worse, 59 against 54 runs
    // complete (three builds side by side); the other 126 instances barely reach stable mode
    sat.setStableForGood(
        Boolean.parseBoolean(System.getProperty("jacop.lcg.stableForGood", "true")));
    if (Boolean.getBoolean("jacop.lcg.check")) {
      checker = new ExplanationChecker(trail);
    }
    if (minimality > 0) {
      minimiser = new ExplanationMinimality(trail);
    }
    if (!"off".equals(linearMode)) {
      linear =
          new LinearConflict(
              trail,
              store,
              e -> e < cause.length && cause[e] != 0 ? sat.reasonKind(cause[e]) : 6,
              Boolean.parseBoolean(System.getProperty("jacop.lcg.linearKept", "true"))
                  ? this::linearOrigin
                  : null);
    }
    List<IntVar> all = new ArrayList<>();
    for (int i = 0; i < store.size(); i++) {
      if (store.vars[i] instanceof IntVar x) {
        all.add(x);
      }
    }
    for (Var v : store.variablesHashMap.values()) {
      if (v instanceof BooleanVar b) {
        all.add(b);
      }
    }
    int n = 0;
    for (IntVar x : all) {
      n = Math.max(n, trail.id(x) + 1);
    }
    vars = new IntVar[n];
    root = new IntDomain[n];
    ge = new LiteralMap[n];
    eq = new LiteralMap[n];
    linked = new LiteralMap[n];
    activity = new double[n];
    bumpedAt = new long[n];
    Arrays.fill(bumpedAt, -1);
    heap.grow(n, activity);
    wide.grow(n, activity);
    lateHeap.grow(n, activity);
    late = new boolean[n];
    unused = new boolean[n];
    for (IntVar x : all) {
      int i = trail.id(x);
      vars[i] = x;
      root[i] = x.dom().cloneLight();
      ge[i] = new LiteralMap(root[i].min(), root[i].max());
      eq[i] = new LiteralMap(root[i].min(), root[i].max());
      linked[i] = new LiteralMap(root[i].min(), root[i].max());
      if (!root[i].singleton()) {
        heapOf(i).insert(i);
        if (root[i].min() < 0 || root[i].max() > 1) {
          wideVariables++;
        } else {
          booleanVariables++;
        }
      }
    }
    sat.connect(this);
  }

  // --------------------------------------------------------------------------------- proof

  // the VeriPB proof and where its OPB model goes, or null
  private VeriPbProof proof;
  private OutputStream proofModel;
  private boolean proofStarted;

  // the trail of the propagation before the solver, whose changes the proof derives, or null
  private AtomicTrail rootTrail;
  // the constraint whose propagation failed at the root, and whether the proof derived the failure
  private Constraint failedAtRoot;
  private boolean rootRefuted;
  // a clause added before the search is false at the root: unit propagation over the model and the
  // root units refutes it
  private boolean clauseFailedAtRoot;
  // the trail and the domains the proof steps read: the solver's trail and its root domains, and
  // while the root propagation is logged, the root trail and the domains it has reached
  private AtomicTrail proofTrail;
  private IntDomain[] proofDomains;
  // the lines of the cardinality constraints of the proof model
  private Map<Constraint, OpbEncoder.CardinalityLines> proofCardinality = Map.of();
  // the equalities of the proof model, the first order line of each variable and the domains the
  // model states, for the core-guided phase's lower-bound line
  private Map<Constraint, OpbEncoder.EqualityLine> proofEqualities = Map.of();
  private Map<Constraint, List<OpbEncoder.EqualityLine>> proofAllEqualities = Map.of();
  // the position literals of the circuits of the proof model
  private Map<Constraint, OpbEncoder.CircuitLines> proofCircuits = Map.of();
  private Map<Constraint, OpbEncoder.TimetableLines> proofTimetables = Map.of();
  // the lines of the linear relations of the proof model, which the steps of the linear
  // relaxation combine, and the ids of those steps not deleted yet
  private Map<Constraint, long[]> proofLinearLines = Map.of();
  private final List<Long> proofLpSteps = new ArrayList<>();
  private long[] proofChains;
  private IntDomain[] proofModelDomains;
  // the auxiliary variables the proof defines, named y<number>
  private final BitSet proofAuxiliaries = new BitSet();
  // the clauses of addClause, for the OPB model
  private final List<IntVar[][]> proofClauses = new ArrayList<>();

  /**
   * The most terms the OPB model of a proof may have; the system property {@code
   * jacop.lcg.proofTerms} sets it.
   */
  private static final long PROOF_TERMS = Long.getLong("jacop.lcg.proofTerms", 20_000_000L);

  /**
   * Whether the proof names the constraint behind each explanation in a comment and writes each
   * conflict clause as a step, for debugging.
   */
  private static final boolean PROOF_TRACE = Boolean.getBoolean("jacop.lcg.proofTrace");

  /**
   * Writes a VeriPB proof of the search ({@link VeriPbProof}) and the OPB model it is checked
   * against ({@link OpbEncoder}): the model as the store holds it when the search starts, so its
   * root propagation and the translation to the store are not checked. Under a proof, minimisation
   * is branch and bound after the core-guided phase, whose cores, totalizers and lower bounds the
   * proof derives ({@link CoreProof}) without its at-most-one groups; lower-bound runs,
   * neighbourhood runs and a shared bound, which assume what the proof cannot state, are off. A
   * search stopped by a limit concludes the lower bound it proved. Set it right after the solver is
   * built; {@link #solve} and {@link #minimize} write the model when they start and the conclusion
   * when they end, and close both outputs.
   *
   * @param model where the OPB model goes
   * @param out where the proof goes
   */
  public void setProof(OutputStream model, OutputStream out) {
    proofModel = model;
    proof = new VeriPbProof(out, this::proofName);
    sat.setProof(proof);
  }

  /**
   * Derives the root propagation in the proof: the OPB model is stated over the domains a trail had
   * when it was attached to the store, before the propagation, and the proof derives each change
   * the trail recorded at the root as a unit. Changes without a reason, or by a constraint the
   * model cannot state, narrow the model's domains instead. The trail is detached here; attach it
   * after the model's constraints are imposed, before the store propagates them.
   *
   * @param rootTrail the trail of the root propagation
   */
  public void setRootTrail(AtomicTrail rootTrail) {
    rootTrail.detach();
    this.rootTrail = rootTrail;
  }

  /**
   * Writes the proof that the propagation of a store at the root fails: the OPB model over the
   * domains the root trail was attached with, the changes of the propagation as units, and the
   * failure of the constraint that failed.
   *
   * @param store the store, whose propagation has just failed
   * @param rootTrail the trail of the propagation
   * @param model where the OPB model goes
   * @param out where the proof goes
   */
  public static void proveRootFailure(
      Store store, AtomicTrail rootTrail, OutputStream model, OutputStream out) {
    Constraint failed = store.recentlyFailedConstraint;
    store.clearChanged();
    LcgSolver solver = new LcgSolver(store);
    solver.setRootTrail(rootTrail);
    solver.setProof(model, out);
    solver.rootFailed = true;
    solver.failedAtRoot = failed;
    solver.finishProof(CdclSolver.UNSAT, false);
  }

  /**
   * Returns the proof writer, for its statistics.
   *
   * @return the proof, or null
   */
  public VeriPbProof proof() {
    return proof;
  }

  // the OPB name of a solver variable
  private String proofName(int dimacsVar) {
    int i = litVar[dimacsVar];
    if (i < 0) {
      if (proofAuxiliaries.get(dimacsVar)) {
        return "y" + dimacsVar;
      }
      throw new IllegalStateException("an auxiliary variable in a proof");
    }
    return litKind[dimacsVar] == GE_KIND
        ? OpbEncoder.ge(i, litValue[dimacsVar])
        : OpbEncoder.eq(i, litValue[dimacsVar]);
  }

  /**
   * Returns every constraint of the store, for the OPB model: those of the variables' domains, the
   * watched-literal constraints, the value watchers and the constraints registered as unlisted
   * (such as a LinearBool of many terms, which watches values only once it propagates), which the
   * store's constraint list does not have.
   */
  private Set<Constraint> proofConstraints() {
    Set<Constraint> constraints = new LinkedHashSet<>(store.getConstraints());
    constraints.addAll(store.watchedLiteralConstraints());
    for (int i = 0; i < store.size(); i++) {
      constraints.addAll(store.valueWatchers(store.vars[i]));
    }
    constraints.addAll(store.unlistedConstraints());
    return constraints;
  }

  /** Writes the OPB model and starts the proof, once. */
  private void startProof() {
    if (proof == null || proofStarted) {
      return;
    }
    proofStarted = true;
    proofTrail = trail;
    proofDomains = root;
    Set<Constraint> constraints = proofConstraints();
    for (Constraint c : constraints) {
      if (c instanceof Circuit circuit) {
        // the proof derives cuts of the graph, not dominator reasons
        circuit.cutReasonsOnly();
      }
    }
    IntDomain[] domains = root;
    List<Integer> derived = new ArrayList<>();
    int axioms = 0;
    int localLate = 0;
    if (rootTrail != null) {
      localLate = rootTrail.lateVariables();
      domains = new IntDomain[vars.length];
      for (int i = 0; i < vars.length; i++) {
        domains[i] = vars[i] == null ? null : rootTrail.rootDomain(vars[i]);
      }
      Map<Constraint, Boolean> encodable = new IdentityHashMap<>();
      for (Constraint c : constraints) {
        encodable.put(c, true);
      }
      List<Integer> axiomEntries = new ArrayList<>();
      OpbEncoder probe = new OpbEncoder(vars, root, trail::id, PROOF_TERMS);
      for (int e = 0; e < rootTrail.size() && rootTrail.level(e) <= baseLevel; e++) {
        int i = trail.id(rootTrail.variable(e));
        Constraint c = rootTrail.reason(e);
        if (i >= vars.length || vars[i] == null) {
          continue;
        }
        if (c != null && encodable.computeIfAbsent(c, probe::encodes)) {
          constraints.add(c);
          derived.add(e);
        } else {
          axiomEntries.add(e);
        }
      }
      if (failedAtRoot != null && !encodable.computeIfAbsent(failedAtRoot, probe::encodes)) {
        failedAtRoot = null;
      } else if (failedAtRoot != null) {
        constraints.add(failedAtRoot);
      }
      // the changes the proof cannot derive narrow the domains of the model
      for (int e : axiomEntries) {
        int i = trail.id(rootTrail.variable(e));
        int v = rootTrail.value(e);
        domains[i] =
            switch (rootTrail.kind(e)) {
              case AtomicTrail.GE -> domains[i].intersect(v, domains[i].max());
              case AtomicTrail.LE -> domains[i].intersect(domains[i].min(), v);
              default -> domains[i].subtract(v);
            };
        axioms++;
      }
    }
    StringBuilder names = new StringBuilder();
    OpbEncoder model;
    String tooLarge = null;
    try {
      long values = 0;
      for (int i = 0; i < vars.length && rootTrail != null; i++) {
        values += vars[i] == null ? 0 : (long) domains[i].max() - domains[i].min() + 1;
      }
      // the order and value lines of a domain cost about 8 terms per value
      if (8 * values > PROOF_TERMS) {
        throw new OpbEncoder.TooLarge("its domains have " + values + " values");
      }
      model = proofModel(domains, constraints, names);
    } catch (OpbEncoder.TooLarge e) {
      if (rootTrail == null) {
        throw e;
      }
      // the domains the model states are too wide: it is stated after root propagation instead
      tooLarge = e.getMessage();
      rootTrail = null;
      failedAtRoot = null;
      domains = root;
      names.setLength(0);
      constraints = proofConstraints();
      model = proofModel(domains, constraints, names);
    }
    String objectiveLine = objective >= 0 ? model.objective(vars[objective]) : null;
    try {
      model.write(proofModel, objectiveLine, names);
      proofModel.close();
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    }
    proof.start(model.numConstraints());
    if (rootTrail != null) {
      proofRoot(domains, derived, axioms, localLate);
    } else if (tooLarge != null) {
      proof.comment("root propagation not derived: over the domains before it, " + tooLarge);
    }
    if (rootFailed) {
      // the store failed at the root, which the proof does not derive
      proof.comment(
          "the store failed at the root"
              + (failedAtRoot == null ? "" : ", in " + failedAtRoot.id())
              + (clauseFailedAtRoot ? ", in a clause" : ""));
    }
  }

  /** Encodes the constraints over the domains, and names the variables in comments. */
  private OpbEncoder proofModel(
      IntDomain[] domains, Set<Constraint> constraints, StringBuilder names) {
    OpbEncoder model = new OpbEncoder(vars, domains, trail::id, PROOF_TERMS);
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] != null && !domains[i].singleton()) {
        names.append("* x").append(i).append(" is ").append(vars[i].id()).append(' ');
        names.append(domains[i]).append('\n');
      }
    }
    model.variables();
    for (Constraint c : constraints) {
      model.constraint(c);
    }
    for (IntVar[][] clause : proofClauses) {
      model.clause(clause[0], clause[1]);
    }
    proofCardinality = model.cardinalityLines();
    proofEqualities = model.equalityLines();
    proofAllEqualities = model.allEqualityLines();
    proofCircuits = model.circuitLines();
    proofTimetables = model.timetableLines();
    proofLinearLines = model.linearLines();
    proofChains = model.chainLines();
    proofModelDomains = domains;
    if (!model.unsupported().isEmpty()) {
      throw new UnsupportedOperationException(
          "proof logging does not support " + String.join(", ", model.unsupported()));
    }
    return model;
  }

  /**
   * Derives the changes of the root propagation, in their order, each as a unit from the units
   * before it: unit propagation over the reason's encoding gives it, as it gives an explanation in
   * the search, with the steps of {@link #proofCardinality} and {@link #proofLinearBounds}.
   */
  private void proofRoot(IntDomain[] domains, List<Integer> derived, int axioms, int late) {
    proof.comment(
        derived.size()
            + " root changes derived, "
            + axioms
            + " taken into the model's domains, "
            + late
            + " variables stated after their first change");
    IntDomain[] reached = domains.clone();
    proofTrail = rootTrail;
    proofDomains = reached;
    EntryList none = new EntryList();
    for (int e : derived) {
      int i = trail.id(rootTrail.variable(e));
      int v = rootTrail.value(e);
      IntDomain d = reached[i];
      IntDomain next =
          switch (rootTrail.kind(e)) {
            case AtomicTrail.GE -> d.intersect(v, d.max());
            case AtomicTrail.LE -> d.intersect(d.min(), v);
            default -> d.subtract(v);
          };
      if (next.getSize() == d.getSize()) {
        continue;
      }
      Constraint c = rootTrail.reason(e);
      proofCardinality(c, none, 0, e);
      proofCircuit(c, none, 0, e);
      proofEnergy(c, none, 0, e);
      if (c instanceof Knapsack k) {
        // the row of the reason, which the root propagation did not ask for
        k.explain(rootTrail, e, new EntryList());
      }
      if (c instanceof LinearRelaxation r) {
        // the form of the reason and its certificate, which the root propagation did not ask for
        r.explain(rootTrail, e, new EntryList());
        proofLp(c, none, 0, e);
      }
      proofLinearBounds(c, none, 0, e);
      proof.lemma("rup 1 " + proofAtom(e, 0) + " >= 1 ;\n");
      reached[i] = next;
    }
    if (rootFailed && failedAtRoot != null) {
      proofCardinality(failedAtRoot, none, 0, -1);
      proofCircuit(failedAtRoot, none, 0, -1);
      proofEnergy(failedAtRoot, none, 0, -1);
      if (failedAtRoot instanceof Knapsack k) {
        k.explainFailure(rootTrail, new EntryList());
      }
      if (failedAtRoot instanceof LinearRelaxation r) {
        r.explainFailure(rootTrail, new EntryList());
        proofLp(failedAtRoot, none, 0, -1);
      }
      proofLinearBounds(failedAtRoot, none, 0, -1);
      rootRefuted = true;
    }
    proofTrail = trail;
    proofDomains = root;
  }

  /**
   * Logs the explanation of an atom the solver does not have, which a conflict clause replaces by
   * its reason: unit propagation over the model derives the atom from its reason, but not the
   * conflict clause from the atoms of the reasons, since a bound of an integer is several order
   * literals. The lemma {@code reason -> atom} is the step between.
   */
  private void proofLemma(int entry, EntryList reason, int from, int extra) {
    String atom = proofAtom(entry, 0);
    if ("1".equals(atom)) {
      return;
    }
    StringBuilder s = new StringBuilder("rup 1 ").append(atom);
    // several atoms of a reason can be one literal of the model, written once
    Set<String> written = new HashSet<>();
    written.add(atom);
    for (int k = from; k < reason.size(); k++) {
      String r = proofAtom(reason.get(k), reason.slack(k));
      String negated = r.startsWith("~") ? r.substring(1) : "~" + r;
      if (!"1".equals(r) && written.add(negated)) {
        s.append(" 1 ").append(negated);
      }
    }
    if (extra != 0) {
      String name = proofName(Math.abs(extra));
      s.append(" 1 ").append(extra > 0 ? "~" + name : name);
    }
    proof.lemma(s.append(" >= 1 ;\n"));
  }

  /**
   * Writes the steps that make a reason or a failure of a cardinality constraint (all different or
   * global cardinality) a rup step. Under its hypotheses, the atoms of the reason and the negated
   * atom, the flow network source to variables (each exactly 1), variables to their values left,
   * values to sink (the bounds of their counters) has no feasible flow, and a minimum cut A of it
   * is violated: the lower bounds into A exceed the capacities out of A. Without the source and the
   * sink in A, the variables S of A have fewer places than there are of them: the clauses "each of
   * S takes one of its values left" added to the upper lines of the values of A are false under the
   * hypotheses. With both, the values W outside A need more variables than can take them: the lower
   * lines of W added to the at-most-one lines of the variables outside A are false.
   *
   * @param c the constraint
   * @param atoms the atoms of the reason, from position from
   * @param from the first atom of the reason
   * @param entry the entry explained, or -1 for a failure
   */
  private void proofCardinality(Constraint c, EntryList atoms, int from, int entry) {
    OpbEncoder.CardinalityLines lines = proofCardinality.get(c);
    if (lines == null || !proofStarted) {
      return;
    }
    int[] variables = lines.variables;
    int[] values = lines.values;
    int n = variables.length;
    int m = values.length;
    IntDomain[] dom = new IntDomain[n];
    StringBuilder[] literals = new StringBuilder[n];
    hypotheses(lines.position, variables, atoms, from, entry, dom, literals);
    int[] counters = lines.counters;
    IntDomain[] count = new IntDomain[m];
    for (int k = 0; k < m; k++) {
      count[k] =
          counters[k] < 0
              ? new IntervalDomain(lines.low[k], lines.up[k])
              : proofDomains[counters[k]];
    }
    if (!lines.counterPosition.isEmpty()) {
      int[] freeCounter = new int[m];
      Arrays.fill(freeCounter, -1);
      lines.counterPosition.forEach((i, k) -> freeCounter[k] = i);
      IntDomain[] restricted = new IntDomain[m];
      StringBuilder[] counterLiterals = new StringBuilder[m];
      int[] ids = new int[m];
      for (int k = 0; k < m; k++) {
        ids[k] = freeCounter[k] < 0 ? counters[k] : freeCounter[k];
      }
      hypotheses(lines.counterPosition, ids, atoms, from, entry, restricted, counterLiterals);
      for (int k = 0; k < m; k++) {
        if (freeCounter[k] >= 0) {
          count[k] = restricted[k];
        }
      }
    }
    Map<Integer, Integer> valueIndex = new HashMap<>();
    for (int k = 0; k < m; k++) {
      valueIndex.put(values[k], k);
    }
    // the values not counted by an open constraint are free: any number of variables take them,
    // or as many as the rest counts, when one does: then all of them are one node
    Map<Integer, Integer> freeValues = new HashMap<>();
    int restNode = n + m + 2;
    for (int j = 0; j < n && !lines.closed; j++) {
      for (ValueEnumeration e = dom[j].valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        if (!valueIndex.containsKey(v)) {
          freeValues.putIfAbsent(v, lines.rest >= 0 ? restNode : n + m + 2 + freeValues.size());
        }
      }
    }
    IntDomain restDomain = null;
    if (lines.rest >= 0) {
      IntDomain[] restricted = new IntDomain[1];
      hypotheses(
          Map.of(lines.rest, 0),
          new int[] {lines.rest},
          atoms,
          from,
          entry,
          restricted,
          new StringBuilder[1]);
      restDomain = restricted[0];
      if (restDomain.isEmpty()) {
        return;
      }
    }
    int freeNodes = lines.rest >= 0 ? 1 : freeValues.size();
    // nodes: source 0, sink 1, variables, values, free values, the source and sink of lower bounds
    int source = n + m + 2 + freeNodes;
    int sink = source + 1;
    Flow flow = new Flow(sink + 1);
    for (int j = 0; j < n; j++) {
      flow.add(0, 2 + j, 1, 1);
      for (ValueEnumeration e = dom[j].valueEnumeration(); e.hasMoreElements(); ) {
        int v = e.nextElement();
        Integer k = valueIndex.get(v);
        Integer node = freeValues.get(v);
        if (k != null) {
          flow.add(2 + j, 2 + n + k, 0, 1);
        } else if (node != null) {
          flow.add(2 + j, node, 0, 1);
        }
      }
    }
    if (restDomain != null) {
      flow.add(restNode, 1, Math.max(0, restDomain.min()), Math.min(n, restDomain.max()));
    } else {
      for (int node : freeValues.values()) {
        flow.add(node, 1, 0, n);
      }
    }
    for (int k = 0; k < m; k++) {
      if (count[k].isEmpty()) {
        return;
      }
      int lo = Math.max(0, count[k].min());
      int hi = Math.min(n, count[k].max());
      if (lo > hi) {
        return;
      }
      flow.add(2 + n + k, 1, lo, hi);
    }
    flow.add(1, 0, 0, n + 1);
    boolean[] cut = flow.violatedCut(source, sink);
    if (cut == null) {
      return;
    }
    StringBuilder pol = new StringBuilder();
    int operands = 0;
    if (!cut[0] && !cut[1]) {
      for (int k = 0; k < m; k++) {
        if (cut[2 + n + k]) {
          String operand = lines.upper[k] > 0 ? Long.toString(lines.upper[k]) : null;
          for (int j = 0; operand == null && j < n; j++) {
            // a value only one variable can take: the axiom ~[x = v] >= 0 stands for its line
            if (cut[2 + j]
                && !proofDomains[variables[j]].singleton()
                && proofDomains[variables[j]].contains(values[k])) {
              operand = "~" + OpbEncoder.eq(variables[j], values[k]);
            }
          }
          if (operand != null) {
            pol.append(operands++ == 0 ? "" : " ").append(operand).append(operands > 1 ? " +" : "");
          }
        }
      }
      if (restDomain != null && cut[restNode]) {
        pol.append(operands++ == 0 ? "" : " ").append(lines.restUpper);
        pol.append(operands > 1 ? " +" : "");
      }
      for (int j = 0; j < n; j++) {
        int i = variables[j];
        if (!cut[2 + j] || proofDomains[i].singleton()) {
          continue;
        }
        StringBuilder takes = new StringBuilder("rup");
        for (ValueEnumeration e = dom[j].valueEnumeration(); e.hasMoreElements(); ) {
          takes.append(" 1 ").append(OpbEncoder.eq(i, e.nextElement()));
        }
        long id = proof.lemma(takes.append(literals[j]).append(" >= 1 ;\n"));
        pol.append(operands++ == 0 ? "" : " ").append(id).append(operands > 1 ? " +" : "");
      }
    } else if (cut[0] && cut[1]) {
      for (int k = 0; k < m; k++) {
        if (!cut[2 + n + k] && lines.lower[k] > 0) {
          pol.append(operands++ == 0 ? "" : " ").append(lines.lower[k]);
          pol.append(operands > 1 ? " +" : "");
        }
      }
      if (restDomain != null && !cut[restNode]) {
        pol.append(operands++ == 0 ? "" : " ").append(lines.restLower);
        pol.append(operands > 1 ? " +" : "");
      }
      for (int j = 0; j < n; j++) {
        if (!cut[2 + j] && lines.atMostOne[j] > 0) {
          pol.append(operands++ == 0 ? "" : " ").append(lines.atMostOne[j]);
          pol.append(operands > 1 ? " +" : "");
        }
      }
    }
    if (operands >= 2) {
      proof.pol(pol);
    }
  }

  /**
   * A flow network with lower bounds on its arcs, for the cuts of {@link #proofCardinality}: an arc
   * u to v with bounds l..h becomes one of capacity h - l, with l moved to arcs from the source of
   * the lower bounds to v and from u to their sink.
   */
  private static final class Flow {
    private final int[] head;
    private int[] to = new int[64];
    private int[] capacity = new int[64];
    private int[] next = new int[64];
    private int arcs;
    private final int[] excess;

    Flow(int nodes) {
      head = new int[nodes];
      Arrays.fill(head, -1);
      excess = new int[nodes];
    }

    void add(int u, int v, int lower, int upper) {
      arc(u, v, upper - lower);
      excess[v] += lower;
      excess[u] -= lower;
    }

    private void arc(int u, int v, int c) {
      if (arcs + 2 > to.length) {
        to = Arrays.copyOf(to, 2 * to.length);
        capacity = Arrays.copyOf(capacity, 2 * capacity.length);
        next = Arrays.copyOf(next, 2 * next.length);
      }
      // the arc and its reverse, at a and a + 1 (a ^ 1 finds one from the other)
      int a = arcs;
      to[a] = v;
      capacity[a] = c;
      next[a] = head[u];
      head[u] = a;
      to[a + 1] = u;
      capacity[a + 1] = 0;
      next[a + 1] = head[v];
      head[v] = a + 1;
      arcs += 2;
    }

    /**
     * Returns the nodes of a violated cut, reachable from the source of the lower bounds once the
     * flow is maximal, or null when a feasible flow exists.
     */
    boolean[] violatedCut(int source, int sink) {
      int demand = 0;
      for (int v = 0; v < source; v++) {
        if (excess[v] > 0) {
          arc(source, v, excess[v]);
          demand += excess[v];
        } else if (excess[v] < 0) {
          arc(v, sink, -excess[v]);
        }
      }
      // Dinic: a blocking flow along the shortest paths of the residual graph in each phase
      int nodes = head.length;
      int[] distance = new int[nodes];
      int[] current = new int[nodes];
      int[] queue = new int[nodes];
      int total = 0;
      while (levels(source, sink, distance, queue)) {
        System.arraycopy(head, 0, current, 0, nodes);
        for (int pushed;
            (pushed = block(source, sink, Integer.MAX_VALUE, distance, current)) > 0; ) {
          total += pushed;
        }
      }
      if (total == demand) {
        return null;
      }
      // the nodes the last breadth-first search reached: those reachable in the residual graph
      boolean[] seen = new boolean[source];
      for (int v = 0; v < source; v++) {
        seen[v] = distance[v] >= 0;
      }
      return seen;
    }

    // the distances from the source in the residual graph; tells whether the sink is reached
    private boolean levels(int source, int sink, int[] distance, int[] queue) {
      Arrays.fill(distance, -1);
      distance[source] = 0;
      int first = 0;
      int last = 0;
      queue[last++] = source;
      while (first < last) {
        int u = queue[first++];
        for (int a = head[u]; a >= 0; a = next[a]) {
          if (capacity[a] > 0 && distance[to[a]] < 0) {
            distance[to[a]] = distance[u] + 1;
            queue[last++] = to[a];
          }
        }
      }
      return distance[sink] >= 0;
    }

    // a path of increasing distances, each arc tried once per phase from current[u]
    private int block(int u, int sink, int limit, int[] distance, int[] current) {
      if (u == sink) {
        return limit;
      }
      for (; current[u] >= 0; current[u] = next[current[u]]) {
        int a = current[u];
        int v = to[a];
        if (capacity[a] > 0 && distance[v] == distance[u] + 1) {
          int pushed = block(v, sink, Math.min(limit, capacity[a]), distance, current);
          if (pushed > 0) {
            capacity[a] -= pushed;
            capacity[a ^ 1] += pushed;
            return pushed;
          }
        }
      }
      return 0;
    }
  }

  /**
   * Writes the step that makes an energy reason of a time-indexed cumulative a rup step. Under the
   * hypotheses of the clause each task starts in [lo, hi]; a window [a, b) where the tasks need
   * more energy than the limit gives is overloaded by the sum of the load lines at its time points,
   * with each needing task's use times the definitions of its covering literals, which turn its
   * load into order literals of its start, and times the order lines that pair the literals the
   * hypotheses leave free, so that only the energy the task needs at least is left. Unit
   * propagation on the sum finds the overload. A reason that a time point overloaded by the
   * compulsory parts gives is a rup step as it is.
   *
   * @param c the constraint
   * @param atoms the atoms of the reason, from position from
   * @param from the first atom of the reason
   * @param entry the entry explained, or -1 for a failure
   */
  private void proofEnergy(Constraint c, EntryList atoms, int from, int entry) {
    OpbEncoder.TimetableLines lines = proofTimetables.get(c);
    if (lines == null || !proofStarted) {
      return;
    }
    int[] starts = lines.starts();
    int n = starts.length;
    int[] variables = Arrays.copyOf(starts, n + 1);
    variables[n] = lines.limit();
    Map<Integer, Integer> position = new HashMap<>();
    for (int j = 0; j <= n; j++) {
      if (position.put(variables[j], j) != null) {
        return; // a variable in two places
      }
    }
    IntDomain[] dom = new IntDomain[n + 1];
    StringBuilder[] literals = new StringBuilder[n + 1];
    hypotheses(position, variables, atoms, from, entry, dom, literals);
    for (IntDomain x : dom) {
      if (x.isEmpty()) {
        return; // unit propagation empties the domain
      }
    }
    long cap = dom[n].max();
    int[] d = lines.durations();
    int[] r = lines.uses();
    int[] lo = new int[n];
    int[] hi = new int[n];
    TreeMap<Long, Long> profile = new TreeMap<>();
    List<Long> left = new ArrayList<>();
    List<Long> right = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      lo[i] = dom[i].min();
      hi[i] = dom[i].max();
      if (d[i] > 0 && r[i] > 0) {
        if (hi[i] < (long) lo[i] + d[i]) {
          profile.merge((long) hi[i], (long) r[i], Long::sum);
          profile.merge((long) lo[i] + d[i], (long) -r[i], Long::sum);
        }
        left.add((long) lo[i]);
        left.add((long) hi[i]);
        right.add((long) lo[i] + d[i]);
        right.add((long) hi[i] + d[i]);
      }
    }
    long load = 0;
    for (long change : profile.values()) {
      load += change;
      if (load > cap) {
        return; // a time point the compulsory parts overload
      }
    }
    // the narrowest overloaded window
    long a = 0;
    long b = 0;
    for (long x : new TreeSet<>(left)) {
      for (long y : new TreeSet<>(right)) {
        if (y <= x || b > a && y - x >= b - a) {
          continue;
        }
        long energy = 0;
        for (int i = 0; i < n; i++) {
          if (d[i] > 0 && r[i] > 0) {
            energy +=
                (long) r[i] * Math.min(overlap(lo[i], d[i], x, y), overlap(hi[i], d[i], x, y));
          }
        }
        if (energy > cap * (y - x)) {
          a = x;
          b = y;
        }
      }
    }
    if (b <= a) {
      return;
    }
    StringBuilder pol = new StringBuilder();
    int operands = 0;
    for (long t = a; t < b; t++) {
      Long id = lines.load().get(t);
      if (id != null) {
        pol.append(operands++ == 0 ? "" : " ").append(id).append(operands > 1 ? " +" : "");
      }
    }
    for (int i = 0; i < n; i++) {
      if (d[i] <= 0
          || r[i] <= 0
          || Math.min(overlap(lo[i], d[i], a, b), overlap(hi[i], d[i], a, b)) <= 0) {
        continue;
      }
      Map<Long, Long> covers = lines.covers().get(i);
      for (long t = a; t < b; t++) {
        Long id = covers.get(t);
        if (id != null) {
          pol.append(operands++ == 0 ? "" : " ").append(id);
          pol.append(r[i] == 1 ? "" : " " + r[i] + " *").append(operands > 1 ? " +" : "");
        }
      }
      // the load is r times [s >= u] over u in [a - d + 1, b - d] less those over [a + 1, b]; the
      // first ones lie before the second ones, and each free second one cancels against a free
      // first one by the order lines between them
      List<Long> first = new ArrayList<>();
      List<Long> second = new ArrayList<>();
      for (long u = Math.max(a - d[i] + 1, lo[i] + 1L); u <= Math.min(b - d[i], hi[i]); u++) {
        if (u < a + 1) {
          first.add(u);
        }
      }
      for (long u = Math.max(a + 1, lo[i] + 1L); u <= Math.min(b, hi[i]); u++) {
        if (u > b - d[i]) {
          second.add(u);
        }
      }
      int pairs = Math.min(first.size(), second.size());
      Map<Long, Long> multiplicity = new TreeMap<>();
      for (int k = 0; k < pairs; k++) {
        for (long v = first.get(k); v < second.get(k); v++) {
          multiplicity.merge(v, 1L, Long::sum);
        }
      }
      for (var e : multiplicity.entrySet()) {
        long id = proofChainLine(starts[i], (int) (long) e.getKey());
        if (id == 0) {
          return;
        }
        long k = r[i] * e.getValue();
        pol.append(operands++ == 0 ? "" : " ").append(id);
        pol.append(k == 1 ? "" : " " + k + " *").append(operands > 1 ? " +" : "");
      }
    }
    if (operands >= 2) {
      proof.pol(pol);
    }
  }

  /**
   * Writes the step that makes a reason of the linear relaxation a rup step. A relaxation built for
   * a proof ({@link LinearRelaxation#ofModel}) keeps, for each form it propagates, the rows it
   * combines and their integer multipliers ({@link LinearRelaxation.Certificate}): the form is the
   * {@code pol} sum of the lines of those rows' constraints times the multipliers, the line {@code
   * sum <= c} for a positive one and {@code sum >= c} for a negative one. Unit propagation on the
   * sum derives the reason, as on the line of a linear constraint, with the steps of {@link
   * #proofLinearBounds} past removed values. A line of a constraint folds the variables fixed at
   * the root into its constant, which the root units give back. The sums are deleted at the next
   * restart, after the clauses of their conflicts.
   *
   * @param c the constraint
   * @param atoms the atoms of the reason, from position from
   * @param from the first atom of the reason
   * @param entry the entry explained, or -1 for a failure
   */
  private void proofLp(Constraint c, EntryList atoms, int from, int entry) {
    if (!(c instanceof LinearRelaxation r) || !proofStarted || !r.certifies()) {
      return;
    }
    LinearRelaxation.Certificate certificate = r.certificate();
    if (certificate == null) {
      proof.comment("a reason of the linear relaxation without a certificate");
      return;
    }
    Constraint[] rows = certificate.rows();
    long[] multipliers = certificate.multipliers();
    StringBuilder pol = new StringBuilder();
    for (int k = 0; k < rows.length; k++) {
      long[] ids = proofLinearLines.get(rows[k]);
      long id = ids == null ? 0 : ids[multipliers[k] > 0 ? 1 : 0];
      if (id == 0) {
        proof.comment("a row of the linear relaxation without its line: " + rows[k].id());
        return;
      }
      long a = Math.abs(multipliers[k]);
      pol.append(k == 0 ? "" : " ").append(id).append(a == 1 ? "" : " " + a + " *");
      pol.append(k == 0 ? "" : " +");
    }
    if (rows.length > 1) {
      // one row is its line already, whatever its multiplier
      proofLpSteps.add(proof.pol(pol));
    }
    proofLinearBounds(certificate.form(), atoms, from, entry);
  }

  // deletes the sums of the linear relaxation, whose clauses are all written at a restart
  private void deleteLpSteps() {
    if (proof == null || proofLpSteps.isEmpty()) {
      return;
    }
    long[] ids = new long[proofLpSteps.size()];
    for (int k = 0; k < ids.length; k++) {
      ids[k] = proofLpSteps.get(k);
    }
    proofLpSteps.clear();
    proof.deleteSteps(ids);
  }

  // the time a task started at s with duration d spends in [a, b)
  private static long overlap(long s, long d, long a, long b) {
    return Math.max(0, Math.min(s + d, b) - Math.max(s, a));
  }

  /**
   * Writes the steps that make a cut reason of a circuit a rup step. Under the hypotheses of the
   * clause, the arcs left are those of the domains; a strongly connected component that no arc
   * leaves (a sink of the graph of components) is a set C of nodes whose circuit stays in C. When C
   * does not hold node 0, no node of C has a position after node 0: the clause "hypotheses imply
   * node i of C is not at position k" is a rup step for k from n - 1 down to 1, since the arcs from
   * i lead into C, whose nodes are not at k + 1. When C holds node 0, the nodes outside it have no
   * arc into them from C and, by the same steps backwards from node 0, no position before it. Unit
   * propagation then finds a node without a position.
   *
   * @param c the constraint
   * @param atoms the atoms of the reason, from position from
   * @param from the first atom of the reason
   * @param entry the entry explained, or -1 for a failure
   */
  private void proofCircuit(Constraint c, EntryList atoms, int from, int entry) {
    OpbEncoder.CircuitLines lines = proofCircuits.get(c);
    if (lines == null || !proofStarted) {
      return;
    }
    int[] variables = lines.variables();
    int n = variables.length;
    Map<Integer, Integer> position = new HashMap<>();
    for (int j = 0; j < n; j++) {
      position.put(variables[j], j);
    }
    IntDomain[] dom = new IntDomain[n];
    StringBuilder[] literals = new StringBuilder[n];
    hypotheses(position, variables, atoms, from, entry, dom, literals);
    int[][] successors = new int[n][];
    for (int i = 0; i < n; i++) {
      int[] s = new int[n];
      int count = 0;
      for (ValueEnumeration e = dom[i].valueEnumeration(); e.hasMoreElements(); ) {
        long j = (long) e.nextElement() - lines.offset();
        if (j >= 0 && j < n && j != i) {
          s[count++] = (int) j;
        }
      }
      if (count == 0) {
        return; // a node without a successor: unit propagation finds it
      }
      successors[i] = Arrays.copyOf(s, count);
    }
    int[] component = components(successors);
    if (component == null) {
      return; // one strongly connected component: not a cut reason
    }
    // a component that no arc leaves (forwards) or enters (backwards) without node 0, the smallest
    int count = 0;
    for (int k : component) {
      count = Math.max(count, k + 1);
    }
    boolean[] leaves = new boolean[count];
    boolean[] entered = new boolean[count];
    int[] size = new int[count];
    for (int v = 0; v < n; v++) {
      size[component[v]]++;
      for (int w : successors[v]) {
        if (component[w] != component[v]) {
          leaves[component[v]] = true;
          entered[component[w]] = true;
        }
      }
    }
    int localBest = -1;
    boolean forward = true;
    for (int k = 0; k < count; k++) {
      if (k != component[0]
          && (!leaves[k] || !entered[k])
          && (localBest < 0 || size[k] < size[localBest])) {
        localBest = k;
        forward = !leaves[k];
      }
    }
    // the hypotheses used: on the arcs out of the set forwards, into it backwards
    StringBuilder clause = new StringBuilder();
    for (int i = 0; i < n; i++) {
      if ((component[i] == localBest) == forward) {
        clause.append(literals[i]);
      }
    }
    String[][] p = forward ? lines.forward() : lines.reverse();
    for (int k = n - 1; k >= 1; k--) {
      for (int i = 1; i < n; i++) {
        if (component[i] == localBest && !"0".equals(p[i][k])) {
          proof.lemma("rup" + clause + " 1 " + PbModel.not(p[i][k]) + " >= 1 ;\n");
        }
      }
    }
  }

  /** The strongly connected component of each node of a graph, or null for one component. */
  private static int[] components(int[][] successors) {
    int n = successors.length;
    // Kosaraju: the finishing order of a depth-first search, then components on the reverse graph
    int[] order = new int[n];
    int finished = 0;
    boolean[] seen = new boolean[n];
    int[] stack = new int[n];
    int[] next = new int[n];
    for (int s = 0; s < n; s++) {
      if (seen[s]) {
        continue;
      }
      int sp = 0;
      stack[sp++] = s;
      seen[s] = true;
      next[s] = 0;
      while (sp > 0) {
        int v = stack[sp - 1];
        if (next[v] < successors[v].length) {
          int w = successors[v][next[v]++];
          if (!seen[w]) {
            seen[w] = true;
            next[w] = 0;
            stack[sp++] = w;
          }
        } else {
          order[finished++] = v;
          sp--;
        }
      }
    }
    int[] inCount = new int[n];
    for (int[] s : successors) {
      for (int w : s) {
        inCount[w]++;
      }
    }
    int[][] predecessors = new int[n][];
    for (int v = 0; v < n; v++) {
      predecessors[v] = new int[inCount[v]];
    }
    int[] fill = new int[n];
    for (int v = 0; v < n; v++) {
      for (int w : successors[v]) {
        predecessors[w][fill[w]++] = v;
      }
    }
    int[] component = new int[n];
    Arrays.fill(component, -1);
    int components = 0;
    for (int k = n - 1; k >= 0; k--) {
      int s = order[k];
      if (component[s] >= 0) {
        continue;
      }
      int sp = 0;
      stack[sp++] = s;
      component[s] = components;
      while (sp > 0) {
        int v = stack[--sp];
        for (int u : predecessors[v]) {
          if (component[u] < 0) {
            component[u] = components;
            stack[sp++] = u;
          }
        }
      }
      components++;
    }
    return components == 1 ? null : component;
  }

  /**
   * Restricts the root domains of some variables by the hypotheses of a clause: the atoms of a
   * reason and the negated atom it explains.
   *
   * @param position the position of each trail index among the variables
   * @param variables the trail indexes of the variables
   * @param atoms the atoms of the reason, from position from
   * @param from the first atom of the reason
   * @param entry the entry explained, or -1 for a failure
   * @param dom filled with the domain of each variable under the hypotheses
   * @param literals filled with the clause literals of each variable, each preceded by " 1 "
   * @return whether a hypothesis removes a value inside the bounds
   */
  private boolean hypotheses(
      Map<Integer, Integer> position,
      int[] variables,
      EntryList atoms,
      int from,
      int entry,
      IntDomain[] dom,
      StringBuilder[] literals) {
    for (int j = 0; j < variables.length; j++) {
      dom[j] = proofDomains[variables[j]];
      literals[j] = new StringBuilder();
    }
    boolean hole = false;
    for (int j = 0; j < variables.length && proofTrail != trail; j++) {
      // while the root propagation is logged, the values it removed are holes too
      hole |= dom[j].getSize() < (long) dom[j].max() - dom[j].min() + 1;
    }
    for (int k = from; k < atoms.size(); k++) {
      int e = atoms.get(k);
      Integer j = position.get(trail.id(proofTrail.variable(e)));
      if (j != null) {
        String atom = proofAtom(e, atoms.slack(k));
        int v = proofTrail.value(e);
        dom[j] =
            switch (proofTrail.kind(e)) {
              case AtomicTrail.GE -> dom[j].intersect(v - atoms.slack(k), dom[j].max());
              case AtomicTrail.LE -> dom[j].intersect(dom[j].min(), v + atoms.slack(k));
              default -> dom[j].subtract(v);
            };
        hole |= proofTrail.kind(e) == AtomicTrail.NE;
        if (!"1".equals(atom)) {
          literals[j].append(" 1 ").append(atom.startsWith("~") ? atom.substring(1) : "~" + atom);
        }
      }
    }
    if (entry >= 0) {
      Integer j = position.get(trail.id(proofTrail.variable(entry)));
      if (j != null) {
        int v = proofTrail.value(entry);
        dom[j] =
            switch (proofTrail.kind(entry)) {
              case AtomicTrail.GE -> dom[j].intersect(dom[j].min(), v - 1);
              case AtomicTrail.LE -> dom[j].intersect(v + 1, dom[j].max());
              default -> dom[j].intersect(v, v);
            };
        literals[j].append(" 1 ").append(proofAtom(entry, 0));
      }
    }
    return hole;
  }

  /**
   * Writes the bounds that a linear constraint implies under the hypotheses of a clause, when a
   * hypothesis removes a value inside the bounds. Unit propagation over the order literals of a
   * linear line derives a bound, but not the bound past a removed value: the clause "hypotheses
   * imply x &gt;= v" is a rup step, and the one with v moved past the removed values after it.
   *
   * @param c the constraint
   * @param atoms the atoms of the reason, from position from
   * @param from the first atom of the reason
   * @param entry the entry explained, or -1 for a failure
   */
  private void proofLinearBounds(Constraint c, EntryList atoms, int from, int entry) {
    if (proofStarted && c instanceof Binpacking b) {
      proofBinLoads(b, atoms, from, entry);
    }
    LinearForm f = proofStarted ? OpbEncoder.form(c) : null;
    if (f == null && proofStarted && c instanceof Knapsack k) {
      f = proofKnapsackRow(k);
    }
    proofLinearBounds(f, atoms, from, entry);
  }

  /**
   * Writes the row of a knapsack reason, b times the profit equality less a times the weight
   * equality ({@link Knapsack#explanationRatio}), by pol steps over the model's lines, and returns
   * it; null when the reason is not one of a row.
   */
  private LinearForm proofKnapsackRow(Knapsack k) {
    long[] ratio = k.explanationRatio();
    List<OpbEncoder.EqualityLine> lines = proofAllEqualities.get(k);
    if (ratio == null || lines == null || lines.size() != 2) {
      return null;
    }
    long a = ratio[0];
    long b = ratio[1];
    // lines: sum(w q) - capacity >= 0 (id), <= 0 (id + 1); the same for the profit
    long weight = lines.get(0).id();
    long profit = lines.get(1).id();
    if (a == 0) {
      return lines.get(1).form();
    }
    if (b == 0) {
      return lines.get(0).form();
    }
    // b * profit - a * weight >= 0 and <= 0
    proof.pol(profit + " " + b + " * " + (weight + 1) + " " + a + " * +");
    proof.pol((profit + 1) + " " + b + " * " + weight + " " + a + " * +");
    LinearForm[] rows = k.rows();
    int n = rows[0].vars().length;
    IntVar[] localVars = new IntVar[n + 1];
    long[] w = new long[n + 1];
    for (int i = 0; i < n - 1; i++) {
      localVars[i] = rows[0].vars()[i];
      w[i] = b * rows[1].weights()[i] - a * rows[0].weights()[i];
    }
    localVars[n - 1] = rows[0].vars()[n - 1];
    w[n - 1] = a;
    localVars[n] = rows[1].vars()[n - 1];
    w[n] = -b;
    return new LinearForm(localVars, w, 0, LinearForm.EQ);
  }

  private void proofLinearBounds(LinearForm f, EntryList atoms, int from, int entry) {
    if (f == null || f.relation() == LinearForm.NE) {
      return;
    }
    int n = f.vars().length;
    int[] variables = new int[n];
    Map<Integer, Integer> position = new HashMap<>();
    for (int j = 0; j < n; j++) {
      variables[j] = trail.id(f.vars()[j]);
      if (position.put(variables[j], j) != null) {
        return;
      }
    }
    IntDomain[] dom = new IntDomain[n];
    StringBuilder[] literals = new StringBuilder[n];
    if (!hypotheses(position, variables, atoms, from, entry, dom, literals)) {
      return;
    }
    StringBuilder clause = new StringBuilder();
    for (StringBuilder l : literals) {
      clause.append(l);
    }
    long[] w = f.weights();
    int changed = 1;
    for (int round = 0; changed > 0 && round < 4 * n; round++) {
      changed = 0;
      for (int k = 0; k < n; k++) {
        if (w[k] == 0) {
          continue;
        }
        // the bounds of w[k] * x[k] that the other terms leave, for sum <= c and sum >= c
        long smallest = 0;
        long largest = 0;
        for (int j = 0; j < n; j++) {
          if (j != k) {
            smallest += Math.min(w[j] * dom[j].min(), w[j] * dom[j].max());
            largest += Math.max(w[j] * dom[j].min(), w[j] * dom[j].max());
          }
        }
        long lo = Long.MIN_VALUE;
        long hi = Long.MAX_VALUE;
        if (f.relation() != LinearForm.GE) {
          // w x <= c - smallest
          long r = f.c() - smallest;
          if (w[k] > 0) {
            hi = Math.floorDiv(r, w[k]);
          } else {
            lo = -Math.floorDiv(r, -w[k]);
          }
        }
        if (f.relation() != LinearForm.LE) {
          // w x >= c - largest
          long r = f.c() - largest;
          if (w[k] > 0) {
            lo = Math.max(lo, -Math.floorDiv(-r, w[k]));
          } else {
            hi = Math.min(hi, Math.floorDiv(-r, -w[k]));
          }
        }
        IntDomain d = dom[k];
        if (lo > d.min()) {
          changed += proofBound(variables[k], clause, (int) Math.min(lo, d.max() + 1L), true);
        }
        if (hi < d.max()) {
          changed += proofBound(variables[k], clause, (int) Math.max(hi, d.min() - 1L), false);
        }
        dom[k] = d.intersect((int) Math.max(lo, d.min()), (int) Math.min(hi, d.max()));
        if (dom[k].isEmpty()) {
          return;
        }
        if (dom[k].min() > Math.max(lo, d.min())) {
          proofBound(variables[k], clause, dom[k].min(), true);
        }
        if (dom[k].max() < Math.min(hi, d.max())) {
          proofBound(variables[k], clause, dom[k].max(), false);
        }
      }
    }
  }

  /**
   * Writes the bounds of the loads of a bin packing under the hypotheses of a clause, when a load
   * has a removed value inside its bounds: the load of a bin is at least the weight of the items
   * packed in it and at most that of the items that can be in it (its line sum w_i [x_i = b] - load
   * = 0, {@link Binpacking#encode}), and the loads sum to the weight of all items. A rup step
   * derives a bound from these lines when its negation contradicts them, but not one past a removed
   * value, nor the bounds that follow from it: each bound of the fixpoint is a lemma under the
   * clause, the one at the weight and then the one past the removed values (steelmillslab).
   */
  private void proofBinLoads(Binpacking b, EntryList atoms, int from, int entry) {
    IntVar[] bins = b.binVariables();
    int[] weights = b.itemWeights();
    IntVar[] loads = b.loads();
    List<Integer> ids = new ArrayList<>();
    Map<Integer, Integer> position = new HashMap<>();
    int[] itemPosition = new int[bins.length];
    for (int k = 0; k < bins.length; k++) {
      int i = trail.id(bins[k]);
      Integer j = position.get(i);
      if (j == null) {
        j = ids.size();
        position.put(i, j);
        ids.add(i);
      }
      itemPosition[k] = j;
    }
    int[] loadPosition = new int[loads.length];
    for (int l = 0; l < loads.length; l++) {
      int i = trail.id(loads[l]);
      if (position.containsKey(i)) {
        return; // a load that is also a bin
      }
      loadPosition[l] = ids.size();
      position.put(i, ids.size());
      ids.add(i);
    }
    int[] variables = ids.stream().mapToInt(Integer::intValue).toArray();
    IntDomain[] dom = new IntDomain[variables.length];
    StringBuilder[] literals = new StringBuilder[variables.length];
    hypotheses(position, variables, atoms, from, entry, dom, literals);
    // only a load with a removed value inside its bounds, at the root or under the hypotheses,
    // stops unit propagation
    boolean hole = false;
    for (int p : loadPosition) {
      hole |= !dom[p].isEmpty() && dom[p].getSize() < (long) dom[p].max() - dom[p].min() + 1;
    }
    if (!hole) {
      return;
    }
    StringBuilder clause = new StringBuilder();
    for (StringBuilder l : literals) {
      clause.append(l);
    }
    long all = 0;
    for (int w : weights) {
      all += w;
    }
    // the rows of the bins and the sum of the loads to a fixpoint, as unit propagation over the
    // lines with the lemmas goes
    boolean changed = true;
    for (int round = 0; changed && round < 4 * (loads.length + bins.length); round++) {
      changed = false;
      for (int l = 0; l < loads.length; l++) {
        int bin = b.minBin() + l;
        long packed = 0;
        long possible = 0;
        for (int k = 0; k < bins.length; k++) {
          IntDomain d = dom[itemPosition[k]];
          if (d.contains(bin)) {
            possible += weights[k];
            if (d.singleton()) {
              packed += weights[k];
            }
          }
        }
        int p = loadPosition[l];
        IntDomain before = dom[p];
        if (!proofTighten(variables[p], dom, p, packed, possible, clause)) {
          return;
        }
        changed |= dom[p] != before;
        // the items that overload the bin or that it needs
        for (int k = 0; k < bins.length; k++) {
          int q = itemPosition[k];
          IntDomain d = dom[q];
          if (!d.contains(bin) || d.singleton()) {
            continue;
          }
          if (packed + weights[k] > dom[p].max()) {
            dom[q] = d.subtract(bin);
            changed = true;
          } else if (possible - weights[k] < dom[p].min()) {
            dom[q] = d.intersect(bin, bin);
            changed = true;
          }
          if (dom[q].isEmpty()) {
            return;
          }
        }
      }
      long sumMin = 0;
      long sumMax = 0;
      for (int l = 0; l < loads.length; l++) {
        sumMin += dom[loadPosition[l]].min();
        sumMax += dom[loadPosition[l]].max();
      }
      for (int l = 0; l < loads.length; l++) {
        int p = loadPosition[l];
        IntDomain before = dom[p];
        long lo = all - (sumMax - before.max());
        long hi = all - (sumMin - before.min());
        if (!proofTighten(variables[p], dom, p, lo, hi, clause)) {
          return;
        }
        if (dom[p] != before) {
          changed = true;
          sumMin += dom[p].min() - before.min();
          sumMax += dom[p].max() - before.max();
        }
      }
    }
  }

  /**
   * Restricts dom[p], the domain of variable i, to lo..hi, writing the bound lemmas under the
   * clause: each new bound, then the one past the removed values next to it. Returns false when the
   * domain is empty.
   */
  private boolean proofTighten(
      int i, IntDomain[] dom, int p, long lo, long hi, CharSequence clause) {
    IntDomain d = dom[p];
    if (lo > d.min()) {
      if (lo > d.max()) {
        return false;
      }
      proofBound(i, clause, (int) lo, true);
      if (!d.contains((int) lo)) {
        proofBound(i, clause, (int) Math.min(nextValue(d, (int) lo), hi + 1), true);
      }
    }
    if (hi < d.max()) {
      if (hi < d.min()) {
        return false;
      }
      proofBound(i, clause, (int) hi, false);
      if (!d.contains((int) hi)) {
        proofBound(i, clause, (int) Math.max(previousValue(d, (int) hi), lo - 1), false);
      }
    }
    if (lo > d.min() || hi < d.max()) {
      dom[p] = d.intersect((int) Math.max(lo, d.min()), (int) Math.min(hi, d.max()));
    }
    return !dom[p].isEmpty();
  }

  // the smallest value of d above v, or d.max() + 1
  private static int nextValue(IntDomain d, int v) {
    return v >= d.max() ? d.max() + 1 : d.nextValue(v);
  }

  // the largest value of d below v, or d.min() - 1
  private static int previousValue(IntDomain d, int v) {
    return v <= d.min() ? d.min() - 1 : d.previousValue(v);
  }

  // writes "clause or x >= v" (or x <= v); returns 1, or 0 when the bound is outside the root
  private int proofBound(int i, CharSequence clause, int v, boolean lower) {
    IntDomain d = proofDomains[i];
    if (lower ? v <= d.min() || v > d.max() : v >= d.max() || v < d.min()) {
      return 0;
    }
    String bound = lower ? OpbEncoder.ge(i, v) : "~" + OpbEncoder.ge(i, v + 1);
    proof.lemma("rup 1 " + bound + clause + " >= 1 ;\n");
    return 1;
  }

  /** The OPB literal of a trail entry's atom weakened by slack, or "1" when the root has it. */
  private String proofAtom(int entry, int slack) {
    int i = trail.id(proofTrail.variable(entry));
    long v = proofTrail.value(entry);
    return switch (proofTrail.kind(entry)) {
      case AtomicTrail.GE ->
          v - slack <= proofDomains[i].min() ? "1" : OpbEncoder.ge(i, (int) (v - slack));
      case AtomicTrail.LE ->
          v + slack >= proofDomains[i].max() ? "1" : "~" + OpbEncoder.ge(i, (int) (v + slack + 1));
      default -> proofDomains[i].contains((int) v) ? "~" + OpbEncoder.eq(i, (int) v) : "1";
    };
  }

  /** Logs a solution of the store's domains: the order literals true in it. */
  private void logSolution() {
    List<String> lits = new ArrayList<>();
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] == null || root[i].singleton()) {
        continue;
      }
      int value = solution[i];
      for (int v = root[i].min() + 1; v <= root[i].max(); v++) {
        lits.add(v <= value ? OpbEncoder.ge(i, v) : "~" + OpbEncoder.ge(i, v));
      }
    }
    proof.solution(lits, objective >= 0);
  }

  /** Writes the conclusion of a search and closes the proof. */
  private void finishProof(int result, boolean optimising) {
    if (proof == null) {
      return;
    }
    startProof();
    if (rootRefuted || clauseFailedAtRoot) {
      // unit propagation over the derived units and the failed constraint gives the contradiction
      if (optimising) {
        proof.concludeBounds("INF", "INF");
      } else {
        proof.concludeUnsatisfiable();
      }
    } else if (optimising && !rootFailed && result == CdclSolver.UNKNOWN) {
      concludeLowerBound();
    } else if (rootFailed || result == CdclSolver.UNKNOWN) {
      proof.concludeNothing();
    } else if (!optimising) {
      if (result == CdclSolver.SAT) {
        proof.concludeSatisfiable();
      } else {
        proof.concludeUnsatisfiable();
      }
    } else if (best == null) {
      proof.concludeBounds("INF", "INF");
    } else {
      String value = Integer.toString(best[objective]);
      proof.concludeBounds(value, value);
    }
    try {
      proof.close();
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    }
  }

  /**
   * Concludes the bounds a search stopped by a limit proved: the best solution, and the lower bound
   * of the core-guided phase or of the root, stated over the objective's order literals; unit
   * propagation derives it from the clause that the objective is at least that bound.
   */
  private void concludeLowerBound() {
    IntDomain d = proofModelDomains == null ? null : proofModelDomains[objective];
    long lower = root[objective].min();
    if (coreSearch != null) {
      lower = Math.max(lower, coreSearch.lowerBound);
    }
    String upper = best == null ? null : Integer.toString(best[objective]);
    boolean reached = best != null && best[objective] <= lower;
    if (d == null || d.singleton() || lower <= d.min()) {
      if (reached && d != null) {
        // a solution at the least value of the objective: its improving constraint is false
        proof.concludeBounds(upper, upper);
      } else {
        proof.concludeNothing();
      }
      return;
    }
    StringBuilder s = new StringBuilder("rup");
    for (int v = d.min() + 1; v <= d.max(); v++) {
      s.append(" 1 ").append(OpbEncoder.ge(objective, v));
    }
    long id = proof.lemma(s.append(" >= ").append(lower - d.min()).append(" ;\n"));
    // with a solution at the bound, the improving constraint and the bound contradict each other
    proof.concludeBounds(reached ? upper : lower + " : " + id, upper);
  }

  // ------------------------------------------------------------------------------- literals

  private int newLiteral(int i, int kind, int value) {
    int d;
    if (numFree > 0) {
      d = free[--numFree];
      sat.reuse(d);
    } else {
      d = sat.newVariables(1);
      sat.observe(d);
    }
    if (d >= litVar.length) {
      int n = 2 * d;
      litVar = Arrays.copyOf(litVar, n);
      litKind = Arrays.copyOf(litKind, n);
      litValue = Arrays.copyOf(litValue, n);
    }
    if (d >= transientLit.length) {
      transientLit = Arrays.copyOf(transientLit, 2 * d);
    }
    if (d < atomUse.length) {
      atomUse[d] = 0;
    }
    litVar[d] = i;
    litKind[d] = (byte) kind;
    litValue[d] = value;
    return d;
  }

  /** A new solver variable that is not an atom, such as an output of a cardinality encoding. */
  int newAuxiliary() {
    int d = sat.newVariables(1);
    auxiliaryVariables++;
    if (d >= litVar.length) {
      int n = 2 * d;
      litVar = Arrays.copyOf(litVar, n);
      litKind = Arrays.copyOf(litKind, n);
      litValue = Arrays.copyOf(litValue, n);
    }
    litVar[d] = -1;
    return d;
  }

  /** The variable of [x >= v] for v in (root min, root max], created when missing, linked. */
  private int geVar(int i, int v) {
    int d = ge[i].get(v);
    if (d != LiteralMap.NONE) {
      if (transientLit[d]) {
        link(i, v, d);
      }
      return d;
    }
    int lit = newLiteral(i, GE_KIND, v);
    ge[i].put(v, lit);
    link(i, v, lit);
    return lit;
  }

  /**
   * Links [x >= v] to its linked neighbours by binary clauses, and pushes it when the domain
   * already decides it, since no clause may imply it yet.
   */
  private void link(int i, int v, int lit) {
    transientLit[lit] = false;
    boundLiterals++;
    int below = linked[i].lower(v);
    int above = linked[i].higher(v);
    if (below != LiteralMap.NONE) {
      structural.add(new int[] {-lit, below}); // [x >= v] -> [x >= below]
    }
    if (above != LiteralMap.NONE) {
      structural.add(new int[] {-above, lit}); // [x >= above] -> [x >= v]
    }
    linked[i].put(v, lit);
    if (!RELEASE || sat.value(lit) != 0) {
      return;
    }
    int e = trail.earliestLowerBound(vars[i], v, pushed);
    int implied = lit;
    if (e < 0 || e >= pushed) {
      e = trail.earliestUpperBound(vars[i], v - 1L, pushed);
      implied = -lit;
    }
    if (e >= 0 && e < pushed) {
      addImplied(implied, e);
    }
  }

  // a literal that the domains imply by a pushed entry, to push before the next atom
  private void addImplied(int lit, int entry) {
    if (numImplied == impliedLits.length) {
      impliedLits = Arrays.copyOf(impliedLits, 2 * numImplied);
      impliedEntries = Arrays.copyOf(impliedEntries, 2 * numImplied);
    }
    impliedLits[numImplied] = lit;
    impliedEntries[numImplied++] = entry;
  }

  /**
   * The variable of [x >= v] for a trail entry: an existing one, or a transient one, which is not
   * linked; the caller pushes the nearest linked literal it implies.
   */
  private int geEntryVar(int i, int v) {
    int d = ge[i].get(v);
    if (d != LiteralMap.NONE) {
      return d;
    }
    if (!RELEASE || sat.hasProof()) {
      return geVar(i, v);
    }
    int lit = newLiteral(i, GE_KIND, v);
    ge[i].put(v, lit);
    addTransient(lit);
    return lit;
  }

  private void addTransient(int lit) {
    transientLit[lit] = true;
    transientLiterals++;
    if (numTransients == transients.length) {
      transients = Arrays.copyOf(transients, 2 * numTransients);
      transientLevel = Arrays.copyOf(transientLevel, 2 * numTransients);
    }
    transients[numTransients] = lit;
    transientLevel[numTransients++] = sat.decisionLevel();
  }

  /** Links a transient literal that now occurs in a clause. */
  private void keep(int lit) {
    int d = Math.abs(lit);
    if (d < transientLit.length && transientLit[d]) {
      if (litKind[d] == EQ_KIND) {
        linkEq(litVar[d], litValue[d], d);
      } else {
        link(litVar[d], litValue[d], d);
      }
    }
  }

  /** Releases the transient literals created above a level, now unassigned. */
  private void release(int level) {
    while (numTransients > 0 && transientLevel[numTransients - 1] > level) {
      int d = transients[--numTransients];
      if (!transientLit[d]) {
        continue;
      }
      transientLit[d] = false;
      (litKind[d] == EQ_KIND ? eq : ge)[litVar[d]].remove(litValue[d]);
      sat.retire(d);
      if (numFree == free.length) {
        free = Arrays.copyOf(free, 2 * numFree);
      }
      free[numFree++] = d;
      literalsReleased++;
    }
  }

  /**
   * The nearest linked literal the atom of an entry implies when the entry's own literal is
   * transient, or 0.
   */
  private int linkedNeighbour(int entry, int lit) {
    if (!transientLit[Math.abs(lit)] || trail.kind(entry) == AtomicTrail.NE) {
      return 0;
    }
    int i = trail.id(trail.variable(entry));
    int v = trail.value(entry);
    if (trail.kind(entry) == AtomicTrail.GE) {
      int below = linked[i].lower(v);
      return below == LiteralMap.NONE ? 0 : below;
    }
    int above = linked[i].higher(v + 1);
    return above == LiteralMap.NONE ? 0 : -above;
  }

  /** The literal [x >= v]; 0 stands for a constant, which callers rule out. */
  private int geLit(int i, int v) {
    if (v <= root[i].min() || v > root[i].max()) {
      throw new IllegalStateException("[" + vars[i].id() + " >= " + v + "] is a constant");
    }
    return geVar(i, v);
  }

  /** The variable of [x = v] for v in the root domain, created when missing. */
  private int eqVar(int i, int v) {
    int d = eq[i].get(v);
    if (d != LiteralMap.NONE) {
      if (transientLit[d]) {
        linkEq(i, v, d);
      }
      return d;
    }
    int lit = newLiteral(i, EQ_KIND, v);
    eq[i].put(v, lit);
    linkEq(i, v, lit);
    return lit;
  }

  /**
   * The variable of [x = v] for a [x != v] trail entry: an existing one, or a transient one, in no
   * clause and not linked to [x >= v] and [x >= v + 1] until it occurs in a clause. Each value a
   * constraint removes from inside a domain is such an atom, and linking each made two bound
   * literals and four clauses for it.
   */
  private int eqEntryVar(int i, int v) {
    int d = eq[i].get(v);
    if (d != LiteralMap.NONE) {
      return d;
    }
    if (!RELEASE || sat.hasProof()) {
      return eqVar(i, v);
    }
    int lit = newLiteral(i, EQ_KIND, v);
    eq[i].put(v, lit);
    addTransient(lit);
    return lit;
  }

  /** Links [x = v] to [x >= v] and [x >= v + 1] by clauses. */
  private void linkEq(int i, int v, int lit) {
    transientLit[lit] = false;
    boolean atMin = v == root[i].min();
    boolean atMax = v == root[i].max();
    int geV = atMin ? 0 : geVar(i, v);
    int geNext = atMax ? 0 : geVar(i, v + 1);
    if (!atMin) {
      structural.add(new int[] {-lit, geV});
    }
    if (!atMax) {
      structural.add(new int[] {-lit, -geNext});
    }
    if (atMin && atMax) {
      structural.add(new int[] {lit});
    } else if (atMin) {
      structural.add(new int[] {lit, geNext});
    } else if (atMax) {
      structural.add(new int[] {lit, -geV});
    } else {
      structural.add(new int[] {lit, -geV, geNext});
    }
    equalityLiterals++;
    if (deferredAtoms > 0 && sat.value(lit) == 0) {
      // a deferred removal of v implies the new literal false, and no clause does
      EntryList found = scratchEntries;
      found.clear();
      if (trail.excludedBefore(vars[i], v, pushed, found)
          && found.size() > 0
          && trail.kind(found.get(0)) == AtomicTrail.NE) {
        addImplied(-lit, found.get(0));
      }
    }
  }

  /**
   * Whether a trail entry about to be pushed is a value removal to keep out of the solver: it has
   * no literal yet and the solver is over its {@link #literalBudget}.
   */
  private boolean defer(int entry) {
    return trail.kind(entry) == AtomicTrail.NE
        && RELEASE
        && !sat.hasProof()
        && sat.numVars() - numFree >= literalBudget
        && eq[trail.id(trail.variable(entry))].get(trail.value(entry)) == LiteralMap.NONE
        && !genericDeferred.contains(trail.reason(entry));
  }

  /**
   * Whether the solver has a trail entry's atom true. A value removal with no literal, deferred or
   * not pushed yet, is not given one: the caller explains it instead.
   */
  private boolean inSolver(int entry) {
    if (trail.kind(entry) == AtomicTrail.NE) {
      int d = eq[trail.id(trail.variable(entry))].get(trail.value(entry));
      return d != LiteralMap.NONE && sat.value(-d) > 0;
    }
    return sat.value(atomLit(entry)) > 0;
  }

  /**
   * Replaces the deferred value removals of a reason by their explanations, which are earlier on
   * the trail, until every entry left has its atom in the solver. Returns the solver literal of the
   * reason, which is {@code extra} unless an explanation brings one.
   */
  private int explainDeferred(EntryList reason, int extra) {
    EntryList stack = scratchEntries;
    stack.clear();
    for (int k = 0; k < reason.size(); k++) {
      stack.addFrom(reason, k);
    }
    reason.clear();
    // each deferred removal is explained once: explanations share them, and expanding one at each
    // citation took exponential time (a magic sequence of 80 counts)
    int seen = nextStamp();
    if (entryStamp.length < trail.size()) {
      entryStamp = Arrays.copyOf(entryStamp, Math.max(trail.size(), 2 * entryStamp.length));
    }
    while (stack.size() > 0) {
      int last = stack.size() - 1;
      int f = stack.get(last);
      if (trail.kind(f) != AtomicTrail.NE || inSolver(f)) {
        reason.addFrom(stack, last);
        stack.truncate(last);
        continue;
      }
      stack.truncate(last);
      if (entryStamp[f] == seen) {
        continue;
      }
      entryStamp[f] = seen;
      int lit = explainEntry(f, stack);
      if (lit != 0) {
        if (extra != 0 && extra != lit) {
          throw new IllegalStateException("a reason with two solver literals");
        }
        extra = lit;
      }
    }
    return extra;
  }

  /** The DIMACS literal that is true when a trail entry's atom holds. */
  private int atomLit(int entry) {
    int i = trail.id(trail.variable(entry));
    int v = trail.value(entry);
    return switch (trail.kind(entry)) {
      case AtomicTrail.GE -> geEntryLit(i, v);
      case AtomicTrail.LE -> -geEntryLit(i, v + 1);
      default -> -eqEntryVar(i, v);
    };
  }

  private int geEntryLit(int i, int v) {
    if (v <= root[i].min() || v > root[i].max()) {
      throw new IllegalStateException("[" + vars[i].id() + " >= " + v + "] is a constant");
    }
    return geEntryVar(i, v);
  }

  /**
   * The literal of an atom weakened by {@code slack} (see {@link EntryList#addLifted}), which
   * {@link #weakest} found; the entry's own literal when slack is 0.
   */
  private int atomLit(int entry, int slack) {
    if (slack == 0) {
      return atomLit(entry);
    }
    int i = trail.id(trail.variable(entry));
    int v = trail.value(entry);
    liftedLiterals++;
    return trail.kind(entry) == AtomicTrail.GE ? geLit(i, v - slack) : -geLit(i, v + slack + 1);
  }

  // reasons may cite literals true before this solver trail position (see weakest)
  private int liftBefore = Integer.MAX_VALUE;

  /**
   * The weakest bound from the limit to an atom's value whose literal exists and is true before
   * {@link #liftBefore}, so a reason may cite it.
   */
  private int weakest(IntVar x, boolean lower, int value, long limit) {
    LiteralMap m = ge[trail.id(x)];
    if (lower) {
      // [x >= u] for u in [limit, value), weakest first
      for (long u = m.ceilingValue(limit); u < value; u = m.ceilingValue(u + 1)) {
        if (holdsBefore(m.get((int) u))) {
          return (int) u;
        }
      }
    } else {
      // [x <= u - 1] = -[x >= u] for u in (value + 1, limit + 1], weakest (largest u) first
      for (long u = m.floorValue(limit + 1); u > value + 1L; u = m.floorValue(u - 1)) {
        if (holdsBefore(-m.get((int) u))) {
          return (int) u - 1;
        }
      }
    }
    return value;
  }

  // whether the solver has a literal true before liftBefore
  private boolean holdsBefore(int lit) {
    if (sat.value(lit) <= 0) {
      return false;
    }
    int position = sat.trailPosition(lit);
    return position >= 0 && position < liftBefore;
  }

  /** Sets the {@link #literalBudget}; 0 keeps every value removal with no literal out. */
  void setLiteralBudget(long budget) {
    literalBudget = budget;
  }

  /**
   * Returns the solver, for its settings and statistics.
   *
   * @return the CDCL solver
   */
  public CdclSolver sat() {
    return sat;
  }

  // ------------------------------------------------------------------------ root probing

  // -Djacop.lcg.probe.domain: the largest domain whose values root probing tries one by one
  private static final int PROBE_MAX_DOMAIN = Integer.getInteger("jacop.lcg.probe.domain", 64);

  // -Djacop.lcg.probe.barren: the share of its budget after which probing that found no fact stops
  private static final double PROBE_BARREN =
      Double.parseDouble(System.getProperty("jacop.lcg.probe.barren", "0.25"));

  /** Statistics of {@link #probeRoot}: whether it stopped early for finding no fact. */
  public boolean probeBarren;

  /** Statistics of {@link #probeRoot}: 0/1 variables not fixed when probing started. */
  public long probeBooleans;

  /** Statistics of {@link #probeRoot}: 0/1 variables the root's propagation fixed before it. */
  public long probeFixedBefore;

  /** Statistics of {@link #probeRoot}: other variables whose values it probes (small domains). */
  public long probeValueVariables;

  /** Statistics of {@link #probeRoot}: the values of those variables when probing started. */
  public long probeValues;

  /** Statistics of {@link #probeRoot}: literals probed. */
  public long probeProbes;

  /** Statistics of {@link #probeRoot}: failed literals, whose negation became a root fact. */
  public long probeFailed;

  /**
   * Statistics of {@link #probeRoot}: atoms that every value of a variable implies (root facts).
   */
  public long probeLifted;

  /** Statistics of {@link #probeRoot}: 0/1 variables fixed at the root by probing. */
  public long probeFixedBooleans;

  /** Statistics of {@link #probeRoot}: values removed from the small domains by probing. */
  public long probeValuesRemoved;

  /** Statistics of {@link #probeRoot}: pairs of 0/1 variables found equal or opposite. */
  public long probeEquivalences;

  /** Statistics of {@link #probeRoot}: implications x = 1 -> y = 0 between 0/1 variables. */
  public long probeExclusions;

  /** Statistics of {@link #probeRoot}: passes over the variables. */
  public long probePasses;

  /** Statistics of {@link #probeRoot}: nanoseconds spent. */
  public long probeNanos;

  /** Statistics of {@link #probeRoot}: whether the budget stopped probing before its fixpoint. */
  public boolean probeExhausted;

  // an atom of a probe's consequences, decoded at once since transient literals are reused
  private record Atom(int var, int kind, int value, boolean holds) {
    Atom negated() {
      return new Atom(var, kind, value, !holds);
    }
  }

  private Atom atom(int lit) {
    int d = Math.abs(lit);
    int i = litVar[d];
    return i < 0 ? null : new Atom(i, litKind[d], litValue[d], lit > 0);
  }

  // the value a 0/1 variable takes when an atom of it holds, or -1 when the atom is not of one
  private int booleanValue(Atom a) {
    if (!isBoolean(a.var)) {
      return -1;
    }
    // [x >= 1] or [x = v] for v in {0, 1}
    int v = a.kind == GE_KIND ? 1 : a.value;
    return a.holds ? v : 1 - v;
  }

  private boolean isBoolean(int i) {
    return i >= 0 && i < vars.length && vars[i] != null && root[i].min() == 0 && root[i].max() == 1;
  }

  // whether the store's domains imply an atom already
  private boolean entailed(Atom a) {
    IntDomain d = vars[a.var].dom();
    if (a.kind == GE_KIND) {
      return a.holds ? d.min() >= a.value : d.max() < a.value;
    }
    return a.holds ? d.singleton(a.value) : !d.contains(a.value);
  }

  private int literalOf(Atom a) {
    int d = a.kind == GE_KIND ? geLit(a.var, a.value) : eqVar(a.var, a.value);
    return a.holds ? d : -d;
  }

  private Set<Atom> consequences(int[] implied) {
    Set<Atom> atoms = new HashSet<>(implied.length * 2);
    for (int l : implied) {
      Atom a = atom(l);
      if (a != null) {
        atoms.add(a);
      }
    }
    return atoms;
  }

  // the outcome of probing one variable
  private static final int REFUTED = -1;
  private static final int NOTHING = 0;
  private static final int FACTS = 1;

  /**
   * Failed-literal probing at the root, which only adds facts: each value of each 0/1 variable,
   * then each value of each variable with a small domain, is assumed in turn and propagated by the
   * clauses and the store's constraints. A value that fails is removed at the root; an atom that
   * every value of a variable implies holds at the root (lifting). The model itself is not changed.
   * Pairs of 0/1 variables found equal or opposite, and implications x = 1 -> y = 0 (the edges of
   * at-most-one cliques), are counted. Passes repeat while a pass adds facts and the budget lasts.
   *
   * <p>Failed literals and lifting are the classic SAT probing techniques: J. W. Freeman,
   * Improvements to propositional satisfiability search algorithms, PhD thesis, University of
   * Pennsylvania, 1995; I. Lynce and J. Marques-Silva, Probing-based preprocessing techniques for
   * propositional satisfiability, ICTAI 2003; for mixed integer programs M. W. P. Savelsbergh,
   * Preprocessing and probing techniques for mixed integer programming problems, ORSA Journal on
   * Computing 6(4), 1994. Probing every value of a variable is singleton consistency at the root:
   * R. Debruyne and C. Bessière, Some practicable filtering techniques for the constraint
   * satisfaction problem, IJCAI 1997.
   *
   * @param budgetNanos the time probing may take
   * @return false when probing proved that the constraints have no solution
   */
  public boolean probeRoot(long budgetNanos) {
    long start = System.nanoTime();
    long end = budgetNanos >= Long.MAX_VALUE - start ? Long.MAX_VALUE : start + budgetNanos;
    end = Math.min(end, sat.deadline());
    if (rootFailed || proof != null) {
      return !rootFailed;
    }
    encodeGraphs();
    // the clauses added since the solver was made (graphs, collected clauses) propagate first, so
    // that only what probing adds is counted
    if (!propagateRoot()) {
      rootFailed = true;
      return false;
    }
    List<Integer> booleans = new ArrayList<>();
    List<Integer> valued = new ArrayList<>();
    for (int i = 0; i < vars.length; i++) {
      if (isBoolean(i) && vars[i].singleton()) {
        probeFixedBefore++;
      } else if (isBoolean(i)) {
        booleans.add(i);
      } else if (vars[i] != null && !vars[i].singleton() && vars[i].getSize() <= PROBE_MAX_DOMAIN) {
        valued.add(i);
        probeValues += vars[i].getSize();
      }
    }
    probeBooleans = booleans.size();
    probeValueVariables = valued.size();
    try {
      boolean changed = true;
      while (changed) {
        changed = false;
        probePasses++;
        for (List<Integer> group : List.of(booleans, valued)) {
          for (int i : group) {
            long now = System.nanoTime();
            if (now > end) {
              probeExhausted = true;
              return true;
            }
            if (probeFailed + probeLifted == 0 && now - start > PROBE_BARREN * (end - start)) {
              // a share of the budget gave nothing: the rest would most likely give nothing too
              probeBarren = true;
              return true;
            }
            int outcome = isBoolean(i) ? probeBoolean(i) : probeValues(i, end);
            if (outcome == REFUTED) {
              rootFailed = true;
              return false;
            }
            changed |= outcome == FACTS;
          }
        }
      }
      return true;
    } finally {
      probeNanos += System.nanoTime() - start;
      if (!rootFailed && !propagateRoot()) {
        rootFailed = true;
      }
      for (int i : booleans) {
        if (vars[i].singleton() || sat.value(geLit(i, 1)) != 0) {
          probeFixedBooleans++;
        }
      }
      long left = 0;
      for (int i : valued) {
        left += vars[i].getSize();
      }
      probeValuesRemoved = probeValues - left;
    }
  }

  // probes both values of a 0/1 variable
  private int probeBoolean(int i) {
    int one = geLit(i, 1);
    if (vars[i].singleton() || sat.value(one) != 0) {
      return NOTHING;
    }
    probeProbes++;
    int[] upImplied = probe(one);
    if (!sat.isOk()) {
      return REFUTED;
    }
    if (upImplied == null) {
      probeFailed++;
      return sat.addClause(-one) ? FACTS : REFUTED;
    }
    if (sat.value(one) != 0) {
      return NOTHING;
    }
    Set<Atom> up = consequences(upImplied);
    probeProbes++;
    int[] downImplied = probe(-one);
    if (!sat.isOk()) {
      return REFUTED;
    }
    if (downImplied == null) {
      probeFailed++;
      return sat.addClause(one) ? FACTS : REFUTED;
    }
    if (sat.value(one) != 0) {
      return NOTHING;
    }
    if (probeConflicts != null) {
      recordConflicts(i, 1, up);
      recordConflicts(i, 0, consequences(downImplied));
    }
    List<Atom> lifted = new ArrayList<>();
    for (int l : downImplied) {
      Atom a = atom(l);
      if (a == null) {
        continue;
      }
      if (up.contains(a)) {
        lifted.add(a);
      }
      if (booleanValue(a) >= 0 && a.var > i && up.contains(a.negated())) {
        // x = 0 -> y = b and x = 1 -> y = 1 - b: y equals x or its negation
        probeEquivalences++;
      }
    }
    for (Atom a : up) {
      if (a.var > i && booleanValue(a) == 0) {
        probeExclusions++;
      }
    }
    return addLifted(lifted);
  }

  // the conflicts (x = value, y = 1 - b) of the implications x = value -> y = b found by a probe
  private void recordConflicts(int i, int value, Set<Atom> implied) {
    for (Atom a : implied) {
      int b = booleanValue(a);
      if (b >= 0 && a.var != i && probeConflicts.size() < probeConflictCap) {
        probeConflicts.add(new IntVar[] {vars[i], vars[a.var]});
        probeConflictValues.add(new int[] {value, 1 - b});
      }
    }
  }

  // the conflicts between values of 0/1 variables that probing found, when they are kept
  private List<IntVar[]> probeConflicts;
  private List<int[]> probeConflictValues;
  private int probeConflictCap;

  // when (System.nanoTime()) the next run of the search from the root probes it first, or 0
  private long delayedProbeAt;
  private long delayedProbeBudget;

  /**
   * Probes the root ({@link #probeRoot}) at the start of the first run of the search from the root
   * after a time, between runs of branch and bound, so that instances solved before it do not pay
   * for probing. A satisfaction search is one run and is not probed.
   *
   * @param atNanos the {@link System#nanoTime()} after which the next run probes first
   * @param budgetNanos the time probing may take
   */
  public void setDelayedProbe(long atNanos, long budgetNanos) {
    delayedProbeAt = atNanos == 0 ? 1 : atNanos;
    delayedProbeBudget = budgetNanos;
  }

  /**
   * Keeps the conflicts that the next {@link #probeRoot} finds between values of 0/1 variables: x =
   * a and y = b cannot hold together because probing x = a implied y = 1 - b. They are the edges of
   * the at-most-one cliques (and, two by two, the equivalences) that the linear relaxation can use
   * as clique rows.
   *
   * @param cap the most conflicts kept
   */
  public void keepProbeConflicts(int cap) {
    probeConflicts = new ArrayList<>();
    probeConflictValues = new ArrayList<>();
    probeConflictCap = cap;
  }

  /**
   * Returns the conflicts kept by {@link #keepProbeConflicts}.
   *
   * @return pairs of 0/1 variables
   */
  public List<IntVar[]> probeConflicts() {
    return probeConflicts == null ? List.of() : probeConflicts;
  }

  /**
   * Returns the values of the conflicts of {@link #probeConflicts}, at the same positions.
   *
   * @return pairs of values, each 0 or 1
   */
  public List<int[]> probeConflictValues() {
    return probeConflictValues == null ? List.of() : probeConflictValues;
  }

  // probes each value of a variable with a small domain
  private int probeValues(int i, long end) {
    int outcome = NOTHING;
    Set<Atom> common = null;
    boolean complete = true;
    for (ValueEnumeration e = vars[i].dom().cloneLight().valueEnumeration();
        e.hasMoreElements(); ) {
      int v = e.nextElement();
      if (!vars[i].dom().contains(v)) {
        continue;
      }
      if (vars[i].singleton() || System.nanoTime() > end) {
        complete = false;
        break;
      }
      int lit = eqVar(i, v);
      if (sat.value(lit) != 0) {
        complete &= sat.value(lit) < 0;
        continue;
      }
      probeProbes++;
      int[] implied = probe(lit);
      if (!sat.isOk()) {
        return REFUTED;
      }
      if (implied == null) {
        probeFailed++;
        if (!sat.addClause(-lit)) {
          return REFUTED;
        }
        outcome = FACTS;
        continue;
      }
      if (sat.value(lit) != 0) {
        complete = false;
        continue;
      }
      Set<Atom> atoms = consequences(implied);
      if (common == null) {
        common = atoms;
      } else {
        common.retainAll(atoms);
      }
    }
    if (complete && common != null && !common.isEmpty()) {
      int lifted = addLifted(new ArrayList<>(common));
      if (lifted != NOTHING) {
        return lifted;
      }
    }
    return outcome;
  }

  private int addLifted(List<Atom> lifted) {
    int outcome = NOTHING;
    for (Atom a : lifted) {
      if (entailed(a)) {
        continue;
      }
      int lit = literalOf(a);
      if (sat.value(lit) > 0) {
        continue;
      }
      probeLifted++;
      outcome = FACTS;
      if (!sat.addClause(lit)) {
        return REFUTED;
      }
    }
    return outcome;
  }

  // propagates the root, with the store's constraints, by probing an atom not decided yet
  private boolean propagateRoot() {
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] != null && !vars[i].singleton()) {
        int lit = geLit(i, vars[i].max());
        if (sat.value(lit) == 0) {
          probe(lit);
          return sat.isOk();
        }
      }
    }
    return sat.isOk();
  }

  /**
   * Solves the store's constraints.
   *
   * @return {@link CdclSolver#SAT}, {@link CdclSolver#UNSAT} or {@link CdclSolver#UNKNOWN}
   */
  public int solve() {
    int result = solve(new int[0]);
    if (objective < 0) {
      finishProof(result, false);
    }
    return result;
  }

  private int solve(int... assumed) {
    encodeGraphs();
    startProof();
    if (rootFailed) {
      return CdclSolver.UNSAT;
    }
    if (delayedProbeAt != 0 && assumed.length == 0 && System.nanoTime() >= delayedProbeAt) {
      // the search has run for a while without an answer: probe the root, now with the learnt
      // clauses and the bound of the best solution
      delayedProbeAt = 0;
      if (!probeRoot(delayedProbeBudget)) {
        return CdclSolver.UNSAT;
      }
    }
    solution = null;
    exchangeShared();
    // clauses propagate between constraints: each consistency() returns after a pruning constraint
    store.setReturnAfterPruning(!fullFixpoint);
    int result;
    try {
      result = sat.solve(assumed);
    } finally {
      store.setReturnAfterPruning(false);
    }
    if (proof != null && result == CdclSolver.UNSAT && assumed.length > 0 && sat.isOk()) {
      // the clause that one of the failed assumptions is false, which unit propagation derives
      // from the clauses the solver has, as conflict analysis did
      int[] localFailed = sat.failedAssumptions();
      int[] clause = new int[localFailed.length];
      for (int k = 0; k < localFailed.length; k++) {
        clause[k] = -localFailed[k];
      }
      if (clause.length > 0) {
        proof.lemma(proofClause(clause));
      }
    }
    // the solver leaves its last assignment without notifying; the store goes back to the root
    notifyBacktrack(0);
    exchangeShared();
    return result;
  }

  /**
   * Minimises a variable by branch and bound inside one search: at each solution the solver gets
   * the clause that the objective is smaller and backjumps, keeping its learnt clauses, until no
   * solution is left. {@link #value} then gives the best solution found.
   *
   * @param objective the variable to minimise
   * @return {@link CdclSolver#SAT} when the best solution is optimal, {@link CdclSolver#UNSAT} when
   *     there is no solution, or {@link CdclSolver#UNKNOWN} when a limit stopped the search
   */
  public int minimize(IntVar objective) {
    clauseObjective = objective;
    encodeGraphs();
    this.objective = trail.id(objective);
    best = null;
    lastBound = Long.MIN_VALUE;
    if (proof != null && coreShare > 0) {
      // the core-guided phase sums the model's lines, so the proof starts before it
      startProof();
    }
    coreSearch = coreShare > 0 ? CoreSearch.of(this, objective) : null;
    int result;
    // a conflict limit set before bounds the core-guided phase and branch and bound
    conflictCap = sat.conflictLimit();
    try {
      if (bisectGap > 0 && proof == null) {
        result = minimizeByBisection();
      } else if (coreSearch != null) {
        result = minimizeWithCores();
      } else {
        result = interleaved() ? minimizeWithLowerBoundSearch() : solve();
      }
    } finally {
      this.objective = -1;
      sat.setConflictLimit(Long.MAX_VALUE);
      conflictCap = Long.MAX_VALUE;
    }
    solution = best;
    if (proof != null) {
      int id = this.objective;
      this.objective = trail.id(objective);
      finishProof(result, true);
      this.objective = id;
    }
    if (result == CdclSolver.UNKNOWN && !sharedBoundUnreachable) {
      return CdclSolver.UNKNOWN;
    }
    // SAT when the solution has the smallest value of the objective, UNSAT when none is better
    return best == null ? CdclSolver.UNSAT : CdclSolver.SAT;
  }

  /**
   * Runs core-guided search, then branch and bound from its best solution and lower bound. The
   * core-guided search takes at most its share of the time left (its budget of conflicts when there
   * is no deadline), and stops early when one call of the solver needs more than its limit of
   * conflicts: a sign that it no longer finds cores or solutions quickly. It also stops when it has
   * no solution of its own after a third of its time. Under a solution bound, every solution the
   * core-guided search finds would have to improve, which makes its strata hard, so the bound comes
   * only after it. Branch and bound then starts from the variables' activity before the core-guided
   * search.
   */
  // the most times the core-guided phase gets another share of the time
  private static final int MAX_CORE_EXTENSIONS = 8;

  // -Djacop.lcg.coreSkip=false: the core-guided phase runs after its probe even when the probe's
  // rate could not raise the bound to the objective's root bound
  private static final boolean CORE_SKIP =
      Boolean.parseBoolean(System.getProperty("jacop.lcg.coreSkip", Boolean.TRUE.toString()));

  // the share of the core-guided phase that measures its rate when the objective's root bound is
  // above the cores' lower bound
  private static final double CORE_TRIAL =
      Double.parseDouble(System.getProperty("jacop.lcg.coreTrial", "0.1"));

  /**
   * Statistics: core-guided phases skipped after the probe, as below the objective's root bound.
   */
  public long coreSkips;

  // -Djacop.lcg.coreProbeSkip=false: the core-guided phase runs after branch and bound also when
  // its probe stopped without a solution of its own
  private boolean coreProbeSkip =
      Boolean.parseBoolean(System.getProperty("jacop.lcg.coreProbeSkip", Boolean.TRUE.toString()));

  /** Statistics: core-guided phases skipped as their probe found no solution of its own. */
  public long probeSkips;

  private int minimizeWithCores() {
    long millis = timeLimitMillis;
    if (millis <= 0 && sat.deadline() != Long.MAX_VALUE) {
      millis = Math.max(1, (sat.deadline() - System.nanoTime()) / 1_000_000L);
    }
    workEnd = millis > 0 ? sat.work() + millis * WORK_PER_MS : Long.MAX_VALUE;
    int result;
    if (coresWithoutSolutionOnly) {
      result = firstSolutionBeforeCores();
      if (result == CdclSolver.UNSAT) {
        return result;
      }
      if (best != null) {
        // a solution: branch and bound goes on, as without the core-guided phase
        return interleaved() ? minimizeWithLowerBoundSearch() : solve();
      }
      if (System.nanoTime() > sat.deadline()) {
        return result;
      }
    } else if (coreDelayShare > 0) {
      boolean probeWithoutSolution = false;
      if (coreProbeShare > 0) {
        long stops = coreSearch.noSolutionStops;
        result = runCores(coreProbeShare, coreDelayBudget, false);
        if (result != CdclSolver.UNKNOWN || System.nanoTime() > sat.deadline()) {
          return result;
        }
        probeWithoutSolution = coreSearch.noSolutionStops > stops;
      }
      result = minimizeBeforeCores();
      if (result != CdclSolver.UNKNOWN || System.nanoTime() > sat.deadline()) {
        return result;
      }
      if (coreProbeSkip && probeWithoutSolution && best != null) {
        // the probe found no solution of its own while branch and bound did: the rest of the phase
        // stops the same way after a third of its work and gives the time back
        probeSkips++;
        return afterCores();
      }
    }
    double share = coreShare;
    if (CORE_SKIP && workEnd != Long.MAX_VALUE && coreSearch.lowerBound < root[objective].min()) {
      // the root bound of the objective (from the linear relaxation, say) is above the cores' lower
      // bound: a trial part of the phase measures how fast the cores raise it, and the rest of the
      // phase runs only if they could reach the root bound at that rate. Below it they prove
      // nothing, and branch and bound needs the time for the solutions: concert-hall-cap 2024
      // 200_20 found no better solution during 32 s of cores that raised the bound a twentieth of
      // the way to the root bound
      coreSearch.mark();
      result = runCores(CORE_TRIAL * coreShare, coreBudget, false);
      if (result != CdclSolver.UNKNOWN) {
        return result;
      }
      share = (1 - CORE_TRIAL) * coreShare / (1 - CORE_TRIAL * coreShare);
      boolean reach = coreSearch.canReach(root[objective].min(), (long) (share * workLeft()));
      if (!reach) {
        coreSkips++;
        return afterCores();
      }
    }
    double[] saved = CORE_RESTORE ? activity.clone() : null;
    double savedInc = activityInc;
    result = runCores(share, coreBudget, true);
    if (result != CdclSolver.UNKNOWN) {
      return result;
    }
    if (saved != null) {
      // the core phase bumped the variables of conflicts under its assumptions, which mislead
      // branch and bound: harmony-brother reached the optimum's bound in 8 s and then did not find
      // the optimum, which branch and bound alone proves in 35 s
      System.arraycopy(saved, 0, activity, 0, Math.min(saved.length, activity.length));
      activityInc = savedInc;
      rebuildHeap(heap);
      rebuildHeap(wide);
      rebuildHeap(lateHeap);
    }
    return afterCores();
  }

  /** Branch and bound after the core-guided phase, from its best solution. */
  private int afterCores() {
    if (!requireBetter()) {
      return CdclSolver.SAT;
    }
    return interleaved() ? minimizeWithLowerBoundSearch() : solve();
  }

  /** Whether runs of branch and bound alternate with lower-bound or neighbourhood runs. */
  private boolean interleaved() {
    return proof == null && (lowerBoundShare > 0 || lns != null);
  }

  /**
   * Runs core-guided search for a share of the work left (see {@link #setTimeLimit}), or a number
   * of conflicts when there is neither a time limit nor a deadline. A later run picks up where this
   * one stopped. When extend is set, a run that stopped while its lower bound, at its rate so far,
   * would meet the best solution before the end of the run gets another share of the work left. So
   * does a run that stopped as too slow for the work left of its share once the run brought its
   * lower bound half way to the best solution (jp-encoding data1000 stopped after 94 cores, 1,800
   * below the best solution and 2,800 above the bound the run started from, and is proved in 2 s
   * more); further from it, branch and bound needs the time more (concert-hall-cap, 18,500 below
   * and 3,500 above, lost its proof). A run that did not raise the bound is not extended
   * (concert-hall-cap spent two extensions, half of the time left each, at one bound).
   */
  private int runCores(double share, long conflicts, boolean extend) {
    long deadline = sat.deadline();
    coreMode = true;
    try {
      if (workEnd == Long.MAX_VALUE) {
        return coreSearch.run(sat.conflicts + conflicts, coreCallLimit);
      }
      long full = setPhaseLimits(share, deadline);
      int result;
      if (CORE_NO_SOLUTION > 0) {
        // without a solution of its own by this share of the phase, branch and bound gets the time
        long now = sat.work();
        sat.setWorkLimit(now + (long) (CORE_NO_SOLUTION * (full - now)));
        result = coreSearch.run(Long.MAX_VALUE, coreCallLimit);
        if (result == CdclSolver.UNKNOWN && sat.work() >= sat.workLimit()) {
          if (ownSolution()) {
            sat.setWorkLimit(full);
            result = coreSearch.run(Long.MAX_VALUE, coreCallLimit);
          } else {
            coreSearch.noSolutionStops++;
          }
        }
      } else {
        result = coreSearch.run(Long.MAX_VALUE, coreCallLimit);
      }
      for (int extension = 0;
          extend
              && extension < MAX_CORE_EXTENSIONS
              && result == CdclSolver.UNKNOWN
              && extendCores(deadline);
          extension++) {
        setPhaseLimits(share, deadline);
        result = coreSearch.run(Long.MAX_VALUE, coreCallLimit);
      }
      return result;
    } finally {
      coreMode = false;
      endPhase(deadline);
    }
  }

  /**
   * Gives a phase of the core-guided schedule its share of the work left (see {@link #workLeft}):
   * the solver's work limit, and, with a deadline, a deadline at {@link #CLOCK_SLACK} times that
   * share of the time left, which stops the phase only where the work is much slower than {@link
   * #WORK_PER_MS}.
   *
   * @return the work limit set
   */
  private long setPhaseLimits(double share, long deadline) {
    if (deadline != Long.MAX_VALUE) {
      long now = System.nanoTime();
      double slack = Math.min(1, CLOCK_SLACK * share);
      sat.setDeadline(now + (long) (slack * Math.max(0, deadline - now)));
    }
    long limit = sat.work() + (long) (share * workLeft());
    sat.setWorkLimit(limit);
    return limit;
  }

  /** Restores the limits of the run after a phase of the core-guided schedule. */
  private void endPhase(long deadline) {
    if (sat.deadline() < deadline && System.nanoTime() > sat.deadline()) {
      clockStops++;
    }
    sat.setDeadline(deadline);
    sat.setWorkLimit(Long.MAX_VALUE);
    sat.setConflictLimit(conflictCap);
  }

  /** The work left before the end of the run, as the core-guided schedule counts it. */
  private long workLeft() {
    return Math.max(0, workEnd - sat.work());
  }

  /** The work at which the core-guided schedule counts the run as over. */
  long workEnd() {
    return workEnd;
  }

  /**
   * The work of the solver per millisecond of a time limit, from which the core-guided phase and
   * the branch and bound before it take their shares, so that a run repeats with the same limit
   * whatever the load of the machine. The work is the propagated literals plus {@link
   * #WORK_PER_CALL} per consistency call of a constraint.
   */
  static final long WORK_PER_MS = Long.getLong("jacop.lcg.workPerMs", 2_000);

  // the work of one consistency call of a constraint, in propagated literals
  static final long WORK_PER_CALL = Long.getLong("jacop.lcg.workPerCall", 3);

  // a phase also stops at this many times its share of the time left, where the work is slower
  private static final double CLOCK_SLACK =
      Double.parseDouble(System.getProperty("jacop.lcg.clockSlack", "1.5"));

  /** Statistics: phases of the core-guided schedule stopped by the clock, not by their work. */
  public long clockStops;

  // -Djacop.lcg.coreAnySolution=true: the old test, any best solution, also one of branch and
  // bound before the phase
  private static final boolean CORE_ANY_SOLUTION =
      "true".equals(System.getProperty("jacop.lcg.coreAnySolution"));

  /**
   * Whether the core-guided phase has a solution of its own, which lets it run past the share of
   * its time that {@link #CORE_NO_SOLUTION} gives it without one. Solutions of branch and bound
   * before the phase do not count: there nearly always is one, and city-position spent half of its
   * time in cores that raised the bound to 435 against an optimum of 3,493.
   */
  private boolean ownSolution() {
    return CORE_ANY_SOLUTION ? best != null : coreSearch.stratumSolutions > 0;
  }

  /**
   * Whether the core-guided run that just stopped gets another share of the time left before the
   * given deadline, as {@link #runCores} describes.
   */
  private boolean extendCores(long deadline) {
    if (System.nanoTime() > deadline || !coreSearch.rose() || !coreSearch.closing(workEnd)) {
      return false;
    }
    return sat.work() >= sat.workLimit() || !coreSearch.exhausted() && coreSearch.halfWay();
  }

  /**
   * Runs branch and bound for the share of the time left that {@link #setCoreDelay} gives it (its
   * budget of conflicts when there is no deadline), before core-guided search. Easy models, which
   * branch and bound proves in a few conflicts, are then done before the core-guided phase spends
   * its share on cores that raise the lower bound slowly. The bound that each solution must improve
   * is an assumption, not a clause: under a bound every stratum of the core-guided phase would have
   * to improve, which makes its strata hard. Clauses learnt under an assumption hold without it.
   */
  /**
   * Runs branch and bound for the share of the time left that {@link #setCoreDelay} gives it,
   * before the core-guided phase that {@link #setCoresWithoutSolutionOnly} runs only without a
   * solution. With one, branch and bound goes on as without the core-guided phase.
   */
  private int firstSolutionBeforeCores() {
    long deadline = sat.deadline();
    if (workEnd != Long.MAX_VALUE) {
      setPhaseLimits(coreDelayShare, deadline);
    } else {
      sat.setConflictLimit(Math.min(conflictCap, sat.conflicts + coreDelayBudget));
    }
    try {
      return solve();
    } finally {
      endPhase(deadline);
    }
  }

  private int minimizeBeforeCores() {
    long deadline = sat.deadline();
    if (workEnd != Long.MAX_VALUE) {
      setPhaseLimits(coreDelayShare, deadline);
    } else {
      sat.setConflictLimit(Math.min(conflictCap, sat.conflicts + coreDelayBudget));
    }
    coreMode = true; // a solution ends the call of the solver without a clause
    try {
      while (true) {
        if (best != null && best[objective] <= root[objective].min()) {
          return CdclSolver.SAT;
        }
        int result = best == null ? solve() : solve(-geLit(objective, best[objective]));
        if (result == CdclSolver.UNSAT) {
          // with a best solution: none is better, whether or not the bound took part
          return best == null ? CdclSolver.UNSAT : CdclSolver.SAT;
        }
        if (result == CdclSolver.UNKNOWN) {
          return result;
        }
      }
    } finally {
      coreMode = false;
      endPhase(deadline);
    }
  }

  /**
   * Adds the clause that the objective is below its value in the best solution, if there is one.
   * Returns false when that value is the objective's smallest, so the best solution is optimal.
   */
  boolean requireBetter() {
    if (best == null) {
      return true;
    }
    int v = best[objective];
    if (v <= vars[objective].min()) {
      return false;
    }
    addProvedClause(-geLit(objective, v)); // objective <= v - 1
    return true;
  }

  // ------------------------------------------------------- proof of the core-guided phase

  /** Whether a proof is written. */
  boolean proving() {
    return proof != null;
  }

  /**
   * Adds a clause that unit propagation derives, writing it to the proof as a {@code rup} step: the
   * solver writes only the clauses it derives itself.
   *
   * @param lits the clause, DIMACS literals
   * @return false when the solver is unsatisfiable at the root
   */
  boolean addProvedClause(int... lits) {
    if (proof != null) {
      proof.lemma(proofClause(lits));
    }
    return sat.addClause(lits);
  }

  // the rup step of a clause
  private String proofClause(int... lits) {
    StringBuilder s = new StringBuilder("rup");
    for (int l : lits) {
      s.append(" 1 ").append(proofLiteral(l));
    }
    return s.append(" >= 1 ;\n").toString();
  }

  /** The proof's name of a DIMACS literal, with {@code ~} when negative. */
  String proofLiteral(int lit) {
    String name = proofName(Math.abs(lit));
    return lit < 0 ? "~" + name : name;
  }

  /** Names an auxiliary variable in the proof, which then defines it. */
  void nameAuxiliary(int d) {
    proofAuxiliaries.set(d);
  }

  /**
   * The id of the order line {@code [x >= v] or not [x >= v + 1]} of variable i in the proof's
   * model, or 0 when the model has no such line.
   */
  long proofChainLine(int i, int v) {
    IntDomain d = proofModelDomains[i];
    if (d == null || d.singleton() || v <= d.min() || v >= d.max() || proofChains[i] == 0) {
      return 0;
    }
    return proofChains[i] + (v - d.min() - 1);
  }

  /**
   * The ids of the model's lines {@code sum >= c} and {@code sum <= c} of an equality, for the sum
   * and constant of the given form, or null when the model does not have them.
   */
  long[] proofEquality(Constraint c, LinearForm f) {
    OpbEncoder.EqualityLine line = proofEqualities.get(c);
    if (line == null) {
      return null;
    }
    int sign = sameSum(f, line.form());
    if (sign == 0) {
      return null;
    }
    return sign > 0 ? new long[] {line.id(), line.id() + 1} : new long[] {line.id() + 1, line.id()};
  }

  // 1 when the forms are the same sum and constant, -1 when one is the other negated, else 0
  private static int sameSum(LinearForm f, LinearForm g) {
    Map<IntVar, Long> a = terms(f);
    Map<IntVar, Long> b = terms(g);
    if (a.equals(b) && f.c() == g.c()) {
      return 1;
    }
    b.replaceAll((x, w) -> -w);
    return a.equals(b) && f.c() == -g.c() ? -1 : 0;
  }

  private static Map<IntVar, Long> terms(LinearForm f) {
    Map<IntVar, Long> terms = new HashMap<>();
    for (int k = 0; k < f.vars().length; k++) {
      terms.merge(f.vars()[k], f.weights()[k], Long::sum);
    }
    terms.values().removeIf(w -> w == 0);
    return terms;
  }

  /**
   * Turns on core-guided search in {@link #minimize} when the objective is a linear sum: before
   * branch and bound, it finds unsatisfiable cores of the assumptions that each term of the sum
   * stays at its lower bound and relaxes them (OLL), raising the objective's lower bound, until it
   * proves a solution optimal, its time is up, or one call of the solver needs too many conflicts.
   *
   * @param share the share of the time left that it may take; 0 turns it off
   * @param conflicts the conflicts it may take when there is no deadline
   * @param callLimit the conflicts one call of the solver may take before it stops
   */
  public void setCoreSearch(double share, long conflicts, long callLimit) {
    coreShare = share;
    coreBudget = Math.max(1, conflicts);
    coreCallLimit = Math.max(1, callLimit);
  }

  /**
   * Lets branch and bound run first when {@link #minimize} uses core-guided search: for a share of
   * the time left, or for a number of conflicts when there is no deadline. The core-guided phase
   * starts only when this run neither proves the optimum nor shows there is no solution, and keeps
   * its best solution.
   *
   * @param share the share of the time left for branch and bound first; 0 for none
   * @param conflicts the conflicts of that run, and of the probe, when there is no deadline
   * @param probe the share of the time left for core-guided search before that run, which proves
   *     the models where cores close the gap at once; 0 for none
   */
  /**
   * Sets whether the core-guided phase of {@link #minimize} runs only when a search for a first
   * solution, for the share of the time that {@link #setCoreDelay} gives branch and bound, finds
   * none. With a solution, branch and bound keeps the time.
   *
   * @param only true to skip the core-guided phase after a solution
   */
  public void setCoresWithoutSolutionOnly(boolean only) {
    coresWithoutSolutionOnly = only;
  }

  /**
   * Sets whether the core-guided phase of {@link #minimize} is skipped after branch and bound when
   * its probe ({@link #setCoreDelay}) stopped without a solution of its own and branch and bound
   * found one. The rest of the phase would stop the same way after a third of its time: on
   * fast-food, gt-sort and city-position it only delayed branch and bound. On by default ({@code
   * -Djacop.lcg.coreProbeSkip}).
   *
   * @param skip true to skip the phase after such a probe
   */
  public void setCoreProbeSkip(boolean skip) {
    coreProbeSkip = skip;
  }

  public void setCoreDelay(double share, long conflicts, double probe) {
    coreDelayShare = share;
    coreDelayBudget = Math.max(1, conflicts);
    coreProbeShare = probe;
  }

  /**
   * Sets the time limit of the run, from which the core-guided phase of {@link #minimize} and the
   * branch and bound before it take their shares as work ({@link CdclSolver#work}, {@link
   * #WORK_PER_MS} per millisecond), so that a run repeats with the same limit whatever the load of
   * the machine. Without it they take shares of the deadline's time left, counted as work at the
   * start of {@link #minimize}, or, without a deadline either, their budgets of conflicts. It does
   * not stop the run: the deadline does.
   *
   * @param millis the time limit in milliseconds, 0 for none
   */
  public void setTimeLimit(long millis) {
    timeLimitMillis = Math.max(0, millis);
  }

  /**
   * Returns the core-guided phase of the last {@link #minimize}, for its statistics.
   *
   * @return the phase, or null when it did not run
   */
  public CoreSearch coreSearch() {
    return coreSearch;
  }

  // ------------------------------------------------- access for the core-guided phase

  CdclSolver solver() {
    return sat;
  }

  /** The conflict limit set before {@link #minimize}, which the core-guided phase keeps. */
  long conflictCap() {
    return conflictCap;
  }

  /** The index of a variable of the store, or -1 when it is not one of the solver's variables. */
  int index(IntVar x) {
    int i = trail.id(x);
    return i >= 0 && i < vars.length && vars[i] == x ? i : -1;
  }

  IntVar variable(int i) {
    return vars[i];
  }

  /** The literal {@code [x >= v]} of variable i, for v in (root min, root max]. */
  int geLiteral(int i, int v) {
    return geLit(i, v);
  }

  /** The literal {@code [x = v]} of variable i, for v in its root domain. */
  int eqLiteral(int i, int v) {
    return eqVar(i, v);
  }

  /** Whether literal lit of variable i's atoms holds when the variable takes value v. */
  boolean holds(int lit, int i, int v) {
    int d = Math.abs(lit);
    if (litVar[d] != i) {
      throw new IllegalArgumentException(lit + " is not an atom of variable " + i);
    }
    boolean atom = litKind[d] == GE_KIND ? v >= litValue[d] : v == litValue[d];
    return atom == lit > 0;
  }

  /** The domain of variable i when the solver was made. */
  IntDomain rootDomain(int i) {
    return root[i];
  }

  /** Probes a literal at the root, see {@link CdclSolver#probe(int)}. */
  int[] probe(int lit) {
    if (rootFailed) {
      return null;
    }
    store.setReturnAfterPruning(!fullFixpoint);
    try {
      return sat.probe(lit);
    } finally {
      store.setReturnAfterPruning(false);
      notifyBacktrack(0);
    }
  }

  int solveUnder(int... assumed) {
    return solve(assumed);
  }

  /** The objective's value in the best solution so far, or {@link Long#MAX_VALUE}. */
  long bestObjective() {
    return best == null ? Long.MAX_VALUE : best[objective];
  }

  /**
   * The objective value that a solution must beat: that of the best solution, here or found
   * elsewhere and given by {@link #setSharedBound}; {@link Long#MAX_VALUE} while there is none.
   */
  long boundObjective() {
    long bound = bestObjective();
    if (sharedBound != null) {
      int localShared = sharedBound.getAsInt();
      if (localShared != Integer.MAX_VALUE) {
        bound = Math.min(bound, localShared);
      }
    }
    return bound;
  }

  /**
   * Alternates branch and bound with objective lower-bound search: runs of branch and bound end
   * after a number of conflicts, and each is followed by a run under the assumption that the
   * objective is at its lower bound, with a share of those conflicts. When that run proves the
   * assumption impossible, the lower bound goes up by a clause; when it finds a solution, the
   * solution is optimal. The budget of conflicts grows by half at each round.
   */
  private int minimizeWithLowerBoundSearch() {
    long budget = lowerBoundBudget;
    double share = lowerBoundShare;
    // before the first solution a run that neither raises the bound nor finds a solution halves the
    // share of the next one, and a raise restores it: the runs take time from the search for a
    // first
    // solution (XCSP3 IHTC-i30 found none in 600 s with the full share, base finds one after 240 s)
    double early = 1;
    while (true) {
      long before = best == null ? Long.MAX_VALUE : best[objective];
      long limit = sat.conflicts + budget;
      sat.setConflictLimit(limit);
      long start = System.nanoTime();
      int result = solve();
      if (result != CdclSolver.UNKNOWN || sat.conflicts < limit) {
        return result; // done, or stopped by the deadline
      }
      if (lns != null && best != null) {
        result = neighbourhoodRuns((long) (lnsShare * (System.nanoTime() - start)));
        if (result != CdclSolver.UNKNOWN || System.nanoTime() > sat.deadline()) {
          return result;
        }
      }
      if (lowerBoundShare > 0) {
        if (shaveGrowth > 1 && best != null) {
          // a round that did not improve the best solution gives the bound more of the next one
          share = best[objective] < before ? lowerBoundShare : Math.min(share * shaveGrowth, 4);
        }
        boolean noSolution = best == null;
        long raisedBefore = lowerBoundRaised;
        result = lowerBoundRun((long) (budget * share * (noSolution ? early : 1)));
        if (result != CdclSolver.UNKNOWN) {
          return result;
        }
        if (noSolution) {
          early = lowerBoundRaised > raisedBefore ? 1 : early / 2;
        }
      }
      budget += budget / 2;
    }
  }

  /**
   * One lower-bound run of {@link #minimizeWithLowerBoundSearch}: assumes the objective at most a
   * target and, when that is impossible, raises its lower bound above the target by a clause. The
   * target is the lower bound itself, or with shaving a step above it; with shaving, the conflicts
   * a proof leaves go to the next, doubled step.
   *
   * @return {@link CdclSolver#UNKNOWN} to go on, or the result of the search when the run proved
   *     the best solution optimal or that there is none
   */
  private int lowerBoundRun(long conflicts) {
    long limit = sat.conflicts + conflicts;
    int raised = Integer.MIN_VALUE; // the bound this call proved, which the root may not show yet
    while (true) {
      // after solve the domains are those of level 0
      int lb = Math.max(vars[objective].min(), raised);
      // before the first solution the run assumes the objective at its lower bound, without
      // shaving: puzzles such as ButtonsScissors have their first solutions only near the optimum
      // and are much easier with the tightest bound (XCSP3 ButtonsScissors-00: 0.2 s with the
      // objective at most 9, the optimum, no solution in 15 s with at most 13)
      if (best == null ? lb >= vars[objective].max() : lb >= best[objective]) {
        return CdclSolver.UNKNOWN;
      }
      // objective <= target: the lower bound itself, or a step above it when shaving
      int target =
          shaving && best != null ? (int) Math.min(lb + shaveStep - 1, best[objective] - 1L) : lb;
      int lit = -geLit(objective, target + 1);
      sat.setConflictLimit(limit);
      lowerBoundRuns++;
      int result = solve(lit);
      if (result == CdclSolver.SAT) {
        return result; // a solution at the smallest value of the objective
      }
      if (result != CdclSolver.UNSAT) {
        if (sat.conflicts < limit) {
          return result; // stopped by the deadline
        }
        if (best != null) {
          shaveStep = Math.max(1, shaveStep / 2);
        }
        return CdclSolver.UNKNOWN;
      }
      if (sat.failedAssumptions().length == 0 || best != null && best[objective] <= target) {
        // no better solution at all; or the run found one within the target and then none
        // better, and every better one would be within the target too
        return result;
      }
      sat.addClause(-lit); // objective >= target + 1
      lowerBoundRaised++;
      raised = target + 1;
      reportBound(target + 1L);
      if (!shaving || best == null) {
        // before the first solution one step per round: a sum objective (XCSP3 Cargo) raised its
        // bound one by one for the whole round and found no solution
        return CdclSolver.UNKNOWN;
      }
      shaveStep = Math.min(2 * shaveStep, 1L << 30);
    }
  }

  /**
   * Dichotomic search on the objective's bound, for a thread of a portfolio that works on the lower
   * bound while others look for solutions: each probe assumes the objective at most a value between
   * its lower bound lb and the best solution ub, here or shared, at first the midpoint. A probe
   * that proves this impossible raises lb above that value by a clause; one that finds solutions
   * lowers ub, and goes on as branch and bound under the assumption. A probe that runs out of
   * conflicts tries a value nearer lb next, at half the distance, as CP-SAT's objective shaving
   * does, and at lb itself the probes get twice the conflicts. A proof moves the next value back
   * towards the midpoint. Once ub - lb is within the gap of |ub|, branch and bound takes over, with
   * its own lower-bound runs.
   *
   * <p>The probe's bound is an assumption, a decision, so every clause learnt under it holds for
   * the model under the bound of branch and bound, as the clauses of branch and bound do, and may
   * be shared; only the clause added after a proof, lb >= value + 1, depends on the probe, and it
   * is implied by the model and ub. Without a solution anywhere, branch and bound runs first, with
   * a growing budget of conflicts, until it or another thread finds one.
   *
   * @return {@link CdclSolver#UNKNOWN} when a limit stopped the search; else the result of the
   *     search as for {@link #solve}: SAT when a solution was found at the smallest value of the
   *     objective, UNSAT when no solution is better than ub
   */
  private int minimizeByBisection() {
    long budget = lowerBoundBudget > 0 ? lowerBoundBudget : 1000;
    long noSolutionBudget = budget;
    // the share of [lb, ub - 1] below the probe's value
    double fraction = 0.5;
    int raised = Integer.MIN_VALUE; // the bound proved here, which the root may not show yet
    while (true) {
      long ub = boundObjective();
      if (ub == Long.MAX_VALUE) {
        // no solution yet: branch and bound until one, here or elsewhere
        long limit = sat.conflicts + noSolutionBudget;
        sat.setConflictLimit(limit);
        int result = solve();
        sat.setConflictLimit(Long.MAX_VALUE);
        if (result != CdclSolver.UNKNOWN || sat.conflicts < limit) {
          return result; // done, or stopped by the deadline
        }
        noSolutionBudget += noSolutionBudget / 2;
        continue;
      }
      // after solve the domains are those of level 0
      long lb = Math.max(vars[objective].min(), raised);
      if (lb >= ub || ub - lb <= bisectGap * Math.abs((double) ub)) {
        // closed, or within the gap: branch and bound from here, which also proves lb >= ub
        return interleaved() ? minimizeWithLowerBoundSearch() : solve();
      }
      long hi = ub - 1; // a better solution has the objective at most hi
      int target = (int) Math.min(hi, lb + (long) Math.floor(fraction * (hi - lb)));
      int lit = -geLit(objective, target + 1);
      long limit = sat.conflicts + budget;
      sat.setConflictLimit(limit);
      bisectProbes++;
      int result = solve(lit);
      sat.setConflictLimit(Long.MAX_VALUE);
      if (result == CdclSolver.SAT) {
        return result; // a solution at the smallest value of the objective
      }
      if (result != CdclSolver.UNSAT) {
        if (sat.conflicts < limit) {
          return result; // stopped by the deadline
        }
        bisectLimits++;
        if (target > lb) {
          fraction /= 2;
        } else {
          budget = Math.min(2 * budget, 1L << 40);
        }
        continue;
      }
      if (sat.failedAssumptions().length == 0 || bestObjective() <= target) {
        // no better solution than ub at all; or the probe found one within its value and then
        // none better, and every better one would be within the value too
        return result;
      }
      addProvedClause(-lit); // objective >= target + 1
      bisectRaised++;
      raised = target + 1;
      reportBound(target + 1L);
      fraction = Math.min(0.5, 2 * fraction);
    }
  }

  /**
   * Turns on dichotomic bound search in {@link #minimize} (see {@link #minimizeByBisection}), in
   * place of the core-guided phase, until the gap between the best solution and the lower bound is
   * at most the given share of the best solution.
   *
   * @param gap the relative gap at which branch and bound takes over; 0 turns it off
   */
  public void setBisection(double gap) {
    bisectGap = Math.max(0, gap);
  }

  /**
   * Runs in large neighbourhoods of the best solution for the given time: each run assumes that the
   * variables outside the neighbourhood keep their values in the best solution and stops after its
   * conflicts. The assumptions are decisions, so what the runs learn holds for every later search.
   *
   * @return {@link CdclSolver#UNKNOWN} to go on, or the result of the search when a run proved that
   *     no better solution exists (UNSAT without failed assumptions, or SAT at the objective's
   *     smallest value)
   */
  private int neighbourhoodRuns(long nanos) {
    long end = Math.min(System.nanoTime() + nanos, sat.deadline());
    while (System.nanoTime() < end) {
      int[] fixed = lns.neighbourhood();
      int[] upper = lns.upperBounded();
      int[] assumed = new int[fixed.length + upper.length];
      int n = 0;
      for (int k : fixed) {
        int i = lnsIds[k];
        int v = lns.value(k);
        if (i >= 0 && !vars[i].singleton() && vars[i].domain.contains(v)) {
          assumed[n++] = eqVar(i, v);
        }
      }
      for (int k : upper) {
        int i = lnsIds[k];
        int v = lns.value(k);
        if (i >= 0 && !vars[i].singleton() && v >= vars[i].min() && v < vars[i].max()) {
          assumed[n++] = -geVar(i, v + 1);
        }
      }
      long before = best[objective];
      sat.setConflictLimit(sat.conflicts + lnsConflicts);
      lnsRuns++;
      int result = solve(Arrays.copyOf(assumed, n));
      boolean improved = best[objective] < before;
      if (improved) {
        lnsImproved++;
      }
      if (result == CdclSolver.SAT
          || (result == CdclSolver.UNSAT && sat.failedAssumptions().length == 0)) {
        return result;
      }
      AdaptiveLns.Outcome outcome;
      if (improved) {
        outcome = AdaptiveLns.Outcome.IMPROVED;
      } else if (result == CdclSolver.UNSAT) {
        outcome = AdaptiveLns.Outcome.EXHAUSTED;
      } else {
        outcome = AdaptiveLns.Outcome.LIMIT;
      }
      lns.outcome(outcome);
    }
    sat.setConflictLimit(Long.MAX_VALUE);
    return CdclSolver.UNKNOWN;
  }

  /**
   * Turns on large neighbourhood search in {@link #minimize}: after each run of branch and bound
   * from the first solution on, runs in neighbourhoods of the best solution take the given share of
   * the time that run took. The neighbourhoods fix their variables by assumptions.
   *
   * @param neighbourhoods the neighbourhoods, over variables of the store; null turns it off
   * @param share the time of neighbourhood runs per unit of time of branch and bound
   * @param conflicts the conflicts of one neighbourhood run
   */
  public void setLns(AdaptiveLns neighbourhoods, double share, long conflicts) {
    lns = neighbourhoods;
    lnsShare = share;
    lnsConflicts = Math.max(1, conflicts);
    if (lns != null) {
      IntVar[] xs = lns.variables();
      lnsIds = new int[xs.length];
      for (int k = 0; k < xs.length; k++) {
        lnsIds[k] = index(xs[k]);
      }
    }
  }

  /**
   * Returns the neighbourhoods of large neighbourhood search, for their statistics.
   *
   * @return the neighbourhoods, or null when it is off
   */
  public AdaptiveLns lns() {
    return lns;
  }

  /**
   * Turns on objective lower-bound search in {@link #minimize}: runs of branch and bound alternate
   * with runs that assume the objective at its lower bound, which take the given share of the
   * conflicts of the runs before them.
   *
   * @param share the conflicts of a lower-bound run per conflict of branch and bound; 0 for none
   * @param firstRun the conflicts of the first run of branch and bound, growing by half each round
   */
  public void setLowerBoundSearch(double share, long firstRun) {
    lowerBoundShare = share;
    lowerBoundBudget = Math.max(1, firstRun);
  }

  /**
   * Turns objective shaving on in the lower-bound runs of {@link #setLowerBoundSearch}: instead of
   * the objective at its lower bound, each run assumes it at most a step above the bound. A run
   * that proves the assumption impossible raises the bound by the whole step and doubles it; a run
   * that runs out of conflicts halves it. The bound then closes on the best solution by large steps
   * when the steps are easy to prove, as CP-SAT's objective shaving does.
   *
   * @param on whether to shave
   */
  public void setShaving(boolean on) {
    shaving = on;
    shaveStep = 1;
  }

  /**
   * Makes the share of conflicts that lower-bound runs get grow by the given factor after each
   * round of branch and bound that did not improve the best solution, up to four times the
   * conflicts of branch and bound; an improving round sets it back.
   *
   * @param growth the factor, 1 for a fixed share
   */
  public void setLowerBoundGrowth(double growth) {
    shaveGrowth = Math.max(1, growth);
  }

  /**
   * Sets the random seed, which changes the initial order of the variables in activity branching
   * and of the literals in the SAT solver's decisions. Set it before solving; 0 keeps the order of
   * the variables.
   *
   * @param seed the seed
   */
  public void setSeed(long seed) {
    sat.setSeed(seed);
    if (seed != 0) {
      SplittableRandom random = new SplittableRandom(seed);
      for (int i = 0; i < activity.length; i++) {
        activity[i] = random.nextDouble() * 1e-3;
      }
      rebuildHeap(heap);
      rebuildHeap(wide);
      rebuildHeap(lateHeap);
    }
  }

  /**
   * Makes a run of {@link Branching#ALTERNATE} that improved the best solution keep its turn at the
   * next restart, instead of passing it to the next way of branching.
   *
   * @param keep whether an improving run keeps its turn
   */
  public void setKeepImprovingRun(boolean keep) {
    keepImprovingRun = keep;
  }

  /**
   * Sets how decisions are made outside the runs of the annotation. Set it before solving.
   *
   * @param branching the branching
   */
  public void setBranching(Branching branching) {
    this.branching = branching;
    activityBranching = branching == Branching.ACTIVITY;
  }

  /**
   * Sets whether the store runs to its fixpoint before the clauses propagate again (the default),
   * or returns to the clauses after each pruning constraint. Set it before solving.
   *
   * @param fullFixpoint true for the store's fixpoint
   */
  public void setFullFixpoint(boolean fullFixpoint) {
    this.fullFixpoint = fullFixpoint;
  }

  /**
   * Returns whether the store runs to its fixpoint before the clauses propagate again.
   *
   * @return see {@link #setFullFixpoint}
   */
  public boolean fullFixpoint() {
    return fullFixpoint;
  }

  /**
   * Sets whether activity branching decides the 0/1 variables first, before any other variable is
   * decided, as CP-SAT's default search does, or takes all variables in one order of activity. The
   * default is the first, unless the system property {@code jacop.lcg.booleansFirst} is false. Set
   * it before solving.
   *
   * @param booleansFirst true for the 0/1 variables first
   */
  public void setBooleansFirst(boolean booleansFirst) {
    if (booleansFirst == split) {
      return;
    }
    split = booleansFirst;
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] != null && !late[i] && (heap.contains(i) || wide.contains(i))) {
        (heap.contains(i) ? heap : wide).remove(i);
        heapOf(i).insert(i);
      }
    }
  }

  /**
   * Sets whether the runs of activity branching take turns at restarts with and without the 0/1
   * variables first (see {@link #setBooleansFirst}), starting with the current setting. Neither
   * order is better on most models, and the one that is differs between models of one kind. Set it
   * before solving.
   *
   * @param turns true for turns
   */
  public void setBooleansFirstTurns(boolean turns) {
    booleansFirstTurns = turns;
  }

  /**
   * Returns whether activity branching decides the 0/1 variables first.
   *
   * @return true for the 0/1 variables first
   */
  public boolean booleansFirst() {
    return split;
  }

  /**
   * Sets the model's search annotation as the branching. Under fixed search every run follows it;
   * under free search the runs alternate between it and the activity of the variables, starting
   * with it. When it has fixed all its variables, the activity completes the assignment.
   *
   * @param select the annotation's variable and value selection, or null for none
   * @param free true for free search
   */
  public void setAnnotation(SelectChoicePoint<? extends Var> select, boolean free) {
    annotation = select;
    freeSearch = free;
    annotationRun = select != null;
    if (annotationRun && branching == Branching.ALTERNATE) {
      activityBranching = true;
    }
  }

  /**
   * Sets a selection that starts the runs of activity branching under fixed search with restarts
   * (see {@link #setFixedRestarts}): its decisions come first in those runs, and activity branching
   * takes over when it gives none. A selection that follows the solution of the linear relaxation
   * gives those runs the relaxation's values, which the model's annotation may not find (the
   * annotation of concert-hall-cap rejects every offer first). Set it before solving.
   *
   * @param select the selection, or null for none
   */
  public void setActivityGuide(SelectChoicePoint<? extends Var> select) {
    activityGuide = select;
  }

  /**
   * Sets restarts under fixed search (an annotation set with free false). Without them the solver
   * never restarts, so its learnt clauses prune but never reorder the search. With them the solver
   * restarts on its own schedule; each run follows the annotation (REPLAY) or the runs take turns
   * between the annotation and activity branching (ALTERNATE). In every run activity branching
   * completes the assignment once the annotation has fixed its variables. Set it before solving.
   *
   * @param mode how runs branch, or OFF for no restarts
   * @param afterSolution true to restart only once a first solution is found
   */
  public void setFixedRestarts(FixedRestarts mode, boolean afterSolution) {
    fixedRestarts = mode;
    restartsAfterSolution = mode != FixedRestarts.OFF && afterSolution;
    sat.setRestarts(mode != FixedRestarts.OFF && !afterSolution);
  }

  /**
   * Adds a clause over 0/1 variables: one of the positive variables is 1 or one of the negative
   * ones is 0. It goes to the SAT solver as a clause of {@code [x >= 1]} literals, so it is
   * propagated and explained by the solver itself. Add clauses before solving.
   *
   * @param positive variables of which one may be 1
   * @param negative variables of which one may be 0
   */
  public void addClause(IntVar[] positive, IntVar[] negative) {
    if (proof != null) {
      proofClauses.add(new IntVar[][] {positive.clone(), negative.clone()});
    }
    List<Integer> clause = new ArrayList<>();
    for (int sign = 1; sign >= -1; sign -= 2) {
      for (IntVar x : sign > 0 ? positive : negative) {
        int i = trail.id(x);
        if (root[i].min() < 0 || root[i].max() > 1) {
          throw new IllegalArgumentException(x + " is not a 0/1 variable");
        }
        if (root[i].singleton()) {
          if (root[i].min() == (sign > 0 ? 1 : 0)) {
            return; // satisfied at the root
          }
          continue; // false at the root
        }
        clause.add(sign * geLit(i, 1));
      }
    }
    if (clause.isEmpty() || !sat.addClause(clause.stream().mapToInt(Integer::intValue).toArray())) {
      rootFailed = true;
      clauseFailedAtRoot = true;
    }
  }

  /**
   * Whether layered-graph constraints (regular, mdd) become clauses of the solver in place of their
   * propagation and explanations by cuts of the graph; the system property {@code
   * jacop.lcg.graphClauses} turns it off.
   */
  private static final boolean GRAPH_CLAUSES =
      Boolean.parseBoolean(System.getProperty("jacop.lcg.graphClauses", "true"));

  private boolean graphClauses = GRAPH_CLAUSES;

  /** Whether {@link #encodeGraphs} ran. */
  private boolean graphsEncoded;

  /** The layered-graph constraints {@link #encodeGraphs} removed from the store. */
  private final List<LayeredGraphConstraint> encodedGraphs = new ArrayList<>();

  /**
   * Sets whether layered-graph constraints (regular, mdd) become clauses of the solver, before it
   * starts; on by default.
   *
   * @param on true for clauses, false to propagate and explain the constraints themselves
   */
  public void setGraphClauses(boolean on) {
    graphClauses = on;
  }

  /** Statistics: layered-graph constraints given to the solver as clauses. */
  public long graphConstraintsEncoded;

  /** Statistics: clauses implied by constraints ({@link ImpliedClauses}) given to the solver. */
  public long impliedClauses;

  /**
   * Gives the solver every layered-graph constraint of the store as clauses ({@link
   * LayeredGraphConstraint#encodeClauses}) and removes the constraint from the store. Unit
   * propagation over the clauses is domain consistent, as the constraint is, and explains itself:
   * explaining by cuts of the graph made the conflicts of regular-heavy models slow and their
   * clauses long. Constraints with {@link ImpliedClauses} add theirs here too and stay in the
   * store. Neither under a proof, whose model has no auxiliary variables and no implied clauses.
   */
  private void encodeGraphs() {
    if (graphsEncoded) {
      return;
    }
    graphsEncoded = true;
    if (proof != null || rootFailed) {
      return;
    }
    ClauseModel model =
        new ClauseModel() {
          @Override
          public int newLiteral() {
            return newAuxiliary();
          }

          @Override
          public int valueLiteral(IntVar x, int v) {
            return eqVar(trail.id(x), v);
          }

          @Override
          public void clause(int[] literals, int size) {
            if (!rootFailed && !sat.addClause(Arrays.copyOf(literals, size))) {
              rootFailed = true;
              clauseFailedAtRoot = true;
            }
          }
        };
    boolean propagatorLeft = false;
    objectiveTerms = objectiveTerms();
    for (Constraint c : store.getConstraints()) {
      if (graphClauses && c instanceof LayeredGraphConstraint g && g.encodeClauses(model)) {
        g.removeConstraint();
        encodedGraphs.add(g);
        graphConstraintsEncoded++;
      } else if ((clauseCandidate(c) || permutationCandidate(c)) && encodeAsClauses(c)) {
        constraintsAsClauses++;
        if (c instanceof Alldistinct) {
          permutationsAsClauses++;
        }
      } else {
        propagatorLeft = true;
        if (c instanceof ImpliedClauses i && !rootFailed) {
          impliedClauses += i.impliedClauses(model);
        }
      }
    }
    if (PURE_CLAUSE_LITERALS
        && freeSearch
        && branching == Branching.ALTERNATE
        && annotation != null
        && !propagatorLeft
        && allBinary()) {
      // every constraint became clauses and every variable is 0/1: the model is a CNF, and the
      // turns of the annotation (or dom/wdeg) and of activity branching only make slower SAT
      // decisions. Nonograms at 600 s, two seeds: 2026 hard_03 53-56 s instead of 388 s and
      // unsolved, 2013 dom_14 4-22 s instead of 79-129 s; 19 of 58 runs faster, 1 slower. Not with
      // wider domains: pentominoes, whose regular constraints become clauses too, lost up to 4x
      branching = Branching.LITERALS;
      annotation = null;
      annotationRun = false;
      activityBranching = false;
      pureClauses = true;
    }
  }

  /**
   * The classes of small constraints that become clauses of the solver in place of their
   * propagators ({@link ClauseEncoder}): a comma-separated list of simple class names, "all" or
   * "none", by the system property {@code jacop.lcg.clauses}.
   */
  static final String CLAUSE_CLASSES = System.getProperty("jacop.lcg.clauses", "none");

  /** The most clauses one constraint may become, {@code jacop.lcg.clauses.limit}. */
  static final int CLAUSE_LIMIT = Integer.getInteger("jacop.lcg.clauses.limit", 256);

  /** The most values a variable of such a constraint may have, {@code jacop.lcg.clauses.dom}. */
  static final int CLAUSE_DOM = Integer.getInteger("jacop.lcg.clauses.dom", 64);

  /** Prints each constraint tried as clauses, {@code jacop.lcg.clauses.debug}. */
  static final boolean CLAUSE_DEBUG = Boolean.getBoolean("jacop.lcg.clauses.debug");

  /**
   * The most clauses of a sum of 0/1 variables (with at most one other variable) outside a
   * reification, which becomes a unary counter, {@code jacop.lcg.clauses.counter}.
   */
  static final int CLAUSE_COUNTER = Integer.getInteger("jacop.lcg.clauses.counter", 20000);

  /** The most unfixed 0/1 variables of such a sum, {@code jacop.lcg.clauses.boolArity}. */
  static final int CLAUSE_BOOL_ARITY = Integer.getInteger("jacop.lcg.clauses.boolArity", 256);

  private static final java.util.Set<String> CLAUSE_SET =
      new java.util.HashSet<>(Arrays.asList(CLAUSE_CLASSES.split(",")));

  /** Statistics: constraints given to the solver as clauses by {@link ClauseEncoder}. */
  public long constraintsAsClauses;

  /** Statistics: clauses of those constraints. */
  public long constraintClauses;

  /** The constraints removed from the store as clauses, put back by {@link #release}. */
  private final List<Constraint> encodedConstraints = new ArrayList<>();

  private ClauseEncoder clauseEncoder;

  /** The classes "counter" in {@code jacop.lcg.clauses} gives to the unary counter alone. */
  private static final java.util.Set<String> COUNTER_CLASSES =
      java.util.Set.of(
          "LinearInt",
          "SumBool",
          "LinearBool",
          "SumInt",
          "Count",
          "CountBounds",
          "AtMost",
          "AtLeast");

  private boolean counterOnly(Constraint c) {
    String name = c.getClass().getSimpleName();
    return CLAUSE_SET.contains("counter")
        && COUNTER_CLASSES.contains(name)
        && !"all".equals(CLAUSE_CLASSES)
        && !CLAUSE_SET.contains(name);
  }

  /**
   * The variables of the objective's definition (the objective and the terms of a linear form over
   * it), or an empty set. A constraint over them stays a propagator: the core-guided phase and the
   * LP read the definitions of the objective's terms from the store, such as {@code b <=> x = c} of
   * a term b (spot5 28 loses its at-most-one groups and its proof when they are clauses).
   */
  private java.util.Set<IntVar> objectiveTerms() {
    java.util.Set<IntVar> terms = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
    if (clauseObjective == null || "none".equals(CLAUSE_CLASSES)) {
      return terms;
    }
    terms.add(clauseObjective);
    List<LinearForm> forms = new ArrayList<>();
    for (Constraint c : store.getConstraints()) {
      LinearForm f = LinearForms.of(c);
      if (f != null && f.relation() == LinearForm.EQ) {
        forms.add(f);
      }
    }
    // the objective's sum, then the definitions of its terms that are defined once more (blocks
    // of a split sum, y = b of bool2int), as the core phase follows them
    Map<IntVar, Integer> occurs = new IdentityHashMap<>();
    for (LinearForm f : forms) {
      for (IntVar x : f.vars()) {
        occurs.merge(x, 1, Integer::sum);
      }
    }
    java.util.Set<IntVar> last = java.util.Set.of(clauseObjective);
    for (int round = 0; !last.isEmpty() && round < 4; round++) {
      java.util.Set<IntVar> added = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
      for (LinearForm f : forms) {
        boolean follow = false;
        for (IntVar x : f.vars()) {
          follow |= last.contains(x) && (round == 0 || occurs.get(x) <= 2);
        }
        if (follow) {
          for (IntVar x : f.vars()) {
            if (terms.add(x)) {
              added.add(x);
            }
          }
        }
      }
      last = added;
    }
    return terms;
  }

  private java.util.Set<IntVar> objectiveTerms = java.util.Set.of();

  /** The objective of {@link #minimize}, known when its terms are left out of the clauses. */
  private IntVar clauseObjective;

  /**
   * Whether permutations become clauses, the system property {@code jacop.lcg.alldiffClauses} (true
   * by default).
   */
  static final boolean ALLDIFF_CLAUSES =
      Boolean.parseBoolean(System.getProperty("jacop.lcg.alldiffClauses", "true"));

  /** Statistics: all different constraints over permutations given to the solver as clauses. */
  public long permutationsAsClauses;

  /**
   * Whether a domain consistent all different constraint is a permutation, as many variables as
   * values, with few enough clauses ({@link ClauseEncoder#ALLDIFF_LIMIT}) to become clauses in
   * place of its propagator, as CP-SAT expands a permutation into exactly-one constraints over the
   * literals [x = v] (Lynce and Ouaknine, "Sudoku as a SAT problem", ISAIM 2006, the extended
   * encoding). Unit propagation over them finds the values each variable must take and the
   * variables each value must go to, though not the larger Hall sets the propagator finds; each
   * step is a clause of the solver, with no explanation to build. On the 25x25 sudokus of Gecode's
   * examples, under their fixed search, the solver makes about twice as many conflicts a second and
   * searches trees of about the same size.
   */
  private boolean permutationCandidate(Constraint c) {
    if (!ALLDIFF_CLAUSES || c.getClass() != Alldistinct.class) {
      return false;
    }
    java.util.Set<Var> list = c.arguments();
    IntervalDomain union = new IntervalDomain();
    for (Var v : list) {
      IntVar x = (IntVar) v;
      if (x == clauseObjective || objectiveTerms.contains(x)) {
        return false;
      }
      if (!x.singleton() && (trail.id(x) < 0 || trail.id(x) >= vars.length)) {
        return false;
      }
      union = (IntervalDomain) union.union(x.dom());
      if (union.getSize() > list.size()) {
        return false;
      }
    }
    return union.getSize() == list.size();
  }

  private boolean clauseCandidate(Constraint c) {
    if ("none".equals(CLAUSE_CLASSES)
        || !("all".equals(CLAUSE_CLASSES)
            || CLAUSE_SET.contains(c.getClass().getSimpleName())
            || counterOnly(c))) {
      return false;
    }
    int arity = 0;
    int wide = 0;
    for (org.jacop.core.Var v : c.arguments()) {
      if (!(v instanceof IntVar x) || objectiveTerms.contains(x)) {
        return false;
      }
      if (!x.singleton()) {
        arity++;
        if (trail.id(x) >= vars.length || x.getSize() > CLAUSE_BOOL_ARITY + 1) {
          return false;
        }
        if (x.getSize() > CLAUSE_DOM) {
          wide++;
        }
      }
    }
    // one variable wider than the limit, such as the count of a counter; the encoder's own limits
    // decide the rest
    return wide <= 1 && arity <= CLAUSE_BOOL_ARITY && (wide == 0 || arity > 2);
  }

  private boolean encodeAsClauses(Constraint c) {
    if (clauseEncoder == null) {
      clauseEncoder =
          new ClauseEncoder(
              new ClauseEncoder.Literals() {
                @Override
                public int atLeast(IntVar x, int v) {
                  return geLit(trail.id(x), v);
                }

                @Override
                public int valueLiteral(IntVar x, int v) {
                  return eqVar(trail.id(x), v);
                }

                @Override
                public int auxiliary() {
                  return newAuxiliary();
                }

                @Override
                public IntDomain root(IntVar x) {
                  return x.dom();
                }
              },
              CLAUSE_LIMIT,
              CLAUSE_COUNTER);
    }
    List<int[]> cs = clauseEncoder.encode(c, counterOnly(c));
    if (CLAUSE_DEBUG) {
      String s = c.toString();
      System.out.println(
          "% clauses "
              + (cs == null ? "rejected " : cs.size() + " ")
              + (s.length() > 300 ? s.substring(0, 300) : s));
    }
    if (cs == null) {
      return false;
    }
    for (int[] cl : cs) {
      constraintClauses++;
      if (!rootFailed && !sat.addClause(cl)) {
        rootFailed = true;
        clauseFailedAtRoot = true;
      }
    }
    c.removeConstraint();
    encodedConstraints.add(c);
    return true;
  }

  /** Whether every variable of the model has at most two values, so that it is a 0/1 CNF. */
  private boolean allBinary() {
    for (IntVar x : vars) {
      if (x != null && x.getSize() > 2) {
        return false;
      }
    }
    return true;
  }

  /**
   * Whether a free search whose model is clauses only, with no constraint left in the store once
   * {@link #encodeGraphs} has run, leaves all decisions to the SAT solver (as {@link
   * Branching#LITERALS}). On by default; the system property {@code jacop.lcg.pureClauseLiterals}
   * set to false turns it off.
   */
  static final boolean PURE_CLAUSE_LITERALS =
      Boolean.parseBoolean(System.getProperty("jacop.lcg.pureClauseLiterals", "true"));

  /** Whether the model became clauses only and its search was left to the SAT solver. */
  public boolean pureClauses;

  /**
   * Turns the explanation checker on or off: every explanation is then derived again in a scratch
   * store, and a wrong one stops the solver with an {@link IllegalStateException}. The system
   * property {@code jacop.lcg.check=true} turns it on for every solver.
   *
   * @param on true to check explanations
   */
  public void setChecking(boolean on) {
    checker = on ? new ExplanationChecker(trail) : null;
  }

  /**
   * Returns the explanation checker, for its statistics.
   *
   * @return the checker, or null when checking is off
   */
  public ExplanationChecker checker() {
    return checker;
  }

  /**
   * Sets an action run at every solution while the store's domains are fixed to it, for example to
   * print the solution.
   *
   * @param action the action, or null for none
   */
  public void onSolution(Runnable action) {
    onSolution = action;
  }

  /**
   * Sets the action that takes the bound of the objective that {@link #minimize} has proved: no
   * solution better than the best one has a smaller value of the objective. It is called whenever
   * the search leaves the root with a better bound than before, after the root's propagation, so a
   * search without restarts reports the bounds that backjumps to the root prove. It may call {@link
   * #stop}.
   *
   * @param action the action, given the objective's smallest value at the root
   */
  public void onBound(LongConsumer action) {
    onBound = action;
  }

  /**
   * Gives a bound of the objective proved at the root, under the bound of branch and bound, to the
   * action of {@link #onBound} when it is larger than the last one given: by a restart, a
   * lower-bound run or a core of the core-guided phase.
   */
  void reportBound(long lower) {
    if (onBound != null && objective >= 0 && lower > lastBound) {
      lastBound = lower;
      onBound.accept(lower);
    }
  }

  /**
   * Returns the value of a variable in the last solution.
   *
   * @param x a variable of the store
   * @return its value
   */
  public int value(IntVar x) {
    if (solution == null) {
      throw new IllegalStateException("no solution");
    }
    return solution[trail.id(x)];
  }

  // ------------------------------------------------------------------ the external propagator

  @Override
  public void notifyLearntLiteral(int lit) {
    int dimacsVar = Math.abs(lit);
    if (litVar[dimacsVar] < 0) {
      return; // not an atom
    }
    if (branching != Branching.LITERALS) {
      bump(litVar[dimacsVar]);
    }
    if (dimacsVar < atomUse.length && atomUse[dimacsVar] == 1) {
      atomUse[dimacsVar] = 2;
      atomLiteralsLearnt++;
    }
    keep(lit);
  }

  @Override
  public void notifyAnalysedLiteral(int var) {
    if (var < litVar.length && litVar[var] >= 0 && branching != Branching.LITERALS) {
      int i = litVar[var];
      if (bumpedAt[i] != sat.conflicts) {
        bump(i); // each integer variable once per conflict, learnt ones not again
      }
    }
  }

  @Override
  public void notifyKeptLiteral(int lit) {
    keep(lit);
  }

  @Override
  public void notifyAssignment(int lit, boolean fixed) {
    if (numPending == pending.length) {
      pending = Arrays.copyOf(pending, 2 * numPending);
    }
    pending[numPending++] = lit;
  }

  @Override
  public void notifyNewDecisionLevel() {
    if (onBound != null && objective >= 0 && store.level == baseLevel) {
      rootBound();
    }
    store.setLevel(store.level + 1);
  }

  /**
   * Passes on the objective's bound at the root, at a fixpoint, when it is better than the last one
   * passed: the root holds the bound of branch and bound, so the objective's minimum there holds
   * for every solution better than the best one, and so does the bound of the core-guided phase.
   */
  private void rootBound() {
    long lower = vars[objective].min();
    if (coreSearch != null) {
      lower = Math.max(lower, coreSearch.lowerBound);
    }
    reportBound(lower);
  }

  // the values of the fixed variables when the SAT trail before the last decision is the longest
  // since the last restart
  private void saveTarget() {
    int level = sat.decisionLevel();
    if (level == 0) {
      return;
    }
    int assigned = sat.trailSize();
    if (assigned <= targetTrail) {
      return;
    }
    targetTrail = assigned;
    if (targetValue == null) {
      targetValue = new int[vars.length];
      targetSet = new boolean[vars.length];
    }
    targetSnapshots++;
    for (int i = 0; i < targetValue.length; i++) {
      IntVar x = vars[i];
      if (x != null && x.singleton()) {
        targetValue[i] = x.value();
        targetSet[i] = true;
      }
    }
  }

  @Override
  public void notifyBacktrack(int level) {
    if (sat.conflicts != backtrackConflicts) {
      // a conflict led here: its last decision was on decisionVar
      backtrackConflicts = sat.conflicts;
      conflictVar = decisionVar;
      if (phase == null
          && activityBranching
          && (TARGET_PHASE == null ? freeSearch : Boolean.parseBoolean(TARGET_PHASE))) {
        saveTarget();
      }
    }
    trail.beginBacktrack();
    try {
      while (store.level > baseLevel + level) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }
    } finally {
      trail.endBacktrack();
    }
    // a variable fixed at the decision level it was taken off at, or below, may be free again
    while (numPopped > 0 && poppedLevel[numPopped - 1] > level) {
      int v = popped[--numPopped];
      heapOf(v).insert(v);
    }
    while (numAnnotationIndices > 0 && annotationLevel[numAnnotationIndices - 1] > level) {
      numAnnotationIndices--;
    }
    while (numLastLevels > 0 && lastLevel[numLastLevels - 1] > level) {
      lastSize = lastLevelSize[--numLastLevels];
    }
    // a notified literal at or below the level stays assigned, and the solver does not notify it
    // again: it is applied at the next propagation (the root's, when a probe stopped at the
    // deadline)
    int kept = 0;
    for (int k = 0; k < numPending; k++) {
      int lit = pending[k];
      if (sat.value(lit) != 0 && sat.levelOf(lit) <= level) {
        pending[kept++] = lit;
      }
    }
    numPending = kept;
    failed = false;
    pushed = Math.min(pushed, trail.size());
    numImplied = 0;
    release(level);
    if (linear != null) {
      imposeLearntLinear(level);
    }
  }

  private void learnLinear(LinearForm f) {
    // a learnt sum is a cutting-plane derivation, which a proof of rup steps cannot state
    if (f == null
        || !"learn".equals(linearMode)
        || proof != null
        || learntSeen.size() >= linearLimit) {
      return;
    }
    // the sum of the terms' largest magnitudes must fit in a long, with room
    double largest = Math.abs((double) f.c());
    for (int k = 0; k < f.vars().length; k++) {
      IntDomain d = root[trail.id(f.vars()[k])];
      largest += Math.abs((double) f.weights()[k]) * Math.max(Math.abs(d.min()), Math.abs(d.max()));
    }
    if (largest > 0x1p61 || !learntSeen.add(f)) {
      return;
    }
    learntLinear.add(f);
  }

  // per solver literal (at 2 * var, + 1 when negative): the linear constraint that last explained
  // it, whose explanation the solver may keep as a clause
  private Constraint[] keptOrigin = new Constraint[0];

  private void noteOrigin(int lit, Constraint c) {
    int key = 2 * Math.abs(lit) + (lit < 0 ? 1 : 0);
    if (key >= keptOrigin.length) {
      keptOrigin = Arrays.copyOf(keptOrigin, Math.max(key + 1, 2 * keptOrigin.length));
    }
    keptOrigin[key] = c;
  }

  private Constraint linearOrigin(int entry) {
    int lit = entry < cause.length ? cause[entry] : 0;
    if (lit == 0) {
      return null;
    }
    int key = 2 * Math.abs(lit) + (lit < 0 ? 1 : 0);
    return key < keptOrigin.length ? keptOrigin[key] : null;
  }

  /** The learnt linear sums so far, imposed or not, for tests. */
  Set<LinearForm> learntLinear() {
    return learntSeen;
  }

  // the learnt sums imposed, with the decision level of each, in order of levels: a constraint
  // imposed above the root leaves its variables when the store backtracks below that level
  private final List<LinearForm> liveLinear = new ArrayList<>();
  private int[] liveLevel = new int[16];

  // after backtracking to a level: the learnt sums imposed above it, and the new ones, are imposed
  // at it; at the root they stay for good. They hold in every solution of the model
  private void imposeLearntLinear(int level) {
    while (!liveLinear.isEmpty() && liveLevel[liveLinear.size() - 1] > level) {
      learntLinear.add(liveLinear.remove(liveLinear.size() - 1));
    }
    for (LinearForm f : learntLinear) {
      store.impose(new LearntLinear(f));
      if (liveLinear.size() == liveLevel.length) {
        liveLevel = Arrays.copyOf(liveLevel, 2 * liveLevel.length);
      }
      liveLevel[liveLinear.size()] = level;
      liveLinear.add(f);
      linearImposed++;
    }
    learntLinear.clear();
  }

  /**
   * Returns the counts of the cut-based conflict analysis (system property {@code
   * jacop.lcg.linear}), by outcome; empty when it is off.
   *
   * @return the counts
   */
  public Map<String, Long> linearStatistics() {
    if (linear == null) {
      return Map.of();
    }
    Map<String, Long> m = new TreeMap<>(linear.outcomes);
    m.put("learntTerms", linear.learntTerms);
    m.put("learntSteps", linear.learntSteps);
    m.put("imposed", linearImposed);
    return m;
  }

  // re-presolve at restarts, see setRestartPresolve
  private double restartPresolve;
  private int restartPresolveVariables = -1;
  private int rootAtPresolve;

  /** The restarts at which the root was presolved again. */
  public long represolves;

  /** The constraints that presolving at restarts found satisfied at the root and left out. */
  public long represolveEntailed;

  /**
   * Presolves the root again at a restart once the root literals learnt since the last time number
   * at least a share of the integer variables, as SCIP restarts its root when presolving/restartfac
   * (2.5%) of the variables got fixed. The re-presolve leaves out the constraints the root domains
   * satisfy: they can no longer prune in any branch, but they were still woken and propagated. Off
   * (0) by default.
   *
   * @param factor the share of the integer variables, 0 for no re-presolve.
   */
  public void setRestartPresolve(double factor) {
    this.restartPresolve = factor;
  }

  private void presolveAtRestart() {
    if (restartPresolveVariables < 0) {
      restartPresolveVariables = 0;
      for (int i = 0; i < store.size(); i++) {
        if (store.vars[i] instanceof IntVar) {
          restartPresolveVariables++;
        }
      }
    }
    int localRoot = sat.rootAssignments();
    if (localRoot - rootAtPresolve < restartPresolve * Math.max(1, restartPresolveVariables)) {
      return;
    }
    rootAtPresolve = localRoot;
    represolves++;
    Set<Constraint> constraints = Collections.newSetFromMap(new IdentityHashMap<>());
    for (int i = 0; i < store.size(); i++) {
      constraints.addAll(store.vars[i].dom().constraints());
    }
    for (Constraint c : constraints) {
      // at the root level of the search, which it does not backtrack below
      if (!c.isEntailed() && c instanceof SatisfiedPresent p && p.satisfied()) {
        store.markEntailed(c);
        represolveEntailed++;
      }
    }
  }

  @Override
  public void notifyRestart() {
    // a restart under assumptions keeps their level, whose bounds hold only under them
    if (store.level == baseLevel) {
      deleteLpSteps();
      if (onBound != null && objective >= 0) {
        rootBound();
      }
      if (restartPresolve > 0) {
        presolveAtRestart();
      }
      exchangeShared();
    }
    targetTrail = 0;
    boolean improved = improvedInRun;
    improvedInRun = false;
    if (keepImprovingRun && improved) {
      return; // the run that improved the best solution goes on in the same way
    }
    if (branching == Branching.ALTERNATE && annotation != null && freeSearch) {
      // the annotation, the literals and the activity in turn, with the activity completing the
      // annotation's runs
      runs++;
      annotationRun = runs % 3 == 0;
      activityBranching = runs % 3 != 1;
    } else if (branching == Branching.ALTERNATE) {
      activityBranching = !activityBranching;
    } else if (annotation != null && freeSearch) {
      annotationRun = !annotationRun;
    } else if (annotation != null && fixedRestarts == FixedRestarts.ALTERNATE) {
      annotationRun = !annotationRun;
    } else if (annotation != null && fixedRestarts == FixedRestarts.TURNS) {
      runs++;
      annotationRun = runs % 3 == 0;
      activityBranching = runs % 3 != 1;
    }
    if (booleansFirstTurns && activityBranching) {
      setBooleansFirst(!split);
    }
  }

  /**
   * Semantic minimisation (Feydy, Schutt and Stuckey 2013): a learnt literal whose set of values of
   * its variable is inside the set of another learnt literal on the same variable implies that
   * literal, so the clause holds without it; for example {@code [x <= 2]} next to {@code [x <= 4]},
   * or {@code [x = 3]} next to {@code [x != 5]}.
   */
  @Override
  public int minimizeLearnt(int[] clause, int size) {
    if (!semantic) {
      return size;
    }
    if (minimizeKeys.length < size) {
      minimizeKeys = new long[2 * size];
      minimizeRemoved = new boolean[2 * size];
    }
    for (int k = 0; k < size; k++) {
      minimizeKeys[k] = (long) litVar[Math.abs(clause[k])] << 32 | k;
      minimizeRemoved[k] = false;
    }
    Arrays.sort(minimizeKeys, 0, size);
    int removed = 0;
    for (int from = 0, to; from < size; from = to) {
      long aVar = minimizeKeys[from] >>> 32;
      to = from + 1;
      while (to < size && minimizeKeys[to] >>> 32 == aVar) {
        to++;
      }
      if (to - from > 16 && aVar <= Integer.MAX_VALUE) {
        removed += minimizeGroup(clause, from, to);
        continue;
      }
      for (int a = from; a < to; a++) {
        int i = (int) minimizeKeys[a];
        if (i == 0 || litVar[Math.abs(clause[i])] < 0) {
          continue; // the asserting literal stays, and so do literals that are not atoms
        }
        for (int b = from; b < to; b++) {
          int j = (int) minimizeKeys[b];
          if (j != i && !minimizeRemoved[j] && implies(clause[i], clause[j])) {
            minimizeRemoved[i] = true;
            removed++;
            break;
          }
        }
      }
    }
    if (removed == 0) {
      return size;
    }
    int kept = 0;
    for (int k = 0; k < size; k++) {
      if (!minimizeRemoved[k]) {
        clause[kept++] = clause[k];
      }
    }
    return kept;
  }

  /**
   * Semantic minimisation of the literals of one variable, keys {@code from} to {@code to}, in
   * linear time for long groups: of the {@code [x >= v]} literals only the weakest can stay, and so
   * of the {@code [x < v]} ones, while an {@code [x = v]} literal goes when it implies another
   * literal of the group. Returns the number of literals removed.
   */
  private int minimizeGroup(int[] clause, int from, int to) {
    int lo = -1; // the [x >= v] literal with the smallest v
    int hi = -1; // the [x < v] literal with the largest v
    int holeMin = Integer.MAX_VALUE;
    int holeMax = Integer.MIN_VALUE;
    int holes = 0;
    for (int a = from; a < to; a++) {
      int i = (int) minimizeKeys[a];
      int l = clause[i];
      int d = Math.abs(l);
      if (litKind[d] == GE_KIND) {
        if (l > 0 && (lo < 0 || litValue[d] < litValue[Math.abs(clause[lo])])) {
          lo = i;
        } else if (l < 0 && (hi < 0 || litValue[d] > litValue[Math.abs(clause[hi])])) {
          hi = i;
        }
      } else if (l < 0) {
        holes++;
        holeMin = Math.min(holeMin, litValue[d]);
        holeMax = Math.max(holeMax, litValue[d]);
      }
    }
    // the weakest bounds go when they imply a hole: [x >= v] that x != w for w < v
    if (lo > 0 && holeMin < litValue[Math.abs(clause[lo])]) {
      minimizeRemoved[lo] = true;
    }
    if (hi > 0 && holeMax >= litValue[Math.abs(clause[hi])]) {
      minimizeRemoved[hi] = true;
    }
    int removed = (lo > 0 && minimizeRemoved[lo] ? 1 : 0) + (hi > 0 && minimizeRemoved[hi] ? 1 : 0);
    for (int a = from; a < to; a++) {
      int i = (int) minimizeKeys[a];
      if (i == 0 || i == lo || i == hi) {
        continue;
      }
      int l = clause[i];
      int d = Math.abs(l);
      boolean drop;
      if (litKind[d] == GE_KIND) {
        // implies the weakest bound of its side, or the hole the weakest one implies
        drop = true;
      } else if (l > 0) {
        long v = litValue[d];
        // x = v implies the weakest bound of a side it is on, or a hole at another value
        drop =
            lo >= 0 && v >= litValue[Math.abs(clause[lo])]
                || hi >= 0 && v < litValue[Math.abs(clause[hi])]
                || holes > 1
                || holes == 1 && holeMin != v;
      } else {
        drop = false; // x != v implies nothing else
      }
      if (drop) {
        minimizeRemoved[i] = true;
        removed++;
      }
    }
    return removed;
  }

  // whether literal a implies literal b, both on the same variable, by their sets of values
  private boolean implies(int a, int b) {
    int va = Math.abs(a);
    int vb = Math.abs(b);
    boolean aEq = litKind[va] == EQ_KIND;
    boolean bEq = litKind[vb] == EQ_KIND;
    if (aEq && a < 0) {
      return false; // x != v implies no other atom's literal on x
    }
    long aLo = a > 0 ? litValue[va] : Long.MIN_VALUE;
    long aHi = aEq || a < 0 ? litValue[va] - (aEq ? 0L : 1L) : Long.MAX_VALUE;
    if (bEq && b < 0) {
      return litValue[vb] < aLo || litValue[vb] > aHi;
    }
    long bLo = b > 0 ? litValue[vb] : Long.MIN_VALUE;
    long bHi = bEq || b < 0 ? litValue[vb] - (bEq ? 0L : 1L) : Long.MAX_VALUE;
    return bLo <= aLo && aHi <= bHi;
  }

  @Override
  public int integerVariable(int aVar) {
    return semanticUip && aVar < litVar.length ? litVar[aVar] : -1;
  }

  /**
   * The atom equal to a conjunction of true atoms of one variable, when one exists: the values they
   * leave form one interval, after the {@code x != v} atoms at its ends, that touches a root bound
   * ({@code [x >= v]} or {@code [x <= v]}) or holds one value ({@code [x = v]}).
   */
  @Override
  public int semanticUip(int[] lits, int size) {
    int i = litVar[Math.abs(lits[0])];
    long lo = Long.MIN_VALUE;
    long hi = Long.MAX_VALUE;
    for (int k = 0; k < size; k++) {
      int d = Math.abs(lits[k]);
      long v = litValue[d];
      if (litKind[d] == GE_KIND) {
        if (lits[k] > 0) {
          lo = Math.max(lo, v);
        } else {
          hi = Math.min(hi, v - 1);
        }
      } else if (lits[k] > 0) {
        lo = Math.max(lo, v);
        hi = Math.min(hi, v);
      }
    }
    for (boolean moved = true; moved; ) {
      moved = false;
      for (int k = 0; k < size; k++) {
        int d = Math.abs(lits[k]);
        if (litKind[d] == EQ_KIND && lits[k] < 0 && (litValue[d] == lo || litValue[d] == hi)) {
          lo += litValue[d] == lo ? 1 : 0;
          hi -= litValue[d] == hi ? 1 : 0;
          moved = true;
        }
      }
    }
    for (int k = 0; k < size; k++) {
      int d = Math.abs(lits[k]);
      if (litKind[d] == EQ_KIND && lits[k] < 0 && lo < litValue[d] && litValue[d] < hi) {
        return 0; // a hole inside the interval
      }
    }
    int min = root[i].min();
    int max = root[i].max();
    if (lo > hi || lo <= min && hi >= max) {
      return 0;
    }
    int d = LiteralMap.NONE;
    if (lo == hi) {
      d = eq[i].get((int) lo);
    }
    if (d == LiteralMap.NONE && hi >= max) {
      return orZero(ge[i].get((int) lo), 1);
    }
    if (d == LiteralMap.NONE && lo <= min) {
      return orZero(ge[i].get((int) hi + 1), -1);
    }
    return orZero(d, 1);
  }

  private static int orZero(int d, int sign) {
    return d == LiteralMap.NONE ? 0 : sign * d;
  }

  private void setPropagated(int dimacsVar, int e) {
    if (dimacsVar >= propagated.length) {
      propagated = Arrays.copyOf(propagated, Math.max(dimacsVar + 1, 2 * propagated.length));
    }
    propagated[dimacsVar] = e;
  }

  /**
   * Makes {@link #minimize} look only for solutions better than the best one found outside this
   * solver, for example by another search of the same model in a parallel portfolio. The supplier
   * is read from the solver's thread whenever it takes clauses, and gives {@link Integer#MAX_VALUE}
   * as long as there is no such solution. When {@link #minimize} then ends without a better
   * solution, the best solution found outside is optimal.
   *
   * @param bound the objective value of the best solution found elsewhere
   */
  public void setSharedBound(IntSupplier bound) {
    sharedBound = bound;
  }

  /**
   * Makes activity branching prefer the values of the best solution found outside this solver
   * whenever it takes up that solution's bound (see {@link #setSharedBound}) and the solution is
   * better than its own: the search goes on near that solution, as it does near its own best
   * (solution-guided search, Beck 2007; CP-SAT's workers take the best solution as their hint in
   * the same way). The values are only preferred; the bound clause excludes the solution itself.
   *
   * @param solution the best solution found elsewhere, with the bound's objective value
   */
  public void setSharedPhase(SharedSolution solution) {
    sharedPhase = solution;
  }

  /**
   * Gives values that activity branching prefers until the first solution of this solver, for
   * example those of a solution found by local search.
   *
   * @param xs variables of the store
   * @param values their values
   */
  public void setPhase(IntVar[] xs, int[] values) {
    int[] p = new int[vars.length];
    for (int i = 0; i < vars.length; i++) {
      p[i] = vars[i] == null ? 0 : vars[i].min();
    }
    for (int k = 0; k < xs.length; k++) {
      int i = index(xs[k]);
      if (i >= 0) {
        p[i] = values[k];
      }
    }
    phase = p;
  }

  /**
   * Hands the store back for search without learning: its changes are no longer recorded, and the
   * layered-graph constraints that went to the solver as clauses are in the store again. The solver
   * cannot solve again afterwards; its best solution stays readable.
   */
  public void release() {
    trail.detach();
    for (LayeredGraphConstraint g : encodedGraphs) {
      g.restoreConstraint(store);
    }
    encodedGraphs.clear();
    // search without learning needs the propagators of the constraints that became clauses
    for (Constraint c : encodedConstraints) {
      // removeConstraint only marked it as entailed above the root
      store.clearEntailed(c);
      c.impose(store);
    }
    encodedConstraints.clear();
  }

  /**
   * Tells whether the best solution has a value for x: there is one, and x existed when the solver
   * was built.
   *
   * @param x the variable
   * @return true when {@link #value} gives x's value
   */
  public boolean hasValue(IntVar x) {
    return solution != null && trail.id(x) < solution.length;
  }

  /**
   * Shares clauses with the solvers of the same model in other threads: learnt clauses of at most
   * the given size and LBD over atoms of named variables, and the root bounds of those variables,
   * go out at restarts, when those of the other solvers come in. The store holds the model all
   * solvers share plus the constraints named by {@code added} (such as symmetry breaking), and the
   * shared bound must be the cost of a solution all of them know of; see {@link SharedClauses}.
   *
   * @param pool the clauses of all solvers
   * @param added the constraints the store adds to the shared model, the same text for the same
   *     constraints in every solver; empty when it adds none
   * @param name the name of a variable in the model, or null for a variable of this store only
   * @param size the largest learnt clause shared
   * @param lbd the largest LBD of a learnt clause shared
   */
  public void setSharedClauses(
      SharedClauses pool, String added, Function<IntVar, String> name, int size, int lbd) {
    if (pool == null || sat.hasProof()) {
      return;
    }
    shared = pool;
    sharedSource = pool.newSource(added);
    sharedId = new int[vars.length];
    publishedMin = new int[vars.length];
    publishedMax = new int[vars.length];
    int top = -1;
    for (int i = 0; i < vars.length; i++) {
      sharedId[i] = -1;
      if (vars[i] != null && !root[i].singleton()) {
        String n = name.apply(vars[i]);
        if (n != null) {
          sharedId[i] = pool.id(n);
          top = Math.max(top, sharedId[i]);
          publishedMin[i] = root[i].min();
          publishedMax[i] = root[i].max();
        }
      }
    }
    sharedLocal = new int[top + 1];
    Arrays.fill(sharedLocal, -1);
    for (int i = 0; i < vars.length; i++) {
      if (sharedId[i] >= 0) {
        sharedLocal[sharedId[i]] = i;
      }
    }
    sat.setLearntExport(size, lbd);
  }

  @Override
  public void notifyLearnt(int[] clause, int lbd) {
    if (shared == null) {
      return;
    }
    int[] c = new int[2 + 3 * clause.length];
    c[0] = sharedSource;
    c[1] = lbd;
    for (int k = 0; k < clause.length; k++) {
      int d = Math.abs(clause[k]);
      int i = d < litVar.length ? litVar[d] : -1;
      if (i < 0 || sharedId[i] < 0) {
        return; // an auxiliary literal or a variable of this store only
      }
      c[2 + 3 * k] = sharedId[i];
      c[3 + 3 * k] = litKind[d] + (clause[k] < 0 ? SharedClauses.NEGATED : 0);
      c[4 + 3 * k] = litValue[d];
    }
    exportBatch.add(c);
    clausesExported++;
  }

  @Override
  public int[] importedClause() {
    return imports.poll();
  }

  /** At the root: gives out the new learnt clauses and root bounds, takes in the others'. */
  private void exchangeShared() {
    if (shared == null || failed) {
      return;
    }
    for (int i = 0; i < sharedId.length; i++) {
      if (sharedId[i] < 0) {
        continue;
      }
      IntVar x = vars[i];
      if (x.min() > publishedMin[i]) {
        publishedMin[i] = x.min();
        exportBatch.add(new int[] {sharedSource, 1, sharedId[i], SharedClauses.GE, x.min()});
        boundsExported++;
      }
      if (x.max() < publishedMax[i]) {
        publishedMax[i] = x.max();
        exportBatch.add(
            new int[] {
              sharedSource, 1, sharedId[i], SharedClauses.GE + SharedClauses.NEGATED, x.max() + 1
            });
        boundsExported++;
      }
    }
    if (!exportBatch.isEmpty()) {
      shared.publish(exportBatch);
      exportBatch.clear();
    }
    List<int[]> in = new ArrayList<>();
    sharedRead = shared.read(sharedRead, sharedSource, in);
    for (int[] c : in) {
      int[] clause = localClause(c);
      if (clause == null) {
        clausesSkipped++;
      } else {
        imports.add(clause);
        clausesImported++;
      }
    }
  }

  /**
   * A shared clause in this solver's literals, without the atoms false at the root; null when an
   * atom is true at the root, a variable is not in this store, or a literal of a clause of two or
   * more atoms does not exist here (new literals cost more than the clause saves).
   */
  private int[] localClause(int[] c) {
    int n = (c.length - 2) / 3;
    int[] clause = new int[n];
    int size = 0;
    for (int k = 0; k < n; k++) {
      int id = c[2 + 3 * k];
      int i = id < sharedLocal.length ? sharedLocal[id] : -1;
      if (i < 0) {
        return null;
      }
      boolean negated = c[3 + 3 * k] >= SharedClauses.NEGATED;
      int kind = c[3 + 3 * k] % SharedClauses.NEGATED;
      int v = c[4 + 3 * k];
      IntDomain r = root[i];
      boolean atRootTrue;
      boolean atRootFalse;
      if (kind == SharedClauses.GE) {
        atRootTrue = v <= r.min();
        atRootFalse = v > r.max();
      } else {
        atRootFalse = !r.contains(v);
        atRootTrue = r.singleton(v);
      }
      if (atRootTrue || atRootFalse) {
        if (atRootTrue != negated) {
          return null; // the clause holds at the root
        }
        continue;
      }
      int d = (kind == SharedClauses.GE ? ge : eq)[i].get(v);
      if (d == LiteralMap.NONE) {
        if (n > 1) {
          return null;
        }
        d = kind == SharedClauses.GE ? geVar(i, v) : eqVar(i, v);
      } else {
        keep(d);
      }
      clause[size++] = negated ? -d : d;
    }
    return Arrays.copyOf(clause, size);
  }

  /** Stops {@link #solve} and {@link #minimize}, also when called from another thread. */
  public void stop() {
    sat.cancel();
  }

  @Override
  public int[] externalClause() {
    if (structural.isEmpty()
        && sharedBound != null
        && proof == null
        && objective >= 0
        && !coreMode) {
      importBound();
    }
    return structural.poll();
  }

  /** Adds the clause that the objective is below a better bound found elsewhere. */
  private void importBound() {
    int localShared = sharedBound.getAsInt();
    if (localShared >= importedBound || (best != null && localShared >= best[objective])) {
      return;
    }
    importedBound = localShared;
    if (localShared <= root[objective].min()) {
      sharedBoundUnreachable = true;
      sat.cancel();
    } else if (localShared <= root[objective].max()) {
      // the literal first, so that its linking clauses come before the bound
      int lit = geLit(objective, localShared);
      structural.add(new int[] {-lit}); // objective <= shared - 1
      if (sharedPhase != null) {
        takeSharedPhase();
      }
    }
  }

  /** Prefers the values of the shared solution, keeping the preferred values of other variables. */
  private void takeSharedPhase() {
    int[] p = new int[vars.length];
    for (int i = 0; i < vars.length; i++) {
      if (phase != null && i < phase.length) {
        p[i] = phase[i];
      } else if (vars[i] != null) {
        p[i] = vars[i].min();
      }
    }
    boolean[] taken = {false};
    sharedPhase.values(
        (x, v) -> {
          int i = index(x);
          if (i >= 0 && i < p.length) {
            p[i] = v;
            taken[0] = true;
          }
        });
    if (taken[0]) {
      phase = p;
      sharedPhases++;
    }
  }

  /**
   * Pushes the atoms the store recorded to the solver one at a time, each with its explanation as
   * reason; once all are in, applies the solver's new assignments to the domains and propagates the
   * store. A failure is returned as a false literal whose reason is the conflict clause, which the
   * solver takes as a conflict.
   */
  @Override
  public int propagate() {
    if (failed) {
      return 0;
    }
    while (true) {
      while (numImplied > 0) {
        int lit = impliedLits[--numImplied];
        if (sat.value(lit) <= 0) {
          setPropagated(Math.abs(lit), impliedEntries[numImplied]);
          return lit;
        }
      }
      while (pushed < trail.size()) {
        int e = pushed;
        if (defer(e)) {
          deferredAtoms++;
          pushed++;
          continue;
        }
        int lit = atomLit(e);
        if (sat.value(lit) > 0) {
          // a transient literal implies no linked one by a clause: the nearest is pushed too
          int next = linkedNeighbour(e, lit);
          if (next != 0 && sat.value(next) <= 0) {
            setPropagated(Math.abs(next), e);
            return next;
          }
          pushed++;
          continue;
        }
        int dimacsVar = Math.abs(lit);
        setPropagated(dimacsVar, e);
        if (dimacsVar >= atomUse.length) {
          atomUse = Arrays.copyOf(atomUse, propagated.length);
        }
        if (atomUse[dimacsVar] == 0) {
          atomUse[dimacsVar] = 1;
          atomLiterals++;
        }
        atomsPropagated++;
        return lit;
      }
      if (numPending == 0 && !store.hasPendingConstraints()) {
        return 0;
      }
      int from = trail.size();
      for (int k = 0; k < numPending; k++) {
        int lit = pending[k];
        try {
          apply(lit);
        } catch (FailException _) {
          IntVar x = vars[litVar[Math.abs(lit)]];
          EntryList atoms = failureAtoms;
          atoms.clear();
          trail.atomsBefore(x, trail.size(), atoms);
          return conflict(atoms, lit);
        }
        if (trail.size() > cause.length) {
          cause = Arrays.copyOf(cause, Math.max(trail.size(), 2 * cause.length));
        }
        for (; from < trail.size(); from++) {
          cause[from] = lit;
        }
      }
      numPending = 0;
      if (!store.consistency()) {
        constraintConflicts++;
        EntryList atoms = failureAtoms;
        atoms.clear();
        if (linear != null) {
          learnLinear(linear.analyse(store.recentlyFailedConstraint, store.level));
        }
        boolean own = trail.explainFailure(store.recentlyFailedConstraint, atoms);
        if (PROOF_TRACE && proof != null) {
          proof.comment((own ? "failure " : "generic failure ") + store.recentlyFailedConstraint);
        }
        if (proof != null) {
          proofCardinality(store.recentlyFailedConstraint, atoms, 0, -1);
          proofCircuit(store.recentlyFailedConstraint, atoms, 0, -1);
          proofEnergy(store.recentlyFailedConstraint, atoms, 0, -1);
          proofLp(store.recentlyFailedConstraint, atoms, 0, -1);
          proofLinearBounds(store.recentlyFailedConstraint, atoms, 0, -1);
        }
        count(store.recentlyFailedConstraint, own, atoms.size(), 3);
        measure(store.recentlyFailedConstraint, own, -1, atoms, 0);
        if (checker != null) {
          verify(checker.checkFailure(store.recentlyFailedConstraint, atoms));
        }
        return conflict(atoms, 0);
      }
    }
  }

  /**
   * Adds the reason entries of an entry to {@code out}; an entry recorded while applying a solver
   * literal is explained by its variable's atoms before it and that literal, which is returned.
   *
   * @return the solver literal that is part of the reason, or 0
   */
  // constraints that gave a deferred removal the generic reason: their removals are pushed again,
  // since a clause citing one cites every atom of their variables in its place
  private final Set<Constraint> genericDeferred =
      Collections.newSetFromMap(new IdentityHashMap<>());

  private int explainEntry(int e, EntryList out) {
    if (trail.reason(e) == null) {
      trail.atomsBefore(trail.variable(e), e, out);
      return cause[e];
    }
    int mark = out.size();
    boolean own = trail.explain(e, out);
    if (PROOF_TRACE && proof != null) {
      proof.comment((own ? "reason " : "generic reason ") + trail.reason(e));
    }
    if (proof != null) {
      proofCardinality(trail.reason(e), out, mark, e);
      proofCircuit(trail.reason(e), out, mark, e);
      proofEnergy(trail.reason(e), out, mark, e);
      proofLp(trail.reason(e), out, mark, e);
      proofLinearBounds(trail.reason(e), out, mark, e);
    }
    if (!own && e < pushed && trail.kind(e) == AtomicTrail.NE && !inSolver(e)) {
      genericDeferred.add(trail.reason(e));
    }
    count(trail.reason(e), own, out.size() - mark, 0);
    measure(trail.reason(e), own, e, out, mark);
    if (checker != null) {
      EntryList reason = new EntryList();
      for (int k = mark; k < out.size(); k++) {
        reason.addFrom(out, k);
      }
      verify(checker.checkReason(e, reason));
    }
    return 0;
  }

  // per constraint class: reasons, generic reasons and atoms in them, then the same for failures
  private void count(Constraint c, boolean own, int atoms, int at) {
    long[] counts =
        explanationCounts.computeIfAbsent(
            c == null ? "none" : c.getClass().getSimpleName(), k -> new long[8]);
    counts[at]++;
    if (!own) {
      counts[at + 1]++;
    } else if (trail.replayed()) {
      counts[6 + at / 3]++;
    }
    counts[at + 2] += atoms;
  }

  // every minimality-th explanation: how many of its atoms propagation needs (and how many of
  // those a weaker earlier atom replaces), per class and kind (own or generic, reason or failure)
  private void measure(Constraint c, boolean own, int entry, EntryList out, int mark) {
    if (minimiser == null || c == null || ++untilMinimised < minimality) {
      return;
    }
    untilMinimised = 0;
    EntryList reason = new EntryList();
    for (int k = mark; k < out.size(); k++) {
      reason.add(out.get(k));
    }
    // an explanation may cite an entry more than once; only the distinct ones are measured
    reason.sortUnique(0);
    int[] m = minimiser.minimise(c, entry, reason);
    String key =
        c.getClass().getSimpleName()
            + (entry < 0 ? "/failure" : "/reason")
            + (own ? "" : "/generic");
    long[] counts = minimalityCounts.computeIfAbsent(key, k -> new long[7]);
    if (m == null) {
      counts[5]++;
    } else if (m[1] < 0) {
      counts[4]++;
    } else {
      counts[0]++;
      counts[1] += m[0];
      counts[2] += m[1];
      counts[3] += m[2];
      counts[6] += m[3];
    }
  }

  /**
   * Returns the minimality statistics of the explanations sampled with the system property {@code
   * jacop.lcg.minimality} (every n-th one), per constraint class and kind ({@code Class/reason} or
   * {@code Class/failure}, with {@code /generic} for the generic reason): explanations minimised,
   * their atoms, the atoms propagation needed, the needed atoms a weaker earlier atom replaced,
   * explanations propagation could not use as a whole, explanations that could not be checked, and
   * the needed bound atoms that a weaker bound, not on the trail, could replace.
   *
   * @return seven counts per key, in the order above
   */
  public Map<String, long[]> minimalityStatistics() {
    return minimalityCounts;
  }

  /**
   * Returns the explanation statistics per constraint class (simple name): reasons asked, those
   * given by the generic reason, and the atoms in them; then failures explained, those explained
   * generically, and their atoms; then the reasons and the failures explained by replaying the
   * constraint (counted as its own).
   *
   * @return eight counts per class, in the order above
   */
  public Map<String, long[]> explanationStatistics() {
    return explanationCounts;
  }

  private static void verify(String problem) {
    if (problem != null) {
      throw new IllegalStateException("wrong explanation: " + problem);
    }
  }

  /**
   * Turns a failure into a conflict: the negated atoms, each one not yet in the solver replaced by
   * its own explanation, and the negated solver literal extra unless 0. Returns a false literal of
   * the clause, whose reason is the clause.
   */
  private int conflict(EntryList atoms, int extra) {
    numPending = 0;
    failed = true;
    int seen = nextStamp();
    if (entryStamp.length < trail.size()) {
      entryStamp = Arrays.copyOf(entryStamp, Math.max(trail.size(), 2 * entryStamp.length));
    }
    if (entrySlack.length < trail.size()) {
      entrySlack = Arrays.copyOf(entrySlack, Math.max(trail.size(), 2 * entrySlack.length));
    }
    // the smallest slack each entry is cited with
    int[] slack = entrySlack;
    EntryList inSolver = conflictInSolver;
    inSolver.clear();
    EntryList lits = conflictLits;
    lits.clear();
    if (extra != 0) {
      lits.add(-extra);
    }
    EntryList stack = atoms;
    while (stack.size() > 0) {
      int e = stack.get(stack.size() - 1);
      int eSlack = stack.slack(stack.size() - 1);
      stack.truncate(stack.size() - 1);
      if (entryStamp[e] == seen) {
        slack[e] = Math.min(slack[e], eSlack);
        continue;
      }
      entryStamp[e] = seen;
      slack[e] = eSlack;
      if (inSolver(e)) {
        inSolver.add(e);
      } else {
        int mark = stack.size();
        int more = explainEntry(e, stack);
        if (more != 0) {
          lits.add(-more);
        }
        if (proof != null) {
          proofLemma(e, stack, mark, more);
        }
      }
    }
    int[] clause = new int[inSolver.size() + lits.size()];
    int size = 0;
    int distinct = nextStamp();
    for (int k = 0; k < clause.length; k++) {
      int lit;
      if (k < inSolver.size()) {
        int e = inSolver.get(k);
        lit = -atomLit(e, slack[e]);
      } else {
        lit = lits.get(k - inSolver.size());
      }
      int key = 2 * Math.abs(lit) + (lit < 0 ? 1 : 0);
      if (key >= litStamp.length) {
        litStamp = Arrays.copyOf(litStamp, Math.max(key + 1, 2 * litStamp.length));
      }
      if (litStamp[key] != distinct) {
        litStamp[key] = distinct;
        clause[size++] = lit;
      }
    }
    if (size < clause.length) {
      clause = Arrays.copyOf(clause, size);
    }
    if (clause.length == 0) {
      // the explanations, stronger than propagation at the root, prove the model unsatisfiable:
      // the empty clause follows, and so does any clause, here one false literal; the solver
      // backjumps to the root on it and then takes the empty clause
      int any = extra == 0 ? trueAtom() : extra;
      if (any == 0) {
        throw new IllegalStateException(
            "the constraints failed on the root domains: " + store.recentlyFailedConstraint);
      }
      structural.add(new int[0]);
      clause = new int[] {-any};
    }
    if (PROOF_TRACE && proof != null) {
      // the conflict clause as a step of its own, so that a checker names it when it is not rup
      int[] internal = new int[clause.length];
      for (int k = 0; k < clause.length; k++) {
        internal[k] = clause[k] > 0 ? 2 * (clause[k] - 1) : 2 * (-clause[k] - 1) + 1;
      }
      proof.comment("conflict clause of " + store.recentlyFailedConstraint);
      proof.add(internal, 0, internal.length);
    }
    pushedReason = clause;
    return clause[0];
  }

  // a new stamp for entryStamp and litStamp, clearing both when the stamps wrap around
  private int nextStamp() {
    if (++stamp == Integer.MAX_VALUE) {
      Arrays.fill(entryStamp, 0);
      Arrays.fill(litStamp, 0);
      stamp = 1;
    }
    return stamp;
  }

  // a literal the solver has true, or 0 when it has assigned nothing
  private int trueAtom() {
    int n = sat.trailSize();
    return n == 0 ? 0 : sat.trailLiteral(n - 1);
  }

  private void apply(int lit) {
    int dimacsVar = Math.abs(lit);
    IntVar x = vars[litVar[dimacsVar]];
    int v = litValue[dimacsVar];
    store.currentConstraint = null;
    if (litKind[dimacsVar] == GE_KIND) {
      if (lit > 0) {
        x.domain.inMin(store.level, x, v);
      } else {
        x.domain.inMax(store.level, x, v - 1);
      }
    } else if (lit > 0) {
      x.domain.in(store.level, x, v, v);
    } else if (x.domain.contains(v)) {
      x.domain.inComplement(store.level, x, v);
    }
  }

  /**
   * Returns the reason of a literal: the conflict clause just returned by {@link #propagate}, or
   * the explanation of the atom pushed as that literal, computed now.
   */
  @Override
  public int[] reason(int lit) {
    if (pushedReason != null && pushedReason[0] == lit) {
      int[] r = pushedReason;
      pushedReason = null;
      return r;
    }
    int e = propagated[Math.abs(lit)];
    if (linear != null && linear.usable(trail.reason(e))) {
      noteOrigin(lit, trail.reason(e));
    }
    EntryList reason = reasonEntries;
    reason.clear();
    liftBefore = sat.trailPosition(lit);
    int extra;
    try {
      extra = explainEntry(e, reason);
      if (deferredAtoms > 0) {
        extra = explainDeferred(reason, extra);
      }
    } finally {
      liftBefore = Integer.MAX_VALUE;
    }
    int[] clause = new int[reason.size() + (extra == 0 ? 1 : 2)];
    clause[0] = lit;
    for (int k = 0; k < reason.size(); k++) {
      clause[k + 1] = -atomLit(reason.get(k), reason.slack(k));
    }
    if (extra != 0) {
      clause[clause.length - 1] = -extra;
    }
    reasons++;
    reasonLiterals += clause.length;
    return clause;
  }

  /**
   * Decides on the model's annotation in its runs while it has unfixed variables; otherwise, with
   * activity branching, on the most active unfixed variable, a 0/1 one while any is unfixed (unless
   * the system property {@code jacop.lcg.booleansFirst} is false, which branches on all variables
   * in one order of activity): its value in the last solution when still possible, else the lower
   * half of its domain (the system property {@code jacop.lcg.value} = {@code min} or {@code max}
   * picks its smallest or largest value instead). Without activity branching, leaves the decision
   * to the solver's VSIDS until every literal is assigned, then branches on {@code [x <= min]} of
   * the unfixed variable with the smallest domain.
   */
  @Override
  public int decide() {
    if (branching == Branching.AUTO
        && best == null
        && !activityBranching
        && sat.conflicts >= AUTO_CONFLICTS) {
      activityBranching = true; // no solution yet from the literals: activity until the first one
    }
    if (annotationRun) {
      int lit = annotationDecision();
      if (lit != 0) {
        annotationDecisions++;
        return lit;
      }
    }
    if (activityBranching) {
      if (activityGuide != null && !freeSearch && annotation != null) {
        int lit = guideDecision();
        if (lit != 0) {
          guideDecisions++;
          return lit;
        }
      }
      return activityDecision();
    }
    return 0;
  }

  /** The next decision of the selection that starts the activity runs, or 0 when it has none. */
  private int guideDecision() {
    Var v = activityGuide.getChoiceVariable(0);
    if (v == null) {
      return 0;
    }
    int i = idOf(v);
    if (i < 0 || vars[i].singleton()) {
      return 0;
    }
    int value = activityGuide.getChoiceValue();
    return vars[i].domain.contains(value) ? assignLit(i, value) : 0;
  }

  // decideLast scans the variables in lastOrder[0, lastSize), moving the fixed ones past lastSize;
  // lastLevelSize[k] is lastSize when the scan first ran at decision level lastLevel[k], restored
  // when search backtracks below that level (the scan over all variables at each decision took
  // 48 % of skill-allocation's run time)
  private int[] lastOrder;
  private int lastSize;
  private int[] lastLevel = new int[16];
  private int[] lastLevelSize = new int[16];
  private int numLastLevels;

  /**
   * Without activity branching, once the solver has assigned every literal, branches on {@code [x
   * <= min]} of the unfixed variable with the smallest domain.
   */
  @Override
  public int decideLast() {
    if (activityBranching || !structural.isEmpty()) {
      return 0;
    }
    if (lastOrder == null || lastOrder.length != vars.length) {
      lastOrder = new int[vars.length];
      lastSize = 0;
      for (int i = 0; i < vars.length; i++) {
        if (vars[i] != null && !unused[i]) {
          lastOrder[lastSize++] = i;
        }
      }
      numLastLevels = 0;
    }
    int level = sat.decisionLevel();
    if (numLastLevels == 0 || lastLevel[numLastLevels - 1] < level) {
      if (numLastLevels == lastLevel.length) {
        lastLevel = Arrays.copyOf(lastLevel, 2 * numLastLevels);
        lastLevelSize = Arrays.copyOf(lastLevelSize, 2 * numLastLevels);
      }
      lastLevel[numLastLevels] = level;
      lastLevelSize[numLastLevels++] = lastSize;
    }
    int localBest = -1;
    int bestSize = Integer.MAX_VALUE;
    int size = lastSize;
    for (int p = 0; p < size; ) {
      int i = lastOrder[p];
      IntVar x = vars[i];
      if (x.singleton()) {
        // fixed at this level or below: out of the scan until a backtrack below the level
        lastOrder[p] = lastOrder[--size];
        lastOrder[size] = i;
        continue;
      }
      p++;
      if (!unused[i]) {
        int n = x.getSize();
        if (n < bestSize || (n == bestSize && i < localBest)) {
          localBest = i;
          bestSize = n;
        }
      }
    }
    lastSize = size;
    if (localBest < 0) {
      return 0;
    }
    searchDecisions++;
    return -geLit(localBest, vars[localBest].min() + 1);
  }

  // the heap of a variable: lateHeap for a late variable, else wide for one that is not 0/1
  private void rebuildHeap(VarHeap h) {
    int[] members = new int[activity.length];
    int n = 0;
    for (int i = 0; i < activity.length; i++) {
      if (h.contains(i)) {
        members[n++] = i;
      }
    }
    h.rebuild(members, n);
  }

  private VarHeap heapOf(int i) {
    if (late[i]) {
      return lateHeap;
    }
    return split && (root[i].min() < 0 || root[i].max() > 1) ? wide : heap;
  }

  // takes the fixed variables off the top of a heap, to be put back on backtracking
  private void popFixed(VarHeap h) {
    while (!h.isEmpty() && vars[h.max()].singleton()) {
      if (numPopped == popped.length) {
        popped = Arrays.copyOf(popped, 2 * numPopped);
        poppedLevel = Arrays.copyOf(poppedLevel, 2 * numPopped);
      }
      popped[numPopped] = h.removeMax();
      poppedLevel[numPopped++] = sat.decisionLevel();
    }
  }

  private int activityDecision() {
    popFixed(heap);
    popFixed(wide);
    VarHeap h = heap.isEmpty() ? wide : heap;
    if (h.isEmpty()) {
      popFixed(lateHeap);
      h = lateHeap;
      if (h.isEmpty()) {
        return 0;
      }
    }
    int i = h.max();
    if (lastConflict
        && conflictVar >= 0
        && !vars[conflictVar].singleton()
        && heapOf(conflictVar) == h) {
      i = conflictVar; // last-conflict branching (Lecoutre et al. 2009)
    }
    conflictVar = -1;
    decisionVar = i;
    if (late[i]) {
      lateDecisions++;
    }
    IntVar x = vars[i];
    searchDecisions++;
    if (phase != null && x.domain.contains(phase[i])) {
      return assignLit(i, phase[i]);
    }
    if (phase == null
        && targetSet != null
        && i < targetSet.length
        && targetSet[i]
        && x.domain.contains(targetValue[i])) {
      targetDecisions++;
      return assignLit(i, targetValue[i]);
    }
    return switch (valueChoice) {
      case "max" -> geLit(i, x.max());
      case "split" -> -geLit(i, x.min() + (x.max() - x.min()) / 2 + 1);
      default -> -geLit(i, x.min() + 1);
    };
  }

  /**
   * Sets the variables that no constraint uses, such as the variables a reformulation of the model
   * replaced: they are never branched on, and a solution gives them their least value. Set them
   * before solving, and impose no constraint on them afterwards.
   *
   * @param vs the unused variables
   */
  public void setUnusedVariables(Iterable<? extends Var> vs) {
    for (Var v : vs) {
      int i = idOf(v);
      if (i >= 0 && !unused[i]) {
        unused[i] = true;
        for (VarHeap h : new VarHeap[] {heap, wide, lateHeap}) {
          if (h.contains(i)) {
            h.remove(i);
          }
        }
      }
    }
  }

  /**
   * Sets the variables branched on by activity only after every other variable is fixed, such as
   * variables defined by a constraint from the others. Set them before solving.
   *
   * @param defined the variables to branch on last
   */
  public void setLateVariables(Iterable<? extends Var> defined) {
    for (Var v : defined) {
      int i = idOf(v);
      if (i >= 0 && !late[i]) {
        VarHeap h = heapOf(i);
        late[i] = true;
        lateVariables++;
        if (h.contains(i)) {
          h.remove(i);
          lateHeap.insert(i);
        }
      }
    }
  }

  private void bump(int i) {
    bumpedAt[i] = sat.conflicts;
    if (sat.conflicts != activityConflicts) {
      activityConflicts = sat.conflicts;
      activityInc /= 0.95;
    }
    if ((activity[i] += activityInc) > 1e100) {
      for (int k = 0; k < activity.length; k++) {
        activity[k] *= 1e-100;
      }
      activityInc *= 1e-100;
    }
    heapOf(i).increased(i);
  }

  /**
   * The annotation's next decision as a literal, or 0 when it has fixed all its variables or
   * chooses something that is not an atom of the store's integer variables.
   */
  private int annotationDecision() {
    int from = numAnnotationIndices > 0 ? annotationIndex[numAnnotationIndices - 1] : 0;
    if (from == ANNOTATION_DONE) {
      return 0;
    }
    Var v = annotation.getChoiceVariable(from);
    PrimitiveConstraint c = v == null ? annotation.getChoiceConstraint(from) : null;
    if (numAnnotationIndices > 0
        && annotationLevel[numAnnotationIndices - 1] == sat.decisionLevel()) {
      numAnnotationIndices--; // a later index at the same level replaces it
    }
    if (numAnnotationIndices == annotationIndex.length) {
      int n = Math.max(16, 2 * numAnnotationIndices);
      annotationIndex = Arrays.copyOf(annotationIndex, n);
      annotationLevel = Arrays.copyOf(annotationLevel, n);
    }
    annotationIndex[numAnnotationIndices] =
        v != null || c != null ? annotation.getIndex() : ANNOTATION_DONE;
    annotationLevel[numAnnotationIndices++] = sat.decisionLevel();
    if (c instanceof MirroredChoice mc) {
      // an element of a set variable out of the set first (outdomain)
      int i = idOf(mc.mirrored().decisionVariable(mc.value()));
      return i < 0 ? 0 : assignLit(i, mc.holds() ? 1 : 0);
    }
    if (v instanceof Mirrored m) {
      // the left branch on a set variable's element is that the element is in the set
      int i = idOf(m.decisionVariable(annotation.getChoiceValue()));
      return i < 0 ? 0 : assignLit(i, 1);
    }
    if (v != null) {
      int i = idOf(v);
      if (i < 0) {
        return 0;
      }
      int value = annotation.getChoiceValue();
      return vars[i].domain.contains(value) ? assignLit(i, value) : 0;
    }
    if (!(c instanceof LinearExplainable l)) {
      return 0;
    }
    LinearForm f = l.linearForm();
    if (f == null || f.vars().length != 1 || Math.abs(f.weights()[0]) != 1) {
      return 0;
    }
    int i = idOf(f.vars()[0]);
    if (i < 0) {
      return 0;
    }
    long w = f.weights()[0];
    long bound = w * f.c(); // the relation on x itself, with LE and GE swapped for -x
    int relation = f.relation();
    if (w < 0 && relation == LinearForm.LE) {
      relation = LinearForm.GE;
    } else if (w < 0 && relation == LinearForm.GE) {
      relation = LinearForm.LE;
    }
    IntDomain d = vars[i].domain;
    if (bound < d.min() || bound > d.max()) {
      return 0;
    }
    int b = (int) bound;
    return switch (relation) {
      case LinearForm.LE -> b < d.max() ? -geLit(i, b + 1) : 0;
      case LinearForm.GE -> b > d.min() ? geLit(i, b) : 0;
      case LinearForm.EQ -> d.contains(b) ? eqVar(i, b) : 0;
      default -> d.contains(b) ? -eqVar(i, b) : 0;
    };
  }

  /**
   * The decision that x = v, for v in the domain of an unfixed x: [x <= v] when v is its smallest
   * value and [x >= v] when v is its largest, which fix x as [x = v] would without creating that
   * literal and its clauses, else [x = v].
   */
  private int assignLit(int i, int v) {
    IntDomain d = vars[i].domain;
    if (v == d.min()) {
      return -geLit(i, v + 1);
    }
    if (v == d.max()) {
      return geLit(i, v);
    }
    return eqVar(i, v);
  }

  private int idOf(Var v) {
    if (!(v instanceof IntVar x) || x.singleton()) {
      return -1;
    }
    int i = trail.id(x);
    return i >= 0 && i < vars.length && vars[i] == x ? i : -1;
  }

  /**
   * Records a solution. When minimising, it then rejects the model with the clause that the
   * objective is smaller, unless the objective is at its smallest value.
   */
  @Override
  public boolean checkModel(int[] model) {
    solution = new int[vars.length];
    for (int i = 0; i < vars.length; i++) {
      if (vars[i] != null) {
        if (unused[i] && !vars[i].singleton()) {
          solution[i] = vars[i].min();
          continue;
        }
        if (!vars[i].singleton()) {
          throw new IllegalStateException(vars[i] + " is not fixed in a model");
        }
        solution[i] = vars[i].value();
      }
    }
    // under core-guided search a solution need not improve on the best one
    boolean improving = objective < 0 || best == null || solution[objective] < best[objective];
    if (proof != null && improving) {
      logSolution();
    }
    if (onSolution != null && improving) {
      onSolution.run();
    }
    if (restartsAfterSolution) {
      restartsAfterSolution = false;
      sat.setRestarts(true);
    }
    if (objective < 0) {
      return true;
    }
    if (improving) {
      improvedInRun = true;
      best = solution;
      phase = solution;
      if (branching == Branching.AUTO) {
        activityBranching = false; // the solver's saved phases now hold this solution
      }
      solutions++;
      if (lns != null) {
        lns.solution();
      }
    }
    if (coreMode) {
      return true;
    }
    int v = solution[objective];
    if (v <= root[objective].min()) {
      return true;
    }
    // the literal first, so that its linking clauses come before the bound
    int lit = geLit(objective, v);
    structural.add(new int[] {-lit}); // objective <= v - 1
    return false;
  }
}
