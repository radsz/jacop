/*
 * LinearRelaxation.java
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

package org.jacop.constraints.lp;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.IntStream;
import org.jacop.api.Copyable;
import org.jacop.api.Stateful;
import org.jacop.api.VarMap;
import org.jacop.constraints.ChannelOrder;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.Linearizations;
import org.jacop.constraints.Routes;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.constraints.cumulative.CumulativeUnaryOptional;
import org.jacop.constraints.table.HybridTable;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.LinearReasons;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;

/**
 * The linear relaxation of the linear constraints of a store, solved by a dual simplex during
 * search, as a propagator of lowest priority. Every deduction is an integer combination of the
 * rows: the multipliers of the simplex (its dual values at an optimal basis, or the row of the
 * basis inverse that proves infeasibility) are scaled and rounded to integers, the combination
 * {@code sum lambda_i a_i x} with the matching sides of the rows is computed exactly, and the
 * resulting inequality is propagated by bounds reasoning. A combination of rows holds wherever the
 * rows do, so floating-point errors of the simplex can weaken the deduction but never make it
 * wrong. With an objective, the combination of the dual values bounds the objective and fixes
 * variables by their reduced costs; without one, the relaxation only detects infeasibility.
 *
 * <p>For lazy clause generation each deduction is explained by its inequality ({@link LinearForm}),
 * through the bounds of the other variables, as a linear constraint of the model would be.
 *
 * <p>The simplex is the dense {@link DualSimplex} by default, or the sparse revised dual simplex of
 * JaLP ({@link Simplex#SPARSE}, {@code org.jacop.jalp.RevisedDualSimplex} through {@code
 * JalpSimplex}), which fits large sparse relaxations. With {@link Simplex#LAZY} the sparse simplex
 * starts without rows: each solve adds, in batches, the rows its solution breaks and solves again,
 * and rows that stay inactive for many solves leave the simplex again. The rows the simplex lacks
 * only weaken its deductions; every deduction is still a combination of rows of the model.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LinearRelaxation extends Constraint
    implements Explainable, LinearReasons, PbEncodable, Stateful, Copyable<LinearRelaxation> {

  /** The value of a system property that turns a default-on flag off. */
  private static final String FALSE = "false";

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The simplex that solves the relaxation. */
  public enum Simplex {
    /** The dense tableau simplex, {@link DualSimplex}. */
    DENSE,
    /** The sparse revised dual simplex of JaLP, with every row. */
    SPARSE,
    /** The sparse revised simplex with the rows added and removed lazily. */
    LAZY
  }

  // whether certificate() cleans the combination: drops the multipliers of a missing side and
  // divides each inequality by the gcd of its weights
  private static final boolean CLEAN = !FALSE.equals(System.getProperty("org.jacop.lp.clean"));

  // multipliers below this share of the largest are taken as round-off of the simplex
  private static final double NOISE = 1e-11;

  // the scales tried for the multipliers, the largest first
  private static final long[] SCALES = {1L << 40, 1L << 32, 1L << 24, 1L << 16, 1L << 8, 1};

  // the scale of the rows of the basis inverse the Gomory cuts come from, and the one tried when
  // that overflows. The rounding error of a multiplier times the weights of its row must stay well
  // below the weight of the basic column in the combination: with the cuts of a first round as
  // rows, whose weights reach 2^24, the multipliers of 2^20 were too coarse and the later rounds
  // found no violated Gomory cut (hoist, racp, radiation)
  private static final long GOMORY_SCALE = Long.getLong("org.jacop.lp.gomoryScale", 1L << 36);
  private static final long GOMORY_FALLBACK = 1L << 20;

  private final IntVar[] x;
  // whether each column is an auxiliary column of the relaxation ({@link LpColumn}), not a
  // variable of the store, and whether there is any
  private final boolean[] lpOnly;
  private final boolean anyLpOnly;
  // whether the relaxation holds the all-different-except encodings over auxiliary columns, or the
  // value encodings of the model's Booleans that chose the sparse simplex, which are the relaxation
  // itself and are not dropped for the pivot limits of search (the other encodings are extra rows
  // like any)
  private boolean keepEncodings;
  // the extra rows before the value encodings of valueRows' tried rows, which come last; the others
  // are tried without them when all of them are not kept
  private int plainExtra = Integer.MAX_VALUE;
  // the extra rows before the flow models of layered graphs, which come after the other tried
  // value encodings; the rows before them are tried without them when all are not kept, and are
  // kept instead of all when they give the same bound
  private int triedExtra = Integer.MAX_VALUE;
  // the value encodings ahead of the other extra rows, tried alone first when not every candidate
  // row fits the share (see of)
  private int leadExtra = 0;
  private static final boolean LEAD_ENCODINGS =
      !FALSE.equals(System.getProperty("org.jacop.lp.leadEncodings"));
  // the rows, the cuts last
  private int[][] rowColumns;
  private long[][] rowWeights;
  private long[] rowLo;
  private long[] rowHi;
  private boolean[] hasLo;
  private boolean[] hasHi;
  private final IntVar objective;
  private LpSolver lp;
  // the simplex of the relaxation: the one it was created with, or the sparse one after the rows
  // of a full dense tableau moved there for the cuts
  private Simplex simplex;
  private final Simplex createdWith;

  // the pivots of simplices dropped for a copy kept before them
  private long droppedPivots;

  // the rows of the relaxation are one pool, of which the simplex holds a part: the row of the
  // relaxation of each row of the simplex, whether each row of the relaxation is in the simplex,
  // and for each row of the simplex the optimal solves in a row in which it was inactive. The
  // first baseCount rows of the simplex are rows of the model that never leave it (none with lazy
  // rows); the others (the rows of other constraints, cuts, lazy rows) leave it after poolAge
  // inactive solves, stay in the pool, and come back when a solution of the simplex breaks them
  private int[] lpRow;
  private boolean[] inLp;
  private int[] inactive;
  private int baseCount;
  // whether lpRow is the identity, the rows of the simplex those of the relaxation in order
  private boolean identityRows;
  // the rows of the pool that are not in the simplex
  private int dormant;
  // for each row of the pool, the times it came back to the simplex: each return doubles the
  // inactive solves after which it leaves again, so that a row the search keeps breaking stays
  private int[] returns = new int[0];

  // the nonzeros of the rows checked against the solution since the last propagation
  private long scanned;

  // the rows as given, and the sense of the objective, for copies
  private final List<LinearForm> forms = new ArrayList<>();

  // the source of the given and further rows ({@link LpSources}), and of each cut row by its row
  // (null for a row that is not a cut); the statistics by source, null unless they are kept
  private Map<LinearForm, String> formSource = Map.of();
  private String[] cutSource = new String[0];
  private final LpSources sources = LpSources.on ? new LpSources() : null;
  private final boolean maximize;

  /** The most simplex pivots per propagation. */
  private int pivotLimit = 500;

  // the relaxation is solved at one call in period; the period doubles after IDLE_RUNS solves that
  // deduce nothing, up to MAX_PERIOD, and halves after one that deduces something
  private static final int IDLE_RUNS = Integer.getInteger("org.jacop.lp.idle", 32);
  private static final int MAX_PERIOD = Integer.getInteger("org.jacop.lp.maxPeriod", 4096);
  private int period = 1;
  private int tick;
  private int idle;

  // the largest tableau, rows times columns, that is built, and the tableau entries the pivots of
  // one propagation may update, below the root and at the root
  private static final long MAX_TABLEAU = Long.getLong("org.jacop.lp.maxTableau", 4_000_000L);

  // the most nonzeros of the rows of the sparse simplex
  private static final long MAX_NONZEROS = Long.getLong("org.jacop.lp.maxNonzeros", 4_000_000L);

  // lazy rows: the most rows added per round, the rounds per solve, and the optimal solves a row
  // stays inactive before it leaves the simplex
  private static final int LAZY_BATCH = Integer.getInteger("org.jacop.lp.lazyBatch", 50);
  private static final int LAZY_ROUNDS = Integer.getInteger("org.jacop.lp.lazyRounds", 100);
  private static final int LAZY_AGE = Integer.getInteger("org.jacop.lp.lazyAge", 100);

  // the value encodings of the model's Booleans in place of the hull rows of the element
  // constraints they cover, and counted with the exempt rows when the simplex is chosen by size
  // (-Dorg.jacop.lp.encodingRows=false: the hull rows, and the simplex chosen without them; not
  // final: a test hook)
  static boolean encodingRowsOn = !FALSE.equals(System.getProperty("org.jacop.lp.encodingRows"));

  // the row pool: whether the rows of other constraints and the cuts leave the simplex after
  // POOL_AGE optimal solves in which they are inactive (with lazy rows every row does, after
  // LAZY_AGE); and whether the rows of other constraints that the root trial does not keep, and
  // the cuts of a round that does not move the bound, stay in the pool instead of being dropped.
  // Both are off: such rows come back at the first solves in search, as its solution breaks them,
  // which undoes the root's choice to leave them out, and neither moved a result on the wide set
  private static final boolean POOL = !FALSE.equals(System.getProperty("org.jacop.lp.pool"));
  private static final int POOL_AGE = Integer.getInteger("org.jacop.lp.poolAge", 100);
  private static final boolean POOL_EXTRA = Boolean.getBoolean("org.jacop.lp.poolExtra");
  private static final boolean POOL_CUTS = Boolean.getBoolean("org.jacop.lp.poolCuts");
  private static final long WORK = Long.getLong("org.jacop.lp.work", 20_000_000L);
  private static final long ROOT_WORK = Long.getLong("org.jacop.lp.rootWork", 1_000_000_000L);

  // the most pivots of the first solve, which has the root budget instead of the pivot limit: a
  // root LP that stops at the limit gives neither a bound nor cuts; not final, so that tests can
  // make a root solve stop at it
  static int rootPivots = Integer.getInteger("org.jacop.lp.rootPivots", 20_000);

  // the tableau entries earned by each call of consistency, up to WORK; a solve spends the entries
  // its pivots update, a solve that only tightens bounds a PRUNE_DISCOUNT-th of them, and a solve
  // that fails the node fills the credit; while the credit is negative the relaxation is not
  // solved,
  // so a relaxation that finds little costs a bounded share of the search
  private static final long WORK_PER_CALL = Long.getLong("org.jacop.lp.workPerCall", 4096L);
  private static final long PRUNE_DISCOUNT = Long.getLong("org.jacop.lp.pruneDiscount", 16L);

  // the work of the sparse simplex in search counted against the credit, in units of a dense
  // tableau entry. A unit of the sparse simplex's work takes 1-1.8 ns and a dense tableau entry
  // 0.45-0.57 ns (Challenge: triangular n11, unit-commitment, roster-shifts-bool), but a factor of
  // 3 slowed the LP proofs (roster-shifts-bool s200_e50_c8 16 -> 32 s, harmony canon 28 -> 49 s)
  // more than it helped elsewhere (triangular n11 LP time 56 -> 30 of 60 s), so it stays 1
  private static final long SPARSE_COST = Long.getLong("org.jacop.lp.sparseCost", 1L);
  private long credit = WORK;

  // the solves in a row stopped at the pivot limit; after IDLE_RUNS of them the simplex is taken to
  // be stalling and the relaxation is not solved again
  private int stalled;

  // the deductions of the current branch, for their explanations: variable, form, level
  private final List<IntVar> deducedVar = new ArrayList<>();
  private final List<LinearForm> deducedForm = new ArrayList<>();
  private final List<Integer> deducedLevel = new ArrayList<>();
  // the auxiliary columns that the form of a deduction leaves at a bound the domain of their
  // variable gives: j when [x = v] is 0 as v is not in the domain of x, ~j when it is 1 as x is v;
  // the form holds only with these facts, which its explanation adds (null when there are none)
  private final List<int[]> deducedFacts = new ArrayList<>();

  // the form propagated when the last failure happened, and its facts
  private LinearForm failureForm;
  private int[] failureFacts;

  // the facts of the two inequalities of the last combine(): upper, lower
  private final int[][] combineFacts = new int[2][];

  /**
   * How a deduction of a relaxation built for a proof ({@link #ofModel}) follows from the model:
   * the form is the sum over k of {@code multipliers[k]} times the relation of the constraint
   * {@code rows[k]}, its {@code <=} side for a positive multiplier and its {@code >=} side, times
   * the absolute value, for a negative one. A proof writes it as a {@code pol} step over the lines
   * of those constraints.
   *
   * @param form the form that is propagated, {@code sum w x <= c}
   * @param rows the constraints of the rows combined
   * @param multipliers the multiplier of each, not zero
   */
  public record Certificate(LinearForm form, Constraint[] rows, long[] multipliers) {
    @Override
    public boolean equals(Object o) {
      return o instanceof Certificate c
          && form == c.form
          && Arrays.equals(rows, c.rows)
          && Arrays.equals(multipliers, c.multipliers);
    }

    @Override
    public int hashCode() {
      return 31 * Arrays.hashCode(rows) + Arrays.hashCode(multipliers);
    }

    @Override
    public String toString() {
      return "Certificate(" + rows.length + " rows)";
    }
  }

  // for a proof: the constraint of each row, or null when the relaxation is not built for one
  private Constraint[] rowSource;
  // the certificate of each deduction (by deducedForm), of the last failure, and of the form that
  // explained last
  private final List<Certificate> deducedCertificate = new ArrayList<>();
  private Certificate failureCertificate;
  private Certificate lastCertificate;

  /** Statistics: propagations. */
  public long calls;

  /** Statistics: infeasible relaxations. */
  public long infeasible;

  /**
   * Statistics: infeasible relaxations whose rounded Farkas multipliers proved the infeasibility at
   * no scale. Skipping the solves below such a solve was tried and lost: the subtree is then
   * searched without the relaxation (the 60-item knapsack with search cuts of weights up to 2^24:
   * 141 million nodes in 60 s after 5 unproven solves).
   */
  public long unproven;

  /** Statistics: failures proved by an exact combination. */
  public long failures;

  /** Statistics: bounds tightened. */
  public long prunings;

  /** Statistics: propagations stopped at the pivot limit. */
  public long limits;

  /** The solves stopped at their limit whose duals were turned into a bound, and what it pruned. */
  public long anytimeSolves;

  /** The prunings by the bounds of solves stopped at their limit. */
  public long anytimePrunings;

  /** The failures found by the bounds of solves stopped at their limit. */
  public long anytimeFailures;

  private long anytimePruningsBefore = -1;
  private long anytimeFailuresBefore;

  // the duals of a solve stopped at its pivot limit bound the objective too
  // (org.jacop.lp.anytimeBound)
  private static final boolean ANYTIME_BOUND =
      Boolean.parseBoolean(System.getProperty("org.jacop.lp.anytimeBound", "true"));

  /** Statistics: the objective bound of the first optimal solve, or NaN. */
  public double rootBound = Double.NaN;

  /** Statistics: the objective bound of the first optimal solve after the cuts, or NaN. */
  public double cutBound = Double.NaN;

  /** Statistics: cuts added. */
  public long cuts;

  /** Statistics: cuts that did not move the root bound, kept in the pool out of the simplex. */
  public long pooledCuts;

  /** Statistics: rows of other constraints the root trial did not keep, kept in the pool. */
  public long pooledExtra;

  /** Statistics: the clique rows in place of the rows of pairs of conflicting 0/1 literals. */
  public int pairCliques;

  /**
   * Statistics: the rows over the terms of the objective for which the sparse simplex was taken,
   * since they did not fit the dense tableau; 0 when that did not happen.
   */
  public int nearRows;

  /**
   * The value encodings that went ahead of the other extra rows, which did not all fit the share of
   * the trial; 0 when none did.
   */
  public int leadEncodings;

  /** The clique rows over value Booleans among the candidates (Linearizations.valueCliques). */
  public int valueCliques;

  /** Whether the value encodings ahead of the other extra rows were kept alone at their trial. */
  public boolean leadKept;

  /**
   * Statistics: the element constraints whose hull rows were left out for the value encoding that
   * links their value to the Booleans of their index.
   */
  public int encodedElements;

  /** Statistics: whether the value encodings of the model's Booleans chose the sparse simplex. */
  public boolean encodingsSparse;

  /** Statistics: the clause rows of tables over 0/1 variables tried at the first solve. */
  public int tableClauses;

  /** Statistics: the time of the solves and their propagation, in nanoseconds. */
  public long solveNanos;

  /** Statistics: rows added to the simplex from the pool, as the simplex's solution broke them. */
  public long lazyAdded;

  /** Statistics: rows removed from the simplex to the pool, as they stayed inactive. */
  public long lazyRemoved;

  /** Statistics: rows of constraints that are not linear relations, kept after the first solve. */
  public long extraRows;

  /** Statistics: whether those rows were dropped in search, as too many solves hit the limit. */
  public boolean extraDropped;

  /** Statistics: the extra rows of a satisfaction model kept on probation at the root. */
  public boolean probationKept;

  /** Statistics: the solves charged as pruning ones because the relaxation failed nodes often. */
  public long failingSolves;

  /**
   * Statistics: whether those rows moved the dense tableau to the sparse simplex, as it left too
   * few pivots for a solve in search.
   */
  public boolean extraSparse;

  /** Statistics: the auxiliary columns ({@link LpColumn}) of the relaxation. */
  public int valueColumns;

  /**
   * Statistics: the free auxiliary columns ({@link LpColumn#isFree}) of the relaxation, the wires
   * of the sorting networks of all-different permutations.
   */
  public int freeColumns;

  /** Statistics: the objective bound of the first solve without those rows, or NaN. */
  public double baseBound = Double.NaN;

  /** Statistics: solves at least {@code org.jacop.lp.basisJump} levels above the last solve. */
  public long jumpSolves;

  /** Statistics: the pivots of those solves. */
  public long jumpPivots;

  /** Statistics: bases restored for those solves. */
  public long basisRestores;

  // the bases of the last optimal solve at each of the levels of the current branch, shallowest
  // first, restored when the search jumps back from deeper levels (a restart, a long backjump):
  // the basis the deeper node left is optimal for bounds far from the current ones, the kept one
  // for bounds close to them (roadmap A5)
  private static final boolean KEEP_BASES =
      !FALSE.equals(System.getProperty("org.jacop.lp.keepBases"));
  private static final int BASIS_JUMP = Integer.getInteger("org.jacop.lp.basisJump", 2);
  private static final int MAX_BASES = Integer.getInteger("org.jacop.lp.maxBases", 32);
  // the dense simplex saves a basis with a copy of its tableau, about one pivot, so it keeps the
  // bases of the levels at most this far below the first solve only (restarts, long backjumps);
  // -1 keeps none
  private static final int DENSE_BASIS_DEPTH =
      Integer.getInteger("org.jacop.lp.denseBasisDepth", 3);
  private int firstSolveLevel = -1;
  // while the rows of the other constraints are judged by the solves that stop at the limit, the
  // first solves after a jump start from the basis the deeper node left, as before bases were
  // kept: a restored basis spares them the limit and keeps rows that slow every later solve
  // (slnb7x7: 404 big-M rows kept, 4x the LP time)
  private static final long BASIS_PROBATION = Long.getLong("org.jacop.lp.basisProbation", 1000L);
  private final List<Object> bases = new ArrayList<>();
  private int[] basisLevel = new int[0];
  private LpSolver basesOf;
  private int lastSolveLevel = -1;

  // whether the rows of constraints that are not linear relations are added (Linearizations)
  private static final boolean LINEARIZE =
      !FALSE.equals(System.getProperty("org.jacop.lp.linearize"));

  // the rows of constraints that are not linear relations (Linearizations) are added at the first
  // solve, and kept when they move the bound, find infeasibility or are few
  private static final int SMALL_EXTRA = Integer.getInteger("org.jacop.lp.smallExtra", 100);

  // the rows of the constraints that are not linear relations, added at the first solve
  private List<LinearForm> extraForms = new ArrayList<>();
  // the rows of the other constraints once kept: the prunings found with them stay explained by
  // them, so a copy keeps them even after they are dropped here
  private List<LinearForm> keptExtraForms = List.of();
  // a copy keeps the rows of the other constraints that its original kept, whatever its own solve
  private boolean keepExtra;
  private int[][] extraColumns = new int[0][];
  private long[][] extraWeights = new long[0][];
  private long[] extraSide = new long[0];
  private int[] extraRelation = new int[0];

  // the simplex before the rows of the other constraints, the number of rows then, and the limits
  // hit before them; the rows are dropped when three solves with them, and one in twenty, stop at
  // the pivot limit
  private LpSolver beforeExtra;
  private int baseRows;
  private long extraLimits;
  private static final int EXTRA_LIMITS = Integer.getInteger("org.jacop.lp.extraLimits", 3);

  // the extra rows of a dense tableau whose search solves get fewer pivots than this move to the
  // sparse simplex when it costs at most a quarter of the tableau per pivot (moveExtraToSparse)
  private static final boolean EXTRA_SPARSE =
      !FALSE.equals(System.getProperty("org.jacop.lp.extraSparse"));
  private static final long EXTRA_SPARSE_PIVOTS = 100;
  private static final long EXTRA_SPARSE_GAIN = 4;

  // the most given rows of a relaxation whose extra rows move to the sparse simplex: the row of the
  // objective alone, as in a set covering, whose rows are all clauses. With more given rows the
  // extra rows kept on the sparse simplex made search slower (mqueens n11 7 -> 21 s, 12 rows;
  // prize-collecting 32-4-8-2 14 -> 32 s, 33 rows; hoist PU_2_8_1 3 -> 9 s, 94 rows; at 240 s)
  private static final int EXTRA_SPARSE_ROWS = 1;

  // whether the extra rows carry the bound of the relaxation: without them it does not cut the
  // domain of the objective
  private boolean extraCarry;
  // the call at which the extra rows were added
  private long extraCall;
  // the failures of the relaxation before the extra rows were added
  private long extraFailures;

  // the extra rows of a satisfaction model are kept at the root on probation: after this many
  // solves they are dropped unless at least FAIL_RATE of the solves since then failed the node;
  // 0 turns the probation off (the rows are then kept only when the root LP is infeasible)
  private static final int SATISFACTION_PROBATION =
      Integer.getInteger("org.jacop.lp.satisfactionProbation", 64);
  private boolean probation;

  // the share of solves that fail the node above which the relaxation is taken to pay for itself:
  // its solves that deduce nothing are charged a PRUNE_DISCOUNT-th of their work, and its extra
  // rows are not dropped for the pivot limits they hit
  private static final double FAIL_RATE =
      Double.parseDouble(System.getProperty("org.jacop.lp.failRate", "0.1"));
  // the share of the recent solves that failed the node, decaying by 1/32 a solve
  private double recentFailures;

  // whether the sparse simplex was chosen by the size of the relaxation in place of the dense one
  private boolean bySize;

  // a relaxation over the size caps of the sparse simplex in search: solved at the root only
  private boolean large;

  // made by refutation(): solved once at the root, then removed
  private boolean refutation;
  // a refutation whose objective is a free column of the longest inequality of the model
  private boolean pseudoObjective;
  private int refutationStatus = -1;
  // the status of the last solve
  private int lastSolveStatus = -1;

  // the solutions kept so far, which tells a reader of the last solution when it changed
  private int solutionVersion;

  // the time of a root solve of a large relaxation, in nanoseconds
  private long largeRootNanos = (long) (LARGE_ROOT_SECONDS * 1e9);

  // when the time of the solves of the root of a large relaxation runs out (0 before they start;
  // each restart solve starts again)
  private long largeDeadline;

  // MIR cuts at the root: rounds, cuts per round, and the share of the rows they may add
  private static final boolean CUTS_ENABLED =
      !FALSE.equals(System.getProperty("org.jacop.lp.cuts"));
  private static final int CUT_ROUNDS = Integer.getInteger("org.jacop.lp.cutRounds", 5);
  // rounds after the first CUT_ROUNDS, while each still moves the bound: at most this many rounds
  // in all, within CUT_EXTRA_NANOS of the end of the first CUT_ROUNDS
  private static final int CUT_ROUNDS_MAX = Integer.getInteger("org.jacop.lp.cutRoundsMax", 50);
  private static final long CUT_EXTRA_NANOS =
      (long) (Double.parseDouble(System.getProperty("org.jacop.lp.cutExtraSeconds", "1")) * 1e9);
  // an extra round must move the bound by this share of what the rounds before it moved it
  private static final double CUT_PROGRESS = 0.01;
  private static final int CUTS_PER_ROUND = Integer.getInteger("org.jacop.lp.cutsPerRound", 50);
  private static final int MAX_SOURCES = 100;

  // whether the rows of a dense tableau with no room for a round of cuts move to the sparse
  // simplex, which has no tableau, for the cut rounds; they stay there, with the cuts, when the
  // cuts raise the bound of the integer objective, and go back to the dense tableau otherwise
  private static final boolean SPARSE_CUTS =
      !FALSE.equals(System.getProperty("org.jacop.lp.sparseCuts"));

  // the dense simplex whose rows moved to the sparse one for the cuts, and its rows in the pool,
  // until the cut rounds end
  private LpSolver denseBeforeCuts;
  private int[] denseLpRow;
  private boolean[] denseInLp;
  private int[] denseInactive;
  private boolean denseIdentity;
  private int denseRows;
  private int denseDormant;

  /** Statistics: whether the rows moved from the full dense tableau to JaLP for the cuts. */
  public boolean sparseCuts;

  // the size cap of the dense tableau for the cuts of this relaxation
  private long tableauCap = MAX_TABLEAU;

  // the scale of the multipliers of the Gomory rows of this relaxation
  private long gomoryScale = GOMORY_SCALE;

  /**
   * Sets the scale of the rows of the basis inverse the Gomory cuts come from: their largest entry
   * becomes about the scale before they are rounded to integers. The default is {@code
   * org.jacop.lp.gomoryScale} (2^36); a row that overflows at that scale is taken again at 2^20.
   *
   * @param scale the scale, at least 1
   */
  public void setGomoryScale(long scale) {
    gomoryScale = scale;
  }

  /**
   * Sets the size cap of the dense tableau, rows times columns, for the cuts of this relaxation:
   * the cut rounds stop adding cuts to the dense tableau at the cap, and the rows move to the
   * sparse simplex when a round of cuts would pass it. The default is {@code
   * org.jacop.lp.maxTableau} (4,000,000); tests set a small cap to reach the move on small models.
   *
   * @param cap the most entries of the dense tableau with the cuts
   */
  public void setTableauCap(long cap) {
    tableauCap = cap;
  }

  private static final double MAX_PARALLELISM = 0.9;

  // rounded capacity cuts of the Routes constraints at the root, before the MIR cuts: rounds and
  // the share of the rows they may add; the rounds stop when no cut is violated or the bound
  // stalls, and the cuts are dropped when they do not move the bound
  private static final boolean CAPACITY_CUTS =
      !FALSE.equals(System.getProperty("org.jacop.lp.capacityCuts"));
  private static final int CAPACITY_ROUNDS = Integer.getInteger("org.jacop.lp.capacityRounds", 50);
  private static final int CAPACITY_STALL = 3;

  // the separations of the capacity cuts, one for each Routes with its arcs among the columns
  private List<CapacityCuts> capacity = new ArrayList<>();

  // blossom and comb cuts (CombCuts) also in search, not only at the root
  private static final boolean COMB_SEARCH = Boolean.getBoolean("org.jacop.lp.combSearch");

  // energy cuts of the cumulative resources at the root, in the rounds of the capacity cuts
  private static final boolean ENERGY_CUTS =
      !FALSE.equals(System.getProperty("org.jacop.lp.energyCuts"));

  // the separations of the energy cuts, one for each cumulative resource
  private List<EnergyCuts> energy = new ArrayList<>();

  /** Statistics: energy cuts of cumulative resources added. */
  public long energyCuts;

  // the capacity, energy and Hall cuts kept, as rows: they follow from the Routes, cumulative and
  // all-different constraints, not from the rows, so a copy takes them as rows of its own
  private final List<LinearForm> capacityForms = new ArrayList<>();

  /** Statistics: rounded capacity cuts added. */
  public long capacityCuts;

  /**
   * Statistics: the 2-path cuts of the Routes with time windows among the capacity cuts, at the
   * root and in search ({@link CapacityCuts#twoPathCuts}).
   *
   * @return the number of 2-path cuts separated
   */
  public long twoPathCuts() {
    long sum = 0;
    for (CapacityCuts c : capacity) {
      sum += c.twoPathCuts();
    }
    return sum;
  }

  /** Statistics: the arc-time rows of the Routes with time windows in the relaxation. */
  public int arcTimeRows;

  // Hall cuts of the all-different constraints ({@link AlldifferentCuts}) at the root, after the
  // capacity and energy cuts and before the MIR cuts, in rounds like those; for an objective only
  private static final boolean ALLDIFF_CUTS =
      !FALSE.equals(System.getProperty("org.jacop.lp.alldiffCuts"));

  // the separations of the Hall cuts, one for each all-different
  private List<AlldifferentCuts> hall = new ArrayList<>();

  /** Statistics: Hall cuts of all-different constraints added. */
  public long alldiffCuts;

  /** Statistics: the objective bound after the Hall cuts, before the MIR cuts, or NaN. */
  public double alldiffBound = Double.NaN;

  // the Hall cuts of the all-different constraints with exceptions (alldifferent_except_0) and of
  // the global cardinality constraints (GCC, CountValues), with the copies of their values
  private static final boolean ALLDIFF_VARIANTS =
      !FALSE.equals(System.getProperty("org.jacop.lp.alldiffVariants"));

  // Hall cuts in search, as the capacity cuts: separated from the solution of an optimal solve
  // every hallPeriod solves, the period doubling (up to CAPACITY_MAX_PERIOD) after a separation
  // that finds no violated cut and halving after one that does; the cuts use the root domains, so
  // they hold globally, and go into the row pool; off by default, as on the Challenge instances
  // that have them they cost more solves than the bound gains (osolpro alldiff-hall-search)
  private static final boolean ALLDIFF_SEARCH =
      "true".equals(System.getProperty("org.jacop.lp.alldiffSearch"));
  private static final int ALLDIFF_SEARCH_CUTS =
      Integer.getInteger("org.jacop.lp.alldiffSearchCuts", 10);
  private boolean alldiffSearch = ALLDIFF_SEARCH;
  private int hallPeriod = 4;
  private int hallWaited;
  // the column of each variable of each separation, -1 when the variable is not a column
  private int[][] hallColumns;
  private final Set<List<Long>> hallSeen = new HashSet<>();

  /** Statistics: the all-different constraints with Hall cuts, and those of them with copies. */
  public long alldiffLists;

  public long alldiffVariantLists;

  /** Statistics: Hall cuts added in search. */
  public long alldiffSearchCuts;

  /** Statistics: separations of Hall cuts in search. */
  public long alldiffSeparations;

  // generalized subtour elimination cuts of the forests of Tree and Path ({@link TreeCuts}) at the
  // root, after the Hall cuts and before the MIR cuts, in rounds like those; for an objective only
  private static final boolean TREE_CUTS =
      !FALSE.equals(System.getProperty("org.jacop.lp.treeCuts"));

  // the separations of the tree cuts, one for each acyclic Reachable
  private List<TreeCuts> trees = new ArrayList<>();

  // the most rounds of tree cuts: each round adds a few dozen cuts and the bound climbs far (ch130
  // of surface-based-tsp: 6,096 after 50 rounds, 6,108 of the optimum 6,112 at the end)
  private static final int TREE_ROUNDS = Integer.getInteger("org.jacop.lp.treeRounds", 200);

  /** Statistics: subtour elimination cuts of trees and paths added. */
  public long treeCuts;

  /** Statistics: the objective bound after the tree cuts, before the MIR cuts, or NaN. */
  public double treeBound = Double.NaN;

  /**
   * The number of trees and paths whose subtour elimination cuts the relaxation makes at the root.
   *
   * @return the number of acyclic Reachable constraints with tree cuts
   */
  public int treeConstraints() {
    return trees.size();
  }

  // MIR and Gomory cuts in search, like the capacity cuts: separated from the solution of an
  // optimal solve every mirPeriod solves, over the bounds of the first solve, so that they hold
  // globally; the period halves after a separation whose cuts move the bound and doubles otherwise
  // (up to CAPACITY_MAX_PERIOD). The cuts go into the row pool and leave the simplex when they age.
  // A model with a weak root relaxation that only branching tightens (tank allocation, XCSP 2025,
  // where CP-SAT adds about 1,200 cuts in search) gets its bound from them. Off by default
  // (-Dorg.jacop.lp.mirSearch=true): the separations take the work budget of the LP calls, so on a
  // knapsack of 60 items the LP ran 8 times less often and the search needed 7 times more nodes
  private static final boolean MIR_SEARCH = Boolean.getBoolean("org.jacop.lp.mirSearch");
  private static final int MIR_SEARCH_CUTS = Integer.getInteger("org.jacop.lp.mirSearchCuts", 10);
  // the largest weight of a cut made in the cut rounds (see MirCut.capped), unlimited by default
  // (-Dorg.jacop.lp.cutWeight=1048576 for 2^20): a cut row of weights near 2^24, with a right side
  // near 10^10, gets Farkas multipliers of 10^-7 of the wrong sign from the dense tableau, which
  // the integer certificate cannot use, so the infeasible solve proves nothing (smelt_4, MiniZinc
  // Challenge 2014, -f: 56 of 57 infeasible solves; tank allocation: thousands in 60 s). 2^20
  // removes them there, but on the 41 wide instances whose cuts it changes it was not faster at
  // 240 s (-f 1.03, default 1.10 time on the solved ones, within the noise of two base runs)
  private static final long ROOT_CUT_WEIGHT =
      Long.getLong("org.jacop.lp.cutWeight", Long.MAX_VALUE);
  // the largest weight of a cut made in search (see MirCut.capped)
  private static final long MIR_SEARCH_WEIGHT =
      Long.getLong("org.jacop.lp.mirSearchWeight", 1L << 16);
  private int mirPeriod = 4;
  private int mirWaited;
  // the rows of the first cut rounds, as aggregates, and the keys of the cuts chosen so far
  private Aggregate[] mirRows;
  private Set<List<Long>> mirSeen;
  // the columns of the simplex the rows were taken over; another simplex (the extra rows dropped)
  // ends the cuts in search
  private int mirColumns;

  /** Statistics: rounds of root cuts whose re-solve stopped at its pivot limit. */
  public long cutLimits;

  // zero-half cuts in the cut rounds, from sets of tight rows whose sum is odd on the right side
  // (ZeroHalfCuts), rounded with the MIR of divisor 2. Off by default
  // (-Dorg.jacop.lp.zeroHalf=true):
  // on the 240 wide instances they fire on 36 and raise the integer root bound of 10 (lower 2),
  // but at 240 s on the 41 where the cuts change the solves were the same, 5-7 % slower, and the
  // best solutions of 3 families worse: the extra rows cost each solve more than they prune. Not
  // final, so that tests can switch it on
  static boolean zeroHalfOn = Boolean.getBoolean("org.jacop.lp.zeroHalf");
  // the most slack of a row the zero-half separator takes, the most rows, and the most sets
  private static final double ZERO_HALF_SLACK = 0.1;
  private static final int ZERO_HALF_ROWS = 2000;
  private static final int ZERO_HALF_SETS = 50;
  // the least efficacy of a zero-half cut: the dense sums of many rows the separator finds on
  // tank allocation (XCSP 2025) are violated by 0.001 to 0.1 over their norm, and those below 0.02
  // took the places of better MIR cuts (cut bound 1676 -> 1681) and made the LP numerically weak
  private static final double ZERO_HALF_EFFICACY = 0.02;

  /** Statistics: zero-half cuts added (in the cut rounds and in search). */
  public long zeroHalfCuts;

  /** Statistics: MIR cuts of the rows weighted by their dual values added (rounds and search). */
  public long dualCuts;

  /** Statistics: MIR and Gomory cuts added in search. */
  public long mirSearchCuts;

  /** Statistics: separations of MIR and Gomory cuts in search. */
  public long mirSeparations;

  // capacity and multistar cuts in search: separated from the solution of an optimal solve every
  // capacityPeriod solves, the period doubling (up to CAPACITY_MAX_PERIOD) after a separation that
  // finds no violated cut and halving after one that does. The cuts hold globally (root demands,
  // capacity and self loops), go into the row pool and leave the simplex when they age.
  private static final boolean CAPACITY_SEARCH =
      !FALSE.equals(System.getProperty("org.jacop.lp.capacitySearch"));
  // the big-M arc-time rows of Routes with time windows and node times (CapacityCuts.arcTimeRows),
  // as rows of the relaxation, or tried like the linearized rows with ARC_TIME_TRIED
  private static final boolean ARC_TIME_ROWS =
      !FALSE.equals(System.getProperty("org.jacop.lp.arcTimeRows"));
  private static final boolean ARC_TIME_TRIED =
      "tried".equals(System.getProperty("org.jacop.lp.arcTimeRows"));
  private static final int CAPACITY_SEARCH_CUTS =
      Integer.getInteger("org.jacop.lp.capacitySearchCuts", 10);
  private static final int CAPACITY_MAX_PERIOD = 1024;
  private int capacityPeriod = 4;
  private int capacityWaited;
  // the column of each arc of each separation, -1 when the arc is not a column
  private int[][] capacityColumns;
  private final Set<List<Long>> capacitySeen = new HashSet<>();

  /** Statistics: capacity and multistar cuts added in search. */
  public long capacitySearchCuts;

  /** Statistics: separations of capacity cuts in search. */
  public long capacitySeparations;

  // the cuts separated in search keep a short period only while they move the bound: a separation
  // whose cuts leave the objective bound of the re-solve where it was counts as one that finds
  // none, so the period doubles, as violated cuts that do not tighten only make each solve dearer
  // (Hall cuts in search lost pigment20a's and cable-tree-wiring A022's optima to that cost)
  private static final boolean SEARCH_CUT_GATE =
      !FALSE.equals(System.getProperty("org.jacop.lp.searchCutGate"));

  /** Statistics: separations in search whose cuts moved the bound or made the LP infeasible. */
  public long searchSeparationsMoved;

  // energy cuts of the cumulative resources also in search, under the same period and gate as the
  // capacity cuts; they use the bounds of the first solve, so they hold globally (off by default)
  private static final boolean ENERGY_SEARCH =
      "true".equals(System.getProperty("org.jacop.lp.energySearch"));
  private boolean energySearch = ENERGY_SEARCH;
  private int energyPeriod = 4;
  private int energyWaited;
  // the column of each start of each energy separation (-1 when not a column), and the bounds of
  // the columns at the first solve
  private int[][] energyColumns;
  private long[] energyLo;
  private long[] energyHi;
  private final Set<List<Long>> energySeen = new HashSet<>();

  /** Statistics: energy cuts added in search. */
  public long energySearchCuts;

  /** Statistics: separations of energy cuts in search. */
  public long energySeparations;

  /** Statistics: the objective bound after the capacity cuts, before the MIR cuts, or NaN. */
  public double capacityBound = Double.NaN;

  // the cuts are made at the first solve only, before any search decision: they use the bounds of
  // that moment, which hold for the whole search
  private boolean cutsTried;

  // restarts, with org.jacop.lp.restartSolves=true: the relaxation is solved again at the level of
  // its first solve whenever the bound of the objective has improved since the last solve there,
  // with the root budget and, unless org.jacop.lp.restartCuts=false, new cut rounds over the bounds
  // of the first solve; what it deduces there holds for the rest of the search. Off by default:
  // on the wide set (220, 60 s) it was neutral under -f and cost the proof of ATSP instance10 in
  // the default mode (LP time 0.4 s to 3.8 s), while the root reduced costs alone gain the same
  // not final, so that tests can switch it on
  static boolean restartSolvesOn = "true".equals(System.getProperty("org.jacop.lp.restartSolves"));
  private static final boolean RESTART_CUTS =
      !FALSE.equals(System.getProperty("org.jacop.lp.restartCuts"));
  private int rootLevel = -1;
  private long rootObjective;
  private boolean restarting;
  private long[] rootLo;
  private long[] rootHi;

  /** Statistics: solves at the root level after the bound of the objective improved. */
  public long restartSolves;

  // with org.jacop.lp.restartBounds=true (and restartSolves), the cut rounds of a restart solve use
  // the bounds of the root level at that restart, which the learnt facts and the bound of the
  // objective tighten, instead of those of the first solve: the cuts CP-SAT makes at its restarts
  // (TankAllocation, XCSP 2025). Such cuts hold while the root level stays; should the search ever
  // remove that level, the relaxation stops solving and checks only the rows made before them
  // not final, so that tests can switch it on
  static boolean restartBoundsOn = "true".equals(System.getProperty("org.jacop.lp.restartBounds"));
  // the rows before the first cut over tightened root bounds, or -1 when there is none
  private int tightFrom = -1;
  // the root level was removed after cuts over its tightened bounds: they no longer hold
  private boolean tightLost;
  // whether the restart solve under way is at the root level itself
  private boolean restartAtRoot;

  /** Statistics: whether the root level was removed after cuts over its tightened bounds. */
  public boolean restartBoundsLost() {
    return tightLost;
  }

  /** Statistics: cuts made at restarts over the tightened bounds of the root level. */
  public long restartBoundCuts;

  /** Statistics: the bound of the last restart solve whose cut rounds ran, or NaN. */
  public double restartCutBound = Double.NaN;

  // root reduced-cost fixing (SCIP's prop_rootredcost): the inequalities of the duals of the last
  // optimal solve at the root level are combinations of the rows, so they hold in the whole search;
  // propagated again at the root level whenever the bound of the objective has improved, they fix
  // the columns whose reduced cost no longer fits in the gap. Only there: propagated at every call
  // they cost more than they prune (bus_scheduling, osolpro #169)
  private static final boolean ROOT_REDUCED_COSTS =
      !FALSE.equals(System.getProperty("org.jacop.lp.rootReducedCosts"));
  private LinearForm[] rootForms = new LinearForm[0];
  // the certificate of each root form, for a proof, or null
  private Certificate[] rootCertificates = new Certificate[0];
  // the LP-only column facts of each root form, for its explanation
  private int[][] rootFacts = new int[0][];
  // the bounds of the objective that the root forms were propagated with on the current branch,
  // and the levels they were propagated at, a trail undone by removeLevel
  private long[] rootBoundsAt = new long[8];
  private int[] rootBoundsLevel = new int[8];
  private int rootBoundsSize;
  private long[] solvedLo;
  private long[] solvedHi;

  // the simplex at the optimum of the last solve at the root level, with as many rows as it had
  // then: a solve at a restart starts from its basis instead of the one search left, which is far
  // from the root (table-layout: a restart solve took as long as the first one)
  private static final boolean RESTART_FROM_ROOT =
      !FALSE.equals(System.getProperty("org.jacop.lp.restartFromRoot"));
  private int restartPeriod = 1;
  private int restartsWaited;
  private LpSolver rootSimplex;
  private int rootSimplexRows;
  // the model row of each simplex row of that copy: the row pool may have swapped rows since
  private int[] rootSimplexLpRows;

  /** Statistics: bounds tightened by the root reduced costs at restarts. */
  public long rootPrunings;

  /**
   * Creates the relaxation of linear forms.
   *
   * @param forms the rows; forms with relation {@code !=} and forms with fewer than two nonzero
   *     weights (after merging duplicate variables) are left out, so the model must enforce them
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   */
  public LinearRelaxation(Collection<LinearForm> forms, IntVar objective, boolean maximize) {
    this(forms, objective, maximize, Simplex.DENSE);
  }

  /**
   * Creates the relaxation of linear forms, solved by the given simplex.
   *
   * @param forms the rows; forms with relation {@code !=} and forms with fewer than two nonzero
   *     weights (after merging duplicate variables) are left out, so the model must enforce them
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   * @param simplex the simplex
   */
  public LinearRelaxation(
      Collection<LinearForm> forms, IntVar objective, boolean maximize, Simplex simplex) {
    this(forms, List.of(), objective, maximize, simplex);
  }

  /**
   * Creates the relaxation of linear forms and of further rows, such as the rows of constraints
   * that are not linear relations, solved by the given simplex. The further rows are added at the
   * first solve and kept only when they raise the bound of the objective, make the relaxation
   * infeasible, or are at most {@code org.jacop.lp.smallExtra} (100) rows; with lazy rows they are
   * rows like the others.
   *
   * @param forms the rows; forms with relation {@code !=} and forms with fewer than two nonzero
   *     weights (after merging duplicate variables) are left out, so the model must enforce them
   * @param extra the further rows
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   * @param simplex the simplex
   */
  public LinearRelaxation(
      Collection<LinearForm> forms,
      Collection<LinearForm> extra,
      IntVar objective,
      boolean maximize,
      Simplex simplex) {
    numberId = idNumber.incrementAndGet();
    this.simplex = simplex;
    this.createdWith = simplex;
    this.objective = objective;
    this.maximize = maximize;
    Map<IntVar, Integer> column = new IdentityHashMap<>();
    List<IntVar> columns = new ArrayList<>();
    List<int[]> rc = new ArrayList<>();
    List<long[]> rw = new ArrayList<>();
    List<long[]> sides = new ArrayList<>();
    if (objective != null) {
      column.put(objective, 0);
      columns.add(objective);
    }
    List<LinearForm> all = new ArrayList<>(forms);
    all.addAll(extra);
    // with lazy rows the further rows are rows like the others
    int given = simplex == Simplex.LAZY ? all.size() : forms.size();
    int base = 0;
    // the columns of the given rows come first: the simplex without the further rows has only these
    int baseColumns = columns.size();
    for (int index = 0; index < all.size(); index++) {
      LinearForm f = all.get(index);
      if (f == null || f.relation() == LinearForm.NE) {
        continue;
      }
      // duplicates merged, zero weights dropped
      Map<Integer, Long> merged = new LinkedHashMap<>();
      boolean overflow = false;
      for (int k = 0; k < f.vars().length; k++) {
        IntVar v = f.vars()[k];
        Integer j = column.get(v);
        if (j == null) {
          j = columns.size();
          column.put(v, j);
          columns.add(v);
        }
        long w = merged.getOrDefault(j, 0L);
        try {
          merged.put(j, Math.addExact(w, f.weights()[k]));
        } catch (ArithmeticException _) {
          overflow = true;
        }
      }
      if (index < given) {
        baseColumns = columns.size();
      }
      merged.values().removeIf(w -> w == 0);
      // rows over fewer than two columns are left out (see the constructors); the model enforces
      // them
      if (overflow || merged.size() < 2) {
        continue;
      }
      if (index < given) {
        this.forms.add(f);
        base++;
      } else {
        extraForms.add(f);
      }
      int[] cs = new int[merged.size()];
      long[] ws = new long[merged.size()];
      int k = 0;
      for (Map.Entry<Integer, Long> e : merged.entrySet()) {
        cs[k] = e.getKey();
        ws[k++] = e.getValue();
      }
      rc.add(cs);
      rw.add(ws);
      sides.add(new long[] {f.relation(), f.c()});
    }
    x = columns.toArray(new IntVar[0]);
    lpOnly = new boolean[x.length];
    for (int j = 0; j < x.length; j++) {
      lpOnly[j] = x[j] instanceof LpColumn;
      if (lpOnly[j] && ((LpColumn) x[j]).isFree()) {
        freeColumns++;
      } else if (lpOnly[j]) {
        valueColumns++;
      }
    }
    // a free column (a wire of a sorting network, the objective of a refutation) has no value
    // either: a row over it is not checked on a ground assignment
    anyLpOnly = valueColumns > 0 || freeColumns > 0;
    int further = rc.size() - base;
    extraColumns = rc.subList(base, rc.size()).toArray(new int[0][]);
    extraWeights = rw.subList(base, rw.size()).toArray(new long[0][]);
    extraSide = new long[further];
    extraRelation = new int[further];
    for (int i = 0; i < further; i++) {
      extraRelation[i] = (int) sides.get(base + i)[0];
      extraSide[i] = sides.get(base + i)[1];
    }
    int m = base;
    rowColumns = rc.subList(0, m).toArray(new int[0][]);
    rowWeights = rw.subList(0, m).toArray(new long[0][]);
    setRows = setRows(m);
    rowLo = new long[m];
    rowHi = new long[m];
    hasLo = new boolean[m];
    hasHi = new boolean[m];
    double[] lo = new double[m];
    double[] hi = new double[m];
    for (int i = 0; i < m; i++) {
      int rel = (int) sides.get(i)[0];
      long c = sides.get(i)[1];
      hasLo[i] = rel != LinearForm.LE;
      hasHi[i] = rel != LinearForm.GE;
      rowLo[i] = c;
      rowHi[i] = c;
      lo[i] = hasLo[i] ? c : Double.NEGATIVE_INFINITY;
      hi[i] = hasHi[i] ? c : Double.POSITIVE_INFINITY;
    }
    double[] cost = new double[baseColumns];
    if (objective != null) {
      cost[0] = maximize ? -1 : 1;
    }
    int n = baseColumns;
    lp =
        switch (simplex) {
          case DENSE -> {
            double[][] a = new double[m][n];
            for (int i = 0; i < m; i++) {
              for (int k = 0; k < rowColumns[i].length; k++) {
                a[i][rowColumns[i][k]] = rowWeights[i][k];
              }
            }
            yield new DualSimplex(a, lo, hi, cost);
          }
          case SPARSE -> sparse(sparseRows(m), doubles(m), lo, hi, cost);
          case LAZY -> sparse(new int[0][], new double[0][], lo, hi, cost);
        };
    if (simplex == Simplex.LAZY) {
      lpRow = new int[0];
      inLp = new boolean[m];
      inactive = new int[0];
      dormant = m;
    } else {
      allRowsInSimplex(m);
      baseCount = m;
    }
    queueIndex = 4;
    // the auxiliary columns are not variables of the store: their variables are in the scope, as
    // the bounds of a column in the simplex come from the domain of its variable
    setScope(
        Arrays.stream(x)
            .filter(v -> !(v instanceof LpColumn c) || !c.isFree())
            .map(v -> v instanceof LpColumn c ? c.variable() : v)
            .distinct()
            .map(v -> (Var) v));
  }

  // the sparse simplex, JaLP's
  private static LpSolver sparse(
      int[][] columns, double[][] weights, double[] lo, double[] hi, double[] cost) {
    return new JalpSimplex(columns, weights, lo, hi, cost);
  }

  /**
   * Creates the relaxation of the linear constraints of a store: the constraints {@link
   * LinearForms#of} reads as linear relations.
   *
   * @param store the store
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   * @return the relaxation, or null when the store has fewer than two rows or the tableau would
   *     have more than {@code org.jacop.lp.maxTableau} (4,000,000) entries
   */
  public static LinearRelaxation of(Store store, IntVar objective, boolean maximize) {
    return of(store, objective, maximize, List.of(), Set.of(), Simplex.DENSE);
  }

  /**
   * Creates the relaxation of the linear constraints of a store, solved by the given simplex.
   *
   * @param store the store
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   * @param simplex the simplex
   * @return the relaxation, or null when the store has fewer than two rows, or the dense tableau
   *     would have more than {@code org.jacop.lp.maxTableau} (4,000,000) entries, or the rows of a
   *     sparse simplex more than {@code org.jacop.lp.maxNonzeros} (4,000,000) nonzeros
   */
  public static LinearRelaxation of(
      Store store, IntVar objective, boolean maximize, Simplex simplex) {
    return of(store, objective, maximize, List.of(), Set.of(), simplex);
  }

  /**
   * Creates the relaxation of the linear constraints of a store with the dense simplex, with rows
   * that are not store constraints and with variables substituted by their definitions.
   *
   * @param store the store
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   * @param extra rows to add to those of the store's constraints
   * @param substituted variables to replace by their definitions
   * @return the relaxation, or null when it has fewer than two rows or the tableau would have more
   *     than {@code org.jacop.lp.maxTableau} (4,000,000) entries
   */
  public static LinearRelaxation of(
      Store store,
      IntVar objective,
      boolean maximize,
      Collection<LinearForm> extra,
      Set<? extends IntVar> substituted) {
    return of(store, objective, maximize, extra, substituted, Simplex.DENSE);
  }

  /**
   * Creates the relaxation of the linear constraints of a store, with rows that are not store
   * constraints and with variables substituted by their definitions, solved by the given simplex.
   *
   * <p>The extra rows are relations implied by the model that the store holds elsewhere, such as
   * the clauses that lazy clause generation hands to the SAT solver. They are added at the first
   * solve together with the linearized rows of the other constraints, and kept on the same terms. A
   * substituted variable {@code s} has a definition, an equality row {@code sum a x + w s = c} with
   * {@code w} = 1 or -1 among the rows; the definition is dropped and {@code s} is replaced by
   * {@code w (c - sum a x)} in the other rows. The block sums of a long linear constraint split for
   * lazy clause generation are such variables: substituting them gives the constraint back as one
   * row, so the relaxation has the rows and columns of the unsplit model. A variable without a
   * definition, the objective, and every variable when a substitution overflows a {@code long} are
   * left as they are.
   *
   * @param store the store
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   * @param extra rows to add to those of the store's constraints
   * @param substituted variables to replace by their definitions
   * @param simplex the simplex
   * @return the relaxation, or null when it has fewer than two rows, or the dense tableau would
   *     have more than {@code org.jacop.lp.maxTableau} (4,000,000) entries, or the rows of a sparse
   *     simplex more than {@code org.jacop.lp.maxNonzeros} (4,000,000) nonzeros
   */
  public static LinearRelaxation of(
      Store store,
      IntVar objective,
      boolean maximize,
      Collection<LinearForm> extra,
      Set<? extends IntVar> substituted,
      Simplex simplex) {
    return of(store, objective, maximize, extra, List.of(), substituted, simplex);
  }

  /**
   * Creates the relaxation of {@link #of(Store, IntVar, boolean, Collection, Set, Simplex)} with
   * further rows that are tried at the first solve like the value encodings of the constraints, and
   * kept only when they raise the bound of the objective or make the relaxation infeasible, such as
   * the convex hulls of tables ({@link org.jacop.constraints.TableCliques}). They have a share of
   * the size cap of the sparse simplex of their own, so that the other rows do not leave them out.
   *
   * @param store the store
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   * @param extra rows to add to those of the store's constraints
   * @param tried rows tried at the first solve after the others
   * @param substituted variables to replace by their definitions
   * @param simplex the simplex
   * @return the relaxation, or null as for {@link #of(Store, IntVar, boolean, Collection, Set,
   *     Simplex)}
   */
  public static LinearRelaxation of(
      Store store,
      IntVar objective,
      boolean maximize,
      Collection<LinearForm> extra,
      Collection<LinearForm> tried,
      Set<? extends IntVar> substituted,
      Simplex simplex) {
    Set<Constraint> constraints = constraintsOf(store);
    List<LinearForm> localForms = new ArrayList<>();
    List<LinearForm> relaxed = new ArrayList<>();
    // the rows of relaxed that go ahead of the others when not all fit
    Set<LinearForm> leading = Set.of();
    // the value encodings of the model's variables (sum b_v = 1, x = sum v b_v)
    Set<LinearForm> encodingSet = Collections.newSetFromMap(new IdentityHashMap<>());
    boolean encodingsLead = false;
    int valueCliqueRows = 0;
    List<CapacityCuts> separations = new ArrayList<>();
    int arcTimeCount = 0;
    List<EnergyCuts> resources = new ArrayList<>();
    List<AlldifferentCuts> hall = new ArrayList<>();
    List<TreeCuts> trees = new ArrayList<>();
    Map<LinearForm, String> tags = new IdentityHashMap<>();
    // the element constraints whose value encodings give their convex hull: their own hull rows
    // are left out (gap of the OR-Library: 836 hull rows next to 400 encoding rows, which made the
    // dense trial of the further rows stop at its pivot limit and keep none)
    Set<Constraint> linked = Collections.newSetFromMap(new IdentityHashMap<>());
    List<LinearForm> encodings = new ArrayList<>();
    if (LINEARIZE) {
      encodings.addAll(Linearizations.encodings(constraints, encodingRowsOn ? linked : null));
    }
    for (Constraint c : constraints) {
      TreeCuts forest = TREE_CUTS && objective != null ? TreeCuts.of(c) : null;
      if (forest != null) {
        trees.add(forest);
      }
      AlldifferentCuts distinct =
          ALLDIFF_CUTS && objective != null ? Linearizations.hallCuts(c, ALLDIFF_VARIANTS) : null;
      if (distinct != null) {
        hall.add(distinct);
      }
      if (CAPACITY_CUTS && c instanceof Routes routes) {
        separations.add(new CapacityCuts(routes));
      }
      if (ARC_TIME_ROWS && objective != null && c instanceof Routes routes) {
        List<LinearForm> rows = CapacityCuts.arcTimeRows(routes, store.level == 0);
        if (ARC_TIME_TRIED) {
          relaxed.addAll(rows);
        } else {
          localForms.addAll(rows);
        }
        tag(tags, rows, "arcTime");
        arcTimeCount += rows.size();
      }
      if (ENERGY_CUTS && objective != null) {
        EnergyCuts e = energyCuts(c);
        if (e != null) {
          resources.add(e);
        }
      }
      LinearForm f = LinearForms.of(c);
      if (f != null && store.isOptionalRow(c)) {
        // tried like the clauses: the 84,897 dominance nogoods of knapPI similar_weights (5,000
        // items) made the relaxation large, solved at the root only, and search lost its bound
        relaxed.add(f);
        tags.put(f, "optional:" + c.getClass().getSimpleName());
      } else if (f != null && f.relation() != LinearForm.NE && f.vars().length > 1) {
        localForms.add(f);
        tags.put(f, "row:" + c.getClass().getSimpleName());
      } else if (f == null && LINEARIZE && !linked.contains(c)) {
        List<LinearForm> rows = Linearizations.of(c);
        relaxed.addAll(rows);
        tag(tags, rows, "lin:" + c.getClass().getSimpleName());
      }
    }
    // like the linearized rows, they are kept only when they help the root relaxation: the
    // clauses of lazy clause generation make thousands of rows on some models (rel2onto: 65 rows
    // become 1,135), and a relaxation that large stalls at its pivot limit and prunes nothing
    for (LinearForm f : extra) {
      if (f != null) {
        relaxed.add(f);
        tags.putIfAbsent(f, "given");
      }
    }
    int pairCliques = 0;
    // for an objective only, whose bound they raise: on satisfaction models (rubik) the longer
    // rows only make each call dearer
    if (PAIR_CLIQUES && objective != null) {
      PairCliques merged = PairCliques.merge(localForms, relaxed);
      localForms = merged.rows;
      relaxed = merged.further;
      pairCliques = merged.cliques;
      tag(tags, localForms, "clique");
      tag(tags, relaxed, "clique");
    }
    if (!substituted.isEmpty()) {
      localForms = substitute(localForms, substituted, objective);
      tag(tags, localForms, "substituted");
    }
    if (LINEARIZE) {
      if (objective != null) {
        List<LinearForm> cliques =
            Linearizations.valueCliques(constraints, List.of(localForms, relaxed));
        valueCliqueRows = cliques.size();
        encodings.addAll(cliques);
      }
      encodingSet.addAll(encodings);
      List<LinearForm> selected = Linearizations.selectedValueRows(constraints, extra);
      tag(tags, encodings, "encoding");
      tag(tags, selected, "valueConj");
      if (selected.isEmpty()) {
        relaxed.addAll(encodings);
      } else {
        // the rows of the value conjunctions first, and the value encodings with them, also when
        // not all rows fit: at the distance of the clause rows of their Booleans from the
        // objective they came after those and did not fit the share (ihtc-2024-kletzander: root
        // bound 0, and 4,757 with the conjunction rows alone, since sum e_v = 1 of the patients
        // that must be admitted was left out)
        relaxed.addAll(0, encodings);
        relaxed.addAll(0, selected);
        leading = Collections.newSetFromMap(new IdentityHashMap<>());
        leading.addAll(selected);
        leading.addAll(encodings);
      }
    }
    // the value encodings over auxiliary columns come first, so that a size cap leaves out other
    // rows before them; they are many rows by nature (a row per value and constraint) and are not
    // held to the trial cap of the sparse simplex chosen by size. The further encodings, tried at
    // the first solve, are made only for an objective: they are kept when they raise its bound or
    // make the LP infeasible, and without an objective only the latter is left: rows kept for one
    // infeasible LP then slow every solve and move the search path (sudoku_fixed p28)
    Linearizations.ValueRows valueRows =
        LINEARIZE
            ? Linearizations.valueRows(constraints, extra, objective != null)
            : new Linearizations.ValueRows(List.of(), List.of());
    List<LinearForm> columnRows = valueRows.kept();
    tag(tags, columnRows, "valueColumns");
    tag(tags, valueRows.tried(), "valueTried");
    tag(tags, valueRows.flow(), "flow");
    tag(tags, tried, "tableCliques");
    List<LinearForm> candidates = new ArrayList<>();
    int exempt = 0;
    for (LinearForm f : columnRows) {
      if (Arrays.stream(f.vars()).noneMatch(substituted::contains)) {
        candidates.add(f);
        exempt++;
      }
    }
    // the rows of the other constraints; rows over a variable that was substituted away are left
    // out
    // the value encodings of the counting, all-different and element constraints come last: they
    // are tried at the first solve like the other rows, and kept only when they help
    List<LinearForm> ownTried = objective == null ? List.of() : new ArrayList<>(tried);
    // the clauses of the tables over 0/1 variables, tried with the table rows: on Fortress (walls
    // that enclose points of a grid) they make the relaxation the vertex cut LP, whose bound is the
    // fewest walls; without them the tables gave the relaxation no row. A table whose variables
    // are all in the given tried rows has its convex hull over tuple columns there (TableCliques),
    // which implies each of its clauses: the clauses of the xor tables of DC only slowed the first
    // solve and moved the search
    int tableClauses = 0;
    if (TABLE_CLAUSES && objective != null) {
      List<LinearForm> clauseRows = new ArrayList<>();
      Set<IntVar> inTried = Collections.newSetFromMap(new IdentityHashMap<>());
      for (LinearForm f : tried) {
        inTried.addAll(Arrays.asList(f.vars()));
      }
      for (Constraint c : constraints) {
        if (c instanceof HybridTable h
            && !h.arguments().stream()
                .allMatch(v -> v.singleton() || v instanceof IntVar i && inTried.contains(i))) {
          List<LinearForm> rows = h.clauseRows();
          clauseRows.addAll(rows);
          tag(tags, rows, "tableClause");
        }
      }
      // more rows than the trial takes in proportion: DC-midori r14, 76,036 rows over the tables
      // past the hull cap, never raised the bound and slowed its first solutions
      if (clauseRows.size() <= MAX_TABLE_CLAUSES) {
        ownTried.addAll(clauseRows);
        tableClauses = clauseRows.size();
      }
    }
    List<LinearForm> triedRows = new ArrayList<>(valueRows.tried());
    triedRows.addAll(ownTried);
    // the sorting networks of the all-different permutations are tried like the value encodings,
    // for an objective only, whose bound they raise
    if (LINEARIZE && objective != null) {
      List<LinearForm> networks = Linearizations.alldifferentNetworks(constraints);
      triedRows.addAll(networks);
      tag(tags, networks, "alldiffNetwork");
    }
    // the candidates that keep their place ahead of the others when not all fit
    int first = exempt;
    for (List<LinearForm> rows : List.of(relaxed, triedRows, valueRows.flow())) {
      for (LinearForm f : rows) {
        if (f.relation() != LinearForm.NE
            && f.vars().length >= 2
            && Arrays.stream(f.vars()).noneMatch(substituted::contains)) {
          candidates.add(f);
          first += leading.contains(f) && first == candidates.size() - 1 ? 1 : 0;
        }
      }
    }
    Set<LinearForm> triedSet = Collections.newSetFromMap(new IdentityHashMap<>());
    triedSet.addAll(triedRows);
    triedSet.addAll(valueRows.flow());
    Set<LinearForm> own = Collections.newSetFromMap(new IdentityHashMap<>());
    own.addAll(ownTried);
    Set<LinearForm> flow = Collections.newSetFromMap(new IdentityHashMap<>());
    flow.addAll(valueRows.flow());
    boolean auto = simplex == Simplex.DENSE && SPARSE_ROWS >= 0;
    boolean large = false;
    if (auto && !sparseTakes(localForms)) {
      // too large for the sparse simplex in search: a large relaxation, solved at the root only, or
      // the dense one, or no relaxation over its cap. Only for an objective: without one a root
      // solve can only find infeasibility (debruijn-binary, nmseq and slow-convergence of the
      // Challenge: 1-5 s more start-up, no change in search)
      large = objective != null && largeTakes(localForms);
      auto = large;
    }
    if (auto
        && (large
            || localForms.size() >= SPARSE_ROWS
            || tableClauses >= SPARSE_ROWS
            || tooLarge(localForms, Simplex.DENSE))) {
      // the dense tableau costs rows times columns per pivot, the sparse simplex its nonzeros: the
      // dense one is kept for small relaxations, where it is as fast, and the sparse one takes the
      // larger ones, also those over the dense size cap, which would get no relaxation at all
      simplex = Simplex.SPARSE;
    }
    // the value encodings of the model's own Booleans count like the exempt rows: on a model that
    // states an assignment by Booleans (x = v) the encodings are its assignment and cost rows, and
    // a dense trial of them at the first solve stopped at its pivot limit (gapd 10x200 of the
    // OR-Library: 800 encoding rows over 2,601 columns, 360 pivots, all rows dropped and the root
    // bound 3,738 instead of 12,4xx)
    int encoded = 0;
    boolean bySparse = false;
    if (encodingRowsOn && auto && simplex == Simplex.DENSE && !encodingSet.isEmpty()) {
      for (LinearForm f : candidates) {
        encoded += encodingSet.contains(f) ? 1 : 0;
      }
    }
    if (auto && simplex == Simplex.DENSE && (exempt > 0 || encoded > 0)) {
      List<LinearForm> withColumns = new ArrayList<>(localForms);
      withColumns.addAll(candidates.subList(0, exempt));
      if (localForms.size() + exempt + encoded >= SPARSE_ROWS
          || tooLarge(withColumns, Simplex.DENSE)) {
        bySparse = encoded > 0;
        // the encodings are rows of the model as a MIP states it: the simplex is chosen by their
        // count too, and the sparse one takes them all when the dense tableau cannot
        simplex = Simplex.SPARSE;
      }
    }
    if (tooLarge(localForms, simplex)) {
      return null;
    }
    List<LinearForm> further = new ArrayList<>();
    int nearRows = 0;
    // the further rows are tried at the first solve over every column; on the sparse simplex
    // chosen by size at most twice the given rows and org.jacop.lp.sparseRows more, so that the
    // trial stays in proportion to the relaxation (a trial over every candidate of a large model
    // can take a minute and then drop them all)
    // a model with trees takes all its other rows: the tree cuts need them (st70 of
    // surface-based-tsp: 388 of its 561 other rows fit the share, root bound 490 and 633 after
    // the tree cuts; all of them, 656 and 675, the optimum)
    // the leading rows of the value conjunctions are counted like the exempt ones, outside the
    // share of the others (ihtc-2024-kletzander test05: 412 leading rows of a share of 472 left out
    // the count row of the objective, and the root bound stayed 0)
    // the encodings that chose the sparse simplex are counted outside the share too (gapd 10x200:
    // a share of 124 rows took 124 of its 800 encoding rows, root bound 3,746)
    long share =
        trees.isEmpty()
            ? 2L * localForms.size()
                + SPARSE_ROWS
                + first
                + (bySparse && leading.isEmpty() ? encoded : 0)
            : Long.MAX_VALUE;
    if (!fitsSimplex(localForms, candidates, simplex, auto, share, own, further)
        && objective != null) {
      // not all fit: after the value encodings, the rows nearest to the objective first, since rows
      // far from it rarely move its bound (tiny-cvrp: 852 of 6,936 rows, those over the variables
      // of the rows of the objective, give the whole bound, and in model order they came too late
      // to fit); the tried value encodings stay after the other rows, since the retry without them
      // takes the rows before them
      further.clear();
      List<LinearForm> sorted = fitOrder(localForms, candidates, first, triedSet, flow, objective);
      if (LEAD_ENCODINGS && !encodingSet.isEmpty() && first < candidates.size()) {
        // the value encodings of the model's variables go right after the leading rows: they are
        // the rows of the model as a MIP states it (each variable takes one value), and among
        // many linearized rows they come late by distance and miss the share. Without them the
        // relaxation can leave every Boolean of a variable at 0 (ROADEF 2020 maintenance
        // planning A_01: 27,276 candidates for a share of 3,484 rows, the 543 encodings left
        // out, root bound the domain bound 31,652,095 with zero duals; with them 31,737,934)
        List<LinearForm> head = new ArrayList<>(sorted.subList(0, first));
        List<LinearForm> enc = new ArrayList<>();
        List<LinearForm> rest = new ArrayList<>();
        for (LinearForm f : sorted.subList(first, sorted.size())) {
          (encodingSet.contains(f) ? enc : rest).add(f);
        }
        if (!enc.isEmpty() && head.isEmpty()) {
          sorted = new ArrayList<>(enc);
          sorted.addAll(rest);
          encodingsLead = true;
          // they are counted like the leading rows, outside the share of the others
          share = share == Long.MAX_VALUE ? share : share + enc.size();
        }
      }
      boolean fitted = fitsSimplex(localForms, sorted, simplex, auto, share, own, further);
      if (!fitted && nearRowsOn && auto && (simplex == Simplex.DENSE || bySparse)) {
        // the rows over the terms of the objective do not fit the dense tableau (or the share of
        // the sparse simplex that the value encodings chose): the sparse simplex takes them all,
        // as many as they are. A model stated in clauses has few rows of
        // its own, and their share left out the rows that bound the objective (CSPLib warehouses
        // cap131: 2 rows of its own, and the clauses b[i,j] -> open[j] with the element costs as
        // value encodings, 3,826 rows, raise the root bound from 626,300 to 914,788, opt 915,059)
        // at most as many as a sparse relaxation in search has rows: pattern-set-mining-k1
        // ionosphere has 110,602 such rows, whose trial took 15 s and did not raise the bound
        Set<LinearForm> near = nearObjective(localForms, sorted, triedSet, objective);
        List<LinearForm> sparse = new ArrayList<>();
        // the value encodings that went ahead come before the near rows: those of them that are
        // not near rows are counted on top (NearRowsTest, 40 stores: with the element hull rows
        // left out for the encodings, the 40 rows sum b = 1 went ahead of the 1,680 near rows and
        // pushed 40 of them out of the share, root bound 8,009 instead of 15,057)
        int ahead = 0;
        for (int k = first; encodingsLead && k < sorted.size(); k++) {
          LinearForm f = sorted.get(k);
          if (!encodingSet.contains(f)) {
            break;
          }
          ahead += near.contains(f) ? 0 : 1;
        }
        long nearShare = Math.max(share, (long) first + near.size() + ahead);
        fitsSimplex(localForms, sorted, Simplex.SPARSE, true, nearShare, own, sparse);
        if (localForms.size() + near.size() <= sparseMaxRows
            && containsAll(sparse, near)
            && !containsAll(further, near)) {
          further = sparse;
          simplex = Simplex.SPARSE;
          nearRows = near.size();
        }
      }
    }
    LinearRelaxation r = new LinearRelaxation(localForms, further, objective, maximize, simplex);
    r.nearRows = nearRows;
    r.bySize = auto && simplex == Simplex.SPARSE;
    r.large = large && simplex == Simplex.SPARSE;
    // the encodings that chose the sparse simplex are the model's rows as well: the solves in
    // search get the pivots of the sparse simplex, not those of the dense tableau they would make
    // (gapd
    // 10x200: 7 pivots a solve, every one stopped at the limit and the relaxation stalled after 32)
    r.keepEncodings = exempt > 0 || bySparse;
    r.plainExtra = (int) r.extraForms.stream().filter(f -> !triedSet.contains(f)).count();
    r.triedExtra = (int) r.extraForms.stream().filter(f -> !flow.contains(f)).count();
    if (encodingsLead) {
      int lead = 0;
      while (lead < r.extraForms.size() && encodingSet.contains(r.extraForms.get(lead))) {
        lead++;
      }
      r.leadExtra = lead;
      r.leadEncodings = lead;
    }
    r.valueCliques = valueCliqueRows;
    r.pairCliques = pairCliques;
    r.encodedElements = linked.size();
    r.encodingsSparse = bySparse;
    r.tableClauses = tableClauses;
    r.formSource = tags;
    r.capacity = separations;
    r.arcTimeRows = arcTimeCount;
    r.energy = resources;
    r.hall = hall;
    r.trees = trees;
    return r.rows() + r.extraColumns.length < 2 ? null : r;
  }

  // the source of each of the forms that has none yet
  private static void tag(
      Map<LinearForm, String> tags, Collection<LinearForm> forms, String source) {
    for (LinearForm f : forms) {
      tags.putIfAbsent(f, source);
    }
  }

  /**
   * Returns the energy cuts of a cumulative resource, over its tasks of positive least duration and
   * usage, or null for another constraint, a resource with optional tasks, or fewer than two such
   * tasks. The least durations, usages and the capacity are those of now, the root.
   */
  private static EnergyCuts energyCuts(Constraint c) {
    if (!(c instanceof CumulativeBasic cb)
        || c instanceof CumulativeOptional
        || c instanceof CumulativeUnaryOptional
        || cb.limit().max() <= 0) {
      return null;
    }
    IntVar[][] t = cb.tasks();
    List<IntVar> starts = new ArrayList<>();
    List<long[]> sizes = new ArrayList<>();
    for (int i = 0; i < t[0].length; i++) {
      if (t[1][i].min() > 0 && t[2][i].min() > 0) {
        starts.add(t[0][i]);
        sizes.add(new long[] {t[1][i].min(), t[2][i].min()});
      }
    }
    if (starts.size() < 2) {
      return null;
    }
    long[] dur = new long[starts.size()];
    long[] use = new long[starts.size()];
    for (int k = 0; k < dur.length; k++) {
      dur[k] = sizes.get(k)[0];
      use[k] = Math.min(sizes.get(k)[1], cb.limit().max());
    }
    return new EnergyCuts(starts.toArray(new IntVar[0]), dur, use, cb.limit().max());
  }

  /**
   * Returns the candidates in the order they are fitted when not all fit: the first exempt ones as
   * they are, then the others by their distance from the objective, the tried ones last.
   */
  static List<LinearForm> fitOrder(
      List<LinearForm> forms,
      List<LinearForm> candidates,
      int exempt,
      Set<LinearForm> tried,
      IntVar objective) {
    return fitOrder(forms, candidates, exempt, tried, Set.of(), objective);
  }

  /**
   * Returns the candidates in the order they are fitted when not all fit: the first exempt ones as
   * they are, then the others by their distance from the objective, the tried ones after them and
   * the flow models of layered graphs (a subset of the tried ones) last.
   */
  static List<LinearForm> fitOrder(
      List<LinearForm> forms,
      List<LinearForm> candidates,
      int exempt,
      Set<LinearForm> tried,
      Set<LinearForm> flow,
      IntVar objective) {
    List<LinearForm> plainRows = new ArrayList<>();
    List<LinearForm> triedRows = new ArrayList<>();
    List<LinearForm> flowRows = new ArrayList<>();
    for (LinearForm f : candidates.subList(exempt, candidates.size())) {
      if (flow.contains(f)) {
        flowRows.add(f);
      } else {
        (tried.contains(f) ? triedRows : plainRows).add(f);
      }
    }
    List<LinearForm> sorted = new ArrayList<>(candidates.subList(0, exempt));
    sorted.addAll(byDistance(forms, plainRows, objective));
    sorted.addAll(byDistance(forms, triedRows, objective));
    sorted.addAll(byDistance(forms, flowRows, objective));
    return sorted;
  }

  /**
   * Creates the relaxation that a VeriPB proof can follow: its rows are the relations of the
   * constraints whose proof model is that relation as a line ({@link LinearForms#ofModelLine}),
   * with no rows of other constraints, no substitution and no cuts, and every deduction keeps the
   * combination of rows it comes from ({@link #certificate()}). The deductions are not divided by
   * the greatest common divisor of their weights, which changes no bound they propagate.
   *
   * @param store the store
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   * @param simplex the simplex; the dense one is replaced by the sparse one from {@code
   *     org.jacop.lp.sparseRows} (100) rows, as in {@link #of}
   * @return the relaxation, or null when it has fewer than two rows or is too large
   */
  public static LinearRelaxation ofModel(
      Store store, IntVar objective, boolean maximize, Simplex simplex) {
    List<LinearForm> localForms = new ArrayList<>();
    Map<LinearForm, Constraint> source = new IdentityHashMap<>();
    for (Constraint c : constraintsOf(store)) {
      LinearForm f = LinearForms.ofModelLine(c);
      if (f != null && f.relation() != LinearForm.NE && f.vars().length > 1) {
        localForms.add(f);
        source.put(f, c);
      }
    }
    if (simplex == Simplex.DENSE
        && SPARSE_ROWS >= 0
        && sparseTakes(localForms)
        && (localForms.size() >= SPARSE_ROWS || tooLarge(localForms, Simplex.DENSE))) {
      simplex = Simplex.SPARSE;
    }
    if (tooLarge(localForms, simplex)) {
      return null;
    }
    LinearRelaxation r = new LinearRelaxation(localForms, List.of(), objective, maximize, simplex);
    r.rowSource = new Constraint[r.forms.size()];
    for (int i = 0; i < r.rowSource.length; i++) {
      r.rowSource[i] = source.get(r.forms.get(i));
    }
    r.cutsTried = true;
    return r.rows() < 2 ? null : r;
  }

  /**
   * Creates the relaxation that tries to refute a satisfaction model at the root: the value
   * encodings of the counting, all-different and element constraints ({@link
   * Linearizations#refutationRows}), the linear rows and clause rows of the model restated over the
   * value columns, and the conflicts of pairs of 0/1 literals merged into cliques. It is solved
   * once, at the root, and then removed: an infeasible relaxation proves that the model has no
   * solution, and a feasible one would only slow every node down. The relaxation of the model
   * ({@link #of}) keeps these encodings only for an objective, since without one they can only make
   * an LP infeasible, and kept for one infeasible LP in search they slow every solve (see there);
   * here they cost one root solve.
   *
   * <p>A pigeonhole count is what the relaxation sees and propagation does not: in the social
   * golfers of the XCSP 2024 competition with 32 players in 8 groups of 4 over 11 weeks, player 0
   * meets 3 players a week, 33 in all, but only 31 others exist. The counts of the groups and the
   * cliques of "meets player 0 in week w" over the weeks give the LP 30 meetings for 28 players
   * after the fixed first week, and the LP is infeasible at once; the search found nothing in 600
   * s. Such counts are pigeonhole arguments, which resolution, and so lazy clause generation,
   * refutes only in exponentially many steps (A. Haken, "The intractability of resolution", TCS 39,
   * 1985), while the LP of the assignment rows with the clique rows of the conflict graph (A.
   * Atamtürk, G. L. Nemhauser and M. W. P. Savelsbergh, "Conflict graphs in solving integer
   * programming problems", EJOR 121, 2000) refutes them at once.
   *
   * @param store the store
   * @param clauses the clause rows of the clauses that lazy clause generation took
   * @return the relaxation, or null when there is no value encoding or the rows are too many
   */
  public static LinearRelaxation refutation(Store store, Collection<LinearForm> clauses) {
    return refutation(store, clauses, Set.of());
  }

  /**
   * Creates the relaxation that tries to refute a satisfaction model at the root, as {@link
   * #refutation(Store, Collection)}, with the block sums of split linear constraints replaced by
   * their definitions in the rows of a model with no value encoding ({@link
   * #pseudoObjectiveRefutation}), so that a long row of the model is one row again.
   *
   * @param store the store
   * @param clauses the clause rows of the clauses that lazy clause generation took
   * @param substituted variables to replace by their definitions
   * @return the relaxation, or null when there is no value encoding or the rows are too many
   */
  public static LinearRelaxation refutation(
      Store store, Collection<LinearForm> clauses, Set<? extends IntVar> substituted) {
    if (!ROOT_REFUTATION || !LINEARIZE) {
      return null;
    }
    Set<Constraint> constraints = constraintsOf(store);
    constraints.removeIf(c -> c instanceof LinearRelaxation);
    List<LinearForm> given = new ArrayList<>();
    for (Constraint c : constraints) {
      LinearForm f = LinearForms.of(c);
      if (f != null && f.relation() != LinearForm.NE && f.vars().length > 1) {
        given.add(f);
      }
    }
    for (LinearForm f : clauses) {
      if (f != null) {
        given.add(f);
      }
    }
    List<LinearForm> rows = Linearizations.refutationRows(constraints, given);
    if (rows.isEmpty()) {
      if (!PSEUDO_OBJECTIVE) {
        return null;
      }
      List<LinearForm> model = substituted.isEmpty() ? given : substitute(given, substituted, null);
      return pseudoObjectiveRefutation(model);
    }
    PairCliques merged = PairCliques.merge(rows, List.of());
    rows = merged.rows;
    Simplex simplex = sparseTakes(rows) ? Simplex.SPARSE : Simplex.DENSE;
    if (tooLarge(rows, simplex)) {
      return null;
    }
    LinearRelaxation r = new LinearRelaxation(rows, List.of(), null, false, simplex);
    r.refutation = true;
    r.pairCliques = merged.cliques;
    r.cutsTried = true;
    return r.rows() < 2 ? null : r;
  }

  /**
   * The refutation of a model with no value encoding, such as a pseudo-Boolean model: its linear
   * rows and clause rows, with the inequality {@code sum w x <= b} whose variables are in the most
   * rows as the objective. The root solve minimizes {@code t = sum w x} over a free column t in
   * [min, b] and its cut rounds raise that bound; the model has no solution when the relaxation, or
   * the relaxation with its cuts, is infeasible. Without an objective a relaxation has no cut
   * rounds, and its vertex is any point of the polytope; with the cardinality row of the model as
   * the objective the cuts work on the point that comes nearest to breaking it.
   *
   * <p>The pseudo-Boolean competition has such cardinality refutations: a vertex cover of at most k
   * vertices of a graph made of odd cycles (vc-lines), where the relaxation takes every vertex at
   * 1/2 and the Chvátal-Gomory and MIR cuts of the cycles (the odd-cycle inequalities, M. W.
   * Padberg, "On the facial structure of set packing polyhedra", Math. Programming 5, 1973) raise
   * the bound past k; and the pigeonhole principle (php), whose relaxation is infeasible as it is,
   * while resolution and so lazy clause generation refutes it only in exponentially many steps (A.
   * Haken, "The intractability of resolution", TCS 39, 1985). The relaxation of such a model is
   * often over the size caps of the relaxation in search (php 230/229: 52,670 columns); it is
   * solved once at the root here, within the pivot limit of the refutation.
   */
  // whether f states a clause over 0/1 variables: unit weights and the right-hand side that makes
  // one literal true enough, sum(positive) - sum(negative) >= 1 - |negative|, or its negation
  private static boolean isClause(LinearForm f) {
    long positive = 0;
    long negative = 0;
    for (int k = 0; k < f.vars().length; k++) {
      IntVar v = f.vars()[k];
      long w = f.weights()[k];
      if (Math.abs(w) != 1 || v.min() < 0 || v.max() > 1) {
        return false;
      }
      if (w > 0) {
        positive++;
      } else {
        negative++;
      }
    }
    return f.relation() == LinearForm.GE ? f.c() == 1 - negative : f.c() == positive - 1;
  }

  private static LinearRelaxation pseudoObjectiveRefutation(List<LinearForm> given) {
    // the inequality whose variables are in the most rows: the cardinality row over every vertex
    // of a vertex cover, the row that bounds the exits of the blocks of a pigeonhole formula with
    // exits (php-exit, each exit in the 93 pigeon rows of its block), not one of those rows
    Map<IntVar, Integer> occurrences = new IdentityHashMap<>();
    for (LinearForm f : given) {
      for (IntVar v : f.vars()) {
        occurrences.merge(v, 1, Integer::sum);
      }
    }
    LinearForm longest = null;
    long most = 0;
    for (LinearForm f : given) {
      if ((f.relation() == LinearForm.LE || f.relation() == LinearForm.GE)
          && f.vars().length >= PSEUDO_OBJECTIVE_LENGTH
          && !isClause(f)) {
        long incidence = 0;
        for (IntVar v : f.vars()) {
          incidence += occurrences.get(v);
        }
        if (incidence > most) {
          most = incidence;
          longest = f;
        }
      }
    }
    // no row but clauses: the relaxation of a formula in conjunctive normal form with clauses of at
    // least two literals takes every variable at 1/2, and its cuts are no stronger than resolution
    // (rubik of the Challenge, 22,410 clauses: 4.5 s for nothing)
    if (longest == null) {
      return null;
    }
    // sum w x <= b; a row >= is negated
    long sign = longest.relation() == LinearForm.LE ? 1 : -1;
    long[] w = new long[longest.vars().length];
    long lo = 0;
    long hi = 0;
    try {
      for (int k = 0; k < w.length; k++) {
        w[k] = Math.multiplyExact(sign, longest.weights()[k]);
        IntVar v = longest.vars()[k];
        long atMin = Math.multiplyExact(w[k], v.min());
        long atMax = Math.multiplyExact(w[k], v.max());
        lo = Math.addExact(lo, Math.min(atMin, atMax));
        hi = Math.addExact(hi, Math.max(atMin, atMax));
      }
    } catch (ArithmeticException _) {
      return null;
    }
    long b = Math.multiplyExact(sign, longest.c());
    if (lo < IntDomain.MIN_INT || Math.min(b, hi) > IntDomain.MAX_INT || lo > Math.min(b, hi)) {
      return null;
    }
    LpColumn t = new LpColumn("refutationObjective", (int) lo, (int) Math.min(b, hi));
    IntVar[] vars = Arrays.copyOf(longest.vars(), w.length + 1);
    vars[w.length] = t;
    long[] weights = Arrays.copyOf(w, w.length + 1);
    weights[w.length] = -1;
    List<LinearForm> rows = new ArrayList<>();
    rows.add(new LinearForm(vars, weights, 0, LinearForm.EQ));
    for (LinearForm f : given) {
      if (f != longest) {
        rows.add(f);
      }
    }
    PairCliques merged = PairCliques.merge(rows, List.of());
    rows = merged.rows;
    // solved once, within the pivot limit of the refutation: the sparse simplex also over the size
    // caps of the relaxation in search, up to those of a large relaxation
    Simplex simplex = sparseTakes(rows) || largeTakes(rows) ? Simplex.SPARSE : Simplex.DENSE;
    if (tooLarge(rows, simplex)) {
      return null;
    }
    LinearRelaxation r = new LinearRelaxation(rows, List.of(), t, false, simplex);
    r.refutation = true;
    r.pseudoObjective = true;
    r.pairCliques = merged.cliques;
    return r.rows() < 2 ? null : r;
  }

  /**
   * Creates the relaxation that tries to refute a model stated in clauses over 0/1 variables at the
   * root, as {@link #refutation} does for models with value encodings: the clause rows and the
   * linear rows of the model, with the conflicts of pairs of literals (the binary clauses) merged
   * into clique rows. It is made only when the binary clauses hold at-most-one structure, at least
   * {@code org.jacop.lp.clauseRefutationCliques} cliques of three or more literals: pigeonhole and
   * mutilated chessboard formulas state each at-most-one as its pairs, and the clauses alone have
   * an LP that is always feasible (each literal at 1/2).
   *
   * @param store the store
   * @param clauses the clause rows of the clauses that lazy clause generation took
   * @return the relaxation, or null when it is off, the model has too few cliques or too many rows
   */
  public static LinearRelaxation clauseRefutation(Store store, Collection<LinearForm> clauses) {
    if (!CLAUSE_REFUTATION || !ROOT_REFUTATION || clauses.isEmpty()) {
      return null;
    }
    List<LinearForm> given = new ArrayList<>();
    for (Constraint c : constraintsOf(store)) {
      if (c instanceof LinearRelaxation) {
        continue;
      }
      LinearForm f = LinearForms.of(c);
      if (f != null && f.relation() != LinearForm.NE && f.vars().length > 1) {
        given.add(f);
      }
    }
    List<LinearForm> clauseRows = new ArrayList<>();
    for (LinearForm f : clauses) {
      if (f == null) {
        continue;
      }
      if (ClauseSimplification.isClause(f)) {
        clauseRows.add(f);
      } else {
        given.add(f);
      }
    }
    ClauseSimplification simplified = ClauseSimplification.of(clauseRows);
    if (simplified.refuted) {
      // unit propagation refutes the clauses: lazy clause generation does so at its root
      return null;
    }
    given.addAll(simplified.rows);
    PairCliques merged = PairCliques.merge(given, List.of());
    if (merged.cliques < CLAUSE_REFUTATION_CLIQUES) {
      return null;
    }
    List<LinearForm> rows = merged.rows;
    Simplex simplex = sparseTakes(rows) ? Simplex.SPARSE : Simplex.DENSE;
    if (tooLarge(rows, simplex)) {
      return null;
    }
    LinearRelaxation r = new LinearRelaxation(rows, List.of(), null, false, simplex);
    r.refutation = true;
    r.pairCliques = merged.cliques;
    r.clauseRefutation = true;
    r.clauseUnits = simplified.units;
    r.clauseEquivalences = simplified.equivalences;
    r.cutsTried = true;
    return r.rows() < 2 ? null : r;
  }

  /**
   * Tells whether this refutation minimizes an inequality of the model ({@link
   * #pseudoObjectiveRefutation}).
   *
   * @return true for a refutation with an objective
   */
  public boolean hasPseudoObjective() {
    return pseudoObjective;
  }

  /**
   * Tells which pass made this refutation: "values" for the value encodings of {@link #refutation},
   * "objective" for {@link #pseudoObjectiveRefutation}, "clauses" for {@link #clauseRefutation}.
   *
   * @return the kind of the refutation
   */
  public String refutationKind() {
    if (pseudoObjective) {
      return "objective";
    }
    return clauseRefutation ? "clauses" : "values";
  }

  /**
   * Returns the outcome of the root solve of a relaxation made by {@link #refutation}.
   *
   * @return "refuted" when it proved that the model has no solution, "feasible", "limit" when it
   *     stopped at its pivot limit, "unsolved" before its solve
   */
  public String refutationOutcome() {
    return switch (refutationStatus) {
      case -1 -> "unsolved";
      case LpSolver.INFEASIBLE -> "refuted";
      case LpSolver.OPTIMAL -> "feasible";
      default -> "limit";
    };
  }

  /**
   * Returns the rows of this relaxation over the variables of the model: the given rows and the
   * further rows tried at the first solve.
   *
   * @return the rows, a new list
   */
  public List<LinearForm> allRows() {
    List<LinearForm> all = new ArrayList<>(forms);
    all.addAll(extraForms);
    return all;
  }

  // the constraints of the variables in the store and of the named ones, such as Boolean
  // variables, which have no store index
  static Set<Constraint> constraintsOf(Store store) {
    Set<Constraint> constraints = new LinkedHashSet<>();
    for (int i = 0; i < store.size(); i++) {
      constraints.addAll(store.vars[i].dom().constraints());
      constraints.addAll(store.valueWatchers(store.vars[i]));
    }
    for (Var v : store.variablesHashMap.values()) {
      constraints.addAll(v.dom().constraints());
      // constraints that watch values, such as long pseudo-Boolean sums, are not in the domains
      constraints.addAll(store.valueWatchers(v));
    }
    constraints.addAll(store.watchedLiteralConstraints());
    // the readers of reifications (value links, encodings) see an order channel as its items
    if (constraints.stream().anyMatch(c -> c.getClass() == ChannelOrder.class)) {
      Set<Constraint> expanded = new LinkedHashSet<>();
      for (Constraint c : constraints) {
        if (c.getClass() == ChannelOrder.class) {
          expanded.addAll(((ChannelOrder) c).reifications());
        } else {
          expanded.add(c);
        }
      }
      return expanded;
    }
    return constraints;
  }

  /**
   * Returns whether the relaxation was built for a proof ({@link #ofModel}).
   *
   * @return true when its deductions have certificates
   */
  public boolean certifies() {
    return rowSource != null;
  }

  /**
   * Returns the certificate of the form that gave the last explanation, by {@link #explain} or
   * {@link #explainFailure}, of a relaxation built for a proof.
   *
   * @return the certificate, or null
   */
  public Certificate certificate() {
    return lastCertificate;
  }

  /**
   * Writes nothing: the relaxation is implied by its rows, and a proof derives each of its
   * deductions from the lines of their constraints. Only a relaxation built for a proof ({@link
   * #ofModel}) has the certificates for that.
   */
  @Override
  public boolean encode(PbModel model) {
    return certifies();
  }

  // the certificate of a combination of the rows by lambda, for the <= side (upper) or the >= side
  private Certificate certified(LinearForm f, long[] lambda, boolean upper) {
    if (rowSource == null || f == null) {
      return null;
    }
    int n = 0;
    for (long l : lambda) {
      n += l != 0 ? 1 : 0;
    }
    // the multipliers of the scaled simplex share powers of two: the same sum divided by their
    // greatest common divisor, exactly, keeps the proof's numbers small
    long g = 0;
    for (long l : lambda) {
      g = gcd(g, Math.abs(l));
    }
    Constraint[] rows = new Constraint[n];
    long[] multipliers = new long[n];
    for (int i = 0, k = 0; i < lambda.length; i++) {
      if (lambda[i] != 0) {
        rows[k] = rowSource[i];
        multipliers[k++] = (upper ? lambda[i] : -lambda[i]) / g;
      }
    }
    return new Certificate(f, rows, multipliers);
  }

  private static boolean containsAll(List<LinearForm> rows, Set<LinearForm> part) {
    Set<LinearForm> in = Collections.newSetFromMap(new IdentityHashMap<>());
    in.addAll(rows);
    return in.containsAll(part);
  }

  /**
   * Returns the candidates, not among the tried ones, at distance at most 1 from the objective (see
   * {@link #byDistance}): the rows over the objective and over the variables of those rows, and the
   * rows over no other columns than these and the given rows.
   */
  static Set<LinearForm> nearObjective(
      List<LinearForm> forms,
      List<LinearForm> candidates,
      Set<LinearForm> tried,
      IntVar objective) {
    int[] distance = distances(forms, candidates, objective);
    Set<LinearForm> near = Collections.newSetFromMap(new IdentityHashMap<>());
    Set<IntVar> columns = Collections.newSetFromMap(new IdentityHashMap<>());
    for (LinearForm f : forms) {
      columns.addAll(Arrays.asList(f.vars()));
    }
    for (int i = 0; i < candidates.size(); i++) {
      if (distance[i] <= 1 && !tried.contains(candidates.get(i))) {
        near.add(candidates.get(i));
        columns.addAll(Arrays.asList(candidates.get(i).vars()));
      }
    }
    // and the rows over their columns only, such as the exactly-one rows of the value encodings,
    // whose Booleans the rows over the terms of the objective bound one by one
    for (LinearForm f : candidates) {
      if (!near.contains(f) && !tried.contains(f) && columns.containsAll(Arrays.asList(f.vars()))) {
        near.add(f);
      }
    }
    return near;
  }

  /**
   * Returns the candidates ordered by their distance from the objective (stable): a row over the
   * objective has distance 0, a row over a variable of a row at distance d has distance d + 1,
   * through the given rows and the candidates; rows not connected to the objective come last.
   */
  static List<LinearForm> byDistance(
      List<LinearForm> forms, List<LinearForm> candidates, IntVar objective) {
    int[] distance = distances(forms, candidates, objective);
    Integer[] order = new Integer[candidates.size()];
    for (int i = 0; i < order.length; i++) {
      order[i] = i;
    }
    Arrays.sort(order, Comparator.comparingInt(i -> distance[i]));
    List<LinearForm> sorted = new ArrayList<>(order.length);
    for (int i : order) {
      sorted.add(candidates.get(i));
    }
    return sorted;
  }

  // the distances of the candidates from the objective (byDistance)
  private static int[] distances(
      List<LinearForm> forms, List<LinearForm> candidates, IntVar objective) {
    List<LinearForm> all = new ArrayList<>(forms.size() + candidates.size());
    all.addAll(forms);
    all.addAll(candidates);
    Map<IntVar, List<Integer>> rowsOf = new IdentityHashMap<>();
    for (int i = 0; i < all.size(); i++) {
      for (IntVar v : all.get(i).vars()) {
        rowsOf.computeIfAbsent(v, k -> new ArrayList<>()).add(i);
      }
    }
    int[] distance = new int[all.size()];
    Arrays.fill(distance, Integer.MAX_VALUE);
    Set<IntVar> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    ArrayDeque<IntVar> queue = new ArrayDeque<>();
    Map<IntVar, Integer> depth = new IdentityHashMap<>();
    seen.add(objective);
    depth.put(objective, 0);
    queue.add(objective);
    while (!queue.isEmpty()) {
      IntVar v = queue.poll();
      int d = depth.get(v);
      for (int i : rowsOf.getOrDefault(v, List.of())) {
        if (distance[i] != Integer.MAX_VALUE) {
          continue;
        }
        distance[i] = d;
        for (IntVar u : all.get(i).vars()) {
          if (seen.add(u)) {
            depth.put(u, d + 1);
            queue.add(u);
          }
        }
      }
    }
    return Arrays.copyOfRange(distance, forms.size(), all.size());
  }

  // the rows over the terms of the objective that do not fit the dense tableau are all taken by
  // the sparse simplex (not final: a test hook)
  static boolean nearRowsOn =
      !Boolean.FALSE.toString().equals(System.getProperty("org.jacop.lp.nearRows"));

  // the dense simplex is chosen for relaxations below this many rows, the sparse one from it on,
  // when the dense one is asked for; -1 keeps the dense one whatever the size
  private static final int SPARSE_ROWS = Integer.getInteger("org.jacop.lp.sparseRows", 100);

  // the most clause rows of tables over all tables; more give none
  private static final int MAX_TABLE_CLAUSES =
      Integer.getInteger("org.jacop.lp.tableClauseRowsMax", 10_000);

  // the clause rows of tables over 0/1 variables (HybridTable.clauseRows)
  private static final boolean TABLE_CLAUSES =
      !FALSE.equals(System.getProperty("org.jacop.lp.tableClauseRows"));

  // the conflicts of pairs of 0/1 literals merged into clique rows
  private static final boolean PAIR_CLIQUES =
      !FALSE.equals(System.getProperty("org.jacop.lp.pairCliques"));

  // satisfaction models: a relaxation of the value encodings solved once at the root, to refute
  // the model (refutation)
  private static final boolean ROOT_REFUTATION =
      !FALSE.equals(System.getProperty("org.jacop.lp.rootRefutation"));

  // made by clauseRefutation
  private boolean clauseRefutation;

  /** The variables that unit propagation fixed in the clause rows of {@link #clauseRefutation}. */
  public int clauseUnits;

  /** The variables that equivalences substituted in {@link #clauseRefutation}. */
  public int clauseEquivalences;

  // models in clauses: a refutation over the clause rows and their clique rows (clauseRefutation),
  // made when the binary clauses form at least this many cliques of three or more literals
  private static final boolean CLAUSE_REFUTATION =
      !FALSE.equals(System.getProperty("org.jacop.lp.clauseRefutation"));
  private static final int CLAUSE_REFUTATION_CLIQUES =
      Integer.getInteger("org.jacop.lp.clauseRefutationCliques", 1);

  // the pivots of its root solve: the pigeonhole, mutilated chessboard and grandtour formulas of
  // the SAT Competition refute in 65, 328 and 184; rubik 6-cube of the MiniZinc Challenge (a
  // solution in 3 s) does not refute in 2,083 pivots, 1.1 s
  private static final int CLAUSE_REFUTATION_PIVOTS =
      Integer.getInteger("org.jacop.lp.clauseRefutationPivots", 1_000);

  // the pivots of the root solve of the refutation: the social golfers refute in 1,442; on the 351
  // XCSP 2022-2025 satisfaction instances it does not refute, the root solve took up to 1.7 s
  // (7,362 pivots) without a limit
  private static final int REFUTATION_PIVOTS =
      Integer.getInteger("org.jacop.lp.rootRefutationPivots", 2_500);

  // a satisfaction model with no value encoding: the refutation minimizes the inequality whose
  // variables are in the most rows with cut rounds (pseudoObjectiveRefutation), when that row has
  // at least this many variables
  private static final boolean PSEUDO_OBJECTIVE =
      !FALSE.equals(System.getProperty("org.jacop.lp.refutationObjective"));
  private static final int PSEUDO_OBJECTIVE_LENGTH =
      Integer.getInteger("org.jacop.lp.refutationObjectiveLength", 3);

  // the largest relaxation, in rows and in columns, that the sparse simplex is chosen for by size:
  // beyond them its root solve and its ratio test take more than the time limit of a run (nside
  // EASY_200_50, 57,505 rows: 52 ms a pivot; rcpsp-wet-diverse j60_19_6, 140,925 columns), and the
  // largest that helped in the Challenge has 19,141 rows (table-layout) and 23,242 columns
  // (physician-scheduling). The column cap was 30,000: the ROADEF 2020 maintenance planning A_06
  // (35,742 columns, 3,040 rows) then became a large relaxation, solved at the root only, and was
  // dropped since its bound without the value encodings did not cut the objective's domain; with
  // them and search solves its bound is 21,377,570 and more (optimum 21,498,698)
  // not final, so that tests can make a small relaxation large
  static int sparseMaxRows = Integer.getInteger("org.jacop.lp.sparseMaxRows", 25_000);
  private static final int SPARSE_MAX_COLUMNS =
      Integer.getInteger("org.jacop.lp.sparseMaxColumns", 50_000);

  // large relaxations: those over the size caps of the sparse simplex up to these many rows and
  // columns (and org.jacop.lp.maxNonzeros nonzeros) are solved at the root only, with a time budget
  // instead of a pivot budget, and not again in search, where each solve would stop at its pivot
  // limit. The store x warehouse form of the 2026 warehouse model (olal41: 116,974 rows after the
  // pair cliques, 24,151 columns) had no relaxation over the caps; the root solve takes 4,078
  // pivots and 9 s, and its bound, 38,467, is the bound CP-SAT proves (38,413)
  private static final boolean LARGE_MODE =
      !Boolean.FALSE.toString().equals(System.getProperty("org.jacop.lp.large"));
  private static final int LARGE_MAX_ROWS =
      Integer.getInteger("org.jacop.lp.largeMaxRows", 1_000_000);
  private static final int LARGE_MAX_COLUMNS =
      Integer.getInteger("org.jacop.lp.largeMaxColumns", 250_000);

  // the time of a root solve of a large relaxation, in seconds, unless setTimeLimit sets a share of
  // the time limit of the run
  private static final double LARGE_ROOT_SECONDS =
      Double.parseDouble(System.getProperty("org.jacop.lp.largeRootSeconds", "30"));

  // the share of the time limit of the run that a root solve of a large relaxation may take
  private static final double LARGE_ROOT_SHARE =
      Double.parseDouble(System.getProperty("org.jacop.lp.largeRootShare", "0.1"));

  private static boolean largeTakes(List<LinearForm> forms) {
    if (!LARGE_MODE || forms.size() > LARGE_MAX_ROWS) {
      return false;
    }
    Set<IntVar> vars = Collections.newSetFromMap(new IdentityHashMap<>());
    long nonzeros = 0;
    for (LinearForm f : forms) {
      vars.addAll(Arrays.asList(f.vars()));
      nonzeros += f.vars().length;
      if (vars.size() > LARGE_MAX_COLUMNS || nonzeros > MAX_NONZEROS) {
        return false;
      }
    }
    return true;
  }

  private static boolean sparseTakes(List<LinearForm> forms) {
    if (forms.size() > sparseMaxRows) {
      return false;
    }
    Set<IntVar> vars = Collections.newSetFromMap(new IdentityHashMap<>());
    for (LinearForm f : forms) {
      vars.addAll(Arrays.asList(f.vars()));
      if (vars.size() > SPARSE_MAX_COLUMNS) {
        return false;
      }
    }
    return true;
  }

  // whether the given rows alone are over the size cap of the simplex
  private static boolean tooLarge(List<LinearForm> forms, Simplex simplex) {
    Set<IntVar> vars = Collections.newSetFromMap(new IdentityHashMap<>());
    long rows = 0;
    long nonzeros = 0;
    for (LinearForm f : forms) {
      vars.addAll(Arrays.asList(f.vars()));
      rows++;
      nonzeros += f.vars().length;
      // the dense tableau has a column for each variable and for each row
      if (simplex == Simplex.DENSE
          ? rows * (rows + vars.size() + 1) > MAX_TABLEAU
          : nonzeros > MAX_NONZEROS) {
        return true;
      }
    }
    return false;
  }

  /**
   * Fills further with the candidate rows the simplex takes after the given rows, in order, until
   * its size cap.
   *
   * @return true when the given rows and every candidate fit; false when the given rows are over
   *     the cap (further stays empty) or some candidates were left out
   */
  private static boolean fitsSimplex(
      List<LinearForm> forms,
      List<LinearForm> candidates,
      Simplex simplex,
      boolean denseCap,
      long share,
      Set<LinearForm> own,
      List<LinearForm> further) {
    if (tooLarge(forms, simplex)) {
      return false;
    }
    Set<IntVar> vars = Collections.newSetFromMap(new IdentityHashMap<>());
    long rows = 0;
    long nonzeros = 0;
    for (LinearForm f : forms) {
      vars.addAll(Arrays.asList(f.vars()));
      rows++;
      nonzeros += f.vars().length;
    }
    // a large relaxation may be over the column cap already: further rows add no columns then
    int columns = vars.size();
    // the rows with a share of their own are not counted in the share of the others
    int counted = 0;
    boolean fitted = true;
    for (LinearForm f : candidates) {
      int added = 0;
      for (IntVar v : f.vars()) {
        added += vars.contains(v) ? 0 : 1;
      }
      boolean ownShare = own.contains(f);
      if (simplex == Simplex.DENSE
          ? (rows + 1) * (rows + 1 + vars.size() + added + 1) > MAX_TABLEAU
          : nonzeros + f.vars().length > MAX_NONZEROS
              || denseCap && vars.size() + added > Math.max(SPARSE_MAX_COLUMNS, columns)) {
        return false;
      }
      if (denseCap && simplex != Simplex.DENSE && !ownShare && counted >= share) {
        if (own.isEmpty()) {
          return false;
        }
        // the share of the others is full: the rows with a share of their own may still come
        fitted = false;
        continue;
      }
      counted += ownShare ? 0 : 1;
      further.add(f);
      vars.addAll(Arrays.asList(f.vars()));
      rows++;
      nonzeros += f.vars().length;
    }
    return fitted;
  }

  /**
   * Returns the rows with the variables that have a definition among them replaced by it, and the
   * definitions left out; the rows unchanged when a substitution overflows.
   */
  private static List<LinearForm> substitute(
      List<LinearForm> forms, Set<? extends IntVar> substituted, IntVar objective) {
    Map<IntVar, LinearForm> definition = new IdentityHashMap<>();
    Map<IntVar, Long> weight = new IdentityHashMap<>();
    Set<LinearForm> definitions = Collections.newSetFromMap(new IdentityHashMap<>());
    for (LinearForm f : forms) {
      if (f.relation() != LinearForm.EQ) {
        continue;
      }
      IntVar s = null;
      int count = 0;
      for (int k = 0; k < f.vars().length; k++) {
        IntVar v = f.vars()[k];
        if (substituted.contains(v) && v != objective && !definition.containsKey(v)) {
          if (s == null && Math.abs(f.weights()[k]) == 1) {
            s = v;
          }
          if (v == s) {
            count++;
          }
        }
      }
      if (s != null && count == 1) {
        definition.put(s, f);
        weight.put(s, f.weights()[indexOf(f, s)]);
        definitions.add(f);
      }
    }
    if (definition.isEmpty()) {
      return forms;
    }
    List<LinearForm> result = new ArrayList<>();
    try {
      for (LinearForm f : forms) {
        if (!definitions.contains(f)) {
          result.add(expand(f, definition, weight, 0));
        }
      }
    } catch (ArithmeticException _) {
      return forms;
    }
    // a variable that a row still has after the expansion, which stops at depth 8, keeps its
    // definition, and so do the variables of that definition: the shared sums of linear overlap
    // factoring nest deeper (CSPLib bus driver scheduling c1, 370 sums: without their definitions
    // they were free columns and the root bound 4.4 instead of 25.4)
    Set<IntVar> kept = Collections.newSetFromMap(new IdentityHashMap<>());
    List<IntVar> todo = new ArrayList<>();
    for (LinearForm f : result) {
      for (IntVar v : f.vars()) {
        if (definition.containsKey(v) && kept.add(v)) {
          todo.add(v);
        }
      }
    }
    while (!todo.isEmpty()) {
      LinearForm d = definition.get(todo.removeLast());
      result.add(d);
      for (IntVar v : d.vars()) {
        if (definition.containsKey(v) && kept.add(v)) {
          todo.add(v);
        }
      }
    }
    return result;
  }

  // f with every defined variable replaced by its definition; definitions may use defined
  // variables, up to a small depth
  private static LinearForm expand(
      LinearForm f, Map<IntVar, LinearForm> definition, Map<IntVar, Long> weight, int depth) {
    boolean any = false;
    for (IntVar v : f.vars()) {
      any |= definition.containsKey(v);
    }
    if (!any || depth > 8) {
      return f;
    }
    List<IntVar> vs = new ArrayList<>();
    List<Long> ws = new ArrayList<>();
    long c = f.c();
    for (int k = 0; k < f.vars().length; k++) {
      IntVar v = f.vars()[k];
      long w = f.weights()[k];
      LinearForm d = definition.get(v);
      if (d == null) {
        vs.add(v);
        ws.add(w);
        continue;
      }
      // d: sum a x + ws s = cd, so w s = w ws cd - w ws sum a x (ws is 1 or -1)
      long f0 = Math.multiplyExact(w, weight.get(v));
      c = Math.subtractExact(c, Math.multiplyExact(f0, d.c()));
      for (int j = 0; j < d.vars().length; j++) {
        if (d.vars()[j] != v) {
          vs.add(d.vars()[j]);
          ws.add(Math.negateExact(Math.multiplyExact(f0, d.weights()[j])));
        }
      }
    }
    long[] w = new long[ws.size()];
    for (int k = 0; k < w.length; k++) {
      w[k] = ws.get(k);
    }
    LinearForm e = new LinearForm(vs.toArray(new IntVar[0]), w, c, f.relation());
    return expand(e, definition, weight, depth + 1);
  }

  private static int indexOf(LinearForm f, IntVar v) {
    for (int k = 0; k < f.vars().length; k++) {
      if (f.vars()[k] == v) {
        return k;
      }
    }
    return -1;
  }

  /**
   * Returns the number of rows.
   *
   * @return the rows of the relaxation
   */
  public int rows() {
    return rowColumns.length;
  }

  /**
   * Sets the most simplex pivots per propagation.
   *
   * @param limit the limit
   */
  public void setPivotLimit(int limit) {
    pivotLimit = limit;
  }

  /**
   * Sets the time limit of the run, which gives a root solve of a large relaxation its time:
   * org.jacop.lp.largeRootShare (0.1) of it.
   *
   * @param millis the time limit of the run in milliseconds; 0 or less for none
   */
  public void setTimeLimit(long millis) {
    if (millis > 0) {
      largeRootNanos = (long) (millis * 1e6 * LARGE_ROOT_SHARE);
    }
  }

  /**
   * Returns whether the relaxation is large: over the size caps of the sparse simplex in search,
   * and so solved at the root only.
   *
   * @return whether the relaxation is large
   */
  public boolean large() {
    return large;
  }

  // a large relaxation removed after its root solve, which did not bound the objective
  private boolean largeDropped;

  /**
   * Returns whether the relaxation is large and was removed after its root solve, whose bound did
   * not cut the domain of the objective.
   *
   * @return whether the large relaxation was removed
   */
  public boolean largeDropped() {
    return largeDropped;
  }

  // whether the root bound cuts the domain of the objective, whose bound before the root solve is
  // given
  private boolean boundsObjective(long domainBound) {
    if (objective == null || Double.isNaN(rootBound)) {
      return false;
    }
    return maximize
        ? Math.floor(rootBound + 1e-6) < domainBound
        : Math.ceil(rootBound - 1e-6) > domainBound;
  }

  /**
   * Returns whether the relaxation is large by its rows: over org.jacop.lp.sparseMaxRows (25,000)
   * of them, as MIP models with a row for each pair of their 0/1 columns are, not only by its
   * columns, as time-indexed encodings with few rows are.
   *
   * @return whether the relaxation is large and has more rows than the sparse simplex takes
   */
  public boolean largeByRows() {
    return large && rows() > sparseMaxRows;
  }

  /**
   * Returns the pivots made so far.
   *
   * @return the pivots
   */
  public long pivots() {
    return lp.pivots() + droppedPivots;
  }

  /**
   * Returns the estimated work of a pivot of the simplex, in tableau entries of the dense simplex.
   *
   * @return the work of a pivot
   */
  public long pivotWork() {
    return lp.pivotWork();
  }

  /**
   * Returns the number of columns.
   *
   * @return the columns of the relaxation
   */
  public int columns() {
    return x.length;
  }

  /**
   * Returns the number of auxiliary value and arc columns ({@link LpColumn}, not the free ones) in
   * the simplex. Before the first solve it is {@link #valueColumns}; after it, the columns of the
   * extra rows that the root trial dropped are not counted, and neither are those of the rows
   * dropped later in search.
   *
   * @return the auxiliary columns of the simplex
   */
  public int simplexValueColumns() {
    if (calls == 0) {
      return valueColumns;
    }
    int n = Math.min(lp.columns(), x.length);
    int count = 0;
    for (int j = 0; j < n; j++) {
      count += lpOnly[j] && !((LpColumn) x[j]).isFree() ? 1 : 0;
    }
    return count;
  }

  /**
   * Returns the number of free auxiliary columns ({@link LpColumn#isFree}) in the simplex, the
   * wires of the sorting networks it keeps; before the first solve, {@link #freeColumns}.
   *
   * @return the free columns of the simplex
   */
  public int simplexFreeColumns() {
    if (calls == 0) {
      return freeColumns;
    }
    int n = Math.min(lp.columns(), x.length);
    int count = 0;
    for (int j = 0; j < n; j++) {
      count += lpOnly[j] && ((LpColumn) x[j]).isFree() ? 1 : 0;
    }
    return count;
  }

  // the values of the columns in the last optimal solution of the simplex, and its store level
  private double[] solution = new double[0];
  private int solutionLevel = -1;
  private boolean keepSolutions;

  /**
   * Makes the relaxation keep the solution of each optimal solve, for {@link #solutionValue}. Off
   * by default, since copying the solution costs time on every solve.
   */
  public void keepSolutions() {
    keepSolutions = true;
  }

  /**
   * Returns the number of solutions kept so far: it changes whenever the last solution does.
   *
   * @return the number of solutions kept so far
   */
  public int solutionVersion() {
    return solutionVersion;
  }

  /**
   * Returns the number of columns of the last optimal solution of the simplex: the columns of the
   * simplex then, which can be fewer than {@link #columns()} when it has no extra rows.
   *
   * @return the columns of the last solution, 0 before the first one
   */
  public int solutionColumns() {
    return solution.length;
  }

  /**
   * Returns the value of a column in the last optimal solution of the simplex, which may be from
   * another branch of the search than the current one.
   *
   * @param j the column, below {@link #solutionColumns()}
   * @return its value
   */
  public double solutionValue(int j) {
    return solution[j];
  }

  // the last optimal solution of the simplex at the lowest store level solved, and that level
  private double[] rootSolution = new double[0];
  private int rootSolutionLevel = Integer.MAX_VALUE;

  /**
   * Returns the number of columns of the root solution (see {@link #rootSolutionValue}).
   *
   * @return the columns of the root solution, 0 before the first one
   */
  public int rootSolutionColumns() {
    return rootSolution.length;
  }

  /**
   * Returns the value of a column in the last optimal solution of the simplex at the lowest store
   * level it solved at, usually the root: unlike {@link #solutionValue}, it does not follow the
   * branches of the search. Kept only after {@link #keepSolutions()}.
   *
   * @param j the column, below {@link #rootSolutionColumns()}
   * @return its value
   */
  public double rootSolutionValue(int j) {
    return rootSolution[j];
  }

  /**
   * Returns the store level of the last optimal solution of the simplex.
   *
   * @return the level, -1 before the first solution
   */
  public int solutionLevel() {
    return solutionLevel;
  }

  /**
   * Returns the variable of a column.
   *
   * @param j the column
   * @return its variable
   */
  public IntVar column(int j) {
    return x[j];
  }

  /**
   * Returns whether the relaxation is a set partitioning, packing or covering model over 0/1
   * columns: each row that does not hold the objective has weights of one sign and size one over
   * columns whose domains are within 0..1 (fixed columns are constants), and there are at most
   * org.jacop.lp.setRowsShare (0.1) rows per column. Its root solution is often almost integral,
   * and its bound is often the optimum (the crew schedules of XCSP 2025 BusScheduling, 199 rows
   * over 14,773 columns: root bound 28.5, optimum 29).
   *
   * @return whether every row of the relaxation is a set row over 0/1 columns
   */
  public boolean setRows() {
    return setRows;
  }

  // whether the model's rows are set rows, decided when the relaxation is built: cuts come later
  private final boolean setRows;

  // whether the first m rows, the model's, are set rows over 0/1 columns
  private boolean setRows(int m) {
    if (m < 2 || m > x.length * SET_ROWS_SHARE) {
      return false;
    }
    for (int i = 0; i < m; i++) {
      int[] cs = rowColumns[i];
      boolean holdsObjective =
          objective != null && Arrays.stream(cs).anyMatch(j -> x[j] == objective);
      if (!holdsObjective && !setRow(cs, rowWeights[i])) {
        return false;
      }
    }
    return true;
  }

  // whether a row has weights of one sign and size one over 0/1 columns; fixed columns are
  // constants of the row
  private boolean setRow(int[] cs, long[] ws) {
    long sign = 0;
    for (int k = 0; k < cs.length; k++) {
      IntVar v = x[cs[k]];
      if (!v.singleton()) {
        if (sign == 0) {
          sign = ws[k];
        }
        if (ws[k] != sign || Math.abs(ws[k]) != 1 || v.min() < 0 || v.max() > 1) {
          return false;
        }
      }
    }
    return true;
  }

  private static final double SET_ROWS_SHARE =
      Double.parseDouble(System.getProperty("org.jacop.lp.setRowsShare", "0.1"));

  /**
   * Returns the variable minimized, or null for satisfaction.
   *
   * @return the objective
   */
  public IntVar objective() {
    return objective;
  }

  /**
   * Returns the simplex that solves the relaxation.
   *
   * @return the simplex
   */
  public Simplex simplex() {
    return simplex;
  }

  /**
   * Returns the number of rows in the simplex, fewer than {@link #rows()} with lazy rows.
   *
   * @return the rows of the simplex
   */
  public int simplexRows() {
    return lp.rows();
  }

  // the rows of the relaxation, sparse, for the sparse simplex
  private int[][] sparseRows(int m) {
    return Arrays.copyOf(rowColumns, m);
  }

  private double[][] doubles(int m) {
    double[][] w = new double[m][];
    for (int i = 0; i < m; i++) {
      w[i] = new double[rowWeights[i].length];
      for (int k = 0; k < w[i].length; k++) {
        w[i][k] = rowWeights[i][k];
      }
    }
    return w;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  // while suspended the relaxation only checks complete assignments
  private boolean suspended;

  /**
   * Suspends or resumes solving the relaxation. While suspended, consistency only fails an
   * assignment of every variable that breaks a row, and leaves the simplex and the schedule of
   * solves as they are, so that propagation outside the search (local search, for example) does not
   * spend the work the search gets.
   *
   * @param suspend true to suspend, false to resume.
   */
  public void suspend(boolean suspend) {
    suspended = suspend;
  }

  /**
   * Tells whether solving the relaxation is suspended, see {@link #suspend(boolean)}.
   *
   * @return true while suspended.
   */
  public boolean isSuspended() {
    return suspended;
  }

  /**
   * Returns the size of the dense tableau of the first solve, its rows and the rows of the other
   * constraints that the first solve tries, times those rows and the columns: an estimate of the
   * cost of the root solve and its cut rounds, known before it runs.
   *
   * @return rows times (rows plus columns) of the first solve.
   */
  public long rootTrialSize() {
    long m = (long) rows() + extraColumns.length;
    return m * (m + columns());
  }

  /**
   * Tells whether the relaxation was solved at least once.
   *
   * @return true after the first solve.
   */
  public boolean solved() {
    return calls > 0;
  }

  @Override
  public void consistency(Store store) {
    if (refutation && calls > 0) {
      return; // solved once at the root, see refutation()
    }
    // root forms made at a restart over tightened root bounds hold only while that level stays
    if (ROOT_REDUCED_COSTS && calls > 0 && !restarting && !tightLost) {
      rootReducedCosts(store);
    }
    if (large && calls > 0 && store.level > rootLevel && !restarting) {
      // a large relaxation does nothing in search once it is solved: it never prunes there, so
      // the constraints of its rows hold an assignment to them, and checking the ground columns
      // would cost a scan of up to all of them at every node (rcpsp-wet-diverse j60_19_6, 140,186
      // columns: 40 instead of 70 million nodes in 240 s)
      return;
    }
    // the simplex may skip a node, round its multipliers to nothing, or fix the last variables by
    // its own pruning without being run again; an assignment that breaks a row must still fail
    checkGround();
    if (suspended || tightLost) {
      return;
    }
    if (rootLevel < 0) {
      rootLevel = store.level;
      rootObjective = objectiveBound();
    } else if (store.level <= rootLevel && objectiveBound() != rootObjective) {
      rootObjective = objectiveBound();
      if (restartSolvesOn && rootBoundsChanged() && ++restartsWaited >= restartPeriod) {
        restartsWaited = 0;
        restartSolve(store);
        checkGround();
        return;
      }
    }
    credit = Math.min(credit + WORK_PER_CALL, WORK);
    if (++tick < period || credit < 0 || stalled >= IDLE_RUNS) {
      return;
    }
    tick = 0;
    long failed = failures;
    long pruned = prunings;
    long pivots = pivots();
    long work = lp.work();
    boolean first = calls == 0;
    long callsBefore = calls;
    // the bound of the objective's domain before the first solve, which the root bound must cut
    long domainBound = 0;
    if (objective != null) {
      domainBound = maximize ? objective.max() : objective.min();
    }
    long started = System.nanoTime();
    try {
      if (refutation) {
        refutationStatus = LpSolver.INFEASIBLE;
      }
      solveAndPropagate(store);
      if (refutation) {
        // feasible, or stopped at its limit: it has done its part
        refutationStatus = lastSolveStatus;
        removeConstraint();
        return;
      }
      if (first) {
        rememberRootBounds();
        if (large && !boundsObjective(domainBound)) {
          // a large relaxation is solved at the root only; one whose bound does not cut the
          // objective's domain has nothing left to give the search, and only slows it down when
          // woken (cable-tree-wiring A073, bound -198: LCG under -f made half the conflicts)
          largeDropped = true;
          removeConstraint();
        }
      }
    } finally {
      solveNanos += System.nanoTime() - started;
      long cost =
          simplex == Simplex.DENSE
              ? (pivots() - pivots + 1) * lp.pivotWork()
              : SPARSE_COST * (Math.max(0, lp.work() - work) + lp.pivotWork() + scanned);
      scanned = 0;
      if (first) {
        // the root solve and its cuts may take up to their own budget; they spend the credit only
        cost = Math.min(cost, WORK);
      }
      // back off while the relaxation finds nothing, come back as soon as it does
      if (calls > callsBefore) {
        recentFailures += ((failures > failed ? 1 : 0) - recentFailures) / 32;
      }
      if (failures > failed) {
        idle = 0;
        period = Math.max(1, period / 2);
        credit = WORK;
      } else if (prunings > pruned || FAIL_RATE > 0 && recentFailures >= FAIL_RATE) {
        if (prunings == pruned) {
          failingSolves++;
        }
        idle = 0;
        period = Math.max(1, period / 2);
        credit -= PRUNE_DISCOUNT == 0 ? 0 : cost / PRUNE_DISCOUNT;
      } else {
        credit -= cost;
        if (++idle >= IDLE_RUNS && period < MAX_PERIOD) {
          idle = 0;
          period *= 2;
        }
      }
    }
    checkGround();
  }

  // propagates the root forms again on the current branch when the bound of the objective has
  // improved since they were last propagated on it. The bounds they were propagated with are
  // trailed by level, so that the prunings undone by a backtrack are made again: at the level of
  // the first solve alone, which the search never returns to, they never fired (knapPI
  // similar_weights of the PB competition, 5,000 items: root bound 48,769.05 and optimum 48,768,
  // no proof in 240 s). On a branch they are propagated once per bound, not at every call, which
  // costs more than it prunes (bus_scheduling, osolpro #169)
  private void rootReducedCosts(Store store) {
    if (rootForms.length == 0) {
      return;
    }
    long bound = objectiveBound();
    if (rootBoundsSize > 0 && rootBoundsAt[rootBoundsSize - 1] == bound) {
      return;
    }
    if (rootBoundsSize > 0 && rootBoundsLevel[rootBoundsSize - 1] == store.level) {
      rootBoundsSize--;
    }
    if (rootBoundsSize == rootBoundsAt.length) {
      rootBoundsAt = Arrays.copyOf(rootBoundsAt, 2 * rootBoundsSize);
      rootBoundsLevel = Arrays.copyOf(rootBoundsLevel, 2 * rootBoundsSize);
    }
    rootBoundsAt[rootBoundsSize] = bound;
    rootBoundsLevel[rootBoundsSize++] = store.level;
    long pruned = prunings;
    for (int k = 0; k < rootForms.length; k++) {
      propagate(store, rootForms[k], rootFacts[k], rootCertificates[k]);
    }
    rootPrunings += prunings - pruned;
  }

  // whether the bounds of a column other than the objective are tighter than at the last solve at
  // the root level: with only the bound of the objective changed, a solve again finds the same
  // optimum (or its infeasibility, which the root reduced costs already prove) and the same cuts
  // (physician-scheduling: 40 to 50 restart solves, up to 20 s, no pruning)
  private boolean rootBoundsChanged() {
    if (solvedLo == null) {
      return true;
    }
    // the cuts over the root bounds also gain from the bound of the objective alone
    for (int j = objective == null || restartBoundsOn ? 0 : 1; j < x.length; j++) {
      if (x[j].min() > solvedLo[j] || x[j].max() < solvedHi[j]) {
        return true;
      }
    }
    return false;
  }

  // the bounds of the columns at the last optimal solve at the root level
  private void rememberRootBounds() {
    if (solvedLo == null) {
      solvedLo = new long[x.length];
      solvedHi = new long[x.length];
    }
    for (int j = 0; j < x.length; j++) {
      solvedLo[j] = x[j].min();
      solvedHi[j] = x[j].max();
    }
  }

  // the bound of the objective that improves with each solution, or 0 without an objective
  private long objectiveBound() {
    if (objective == null) {
      return 0;
    }
    return maximize ? objective.min() : objective.max();
  }

  /**
   * Solves the relaxation at the root level again, after the bound of the objective improved (a
   * restart, or new solutions before the search left the root): with the root budget, and with new
   * cut rounds over the bounds of the first solve, so that the cuts stay global.
   */
  private void restartSolve(Store store) {
    restartSolves++;
    restartAtRoot = store.level == rootLevel;
    largeDeadline = 0;
    long started = System.nanoTime();
    long pruned = prunings;
    restarting = true;
    if (rootSimplex != null
        && rootSimplexRows == rows()
        && Arrays.equals(rootSimplexLpRows, lpRow)) {
      droppedPivots += lp.pivots() - rootSimplex.pivots();
      lp = rootSimplex;
      rootSimplex = null;
    }
    try {
      solveAndPropagate(store);
      // also after a solve stopped at its limit: the next one waits for other bounds to change
      rememberRootBounds();
      // a solve that deduces nothing makes the next one wait for twice as many restarts
      // (physician-scheduling: 47 restart solves took 23 s and pruned nothing)
      restartPeriod = prunings > pruned ? 1 : Math.min(restartPeriod * 2, 1 << 20);
    } finally {
      restarting = false;
      solveNanos += System.nanoTime() - started;
      scanned = 0;
    }
  }

  // fails when every variable is fixed and a row does not hold
  private void checkGround() {
    for (int j = 0; j < x.length; j++) {
      if (!lpOnly[j] && !x[j].singleton()) {
        return;
      }
    }
    int checked = tightLost ? tightFrom : rows();
    for (int i = 0; i < checked; i++) {
      int[] cs = rowColumns[i];
      long[] ws = rowWeights[i];
      if (anyLpOnly && overLpOnly(cs)) {
        continue; // the auxiliary columns have no value; the certificates check such rows
      }
      long sum = 0;
      try {
        for (int k = 0; k < cs.length; k++) {
          sum = Math.addExact(sum, Math.multiplyExact(ws[k], x[cs[k]].value()));
        }
      } catch (ArithmeticException _) {
        continue;
      }
      boolean above = hasHi[i] && sum > rowHi[i];
      if (above || hasLo[i] && sum < rowLo[i]) {
        IntVar[] vars = new IntVar[cs.length];
        long[] w = new long[cs.length];
        for (int k = 0; k < cs.length; k++) {
          vars[k] = x[cs[k]];
          w[k] = above ? ws[k] : -ws[k];
        }
        failureForm = new LinearForm(vars, w, above ? rowHi[i] : -rowLo[i], LinearForm.LE);
        failureFacts = null;
        failureCertificate =
            rowSource == null
                ? null
                : new Certificate(
                    failureForm, new Constraint[] {rowSource[i]}, new long[] {above ? 1 : -1});
        failures++;
        throw Store.failException;
      }
    }
  }

  // the bounds of column j: those of its variable, or for an auxiliary column [x = v] 0 when v is
  // not in the domain of x and 1 when x is v (an arc column of a layered graph is never 1 by its
  // domain); the certificates take these bounds, and explain them
  // by the facts x != v and x = v
  private void setBounds(LpSolver solver, int j) {
    if (lpOnly[j]) {
      LpColumn c = (LpColumn) x[j];
      solver.setBounds(j, c.lower(), c.upper());
    } else {
      solver.setBounds(j, x[j].min(), x[j].max());
    }
  }

  private boolean overLpOnly(int[] cs) {
    for (int j : cs) {
      if (lpOnly[j]) {
        return true;
      }
    }
    return false;
  }

  // the simplex the bounds were last given to, and those bounds: a call gives it only the bounds
  // that changed since, which on most calls are few (the search changes a handful of variables
  // between two solves); a simplex swapped in (the one with the extra rows, the one before the
  // cuts) gets all of them
  private LpSolver boundsOf;
  private int[] sentMin = new int[0];
  private int[] sentMax = new int[0];

  private void sendBounds() {
    int n = lp.columns();
    boolean all = boundsOf != lp || sentMin.length != n;
    if (all) {
      boundsOf = lp;
      sentMin = new int[n];
      sentMax = new int[n];
    }
    for (int j = 0; j < n; j++) {
      int min;
      int max;
      if (lpOnly[j]) {
        // an auxiliary column [x = v]: 0 when v is not in the domain of x, 1 when x is v
        LpColumn c = (LpColumn) x[j];
        min = c.lower();
        max = c.upper();
      } else {
        min = x[j].min();
        max = x[j].max();
      }
      if (all || min != sentMin[j] || max != sentMax[j]) {
        sentMin[j] = min;
        sentMax[j] = max;
        lp.setBounds(j, min, max);
      }
    }
  }

  private void solveAndPropagate(Store store) {
    if (rows() == 0 && (calls > 0 || extraColumns.length == 0)) {
      return; // the bounds of the variables alone deduce nothing
    }
    if (large && calls > 0 && !restarting) {
      // a large relaxation is solved at the root only: in search each solve would stop at its
      // pivot limit (olal41 of the warehouse MIP: 5 pivots, 15 ms a call, never optimal); the root
      // solution guides the search and its reduced costs fix columns at the root level
      return;
    }
    if (probation && calls - extraCall >= SATISFACTION_PROBATION) {
      probation = false;
      if (beforeExtra != null && !failingWithExtra()) {
        dropExtraRows();
      }
    }
    calls++;
    boolean jump = calls > 1 && lastSolveLevel - store.level >= BASIS_JUMP;
    long pivotsBefore = lp.pivots();
    if (KEEP_BASES) {
      restoreBasis(store.level, jump);
    }
    sendBounds();
    long size = Math.max(1, lp.pivotWork());
    if (beforeExtra != null && bySize && !keepEncodings && trees.isEmpty()) {
      // the extra rows on a simplex chosen by size are judged by the pivot limit of the dense
      // tableau they would make, as before the choice: a sparse work unit takes two to four times
      // a dense entry, and the sparse limit alone keeps rows that slow every solve (slnb7x7)
      long dense = (long) lp.rows() * (lp.rows() + lp.columns() + 1);
      if (dense <= MAX_TABLEAU) {
        size = Math.max(size, dense);
      }
    }
    int limit =
        calls == 1 || restarting
            ? (int) Math.clamp(ROOT_WORK / size, 5, rootPivots)
            : (int) Math.clamp(WORK / size, 5, pivotLimit);
    if (refutation) {
      limit = Math.min(limit, clauseRefutation ? CLAUSE_REFUTATION_PIVOTS : REFUTATION_PIVOTS);
    }
    int status =
        (calls == 1 || restarting) && simplex != Simplex.LAZY
            ? rootSolve(lp, limit, rootWork())
            : solvePool(limit);
    status = extendRootSolve(lp, status, calls == 1);
    // the first solve happens in the root propagation, before search makes a decision (also in
    // the free search, which propagates its root a level up, and under lazy clause generation)
    if (calls == 1 && extraColumns.length > 0) {
      status = addExtraRows(status);
    }
    if (status == DualSimplex.OPTIMAL
        && objective != null
        && CUTS_ENABLED
        && (!cutsTried && calls == 1 || restarting && RESTART_CUTS && rootLo != null)) {
      cutsTried = true;
      status = cutRounds();
    }
    if (status == LpSolver.OPTIMAL
        && MIR_SEARCH
        && mirRows != null
        && mirColumns == lp.columns()
        && objective != null
        && calls > 1
        && !restarting
        && ++mirWaited >= mirPeriod) {
      mirWaited = 0;
      long t0 = System.nanoTime();
      status = searchMirCuts(limit);
      timed("s-mir", t0);
    }
    if (status == LpSolver.OPTIMAL
        && CAPACITY_SEARCH
        && capacityColumns != null
        && capacityColumns.length > 0
        && calls > 1
        && !restarting
        && ++capacityWaited >= capacityPeriod) {
      capacityWaited = 0;
      long t0 = System.nanoTime();
      status = searchCapacityCuts(limit);
      timed("s-capacity", t0);
    }
    if (status == LpSolver.OPTIMAL
        && alldiffSearch
        && hallColumns != null
        && hallColumns.length > 0
        && calls > 1
        && !restarting
        && ++hallWaited >= hallPeriod) {
      hallWaited = 0;
      long t0 = System.nanoTime();
      status = searchHallCuts(limit);
      timed("s-hall", t0);
    }
    if (status == LpSolver.OPTIMAL
        && energySearch
        && energyColumns != null
        && energyColumns.length > 0
        && calls > 1
        && !restarting
        && ++energyWaited >= energyPeriod) {
      energyWaited = 0;
      long t0 = System.nanoTime();
      status = searchEnergyCuts(limit);
      timed("s-energy", t0);
    }
    if (sources != null) {
      countRowSolves(status);
    }
    lastSolveLevel = store.level;
    lastSolveStatus = status;
    if (jump) {
      jumpSolves++;
      jumpPivots += lp.pivots() - pivotsBefore;
    }
    if (KEEP_BASES && status == LpSolver.OPTIMAL) {
      saveBasis(store.level);
    }
    if (status == DualSimplex.LIMIT) {
      limits++;
      stalled++;
      long extraHits = limits - extraLimits;
      // the first solves after the root often stop at the limit while the search moves far from
      // the root solution: judge the extra rows only over 20 solves per limit or more
      // the value encodings over auxiliary columns are the relaxation: without them it is the
      // model's few linear rows, so they stay, and the back-off of the solves bounds their cost
      // the rows of a model with trees stay too: the tree cuts made over them are its bound
      // (berlin52
      // of surface-based-tsp: 7,542, the optimum, with them; 6,572 without, and fixed search took
      // 60-190 s instead of 13 s)
      if (beforeExtra != null
          && !keepEncodings
          && !extraCarry
          && trees.isEmpty()
          && !failingWithExtra()
          && (extraHits >= EXTRA_LIMITS && extraHits * 20 > calls && calls >= 20L * EXTRA_LIMITS
              || tableClauses > 0 && extraHits >= 8 && extraHits * 2 > calls)) {
        dropExtraRows();
      }
      if (!ANYTIME_BOUND || objective == null) {
        return;
      }
      // the duals of a dual simplex stopped at its limit are those of a basis that is dual
      // feasible up to the tolerances: the certificate below cleans their signs and bounds the
      // objective over the current domains, which holds whatever the multipliers
      anytimeSolves++;
      anytimePruningsBefore = prunings;
      anytimeFailuresBefore = failures;
    } else {
      stalled = 0;
    }
    if (status == LpSolver.OPTIMAL && (keepSolutions || store.level <= rootSolutionLevel)) {
      // the last solution is kept also before keepSolutions: the selection that follows it is
      // made after the root propagation, and the solves of the search may never be optimal
      // (surface-based-tsp ch130: the root solution after the tree cuts is the optimum, and every
      // one of the 60 solves in search stopped at the pivot limit or was infeasible). The root
      // solution of rootSolutionValue starts with keepSolutions, as before: fixed search, whose
      // activity runs follow it, took 504,252 nodes instead of 422,577 on lot-sizing pigment20a
      // with the solution of the first solve
      int n = lp.columns();
      if (solution.length != n) {
        solution = new double[n];
      }
      for (int j = 0; j < n; j++) {
        solution[j] = lp.value(j);
      }
      solutionVersion++;
      solutionLevel = store.level;
      if (keepSolutions && store.level <= rootSolutionLevel) {
        rootSolution = solution.clone();
        rootSolutionLevel = store.level;
      }
    }
    double[] y;
    if (status == DualSimplex.INFEASIBLE) {
      infeasible++;
      y = byRow(lp.farkas());
    } else if (objective != null) {
      if (Double.isNaN(rootBound) && status == LpSolver.OPTIMAL) {
        rootBound = lp.value(0);
      }
      y = byRow(lp.duals());
    } else {
      return;
    }
    try {
      for (int s = 0; s < SCALES.length; s++) {
        long[] lambda = scaled(y, SCALES[s]);
        if (lambda == null) {
          countUnproven(status);
          return;
        }
        int[][] facts = new int[2][];
        long[][] used = new long[2][];
        LinearForm[] localForms = certificate(lambda, facts, used);
        if (localForms == null) {
          continue; // the combination overflows: try a smaller scale
        }
        if (status == LpSolver.OPTIMAL && (calls == 1 || restarting)) {
          List<LinearForm> kept = new ArrayList<>();
          List<Certificate> keptCertificates = new ArrayList<>();
          List<int[]> keptFacts = new ArrayList<>();
          for (int k = 0; k < localForms.length; k++) {
            if (localForms[k] != null) {
              kept.add(localForms[k]);
              keptCertificates.add(certified(localForms[k], used[k], k == 0));
              keptFacts.add(facts[k]);
            }
          }
          rootForms = kept.toArray(new LinearForm[0]);
          rootCertificates = keptCertificates.toArray(new Certificate[0]);
          rootFacts = keptFacts.toArray(new int[0][]);
          if (restartSolvesOn
              && RESTART_FROM_ROOT
              && simplex != Simplex.LAZY
              && objective != null) {
            rootSimplex = lp.copy();
            rootSimplexRows = rows();
            rootSimplexLpRows = lpRow.clone();
          }
        }
        boolean fits = true;
        for (LinearForm f : localForms) {
          fits &= f == null || fits(f);
        }
        if (fits || s == SCALES.length - 1) {
          for (int k = 0; k < localForms.length; k++) {
            if (localForms[k] != null && sources == null) {
              propagate(store, localForms[k], facts[k], certified(localForms[k], used[k], k == 0));
            } else if (localForms[k] != null) {
              countedPropagate(store, localForms[k], facts[k], used[k], k == 0);
            }
          }
          if (status != LpSolver.INFEASIBLE) {
            return;
          }
          // the rounded Farkas multipliers did not prove the infeasibility: try a smaller scale
        }
        // the bounds reasoning on the form would overflow: try a smaller scale
      }
      countUnproven(status);
    } finally {
      if (anytimePruningsBefore >= 0) {
        anytimePrunings += prunings - anytimePruningsBefore;
        anytimeFailures += failures - anytimeFailuresBefore;
        anytimePruningsBefore = -1;
      }
    }
  }

  // adds the time since start to the separation time of the source
  private void timed(String source, long start) {
    if (sources != null) {
      sources.of(source).nanos += System.nanoTime() - start;
    }
  }

  // the rows of each source in the simplex count one solve each; after the first solve (and its
  // cut rounds) the rows in the simplex are counted, and each source is left out once to see what
  // the root bound loses without it
  private void countRowSolves(int status) {
    int m = Math.min(lpRow.length, lp.rows());
    for (int k = 0; k < m; k++) {
      sources.of(source(lpRow[k])).rowSolves++;
    }
    if (calls != 1 || restarting || status != LpSolver.OPTIMAL || objective == null) {
      return;
    }
    Map<String, List<Integer>> bySource = new java.util.TreeMap<>();
    for (int k = 0; k < m; k++) {
      String src = source(lpRow[k]);
      sources.of(src).rootRows++;
      bySource.computeIfAbsent(src, q -> new ArrayList<>()).add(lpRow[k]);
    }
    double full = lp.value(0);
    for (Map.Entry<String, List<Integer>> e : bySource.entrySet()) {
      List<Integer> others = new ArrayList<>();
      for (int k = 0; k < m; k++) {
        if (!e.getValue().contains(lpRow[k])) {
          others.add(lpRow[k]);
        }
      }
      LpSolver without = subsetSolver(others, lp.columns());
      for (int j = 0; j < lp.columns(); j++) {
        setBounds(without, j);
      }
      int st = rootSolve(without, rootPivots, rootWork());
      LpSources.Stat stat = sources.of(e.getKey());
      if (st == LpSolver.OPTIMAL) {
        double v = without.value(0);
        stat.rootLoss = maximize ? v - full : full - v;
        stat.rootIntLoss = Math.abs((long) integerBound(full) - (long) integerBound(v));
      } else {
        stat.rootLoss = st == LpSolver.INFEASIBLE ? Double.NaN : Double.POSITIVE_INFINITY;
      }
    }
  }

  // a simplex over the given rows of the pool and the first n columns, without column bounds
  private LpSolver subsetSolver(List<Integer> rows, int n) {
    int m = rows.size();
    double[] lo = new double[m];
    double[] hi = new double[m];
    int[][] cs = new int[m][];
    double[][] ws = new double[m][];
    for (int q = 0; q < m; q++) {
      int i = rows.get(q);
      lo[q] = hasLo[i] ? (double) rowLo[i] : Double.NEGATIVE_INFINITY;
      hi[q] = hasHi[i] ? (double) rowHi[i] : Double.POSITIVE_INFINITY;
      cs[q] = rowColumns[i];
      ws[q] = new double[rowWeights[i].length];
      for (int t = 0; t < ws[q].length; t++) {
        ws[q][t] = (double) rowWeights[i][t];
      }
    }
    double[] cost = new double[n];
    if (objective != null) {
      cost[0] = maximize ? -1 : 1;
    }
    return sparse(cs, ws, lo, hi, cost);
  }

  // propagate() of a form of the combination by lambda, which counts for the source of each row
  // with a multiplier when it prunes or fails
  private void countedPropagate(
      Store store, LinearForm f, int[] facts, long[] lambda, boolean upper) {
    long before = prunings;
    try {
      propagate(store, f, facts, certified(f, lambda, upper));
    } catch (FailException e) {
      credit(lambda, true);
      throw e;
    }
    if (prunings > before) {
      credit(lambda, false);
    }
  }

  private void credit(long[] lambda, boolean failure) {
    Map<String, Double> mass = new HashMap<>();
    double total = 0;
    for (int i = 0; i < lambda.length; i++) {
      if (lambda[i] != 0) {
        double a = Math.abs((double) lambda[i]);
        mass.merge(source(i), a, Double::sum);
        total += a;
      }
    }
    for (Map.Entry<String, Double> e : mass.entrySet()) {
      LpSources.Stat st = sources.of(e.getKey());
      if (failure) {
        st.failUses++;
      } else {
        st.uses++;
      }
      st.share += e.getValue() / total;
    }
  }

  // an infeasible LP solve that ends without an integer certificate
  private void countUnproven(int status) {
    if (status == LpSolver.INFEASIBLE) {
      unproven++;
    }
  }

  // drops the bases of levels below the current one, and after a jump restores the basis of the
  // deepest level kept, when it is closer to the current level than the last solve was
  private void restoreBasis(int level, boolean jump) {
    if (basesOf != lp) {
      bases.clear();
      basesOf = lp;
    }
    int k = bases.size();
    while (k > 0 && basisLevel[k - 1] > level) {
      k--;
    }
    bases.subList(k, bases.size()).clear();
    boolean judging = beforeExtra != null && calls - extraCall < BASIS_PROBATION;
    if (!jump || judging || k == 0 || level - basisLevel[k - 1] >= lastSolveLevel - level) {
      return;
    }
    if (lp.restoreBasis(bases.get(k - 1))) {
      basisRestores++;
    } else {
      bases.clear(); // rows were removed since: none of the bases holds
    }
  }

  // keeps the basis of an optimal solve as the one of its level
  private void saveBasis(int level) {
    if (basesOf != lp) {
      bases.clear();
      basesOf = lp;
    }
    if (firstSolveLevel < 0) {
      firstSolveLevel = level;
    }
    if (lp instanceof DualSimplex && level - firstSolveLevel > DENSE_BASIS_DEPTH) {
      return;
    }
    int k = bases.size();
    if (k > 0 && basisLevel[k - 1] == level) {
      Object b = lp.saveBasis();
      if (b == null) {
        return;
      }
      bases.set(k - 1, b);
    } else if (k < MAX_BASES && (k == 0 || basisLevel[k - 1] < level)) {
      Object b = lp.saveBasis();
      if (b == null) {
        return;
      }
      if (basisLevel.length == k) {
        basisLevel = Arrays.copyOf(basisLevel, 2 * k + 1);
      }
      basisLevel[k] = level;
      bases.add(b);
    }
  }

  /**
   * The two inequalities of the combination of the rows by lambda, cleaned (Neumaier and
   * Shcherbina): a multiplier whose row lacks the side its sign needs is dropped from that
   * inequality instead of losing the inequality, and each inequality is divided by the greatest
   * common divisor of its weights with its side rounded down, which holds as every column is an
   * integer. Null when a combination overflows. The multipliers of each inequality go to used.
   */
  private LinearForm[] certificate(long[] lambda, int[][] facts, long[][] used) {
    Aggregate g = aggregate(lambda);
    if (g == null) {
      return null;
    }
    used[0] = lambda;
    used[1] = lambda;
    LinearForm[] localForms = combine(g);
    facts[0] = combineFacts[0];
    facts[1] = combineFacts[1];
    if (!CLEAN || localForms.length == 0) {
      return localForms;
    }
    if (!g.hasUpper()) {
      used[0] = sided(lambda, true);
      Aggregate u = aggregate(used[0]);
      if (u == null) {
        return null;
      }
      LinearForm[] c = combine(u);
      localForms[0] = c.length > 0 ? c[0] : null;
      facts[0] = combineFacts[0];
    }
    if (!g.hasLower()) {
      used[1] = sided(lambda, false);
      Aggregate l = aggregate(used[1]);
      if (l == null) {
        return null;
      }
      LinearForm[] c = combine(l);
      localForms[1] = c.length > 1 ? c[1] : null;
      facts[1] = combineFacts[1];
    }
    for (int k = 0; k < localForms.length && rowSource == null; k++) {
      localForms[k] = localForms[k] == null ? null : divided(localForms[k]);
    }
    return localForms;
  }

  // lambda without the multipliers whose row lacks the side the upper (or lower) inequality needs
  private long[] sided(long[] lambda, boolean upper) {
    long[] l = lambda.clone();
    for (int i = 0; i < l.length; i++) {
      if (l[i] != 0 && !((l[i] > 0) == upper ? hasHi[i] : hasLo[i])) {
        l[i] = 0;
      }
    }
    return l;
  }

  // sum w x <= c divided by the gcd g of the weights: sum (w / g) x <= floor(c / g)
  private static LinearForm divided(LinearForm f) {
    long g = 0;
    for (long w : f.weights()) {
      g = gcd(g, Math.abs(w));
      if (g == 1) {
        return f;
      }
    }
    if (g <= 1) {
      return f;
    }
    long[] w = new long[f.weights().length];
    for (int k = 0; k < w.length; k++) {
      w[k] = f.weights()[k] / g;
    }
    return new LinearForm(f.vars(), w, Math.floorDiv(f.c(), g), LinearForm.LE);
  }

  private static long gcd(long a, long b) {
    while (b != 0) {
      long t = a % b;
      a = b;
      b = t;
    }
    return a;
  }

  // whether the bounds reasoning on sum w x <= c stays within a long with room to spare: the sum
  // of |w| times the largest bound, and |c|, below 2^61
  private static boolean fits(LinearForm f) {
    final double limit = 0x1p61;
    double sum = Math.abs((double) f.c());
    IntVar[] vars = f.vars();
    long[] w = f.weights();
    for (int k = 0; k < vars.length; k++) {
      double b = Math.max(Math.abs((double) vars[k].min()), Math.abs((double) vars[k].max()));
      sum += Math.abs((double) w[k]) * b;
    }
    return sum < limit;
  }

  // the work budget of a root solve of the sparse simplex: its pivots cost far more than the
  // estimate made before the first one (latin-squares-lp 20: 40,000 estimated, 390,000 spent, so
  // 20,000 root pivots took 14 s where the dense simplex had no relaxation at all), so its budget
  // is
  // counted as work spent; optimisation gets four times the budget of satisfaction, whose
  // relaxation can only find infeasibility
  private static final long SPARSE_ROOT_WORK =
      Long.getLong("org.jacop.lp.sparseRootWork", 4_000_000_000L);

  // the most time of a root solve of the sparse simplex, in seconds: on the largest relaxations its
  // work estimate is far off (nside EASY_200_50, 57,505 rows: 52 ms a pivot, 75 s for 1,455
  // pivots, past the time limit of the whole run); the limit only binds on such relaxations
  private static final long SPARSE_ROOT_NANOS =
      (long) (Double.parseDouble(System.getProperty("org.jacop.lp.sparseRootSeconds", "3")) * 1e9);

  // the share of the time of a root solve of a large relaxation (org.jacop.lp.largeRootShare of the
  // time limit) that the root solves of an optimisation relaxation in the sparse simplex share
  // when they stop at their pivots or work: the first solve, and the trial of the extra rows. Such
  // a solve gives neither a bound nor cuts nor a solution, while the relaxations under the size
  // caps of the sparse simplex are cheap per pivot. Drinking-010000 of XCSP 2024 (13,142 rows and
  // 12,570 extra rows of value encodings): the trial stops at its budget and is dropped, the bound
  // stays 0; the extended trial takes 0.8 s more and bounds the objective at 1,000, the optimum,
  // as on Drinking-020000, which is large and gets the time of a large relaxation. 0 turns it off;
  // not final, so that tests can turn it off
  static double rootExtendShare =
      Double.parseDouble(System.getProperty("org.jacop.lp.rootExtendShare", "0.5"));

  // the nanoseconds the extended root solves took; negative when the last stopped at its time too
  private long rootExtendNanos;

  // when the time of the extended root solves runs out (0 before the first one)
  private long extendDeadline;

  // continues a root solve of the sparse simplex that stopped at its pivots or work, within the
  // time that the extended root solves share; only a root solve (root) that stopped at its limit
  private int extendRootSolve(LpSolver s, int status, boolean root) {
    if (!root
        || status != LpSolver.LIMIT
        || objective == null
        || large
        || rootExtendShare <= 0
        || simplex == Simplex.LAZY
        || s instanceof DualSimplex) {
      return status;
    }
    long start = System.nanoTime();
    if (extendDeadline == 0) {
      extendDeadline = start + (long) (largeRootNanos * rootExtendShare);
    }
    if (start >= extendDeadline) {
      return status;
    }
    int r = rootSolve(s, Integer.MAX_VALUE, Long.MAX_VALUE, extendDeadline - start);
    long took = Math.max(1, System.nanoTime() - start);
    rootExtendNanos = (Math.abs(rootExtendNanos) + took) * (r == LpSolver.LIMIT ? -1 : 1);
    return r;
  }

  /**
   * Returns the time of the extended root solves, which run when a root solve of an optimisation
   * relaxation in the sparse simplex (the first one or the trial of the extra rows) stops at its
   * pivots or work.
   *
   * @return the nanoseconds they took, negative when the last one stopped at its time limit, 0 when
   *     none ran
   */
  public long rootExtendNanos() {
    return rootExtendNanos;
  }

  private long rootWork() {
    return objective == null ? ROOT_WORK : SPARSE_ROOT_WORK;
  }

  // a root solve with the rows of the pool that its solution breaks, as solvePool does in search:
  // rows that aged out while the objective was capped are needed once it is not (TankAllocation:
  // 16880 without them)
  private int rootSolvePool(int pivots) {
    int status = rootSolve(lp, pivots, rootWork() / CUT_ROUNDS);
    for (int round = 0; round < LAZY_ROUNDS && status == LpSolver.OPTIMAL; round++) {
      if (dormant == 0 || !addBrokenRows()) {
        break;
      }
      status = rootSolve(lp, pivots, rootWork() / CUT_ROUNDS);
    }
    return status;
  }

  /**
   * A root solve: the dense simplex in one call of at most the given pivots; the sparse one in
   * chunks, until it is done, the pivots run out, its work passes the budget, or its time passes
   * {@code org.jacop.lp.sparseRootSeconds}.
   */
  private int rootSolve(LpSolver s, int pivots, long work) {
    return rootSolve(s, pivots, work, SPARSE_ROOT_NANOS);
  }

  private int rootSolve(LpSolver s, int pivots, long work, long nanos) {
    if (s instanceof DualSimplex) {
      return s.solve(pivots);
    }
    if (large) {
      // the pivots of a large relaxation cost far more than its work estimate says, and its root
      // solve is the only one: it gets time instead of pivots and work
      // the solves of the root (the first one, the trial of further rows and the cut rounds) share
      // the time, so that its rounds of cuts do not take it again each (wlp22 of the warehouse
      // MIP: 62 s of LP time in a 240 s run)
      long now = System.nanoTime();
      if (largeDeadline == 0) {
        largeDeadline = now + largeRootNanos;
      }
      pivots = Integer.MAX_VALUE;
      work = Long.MAX_VALUE;
      nanos = Math.max(0, largeDeadline - now);
    }
    return solveWithin(s, pivots, work, nanos);
  }

  // a solve of the sparse simplex in chunks, until it is done, the pivots run out, its work passes
  // the budget or its time the nanoseconds given
  private static int solveWithin(LpSolver s, int pivots, long work, long nanos) {
    long startPivots = s.pivots();
    long startWork = s.work();
    long startTime = System.nanoTime();
    while (true) {
      long left = pivots - (s.pivots() - startPivots);
      long spent = s.work() - startWork;
      if (left <= 0 || spent >= work || System.nanoTime() - startTime > nanos) {
        return LpSolver.LIMIT;
      }
      long size = Math.max(1, s.pivotWork());
      int chunk = (int) Math.clamp((work - spent) / size, 1, Math.min(left, 50));
      int status = s.solve(chunk);
      if (status != LpSolver.LIMIT) {
        return status;
      }
    }
  }

  // the simplex holds the m rows of the relaxation, in order
  private void allRowsInSimplex(int m) {
    lpRow = new int[m];
    for (int k = 0; k < m; k++) {
      lpRow[k] = k;
    }
    inLp = new boolean[m];
    Arrays.fill(inLp, true);
    inactive = new int[m];
    identityRows = true;
    dormant = 0;
  }

  // multipliers of the rows of the simplex as multipliers of the rows of the relaxation
  private double[] byRow(double[] y) {
    if (identityRows && y.length == rows()) {
      return y;
    }
    double[] full = new double[rows()];
    for (int k = 0; k < y.length; k++) {
      full[lpRow[k]] = y[k];
    }
    return full;
  }

  /**
   * Solves the rows of the simplex, with the rows of the pool that are not in it: after each
   * optimal solve the rows of the pool that its solution breaks, the most broken first, enter the
   * simplex in a batch and it solves again, until it breaks none, it proves infeasibility, or the
   * pivots run out. The rows that may leave and stay inactive for {@code LAZY_AGE} (lazy rows) or
   * {@code org.jacop.lp.poolAge} optimal solves leave the simplex for the pool.
   *
   * @param limit the most pivots
   * @return the status of the last solve
   */
  private int solvePool(int limit) {
    long start = lp.pivots();
    int status = LpSolver.OPTIMAL;
    for (int round = 0; round < LAZY_ROUNDS; round++) {
      long left = limit - (lp.pivots() - start);
      if (left <= 0) {
        return LpSolver.LIMIT;
      }
      status = lp.solve((int) left);
      if (status != LpSolver.OPTIMAL) {
        return status;
      }
      if (dormant == 0 || !addBrokenRows()) {
        if (lpRow.length > baseCount) {
          ageRows();
        }
        return status;
      }
    }
    return status;
  }

  // adds the rows that the solution of the simplex breaks, at most LAZY_BATCH; false when none
  private boolean addBrokenRows() {
    double[] v = new double[lp.columns()];
    for (int j = 0; j < v.length; j++) {
      v[j] = lp.value(j);
    }
    int m = rows();
    double[] score = new double[m];
    List<Integer> broken = new ArrayList<>();
    for (int i = 0; i < m; i++) {
      if (inLp[i]) {
        continue;
      }
      int[] cs = rowColumns[i];
      long[] ws = rowWeights[i];
      scanned += cs.length;
      double act = 0;
      double norm = 0;
      for (int k = 0; k < cs.length; k++) {
        act += ws[k] * v[cs[k]];
        norm += (double) ws[k] * ws[k];
      }
      double gap = 0;
      if (hasLo[i] && act < rowLo[i] - 1e-6 * (1 + Math.abs(rowLo[i]))) {
        gap = rowLo[i] - act;
      } else if (hasHi[i] && act > rowHi[i] + 1e-6 * (1 + Math.abs(rowHi[i]))) {
        gap = act - rowHi[i];
      }
      if (gap > 0) {
        score[i] = gap / Math.sqrt(norm);
        broken.add(i);
      }
    }
    if (broken.isEmpty()) {
      return false;
    }
    broken.sort(Comparator.comparingDouble((Integer i) -> -score[i]));
    int k = Math.min(LAZY_BATCH, broken.size());
    if (simplex == Simplex.DENSE) {
      // the dense tableau stays within its size cap
      long rows = lp.rows();
      while (k > 0 && (rows + k) * (rows + k + lp.columns() + 1) > MAX_TABLEAU) {
        k--;
      }
      if (k == 0) {
        return false;
      }
    }
    int[][] cs = new int[k][];
    double[][] ws = new double[k][];
    double[] lo = new double[k];
    double[] hi = new double[k];
    int l = lpRow.length;
    lpRow = Arrays.copyOf(lpRow, l + k);
    inactive = Arrays.copyOf(inactive, l + k);
    for (int q = 0; q < k; q++) {
      int i = broken.get(q);
      cs[q] = rowColumns[i];
      ws[q] = new double[rowWeights[i].length];
      for (int t = 0; t < ws[q].length; t++) {
        ws[q][t] = rowWeights[i][t];
      }
      lo[q] = hasLo[i] ? rowLo[i] : Double.NEGATIVE_INFINITY;
      hi[q] = hasHi[i] ? rowHi[i] : Double.POSITIVE_INFINITY;
      lpRow[l + q] = i;
      inLp[i] = true;
      if (sources != null) {
        sources.of(source(i)).returns++;
      }
      if (simplex != Simplex.LAZY) {
        if (i >= returns.length) {
          returns = Arrays.copyOf(returns, Math.max(i + 1, 2 * returns.length));
        }
        returns[i]++;
      }
    }
    lp.addRows(cs, ws, lo, hi);
    identityRows = false;
    dormant -= k;
    lazyAdded += k;
    return true;
  }

  // counts the optimal solves in which each row of the simplex that may leave is inactive, its
  // slack basic and strictly within its bounds, and removes the rows inactive for LAZY_AGE solves
  // (lazy rows) or POOL_AGE solves
  private void ageRows() {
    if (simplex != Simplex.LAZY && !POOL) {
      return;
    }
    int age = simplex == Simplex.LAZY ? LAZY_AGE : POOL_AGE;
    int n = lp.columns();
    int old = 0;
    for (int k = baseCount; k < lpRow.length; k++) {
      int i = lpRow[k];
      double s = lp.value(n + k);
      boolean free =
          lp.basicRow(n + k) >= 0
              && (!hasLo[i] || s > rowLo[i] + 1e-6 * (1 + Math.abs(rowLo[i])))
              && (!hasHi[i] || s < rowHi[i] - 1e-6 * (1 + Math.abs(rowHi[i])));
      inactive[k] = free ? inactive[k] + 1 : 0;
      if (inactive[k] >= ageOf(i, age)) {
        old++;
      }
    }
    // removals refactorize the basis, so they wait for a batch
    if (old == 0 || old < Math.min(LAZY_BATCH, lpRow.length / 10 + 1)) {
      return;
    }
    int[] gone = new int[old];
    old = 0;
    for (int k = baseCount; k < lpRow.length; k++) {
      if (inactive[k] >= ageOf(lpRow[k], age)) {
        gone[old++] = k;
        if (sources != null) {
          sources.of(source(lpRow[k])).agedOut++;
        }
      }
    }
    int[] kept = lp.removeRows(gone);
    if (kept == null) {
      return;
    }
    int[] rows2 = new int[kept.length];
    int[] inactive2 = new int[kept.length];
    for (int k = 0; k < kept.length; k++) {
      rows2[k] = lpRow[kept[k]];
      inactive2[k] = inactive[kept[k]];
    }
    for (int i : lpRow) {
      inLp[i] = false;
    }
    for (int i : rows2) {
      inLp[i] = true;
    }
    lazyRemoved += lpRow.length - rows2.length;
    dormant += lpRow.length - rows2.length;
    identityRows = false;
    lpRow = rows2;
    inactive = inactive2;
  }

  // the inactive solves after which row i of the pool leaves the simplex
  private int ageOf(int i, int age) {
    return i < returns.length ? age << Math.min(returns[i], 6) : age;
  }

  // y scaled so that its largest entry is about scale, rounded; null when y is zero. With the
  // certificate cleaning on, entries below 1e-11 of the largest are noise of the simplex (the
  // round-off of its factors and updates) and are zeroed, so that a large scale does not turn
  // them into multipliers of rows without the side they need
  private static long[] scaled(double[] y, long scale) {
    double largest = 0;
    for (double v : y) {
      largest = Math.max(largest, Math.abs(v));
    }
    if (largest == 0 || Double.isNaN(largest) || Double.isInfinite(largest)) {
      return null;
    }
    long[] lambda = new long[y.length];
    for (int i = 0; i < y.length; i++) {
      // multipliers below 1e-11 of the largest are the simplex's round-off, not part of the proof
      double r = y[i] / largest;
      lambda[i] = Math.abs(r) < NOISE ? 0 : Math.round(r * scale);
    }
    return lambda;
  }

  /**
   * The combination {@code sum lambda_i a_i x} of the rows, sparse (the columns ascending with
   * their nonzero weights), with its two sides: {@code <= upper} when every row has the side its
   * multiplier needs, and {@code >= lower} likewise.
   */
  private static final class Aggregate {
    private final int[] columns;
    private final long[] coef;
    private final long upper;
    private final boolean hasUpper;
    private final long lower;
    private final boolean hasLower;

    Aggregate(
        int[] columns, long[] coef, long upper, boolean hasUpper, long lower, boolean hasLower) {
      this.columns = columns;
      this.coef = coef;
      this.upper = upper;
      this.hasUpper = hasUpper;
      this.lower = lower;
      this.hasLower = hasLower;
    }

    int[] columns() {
      return columns;
    }

    long[] coef() {
      return coef;
    }

    long upper() {
      return upper;
    }

    boolean hasUpper() {
      return hasUpper;
    }

    long lower() {
      return lower;
    }

    boolean hasLower() {
      return hasLower;
    }
  }

  // the combination of the rows by lambda, exact; null on overflow
  private Aggregate aggregate(long[] lambda) {
    long[] coef = new long[lp.columns()];
    long upper = 0; // sum lambda_i a_i x <= upper
    long lower = 0; // sum lambda_i a_i x >= lower
    boolean hasUpper = true;
    boolean hasLower = true;
    try {
      for (int i = 0; i < lambda.length; i++) {
        long l = lambda[i];
        if (l == 0) {
          continue;
        }
        int[] cs = rowColumns[i];
        long[] ws = rowWeights[i];
        for (int k = 0; k < cs.length; k++) {
          coef[cs[k]] = Math.addExact(coef[cs[k]], Math.multiplyExact(l, ws[k]));
        }
        if (l > 0 ? hasHi[i] : hasLo[i]) {
          upper = Math.addExact(upper, Math.multiplyExact(l, l > 0 ? rowHi[i] : rowLo[i]));
        } else {
          hasUpper = false;
        }
        if (l > 0 ? hasLo[i] : hasHi[i]) {
          lower = Math.addExact(lower, Math.multiplyExact(l, l > 0 ? rowLo[i] : rowHi[i]));
        } else {
          hasLower = false;
        }
      }
    } catch (ArithmeticException _) {
      return null;
    }
    int size = 0;
    for (long c : coef) {
      size += c != 0 ? 1 : 0;
    }
    int[] columns = new int[size];
    long[] weights = new long[size];
    for (int j = 0, k = 0; j < coef.length; j++) {
      if (coef[j] != 0) {
        columns[k] = j;
        weights[k++] = coef[j];
      }
    }
    return new Aggregate(columns, weights, upper, hasUpper, lower, hasLower);
  }

  // row i alone (lambda the unit vector of i), in time linear in the length of the row
  private Aggregate rowAggregate(int i) {
    int[] cs = rowColumns[i];
    long[] ws = rowWeights[i];
    Integer[] order = new Integer[cs.length];
    for (int k = 0; k < cs.length; k++) {
      order[k] = k;
    }
    Arrays.sort(order, Comparator.comparingInt(k -> cs[k]));
    int[] columns = new int[cs.length];
    long[] weights = new long[cs.length];
    for (int k = 0; k < cs.length; k++) {
      columns[k] = cs[order[k]];
      weights[k] = ws[order[k]];
    }
    return new Aggregate(columns, weights, rowHi[i], hasHi[i], rowLo[i], hasLo[i]);
  }

  /**
   * Returns the two inequalities of the combination {@code sum lambda_i a_i x}, each as {@code <=}
   * (one of them may be null when a row lacks the side it needs).
   */
  private LinearForm[] combine(Aggregate g) {
    int[] columns = g.columns();
    long[] coef = g.coef();
    long upper = g.upper();
    long lower = g.lower();
    int size = 0;
    int[] upperFacts = new int[0];
    int[] lowerFacts = new int[0];
    try {
      for (int k = 0; k < columns.length; k++) {
        if (coef[k] == 0) {
          continue;
        }
        int j = columns[k];
        if (lpOnly[j] && ((LpColumn) x[j]).isFree()) {
          // a free column leaves at its fixed bounds, which hold everywhere: no facts
          long a = Math.multiplyExact(coef[k], (long) x[j].min());
          long b = Math.multiplyExact(coef[k], (long) x[j].max());
          upper = Math.subtractExact(upper, Math.min(a, b));
          lower = Math.subtractExact(lower, Math.max(a, b));
        } else if (lpOnly[j]) {
          // an auxiliary column leaves the inequality at the bound that keeps it valid: sum c x
          // <= upper gives sum_rest c x <= upper - min(c lo, c hi), and sum c x >= lower gives
          // sum_rest c x >= lower - max(c lo, c hi); lo and hi are those of the simplex, from the
          // domain of the column's variable
          LpColumn column = (LpColumn) x[j];
          int lo = column.lower();
          int hi = column.upper();
          long a = coef[k] * (long) lo;
          long b = coef[k] * (long) hi;
          upper = Math.subtractExact(upper, Math.min(a, b));
          lower = Math.subtractExact(lower, Math.max(a, b));
          // the upper side takes c lo for c > 0 and c hi for c < 0, the lower side the other one
          boolean low = lo != 0;
          boolean high = hi != 1;
          if (coef[k] > 0 ? low : high) {
            upperFacts = appended(upperFacts, low && coef[k] > 0 ? ~j : j);
          }
          if (coef[k] > 0 ? high : low) {
            lowerFacts = appended(lowerFacts, high && coef[k] > 0 ? j : ~j);
          }
        } else {
          size++;
        }
      }
    } catch (ArithmeticException _) {
      return new LinearForm[0];
    }
    combineFacts[0] = upperFacts.length == 0 ? null : upperFacts;
    combineFacts[1] = lowerFacts.length == 0 ? null : lowerFacts;
    IntVar[] vars = new IntVar[size];
    long[] w = new long[size];
    long[] neg = new long[size];
    // the lower inequality is negated, and the negation of Long.MIN_VALUE is itself: a multiplier
    // of -2^40 on a weight of 2^23 kept the sign of that weight and made an invalid inequality
    boolean negates = g.hasLower() && lower != Long.MIN_VALUE;
    for (int k = 0, m = 0; k < columns.length; k++) {
      int j = columns[k];
      if (coef[k] != 0 && !lpOnly[j]) {
        vars[m] = x[j];
        w[m] = coef[k];
        negates &= coef[k] != Long.MIN_VALUE;
        neg[m++] = -coef[k];
      }
    }
    return new LinearForm[] {
      g.hasUpper() ? new LinearForm(vars, w, upper, LinearForm.LE) : null,
      negates ? new LinearForm(vars, neg, -lower, LinearForm.LE) : null
    };
  }

  // the pivot limit of one cut round; a refutation is solved once, so its rounds may take the
  // pivots of its root solve, since a round stopped at the limit is dropped and the refutation
  // then fails (php-exit: 4,454 pivots in all)
  private int roundPivots(long size) {
    int pivots = Math.clamp(ROOT_WORK / CUT_ROUNDS / size, 5, rootPivots);
    return pseudoObjective ? Math.max(pivots, REFUTATION_PIVOTS) : pivots;
  }

  /**
   * Rounds of MIR cuts at the root, each followed by a re-solve from the same basis. The cuts come
   * from the rows of the tableau of the basic columns with fractional values (Gomory mixed-integer
   * cuts, made exact: the row of the basis inverse is scaled and rounded into an integer
   * combination of the rows, and the MIR is taken of that combination) and from the rows
   * themselves. They use the bounds of the root, so they hold for the whole search, and they are
   * propagated and explained like the other rows.
   *
   * @return the status of the last solve
   */
  private int cutRounds() {
    int n = lp.columns();
    if (rootLo == null) {
      rootBound = lp.value(0);
      rootLo = new long[x.length];
      rootHi = new long[x.length];
      for (int j = 0; j < x.length; j++) {
        rootLo[j] = x[j].min();
        rootHi[j] = x[j].max();
      }
      // the capacity, energy and Hall cuts are made once, at the first solve
      if (!capacity.isEmpty() || !energy.isEmpty()) {
        long t0 = System.nanoTime();
        int status = capacityRounds();
        timed("capacity", t0);
        if (status != DualSimplex.OPTIMAL) {
          return status;
        }
      }
      if (!hall.isEmpty()) {
        long t0 = System.nanoTime();
        int status = hallRounds();
        timed("hall", t0);
        if (status != DualSimplex.OPTIMAL) {
          return status;
        }
      }
      if (!trees.isEmpty()) {
        long t0 = System.nanoTime();
        int status = treeRounds();
        timed("tree", t0);
        if (status != DualSimplex.OPTIMAL) {
          return status;
        }
      }
    }
    // the bounds of the first solve, which hold everywhere, also for the cuts made at restarts;
    // with restartBounds those of the root level now, which hold while it stays
    long[] lo = Arrays.copyOf(rootLo, n);
    long[] hi = Arrays.copyOf(rootHi, n);
    boolean tight = restarting && restartBoundsOn && rowSource == null && restartAtRoot;
    if (tight) {
      if (tightFrom < 0) {
        tightFrom = rows();
      }
      for (int j = 0; j < Math.min(n, x.length); j++) {
        lo[j] = Math.max(lo[j], x[j].min());
        hi[j] = Math.min(hi[j], x[j].max());
      }
      // the side of the objective that the relaxation proves goes back to that of the first
      // solve: capped there, the optimum sits at the cap and no cut seems to move it
      // (TankAllocation: 1680 with or without the cuts that take the bound below it); the side of
      // the incumbent stays, it is what the cuts gain from
      if (maximize) {
        hi[0] = rootHi[0];
      } else {
        lo[0] = rootLo[0];
      }
      if (lo[0] != sentMin[0] || hi[0] != sentMax[0]) {
        sentMin[0] = (int) lo[0];
        sentMax[0] = (int) hi[0];
        lp.setBounds(0, sentMin[0], sentMax[0]);
      }
      long size = Math.max(1, lp.pivotWork());
      int status = rootSolvePool(Math.clamp(ROOT_WORK / size, 5, rootPivots));
      if (status != LpSolver.OPTIMAL) {
        return status;
      }
    }
    int original = rows();
    long cutsAtStart = cuts;
    // the rows themselves, sorted once: each round then costs their length, not rows x columns
    Aggregate[] unitRows = new Aggregate[original];
    for (int i = 0; i < original; i++) {
      unitRows[i] = rowAggregate(i);
    }
    Set<List<Long>> seen = new HashSet<>();
    if (!restarting) {
      mirRows = unitRows;
      mirSeen = seen;
      mirColumns = n;
    }
    int status = DualSimplex.OPTIMAL;
    long cutsBefore = cuts;
    long mirStart = System.nanoTime();
    boolean moved = !restarting && moveToSparse();
    boolean slack = slackGomory;
    double start = lp.value(0);
    long extraDeadline = 0;
    for (int round = 0; round < Math.max(CUT_ROUNDS, CUT_ROUNDS_MAX); round++) {
      if (round >= CUT_ROUNDS) {
        // further rounds only while the cuts still move the bound, and for a short time
        long now = System.nanoTime();
        if (extraDeadline == 0) {
          extraDeadline = now + CUT_EXTRA_NANOS;
        }
        if (restarting || now > extraDeadline) {
          break;
        }
      }
      List<MirCut> chosen = separateCuts(lo, hi, unitRows, seen, ROOT_CUT_WEIGHT);
      if (chosen.isEmpty()) {
        break;
      }
      LpSolver kept = lp.copy();
      int[] keptRows = lpRow;
      double before = lp.value(0);
      addCuts(chosen);
      long size = Math.max(1, lp.pivotWork());
      status =
          tight
              ? rootSolvePool(roundPivots(size))
              : rootSolve(lp, roundPivots(size), rootWork() / CUT_ROUNDS);
      if (status == DualSimplex.OPTIMAL
          && Math.abs(lp.value(0) - before) <= 1e-6 * (1 + Math.abs(before))) {
        // cuts that do not move the bound only make each solve dearer: back to the LP before them
        dropCuts(chosen.size(), kept, keptRows);
        break;
      }
      if (status == LpSolver.LIMIT) {
        cutLimits++;
      }
      if (status == LpSolver.LIMIT && slackGomory) {
        // the Gomory cuts over the slacks can stall the simplex (degenerate pivots on tank
        // allocation, XCSP 2025); the round is dropped and the next ones take the MIR of the
        // aggregates instead
        dropCuts(chosen.size(), kept, keptRows);
        for (MirCut c : chosen) {
          seen.remove(key(c));
        }
        status = LpSolver.OPTIMAL;
        slackGomory = false;
        continue;
      }
      if (status != DualSimplex.OPTIMAL) {
        if (status == DualSimplex.LIMIT) {
          dropCuts(chosen.size(), kept, keptRows);
          status = DualSimplex.OPTIMAL;
        }
        break;
      }
      double gain = Math.abs(lp.value(0) - before);
      if (round >= CUT_ROUNDS - 1 && gain < CUT_PROGRESS * Math.abs(lp.value(0) - start)) {
        break;
      }
    }
    slackGomory = slack;
    timed("mir", mirStart);
    if (restarting) {
      if (tight) {
        restartBoundCuts += Math.max(0, cuts - cutsAtStart);
      }
      if (status == LpSolver.OPTIMAL) {
        restartCutBound = lp.value(0);
      }
    }
    if (moved
        && status == DualSimplex.OPTIMAL
        && (cuts == cutsBefore
            || integerBound(lp.value(0)) == integerBound(denseBeforeCuts.value(0)))) {
      // the cuts do not raise the bound of the integer objective: the sparse simplex would only
      // make each solve in search dearer than the dense one (mqueens), so back to the dense
      // tableau, at the same optimum, without the cuts
      droppedPivots += lp.pivots() - denseBeforeCuts.pivots();
      lp = denseBeforeCuts;
      simplex = Simplex.DENSE;
      truncateRows(denseRows);
      lpRow = denseLpRow;
      inLp = denseInLp;
      inactive = denseInactive;
      identityRows = denseIdentity;
      dormant = denseDormant;
      cuts = cutsBefore;
      sparseCuts = false;
    }
    denseBeforeCuts = null;
    denseLpRow = null;
    denseInLp = null;
    denseInactive = null;
    if (status == DualSimplex.OPTIMAL && !restarting) {
      cutBound = lp.value(0);
    }
    return status;
  }

  /**
   * Moves the rows of a dense tableau that has no room for a round of cuts to the sparse simplex of
   * JaLP, which has no tableau: its cost per pivot is its nonzeros, and its Gomory rows come from
   * the sparse rows of its basis inverse. The rows are those in the dense simplex, in the same
   * order; the sparse simplex is solved from scratch with the root budget and taken when it reaches
   * the same optimum, so the cuts start from the same bound. {@link #cutRounds} goes back to the
   * dense simplex when the cuts do not raise the bound of the integer objective. {@code
   * -Dorg.jacop.lp.sparseCuts=false} turns the move off.
   *
   * @return whether the rows moved
   */
  private boolean moveToSparse() {
    int m = lp.rows();
    int n = lp.columns();
    long room = (long) (m + CUTS_PER_ROUND) * (m + CUTS_PER_ROUND + n + 1);
    if (!SPARSE_CUTS || simplex != Simplex.DENSE || room <= tableauCap) {
      return false;
    }
    LpSolver s = sparseCopy();
    if (s == null) {
      return false;
    }
    droppedPivots += lp.pivots();
    denseBeforeCuts = lp;
    denseLpRow = lpRow.clone();
    denseInLp = inLp.clone();
    denseInactive = inactive.clone();
    denseIdentity = identityRows;
    denseRows = rows();
    denseDormant = dormant;
    lp = s;
    simplex = Simplex.SPARSE;
    sparseCuts = true;
    return true;
  }

  /**
   * Returns the sparse simplex of JaLP over the rows of the dense tableau, in the same order,
   * solved from scratch with the root budget, when it reaches the optimum of the dense one; null
   * otherwise (its pivots are counted as dropped).
   */
  private LpSolver sparseCopy() {
    int m = lp.rows();
    int n = lp.columns();
    int[][] cs = new int[m][];
    double[][] ws = new double[m][];
    double[] lo = new double[m];
    double[] hi = new double[m];
    long nonzeros = 0;
    for (int k = 0; k < m; k++) {
      int i = lpRow[k];
      cs[k] = rowColumns[i];
      ws[k] = new double[rowWeights[i].length];
      for (int t = 0; t < ws[k].length; t++) {
        ws[k][t] = rowWeights[i][t];
      }
      nonzeros += cs[k].length;
      lo[k] = hasLo[i] ? (double) rowLo[i] : Double.NEGATIVE_INFINITY;
      hi[k] = hasHi[i] ? (double) rowHi[i] : Double.POSITIVE_INFINITY;
    }
    if (nonzeros > MAX_NONZEROS) {
      return null;
    }
    double[] cost = new double[n];
    cost[0] = maximize ? -1 : 1;
    LpSolver s = sparse(cs, ws, lo, hi, cost);
    for (int j = 0; j < n; j++) {
      setBounds(s, j);
    }
    long size = Math.max(1, s.pivotWork());
    int status = rootSolve(s, Math.clamp(ROOT_WORK / size, 5, rootPivots), rootWork());
    double before = lp.value(0);
    if (status != LpSolver.OPTIMAL
        || Math.abs(s.value(0) - before) > 1e-6 * (1 + Math.abs(before))) {
      droppedPivots += s.pivots();
      return null;
    }
    return s;
  }

  /**
   * Moves a dense tableau that the extra rows made too large for search to the sparse simplex: a
   * solve in search takes WORK / pivotWork pivots, and a tableau of a few hundred clause rows over
   * thousands of columns gets only tens of them, so that nearly every solve stops at its limit
   * (scpa1 of the OR-Library set covering, 300 clauses over 3,000 columns: 311 x 3,312 entries, 19
   * pivots a call, 32 of 33 solves at the limit). The sparse simplex costs its nonzeros per pivot,
   * a seventh of the tableau there. Only for extra rows that carry the bound (extraCarry), as in
   * sparseTrial. {@code -Dorg.jacop.lp.extraSparse=false} turns the move off.
   */
  private void moveExtraToSparse() {
    if (!EXTRA_SPARSE
        || simplex != Simplex.DENSE
        || !extraCarry
        || WORK / Math.max(1, lp.pivotWork()) >= EXTRA_SPARSE_PIVOTS) {
      return;
    }
    LpSolver s = sparseCopy();
    if (s == null) {
      return;
    }
    if (s.pivotWork() * EXTRA_SPARSE_GAIN > lp.pivotWork()) {
      droppedPivots += s.pivots();
      return;
    }
    droppedPivots += lp.pivots();
    lp = s;
    simplex = Simplex.SPARSE;
    extraSparse = true;
  }

  // whether the MIR of a row of the tableau also tries the weight of its basic column as divisor,
  // the divisor of the textbook Gomory mixed-integer cut
  private static final boolean GOMORY_DIVISOR =
      !FALSE.equals(System.getProperty("org.jacop.lp.gomoryDivisor"));

  private static final boolean SLACK_GOMORY =
      !FALSE.equals(System.getProperty("org.jacop.lp.slackGomory"));

  private boolean slackGomory = SLACK_GOMORY;

  /**
   * Chooses the Gomory cuts of the root: over the rows and their slacks ({@link #slackGomory}, the
   * default, {@code -Dorg.jacop.lp.slackGomory=false} turns it off) or the MIR of the aggregate of
   * the rows alone.
   *
   * @param on true for the cuts over the slacks
   */
  public void setSlackGomory(boolean on) {
    slackGomory = on;
  }

  /**
   * The Gomory mixed-integer cut of a row of the tableau, exact. The row of the basis inverse,
   * scaled and rounded into integers lambda, gives the integer equality {@code sum_j (lambda A)_j
   * x_j - sum_i lambda_i s_i = 0} over the columns and the slacks {@code s_i = a_i x} of the rows.
   * Every slack is an integer, as the rows have integer weights over integer columns, and lies
   * within the sides of its row (or, for a side the row lacks, the bound its columns imply). The
   * MIR of that equality, both ways, is taken over the columns and the slacks together, in longs,
   * and the slacks are then replaced by their rows. Unlike the MIR of the aggregate {@code sum
   * lambda a x <= sum lambda b}, which puts every slack at a side, a slack keeps its own rounding,
   * which is what the Gomory cut of the textbook, with its real weights, does; its weights are the
   * exact rationals of that cut over a common denominator, scaled down safely when large ({@link
   * MirCut#reduce}). The MIR also tries the weight of the basic column as its divisor, the divisor
   * of the textbook cut.
   *
   * @param lambda the row of the basis inverse, scaled to integers, by row of the relaxation
   * @param basic the basic column of that row
   * @param value the LP solution by column
   * @param lo the global lower bounds by column
   * @param hi the global upper bounds by column
   * @param found the cuts found, to which the cuts of this row are added
   * @return false when the arithmetic overflowed, so that a smaller scale may be tried
   */
  private boolean slackGomory(
      long[] lambda, int basic, double[] value, long[] lo, long[] hi, List<MirCut> found) {
    int n = lp.columns();
    int m = lambda.length;
    long[] coef = new long[n];
    int slacks = 0;
    try {
      for (int i = 0; i < m; i++) {
        long l = lambda[i];
        if (l == 0) {
          continue;
        }
        slacks++;
        int[] cs = rowColumns[i];
        long[] ws = rowWeights[i];
        for (int k = 0; k < cs.length; k++) {
          coef[cs[k]] = Math.addExact(coef[cs[k]], Math.multiplyExact(l, ws[k]));
        }
      }
      int size = slacks;
      for (long c : coef) {
        size += c != 0 ? 1 : 0;
      }
      int[] columns = new int[size];
      long[] weights = new long[size];
      long[] xlo = Arrays.copyOf(lo, n + m);
      long[] xhi = Arrays.copyOf(hi, n + m);
      double[] xv = Arrays.copyOf(value, n + m);
      int q = 0;
      for (int j = 0; j < n; j++) {
        if (coef[j] != 0) {
          columns[q] = j;
          weights[q++] = coef[j];
        }
      }
      for (int i = 0; i < m; i++) {
        if (lambda[i] == 0) {
          continue;
        }
        long least = 0;
        long most = 0;
        double v = 0;
        int[] cs = rowColumns[i];
        long[] ws = rowWeights[i];
        for (int k = 0; k < cs.length; k++) {
          long a = Math.multiplyExact(ws[k], lo[cs[k]]);
          long b = Math.multiplyExact(ws[k], hi[cs[k]]);
          least = Math.addExact(least, Math.min(a, b));
          most = Math.addExact(most, Math.max(a, b));
          v += ws[k] * value[cs[k]];
        }
        xlo[n + i] = hasLo[i] ? Math.max(least, rowLo[i]) : least;
        xhi[n + i] = hasHi[i] ? Math.min(most, rowHi[i]) : most;
        if (xlo[n + i] > xhi[n + i]) {
          return true;
        }
        xv[n + i] = v;
        columns[q] = n + i;
        weights[q++] = -lambda[i];
      }
      long[] neg = new long[size];
      for (int k = 0; k < size; k++) {
        neg[k] = Math.negateExact(weights[k]);
      }
      for (long[] w : new long[][] {weights, neg}) {
        long[] g = MirCut.raw(columns, w, 0, xv, xlo, xhi, GOMORY_DIVISOR ? coef[basic] : 0);
        if (g == null) {
          continue;
        }
        // the slacks replaced by their rows: g_s s_i = g_s a_i x
        long[] cut = new long[n];
        for (int k = 0; k < size; k++) {
          if (g[k] == 0) {
            continue;
          }
          int c = columns[k];
          if (c < n) {
            cut[c] = Math.addExact(cut[c], g[k]);
          } else {
            int[] cs = rowColumns[c - n];
            long[] ws = rowWeights[c - n];
            for (int t = 0; t < cs.length; t++) {
              cut[cs[t]] = Math.addExact(cut[cs[t]], Math.multiplyExact(g[k], ws[t]));
            }
          }
        }
        int nz = 0;
        for (long c : cut) {
          nz += c != 0 ? 1 : 0;
        }
        int[] cc = new int[nz];
        long[] cw = new long[nz];
        for (int j = 0, t = 0; j < n; j++) {
          if (cut[j] != 0) {
            cc[t] = j;
            cw[t++] = cut[j];
          }
        }
        MirCut c = MirCut.finish(cc, cw, g[size], value, lo, hi, true);
        if (c != null) {
          found.add(c);
        }
      }
    } catch (ArithmeticException _) {
      // no cut from this row at this scale
      return false;
    }
    return true;
  }

  /**
   * Rounds of rounded capacity cuts ({@link CapacityCuts}) of the Routes constraints at the root,
   * each followed by a re-solve. The rounds stop when no cut is violated, the bound has not moved
   * for a few rounds, or a solve stops at its limit (that round's cuts are dropped); when the cuts
   * leave the bound where it was they are all dropped.
   *
   * @return the status of the last solve
   */
  private int capacityRounds() {
    Map<IntVar, Integer> columnOf = new IdentityHashMap<>();
    for (int j = 0; j < lp.columns(); j++) {
      columnOf.put(x[j], j);
    }
    capacityColumns = new int[capacity.size()][];
    for (int c = 0; c < capacity.size(); c++) {
      IntVar[] literals = capacity.get(c).literals();
      capacityColumns[c] = new int[literals.length];
      for (int a = 0; a < literals.length; a++) {
        Integer j = columnOf.get(literals[a]);
        capacityColumns[c][a] = j == null ? -1 : j;
      }
    }
    double start = lp.value(0);
    int firstCount = rows();
    LpSolver first = lp.copy();
    int[] firstRows = lpRow;
    int added = 0;
    int addedEnergy = 0;
    int stall = 0;
    int status = DualSimplex.OPTIMAL;
    Set<List<Long>> seen = new HashSet<>();
    long[] lo = new long[lp.columns()];
    long[] hi = new long[lp.columns()];
    for (int j = 0; j < lo.length; j++) {
      lo[j] = x[j].min();
      hi[j] = x[j].max();
    }
    energyColumns = new int[energy.size()][];
    energyLo = lo;
    energyHi = hi;
    for (int k = 0; k < energy.size(); k++) {
      IntVar[] starts = energy.get(k).starts();
      energyColumns[k] = new int[starts.length];
      for (int a = 0; a < starts.length; a++) {
        Integer j = columnOf.get(starts[a]);
        energyColumns[k][a] = j == null ? -1 : j;
      }
    }
    for (int round = 0; round < CAPACITY_ROUNDS && stall < CAPACITY_STALL; round++) {
      // energy cuts stay at the root; in search only capacity cuts are separated
      List<MirCut> chosen = separateCapacity(CUTS_PER_ROUND, seen, true);
      int n = lp.columns();
      int routing = chosen.size();
      if (!energy.isEmpty()) {
        double[] value = new double[n];
        for (int j = 0; j < n; j++) {
          value[j] = lp.value(j);
        }
        List<MirCut> found = new ArrayList<>();
        for (int k = 0; k < energy.size(); k++) {
          found.addAll(energy.get(k).separate(energyColumns[k], value, lo, hi, CUTS_PER_ROUND));
        }
        labelled(found, 0, "energy");
        found.sort(Comparator.comparingDouble((MirCut c) -> -c.efficacy));
        for (MirCut row : found) {
          long m = (long) lp.rows() + chosen.size() + 1;
          if (chosen.size() - routing >= CUTS_PER_ROUND
              || simplex == Simplex.DENSE && m * (m + n) > MAX_TABLEAU) {
            break;
          }
          if (seen.add(key(row))) {
            chosen.add(row);
          }
        }
      }
      if (chosen.isEmpty()) {
        break;
      }
      LpSolver kept = lp.copy();
      int[] keptRows = lpRow;
      double before = lp.value(0);
      addCuts(chosen);
      long size = Math.max(1, lp.pivotWork());
      status = rootSolve(lp, roundPivots(size), rootWork() / CUT_ROUNDS);
      if (status == DualSimplex.LIMIT) {
        dropCuts(chosen.size(), kept, keptRows);
        status = DualSimplex.OPTIMAL;
        break;
      }
      added += chosen.size();
      addedEnergy += chosen.size() - routing;
      if (status != DualSimplex.OPTIMAL) {
        break;
      }
      boolean moved = Math.abs(lp.value(0) - before) > 1e-6 * (1 + Math.abs(before));
      stall = moved ? 0 : stall + 1;
    }
    if (status == DualSimplex.OPTIMAL
        && added > 0
        && Math.abs(lp.value(0) - start) <= 1e-6 * (1 + Math.abs(start))) {
      // cuts that do not move the bound only make each solve dearer
      dropCuts(added, first, firstRows);
      added = 0;
      addedEnergy = 0;
    }
    capacityCuts += added - addedEnergy;
    energyCuts += addedEnergy;
    keepCapacityForms(firstCount, added);
    // the cuts kept stay in the pool; the others may come back in search
    for (int i = firstCount; i < firstCount + added; i++) {
      capacitySeen.add(key(MirCut.row(rowColumns[i], rowWeights[i], rowHi[i], 0)));
    }
    if (status == DualSimplex.OPTIMAL) {
      capacityBound = lp.value(0);
    }
    return status;
  }

  /**
   * Rounds of Hall cuts ({@link AlldifferentCuts}) of the all-different and cardinality constraints
   * over their variables that are columns (two or more), at the root, each followed by a re-solve.
   * As for the capacity cuts, the rounds stop when no cut is violated, the bound has not moved for
   * a few rounds, or a solve stops at its limit (that round's cuts are dropped); when the cuts
   * leave the bound where it was they are all dropped.
   *
   * @return the status of the last solve
   */
  private int hallRounds() {
    Map<IntVar, Integer> columnOf = new IdentityHashMap<>();
    for (int j = 0; j < lp.columns(); j++) {
      columnOf.put(x[j], j);
    }
    // the variables that are not columns stay out of the cuts; two columns or more are needed
    hall.removeIf(h -> Arrays.stream(h.literals()).filter(columnOf::containsKey).count() < 2);
    alldiffLists = hall.size();
    alldiffVariantLists = hall.stream().filter(h -> !h.plain()).count();
    hallColumns = new int[hall.size()][];
    for (int c = 0; c < hall.size(); c++) {
      IntVar[] list = hall.get(c).literals();
      hallColumns[c] = new int[list.length];
      for (int a = 0; a < list.length; a++) {
        hallColumns[c][a] = columnOf.getOrDefault(list[a], -1);
      }
    }
    if (hall.isEmpty()) {
      return DualSimplex.OPTIMAL;
    }
    int firstCount = rows();
    long[] result = separatedRounds(() -> violatedHall(CUTS_PER_ROUND), CAPACITY_ROUNDS, false);
    alldiffCuts += result[1];
    // search does not add the cuts kept here again
    for (int i = firstCount; i < firstCount + result[1]; i++) {
      hallSeen.add(key(MirCut.row(rowColumns[i], rowWeights[i], rowHi[i], 0)));
    }
    if (result[0] == DualSimplex.OPTIMAL) {
      alldiffBound = lp.value(0);
    }
    return (int) result[0];
  }

  /**
   * Rounds of generalized subtour elimination cuts ({@link TreeCuts}) of the forests of Tree and
   * Path, at the root, like the Hall cuts. A node Boolean that is not a column counts at its
   * largest value and an edge Boolean that is not a column at its least, which keeps the cuts
   * valid.
   *
   * @return the status of the last solve
   */
  private int treeRounds() {
    Map<IntVar, Integer> columnOf = new IdentityHashMap<>();
    for (int j = 0; j < lp.columns(); j++) {
      columnOf.put(x[j], j);
    }
    int[][] columns = new int[trees.size()][];
    for (int c = 0; c < trees.size(); c++) {
      IntVar[] list = trees.get(c).literals();
      columns[c] = new int[list.length];
      for (int a = 0; a < list.length; a++) {
        Integer j = columnOf.get(list[a]);
        columns[c][a] = j == null ? -1 : j;
      }
    }
    long[] result =
        separatedRounds(
            () -> {
              List<MirCut> found = new ArrayList<>();
              for (int c = 0; c < trees.size(); c++) {
                TreeCuts t = trees.get(c);
                IntVar[] list = t.literals();
                double[] value = new double[list.length];
                for (int a = 0; a < value.length; a++) {
                  value[a] =
                      columns[c][a] >= 0
                          ? lp.value(columns[c][a])
                          : a < t.nodeCount() ? list[a].max() : list[a].min();
                }
                for (TreeCuts.Cut cut : t.separate(value, CUTS_PER_ROUND)) {
                  MirCut row = row(cut, t, columns[c]);
                  if (row != null) {
                    row.source = "tree";
                    found.add(row);
                  }
                }
              }
              return found;
            },
            TREE_ROUNDS,
            true);
    treeCuts += result[1];
    if (result[0] == DualSimplex.OPTIMAL) {
      treeBound = lp.value(0);
    }
    return (int) result[0];
  }

  // the tree cut as a row sum w x <= rhs over the columns; a node that is not a column moves to
  // the right-hand side at its largest value, an edge at its least; null when no column is left
  private static MirCut row(TreeCuts.Cut cut, TreeCuts t, int[] column) {
    IntVar[] list = t.literals();
    int nodes = t.nodeCount();
    Map<Integer, Long> weights = new java.util.TreeMap<>();
    long rhs = 0;
    for (int i : cut.nodes()) {
      if (column[i] < 0) {
        rhs += list[i].max();
      } else {
        weights.merge(column[i], -1L, Long::sum);
      }
    }
    for (int e : cut.edges()) {
      int a = nodes + e;
      if (column[a] < 0) {
        rhs -= list[a].min();
      } else {
        weights.merge(column[a], 1L, Long::sum);
      }
    }
    weights.values().removeIf(w -> w == 0);
    if (weights.isEmpty()) {
      return null;
    }
    int[] cs = new int[weights.size()];
    long[] ws = new long[weights.size()];
    int k = 0;
    for (Map.Entry<Integer, Long> e : weights.entrySet()) {
      cs[k] = e.getKey();
      ws[k++] = e.getValue();
    }
    return MirCut.row(cs, ws, rhs, cut.efficacy());
  }

  /**
   * Rounds of cuts from a separation at the root, each followed by a re-solve, shared by the Hall
   * and tree cuts.
   *
   * @param separation the violated cuts of the current solution, as rows
   * @param rounds the most rounds
   * @param toSparse whether a dense tableau with no room left moves to the sparse simplex once the
   *     cuts have raised the bound
   * @return the status of the last solve and the number of cuts kept
   */
  private long[] separatedRounds(
      java.util.function.Supplier<List<MirCut>> separation, int rounds, boolean toSparse) {
    double start = lp.value(0);
    int firstCount = rows();
    LpSolver first = lp.copy();
    int[] firstRows = lpRow;
    int added = 0;
    int stall = 0;
    int status = DualSimplex.OPTIMAL;
    Set<List<Long>> seen = new HashSet<>();
    for (int round = 0; round < rounds && stall < CAPACITY_STALL; round++) {
      if (toSparse
          && simplex == Simplex.DENSE
          && Math.abs(lp.value(0) - start) > 1e-6 * (1 + Math.abs(start))
          && moveToSparse()) {
        // the cuts raised the bound and the dense tableau has no room for another round: the rows
        // and the cuts so far move to the sparse simplex for good (ch130 of surface-based-tsp
        // needs about 1,300 tree cuts, which the dense cap stops at a third of the bound's gain);
        // the bound has moved, so the cuts are not dropped at the end either
        denseBeforeCuts = null;
        denseLpRow = null;
        denseInLp = null;
        denseInactive = null;
      }
      List<MirCut> found = separation.get();
      found.sort(Comparator.comparingDouble((MirCut c) -> -c.efficacy));
      List<MirCut> chosen = new ArrayList<>();
      int n = lp.columns();
      for (MirCut row : found) {
        long m = (long) lp.rows() + chosen.size() + 1;
        if (chosen.size() >= CUTS_PER_ROUND
            || simplex == Simplex.DENSE && m * (m + n) > MAX_TABLEAU) {
          break;
        }
        if (seen.add(key(row))) {
          chosen.add(row);
        }
      }
      if (chosen.isEmpty()) {
        break;
      }
      LpSolver kept = lp.copy();
      int[] keptRows = lpRow;
      double before = lp.value(0);
      addCuts(chosen);
      long size = Math.max(1, lp.pivotWork());
      status = rootSolve(lp, roundPivots(size), rootWork() / CUT_ROUNDS);
      if (status == DualSimplex.LIMIT) {
        dropCuts(chosen.size(), kept, keptRows);
        status = DualSimplex.OPTIMAL;
        break;
      }
      added += chosen.size();
      if (status != DualSimplex.OPTIMAL) {
        break;
      }
      boolean moved = Math.abs(lp.value(0) - before) > 1e-6 * (1 + Math.abs(before));
      stall = moved ? 0 : stall + 1;
    }
    if (status == DualSimplex.OPTIMAL
        && added > 0
        && Math.abs(lp.value(0) - start) <= 1e-6 * (1 + Math.abs(start))) {
      // cuts that do not move the bound only make each solve dearer
      dropCuts(added, first, firstRows);
      added = 0;
    }
    keepCapacityForms(firstCount, added);
    return new long[] {status, added};
  }

  // the Hall cuts violated by the solution of the simplex, at most limit of each constraint, as
  // rows; a variable that is not a column stays out of them
  private List<MirCut> violatedHall(int limit) {
    List<MirCut> found = new ArrayList<>();
    for (int c = 0; c < hall.size(); c++) {
      int[] column = hallColumns[c];
      double[] value = new double[column.length];
      for (int a = 0; a < value.length; a++) {
        value[a] = column[a] < 0 ? Double.NaN : lp.value(column[a]);
      }
      for (AlldifferentCuts.Cut cut : hall.get(c).separate(value, limit)) {
        MirCut row = row(cut, column);
        row.source = "hall";
        found.add(row);
      }
    }
    return found;
  }

  // the violated Hall cuts, the most efficacious first, at most limit and within the dense cap;
  // the keys of the cuts chosen are added to seen, and cuts already seen are left out
  private List<MirCut> separateHall(int limit, Set<List<Long>> seen) {
    List<MirCut> found = violatedHall(limit);
    found.sort(Comparator.comparingDouble((MirCut c) -> -c.efficacy));
    List<MirCut> chosen = new ArrayList<>();
    int n = lp.columns();
    for (MirCut row : found) {
      long m = (long) lp.rows() + chosen.size() + 1;
      if (chosen.size() >= limit || simplex == Simplex.DENSE && m * (m + n) > MAX_TABLEAU) {
        break;
      }
      if (seen.add(key(row))) {
        chosen.add(row);
      }
    }
    return chosen;
  }

  /**
   * Sets whether Hall cuts are also separated in search ({@code org.jacop.lp.alldiffSearch}, off by
   * default), for tests.
   *
   * @param on whether they are
   */
  void setAlldiffSearch(boolean on) {
    alldiffSearch = on;
  }

  // Hall cuts from the solution of an optimal solve in search: the violated ones go into the
  // simplex and the pool, and the relaxation is solved again with them
  private int searchHallCuts(int limit) {
    alldiffSeparations++;
    List<MirCut> chosen = separateHall(ALLDIFF_SEARCH_CUTS, hallSeen);
    if (chosen.isEmpty()) {
      hallPeriod = Math.min(2 * hallPeriod, CAPACITY_MAX_PERIOD);
      return LpSolver.OPTIMAL;
    }
    int first = rows();
    double before = lp.value(0);
    addCuts(chosen);
    alldiffSearchCuts += chosen.size();
    keepCapacityForms(first, chosen.size());
    int status = solvePool(limit);
    hallPeriod = nextPeriod(hallPeriod, moved(status, before));
    return status;
  }

  // whether the cuts just added moved the objective bound of the re-solve or made it infeasible;
  // without the gate (org.jacop.lp.searchCutGate=false) any violated cut counts
  private boolean moved(int status, double before) {
    boolean moved =
        status == LpSolver.INFEASIBLE
            || status == LpSolver.OPTIMAL
                && Math.abs(lp.value(0) - before) > 1e-6 * (1 + Math.abs(before));
    if (moved) {
      searchSeparationsMoved++;
    }
    return moved || !SEARCH_CUT_GATE;
  }

  // the period of a separation in search after one that found cuts: halved when they moved the
  // bound, doubled (up to CAPACITY_MAX_PERIOD) when they did not
  private static int nextPeriod(int period, boolean moved) {
    return moved ? Math.max(1, period / 2) : Math.min(2 * period, CAPACITY_MAX_PERIOD);
  }

  /**
   * Sets whether energy cuts are also separated in search ({@code org.jacop.lp.energySearch}, off
   * by default), for tests.
   *
   * @param on whether they are
   */
  void setEnergySearch(boolean on) {
    energySearch = on;
  }

  // energy cuts from the solution of an optimal solve in search, over the bounds of the first
  // solve: the violated ones go into the simplex and the pool, and the relaxation is solved again
  private int searchEnergyCuts(int limit) {
    energySeparations++;
    int n = lp.columns();
    double[] value = new double[n];
    for (int j = 0; j < n; j++) {
      value[j] = lp.value(j);
    }
    List<MirCut> found = new ArrayList<>();
    for (int k = 0; k < energy.size(); k++) {
      found.addAll(
          energy.get(k).separate(energyColumns[k], value, energyLo, energyHi, CUTS_PER_ROUND));
    }
    labelled(found, 0, "energy");
    found.sort(Comparator.comparingDouble((MirCut c) -> -c.efficacy));
    List<MirCut> chosen = new ArrayList<>();
    for (MirCut row : found) {
      long m = (long) lp.rows() + chosen.size() + 1;
      if (chosen.size() >= CAPACITY_SEARCH_CUTS
          || simplex == Simplex.DENSE && m * (m + n) > MAX_TABLEAU) {
        break;
      }
      if (energySeen.add(key(row))) {
        chosen.add(row);
      }
    }
    if (chosen.isEmpty()) {
      energyPeriod = Math.min(2 * energyPeriod, CAPACITY_MAX_PERIOD);
      return LpSolver.OPTIMAL;
    }
    int first = rows();
    double before = lp.value(0);
    addCuts(chosen);
    energySearchCuts += chosen.size();
    keepCapacityForms(first, chosen.size());
    int status = solvePool(limit);
    energyPeriod = nextPeriod(energyPeriod, moved(status, before));
    return status;
  }

  // the Hall cut as a row sum w x <= rhs over the columns of the variables of its constraint
  private static MirCut row(AlldifferentCuts.Cut cut, int[] column) {
    int[] vars = cut.vars();
    long sign = cut.lower() ? -1 : 1;
    Map<Integer, Long> weights = new java.util.TreeMap<>();
    for (int a : vars) {
      weights.merge(column[a], sign, Long::sum);
    }
    int[] cs = new int[weights.size()];
    long[] ws = new long[weights.size()];
    int k = 0;
    for (Map.Entry<Integer, Long> e : weights.entrySet()) {
      cs[k] = e.getKey();
      ws[k++] = e.getValue();
    }
    return MirCut.row(cs, ws, sign * cut.bound(), cut.efficacy());
  }

  // the cuts violated by the solution of the simplex, at most limit and within the dense cap, as
  // rows; the keys of the cuts chosen are added to seen, and cuts already seen are left out
  private List<MirCut> separateCapacity(int limit, Set<List<Long>> seen, boolean root) {
    List<MirCut> chosen = new ArrayList<>();
    int n = lp.columns();
    for (int c = 0; c < capacity.size(); c++) {
      CapacityCuts cc = capacity.get(c);
      IntVar[] literals = cc.literals();
      int[] column = capacityColumns[c];
      double[] value = new double[literals.length];
      for (int a = 0; a < literals.length; a++) {
        value[a] = column[a] < 0 ? literals[a].min() : lp.value(column[a]);
      }
      for (CapacityCuts.Cut cut : cc.separate(value, limit, root || COMB_SEARCH)) {
        MirCut row = row(cut, column);
        if (row != null) {
          row.source = "capacity";
        }
        long m = (long) lp.rows() + chosen.size() + 1;
        if (chosen.size() >= limit || simplex == Simplex.DENSE && m * (m + n) > MAX_TABLEAU) {
          break;
        }
        if (row != null && seen.add(key(row))) {
          chosen.add(row);
        }
      }
    }
    return chosen;
  }

  // the rows [first, first + count) as forms of capacity cuts, for the copies
  private void keepCapacityForms(int first, int count) {
    for (int i = first; i < first + count; i++) {
      IntVar[] vars = new IntVar[rowColumns[i].length];
      for (int k = 0; k < vars.length; k++) {
        vars[k] = x[rowColumns[i][k]];
      }
      capacityForms.add(new LinearForm(vars, rowWeights[i].clone(), rowHi[i], LinearForm.LE));
    }
  }

  // MIR and Gomory cuts from the solution of an optimal solve in search, over the bounds of the
  // first solve: the most efficacious ones go into the simplex and the pool, and the relaxation is
  // solved again with them
  private int searchMirCuts(int limit) {
    mirSeparations++;
    int n = lp.columns();
    List<MirCut> found =
        separateCuts(
            Arrays.copyOf(rootLo, n),
            Arrays.copyOf(rootHi, n),
            mirRows,
            mirSeen,
            MIR_SEARCH_WEIGHT);
    List<MirCut> chosen =
        found.size() > MIR_SEARCH_CUTS ? found.subList(0, MIR_SEARCH_CUTS) : found;
    for (MirCut c : found.subList(chosen.size(), found.size())) {
      mirSeen.remove(key(c));
    }
    if (chosen.isEmpty()) {
      mirPeriod = Math.min(2 * mirPeriod, CAPACITY_MAX_PERIOD);
      return LpSolver.OPTIMAL;
    }
    double before = lp.value(0);
    addCuts(new ArrayList<>(chosen));
    mirSearchCuts += chosen.size();
    int status = solvePool(limit);
    mirPeriod = nextPeriod(mirPeriod, moved(status, before));
    return status;
  }

  // capacity and multistar cuts from the solution of an optimal solve in search: the violated
  // ones go into the simplex and the pool, and the relaxation is solved again with them
  private int searchCapacityCuts(int limit) {
    capacitySeparations++;
    List<MirCut> chosen = separateCapacity(CAPACITY_SEARCH_CUTS, capacitySeen, false);
    if (chosen.isEmpty()) {
      capacityPeriod = Math.min(2 * capacityPeriod, CAPACITY_MAX_PERIOD);
      return LpSolver.OPTIMAL;
    }
    int first = rows();
    double before = lp.value(0);
    addCuts(chosen);
    capacitySearchCuts += chosen.size();
    keepCapacityForms(first, chosen.size());
    int status = solvePool(limit);
    capacityPeriod = nextPeriod(capacityPeriod, moved(status, before));
    return status;
  }

  // the cut as a row sum w x <= rhs over the columns, or null when an arc is not a column
  private static MirCut row(CapacityCuts.Cut cut, int[] column) {
    Map<Integer, Long> weights = new java.util.TreeMap<>();
    long sign = cut.entering() ? -1 : 1;
    int[] arcs = cut.arcs();
    long[] given = cut.weights();
    for (int k = 0; k < arcs.length; k++) {
      if (column[arcs[k]] < 0) {
        return null;
      }
      weights.merge(column[arcs[k]], sign * given[k], Long::sum);
    }
    weights.values().removeIf(w -> w == 0);
    if (weights.isEmpty()) {
      return null;
    }
    int[] cs = new int[weights.size()];
    long[] ws = new long[weights.size()];
    int k = 0;
    for (Map.Entry<Integer, Long> e : weights.entrySet()) {
      cs[k] = e.getKey();
      ws[k++] = e.getValue();
    }
    return MirCut.row(cs, ws, sign * cut.bound(), cut.efficacy());
  }

  private static List<Long> key(MirCut c) {
    List<Long> key = new ArrayList<>();
    for (int k = 0; k < c.columns.length; k++) {
      key.add((long) c.columns[k]);
      key.add(c.weights[k]);
    }
    key.add(c.rhs);
    return key;
  }

  /**
   * Returns the cuts of one round from the current solution of the simplex, without changing the
   * rows or the simplex; {@link #addCuts(List)} installs them.
   *
   * @param lo the global lower bounds by column, of the first solve
   * @param hi the global upper bounds by column, of the first solve
   * @param unitRows the rows that are not cuts, as aggregates
   * @param seen the cuts chosen in earlier rounds, as keys; the cuts chosen are added
   * @param maxWeight the largest weight of a cut; larger cuts are scaled down ({@link
   *     MirCut#capped})
   * @return the cuts chosen, most efficacious first
   */
  private List<MirCut> separateCuts(
      long[] lo, long[] hi, Aggregate[] unitRows, Set<List<Long>> seen, long maxWeight) {
    int n = lp.columns();
    double[] value = new double[n];
    for (int j = 0; j < n; j++) {
      value[j] = lp.value(j);
    }
    List<MirCut> found = new ArrayList<>();
    List<Integer> sources = new ArrayList<>();
    for (int j = 0; j < n; j++) {
      double f = value[j] - Math.floor(value[j]);
      if (lp.basicRow(j) >= 0 && f > 0.01 && f < 0.99) {
        sources.add(j);
      }
    }
    sources.sort(Comparator.comparingDouble(j -> Math.abs(value[j] - Math.floor(value[j]) - 0.5)));
    for (int j : sources.subList(0, Math.min(MAX_SOURCES, sources.size()))) {
      int foundBefore = found.size();
      double[] y = byRow(lp.inverseRow(lp.basicRow(j)));
      long[] lambda = scaled(y, gomoryScale);
      if (lambda != null) {
        long[] coarse = null;
        if (slackGomory && !slackGomory(lambda, j, value, lo, hi, found)) {
          coarse = scaled(y, GOMORY_FALLBACK);
          slackGomory(coarse, j, value, lo, hi, found);
        }
        Aggregate g = aggregate(lambda);
        if (g == null && gomoryScale != GOMORY_FALLBACK) {
          g = aggregate(coarse != null ? coarse : scaled(y, GOMORY_FALLBACK));
        }
        mir(g, value, lo, hi, found);
      }
      labelled(found, foundBefore, "gomory");
    }
    Set<MirCut> dual = Collections.newSetFromMap(new IdentityHashMap<>());
    if (dualAggregateOn) {
      int before = found.size();
      dualAggregate(value, lo, hi, found);
      dual.addAll(found.subList(before, found.size()));
    }
    Set<MirCut> zeroHalf = Collections.newSetFromMap(new IdentityHashMap<>());
    // a refutation also takes the zero-half cuts: they are the odd-cycle inequalities of the
    // cardinality refutations (domset hexgrid)
    if (zeroHalfOn || pseudoObjective) {
      int foundBefore = found.size();
      zeroHalf(value, lo, hi, found, zeroHalf);
      labelled(found, foundBefore, "zerohalf");
    }
    int unitBefore = found.size();
    for (Aggregate row : unitRows) {
      mir(row, value, lo, hi, found);
    }
    labelled(found, unitBefore, "mir");
    if (maxWeight < Long.MAX_VALUE) {
      List<MirCut> small = new ArrayList<>(found.size());
      for (MirCut c : found) {
        MirCut d = MirCut.capped(c, maxWeight, value, lo, hi);
        if (d != null) {
          small.add(d);
          if (d != c && zeroHalf.contains(c)) {
            zeroHalf.add(d);
          }
          if (d != c && dual.contains(c)) {
            dual.add(d);
          }
        }
      }
      found = small;
    }
    found.sort(Comparator.comparingDouble((MirCut c) -> -c.efficacy));
    List<MirCut> chosen = new ArrayList<>();
    for (MirCut c : found) {
      long m = (long) lp.rows() + chosen.size() + 1;
      if (chosen.size() >= CUTS_PER_ROUND || simplex == Simplex.DENSE && m * (m + n) > tableauCap) {
        break;
      }
      List<Long> key = new ArrayList<>();
      for (int k = 0; k < c.columns.length; k++) {
        key.add((long) c.columns[k]);
        key.add(c.weights[k]);
      }
      key.add(c.rhs);
      if (!seen.contains(key) && orthogonal(c, chosen)) {
        seen.add(key);
        chosen.add(c);
        if (zeroHalf.contains(c)) {
          zeroHalfCuts++;
        }
        if (dual.contains(c)) {
          dualCuts++;
        }
      }
    }
    return chosen;
  }

  // names the source of the cuts of found from index from on
  private static void labelled(List<MirCut> found, int from, String source) {
    for (int k = from; k < found.size(); k++) {
      found.get(k).source = source;
    }
  }

  /**
   * Adds the zero-half cuts of the rows in the simplex to found: each row that is tight within
   * ZERO_HALF_SLACK on a side enters as {@code sum w x <= b} (the lower side negated), the
   * separator picks sets of them (ZeroHalfCuts), and each set's exact sum is rounded with the MIR
   * of divisor 2 over the global bounds, so the cut holds everywhere.
   */
  private void zeroHalf(
      double[] value, long[] lo, long[] hi, List<MirCut> found, Set<MirCut> zeroHalf) {
    int n = lp.columns();
    int pool = rows();
    double[] distance = new double[n];
    for (int j = 0; j < n; j++) {
      double v = Math.clamp(value[j], (double) lo[j], (double) hi[j]);
      distance[j] = Math.min(v - lo[j], hi[j] - v);
    }
    int maxLength = 100 + n / 20;
    // each candidate is a pool row and the sign it enters with
    List<int[]> candidates = new ArrayList<>();
    List<Double> slacks = new ArrayList<>();
    for (int i = 0; i < pool; i++) {
      double act = zeroHalfActivity(i, maxLength, value);
      if (Double.isNaN(act)) {
        continue;
      }
      boolean equality = hasLo[i] && hasHi[i] && rowLo[i] == rowHi[i];
      if (hasHi[i] && rowHi[i] - act <= ZERO_HALF_SLACK) {
        candidates.add(new int[] {i, 1});
        slacks.add(Math.max(0, rowHi[i] - act));
      }
      if (!equality && hasLo[i] && act - rowLo[i] <= ZERO_HALF_SLACK) {
        candidates.add(new int[] {i, -1});
        slacks.add(Math.max(0, act - rowLo[i]));
      }
    }
    if (candidates.isEmpty()) {
      return;
    }
    Integer[] order = new Integer[candidates.size()];
    for (int k = 0; k < order.length; k++) {
      order[k] = k;
    }
    Arrays.sort(
        order, Comparator.comparingDouble((Integer k) -> slacks.get(k)).thenComparingInt(k -> k));
    int r = Math.min(order.length, ZERO_HALF_ROWS);
    int[][] columns = new int[r][];
    long[][] weights = new long[r][];
    boolean[] odd = new boolean[r];
    double[] slack = new double[r];
    int[][] picked = new int[r][];
    for (int t = 0; t < r; t++) {
      int[] cand = candidates.get(order[t]);
      int i = cand[0];
      picked[t] = cand;
      columns[t] = rowColumns[i];
      weights[t] = rowWeights[i];
      slack[t] = slacks.get(order[t]);
      // the parity of the right side with the odd columns at their nearer bound
      long side = cand[1] > 0 ? rowHi[i] : -rowLo[i];
      long parity = side & 1;
      for (int k = 0; k < columns[t].length; k++) {
        if ((weights[t][k] & 1) != 0) {
          int j = columns[t][k];
          double v = Math.clamp(value[j], (double) lo[j], (double) hi[j]);
          long bound = hi[j] - v < v - lo[j] ? hi[j] : lo[j];
          parity ^= bound & 1;
        }
      }
      odd[t] = parity != 0;
    }
    for (int[] set :
        ZeroHalfCuts.separate(columns, weights, odd, slack, distance, ZERO_HALF_SETS)) {
      long[] lambda = new long[pool];
      for (int t : set) {
        lambda[picked[t][0]] += picked[t][1];
      }
      MirCut c = zeroHalfCut(aggregate(lambda), value, lo, hi);
      if (c != null && c.efficacy >= ZERO_HALF_EFFICACY) {
        found.add(c);
        zeroHalf.add(c);
      }
    }
  }

  // the zero-half cut of an aggregate: its MIR with divisor 2, or null
  private static MirCut zeroHalfCut(Aggregate g, double[] value, long[] lo, long[] hi) {
    if (g == null || !g.hasUpper() || g.columns().length == 0) {
      return null;
    }
    long[] raw = MirCut.raw(g.columns(), g.coef(), g.upper(), value, lo, hi, 2);
    if (raw == null) {
      return null;
    }
    return MirCut.finish(
        g.columns(), raw, raw[g.columns().length], value, lo, hi, MirCut.REDUCE_CUTS);
  }

  // the activity of pool row i at the LP solution, or NaN if the row cannot enter a zero-half cut:
  // not in the LP, too long, without an odd weight or with a weight too large
  private double zeroHalfActivity(int i, int maxLength, double[] value) {
    int[] cs = rowColumns[i];
    if (!inLp[i] || cs.length > maxLength) {
      return Double.NaN;
    }
    long[] ws = rowWeights[i];
    boolean anyOdd = false;
    boolean small = true;
    double act = 0;
    for (int k = 0; k < cs.length; k++) {
      anyOdd |= (ws[k] & 1) != 0;
      small &= Math.abs(ws[k]) <= 1_000_000;
      act += ws[k] * value[cs[k]];
    }
    return anyOdd && small ? act : Double.NaN;
  }

  // whether the cut is far enough from parallel to each of the cuts chosen
  private static boolean orthogonal(MirCut c, List<MirCut> chosen) {
    for (MirCut o : chosen) {
      double dot = 0;
      int p = 0;
      int q = 0;
      while (p < c.columns.length && q < o.columns.length) {
        if (c.columns[p] == o.columns[q]) {
          dot += (double) c.weights[p] * o.weights[q];
          p++;
          q++;
        } else if (c.columns[p] < o.columns[q]) {
          p++;
        } else {
          q++;
        }
      }
      if (Math.abs(dot) > MAX_PARALLELISM * c.norm * o.norm) {
        return false;
      }
    }
    return true;
  }

  // the MIR cuts of the dual-weighted rows, on by default (-Dorg.jacop.lp.dualAggregate=false: off)
  static boolean dualAggregateOn =
      !Boolean.FALSE.toString().equals(System.getProperty("org.jacop.lp.dualAggregate"));

  /**
   * Adds the MIR cuts of the rows weighted by their dual values, without the rows of the objective
   * (column 0): {@code sum y_i a_i x >= y b} is the row whose bound the LP proves, and its rounding
   * by a divisor near the objective's coefficients counts the columns a solution needs (a
   * Chvatal-Gomory cut with the LP's own multipliers). On covers with near-equal costs this is the
   * cut that proves the optimum (MiniZinc Challenge 2021 wmsmc-int).
   *
   * <p>V. Chvatal, Edmonds polytopes and a hierarchy of combinatorial problems, Discrete
   * Mathematics 4(4), 1973; H. Marchand and L. A. Wolsey, Aggregation and mixed integer rounding to
   * solve MIPs, Operations Research 49(3), 2001.
   */
  private void dualAggregate(double[] value, long[] lo, long[] hi, List<MirCut> found) {
    double[] y = byRow(lp.duals());
    boolean any = false;
    for (int i = 0; i < y.length; i++) {
      int[] cs = rowColumns[i];
      for (int c : cs) {
        if (c == 0) {
          y[i] = 0;
          break;
        }
      }
      any |= y[i] != 0;
    }
    if (!any) {
      return;
    }
    long[] lambda = scaled(y, gomoryScale);
    if (lambda != null) {
      mir(aggregate(lambda), value, lo, hi, found);
    }
  }

  private static void mir(Aggregate g, double[] value, long[] lo, long[] hi, List<MirCut> found) {
    if (g == null) {
      return;
    }
    if (g.hasUpper()) {
      MirCut c = MirCut.of(g.columns(), g.coef(), g.upper(), value, lo, hi);
      if (c != null) {
        found.add(c);
      }
    }
    if (g.hasLower()) {
      if (g.lower() == Long.MIN_VALUE) {
        return;
      }
      long[] neg = new long[g.coef().length];
      for (int k = 0; k < neg.length; k++) {
        if (g.coef()[k] == Long.MIN_VALUE) {
          return;
        }
        neg[k] = -g.coef()[k];
      }
      MirCut c = MirCut.of(g.columns(), neg, -g.lower(), value, lo, hi);
      if (c != null) {
        found.add(c);
      }
    }
  }

  /**
   * Adds the rows of the constraints that are not linear relations after the first solve without
   * them, on a simplex over all the columns, and keeps them when they make the relaxation
   * infeasible, raise the bound of the objective, or are few: many rows that do not move the bound
   * only make each solve dearer.
   *
   * @param status the status of the solve without them
   * @return the status of the solve of the rows kept
   */
  private int addExtraRows(int status) {
    int k = extraColumns.length;
    double before = Double.NaN;
    if (status == DualSimplex.OPTIMAL && objective != null) {
      before = lp.value(0);
      baseBound = before;
    }
    int m = rows();
    int plain = Math.min(plainExtra, k);
    int tiered = Math.min(Math.max(triedExtra, plain), k);
    // the prefixes of the extra rows tried, the longest first: all of them, those before the flow
    // models of layered graphs, and those before every value encoding. The value encodings are many
    // rows over many columns: they are kept only when they make the relaxation infeasible or raise
    // its bound, not for being few. Once a prefix is kept, only the flow models are tried without:
    // they are kept only when they do better than the rows before them
    int lead = Math.min(leadExtra, k);
    // with the value encodings ahead of rows that did not all fit, the encodings alone are tried
    // first: the rows after them are only a share of the candidates, and a trial over all of them
    // can spend the root budget without an optimal solve (ROADEF 2020 A_06: 6,720 rows over 39,003
    // columns stopped at the limit, and the encodings tried after them got no time)
    int[] prefixes =
        lead > 0 && lead < k
            ? IntStream.of(lead, k, tiered, plain).filter(q -> q > 0).distinct().toArray()
            : IntStream.of(k, tiered, plain).filter(q -> q > 0).distinct().toArray();
    LpSolver full = null;
    int kept = 0;
    int keptStatus = status;
    int last = k;
    boolean stop = false;
    for (int i = 0; i < prefixes.length && !stop; i++) {
      int p = prefixes[i];
      if (full != null && (p < tiered || kept == lead)) {
        stop = true;
      } else {
        LpSolver trial = trialRows(status, before, m, p, columnsOf(p), p == plain);
        last = p;
        if (trial == null) {
          // the shorter prefix does not help: the longer one kept stays. When the value encodings
          // alone stopped at the time of a large root solve, the longer prefixes, which hold them,
          // would only spend more of it
          stop = full != null || p == lead && lead < k && trialStatus == LpSolver.LIMIT;
        } else if (full != null && !sameBound(full, keptStatus, trial, trialStatus)) {
          // the longer prefix does better
          droppedPivots += trial.pivots();
          stop = true;
        } else {
          if (full != null) {
            droppedPivots += full.pivots();
          }
          full = trial;
          kept = p;
          keptStatus = trialStatus;
        }
      }
    }
    searchStartMin = null;
    searchStartMax = null;
    leadKept = full != null && lead > 0 && kept == lead;
    if (full != null && kept != last) {
      // a shorter prefix was tried after the one kept
      setExtraRows(m, kept);
    }
    if (full != null && kept < k) {
      k = kept;
      extraForms = new ArrayList<>(extraForms.subList(0, kept));
    }
    extraColumns = new int[0][];
    extraWeights = new long[0][];
    if (full != null) {
      keptExtraForms = extraForms;
      extraRows = k;
      beforeExtra = lp;
      baseRows = m;
      extraLimits = limits;
      extraCall = calls;
      extraFailures = failures;
      droppedPivots += lp.pivots();
      lp = full;
      allRowsInSimplex(m + k);
      extraCarry = carriesBound(status, before, m, keptStatus);
      extraSparse = trialSparse;
      trialSparse = false;
      if (keptStatus == LpSolver.OPTIMAL) {
        moveExtraToSparse();
      }
      return keptStatus;
    }
    // the rows of the last trial are the m + last rows
    poolExtraRows(m, last);
    return status;
  }

  // whether the extra rows kept carry the bound: the relaxation without them is optimal at a bound
  // that does not cut the domain of the objective, and with them it is infeasible or cuts it
  // (set covering: the objective row alone is bounded by 0, the clauses make it 246.8 on scpa1)
  private boolean carriesBound(int status, double before, int given, int keptStatus) {
    if (!baseBoundsNothing(status, before, given)) {
      return false;
    }
    long domain = maximize ? objective.max() : objective.min();
    if (keptStatus == LpSolver.INFEASIBLE) {
      return true;
    }
    double with = lp.value(0);
    return keptStatus == LpSolver.OPTIMAL
        && (maximize ? integerBound(with) < domain : integerBound(with) > domain);
  }

  // whether the relaxation without the extra rows is at most the row of the objective
  // (EXTRA_SPARSE_ROWS), optimal at a bound that does not cut the domain of the objective: the
  // bound
  // it gives the search is the domain's own
  private boolean baseBoundsNothing(int status, double before, int given) {
    if (objective == null
        || given > EXTRA_SPARSE_ROWS
        || status != LpSolver.OPTIMAL
        || Double.isNaN(before)) {
      return false;
    }
    long domain = maximize ? objective.max() : objective.min();
    return maximize ? integerBound(before) >= domain : integerBound(before) <= domain;
  }

  // the columns of the base rows and the first p extra rows
  private int columnsOf(int p) {
    if (p == extraColumns.length) {
      return x.length;
    }
    int n = lp.columns();
    for (int q = 0; q < p; q++) {
      for (int j : extraColumns[q]) {
        n = Math.max(n, j + 1);
      }
    }
    return n;
  }

  // whether two root trials end the same: both infeasible, or both optimal at the same bound of
  // the integer objective (its LP bound rounded up when minimizing, down when maximizing), so that
  // the flow rows are kept only for a bound the search can use
  private boolean sameBound(LpSolver a, int statusA, LpSolver b, int statusB) {
    if (statusA != statusB) {
      return false;
    }
    if (statusA != DualSimplex.OPTIMAL || objective == null) {
      return true;
    }
    return integerBound(a.value(0)) == integerBound(b.value(0));
  }

  private double integerBound(double v) {
    double slack = 1e-6 * (1 + Math.abs(v));
    return maximize ? Math.floor(v + slack) : Math.ceil(v - slack);
  }

  // the rows are the m given ones and the first k extra rows
  private void setExtraRows(int m, int k) {
    rowColumns = Arrays.copyOf(rowColumns, m + k);
    rowWeights = Arrays.copyOf(rowWeights, m + k);
    rowLo = Arrays.copyOf(rowLo, m + k);
    rowHi = Arrays.copyOf(rowHi, m + k);
    hasLo = Arrays.copyOf(hasLo, m + k);
    hasHi = Arrays.copyOf(hasHi, m + k);
    for (int q = 0; q < k; q++) {
      int i = m + q;
      rowColumns[i] = extraColumns[q];
      rowWeights[i] = extraWeights[q];
      hasLo[i] = extraRelation[q] != LinearForm.LE;
      hasHi[i] = extraRelation[q] != LinearForm.GE;
      rowLo[i] = extraSide[q];
      rowHi[i] = extraSide[q];
    }
  }

  // the status of the last root solve of trialRows
  private int trialStatus;
  // the status of the solve of trialRows over the bounds of the search start
  private int trialStatusAtStart = LpSolver.OPTIMAL;

  /**
   * Solves the given rows and the first k extra rows over the first n columns at the root, and
   * returns that simplex when the rows are kept, null otherwise (the rows are then m + k, to be
   * truncated by the caller). With few, at most SMALL_EXTRA rows are kept even when the bound
   * stays.
   */
  private LpSolver trialRows(int status, double before, int m, int k, int n, boolean few) {
    setExtraRows(m, k);
    LpSolver full = rowSolver(m + k, n);
    int withExtra = trialSolve(full, status, before, m, k, n, few);
    if (withExtra == LpSolver.LIMIT && few && baseBoundsNothing(status, before, m)) {
      LpSolver sparse = sparseTrial(m + k, n);
      if (sparse != null) {
        droppedPivots += full.pivots();
        full = sparse;
        withExtra = trialSolve(full, status, before, m, k, n, few);
      }
    }
    // the other rows of a model with trees are kept: alone they rarely move the bound, but with
    // the tree cuts made later they do (st70 of surface-based-tsp: 633 without them, 675 with)
    trialStatus = withExtra;
    boolean kept = trialKeep || !trialCut && (keepExtra || !trees.isEmpty());
    if (!kept
        && !trialCut
        && objective == null
        && SATISFACTION_PROBATION > 0
        && k == extraColumns.length
        && withExtra == LpSolver.OPTIMAL) {
      // a satisfaction model has no bound to raise: the rows stay on probation, and are dropped
      // unless they fail nodes in search (car sequencing p6-76: the class encodings and option
      // tables fail one LP solve in six and prove it in 17 s, 300 conflicts; without them the
      // window rows fail one in twenty and the proof takes 295 s and 1.2 million conflicts)
      kept = true;
      probation = true;
      probationKept = true;
    }
    if (kept) {
      return full;
    }
    droppedPivots += full.pivots();
    if (trialSparse) {
      simplex = Simplex.DENSE;
      trialSparse = false;
    }
    return null;
  }

  // whether the rows of the last trialSolve are kept for their bound, and whether it stopped
  // before the solve over the current bounds (then they are not kept for any other reason)
  private boolean trialKeep;
  private boolean trialCut;

  // the root solves of a trial of the extra rows on the simplex full; returns the status of the
  // solve with them at the current bounds and sets trialKeep
  private int trialSolve(
      LpSolver full, int status, double before, int m, int k, int n, boolean few) {
    for (int j = 0; j < n; j++) {
      setBounds(full, j);
    }
    long size = Math.max(1, full.pivotWork());
    int pivots = Math.clamp(ROOT_WORK / size, 5, rootPivots);
    boolean keep;
    // the pivots and nanoseconds of the solve at the bounds of the start of the search, which cap
    // the solve at the current bounds after it (Long.MAX_VALUE without it)
    long startPivots = Long.MAX_VALUE;
    long startNanos = Long.MAX_VALUE;
    if (searchStartMin != null) {
      // solved after a search that started without it: the rows are kept as they would have been
      // at the start of that search, not for a bound that the facts the search found raise
      // (mqueens n11: 1,859 extra rows kept for a bound 0 -> 1, 12 s of LP in search instead of
      // 0.3 s)
      LpSolver base = rowSolver(m, n);
      for (int j = 0; j < n; j++) {
        setSearchStartBounds(base, j);
        setSearchStartBounds(full, j);
      }
      int baseStatus = rootSolve(base, pivots, rootWork());
      double startBound =
          baseStatus == LpSolver.OPTIMAL && objective != null ? base.value(0) : Double.NaN;
      droppedPivots += base.pivots();
      long before0 = full.pivots();
      long started = System.nanoTime();
      int startStatus = rootSolve(full, pivots, rootWork());
      if (k == leadExtra && startStatus == LpSolver.LIMIT) {
        // as below: the value encodings alone get the time of a large root solve
        extendDeadline = Math.max(extendDeadline, System.nanoTime() + largeRootNanos);
        startStatus = extendRootSolve(full, startStatus, true);
      }
      trialStatusAtStart = startStatus;
      keep = keepRows(startStatus, baseStatus, startBound, full, few, k);
      if (keep
          && startStatus == LpSolver.OPTIMAL
          && objective != null
          && !(few && k <= SMALL_EXTRA)) {
        // the bound that the rows raise at the start bounds is no better than the bound the search
        // has found since: they are not kept for it. rna-alignment-k50-23-49 (MaxSAT Evaluation
        // 2024): 13,579 clause rows raise 0 to 443, where the cores of LCG had 532 (the optimum is
        // 536); keeping them took 16.6 s more of root LP before the rows and the LP were dropped
        double b = integerBound(full.value(0));
        keep = maximize ? b < objective.max() : b > objective.min();
      }
      startPivots = Math.max(MIN_RESOLVE_PIVOTS, full.pivots() - before0);
      startNanos = Math.max(MIN_RESOLVE_NANOS, System.nanoTime() - started);
      for (int j = 0; j < n; j++) {
        setBounds(full, j);
      }
    } else {
      keep = false;
    }
    if (searchStartMin != null && k == leadExtra && !keep && trialStatusAtStart == LpSolver.LIMIT) {
      // the value encodings alone did not finish over the bounds of the search start: a second
      // solve over the current bounds would spend the same time again
      trialKeep = false;
      trialCut = true;
      return LpSolver.LIMIT;
    }
    int withExtra;
    if (searchStartMin != null && !keep && !keepExtra && trees.isEmpty()) {
      // rows that the start bounds do not keep are kept at the current bounds only when they make
      // the relaxation infeasible: that solve gets no more than the solve at the start bounds took,
      // and is not extended (rna-alignment-k50-23-49: 4.5 s and 3,172 pivots at the start bounds,
      // 16.6 s and 6,234 pivots at the current ones)
      withExtra =
          rootSolveCapped(
              full, (int) Math.min(large ? Integer.MAX_VALUE : pivots, startPivots), startNanos);
    } else {
      int first = rootSolve(full, pivots, rootWork());
      if (k == leadExtra && first == LpSolver.LIMIT) {
        // the value encodings alone are the model's own rows: their trial gets the time of a large
        // root solve, a share of the time limit of the run, from now
        extendDeadline = Math.max(extendDeadline, System.nanoTime() + largeRootNanos);
      }
      withExtra = extendRootSolve(full, first, true);
    }
    if (searchStartMin == null) {
      keep = keepRows(withExtra, status, before, full, few, k);
    } else if (withExtra == LpSolver.LIMIT) {
      keep = false;
    } else {
      keep |= withExtra == LpSolver.INFEASIBLE;
    }
    trialKeep = keep;
    trialCut = false;
    return withExtra;
  }

  // whether the trial of the extra rows runs on the sparse simplex in place of the dense one
  private boolean trialSparse;

  /**
   * Returns a sparse simplex for a second trial of the extra rows after the dense trial stopped at
   * its root budget, or null: only when the dense tableau would leave a solve in search fewer than
   * EXTRA_SPARSE_PIVOTS pivots and the sparse one costs at most 1/EXTRA_SPARSE_GAIN of it per
   * pivot. On the dense tableau of scpb1 of the OR-Library set covering (300 clauses over 3,000
   * columns, 5 % dense) the trial stopped at its root budget of 970 pivots and the clauses were
   * left out, root bound 0; on the sparse one the bound is 64.5 and the search proves the optimum
   * 69 in 15 s. The caller tries it, also after a search that started without the rows, only for
   * the plain extra rows (no value encodings) of a relaxation whose given rows bound nothing: where
   * they already cut the domain of the objective the dense trial and the dropping of its rows after
   * the limits stay (mqueens n11, prize-collecting, hoist: 2-3x slower with the rows kept on the
   * sparse simplex); a dense trial that ends in its budget stays dense (peacable_queens 8: 257
   * clause rows dense, no limit in search; the 1,352 rows with the value encodings on the sparse
   * simplex took 389 s of LP in 600 s for a bound 31 in place of 32).
   */
  private LpSolver sparseTrial(int rows, int n) {
    if (simplex != Simplex.DENSE || !EXTRA_SPARSE) {
      return null;
    }
    long dense = (long) rows * (rows + n + 1);
    if (WORK / Math.max(1, dense) >= EXTRA_SPARSE_PIVOTS) {
      return null;
    }
    simplex = Simplex.SPARSE;
    LpSolver s = rowSolver(rows, n);
    if (s.pivotWork() * EXTRA_SPARSE_GAIN > dense) {
      simplex = Simplex.DENSE;
      return null;
    }
    trialSparse = true;
    return s;
  }

  // the fewest pivots and nanoseconds that the solve of a trial at the current bounds gets
  private static final long MIN_RESOLVE_PIVOTS = 100;
  private static final long MIN_RESOLVE_NANOS = 100_000_000L;

  // a root solve within at most the given pivots and nanoseconds, also on a large relaxation (whose
  // root solves otherwise share the time of its root)
  private int rootSolveCapped(LpSolver s, int pivots, long nanos) {
    if (s instanceof DualSimplex) {
      return s.solve(pivots);
    }
    long cap = nanos;
    if (large) {
      long now = System.nanoTime();
      if (largeDeadline == 0) {
        largeDeadline = now + largeRootNanos;
      }
      cap = Math.min(cap, Math.max(0, largeDeadline - now));
    }
    return solveWithin(s, pivots, rootWork(), cap);
  }

  // whether the rows of a trial that ends with the given status are kept, against the solve
  // without them that ends with status and bound before
  private boolean keepRows(
      int withExtra, int status, double before, LpSolver full, boolean few, int k) {
    if (withExtra == LpSolver.INFEASIBLE) {
      return true;
    }
    if (withExtra == LpSolver.LIMIT) {
      return false;
    }
    boolean raised =
        status != LpSolver.OPTIMAL
            || !Double.isNaN(before)
                && Math.abs(full.value(0) - before) > 1e-6 * (1 + Math.abs(before));
    return raised || few && k <= SMALL_EXTRA;
  }

  // a simplex over the first rows given and the first n columns, without bounds on the columns
  private LpSolver rowSolver(int rows, int n) {
    double[] lo = new double[rows];
    double[] hi = new double[rows];
    for (int i = 0; i < rows; i++) {
      lo[i] = hasLo[i] ? (double) rowLo[i] : Double.NEGATIVE_INFINITY;
      hi[i] = hasHi[i] ? (double) rowHi[i] : Double.POSITIVE_INFINITY;
    }
    double[] cost = new double[n];
    if (objective != null) {
      cost[0] = maximize ? -1 : 1;
    }
    if (simplex == Simplex.DENSE) {
      double[][] a = new double[rows][n];
      for (int i = 0; i < rows; i++) {
        for (int t = 0; t < rowColumns[i].length; t++) {
          a[i][rowColumns[i][t]] = (double) rowWeights[i][t];
        }
      }
      return new DualSimplex(a, lo, hi, cost);
    }
    return sparse(sparseRows(rows), doubles(rows), lo, hi, cost);
  }

  // the bounds of the variables when a search started with the relaxation suspended
  private int[] searchStartMin;
  private int[] searchStartMax;

  /**
   * Records the bounds of the variables now, at the start of a search during which the relaxation
   * is suspended, so that its first solve after the search keeps the rows of the other constraints
   * as a first solve now would.
   */
  public void rememberSearchStart() {
    if (calls > 0) {
      return;
    }
    searchStartMin = new int[x.length];
    searchStartMax = new int[x.length];
    for (int j = 0; j < x.length; j++) {
      if (!lpOnly[j]) {
        searchStartMin[j] = x[j].min();
        searchStartMax[j] = x[j].max();
      }
    }
  }

  private void setSearchStartBounds(LpSolver solver, int j) {
    if (lpOnly[j]) {
      setBounds(solver, j);
    } else {
      solver.setBounds(j, searchStartMin[j], searchStartMax[j]);
    }
  }

  // the rows of the other constraints after the first m rows, which the root trial did not keep:
  // with org.jacop.lp.poolExtra those over the columns of the simplex stay in the pool, out of the
  // simplex, and enter it when its solution breaks them; the others are removed
  private void poolExtraRows(int m, int k) {
    List<LinearForm> pooled = new ArrayList<>();
    int kept = m;
    for (int q = 0; POOL_EXTRA && q < k; q++) {
      int i = m + q;
      boolean within = true;
      for (int j : rowColumns[i]) {
        within &= j < lp.columns();
      }
      if (within) {
        rowColumns[kept] = rowColumns[i];
        rowWeights[kept] = rowWeights[i];
        rowLo[kept] = rowLo[i];
        rowHi[kept] = rowHi[i];
        hasLo[kept] = hasLo[i];
        hasHi[kept] = hasHi[i];
        kept++;
        pooled.add(extraForms.get(q));
      }
    }
    truncateRows(kept);
    extraForms = new ArrayList<>();
    if (!pooled.isEmpty()) {
      // a copy keeps them, as the prunings found with them are explained by them
      keptExtraForms = pooled;
      inLp = Arrays.copyOf(inLp, kept);
      dormant += pooled.size();
      identityRows = false;
      pooledExtra = pooled.size();
    }
  }

  // whether at least FAIL_RATE of the solves since the extra rows were added failed the node
  private boolean failingWithExtra() {
    long solves = calls - extraCall;
    return FAIL_RATE > 0 && solves > 0 && failures - extraFailures >= FAIL_RATE * solves;
  }

  // the rows of the other constraints make too many solves in search stop at the pivot limit: back
  // to the simplex without them (and without the cuts, which may use them)
  private void dropExtraRows() {
    droppedPivots += lp.pivots() - beforeExtra.pivots();
    lp = beforeExtra;
    if (lp instanceof DualSimplex) {
      // the cuts may have moved the rows to the sparse simplex; the rows before them are dense
      simplex = Simplex.DENSE;
    }
    truncateRows(baseRows);
    allRowsInSimplex(baseRows);
    // the columns that came with the rows are gone: the search cuts leave their variables out
    forgetColumns(capacityColumns, lp.columns());
    forgetColumns(hallColumns, lp.columns());
    beforeExtra = null;
    extraForms = new ArrayList<>();
    extraRows = 0;
    extraDropped = true;
    // the limits were theirs: the relaxation without them starts again as at the root
    stalled = 0;
    idle = 0;
    period = 1;
    credit = WORK;
  }

  // marks the columns from n on as not columns
  private static void forgetColumns(int[][] columns, int n) {
    if (columns == null) {
      return;
    }
    for (int[] column : columns) {
      for (int a = 0; a < column.length; a++) {
        if (column[a] >= n) {
          column[a] = -1;
        }
      }
    }
  }

  // the source of row i of the pool: its cut separator, or the source of its given or further form
  private String source(int i) {
    if (i < cutSource.length && cutSource[i] != null) {
      return cutSource[i];
    }
    LinearForm f;
    if (i < forms.size()) {
      f = forms.get(i);
    } else {
      List<LinearForm> further = keptExtraForms.isEmpty() ? extraForms : keptExtraForms;
      int q = i - forms.size();
      f = q < further.size() ? further.get(q) : null;
      if (f == null) {
        return "further";
      }
    }
    String s = formSource.get(f);
    if (s != null) {
      return s;
    }
    return i < forms.size() ? "row" : "further";
  }

  /**
   * The statistics of the rows by their source, one line per source (see {@link LpSources}), or
   * null unless {@code -Dorg.jacop.lp.sourceStats=true}.
   *
   * @return the lines, or null
   */
  public String sourceReport() {
    return sources == null ? null : sources.report();
  }

  // keeps the first m rows
  private void truncateRows(int m) {
    returns = Arrays.copyOf(returns, Math.min(returns.length, m));
    cutSource = Arrays.copyOf(cutSource, Math.min(cutSource.length, m));
    rowColumns = Arrays.copyOf(rowColumns, m);
    rowWeights = Arrays.copyOf(rowWeights, m);
    rowLo = Arrays.copyOf(rowLo, m);
    rowHi = Arrays.copyOf(rowHi, m);
    hasLo = Arrays.copyOf(hasLo, m);
    hasHi = Arrays.copyOf(hasHi, m);
  }

  // goes back to the simplex before the last k rows, the cuts of the last round; the cuts stay in
  // the pool, out of the simplex, with org.jacop.lp.poolCuts, and are removed otherwise
  private void dropCuts(int k, LpSolver kept, int[] keptRows) {
    int m = rows() - k;
    if (!POOL_CUTS) {
      truncateRows(m);
    }
    droppedPivots += lp.pivots() - kept.pivots();
    lp = kept;
    lpRow = keptRows;
    inLp = Arrays.copyOf(inLp, rows());
    Arrays.fill(inLp, false);
    for (int i : lpRow) {
      inLp[i] = true;
    }
    inactive = Arrays.copyOf(inactive, lpRow.length);
    if (POOL_CUTS) {
      dormant += k;
      identityRows = false;
      pooledCuts += k;
    }
    cuts -= k;
  }

  // appends the cuts as rows sum w x <= rhs, to the rows and to the simplex; the row arrays are
  // built whole and then swapped in, so a reader of the old arrays never sees a half-filled row
  private void addCuts(List<MirCut> chosen) {
    int m = rows();
    int k = chosen.size();
    int[][] newColumns = Arrays.copyOf(rowColumns, m + k);
    long[][] newWeights = Arrays.copyOf(rowWeights, m + k);
    long[] newHi = Arrays.copyOf(rowHi, m + k);
    boolean[] newHasHi = Arrays.copyOf(hasHi, m + k);
    int[][] cs = new int[k][];
    double[][] ws = new double[k][];
    double[] lo = new double[k];
    double[] hi = new double[k];
    for (int q = 0; q < k; q++) {
      MirCut c = chosen.get(q);
      newColumns[m + q] = c.columns;
      newWeights[m + q] = c.weights;
      newHi[m + q] = c.rhs;
      newHasHi[m + q] = true;
      cs[q] = c.columns;
      ws[q] = new double[c.weights.length];
      for (int t = 0; t < c.columns.length; t++) {
        ws[q][t] = c.weights[t];
      }
      lo[q] = Double.NEGATIVE_INFINITY;
      hi[q] = (double) c.rhs;
    }
    rowLo = Arrays.copyOf(rowLo, m + k);
    hasLo = Arrays.copyOf(hasLo, m + k);
    rowHi = newHi;
    hasHi = newHasHi;
    rowWeights = newWeights;
    rowColumns = newColumns;
    // the cuts go into the simplex at once, as rows its solution breaks
    inLp = Arrays.copyOf(inLp, m + k);
    int l = lpRow.length;
    identityRows &= l == m;
    lpRow = Arrays.copyOf(lpRow, l + k);
    inactive = Arrays.copyOf(inactive, l + k);
    for (int q = 0; q < k; q++) {
      lpRow[l + q] = m + q;
      inLp[m + q] = true;
    }
    lp.addRows(cs, ws, lo, hi);
    cuts += k;
    cutSource = Arrays.copyOf(cutSource, m + k);
    for (int q = 0; q < k; q++) {
      String source = chosen.get(q).source;
      cutSource[m + q] = (calls > 1 && !restarting ? "s-" : "") + (source == null ? "cut" : source);
      if (sources != null) {
        sources.of(cutSource[m + q]).rows++;
      }
    }
  }

  // bounds propagation of sum w x <= c, exact; nothing on overflow
  private void propagate(Store store, LinearForm f, int[] facts, Certificate certificate) {
    IntVar[] vars = f.vars();
    long[] w = f.weights();
    long c = f.c();
    long smallest = 0;
    long[] least = new long[vars.length];
    try {
      for (int k = 0; k < vars.length; k++) {
        least[k] = Math.multiplyExact(w[k], w[k] > 0 ? vars[k].min() : vars[k].max());
        smallest = Math.addExact(smallest, least[k]);
      }
    } catch (ArithmeticException _) {
      return;
    }
    failureForm = f;
    failureFacts = facts;
    failureCertificate = certificate;
    if (smallest > c) {
      failures++;
      throw Store.failException;
    }
    long room;
    try {
      room = Math.subtractExact(c, smallest);
    } catch (ArithmeticException _) {
      return; // the slack is larger than any bound it could tighten
    }
    for (int k = 0; k < vars.length; k++) {
      long wk = w[k];
      // wk * v <= least[k] + room
      long limit;
      try {
        limit = Math.addExact(least[k], room);
      } catch (ArithmeticException _) {
        continue;
      }
      IntVar v = vars[k];
      if (wk > 0) {
        long bound = Math.floorDiv(limit, wk);
        if (bound < v.max()) {
          rec(store, v, f, facts, certificate);
          v.domain.inMax(store.level, v, (int) Math.max(bound, v.min() - 1L));
        }
      } else {
        long bound = Math.ceilDiv(limit, wk);
        if (bound > v.min()) {
          rec(store, v, f, facts, certificate);
          v.domain.inMin(store.level, v, (int) Math.min(bound, v.max() + 1L));
        }
      }
    }
  }

  private void rec(Store store, IntVar v, LinearForm f, int[] facts, Certificate certificate) {
    prunings++;
    deducedVar.add(v);
    deducedForm.add(f);
    deducedFacts.add(facts);
    deducedCertificate.add(certificate);
    deducedLevel.add(store.level);
  }

  @Override
  public void removeLevel(int level) {
    if (tightFrom >= 0 && level <= rootLevel) {
      tightLost = true;
    }
    while (rootBoundsSize > 0 && rootBoundsLevel[rootBoundsSize - 1] >= level) {
      rootBoundsSize--;
    }
    int k = deducedLevel.size();
    while (k > 0 && deducedLevel.get(k - 1) >= level) {
      k--;
    }
    deducedVar.subList(k, deducedVar.size()).clear();
    deducedForm.subList(k, deducedForm.size()).clear();
    deducedFacts.subList(k, deducedFacts.size()).clear();
    deducedCertificate.subList(k, deducedCertificate.size()).clear();
    deducedLevel.subList(k, deducedLevel.size()).clear();
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar v = trail.variable(entry);
    int mark = out.size();
    lastCertificate = null;
    for (int k = deducedVar.size() - 1; k >= 0; k--) {
      if (deducedVar.get(k) == v) {
        if (deducedForm.get(k).explain(trail, entry, out)
            && addFacts(trail, deducedFacts.get(k), entry, out)) {
          lastCertificate = deducedCertificate.get(k);
          return true;
        }
        out.truncate(mark);
      }
    }
    return false;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    lastCertificate = failureCertificate;
    return failureForm != null
        && failureForm.explainFailure(trail, out)
        && addFacts(trail, failureFacts, trail.size(), out);
  }

  private static int[] appended(int[] a, int v) {
    int[] b = Arrays.copyOf(a, a.length + 1);
    b[a.length] = v;
    return b;
  }

  // adds the entries of the facts of a form just before a trail position: x != v, or x = v
  private boolean addFacts(AtomicTrail trail, int[] facts, int position, EntryList out) {
    if (facts == null) {
      return true;
    }
    for (int f : facts) {
      LpColumn c = (LpColumn) x[f >= 0 ? f : ~f];
      if (f >= 0) {
        if (!trail.excludedBefore(c.variable(), c.value(), position, out)) {
          return false;
        }
      } else {
        trail.addLowerBound(c.variable(), position, out);
        trail.addUpperBound(c.variable(), position, out);
      }
    }
    return true;
  }

  @Override
  public LinearForm failureForm() {
    return failureFacts == null ? failureForm : null;
  }

  @Override
  public List<LinearForm> reasonForms(IntVar x) {
    List<LinearForm> localForms = new ArrayList<>();
    for (int k = deducedVar.size() - 1; k >= 0; k--) {
      if (deducedVar.get(k) == x && deducedFacts.get(k) == null) {
        localForms.add(deducedForm.get(k));
      }
    }
    return localForms;
  }

  @Override
  public boolean checksReasons() {
    return true;
  }

  @Override
  public LinearRelaxation copy(VarMap map) {
    // the auxiliary columns are not in the store: the copy gets its own
    Map<IntVar, IntVar> columns = new IdentityHashMap<>();
    List<LinearForm> copies = new ArrayList<>();
    for (LinearForm f : forms) {
      copies.add(new LinearForm(copied(f.vars(), map, columns), f.weights(), f.c(), f.relation()));
    }
    // the capacity cuts are rows of the copy: the prunings made with them stay explained by them
    for (LinearForm f : capacityForms) {
      copies.add(new LinearForm(copied(f.vars(), map, columns), f.weights(), f.c(), f.relation()));
    }
    List<LinearForm> extraCopies = new ArrayList<>();
    for (LinearForm f : keptExtraForms.isEmpty() ? extraForms : keptExtraForms) {
      extraCopies.add(
          new LinearForm(copied(f.vars(), map, columns), f.weights(), f.c(), f.relation()));
    }
    LinearRelaxation c =
        new LinearRelaxation(
            copies,
            extraCopies,
            objective == null ? null : map.get(objective),
            maximize,
            createdWith);
    c.pivotLimit = pivotLimit;
    c.keepExtra = !keptExtraForms.isEmpty();
    c.keepEncodings = keepEncodings;
    c.extraCarry = extraCarry;
    c.refutation = refutation;
    for (CapacityCuts cc : capacity) {
      c.capacity.add(cc.copy(map));
    }
    for (EnergyCuts e : energy) {
      c.energy.add(e.copy(map));
    }
    for (AlldifferentCuts h : hall) {
      c.hall.add(h.copy(map));
    }
    for (TreeCuts t : trees) {
      c.trees.add(t.copy(map));
    }
    return c;
  }

  private static IntVar[] copied(IntVar[] vars, VarMap map, Map<IntVar, IntVar> columns) {
    IntVar[] result = new IntVar[vars.length];
    for (int k = 0; k < vars.length; k++) {
      IntVar v = vars[k];
      if (v instanceof LpColumn c) {
        result[k] =
            columns.computeIfAbsent(v, u -> c.isFree() ? c.copy() : c.copy(map.get(c.variable())));
      } else {
        result[k] = map.get(v);
      }
    }
    return result;
  }

  @Override
  public String toString() {
    return id() + " : LinearRelaxation(" + x.length + " columns, " + rows() + " rows)";
  }
}
