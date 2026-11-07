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
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.Linearizations;
import org.jacop.constraints.Routes;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.constraints.cumulative.CumulativeUnaryOptional;
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
  private static final boolean CLEAN = !"false".equals(System.getProperty("org.jacop.lp.clean"));

  // multipliers below this share of the largest are taken as round-off of the simplex
  private static final double NOISE = 1e-11;

  // the scales tried for the multipliers, the largest first
  private static final long[] SCALES = {1L << 40, 1L << 32, 1L << 24, 1L << 16, 1L << 8, 1};

  // the scale of the rows of the basis inverse the Gomory cuts come from
  private static final long GOMORY_SCALE = 1L << 20;

  private final IntVar[] x;
  // whether each column is an auxiliary column of the relaxation ({@link LpColumn}), not a
  // variable of the store, and whether there is any
  private final boolean[] lpOnly;
  private final boolean anyLpOnly;
  // whether the relaxation holds the all-different-except encodings over auxiliary columns, which
  // are the relaxation itself and are never dropped (the other encodings are extra rows like any)
  private boolean keepEncodings;
  // the extra rows before the value encodings of valueRows' tried rows, which come last; the others
  // are tried without them when all of them are not kept
  private int plainExtra = Integer.MAX_VALUE;
  // the extra rows before the flow models of layered graphs, which come after the other tried
  // value encodings; the rows before them are tried without them when all are not kept, and are
  // kept instead of all when they give the same bound
  private int triedExtra = Integer.MAX_VALUE;
  // the rows, the cuts last
  private int[][] rowColumns;
  private long[][] rowWeights;
  private long[] rowLo;
  private long[] rowHi;
  private boolean[] hasLo;
  private boolean[] hasHi;
  private final IntVar objective;
  private LpSolver lp;
  private final Simplex simplex;

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

  // the row pool: whether the rows of other constraints and the cuts leave the simplex after
  // POOL_AGE optimal solves in which they are inactive (with lazy rows every row does, after
  // LAZY_AGE); and whether the rows of other constraints that the root trial does not keep, and
  // the cuts of a round that does not move the bound, stay in the pool instead of being dropped.
  // Both are off: such rows come back at the first solves in search, as its solution breaks them,
  // which undoes the root's choice to leave them out, and neither moved a result on the wide set
  private static final boolean POOL = !"false".equals(System.getProperty("org.jacop.lp.pool"));
  private static final int POOL_AGE = Integer.getInteger("org.jacop.lp.poolAge", 100);
  private static final boolean POOL_EXTRA = Boolean.getBoolean("org.jacop.lp.poolExtra");
  private static final boolean POOL_CUTS = Boolean.getBoolean("org.jacop.lp.poolCuts");
  private static final long WORK = Long.getLong("org.jacop.lp.work", 20_000_000L);
  private static final long ROOT_WORK = Long.getLong("org.jacop.lp.rootWork", 1_000_000_000L);

  // the most pivots of the first solve, which has the root budget instead of the pivot limit: a
  // root LP that stops at the limit gives neither a bound nor cuts
  private static final int ROOT_PIVOTS = Integer.getInteger("org.jacop.lp.rootPivots", 20_000);

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

  /** Statistics: failures proved by an exact combination. */
  public long failures;

  /** Statistics: bounds tightened. */
  public long prunings;

  /** Statistics: propagations stopped at the pivot limit. */
  public long limits;

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

  /** Statistics: the auxiliary columns ({@link LpColumn}) of the relaxation. */
  public int valueColumns;

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
      !"false".equals(System.getProperty("org.jacop.lp.keepBases"));
  private static final int BASIS_JUMP = Integer.getInteger("org.jacop.lp.basisJump", 2);
  private static final int MAX_BASES = Integer.getInteger("org.jacop.lp.maxBases", 32);
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
      !"false".equals(System.getProperty("org.jacop.lp.linearize"));

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
  private static final int EXTRA_LIMITS = 3;
  // the call at which the extra rows were added
  private long extraCall;

  // whether the sparse simplex was chosen by the size of the relaxation in place of the dense one
  private boolean bySize;

  // MIR cuts at the root: rounds, cuts per round, and the share of the rows they may add
  private static final boolean CUTS_ENABLED =
      !"false".equals(System.getProperty("org.jacop.lp.cuts"));
  private static final int CUT_ROUNDS = Integer.getInteger("org.jacop.lp.cutRounds", 5);
  private static final int CUTS_PER_ROUND = Integer.getInteger("org.jacop.lp.cutsPerRound", 50);
  private static final int MAX_SOURCES = 100;
  private static final double MAX_PARALLELISM = 0.9;

  // rounded capacity cuts of the Routes constraints at the root, before the MIR cuts: rounds and
  // the share of the rows they may add; the rounds stop when no cut is violated or the bound
  // stalls, and the cuts are dropped when they do not move the bound
  private static final boolean CAPACITY_CUTS =
      !"false".equals(System.getProperty("org.jacop.lp.capacityCuts"));
  private static final int CAPACITY_ROUNDS = Integer.getInteger("org.jacop.lp.capacityRounds", 50);
  private static final int CAPACITY_STALL = 3;

  // the separations of the capacity cuts, one for each Routes with its arcs among the columns
  private List<CapacityCuts> capacity = new ArrayList<>();

  // energy cuts of the cumulative resources at the root, in the rounds of the capacity cuts
  private static final boolean ENERGY_CUTS =
      !"false".equals(System.getProperty("org.jacop.lp.energyCuts"));

  // the separations of the energy cuts, one for each cumulative resource
  private List<EnergyCuts> energy = new ArrayList<>();

  /** Statistics: energy cuts of cumulative resources added. */
  public long energyCuts;

  // the capacity cuts kept, as rows: they follow from the Routes, not from the rows, so a copy
  // takes them as rows of its own
  private List<LinearForm> capacityForms = new ArrayList<>();

  /** Statistics: rounded capacity cuts added. */
  public long capacityCuts;

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
      !"false".equals(System.getProperty("org.jacop.lp.restartCuts"));
  private int rootLevel = -1;
  private long rootObjective;
  private boolean restarting;
  private long[] rootLo;
  private long[] rootHi;

  /** Statistics: solves at the root level after the bound of the objective improved. */
  public long restartSolves;

  // root reduced-cost fixing (SCIP's prop_rootredcost): the inequalities of the duals of the last
  // optimal solve at the root level are combinations of the rows, so they hold in the whole search;
  // propagated again at the root level whenever the bound of the objective has improved, they fix
  // the columns whose reduced cost no longer fits in the gap. Only there: propagated at every call
  // they cost more than they prune (bus_scheduling, osolpro #169)
  private static final boolean ROOT_REDUCED_COSTS =
      !"false".equals(System.getProperty("org.jacop.lp.rootReducedCosts"));
  private LinearForm[] rootForms = new LinearForm[0];
  // the certificate of each root form, for a proof, or null
  private Certificate[] rootCertificates = new Certificate[0];
  // the LP-only column facts of each root form, for its explanation
  private int[][] rootFacts = new int[0][];
  private long[] solvedLo;
  private long[] solvedHi;

  // the simplex at the optimum of the last solve at the root level, with as many rows as it had
  // then: a solve at a restart starts from its basis instead of the one search left, which is far
  // from the root (table-layout: a restart solve took as long as the first one)
  private static final boolean RESTART_FROM_ROOT =
      !"false".equals(System.getProperty("org.jacop.lp.restartFromRoot"));
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
   * @param forms the rows; forms with relation {@code !=} are left out
   * @param objective the variable to minimize, or null for satisfaction
   * @param maximize whether the objective is maximized instead
   */
  public LinearRelaxation(Collection<LinearForm> forms, IntVar objective, boolean maximize) {
    this(forms, objective, maximize, Simplex.DENSE);
  }

  /**
   * Creates the relaxation of linear forms, solved by the given simplex.
   *
   * @param forms the rows; forms with relation {@code !=} are left out
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
   * @param forms the rows; forms with relation {@code !=} are left out
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
        } catch (ArithmeticException e) {
          overflow = true;
        }
      }
      if (index < given) {
        baseColumns = columns.size();
      }
      merged.values().removeIf(w -> w == 0);
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
      valueColumns += lpOnly[j] ? 1 : 0;
    }
    anyLpOnly = valueColumns > 0;
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
    Set<Constraint> constraints = constraintsOf(store);
    List<LinearForm> forms = new ArrayList<>();
    List<LinearForm> relaxed = new ArrayList<>();
    List<CapacityCuts> separations = new ArrayList<>();
    List<EnergyCuts> resources = new ArrayList<>();
    for (Constraint c : constraints) {
      if (CAPACITY_CUTS && c instanceof Routes routes) {
        separations.add(new CapacityCuts(routes));
      }
      if (ENERGY_CUTS && objective != null) {
        EnergyCuts e = energyCuts(c);
        if (e != null) {
          resources.add(e);
        }
      }
      LinearForm f = LinearForms.of(c);
      if (f != null && f.relation() != LinearForm.NE && f.vars().length > 1) {
        forms.add(f);
      } else if (f == null && LINEARIZE) {
        relaxed.addAll(Linearizations.of(c));
      }
    }
    // like the linearized rows, they are kept only when they help the root relaxation: the
    // clauses of lazy clause generation make thousands of rows on some models (rel2onto: 65 rows
    // become 1,135), and a relaxation that large stalls at its pivot limit and prunes nothing
    for (LinearForm f : extra) {
      if (f != null) {
        relaxed.add(f);
      }
    }
    int pairCliques = 0;
    // for an objective only, whose bound they raise: on satisfaction models (rubik) the longer
    // rows only make each call dearer
    if (PAIR_CLIQUES && objective != null) {
      PairCliques merged = PairCliques.merge(forms, relaxed);
      forms = merged.rows;
      relaxed = merged.further;
      pairCliques = merged.cliques;
    }
    if (!substituted.isEmpty()) {
      forms = substitute(forms, substituted, objective);
    }
    if (LINEARIZE) {
      relaxed.addAll(Linearizations.encodings(constraints));
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
    for (List<LinearForm> rows : List.of(relaxed, valueRows.tried(), valueRows.flow())) {
      for (LinearForm f : rows) {
        if (f.relation() != LinearForm.NE
            && f.vars().length >= 2
            && Arrays.stream(f.vars()).noneMatch(substituted::contains)) {
          candidates.add(f);
        }
      }
    }
    Set<LinearForm> tried = Collections.newSetFromMap(new IdentityHashMap<>());
    tried.addAll(valueRows.tried());
    tried.addAll(valueRows.flow());
    Set<LinearForm> flow = Collections.newSetFromMap(new IdentityHashMap<>());
    flow.addAll(valueRows.flow());
    boolean auto = simplex == Simplex.DENSE && SPARSE_ROWS >= 0;
    if (auto && !sparseTakes(forms)) {
      // too large for the sparse simplex as it is: the dense one, or no relaxation over its cap
      auto = false;
    }
    if (auto && (forms.size() >= SPARSE_ROWS || tooLarge(forms, Simplex.DENSE))) {
      // the dense tableau costs rows times columns per pivot, the sparse simplex its nonzeros: the
      // dense one is kept for small relaxations, where it is as fast, and the sparse one takes the
      // larger ones, also those over the dense size cap, which would get no relaxation at all
      simplex = Simplex.SPARSE;
    }
    if (auto && simplex == Simplex.DENSE && exempt > 0) {
      List<LinearForm> withColumns = new ArrayList<>(forms);
      withColumns.addAll(candidates.subList(0, exempt));
      if (forms.size() + exempt >= SPARSE_ROWS || tooLarge(withColumns, Simplex.DENSE)) {
        // the encodings are rows of the model as a MIP states it: the simplex is chosen by their
        // count too, and the sparse one takes them all when the dense tableau cannot
        simplex = Simplex.SPARSE;
      }
    }
    if (tooLarge(forms, simplex)) {
      return null;
    }
    List<LinearForm> further = new ArrayList<>();
    // the further rows are tried at the first solve over every column; on the sparse simplex
    // chosen by size at most twice the given rows and org.jacop.lp.sparseRows more, so that the
    // trial stays in proportion to the relaxation (a trial over every candidate of a large model
    // can take a minute and then drop them all)
    if (!fitsSimplex(forms, candidates, simplex, auto, exempt, further) && objective != null) {
      // not all fit: after the value encodings, the rows nearest to the objective first, since rows
      // far from it rarely move its bound (tiny-cvrp: 852 of 6,936 rows, those over the variables
      // of the rows of the objective, give the whole bound, and in model order they came too late
      // to fit); the tried value encodings stay after the other rows, since the retry without them
      // takes the rows before them
      further.clear();
      List<LinearForm> sorted = fitOrder(forms, candidates, exempt, tried, flow, objective);
      fitsSimplex(forms, sorted, simplex, auto, exempt, further);
    }
    LinearRelaxation r = new LinearRelaxation(forms, further, objective, maximize, simplex);
    r.bySize = auto && simplex == Simplex.SPARSE;
    r.keepEncodings = exempt > 0;
    r.plainExtra = (int) r.extraForms.stream().filter(f -> !tried.contains(f)).count();
    r.triedExtra = (int) r.extraForms.stream().filter(f -> !flow.contains(f)).count();
    r.pairCliques = pairCliques;
    r.capacity = separations;
    r.energy = resources;
    return r.rows() + r.extraColumns.length < 2 ? null : r;
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
    List<LinearForm> forms = new ArrayList<>();
    Map<LinearForm, Constraint> source = new IdentityHashMap<>();
    for (Constraint c : constraintsOf(store)) {
      LinearForm f = LinearForms.ofModelLine(c);
      if (f != null && f.relation() != LinearForm.NE && f.vars().length > 1) {
        forms.add(f);
        source.put(f, c);
      }
    }
    if (simplex == Simplex.DENSE
        && SPARSE_ROWS >= 0
        && sparseTakes(forms)
        && (forms.size() >= SPARSE_ROWS || tooLarge(forms, Simplex.DENSE))) {
      simplex = Simplex.SPARSE;
    }
    if (tooLarge(forms, simplex)) {
      return null;
    }
    LinearRelaxation r = new LinearRelaxation(forms, List.of(), objective, maximize, simplex);
    r.rowSource = new Constraint[r.forms.size()];
    for (int i = 0; i < r.rowSource.length; i++) {
      r.rowSource[i] = source.get(r.forms.get(i));
    }
    r.cutsTried = true;
    return r.rows() < 2 ? null : r;
  }

  // the constraints of the variables in the store and of the named ones, such as Boolean
  // variables, which have no store index
  private static Set<Constraint> constraintsOf(Store store) {
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

  /**
   * Returns the candidates ordered by their distance from the objective (stable): a row over the
   * objective has distance 0, a row over a variable of a row at distance d has distance d + 1,
   * through the given rows and the candidates; rows not connected to the objective come last.
   */
  static List<LinearForm> byDistance(
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
    Integer[] order = new Integer[candidates.size()];
    for (int i = 0; i < order.length; i++) {
      order[i] = i;
    }
    int offset = forms.size();
    Arrays.sort(order, Comparator.comparingInt(i -> distance[offset + i]));
    List<LinearForm> sorted = new ArrayList<>(order.length);
    for (int i : order) {
      sorted.add(candidates.get(i));
    }
    return sorted;
  }

  // the dense simplex is chosen for relaxations below this many rows, the sparse one from it on,
  // when the dense one is asked for; -1 keeps the dense one whatever the size
  private static final int SPARSE_ROWS = Integer.getInteger("org.jacop.lp.sparseRows", 100);

  // the conflicts of pairs of 0/1 literals merged into clique rows
  private static final boolean PAIR_CLIQUES =
      !"false".equals(System.getProperty("org.jacop.lp.pairCliques"));

  // the largest relaxation, in rows and in columns, that the sparse simplex is chosen for by size:
  // beyond them its root solve and its ratio test take more than the time limit of a run (nside
  // EASY_200_50, 57,505 rows: 52 ms a pivot; rcpsp-wet-diverse j60_19_6, 140,925 columns), and the
  // largest that helped in the Challenge has 19,141 rows (table-layout) and 23,242 columns
  // (physician-scheduling)
  private static final int SPARSE_MAX_ROWS =
      Integer.getInteger("org.jacop.lp.sparseMaxRows", 25_000);
  private static final int SPARSE_MAX_COLUMNS =
      Integer.getInteger("org.jacop.lp.sparseMaxColumns", 30_000);

  private static boolean sparseTakes(List<LinearForm> forms) {
    if (forms.size() > SPARSE_MAX_ROWS) {
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
      int exempt,
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
    for (LinearForm f : candidates) {
      int added = 0;
      for (IntVar v : f.vars()) {
        added += vars.contains(v) ? 0 : 1;
      }
      if (simplex == Simplex.DENSE
          ? (rows + 1) * (rows + 1 + vars.size() + added + 1) > MAX_TABLEAU
          : nonzeros + f.vars().length > MAX_NONZEROS
              || denseCap
                  && (further.size() >= 2L * forms.size() + SPARSE_ROWS + exempt
                      || vars.size() + added > SPARSE_MAX_COLUMNS)) {
        return false;
      }
      further.add(f);
      vars.addAll(Arrays.asList(f.vars()));
      rows++;
      nonzeros += f.vars().length;
    }
    return true;
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
    } catch (ArithmeticException overflow) {
      return forms;
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

  @Override
  public void consistency(Store store) {
    // the simplex may skip a node, round its multipliers to nothing, or fix the last variables by
    // its own pruning without being run again; an assignment that breaks a row must still fail
    checkGround();
    if (suspended) {
      return;
    }
    if (rootLevel < 0) {
      rootLevel = store.level;
      rootObjective = objectiveBound();
    } else if (store.level <= rootLevel && objectiveBound() != rootObjective) {
      rootObjective = objectiveBound();
      if (ROOT_REDUCED_COSTS) {
        long pruned = prunings;
        for (int k = 0; k < rootForms.length; k++) {
          propagate(store, rootForms[k], rootFacts[k], rootCertificates[k]);
        }
        rootPrunings += prunings - pruned;
      }
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
    long started = System.nanoTime();
    try {
      solveAndPropagate(store);
      if (first) {
        rememberRootBounds();
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
      if (failures > failed) {
        idle = 0;
        period = Math.max(1, period / 2);
        credit = WORK;
      } else if (prunings > pruned) {
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

  // whether the bounds of a column other than the objective are tighter than at the last solve at
  // the root level: with only the bound of the objective changed, a solve again finds the same
  // optimum (or its infeasibility, which the root reduced costs already prove) and the same cuts
  // (physician-scheduling: 40 to 50 restart solves, up to 20 s, no pruning)
  private boolean rootBoundsChanged() {
    if (solvedLo == null) {
      return true;
    }
    for (int j = objective == null ? 0 : 1; j < x.length; j++) {
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
    for (int i = 0; i < rows(); i++) {
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
      } catch (ArithmeticException overflow) {
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
    calls++;
    boolean jump = calls > 1 && lastSolveLevel - store.level >= BASIS_JUMP;
    long pivotsBefore = lp.pivots();
    if (KEEP_BASES) {
      restoreBasis(store.level, jump);
    }
    sendBounds();
    long size = Math.max(1, lp.pivotWork());
    if (beforeExtra != null && bySize && !keepEncodings) {
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
            ? (int) Math.clamp(ROOT_WORK / size, 5, ROOT_PIVOTS)
            : (int) Math.clamp(WORK / size, 5, pivotLimit);
    int status =
        (calls == 1 || restarting) && simplex != Simplex.LAZY
            ? rootSolve(lp, limit, rootWork())
            : solvePool(limit);
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
    lastSolveLevel = store.level;
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
      if (beforeExtra != null
          && !keepEncodings
          && extraHits >= EXTRA_LIMITS
          && extraHits * 20 > calls
          && calls >= 20L * EXTRA_LIMITS) {
        dropExtraRows();
      }
      return;
    }
    stalled = 0;
    if (keepSolutions && status == LpSolver.OPTIMAL) {
      int n = lp.columns();
      if (solution.length != n) {
        solution = new double[n];
      }
      for (int j = 0; j < n; j++) {
        solution[j] = lp.value(j);
      }
      solutionLevel = store.level;
      if (store.level <= rootSolutionLevel) {
        rootSolution = solution.clone();
        rootSolutionLevel = store.level;
      }
    }
    double[] y;
    if (status == DualSimplex.INFEASIBLE) {
      infeasible++;
      y = byRow(lp.farkas());
    } else if (objective != null) {
      if (Double.isNaN(rootBound)) {
        rootBound = lp.value(0);
      }
      y = byRow(lp.duals());
    } else {
      return;
    }
    for (int s = 0; s < SCALES.length; s++) {
      long[] lambda = scaled(y, SCALES[s]);
      if (lambda == null) {
        return;
      }
      int[][] facts = new int[2][];
      long[][] used = new long[2][];
      LinearForm[] forms = certificate(lambda, facts, used);
      if (forms == null) {
        continue; // the combination overflows: try a smaller scale
      }
      if (status == LpSolver.OPTIMAL && (calls == 1 || restarting)) {
        List<LinearForm> kept = new ArrayList<>();
        List<Certificate> keptCertificates = new ArrayList<>();
        List<int[]> keptFacts = new ArrayList<>();
        for (int k = 0; k < forms.length; k++) {
          if (forms[k] != null) {
            kept.add(forms[k]);
            keptCertificates.add(certified(forms[k], used[k], k == 0));
            keptFacts.add(facts[k]);
          }
        }
        rootForms = kept.toArray(new LinearForm[0]);
        rootCertificates = keptCertificates.toArray(new Certificate[0]);
        rootFacts = keptFacts.toArray(new int[0][]);
        if (restartSolvesOn && RESTART_FROM_ROOT && simplex != Simplex.LAZY && objective != null) {
          rootSimplex = lp.copy();
          rootSimplexRows = rows();
          rootSimplexLpRows = lpRow.clone();
        }
      }
      boolean fits = true;
      for (LinearForm f : forms) {
        fits &= f == null || fits(f);
      }
      if (fits || s == SCALES.length - 1) {
        for (int k = 0; k < forms.length; k++) {
          if (forms[k] != null) {
            propagate(store, forms[k], facts[k], certified(forms[k], used[k], k == 0));
          }
        }
        if (status != LpSolver.INFEASIBLE) {
          return;
        }
        // the rounded Farkas multipliers did not prove the infeasibility: try a smaller scale
      }
      // the bounds reasoning on the form would overflow: try a smaller scale
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
    LinearForm[] forms = combine(g);
    facts[0] = combineFacts[0];
    facts[1] = combineFacts[1];
    if (!CLEAN || forms.length == 0) {
      return forms;
    }
    if (!g.hasUpper()) {
      used[0] = sided(lambda, true);
      Aggregate u = aggregate(used[0]);
      if (u == null) {
        return null;
      }
      LinearForm[] c = combine(u);
      forms[0] = c.length > 0 ? c[0] : null;
      facts[0] = combineFacts[0];
    }
    if (!g.hasLower()) {
      used[1] = sided(lambda, false);
      Aggregate l = aggregate(used[1]);
      if (l == null) {
        return null;
      }
      LinearForm[] c = combine(l);
      forms[1] = c.length > 1 ? c[1] : null;
      facts[1] = combineFacts[1];
    }
    for (int k = 0; k < forms.length && rowSource == null; k++) {
      forms[k] = forms[k] == null ? null : divided(forms[k]);
    }
    return forms;
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

  private long rootWork() {
    return objective == null ? ROOT_WORK : SPARSE_ROOT_WORK;
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
    } catch (ArithmeticException overflow) {
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
        if (lpOnly[j]) {
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
    } catch (ArithmeticException overflow) {
      return new LinearForm[0];
    }
    combineFacts[0] = upperFacts.length == 0 ? null : upperFacts;
    combineFacts[1] = lowerFacts.length == 0 ? null : lowerFacts;
    IntVar[] vars = new IntVar[size];
    long[] w = new long[size];
    long[] neg = new long[size];
    for (int k = 0, m = 0; k < columns.length; k++) {
      int j = columns[k];
      if (coef[k] != 0 && !lpOnly[j]) {
        vars[m] = x[j];
        w[m] = coef[k];
        neg[m++] = -coef[k];
      }
    }
    return new LinearForm[] {
      g.hasUpper() ? new LinearForm(vars, w, upper, LinearForm.LE) : null,
      g.hasLower() ? new LinearForm(vars, neg, -lower, LinearForm.LE) : null
    };
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
      // the capacity and energy cuts are made once, at the first solve
      if (!capacity.isEmpty() || !energy.isEmpty()) {
        int status = capacityRounds();
        if (status != DualSimplex.OPTIMAL) {
          return status;
        }
      }
    }
    // the bounds of the first solve, which hold everywhere, also for the cuts made at restarts
    long[] lo = Arrays.copyOf(rootLo, n);
    long[] hi = Arrays.copyOf(rootHi, n);
    int original = rows();
    // the rows themselves, sorted once: each round then costs their length, not rows x columns
    Aggregate[] unitRows = new Aggregate[original];
    for (int i = 0; i < original; i++) {
      unitRows[i] = rowAggregate(i);
    }
    Set<List<Long>> seen = new HashSet<>();
    int status = DualSimplex.OPTIMAL;
    for (int round = 0; round < CUT_ROUNDS; round++) {
      List<MirCut> chosen = separateCuts(lo, hi, unitRows, seen);
      if (chosen.isEmpty()) {
        break;
      }
      LpSolver kept = lp.copy();
      int[] keptRows = lpRow;
      long pivots = lp.pivots();
      double before = lp.value(0);
      addCuts(chosen);
      long size = Math.max(1, lp.pivotWork());
      status =
          rootSolve(
              lp,
              Math.clamp(ROOT_WORK / CUT_ROUNDS / size, 5, ROOT_PIVOTS),
              rootWork() / CUT_ROUNDS);
      if (status == DualSimplex.OPTIMAL
          && Math.abs(lp.value(0) - before) <= 1e-6 * (1 + Math.abs(before))) {
        // cuts that do not move the bound only make each solve dearer: back to the LP before them
        dropCuts(chosen.size(), kept, keptRows);
        break;
      }
      if (status != DualSimplex.OPTIMAL) {
        if (status == DualSimplex.LIMIT) {
          dropCuts(chosen.size(), kept, keptRows);
          status = DualSimplex.OPTIMAL;
        }
        break;
      }
    }
    if (status == DualSimplex.OPTIMAL && !restarting) {
      cutBound = lp.value(0);
    }
    return status;
  }

  private static final boolean SLACK_GOMORY =
      !"false".equals(System.getProperty("org.jacop.lp.slackGomory"));

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
   * MirCut#reduce}).
   */
  private void slackGomory(
      long[] lambda, double[] value, long[] lo, long[] hi, List<MirCut> found) {
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
          return;
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
        long[] g = MirCut.raw(columns, w, 0, xv, xlo, xhi);
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
    } catch (ArithmeticException overflow) {
      // no cut from this row
    }
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
    int[][] energyColumns = new int[energy.size()][];
    for (int k = 0; k < energy.size(); k++) {
      IntVar[] starts = energy.get(k).starts();
      energyColumns[k] = new int[starts.length];
      for (int a = 0; a < starts.length; a++) {
        Integer j = columnOf.get(starts[a]);
        energyColumns[k][a] = j == null ? -1 : j;
      }
    }
    for (int round = 0; round < CAPACITY_ROUNDS && stall < CAPACITY_STALL; round++) {
      List<MirCut> chosen = new ArrayList<>();
      int n = lp.columns();
      for (CapacityCuts cc : capacity) {
        IntVar[] literals = cc.literals();
        int[] column = new int[literals.length];
        double[] value = new double[literals.length];
        for (int a = 0; a < literals.length; a++) {
          Integer j = columnOf.get(literals[a]);
          column[a] = j == null ? -1 : j;
          value[a] = j == null ? literals[a].min() : lp.value(j);
        }
        for (CapacityCuts.Cut cut : cc.separate(value, CUTS_PER_ROUND)) {
          MirCut row = row(cut, column);
          long m = (long) lp.rows() + chosen.size() + 1;
          if (chosen.size() >= CUTS_PER_ROUND
              || simplex == Simplex.DENSE && m * (m + n) > MAX_TABLEAU) {
            break;
          }
          if (row != null && seen.add(key(row))) {
            chosen.add(row);
          }
        }
      }
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
      status =
          rootSolve(
              lp,
              Math.clamp(ROOT_WORK / CUT_ROUNDS / size, 5, ROOT_PIVOTS),
              rootWork() / CUT_ROUNDS);
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
    for (int i = firstCount; i < firstCount + added; i++) {
      IntVar[] vars = new IntVar[rowColumns[i].length];
      for (int k = 0; k < vars.length; k++) {
        vars[k] = x[rowColumns[i][k]];
      }
      capacityForms.add(new LinearForm(vars, rowWeights[i].clone(), rowHi[i], LinearForm.LE));
    }
    if (status == DualSimplex.OPTIMAL) {
      capacityBound = lp.value(0);
    }
    return status;
  }

  // the cut as a row sum w x <= rhs over the columns, or null when an arc is not a column
  private static MirCut row(CapacityCuts.Cut cut, int[] column) {
    Map<Integer, Long> weights = new java.util.TreeMap<>();
    long sign = cut.entering() ? -1 : 1;
    for (int a : cut.arcs()) {
      if (column[a] < 0) {
        return null;
      }
      weights.merge(column[a], sign, Long::sum);
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
   * @return the cuts chosen, most efficacious first
   */
  private List<MirCut> separateCuts(
      long[] lo, long[] hi, Aggregate[] unitRows, Set<List<Long>> seen) {
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
      long[] lambda = scaled(byRow(lp.inverseRow(lp.basicRow(j))), GOMORY_SCALE);
      if (lambda != null) {
        if (slackGomory) {
          slackGomory(lambda, value, lo, hi, found);
        }
        mir(aggregate(lambda), value, lo, hi, found);
      }
    }
    for (Aggregate row : unitRows) {
      mir(row, value, lo, hi, found);
    }
    found.sort(Comparator.comparingDouble((MirCut c) -> -c.efficacy));
    List<MirCut> chosen = new ArrayList<>();
    for (MirCut c : found) {
      long m = (long) lp.rows() + chosen.size() + 1;
      if (chosen.size() >= CUTS_PER_ROUND
          || simplex == Simplex.DENSE && m * (m + n) > MAX_TABLEAU) {
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
      }
    }
    return chosen;
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
    int[] prefixes = IntStream.of(k, tiered, plain).filter(q -> q > 0).distinct().toArray();
    LpSolver full = null;
    int kept = 0;
    int keptStatus = status;
    int last = k;
    for (int p : prefixes) {
      if (full != null && p < tiered) {
        break;
      }
      LpSolver trial = trialRows(status, before, m, p, columnsOf(p), p == plain);
      last = p;
      if (trial == null) {
        if (full != null) {
          // the shorter prefix does not help: the longer one kept stays
          break;
        }
        continue;
      }
      if (full != null && !sameBound(full, keptStatus, trial, trialStatus)) {
        // the longer prefix does better
        droppedPivots += trial.pivots();
        break;
      }
      if (full != null) {
        droppedPivots += full.pivots();
      }
      full = trial;
      kept = p;
      keptStatus = trialStatus;
    }
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
      droppedPivots += lp.pivots();
      lp = full;
      allRowsInSimplex(m + k);
      return keptStatus;
    }
    // the rows of the last trial are the m + last rows
    poolExtraRows(m, last);
    return status;
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

  /**
   * Solves the given rows and the first k extra rows over the first n columns at the root, and
   * returns that simplex when the rows are kept, null otherwise (the rows are then m + k, to be
   * truncated by the caller). With few, at most SMALL_EXTRA rows are kept even when the bound
   * stays.
   */
  private LpSolver trialRows(int status, double before, int m, int k, int n, boolean few) {
    setExtraRows(m, k);
    double[] lo = new double[m + k];
    double[] hi = new double[m + k];
    for (int i = 0; i < m + k; i++) {
      lo[i] = hasLo[i] ? (double) rowLo[i] : Double.NEGATIVE_INFINITY;
      hi[i] = hasHi[i] ? (double) rowHi[i] : Double.POSITIVE_INFINITY;
    }
    double[] cost = new double[n];
    if (objective != null) {
      cost[0] = maximize ? -1 : 1;
    }
    LpSolver full;
    if (simplex == Simplex.DENSE) {
      double[][] a = new double[m + k][n];
      for (int i = 0; i < m + k; i++) {
        for (int t = 0; t < rowColumns[i].length; t++) {
          a[i][rowColumns[i][t]] = (double) rowWeights[i][t];
        }
      }
      full = new DualSimplex(a, lo, hi, cost);
    } else {
      full = sparse(sparseRows(m + k), doubles(m + k), lo, hi, cost);
    }
    for (int j = 0; j < n; j++) {
      setBounds(full, j);
    }
    long size = Math.max(1, full.pivotWork());
    int withExtra = rootSolve(full, Math.clamp(ROOT_WORK / size, 5, ROOT_PIVOTS), rootWork());
    boolean keep;
    if (withExtra == DualSimplex.INFEASIBLE) {
      keep = true;
    } else if (withExtra == DualSimplex.LIMIT) {
      keep = false;
    } else {
      boolean raised =
          status != DualSimplex.OPTIMAL
              || !Double.isNaN(before)
                  && Math.abs(full.value(0) - before) > 1e-6 * (1 + Math.abs(before));
      keep = raised || few && k <= SMALL_EXTRA;
    }
    keep |= keepExtra;
    if (keep) {
      trialStatus = withExtra;
      return full;
    }
    droppedPivots += full.pivots();
    return null;
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

  // the rows of the other constraints make too many solves in search stop at the pivot limit: back
  // to the simplex without them (and without the cuts, which may use them)
  private void dropExtraRows() {
    droppedPivots += lp.pivots() - beforeExtra.pivots();
    lp = beforeExtra;
    truncateRows(baseRows);
    allRowsInSimplex(baseRows);
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

  // keeps the first m rows
  private void truncateRows(int m) {
    returns = Arrays.copyOf(returns, Math.min(returns.length, m));
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
    } catch (ArithmeticException overflow) {
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
    } catch (ArithmeticException overflow) {
      return; // the slack is larger than any bound it could tighten
    }
    for (int k = 0; k < vars.length; k++) {
      long wk = w[k];
      // wk * v <= least[k] + room
      long limit;
      try {
        limit = Math.addExact(least[k], room);
      } catch (ArithmeticException overflow) {
        continue;
      }
      IntVar v = vars[k];
      if (wk > 0) {
        long bound = Math.floorDiv(limit, wk);
        if (bound < v.max()) {
          record(store, v, f, facts, certificate);
          v.domain.inMax(store.level, v, (int) Math.max(bound, v.min() - 1L));
        }
      } else {
        long bound = Math.ceilDiv(limit, wk);
        if (bound > v.min()) {
          record(store, v, f, facts, certificate);
          v.domain.inMin(store.level, v, (int) Math.min(bound, v.max() + 1L));
        }
      }
    }
  }

  private void record(Store store, IntVar v, LinearForm f, int[] facts, Certificate certificate) {
    prunings++;
    deducedVar.add(v);
    deducedForm.add(f);
    deducedFacts.add(facts);
    deducedCertificate.add(certificate);
    deducedLevel.add(store.level);
  }

  @Override
  public void removeLevel(int level) {
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
    List<LinearForm> forms = new ArrayList<>();
    for (int k = deducedVar.size() - 1; k >= 0; k--) {
      if (deducedVar.get(k) == x && deducedFacts.get(k) == null) {
        forms.add(deducedForm.get(k));
      }
    }
    return forms;
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
            copies, extraCopies, objective == null ? null : map.get(objective), maximize, simplex);
    c.pivotLimit = pivotLimit;
    c.keepExtra = !keptExtraForms.isEmpty();
    c.keepEncodings = keepEncodings;
    for (CapacityCuts cc : capacity) {
      c.capacity.add(cc.copy(map));
    }
    for (EnergyCuts e : energy) {
      c.energy.add(e.copy(map));
    }
    return c;
  }

  private static IntVar[] copied(IntVar[] vars, VarMap map, Map<IntVar, IntVar> columns) {
    IntVar[] result = new IntVar[vars.length];
    for (int k = 0; k < vars.length; k++) {
      IntVar v = vars[k];
      result[k] =
          v instanceof LpColumn c
              ? columns.computeIfAbsent(v, u -> c.copy(map.get(c.variable())))
              : map.get(v);
    }
    return result;
  }

  @Override
  public String toString() {
    return id() + " : LinearRelaxation(" + x.length + " columns, " + rows() + " rows)";
  }
}
