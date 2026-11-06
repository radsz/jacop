/*
 * RevisedDualSimplex.java
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

package org.jacop.jalp;

import java.util.Arrays;
import java.util.Random;

/**
 * The revised dual simplex of JaLP over the problem {@code min c x} subject to {@code lo_i <= a_i x
 * <= hi_i} and {@code lo_j <= x_j <= hi_j}. The system is {@code [A -I] (x, s) = 0}: the slack of
 * row i is column {@code n + i} with the bounds of the row. It keeps its basis between calls, so a
 * change of bounds or added rows is solved from the last basis (a warm start).
 *
 * <p>Each pivot does one BTRAN for the row of the basis inverse, one pass over the rows it touches
 * for the row of the tableau, one FTRAN for the entering column and one for the dual steepest-edge
 * weights. The leaving row is chosen by dual steepest edge, the entering column by the bound
 * flipping ratio test with Harris tolerances taken in passes over groups of breakpoints.
 *
 * <p>The rows and columns are scaled by powers of two, so scaling is exact and every value this
 * class returns (values, duals, rows of the basis inverse, Farkas rays) is for the problem as
 * given. Infinite bounds are replaced by artificial bounds, enlarged when the answer depends on
 * one. The costs are perturbed against dual degeneracy; with {@link #setExact(boolean)} the
 * perturbation is removed at the end and the problem solved again from the basis found, so the
 * objective is the one of the problem as given.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class RevisedDualSimplex {

  /** The status of an optimal solve. */
  public static final int OPTIMAL = 0;

  /** The status of a solve that proved the problem infeasible. */
  public static final int INFEASIBLE = 1;

  /** The status of a solve that stopped at its limit of pivots. */
  public static final int LIMIT = 2;

  /** The status of a solve whose objective is unbounded, or that needs values beyond 1e14. */
  public static final int UNBOUNDED = 3;

  /** The primal feasibility tolerance, absolute in the scaled problem. */
  public static final double PRIMAL_TOL = 1e-6;

  /** The dual feasibility tolerance. */
  public static final double DUAL_TOL = 1e-9;

  /** The smallest pivot the ratio test accepts. */
  public static final double PIVOT_TOL = 1e-9;

  // the relative size of the cost perturbation (org.jacop.jalp.perturbation): 1e-6 takes dano3mip
  // from 588,569 pivots to 53,405 and the 400 instances of the LP bench from 422 s to 162 s; 1e-7
  // stalls on dano3mip's dual degeneracy
  private static final double PERTURBATION =
      Double.parseDouble(System.getProperty("org.jacop.jalp.perturbation", "1e-6"));

  // refactorizations after this many updates, against the growth and drift of the eta file
  private static final int REFACTOR_UPDATES = 100;

  // the pivot of the row and of the column must agree this closely, or the basis is refactorized
  private static final double PIVOT_AGREEMENT = 1e-7;

  // a proof holds by itself when its range misses zero by this much relative to its size
  private static final double PROOF_MARGIN = 1e-7;
  private static final double PROOF_NOISE = 1e-11;

  // the artificial bounds: the first, the factor they grow by and the largest
  private static final double BIG_START = 1e6;
  private static final double BIG_GROWTH = 100;
  private static final double BIG_MAX = 1e14;

  // the passes of geometric scaling
  private static final int SCALE_PASSES = 4;

  private int m;
  private final int n;
  private int cols;

  // the rows of the scaled A, sparse over the structural columns
  private int[][] rowIdx;
  private double[][] rowVal;

  // the structural columns of the scaled A
  private final int[][] colIdx;
  private final double[][] colVal;
  private final int[] colLen;
  private long nonzeros;

  // the scale of each row and structural column: the scaled problem is R A C
  private double[] rowScale;
  private final double[] colScale;
  private final boolean scaling;

  // the costs (perturbed and as given, both scaled), and the objective as given
  private double[] cost;
  private double[] trueCost;
  private final double[] givenCost;
  private boolean perturbed;
  private final long seed;
  private boolean exact;

  // the bounds of the scaled problem, and the working bounds with artificial ones for infinities
  private double[] boundLo;
  private double[] boundHi;
  private double[] lo;
  private double[] hi;
  private double big = BIG_START;

  private int[] basis;
  private int[] row; // the row of a basic column, -1 for a nonbasic one
  private boolean[] upper; // a nonbasic column at its upper bound
  private double[] d;
  private double[] beta;
  private double[] weight; // dual steepest edge: the squared norm of each row of B^-1

  // the values of the nonbasic columns that beta was computed with
  private double[] at;
  private boolean betaValid;

  private BasisLu lu;
  private boolean factorValid;

  // the rows from which on the steepest-edge weights are not known yet
  private int weightsFrom;

  private int infeasibleRow = -1;

  // counts the removals of rows: a saved basis is for the rows of one count
  private long rowEpoch;

  // work arrays by row or position, and by column for the row of the tableau (see allocateWork)
  private double[] rho = {};
  private double[] work = {};
  private double[] alphaQ = {};
  private double[] tau = {};
  private double[] alphaRow = {};

  // the nonzeros of rho (sorted by row), of alphaQ and of the steepest-edge tau, for the
  // hypersparse solves; rhs is the right-hand side of those, zero between them
  private int[] rhoIdx = {};
  private int rhoLen;
  private int[] alphaIdx = {};
  private int alphaLen;
  private double[] dseTau = {};
  private int[] tauIdx = {};
  private int tauLen;
  private double[] rhs = {};
  private int[] rhsIdx = {};
  private boolean[] inRhs = {};
  // the change of the basic values from the bound flips, zero between pivots, and its nonzeros
  private double[] flipTau = {};
  private int[] flipIdx = {};

  // the rows whose basic values are outside their bounds, kept up by the pivots (and rows back
  // inside, until the next choice of a leaving row drops them); not valid after any other change
  // of basic values or bounds
  private int[] outside = {};
  private boolean[] outsideRow = {};
  private int outsideLen;
  private boolean outsideValid;

  // rows left out of the choice of leaving rows for the rest of a solve: their violation had no
  // proof of infeasibility on fresh factors
  private boolean[] skipped = {};
  private int skippedRows;
  private double[] proofAlpha = {};
  private int[] touched = {};
  private int touchedCount;
  private boolean[] isTouched = {};

  // the ratio test: the candidates, their pivots and ratios, and the columns flipped
  private int[] candidate = {};
  private double[] candPivot = {};
  private double[] candSlack = {};
  private double[] candRange = {};
  private int[] flipped = {};
  private int flips;
  private boolean artificialProof;

  // solving with no costs, after the proofs kept resting on the artificial bounds
  private boolean feasibility;

  private long totalPivots;
  private long factorizations;
  private long ops;

  /**
   * Creates the problem with the slack basis, scaled.
   *
   * @param columns the columns of each row
   * @param weights the weights of each row, matching its columns
   * @param rowLo the lower bounds of the rows, or negative infinity
   * @param rowHi the upper bounds of the rows, or positive infinity
   * @param cost the objective over the n columns, minimized
   */
  public RevisedDualSimplex(
      int[][] columns, double[][] weights, double[] rowLo, double[] rowHi, double[] cost) {
    this(columns, weights, rowLo, rowHi, cost, true);
  }

  /**
   * Creates the problem with the slack basis. The columns are bounded by [0, +inf) until {@link
   * #setBounds} says otherwise.
   *
   * @param columns the columns of each row
   * @param weights the weights of each row, matching its columns
   * @param rowLo the lower bounds of the rows, or negative infinity
   * @param rowHi the upper bounds of the rows, or positive infinity
   * @param cost the objective over the n columns, minimized
   * @param scale whether to scale the rows and columns
   */
  public RevisedDualSimplex(
      int[][] columns,
      double[][] weights,
      double[] rowLo,
      double[] rowHi,
      double[] cost,
      boolean scale) {
    this.n = cost.length;
    this.m = 0;
    this.cols = n;
    this.scaling = scale;
    this.rowIdx = new int[0][];
    this.rowVal = new double[0][];
    this.colIdx = new int[n][];
    this.colVal = new double[n][];
    this.colLen = new int[n];
    for (int j = 0; j < n; j++) {
      colIdx[j] = new int[2];
      colVal[j] = new double[2];
    }
    rowScale = new double[0];
    colScale = new double[n];
    Arrays.fill(colScale, 1);
    givenCost = cost.clone();
    seed = n * 31L + columns.length;
    this.cost = new double[n];
    trueCost = new double[n];
    boundLo = new double[n];
    boundHi = new double[n];
    Arrays.fill(boundHi, Double.POSITIVE_INFINITY);
    lo = new double[n];
    hi = new double[n];
    basis = new int[0];
    row = new int[n];
    Arrays.fill(row, -1);
    upper = new boolean[n];
    d = new double[n];
    beta = new double[0];
    weight = new double[0];
    at = new double[n];
    if (scale && columns.length > 0) {
      computeColumnScales(columns, weights);
    }
    setCosts(true);
    for (int j = 0; j < n; j++) {
      workingBounds(j);
    }
    allocateWork();
    appendRows(columns, weights, rowLo, rowHi);
    // the slack basis: B = -I, so every row of B^-1 has norm 1
    Arrays.fill(weight, 1);
    weightsFrom = m;
  }

  // a deep copy of the state of another simplex
  private RevisedDualSimplex(RevisedDualSimplex o) {
    m = o.m;
    n = o.n;
    cols = o.cols;
    scaling = o.scaling;
    rowIdx = o.rowIdx.clone(); // the rows themselves are never changed
    rowVal = o.rowVal.clone();
    colIdx = new int[n][];
    colVal = new double[n][];
    for (int j = 0; j < n; j++) {
      colIdx[j] = o.colIdx[j].clone();
      colVal[j] = o.colVal[j].clone();
    }
    colLen = o.colLen.clone();
    nonzeros = o.nonzeros;
    rowScale = o.rowScale.clone();
    colScale = o.colScale.clone();
    cost = o.cost.clone();
    trueCost = o.trueCost.clone();
    givenCost = o.givenCost;
    perturbed = o.perturbed;
    seed = o.seed;
    exact = o.exact;
    boundLo = o.boundLo.clone();
    boundHi = o.boundHi.clone();
    lo = o.lo.clone();
    hi = o.hi.clone();
    big = o.big;
    basis = o.basis.clone();
    row = o.row.clone();
    upper = o.upper.clone();
    d = o.d.clone();
    beta = o.beta.clone();
    weight = o.weight.clone();
    at = o.at.clone();
    betaValid = false;
    factorValid = false; // the copy factorizes its basis again when it is solved
    weightsFrom = o.weightsFrom;
    infeasibleRow = o.infeasibleRow;
    rowEpoch = o.rowEpoch;
    totalPivots = o.totalPivots;
    factorizations = o.factorizations;
    ops = o.ops + (o.lu == null ? 0 : o.lu.ops);
    lu = null;
    touchedCount = 0;
    skippedRows = 0;
    flips = 0;
    artificialProof = false;
    feasibility = false;
    allocateWork();
  }

  /**
   * Returns a deep copy, which factorizes its basis again when it is first solved.
   *
   * @return the copy
   */
  public RevisedDualSimplex copy() {
    return new RevisedDualSimplex(this);
  }

  /**
   * Sets whether the cost perturbation is removed before an optimal solve returns, so that the
   * objective, the values and the duals are those of the costs as given.
   *
   * @param exact whether to remove the perturbation at the end of a solve
   */
  public void setExact(boolean exact) {
    this.exact = exact;
  }

  // the costs of the scaled problem, perturbed or not
  private void setCosts(boolean perturb) {
    Random rnd = new Random(seed);
    for (int j = 0; j < n; j++) {
      double c = givenCost[j] * colScale[j];
      trueCost[j] = c;
      cost[j] = perturb ? c + PERTURBATION * (1 + rnd.nextDouble()) * (1 + Math.abs(c)) : c;
    }
    perturbed = perturb;
  }

  // geometric scaling of the columns over the rows given, the rows scaled on the fly
  private void computeColumnScales(int[][] columns, double[][] weights) {
    int k = columns.length;
    double[] rs = new double[k];
    Arrays.fill(rs, 1);
    double[] cmin = new double[n];
    double[] cmax = new double[n];
    for (int pass = 0; pass < SCALE_PASSES; pass++) {
      for (int i = 0; i < k; i++) {
        double mn = Double.POSITIVE_INFINITY;
        double mx = 0;
        for (int e = 0; e < columns[i].length; e++) {
          double v = Math.abs(weights[i][e] * colScale[columns[i][e]]);
          if (v > 0) {
            mn = Math.min(mn, v);
            mx = Math.max(mx, v);
          }
        }
        rs[i] = mx > 0 ? 1 / Math.sqrt(mn * mx) : 1;
      }
      Arrays.fill(cmin, Double.POSITIVE_INFINITY);
      Arrays.fill(cmax, 0);
      for (int i = 0; i < k; i++) {
        for (int e = 0; e < columns[i].length; e++) {
          int j = columns[i][e];
          double v = Math.abs(weights[i][e] * rs[i]);
          if (v > 0) {
            cmin[j] = Math.min(cmin[j], v);
            cmax[j] = Math.max(cmax[j], v);
          }
        }
      }
      for (int j = 0; j < n; j++) {
        colScale[j] = cmax[j] > 0 ? 1 / Math.sqrt(cmin[j] * cmax[j]) : 1;
      }
    }
    // equilibrate the columns: the largest entry of each column near 1
    Arrays.fill(cmax, 0);
    for (int i = 0; i < k; i++) {
      for (int e = 0; e < columns[i].length; e++) {
        int j = columns[i][e];
        cmax[j] = Math.max(cmax[j], Math.abs(weights[i][e] * rs[i] * colScale[j]));
      }
    }
    for (int j = 0; j < n; j++) {
      colScale[j] = powerOfTwo(cmax[j] > 0 ? colScale[j] / cmax[j] : 1);
    }
  }

  // the largest exponent of a scale factor, as in HiGHS: beyond it a column's reduced cost within
  // the tolerance can hide a large change of the objective over its scaled range
  // (var-smallemery-m6j6: a column scaled by 2^-28, the optimum 1e-4 off)
  private static final int MAX_SCALE_EXPONENT =
      Integer.getInteger("org.jacop.jalp.maxScaleExponent", 20);

  // the power of two nearest to v > 0
  private static double powerOfTwo(double v) {
    if (!(v > 0) || Double.isInfinite(v)) {
      return 1;
    }
    int e = (int) Math.round(Math.log(v) / Math.log(2));
    return Math.scalb(1.0, Math.max(-MAX_SCALE_EXPONENT, Math.min(MAX_SCALE_EXPONENT, e)));
  }

  private void allocateWork() {
    rho = new double[m];
    work = new double[m];
    alphaQ = new double[m];
    tau = new double[m];
    rhoIdx = new int[m];
    rhoLen = 0;
    alphaIdx = new int[m];
    alphaLen = 0;
    dseTau = new double[m];
    tauIdx = new int[m];
    tauLen = 0;
    rhs = new double[m];
    rhsIdx = new int[m];
    inRhs = new boolean[m];
    flipTau = new double[m];
    flipIdx = new int[m];
    outside = new int[m];
    outsideRow = new boolean[m];
    outsideLen = 0;
    outsideValid = false;
    alphaRow = new double[cols];
    touched = new int[cols];
    isTouched = new boolean[cols];
    candidate = new int[cols];
    candPivot = new double[cols];
    candSlack = new double[cols];
    candRange = new double[cols];
    flipped = new int[cols];
  }

  // the working bounds of column j: its bounds with artificial ones for the infinite ones
  private void workingBounds(int j) {
    lo[j] = boundLo[j] == Double.NEGATIVE_INFINITY ? -big : boundLo[j];
    hi[j] = boundHi[j] == Double.POSITIVE_INFINITY ? big : boundHi[j];
    if (lo[j] > hi[j] && (isArtificial(j, false) || isArtificial(j, true))) {
      // a finite bound beyond the artificial one: the artificial one moves past it
      if (isArtificial(j, false)) {
        lo[j] = Math.min(-big, hi[j] - big);
      } else {
        hi[j] = Math.max(big, lo[j] + big);
      }
    }
  }

  private boolean isArtificial(int j, boolean atUpper) {
    return atUpper
        ? boundHi[j] == Double.POSITIVE_INFINITY
        : boundLo[j] == Double.NEGATIVE_INFINITY;
  }

  // appends rows with basic slacks; the factorization and the values must be rebuilt after
  private void appendRows(int[][] columns, double[][] weights, double[] rowLo, double[] rowHi) {
    int k = columns.length;
    int m2 = m + k;
    int cols2 = cols + k;
    rowIdx = Arrays.copyOf(rowIdx, m2);
    rowVal = Arrays.copyOf(rowVal, m2);
    rowScale = Arrays.copyOf(rowScale, m2);
    // the entry of each column in the row being merged, or -1
    int[] slot = new int[n];
    Arrays.fill(slot, -1);
    for (int q = 0; q < k; q++) {
      int i = m + q;
      // duplicates merged, zeros dropped
      int[] cs = columns[q].clone();
      double[] ws = weights[q].clone();
      int len = 0;
      for (int e = 0; e < cs.length; e++) {
        int f = slot[cs[e]];
        if (f >= 0) {
          ws[f] += ws[e];
        } else {
          slot[cs[e]] = len;
          cs[len] = cs[e];
          ws[len++] = ws[e];
        }
      }
      for (int e = 0; e < len; e++) {
        slot[cs[e]] = -1;
      }
      int keep = 0;
      for (int e = 0; e < len; e++) {
        if (ws[e] != 0) {
          cs[keep] = cs[e];
          ws[keep++] = ws[e];
        }
      }
      // the row scale: the largest scaled entry of the row near 1
      double r = 1;
      if (scaling) {
        double mx = 0;
        for (int e = 0; e < keep; e++) {
          mx = Math.max(mx, Math.abs(ws[e] * colScale[cs[e]]));
        }
        r = powerOfTwo(mx > 0 ? 1 / mx : 1);
      }
      rowScale[i] = r;
      for (int e = 0; e < keep; e++) {
        ws[e] *= r * colScale[cs[e]];
      }
      rowIdx[i] = Arrays.copyOf(cs, keep);
      rowVal[i] = Arrays.copyOf(ws, keep);
      nonzeros += keep;
      for (int e = 0; e < keep; e++) {
        int j = rowIdx[i][e];
        if (colLen[j] == colIdx[j].length) {
          colIdx[j] = Arrays.copyOf(colIdx[j], colLen[j] * 2);
          colVal[j] = Arrays.copyOf(colVal[j], colLen[j] * 2);
        }
        colIdx[j][colLen[j]] = i;
        colVal[j][colLen[j]++] = rowVal[i][e];
      }
    }
    // the slack of row i is column n + i; the slacks of the old rows keep their columns
    cost = Arrays.copyOf(cost, cols2);
    trueCost = Arrays.copyOf(trueCost, cols2);
    boundLo = Arrays.copyOf(boundLo, cols2);
    boundHi = Arrays.copyOf(boundHi, cols2);
    lo = Arrays.copyOf(lo, cols2);
    hi = Arrays.copyOf(hi, cols2);
    row = Arrays.copyOf(row, cols2);
    upper = Arrays.copyOf(upper, cols2);
    d = Arrays.copyOf(d, cols2);
    at = Arrays.copyOf(at, cols2);
    basis = Arrays.copyOf(basis, m2);
    beta = Arrays.copyOf(beta, m2);
    weight = Arrays.copyOf(weight, m2);
    for (int q = 0; q < k; q++) {
      int s = cols + q;
      double r = rowScale[m + q];
      boundLo[s] = rowLo[q] * r;
      boundHi[s] = rowHi[q] * r;
      workingBounds(s);
      basis[m + q] = s;
      row[s] = m + q;
    }
    weightsFrom = Math.min(weightsFrom, m);
    m = m2;
    cols = cols2;
    factorValid = false;
    betaValid = false;
    allocateWork();
  }

  /**
   * Returns the number of rows.
   *
   * @return the rows
   */
  public int rows() {
    return m;
  }

  /**
   * Returns the number of structural columns.
   *
   * @return the columns
   */
  public int columns() {
    return n;
  }

  /**
   * Returns the pivots made so far.
   *
   * @return the pivots
   */
  public long pivots() {
    return totalPivots;
  }

  /**
   * Returns the factorizations made so far.
   *
   * @return the factorizations
   */
  public long factorizations() {
    return factorizations;
  }

  // a sparse operation, with its indirect access, against an update of a dense tableau entry
  private static final long OP_COST = 3;

  /**
   * Returns an estimate of the work done so far, in updates of a dense tableau entry.
   *
   * @return the work
   */
  public long work() {
    return OP_COST * (ops + (lu == null ? 0 : lu.ops));
  }

  /**
   * Returns an estimate of the work of one pivot.
   *
   * @return the work of a pivot
   */
  public long pivotWork() {
    long base = OP_COST * (2L * m + cols);
    return totalPivots == 0 ? base : Math.max(base, work() / totalPivots);
  }

  /**
   * Sets the bounds of a column, structural ({@code j < n}) or slack ({@code n + i}).
   *
   * @param j the column
   * @param min its lower bound, or negative infinity
   * @param max its upper bound, or positive infinity
   */
  public void setBounds(int j, double min, double max) {
    double s = j < n ? 1 / colScale[j] : rowScale[j - n];
    boundLo[j] = min * s;
    boundHi[j] = max * s;
    workingBounds(j);
    outsideValid = false;
  }

  /**
   * Solves the problem from the current basis.
   *
   * @param limit the most pivots to make
   * @return {@link #OPTIMAL}, {@link #INFEASIBLE}, {@link #UNBOUNDED} or {@link #LIMIT}
   */
  public int solve(int limit) {
    infeasibleRow = -1;
    outsideValid = false;
    clearSkipped();
    if (feasibility) {
      feasibility = false;
      setCosts(true);
      if (factorValid) {
        computeDuals();
      }
    }
    if (exact && !perturbed) {
      setCosts(true);
      computeDuals();
    }
    if (!factorValid) {
      factorize();
    }
    placeNonbasic();
    updateBeta();
    for (int iter = 0; iter < limit; iter++) {
      ops += 3L * m;
      int r = leavingRow();
      if (r < 0) {
        int status = atOptimum();
        if (status >= 0) {
          return status;
        }
        continue;
      }
      int p = basis[r];
      // the basic columns are held to their own bounds, never to artificial ones
      boolean toLower = beta[r] < boundLo[p];
      rhoLen = unitRow(r, rho, rhoIdx, rhoLen);
      pivotRow();
      int q = enteringColumn(toLower, toLower ? boundLo[p] - beta[r] : beta[r] - boundHi[p]);
      if (q < 0) {
        clearTouched();
        if (artificialProof) {
          // the proof rests on a column at an artificial bound that the objective pulls on:
          // enlarge them and go on, and when they are at their largest drop the objective to
          // tell an infeasible problem from an unbounded one
          if (!enlarge()) {
            if (feasibility) {
              return LIMIT;
            }
            feasibility = true;
            Arrays.fill(cost, 0);
            computeDuals();
            placeNonbasic();
            updateBeta();
          }
          continue;
        }
        if (!proofHolds(r)) {
          if (lu.updates() > 0) {
            // a proof from updated factors that does not hold on its own: confirm it with fresh
            // factors and basic values
            refactor();
            continue;
          }
          // no proof on fresh factors either: the row's violation is round-off (qap15: two equal
          // rows, rho their difference, the range of the combination [0, 0]); the row is left
          // out of the choice of leaving rows until the end of the solve
          skipped[r] = true;
          skippedRows++;
          continue;
        }
        infeasibleRow = r;
        return INFEASIBLE;
      }
      clear(alphaQ, alphaIdx, alphaLen);
      alphaLen = lu.ftran(rhs, rhsIdx, columnInto(q, rhs, rhsIdx), alphaQ, alphaIdx, true);
      double fromRow = alphaRow[q];
      double fromColumn = alphaQ[r];
      if (lu.updates() > 0
          && Math.abs(fromRow - fromColumn) > PIVOT_AGREEMENT * (1 + Math.abs(fromColumn))) {
        // the updates drifted: start again from a fresh factorization
        clearTouched();
        refactor();
        continue;
      }
      if (flips > 0) {
        flipBounds();
      }
      // the primal step: x_q moves until x_p reaches the bound it leaves at
      double bound = toLower ? lo[p] : hi[p];
      double theta = (beta[r] - bound) / fromColumn;
      double xq = (upper[q] ? hi[q] : lo[q]) + theta;
      if (theta != 0) {
        for (int k = 0; k < alphaLen; k++) {
          int i = alphaIdx[k];
          beta[i] -= alphaQ[i] * theta;
        }
      }
      beta[r] = xq;
      // the dual step along the row of the tableau
      double thetaD = d[q] / fromRow;
      for (int t = 0; t < touchedCount; t++) {
        int j = touched[t];
        d[j] -= thetaD * alphaRow[j];
      }
      d[p] = -thetaD;
      d[q] = 0;
      // the steepest-edge weights, from tau = B^-1 rho
      double wr = 0;
      for (int k = 0; k < rhoLen; k++) {
        int i = rhoIdx[k];
        wr += rho[i] * rho[i];
        rhs[i] = rho[i];
        rhsIdx[k] = i;
      }
      clear(dseTau, tauIdx, tauLen);
      tauLen = lu.ftran(rhs, rhsIdx, rhoLen, dseTau, tauIdx, false);
      for (int k = 0; k < alphaLen; k++) {
        int i = alphaIdx[k];
        if (i != r) {
          double f = alphaQ[i] / fromColumn;
          weight[i] = Math.max(weight[i] + f * (f * wr - 2 * dseTau[i]), 1e-12);
        }
      }
      weight[r] = Math.max(wr / (fromColumn * fromColumn), 1e-12);
      clearTouched();
      boolean stable = lu.update(r);
      basis[r] = q;
      row[q] = r;
      row[p] = -1;
      upper[p] = !toLower;
      at[p] = bound;
      totalPivots++;
      if (outsideValid) {
        for (int k = 0; k < alphaLen; k++) {
          noteRow(alphaIdx[k]);
        }
        noteRow(r);
      }
      if (!stable
          || lu.updates() >= REFACTOR_UPDATES
          || lu.updateNonzeros() > 2 * (lu.factorNonzeros + m)) {
        refactor();
      }
    }
    return LIMIT;
  }

  private void refactor() {
    factorize();
    placeNonbasic();
    updateBeta();
  }

  // at a primal feasible basis: the status to return, or -1 to go on pivoting
  private int atOptimum() {
    if (skippedRows > 0) {
      // the rows left out must hold on fresh basic values, or the solve stops at its limit
      clearSkipped();
      refactor();
      if (leavingRow() >= 0) {
        return LIMIT;
      }
    }
    if (feasibility) {
      // feasible, but the objective pulled a column past every artificial bound
      return UNBOUNDED;
    }
    if (exact && perturbed) {
      // the costs as given: the columns whose reduced cost changed sign move to their other bound
      setCosts(false);
      computeDuals();
      placeNonbasic();
      updateBeta();
      return -1;
    }
    if (lu.updates() > 0 && !dualsHold()) {
      return -1;
    }
    // a nonbasic column at an artificial bound that the objective pulls on: the bounds are too
    // close
    for (int j = 0; j < cols; j++) {
      if (row[j] < 0 && isArtificial(j, upper[j]) && lo[j] != hi[j]) {
        if (upper[j] ? d[j] < -DUAL_TOL : d[j] > DUAL_TOL) {
          if (!enlarge()) {
            return UNBOUNDED;
          }
          return -1;
        }
      }
    }
    return OPTIMAL;
  }

  /**
   * Whether the reduced costs, computed again from the duals of the current factors, still place
   * every nonbasic column at the bound it is at. The reduced costs kept up by the pivots drift, and
   * a column whose sign changed would leave the solution not optimal (var-smallemery-m6j6: a column
   * at its lower bound with reduced cost -1.12, the objective 1e-4 off); when one moved, the basic
   * values follow and the pivots go on.
   */
  private boolean dualsHold() {
    computeDuals();
    boolean held = true;
    for (int j = 0; j < cols; j++) {
      if (row[j] < 0 && (upper[j] ? d[j] > DUAL_TOL : d[j] < -DUAL_TOL)) {
        held = false;
      }
    }
    if (!held) {
      placeNonbasic();
      updateBeta();
    }
    return held;
  }

  // enlarges the artificial bounds; false when they are at their largest
  private boolean enlarge() {
    if (big * BIG_GROWTH > BIG_MAX) {
      return false;
    }
    big *= BIG_GROWTH;
    for (int j = 0; j < cols; j++) {
      workingBounds(j);
    }
    betaValid = false;
    if (!factorValid) {
      factorize();
    }
    placeNonbasic();
    updateBeta();
    return true;
  }

  /**
   * Returns the row of the basis inverse that proved infeasibility (a Farkas ray over the rows).
   *
   * @return the multipliers of the rows
   */
  public double[] farkas() {
    return inverseRow(infeasibleRow);
  }

  /**
   * Returns a row of the basis inverse for the problem as given, scaled so that the basic column of
   * the row has coefficient one in the combination {@code y (A x - s)}.
   *
   * @param r the row of the basis
   * @return the multipliers of the rows
   */
  public double[] inverseRow(int r) {
    if (!factorValid) {
      factorize();
    }
    double[] y = new double[m];
    int[] yi = new int[m];
    int len = unitRow(r, y, yi, 0);
    int p = basis[r];
    double f = p < n ? colScale[p] : 1 / rowScale[p - n];
    for (int k = 0; k < len; k++) {
      int i = yi[k];
      y[i] *= rowScale[i] * f;
    }
    return y;
  }

  /**
   * Returns the duals {@code c_B B^-1} of the rows for the costs the last solve ended with.
   *
   * @return the duals by row
   */
  public double[] duals() {
    return duals(cost);
  }

  /**
   * Returns the duals {@code c_B B^-1} of the rows for the costs as given, over the basis the last
   * solve ended with. Without {@link #setExact(boolean)} that basis is optimal for the perturbed
   * costs; these duals are free of the perturbation, and their reduced costs are off by at most the
   * perturbation.
   *
   * @return the duals by row
   */
  public double[] givenDuals() {
    return duals(trueCost);
  }

  private double[] duals(double[] c) {
    if (!factorValid) {
      factorize();
    }
    double[] y = new double[m];
    double[] z = new double[m];
    for (int k = 0; k < m; k++) {
      z[k] = c[basis[k]];
    }
    lu.btran(z, y);
    for (int i = 0; i < m; i++) {
      y[i] *= rowScale[i];
    }
    return y;
  }

  /**
   * Returns the objective of the current solution for the costs as given.
   *
   * @return the objective
   */
  public double objective() {
    double z = 0;
    for (int j = 0; j < n; j++) {
      if (givenCost[j] != 0) {
        z += givenCost[j] * value(j);
      }
    }
    return z;
  }

  /**
   * Returns the value of a column, structural ({@code j < n}) or slack ({@code n + i}).
   *
   * @param j the column
   * @return its value
   */
  public double value(int j) {
    double v = row[j] >= 0 ? beta[row[j]] : upper[j] ? hi[j] : lo[j];
    return j < n ? v * colScale[j] : v / rowScale[j - n];
  }

  /**
   * A basis saved by {@link #saveBasis}: the basic column of each row, the bound of each nonbasic
   * column, and the steepest-edge weights. It holds for the rows of the simplex when it was saved
   * and for the rows added since, whose slacks it makes basic.
   */
  public static final class Basis {
    private final RevisedDualSimplex owner;
    private final long epoch;
    private final int[] basic;
    private final boolean[] atUpper;
    private final double[] weights;
    private final int weightsKnown;

    private Basis(RevisedDualSimplex s) {
      owner = s;
      epoch = s.rowEpoch;
      basic = Arrays.copyOf(s.basis, s.m);
      atUpper = Arrays.copyOf(s.upper, s.cols);
      weights = Arrays.copyOf(s.weight, s.m);
      weightsKnown = Math.min(s.weightsFrom, s.m);
    }

    /**
     * Returns the number of rows the basis is for.
     *
     * @return the rows
     */
    public int rows() {
      return basic.length;
    }
  }

  /**
   * Saves the current basis, to be restored by {@link #restoreBasis} after the bounds have moved
   * far from those it was optimal for (a restart, a long backjump).
   *
   * @return the basis
   */
  public Basis saveBasis() {
    ops += cols + 2L * m;
    return new Basis(this);
  }

  /**
   * Makes a saved basis the current one. The slacks of the rows added since it was saved are basic,
   * so the basis stays nonsingular and dual feasible, as it was when it was saved; the next solve
   * factorizes it. A basis saved before rows were removed, or by another simplex, is not restored.
   *
   * @param b the basis
   * @return whether it was restored
   */
  public boolean restoreBasis(Basis b) {
    if (b.owner != this || b.epoch != rowEpoch || b.basic.length > m) {
      return false;
    }
    int k = b.basic.length;
    ops += cols + 2L * m;
    Arrays.fill(row, 0, cols, -1);
    System.arraycopy(b.basic, 0, basis, 0, k);
    for (int r = k; r < m; r++) {
      basis[r] = n + r;
    }
    for (int r = 0; r < m; r++) {
      row[basis[r]] = r;
    }
    System.arraycopy(b.atUpper, 0, upper, 0, b.atUpper.length);
    Arrays.fill(upper, b.atUpper.length, cols, false);
    System.arraycopy(b.weights, 0, weight, 0, k);
    // the weights of the rows added since are computed again at the factorization
    weightsFrom = b.weightsKnown;
    factorValid = false;
    betaValid = false;
    outsideValid = false;
    infeasibleRow = -1;
    return true;
  }

  /**
   * Returns the row of the basis a column is basic in, or -1.
   *
   * @param j the column
   * @return its row, or -1 when it is nonbasic
   */
  public int basicRow(int j) {
    return row[j];
  }

  /**
   * Adds rows, with basic slacks.
   *
   * @param columns the columns of each row
   * @param weights the weights of each row
   * @param rowLo the lower bounds of the rows
   * @param rowHi the upper bounds of the rows
   */
  public void addRows(int[][] columns, double[][] weights, double[] rowLo, double[] rowHi) {
    if (columns.length > 0) {
      appendRows(columns, weights, rowLo, rowHi);
    }
  }

  /**
   * Removes rows whose slacks are basic. Their slacks leave with them, the basis of the other rows
   * stays, and so does dual feasibility; a row whose slack is nonbasic is kept.
   *
   * @param rows the rows to remove
   * @return the old row of each new row, or null when no row was removed
   */
  public int[] removeRows(int[] rows) {
    boolean[] gone = new boolean[m];
    int removed = 0;
    for (int i : rows) {
      if (i >= 0 && i < m && !gone[i] && row[n + i] >= 0) {
        gone[i] = true;
        removed++;
      }
    }
    if (removed == 0) {
      return null;
    }
    int m2 = m - removed;
    int cols2 = cols - removed;
    int[] newRow = new int[m]; // old row to new row, or -1
    int[] oldRow = new int[m2];
    int k = 0;
    for (int i = 0; i < m; i++) {
      if (gone[i]) {
        newRow[i] = -1;
      } else {
        newRow[i] = k;
        oldRow[k++] = i;
      }
    }
    // the positions of the basis: the positions of the removed slacks go, the others keep order
    int[] newPos = new int[m];
    int[] basis2 = new int[m2];
    double[] beta2 = new double[m2];
    double[] weight2 = new double[m2];
    k = 0;
    for (int r = 0; r < m; r++) {
      int j = basis[r];
      if (j >= n && gone[j - n]) {
        newPos[r] = -1;
        continue;
      }
      newPos[r] = k;
      basis2[k] = j < n ? j : n + newRow[j - n];
      beta2[k] = beta[r];
      weight2[k++] = weight[r];
    }
    double[] cost2 = new double[cols2];
    double[] trueCost2 = new double[cols2];
    double[] boundLo2 = new double[cols2];
    double[] boundHi2 = new double[cols2];
    double[] lo2 = new double[cols2];
    double[] hi2 = new double[cols2];
    boolean[] upper2 = new boolean[cols2];
    double[] d2 = new double[cols2];
    double[] at2 = new double[cols2];
    int[] row2 = new int[cols2];
    for (int j = 0; j < cols; j++) {
      int j2;
      if (j < n) {
        j2 = j;
      } else if (gone[j - n]) {
        continue;
      } else {
        j2 = n + newRow[j - n];
      }
      cost2[j2] = cost[j];
      trueCost2[j2] = trueCost[j];
      boundLo2[j2] = boundLo[j];
      boundHi2[j2] = boundHi[j];
      lo2[j2] = lo[j];
      hi2[j2] = hi[j];
      upper2[j2] = upper[j];
      d2[j2] = d[j];
      at2[j2] = at[j];
      row2[j2] = row[j] >= 0 ? newPos[row[j]] : -1;
    }
    int[][] rowIdx2 = new int[m2][];
    double[][] rowVal2 = new double[m2][];
    double[] rowScale2 = new double[m2];
    for (int i = 0; i < m2; i++) {
      rowIdx2[i] = rowIdx[oldRow[i]];
      rowVal2[i] = rowVal[oldRow[i]];
      rowScale2[i] = rowScale[oldRow[i]];
    }
    rowIdx = rowIdx2;
    rowVal = rowVal2;
    rowScale = rowScale2;
    nonzeros = 0;
    Arrays.fill(colLen, 0);
    for (int i = 0; i < m2; i++) {
      nonzeros += rowIdx[i].length;
      for (int e = 0; e < rowIdx[i].length; e++) {
        int j = rowIdx[i][e];
        if (colLen[j] == colIdx[j].length) {
          colIdx[j] = Arrays.copyOf(colIdx[j], colLen[j] * 2 + 1);
          colVal[j] = Arrays.copyOf(colVal[j], colLen[j] * 2 + 1);
        }
        colIdx[j][colLen[j]] = i;
        colVal[j][colLen[j]++] = rowVal[i][e];
      }
    }
    // weights not known yet are all computed again
    weightsFrom = weightsFrom < m ? 0 : m2;
    basis = basis2;
    beta = beta2;
    weight = weight2;
    cost = cost2;
    trueCost = trueCost2;
    boundLo = boundLo2;
    boundHi = boundHi2;
    lo = lo2;
    hi = hi2;
    upper = upper2;
    d = d2;
    at = at2;
    row = row2;
    m = m2;
    cols = cols2;
    factorValid = false;
    infeasibleRow = -1;
    rowEpoch++;
    allocateWork();
    return oldRow;
  }

  // x += f times the column j of [A -I]
  private void addColumn(int j, double f, double[] x) {
    if (f == 0) {
      return;
    }
    if (j < n) {
      int[] ci = colIdx[j];
      double[] cv = colVal[j];
      for (int e = 0; e < colLen[j]; e++) {
        x[ci[e]] += f * cv[e];
      }
    } else {
      x[j - n] -= f;
    }
  }

  // the row r of B^-1 into y, whose yn nonzeros listed in yi are cleared first; returns the
  // number of its nonzeros, listed in yi by row
  private int unitRow(int r, double[] y, int[] yi, int yn) {
    clear(y, yi, yn);
    rhs[r] = 1;
    rhsIdx[0] = r;
    int len = lu.btran(rhs, rhsIdx, 1, y, yi);
    Arrays.sort(yi, 0, len);
    return len;
  }

  private static void clear(double[] y, int[] yi, int yn) {
    for (int k = 0; k < yn; k++) {
      y[yi[k]] = 0;
    }
  }

  // the flipped columns move to their other bounds, and the basic values with them: the sum of
  // the flipped columns is listed in rhs, and its ftran gives the rows whose values move, which
  // also keep up the rows outside their bounds
  private void flipBounds() {
    int len = 0;
    for (int k = 0; k < flips; k++) {
      int j = flipped[k];
      double old = upper[j] ? hi[j] : lo[j];
      upper[j] = !upper[j];
      double now = upper[j] ? hi[j] : lo[j];
      at[j] = now;
      len = addListed(j, now - old, len);
    }
    for (int k = 0; k < len; k++) {
      inRhs[rhsIdx[k]] = false;
    }
    int yn = lu.ftranFlips(rhs, rhsIdx, len, flipTau, flipIdx);
    for (int k = 0; k < yn; k++) {
      int i = flipIdx[k];
      beta[i] -= flipTau[i];
      flipTau[i] = 0;
    }
    if (outsideValid) {
      for (int k = 0; k < yn; k++) {
        noteRow(flipIdx[k]);
      }
    }
    ops += len + yn;
  }

  // rhs += f times the column j of [A -I], as addColumn, with the rows of rhs listed in rhsIdx
  // (len of them, marked in inRhs); returns the new number of rows listed
  private int addListed(int j, double f, int len) {
    if (f == 0) {
      return len;
    }
    if (j < n) {
      int[] ci = colIdx[j];
      double[] cv = colVal[j];
      for (int e = 0; e < colLen[j]; e++) {
        int i = ci[e];
        if (!inRhs[i]) {
          inRhs[i] = true;
          rhsIdx[len++] = i;
        }
        rhs[i] += f * cv[e];
      }
    } else {
      int i = j - n;
      if (!inRhs[i]) {
        inRhs[i] = true;
        rhsIdx[len++] = i;
      }
      rhs[i] -= f;
    }
    return len;
  }

  // the column j of [A -I] into x, zero before; returns the number of its nonzeros, listed in xi
  private int columnInto(int j, double[] x, int[] xi) {
    if (j >= n) {
      x[j - n] = -1;
      xi[0] = j - n;
      return 1;
    }
    int len = 0;
    int[] ci = colIdx[j];
    double[] cv = colVal[j];
    for (int e = 0; e < colLen[j]; e++) {
      int i = ci[e];
      if (x[i] == 0) {
        xi[len++] = i;
      }
      x[i] += cv[e];
    }
    return len;
  }

  // the row of the tableau rho [A -I] over the nonbasic columns, into alphaRow and touched
  private void pivotRow() {
    touchedCount = 0;
    ops += m;
    // row-wise over the nonzeros of rho, or column-wise over the nonbasic columns when rho is so
    // dense that the rows it touches hold a large share of A
    long rowWork = 0;
    for (int k = 0; k < rhoLen; k++) {
      rowWork += rowIdx[rhoIdx[k]].length + 1;
    }
    if (rowWork * 2 > nonzeros + m) {
      pivotRowByColumns();
      return;
    }
    for (int k = 0; k < rhoLen; k++) {
      int i = rhoIdx[k];
      double ri = rho[i];
      int[] idx = rowIdx[i];
      ops += idx.length;
      double[] val = rowVal[i];
      for (int e = 0; e < idx.length; e++) {
        int j = idx[e];
        if (row[j] < 0) {
          if (!isTouched[j]) {
            isTouched[j] = true;
            touched[touchedCount++] = j;
          }
          alphaRow[j] += ri * val[e];
        }
      }
      int s = n + i;
      if (row[s] < 0) {
        isTouched[s] = true;
        touched[touchedCount++] = s;
        alphaRow[s] = -ri;
      }
    }
  }

  /**
   * Whether rho, the row r of the basis inverse, proves the problem infeasible by itself: the
   * combination {@code rho (A x - s)} is zero for every solution, so it is one when the range of
   * the combination over the true bounds of the nonbasic columns and of the basic column of row r
   * excludes zero. The other basic columns are zero in it, and so are the entries below 1e-11 of
   * the largest, up to round-off. A proof that passes needs no fresh factorization.
   */
  private boolean proofHolds(int r) {
    if (proofAlpha.length < n + m) {
      proofAlpha = new double[n + m];
    }
    double largest = 0;
    for (int j = 0; j < n + m; j++) {
      double a = 0;
      if (row[j] < 0 || row[j] == r) {
        if (j < n) {
          int[] ci = colIdx[j];
          double[] cv = colVal[j];
          for (int e = 0; e < colLen[j]; e++) {
            a += rho[ci[e]] * cv[e];
          }
        } else {
          a = -rho[j - n];
        }
      }
      proofAlpha[j] = a;
      largest = Math.max(largest, Math.abs(a));
    }
    double noise = PROOF_NOISE * largest;
    double min = 0;
    double max = 0;
    double sizeMin = 0;
    double sizeMax = 0;
    for (int j = 0; j < n + m; j++) {
      double a = proofAlpha[j];
      if (Math.abs(a) <= noise) {
        continue;
      }
      double l = boundLo[j];
      double h = boundHi[j];
      double low = a > 0 ? a * l : a * h;
      double high = a > 0 ? a * h : a * l;
      min += low;
      max += high;
      sizeMin += Math.abs(low);
      sizeMax += Math.abs(high);
    }
    // an infinite bound leaves its side unbounded; each side is judged against its own size
    return min > PROOF_MARGIN * (1 + sizeMin) || max < -PROOF_MARGIN * (1 + sizeMax);
  }

  private void pivotRowByColumns() {
    ops += nonzeros + cols;
    for (int j = 0; j < n; j++) {
      if (row[j] < 0) {
        int[] ci = colIdx[j];
        double[] cv = colVal[j];
        double v = 0;
        for (int e = 0; e < colLen[j]; e++) {
          v += rho[ci[e]] * cv[e];
        }
        if (v != 0) {
          isTouched[j] = true;
          touched[touchedCount++] = j;
          alphaRow[j] = v;
        }
      }
    }
    for (int i = 0; i < m; i++) {
      int s = n + i;
      if (row[s] < 0 && rho[i] != 0) {
        isTouched[s] = true;
        touched[touchedCount++] = s;
        alphaRow[s] = -rho[i];
      }
    }
  }

  private void clearTouched() {
    for (int t = 0; t < touchedCount; t++) {
      int j = touched[t];
      isTouched[j] = false;
      alphaRow[j] = 0;
    }
    touchedCount = 0;
  }

  /**
   * The dual ratio test with bound flipping over the touched columns. The breakpoints are taken in
   * groups: each pass finds the largest step that keeps every remaining reduced cost within the
   * dual tolerance (Harris), and the group of breakpoints up to it is flipped as a whole while the
   * slope stays positive and every column of the group has a finite range. Otherwise the largest
   * pivot of the group enters.
   *
   * @return the entering column, or -1 when the row proves infeasibility
   */
  private int enteringColumn(boolean toLower, double gap) {
    ops += 2L * touchedCount;
    flips = 0;
    artificialProof = false;
    int count = 0;
    for (int t = 0; t < touchedCount; t++) {
      int j = touched[t];
      double alpha = alphaRow[j];
      // moving x_j towards its other bound brings the basic variable back towards the bound it
      // leaves at: with x_B = -sum alpha_j x_j, it rises when x_j rises with alpha_j < 0 or falls
      // with alpha_j > 0
      if (Math.abs(alpha) < PIVOT_TOL || lo[j] == hi[j]) {
        continue;
      }
      if ((upper[j] ? alpha > 0 : alpha < 0) == toLower) {
        candidate[count] = j;
        candPivot[count] = Math.abs(alpha);
        candSlack[count] = upper[j] ? -d[j] : d[j];
        // a column moving to an artificial bound enters rather than flips
        candRange[count] = isArtificial(j, !upper[j]) ? Double.POSITIVE_INFINITY : hi[j] - lo[j];
        count++;
      } else if (isArtificial(j, upper[j]) && Math.abs(d[j]) <= DUAL_TOL) {
        // a column at an artificial bound with no pull on it may move on past that bound
        candidate[count] = j;
        candPivot[count] = Math.abs(alpha);
        candSlack[count] = 0;
        candRange[count] = Double.POSITIVE_INFINITY;
        count++;
      }
    }
    double slope = gap;
    double stop = PRIMAL_TOL * Math.max(1, gap);
    while (count > 0) {
      ops += count;
      double bound = Double.POSITIVE_INFINITY;
      for (int i = 0; i < count; i++) {
        bound = Math.min(bound, (Math.max(0, candSlack[i]) + DUAL_TOL) / candPivot[i]);
      }
      // the group of breakpoints up to the bound, moved to the front
      int g = 0;
      double drop = 0;
      int pick = -1;
      for (int i = 0; i < count; i++) {
        if (Math.max(0, candSlack[i]) / candPivot[i] <= bound) {
          swap(i, g);
          drop += candPivot[g] * candRange[g];
          if (pick < 0 || candPivot[g] > candPivot[pick]) {
            pick = g;
          }
          g++;
        }
      }
      if (slope - drop <= stop) {
        return candidate[pick];
      }
      // the whole group flips and the slope stays positive
      for (int i = 0; i < g; i++) {
        flipped[flips++] = candidate[i];
      }
      slope -= drop;
      // what is left moves to the front
      System.arraycopy(candidate, g, candidate, 0, count - g);
      System.arraycopy(candPivot, g, candPivot, 0, count - g);
      System.arraycopy(candSlack, g, candSlack, 0, count - g);
      System.arraycopy(candRange, g, candRange, 0, count - g);
      count -= g;
      ops += g;
    }
    // every eligible column at its other bound leaves the basic variable outside: infeasible,
    // unless the proof uses another column at an artificial bound (a flipped column never moves
    // to one)
    flips = 0;
    for (int t = 0; t < touchedCount && !artificialProof; t++) {
      int j = touched[t];
      // entries below the pivot tolerance are round-off of entries that cancel
      if (Math.abs(alphaRow[j]) >= PIVOT_TOL && lo[j] != hi[j] && isArtificial(j, upper[j])) {
        artificialProof = (upper[j] ? alphaRow[j] > 0 : alphaRow[j] < 0) != toLower;
      }
    }
    return -1;
  }

  private void swap(int a, int b) {
    int c = candidate[a];
    candidate[a] = candidate[b];
    candidate[b] = c;
    double v = candPivot[a];
    candPivot[a] = candPivot[b];
    candPivot[b] = v;
    v = candSlack[a];
    candSlack[a] = candSlack[b];
    candSlack[b] = v;
    v = candRange[a];
    candRange[a] = candRange[b];
    candRange[b] = v;
  }

  // the basic row farthest outside its bounds, by dual steepest edge, or -1
  private void clearSkipped() {
    if (skipped.length < m) {
      skipped = new boolean[m];
    } else if (skippedRows > 0) {
      Arrays.fill(skipped, false);
    }
    skippedRows = 0;
  }

  private int leavingRow() {
    if (!outsideValid) {
      outsideLen = 0;
      for (int i = 0; i < m; i++) {
        outsideRow[i] = false;
        noteRow(i);
      }
      outsideValid = true;
      ops += m;
    }
    // the rows outside their bounds, which the pivots keep up, less those back inside; among
    // equal scores the first row, as a pass over all rows would take it
    int r = -1;
    double worst = 0;
    int kept = 0;
    for (int k = 0; k < outsideLen; k++) {
      int i = outside[k];
      int p = basis[i];
      double gap = gap(beta[i], boundLo[p], boundHi[p]);
      if (gap <= 0) {
        outsideRow[i] = false;
        continue;
      }
      outside[kept++] = i;
      if (skippedRows > 0 && skipped[i]) {
        continue;
      }
      double score = gap * gap / weight[i];
      if (score > worst || score == worst && i < r) {
        worst = score;
        r = i;
      }
    }
    ops += outsideLen;
    outsideLen = kept;
    return r;
  }

  // row i joins the rows outside their bounds when its basic value is
  private void noteRow(int i) {
    if (!outsideRow[i]) {
      int p = basis[i];
      if (gap(beta[i], boundLo[p], boundHi[p]) > 0) {
        outsideRow[i] = true;
        outside[outsideLen++] = i;
      }
    }
  }

  private static double gap(double v, double lo, double hi) {
    if (v < lo - PRIMAL_TOL) {
      return lo - v;
    } else if (v > hi + PRIMAL_TOL) {
      return v - hi;
    }
    return 0;
  }

  // puts each nonbasic column at the bound its reduced cost asks for
  private void placeNonbasic() {
    ops += cols;
    for (int j = 0; j < cols; j++) {
      if (row[j] < 0) {
        if (d[j] > DUAL_TOL) {
          upper[j] = false;
        } else if (d[j] < -DUAL_TOL) {
          upper[j] = true;
        } else if (isArtificial(j, upper[j]) && !isArtificial(j, !upper[j])) {
          // no pull either way: the finite bound
          upper[j] = !upper[j];
        }
      }
    }
  }

  // moves the basic values with the nonbasic columns whose values changed since the last call
  private void updateBeta() {
    outsideValid = false;
    if (!betaValid) {
      computeBeta();
      return;
    }
    ops += cols + m;
    Arrays.fill(work, 0);
    boolean any = false;
    for (int j = 0; j < cols; j++) {
      if (row[j] < 0) {
        double v = upper[j] ? hi[j] : lo[j];
        double delta = v - at[j];
        if (delta != 0) {
          addColumn(j, delta, work);
          at[j] = v;
          any = true;
        }
      }
    }
    if (any) {
      lu.ftran(work, tau);
      for (int i = 0; i < m; i++) {
        beta[i] -= tau[i];
      }
    }
  }

  // x_B = -B^-1 N x_N
  private void computeBeta() {
    betaValid = true;
    outsideValid = false;
    ops += cols + m + nonzeros;
    Arrays.fill(work, 0);
    for (int j = 0; j < cols; j++) {
      if (row[j] < 0) {
        double v = upper[j] ? hi[j] : lo[j];
        at[j] = v;
        addColumn(j, v, work);
      }
    }
    lu.ftran(work, beta);
    for (int i = 0; i < m; i++) {
      beta[i] = -beta[i];
    }
  }

  // d_j = c_j - y a_j with y = c_B B^-1, in the scaled problem
  private void computeDuals() {
    if (!factorValid) {
      factorize();
      return;
    }
    ops += nonzeros + cols;
    double[] y = new double[m];
    double[] z = new double[m];
    for (int k = 0; k < m; k++) {
      z[k] = cost[basis[k]];
    }
    lu.btran(z, y);
    for (int j = 0; j < n; j++) {
      if (row[j] >= 0) {
        d[j] = 0;
        continue;
      }
      double s = cost[j];
      int[] ci = colIdx[j];
      double[] cv = colVal[j];
      for (int e = 0; e < colLen[j]; e++) {
        s -= y[ci[e]] * cv[e];
      }
      d[j] = s;
    }
    for (int i = 0; i < m; i++) {
      d[n + i] = row[n + i] >= 0 ? 0 : cost[n + i] + y[i];
    }
  }

  /**
   * Factorizes the basis again. Basic columns found dependent are replaced by slacks of rows; the
   * reduced costs and basic values are computed again from the factorization, and the steepest-edge
   * weights not known yet are computed exactly.
   */
  private void factorize() {
    outsideValid = false;
    int[][] ci = new int[m][];
    double[][] cv = new double[m][];
    int[] cl = new int[m];
    for (int k = 0; k < m; k++) {
      int j = basis[k];
      if (j < n) {
        ci[k] = colIdx[j];
        cv[k] = colVal[j];
        cl[k] = colLen[j];
      } else {
        ci[k] = new int[] {j - n};
        cv[k] = new double[] {-1};
        cl[k] = 1;
      }
    }
    if (lu != null) {
      ops += lu.ops;
    }
    lu = new BasisLu(m, ci, cv, cl);
    factorizations++;
    factorValid = true;
    boolean replaced = lu.replacedPos.length > 0;
    for (int s = 0; s < lu.replacedPos.length; s++) {
      int k = lu.replacedPos[s];
      int p = basis[k];
      int sl = n + lu.replacedRow[s];
      row[p] = -1;
      basis[k] = sl;
      row[sl] = k;
      weight[k] = 1;
    }
    computeDuals();
    betaValid = false;
    if (replaced) {
      // the replaced columns are nonbasic now, at the bounds their reduced costs ask for
      weightsFrom = 0;
    }
    if (weightsFrom < m) {
      for (int r = weightsFrom; r < m; r++) {
        rhoLen = unitRow(r, rho, rhoIdx, rhoLen);
        double s = 0;
        for (int k = 0; k < rhoLen; k++) {
          double v = rho[rhoIdx[k]];
          s += v * v;
        }
        weight[r] = Math.max(s, 1e-12);
      }
      weightsFrom = m;
    }
  }
}
