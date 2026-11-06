/*
 * XorSystem.java
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.VarMap;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;

/**
 * A system of parity (XOR) constraints over 0/1 variables, {@code x[i][0] xor x[i][1] xor ... =
 * parity[i]} for every row i, propagated by Gauss-Jordan elimination over GF(2).
 *
 * <p>Posted one by one, parity constraints only propagate when all but one of their variables are
 * fixed, and the clauses of their encoding do no better. A linear combination of the rows can be
 * unit long before any row is, so the system as a whole propagates more: for example {@code a + b +
 * c = 1} and {@code b + c + d = 0} give {@code a + d = 1}. This constraint keeps the rows, bit
 * packed, in reduced row echelon form with respect to the unfixed variables: each row with an
 * unfixed variable has one of them as its pivot (basic variable) and no other row contains that
 * column. Then a row whose only unfixed variable is its pivot fixes the pivot, and a row with no
 * unfixed variable either holds or fails. This finds every value and every failure the system
 * implies by linear algebra over GF(2) (Gauss-Jordan elimination gives full propagation of a
 * conjunction of parity constraints).
 *
 * <p>The rows are changed only by adding one row to another, which gives an equivalent system, so
 * nothing is undone on backtracking: when the pivot of a row gets fixed, another unfixed variable
 * of the row becomes its pivot and is eliminated from the other rows, and a row without a pivot
 * gets one again once a variable of it is unfixed. This is the scheme of Han and Jiang, who keep
 * the matrix as the simplex method keeps its tableau, and of the Gauss-Jordan elimination of
 * CryptoMiniSat. A call checks only the rows that a pivot change touched or that hold a variable
 * fixed since the last call; the columns a call has seen are forgotten when their level is removed.
 *
 * <p>For lazy clause generation the reason of a value fixed by a row is the fixed values of the
 * other variables of that row, the combination of the original rows that gave it; the reason of a
 * failure is the values of a row with no unfixed variable and the wrong parity (the XOR reason
 * clauses of Han and Jiang, and of Laitinen, Junttila and Niemelä).
 *
 * <p>References:
 *
 * <ul>
 *   <li>Cheng-Shen Han and Jie-Hong Roland Jiang. When Boolean Satisfiability Meets Gaussian
 *       Elimination in a Simplex Way. In CAV 2012, LNCS 7358, pages 410-426, Springer, 2012. doi:
 *       10.1007/978-3-642-31424-7_31
 *   <li>Tero Laitinen, Tommi Junttila and Ilkka Niemelä. Classifying and Propagating Parity
 *       Constraints. In CP 2012, LNCS 7514, pages 357-372, Springer, 2012. Extended version:
 *       arXiv:1406.4698.
 *   <li>Mate Soos, Stephan Gocht and Kuldeep S. Meel. Tinted, Detached, and Lazy CNF-XOR Solving
 *       and Its Applications to Counting and Sampling. In CAV 2020, LNCS 12224, pages 463-484,
 *       Springer, 2020. doi: 10.1007/978-3-030-53288-8_22
 *   <li>Mate Soos, Karsten Nohl and Claude Castelluccia. Extending SAT Solvers to Cryptographic
 *       Problems. In SAT 2009, LNCS 5584, pages 244-257, Springer, 2009. doi:
 *       10.1007/978-3-642-02777-2_24
 * </ul>
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class XorSystem extends Constraint
    implements SatisfiedPresent, Stateful, Copyable<XorSystem>, Explainable {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** The variables of the system, each one column. */
  private final IntVar[] vars;

  // the rows as given, for copy and toString
  private final int[][] givenRows;
  private final int[] givenParities;

  private final Map<IntVar, Integer> column = new IdentityHashMap<>();

  private final int words;

  // the current rows, an equivalent system: bits per column and the parity
  private final long[][] rows;
  private final int[] parity;

  // the pivot column of each row, or -1, and the row of each pivot column, or -1
  private final int[] pivotOf;
  private final int[] rowOf;

  // fixed columns and columns fixed to 1, refreshed at each consistency call
  private final long[] fixed;
  private final long[] ones;

  // the fixed columns seen by a call, with the levels at which they were seen, so that a
  // backtrack forgets them; the columns forgotten since the last call; the columns fixed since the
  // last call and their words
  private final long[] seen;
  private final int[] seenColumn;
  private final int[] seenLevel;
  private int seenSize;
  private final long[] newlyUnfixed;
  private boolean firstCall = true;
  private final long[] newlyFixed;
  private final int[] newlyFixedWords;

  // rows changed by a pivot change and not checked since
  private final long[] dirty;

  // rows without a pivot that a pivot change gave unfixed variables, to get a pivot
  private final int[] pending;
  private final boolean[] isPending;
  private int pendingSize;

  // per column: the row that fixed it, as it was then, for its explanation
  private final long[][] reasonRow;

  // the row that failed, as it was then
  private final long[] failedRow;
  private boolean failedValid;

  /** Statistics: values fixed by the system. */
  public long propagations;

  /** Statistics: pivot changes. */
  public long pivotChanges;

  /** Statistics: failures found by the system. */
  public long failures;

  // calls per window of the switch-off rule, and failures per window below which it switches off
  static final int WINDOW = 10_000;
  static final int MIN_FAILURES = 10;

  // implied by other constraints, so it may switch itself off
  private boolean redundant;
  private boolean off;
  private int windowCalls;
  private long windowStart;

  /**
   * It constructs the system {@code xor(rows[i]) = parities[i]} for every i.
   *
   * @param rows the variables of each row; a variable listed twice in a row cancels out
   * @param parities the parity of each row, 0 or 1
   */
  public XorSystem(IntVar[][] rows, int[] parities) {

    checkInputForNullness("rows", rows);
    checkInputForNullness("parities", parities);
    if (rows.length != parities.length) {
      throw new IllegalArgumentException("XorSystem: rows and parities differ in length.");
    }

    numberId = idNumber.incrementAndGet();
    queueIndex = 1;

    int m = rows.length;
    List<IntVar> list = new ArrayList<>();
    givenRows = new int[m][];
    givenParities = new int[m];
    for (int i = 0; i < m; i++) {
      if (parities[i] != 0 && parities[i] != 1) {
        throw new IllegalArgumentException("XorSystem: parity " + parities[i] + " is not 0 or 1.");
      }
      givenParities[i] = parities[i];
      givenRows[i] = new int[rows[i].length];
      for (int j = 0; j < rows[i].length; j++) {
        IntVar x = rows[i][j];
        checkInputForNullness("rows", new Object[] {x});
        if (x.min() < 0 || x.max() > 1) {
          throw new IllegalArgumentException("XorSystem: variable " + x + " is not 0/1.");
        }
        Integer c = column.get(x);
        if (c == null) {
          c = list.size();
          column.put(x, c);
          list.add(x);
        }
        givenRows[i][j] = c;
      }
    }
    vars = list.toArray(new IntVar[0]);
    int n = vars.length;
    words = Math.max(1, (n + 63) >>> 6);

    this.rows = new long[m][words];
    parity = new int[m];
    for (int i = 0; i < m; i++) {
      for (int c : givenRows[i]) {
        this.rows[i][c >>> 6] ^= 1L << c;
      }
      parity[i] = givenParities[i];
    }
    pivotOf = new int[m];
    Arrays.fill(pivotOf, -1);
    rowOf = new int[n];
    Arrays.fill(rowOf, -1);
    fixed = new long[words];
    ones = new long[words];
    seen = new long[words];
    seenColumn = new int[n];
    seenLevel = new int[n];
    newlyFixed = new long[words];
    newlyUnfixed = new long[words];
    newlyFixedWords = new int[words];
    dirty = new long[(m + 63) >>> 6];
    pending = new int[m];
    isPending = new boolean[m];
    // the first call checks every row
    Arrays.fill(dirty, -1L);
    reasonRow = new long[n][];
    failedRow = new long[words];

    setScope(vars);
  }

  /**
   * It returns the number of rows of the system.
   *
   * @return the number of rows
   */
  public int numberOfRows() {
    return rows.length;
  }

  /**
   * It tells the system that other constraints of the model imply it, so it may stop propagating. A
   * redundant system switches itself off when it finds fewer than ten failures in ten thousand
   * calls: the other constraints then fix the same values a little later and the elimination is not
   * worth its cost. This follows the automatic disabling of the Gauss-Jordan matrices of
   * CryptoMiniSat (Soos, Gocht and Meel 2020).
   *
   * @param redundant true if other constraints imply the system
   */
  public void setRedundant(boolean redundant) {
    this.redundant = redundant;
  }

  /**
   * It tells whether a redundant system has switched itself off.
   *
   * @return true if the system no longer propagates
   */
  public boolean isOff() {
    return off;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.GROUND;
  }

  @Override
  public void consistency(final Store store) {
    if (off) {
      return;
    }
    if (redundant && ++windowCalls == WINDOW) {
      if (failures - windowStart < MIN_FAILURES) {
        off = true;
        return;
      }
      windowCalls = 0;
      windowStart = failures;
    }
    refreshFixed();
    int fixedWords = 0;
    boolean unfixed = firstCall;
    if (firstCall) {
      // every row gets a pivot
      Arrays.fill(newlyUnfixed, -1L);
      firstCall = false;
    }
    for (int j = 0; j < words; j++) {
      assert (seen[j] & ~fixed[j]) == 0 : "a backtrack forgets the columns it unfixes";
      long bits = fixed[j] & ~seen[j];
      newlyFixed[j] = bits;
      if (bits != 0) {
        newlyFixedWords[fixedWords++] = j;
        seen[j] |= bits;
        while (bits != 0) {
          see((j << 6) + Long.numberOfTrailingZeros(bits), store.level);
          bits &= bits - 1;
        }
      }
      unfixed |= newlyUnfixed[j] != 0;
    }
    repivotFixedPivots(fixedWords);
    if (unfixed) {
      pivotUnfixedRows();
      Arrays.fill(newlyUnfixed, 0L);
    }
    while (pendingSize > 0) {
      int i = pending[--pendingSize];
      isPending[i] = false;
      if (pivotOf[i] < 0) {
        pivot(i);
      }
    }
    check(store, fixedWords);
    assert atFixpoint() : "XorSystem: a row with at most one unfixed variable is left";
  }

  private void see(int c, int level) {
    seenColumn[seenSize] = c;
    seenLevel[seenSize++] = level;
  }

  @Override
  public void removeLevel(int level) {
    while (seenSize > 0 && seenLevel[seenSize - 1] >= level) {
      int c = seenColumn[--seenSize];
      seen[c >>> 6] &= ~(1L << c);
      newlyUnfixed[c >>> 6] |= 1L << c;
    }
  }

  private void refreshFixed() {
    Arrays.fill(fixed, 0L);
    Arrays.fill(ones, 0L);
    for (int c = 0; c < vars.length; c++) {
      IntVar x = vars[c];
      if (x.singleton()) {
        fixed[c >>> 6] |= 1L << c;
        if (x.min() == 1) {
          ones[c >>> 6] |= 1L << c;
        }
      }
    }
  }

  // a row whose pivot got fixed takes another unfixed variable of it as its pivot
  private void repivotFixedPivots(int fixedWords) {
    for (int t = 0; t < fixedWords; t++) {
      int j = newlyFixedWords[t];
      long bits = newlyFixed[j];
      while (bits != 0) {
        int p = (j << 6) + Long.numberOfTrailingZeros(bits);
        bits &= bits - 1;
        int i = rowOf[p];
        if (i >= 0) {
          rowOf[p] = -1;
          pivotOf[i] = -1;
          pivot(i);
        }
      }
    }
  }

  // a row without a pivot, all of whose variables were fixed, gets one when one is unfixed
  private void pivotUnfixedRows() {
    for (int i = 0; i < rows.length; i++) {
      if (pivotOf[i] < 0 && intersects(rows[i], newlyUnfixed)) {
        pivot(i);
      }
    }
  }

  private boolean intersects(long[] r, long[] mask) {
    for (int j = 0; j < words; j++) {
      if ((r[j] & mask[j]) != 0) {
        return true;
      }
    }
    return false;
  }

  // makes the first unfixed variable of row i, if any, its pivot and eliminates it from the other
  // rows; the rows changed are checked by the next check
  private void pivot(int i) {
    int c = firstUnfixed(rows[i]);
    if (c < 0) {
      return;
    }
    pivotChanges++;
    pivotOf[i] = c;
    rowOf[c] = i;
    dirty[i >>> 6] |= 1L << i;
    long[] r = rows[i];
    int w = c >>> 6;
    long bit = 1L << c;
    for (int k = 0; k < rows.length; k++) {
      if (k != i && (rows[k][w] & bit) != 0) {
        long[] rk = rows[k];
        for (int j = 0; j < words; j++) {
          rk[j] ^= r[j];
        }
        parity[k] ^= parity[i];
        if (pivotOf[k] < 0 && !isPending[k]) {
          isPending[k] = true;
          pending[pendingSize++] = k;
        }
        dirty[k >>> 6] |= 1L << k;
      }
    }
  }

  private int firstUnfixed(long[] r) {
    for (int j = 0; j < words; j++) {
      long u = r[j] & ~fixed[j];
      if (u != 0) {
        return (j << 6) + Long.numberOfTrailingZeros(u);
      }
    }
    return -1;
  }

  // checks the rows changed since the last call or holding a variable fixed since: fixes the pivot
  // of a row whose only unfixed variable it is and fails on a violated row
  private void check(Store store, int fixedWords) {
    for (int i = 0; i < rows.length; i++) {
      long[] r = rows[i];
      long flag = 1L << i;
      if ((dirty[i >>> 6] & flag) == 0 && !holdsNewlyFixed(r, fixedWords)) {
        continue;
      }
      dirty[i >>> 6] &= ~flag;
      int unfixed = 0;
      int sum = parity[i];
      for (int j = 0; j < words && unfixed < 2; j++) {
        unfixed += Long.bitCount(r[j] & ~fixed[j]);
        sum ^= Long.bitCount(r[j] & ones[j]) & 1;
      }
      if (unfixed >= 2) {
        continue;
      }
      if (unfixed == 0) {
        if (sum != 0) {
          System.arraycopy(r, 0, failedRow, 0, words);
          failedValid = true;
          failures++;
          throw Store.failException;
        }
        continue;
      }
      // the only unfixed variable is the pivot, which takes the remaining parity
      int p = pivotOf[i];
      assert p >= 0 && (r[p >>> 6] & (1L << p)) != 0 && (fixed[p >>> 6] & (1L << p)) == 0
          : "the unfixed variable of a row is its pivot";
      long[] reason = reasonRow[p];
      if (reason == null) {
        reason = new long[words];
        reasonRow[p] = reason;
      }
      System.arraycopy(r, 0, reason, 0, words);
      propagations++;
      IntVar x = vars[p];
      x.domain.inValue(store.level, x, sum);
      // the pivot is in no other row, so no other row changes; the row, now fixed, has no pivot
      // until one of its variables is unfixed
      long bit = 1L << p;
      fixed[p >>> 6] |= bit;
      seen[p >>> 6] |= bit;
      see(p, store.level);
      if (sum == 1) {
        ones[p >>> 6] |= bit;
      }
      pivotOf[i] = -1;
      rowOf[p] = -1;
    }
  }

  private boolean holdsNewlyFixed(long[] r, int fixedWords) {
    for (int t = 0; t < fixedWords; t++) {
      int j = newlyFixedWords[t];
      if ((r[j] & newlyFixed[j]) != 0) {
        return true;
      }
    }
    return false;
  }

  // every row with an unfixed variable has an unfixed pivot and at least two unfixed variables
  private boolean atFixpoint() {
    for (int i = 0; i < rows.length; i++) {
      int unfixed = 0;
      for (int j = 0; j < words; j++) {
        unfixed += Long.bitCount(rows[i][j] & ~fixed[j]);
      }
      int p = pivotOf[i];
      if (unfixed == 1 || unfixed > 1 && (p < 0 || (fixed[p >>> 6] & (1L << p)) != 0)) {
        return false;
      }
    }
    return true;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    IntVar x = trail.variable(entry);
    Integer c = column.get(x);
    if (c == null || reasonRow[c] == null) {
      return false;
    }
    return addValues(trail, reasonRow[c], c, entry, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (!failedValid) {
      return false;
    }
    failedValid = false;
    return addValues(trail, failedRow, -1, trail.size(), out);
  }

  // adds the atoms of the values of the row's variables other than skip before the position
  private boolean addValues(AtomicTrail trail, long[] r, int skip, int position, EntryList out) {
    for (int j = 0; j < words; j++) {
      long bits = r[j];
      while (bits != 0) {
        int c = (j << 6) + Long.numberOfTrailingZeros(bits);
        bits &= bits - 1;
        if (c == skip) {
          continue;
        }
        IntVar y = vars[c];
        if (trail.minBefore(y, position) == 1) {
          trail.addLowerBound(y, position, out);
        } else if (trail.maxBefore(y, position) == 0) {
          trail.addUpperBound(y, position, out);
        } else {
          // not fixed before the position: the row is not the reason
          return false;
        }
      }
    }
    return true;
  }

  @Override
  public boolean satisfied() {
    for (IntVar x : vars) {
      if (!x.singleton()) {
        return false;
      }
    }
    for (int i = 0; i < givenRows.length; i++) {
      int sum = givenParities[i];
      for (int c : givenRows[i]) {
        sum ^= vars[c].value();
      }
      if (sum != 0) {
        return false;
      }
    }
    return true;
  }

  @Override
  public XorSystem copy(VarMap map) {
    IntVar[][] copied = new IntVar[givenRows.length][];
    for (int i = 0; i < givenRows.length; i++) {
      copied[i] = new IntVar[givenRows[i].length];
      for (int j = 0; j < givenRows[i].length; j++) {
        copied[i][j] = map.get(vars[givenRows[i][j]]);
      }
    }
    return new XorSystem(copied, givenParities);
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder(id());
    result.append(" : XorSystem([");
    for (int i = 0; i < givenRows.length; i++) {
      if (i > 0) {
        result.append(", ");
      }
      result.append("xor(");
      for (int j = 0; j < givenRows[i].length; j++) {
        if (j > 0) {
          result.append(", ");
        }
        result.append(vars[givenRows[i][j]].id());
      }
      result.append(") = ").append(givenParities[i]);
    }
    result.append("])");
    return result.toString();
  }
}
