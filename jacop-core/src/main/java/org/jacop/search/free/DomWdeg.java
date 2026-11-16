/*
 * DomWdeg.java
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

package org.jacop.search.free;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.DomainChangeRecorder;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TrailedInts;
import org.jacop.core.Var;
import org.jacop.search.Indomain;
import org.jacop.search.SelectChoicePoint;

/**
 * The dom/wdeg variable heuristic (Boussemart et al. 2004): every constraint has a weight, one more
 * each time its propagation fails, and the selected variable has the smallest ratio of its domain
 * size to the sum of the weights of its constraints that have at least one other unfixed variable.
 * Weights are kept across restarts.
 *
 * <p>Two refinements of the weights are available through {@link Weighting}: wdeg^ca.cd (Wattez et
 * al. 2019), with a weight per constraint and variable, and CHS, conflict history search (Habet and
 * Terrioux 2021), where the weight of a constraint rewards recent failures and decays.
 *
 * <p>It is a {@link SearchMonitor}: add it to the {@link FreeSearch} it branches for, so that it
 * sees the failures. Ties go to the variable given first.
 *
 * <p>The selection is incremental: the unfixed search variables and the unfixed variables of the
 * constraints are kept in reversible sparse sets, and each constraint counts its unfixed variables,
 * so a selection visits only the unfixed variables and not the scopes of their constraints.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class DomWdeg implements SelectChoicePoint<IntVar>, SearchMonitor {

  /** How the weights are updated when a constraint fails. */
  public enum Weighting {
    /** The weight of the failed constraint grows by one (Boussemart et al. 2004). */
    WDEG,
    /**
     * Each unfixed variable of the failed constraint gets its own weight for that constraint, which
     * grows by one divided by the number of unfixed variables of the constraint and by the domain
     * size of the variable (wdeg^ca.cd, Wattez et al. 2019).
     */
    CACD,
    /**
     * The weight of the failed constraint moves towards a reward that is larger when the constraint
     * failed recently; weights decay between restarts (conflict history search, Habet and Terrioux
     * 2021).
     */
    CHS
  }

  private static final double CHS_ALPHA = 0.1d;
  private static final double CHS_ALPHA_MIN = 0.06d;
  private static final double CHS_ALPHA_STEP = 1e-6d;
  private static final double CHS_DECAY = 0.995d;
  private static final double CHS_DELTA = 1e-4d;

  private final IntVar[] vars;
  private final Indomain<IntVar> indomain;
  private final Weighting weighting;

  private final Map<Constraint, Integer> constraintIndex = new IdentityHashMap<>();
  private final double[] weights;
  private final int[][] varConstraints;

  /** The distinct variables of the constraints' scopes. */
  private final Var[] scopeVars;

  /** For each scope variable, the constraint of each of its occurrences in a scope. */
  private final int[][] occurrences;

  /** For each constraint, the number of occurrences of unfixed variables in its scope. */
  private final int[] unfixed;

  /**
   * Sparse sets of the search variables and of the scope variables: the elements not seen fixed
   * come first, and those seen fixed last, as many as counted in {@link #removed}.
   */
  private final int[] searchOrder;

  private final int[] scopeOrder;

  /**
   * The number of elements seen fixed in each sparse set, restored on backtracking; created at the
   * first selection. Zero, the initial value, holds at every level.
   */
  private TrailedInts removed;

  /** The size of the scope variable set that {@link #unfixed} counts. */
  private int countedScopeSize;

  /**
   * For wdeg^ca.cd, the weight of each constraint of a variable, in the order of varConstraints.
   */
  private final double[][] varWeights;

  /**
   * For wdeg and wdeg^ca.cd, the positions i of the search variables of each constraint, each
   * followed by the position j of the constraint in varConstraints[i].
   */
  private final int[][] scopePositions;

  /**
   * For wdeg, the weighted degree of each search variable, kept up to date as constraints get fewer
   * than two unfixed variables and as weights grow. The weights are whole numbers, so the sums are
   * exact and equal to those of {@link #weightedDegree(int)}.
   */
  private final double[] degrees;

  /**
   * For CHS, the number of failures so far and the failure count when each constraint last failed.
   */
  private long conflicts;

  private final long[] lastConflict;
  private double alpha = CHS_ALPHA;

  /** Added to the weight of every constraint; for CHS, so that the degree breaks ties at first. */
  private final double offset;

  private IntVar selected;

  /** For wdeg, the incremental selection, or null for the scan of every unfixed variable. */
  private Incremental incremental;

  /** The rebuilds of the incremental selection so far. */
  private int rebuilds;

  /** Whether the variables cannot be followed incrementally, so that the scan selects. */
  private boolean scanOnly;

  /** Whether each incremental selection is checked against one made from scratch. */
  private boolean checking = Boolean.getBoolean("org.jacop.search.free.domWdegCheck");

  /**
   * Checks each incremental selection of wdeg against one made from the domains and weights from
   * scratch, and throws {@link IllegalStateException} on a difference; for tests.
   *
   * @return this heuristic.
   */
  public DomWdeg checkSelections() {
    checking = true;
    return this;
  }

  /**
   * Tells whether the last selection was incremental (wdeg whose variables the store reports).
   *
   * @return true if it was
   */
  public boolean incremental() {
    return incremental != null;
  }

  /** Whether wdeg may select incrementally, which gives the same variable as the scan. */
  static final boolean INCREMENTAL = !Boolean.getBoolean("org.jacop.search.free.domWdegScan");

  private int flushEvery;
  private long restarts;

  /**
   * Creates the heuristic for the given variables. The constraints are those attached to the
   * variables when it is created.
   *
   * @param vars the variables to branch on.
   * @param indomain the value heuristic.
   */
  public DomWdeg(IntVar[] vars, Indomain<IntVar> indomain) {
    this(vars, indomain, Weighting.WDEG);
  }

  /**
   * Creates the heuristic for the given variables with the given weighting. The constraints are
   * those attached to the variables when it is created.
   *
   * @param vars the variables to branch on.
   * @param indomain the value heuristic.
   * @param weighting how the weights are updated on failures.
   */
  public DomWdeg(IntVar[] vars, Indomain<IntVar> indomain, Weighting weighting) {
    this.vars = vars.clone();
    this.indomain = indomain;
    this.weighting = weighting;
    List<Var[]> scopeList = new ArrayList<>();
    varConstraints = new int[vars.length][];
    for (int i = 0; i < vars.length; i++) {
      List<Constraint> cs = vars[i].constraintsWithWatches();
      int[] indices = new int[cs.size()];
      int n = 0;
      for (Constraint c : cs) {
        Integer k = constraintIndex.get(c);
        if (k == null) {
          k = scopeList.size();
          constraintIndex.put(c, k);
          scopeList.add(c.arguments().toArray(new Var[0]));
        }
        if (!contains(indices, n, k)) {
          indices[n++] = k;
        }
      }
      varConstraints[i] = Arrays.copyOf(indices, n);
    }
    int constraints = scopeList.size();
    weights = new double[constraints];
    Arrays.fill(weights, weighting == Weighting.CHS ? 0.0d : 1.0d);
    offset = weighting == Weighting.CHS ? CHS_DELTA : 0.0d;
    lastConflict = new long[constraints];
    unfixed = new int[constraints];
    Map<Var, Integer> scopeIndex = new IdentityHashMap<>();
    List<Var> scopeVarList = new ArrayList<>();
    int[] occurrenceCounts = new int[0];
    for (Var[] scope : scopeList) {
      for (Var v : scope) {
        Integer x = scopeIndex.get(v);
        if (x == null) {
          x = scopeVarList.size();
          scopeIndex.put(v, x);
          scopeVarList.add(v);
          if (x == occurrenceCounts.length) {
            occurrenceCounts = Arrays.copyOf(occurrenceCounts, 2 * x + 8);
          }
        }
        occurrenceCounts[x]++;
      }
    }
    scopeVars = scopeVarList.toArray(new Var[0]);
    occurrences = new int[scopeVars.length][];
    for (int x = 0; x < scopeVars.length; x++) {
      occurrences[x] = new int[occurrenceCounts[x]];
      occurrenceCounts[x] = 0;
    }
    for (int k = 0; k < constraints; k++) {
      Var[] scope = scopeList.get(k);
      unfixed[k] = scope.length;
      for (Var v : scope) {
        int x = scopeIndex.get(v);
        occurrences[x][occurrenceCounts[x]++] = k;
      }
    }
    countedScopeSize = scopeVars.length;
    scopeOrder = identity(scopeVars.length);
    searchOrder = identity(vars.length);
    if (weighting == Weighting.CACD) {
      varWeights = new double[vars.length][];
      for (int i = 0; i < vars.length; i++) {
        varWeights[i] = new double[varConstraints[i].length];
        Arrays.fill(varWeights[i], 1.0d);
      }
    } else {
      varWeights = null;
    }
    if (weighting != Weighting.CHS) {
      int[] counts = new int[constraints];
      for (int i = 0; i < vars.length; i++) {
        for (int k : varConstraints[i]) {
          counts[k]++;
        }
      }
      scopePositions = new int[constraints][];
      for (int k = 0; k < constraints; k++) {
        scopePositions[k] = new int[2 * counts[k]];
        counts[k] = 0;
      }
      for (int i = 0; i < vars.length; i++) {
        for (int j = 0; j < varConstraints[i].length; j++) {
          int k = varConstraints[i][j];
          scopePositions[k][counts[k]++] = i;
          scopePositions[k][counts[k]++] = j;
        }
      }
    } else {
      scopePositions = null;
    }
    degrees = weighting == Weighting.WDEG ? new double[vars.length] : null;
    computeDegrees();
  }

  /** Computes the cached weighted degrees from the weights and the unfixed counts. */
  private void computeDegrees() {
    if (degrees != null) {
      for (int i = 0; i < vars.length; i++) {
        degrees[i] = weightedDegree(i);
      }
    }
  }

  /** Adds a change of the weight of a constraint to the cached degrees of its search variables. */
  private void addToDegrees(int k, double delta) {
    int[] positions = scopePositions[k];
    for (int p = 0; p < positions.length; p += 2) {
      degrees[positions[p]] += delta;
    }
  }

  private static boolean contains(int[] a, int n, int k) {
    for (int i = 0; i < n; i++) {
      if (a[i] == k) {
        return true;
      }
    }
    return false;
  }

  private static int[] identity(int n) {
    int[] a = new int[n];
    for (int i = 0; i < n; i++) {
      a[i] = i;
    }
    return a;
  }

  /**
   * Brings the unfixed counts of the constraints up to date: the scope variables put back in the
   * set by backtracking count again, then the variables now fixed leave the set.
   */
  private void updateUnfixed() {
    int size = scopeVars.length - removed.get(1);
    for (int p = countedScopeSize; p < size; p++) {
      for (int k : occurrences[scopeOrder[p]]) {
        if (++unfixed[k] == 2 && degrees != null) {
          addToDegrees(k, weights[k]);
        }
      }
    }
    int p = 0;
    while (p < size) {
      int x = scopeOrder[p];
      if (scopeVars[x].singleton()) {
        size--;
        scopeOrder[p] = scopeOrder[size];
        scopeOrder[size] = x;
        for (int k : occurrences[x]) {
          if (--unfixed[k] == 1 && degrees != null) {
            addToDegrees(k, -weights[k]);
          }
        }
      } else {
        p++;
      }
    }
    countedScopeSize = size;
    removed.set(1, scopeVars.length - size);
  }

  /**
   * Returns the weighted degree of a variable: the sum of the weights of its constraints with at
   * least one other unfixed variable.
   *
   * @param i the position of the variable.
   * @return the weighted degree.
   */
  double weightedDegree(int i) {
    double w = 0.0d;
    int[] constraints = varConstraints[i];
    for (int j = 0; j < constraints.length; j++) {
      int k = constraints[j];
      if (unfixed[k] >= 2) {
        w += varWeights == null ? weights[k] + offset : varWeights[i][j];
      }
    }
    return w;
  }

  @Override
  public IntVar getChoiceVariable(int index) {
    selected = null;
    if (vars.length == 0) {
      return null;
    }
    if (removed == null) {
      removed = new TrailedInts(vars[0].getStore(), 4);
    }
    if (degrees != null && INCREMENTAL && !scanOnly) {
      Store store = vars[0].getStore();
      if (incremental != null && store.domainWatcher == incremental && !incremental.valid()) {
        // backtracking went above the node of the counts: changes made before the store reported
        // them to the heuristic were undone
        incremental.rebuild();
      }
      if (incremental == null || store.domainWatcher != incremental) {
        incremental = Incremental.of(this, store);
        scanOnly = incremental == null;
      }
      if (incremental != null) {
        selected = incremental.select();
        return selected;
      }
    }
    updateUnfixed();
    double best = Double.MAX_VALUE;
    int bestIndex = -1;
    int size = vars.length - removed.get(0);
    int p = 0;
    while (p < size) {
      int i = searchOrder[p];
      IntVar v = vars[i];
      if (v.singleton()) {
        size--;
        searchOrder[p] = searchOrder[size];
        searchOrder[size] = i;
        continue;
      }
      p++;
      double w = degrees != null ? degrees[i] : weightedDegree(i);
      // a variable without constraints left comes last, smaller domains first
      double score = w > 0.0d ? v.getSize() / w : Double.MAX_VALUE / 2 + v.getSize();
      // the set is not in the order of the variables, so ties go to the smaller position
      if (selected == null || score < best || (score == best && i < bestIndex)) {
        best = score;
        bestIndex = i;
        selected = v;
      }
    }
    removed.set(0, vars.length - size);
    return selected;
  }

  /**
   * The incremental selection of wdeg. The store reports each domain change of the variables to it
   * ({@link Store#domainWatcher}), and a reversible log of the changed variables tells which ones
   * backtracking restored; at each selection only the variables changed since the last one update
   * the unfixed counts of their constraints, the weighted degrees and a heap of the unfixed search
   * variables ordered by the ratio of dom/wdeg, ties to the smaller position. The selection is that
   * of the scan: on TelecomScheduling-B-10 (XCSP 2026, 5,000 search variables and 39,000 variables
   * in all) the scan of the unfixed variables at each decision took a third of the time.
   */
  private static final class Incremental implements DomainChangeRecorder {

    private final DomWdeg h;

    /** The scope variable and the search position of each variable of the store, -1 if none. */
    private final int[] scopeOf;

    private final int[] searchOf;

    /** The ids of the variables outside the array of the store: scope and search id. */
    private Map<Var, Integer> outside;

    private int[][] outsideIds;

    /** Whether some variable is outside the array of the store. */
    private boolean anyOutside;

    private Store store;

    /** For each scope variable, whether the unfixed counts take it as fixed. */
    private final boolean[] countedFixed;

    /** The store indices of the changed variables, as long as the length in slot 2 of removed. */
    private int[] log = new int[64];

    private int logEnd;

    private final int[] pendingScope;

    private int pendingScopeSize;

    private final boolean[] inPendingScope;

    private final int[] pendingSearch;

    private int pendingSearchSize;

    private final boolean[] inPendingSearch;

    /** A binary heap of the unfixed search variables, with their positions in it (-1 if out). */
    private final int[] heap;

    private int heapSize;

    private final int[] heapPos;

    private final double[] key;

    private Incremental(DomWdeg h, int[] scopeOf, int[] searchOf) {
      this.h = h;
      this.scopeOf = scopeOf;
      this.searchOf = searchOf;
      int ns = h.scopeVars.length;
      int nv = h.vars.length;
      countedFixed = new boolean[ns];
      pendingScope = new int[ns];
      inPendingScope = new boolean[ns];
      pendingSearch = new int[nv];
      inPendingSearch = new boolean[nv];
      heap = new int[nv];
      heapPos = new int[nv];
      key = new double[nv];
    }

    /**
     * Starts the incremental selection for a store, or returns null when it cannot follow the
     * variables: a search variable given twice, a scope variable that is not an integer variable,
     * or variables outside the store.
     */
    static Incremental of(DomWdeg h, Store store) {
      int n = store.size();
      int[] scopeOf = new int[n];
      int[] searchOf = new int[n];
      Arrays.fill(scopeOf, -1);
      Arrays.fill(searchOf, -1);
      // variables outside the array of the store, such as auxiliary Booleans, by identity
      Map<Var, Integer> outside = new IdentityHashMap<>();
      List<int[]> outsideIds = new ArrayList<>();
      for (int x = 0; x < h.scopeVars.length; x++) {
        Var v = h.scopeVars[x];
        if (!(v instanceof IntVar)) {
          return null;
        }
        if (inStore(v, store)) {
          scopeOf[v.index()] = x;
        } else {
          outsideIds(v, outside, outsideIds)[0] = x;
        }
      }
      for (int i = 0; i < h.vars.length; i++) {
        IntVar v = h.vars[i];
        if (inStore(v, store)) {
          if (searchOf[v.index()] >= 0) {
            return null; // given twice
          }
          searchOf[v.index()] = i;
        } else {
          int[] ids = outsideIds(v, outside, outsideIds);
          if (ids[1] >= 0) {
            return null;
          }
          ids[1] = i;
        }
      }
      Incremental inc = new Incremental(h, scopeOf, searchOf);
      inc.outside = outside;
      inc.outsideIds = outsideIds.toArray(new int[0][]);
      inc.anyOutside = !outside.isEmpty();
      inc.store = store;
      inc.rebuild();
      store.domainWatcher = inc;
      return inc;
    }

    private static boolean inStore(Var v, Store store) {
      int si = v.index();
      return si >= 0 && si < store.size() && store.vars[si] == v;
    }

    /** The scope and search ids of a variable outside the store's array, -1 until set. */
    private static int[] outsideIds(Var v, Map<Var, Integer> outside, List<int[]> outsideIds) {
      Integer k = outside.get(v);
      if (k == null) {
        k = outsideIds.size();
        outside.put(v, k);
        outsideIds.add(new int[] {-1, -1});
      }
      return outsideIds.get(k);
    }

    /**
     * The number of the last rebuild, also in slot 3 of removed while its node stays; counted over
     * all incremental selections of the heuristic, so that the number of a new one never equals one
     * that backtracking restores.
     */
    private int rebuildId;

    boolean valid() {
      return h.removed.get(3) == rebuildId;
    }

    /** Counts the unfixed variables of the constraints and fills the heap from the domains. */
    void rebuild() {
      rebuildId = ++h.rebuilds;
      h.removed.set(3, rebuildId);
      int[] scopeSizes = new int[h.unfixed.length];
      for (int x = 0; x < h.scopeVars.length; x++) {
        countedFixed[x] = h.scopeVars[x].singleton();
        if (!countedFixed[x]) {
          for (int k : h.occurrences[x]) {
            scopeSizes[k]++;
          }
        }
      }
      System.arraycopy(scopeSizes, 0, h.unfixed, 0, scopeSizes.length);
      h.computeDegrees();
      // the log starts empty at the node of the rebuild; backtracking above it restores an older
      // length, but then also an older rebuild number, and the next selection rebuilds
      logEnd = 0;
      h.removed.set(2, 0);
      pendingScopeSize = 0;
      Arrays.fill(inPendingScope, false);
      pendingSearchSize = 0;
      Arrays.fill(inPendingSearch, false);
      heapSize = 0;
      Arrays.fill(heapPos, -1);
      for (int i = 0; i < h.vars.length; i++) {
        if (!h.vars[i].singleton()) {
          key[i] = score(i);
          heapPos[i] = heapSize;
          heap[heapSize++] = i;
        }
      }
      for (int p = heapSize / 2 - 1; p >= 0; p--) {
        down(p);
      }
    }

    @Override
    public void domainChanged(IntVar x, int event) {
      int si = x.index();
      if (si >= 0 && si < scopeOf.length && store.vars[si] == x) {
        if (scopeOf[si] < 0 && searchOf[si] < 0) {
          return;
        }
      } else {
        if (!anyOutside) {
          return;
        }
        Integer k = outside.get(x);
        if (k == null) {
          return;
        }
        si = -2 - k;
      }
      syncLog();
      int len = logEnd;
      if (len == log.length) {
        log = Arrays.copyOf(log, 2 * len);
      }
      log[len] = si;
      logEnd = len + 1;
      h.removed.set(2, logEnd);
      mark(si);
    }

    /**
     * Marks the variables of the log entries that backtracking removed: their domains grew back.
     */
    private void syncLog() {
      int len = h.removed.get(2);
      for (int p = len; p < logEnd; p++) {
        mark(log[p]);
      }
      if (len < logEnd) {
        logEnd = len;
      }
    }

    private void mark(int si) {
      if (si < 0) {
        int[] ids = outsideIds[-2 - si];
        if (ids[0] >= 0 && !inPendingScope[ids[0]]) {
          inPendingScope[ids[0]] = true;
          pendingScope[pendingScopeSize++] = ids[0];
        }
        if (ids[1] >= 0) {
          markSearch(ids[1]);
        }
        return;
      }
      int x = scopeOf[si];
      if (x >= 0 && !inPendingScope[x]) {
        inPendingScope[x] = true;
        pendingScope[pendingScopeSize++] = x;
      }
      int i = searchOf[si];
      if (i >= 0) {
        markSearch(i);
      }
    }

    private void markSearch(int i) {
      if (!inPendingSearch[i]) {
        inPendingSearch[i] = true;
        pendingSearch[pendingSearchSize++] = i;
      }
    }

    /** Rescores the search variables of a constraint whose weight changed. */
    void rescoreScope(int k) {
      int[] positions = h.scopePositions[k];
      for (int p = 0; p < positions.length; p += 2) {
        markSearch(positions[p]);
      }
    }

    IntVar select() {
      syncLog();
      for (int q = 0; q < pendingScopeSize; q++) {
        int x = pendingScope[q];
        inPendingScope[x] = false;
        boolean fixed = h.scopeVars[x].singleton();
        if (fixed == countedFixed[x]) {
          continue;
        }
        countedFixed[x] = fixed;
        for (int k : h.occurrences[x]) {
          if (fixed) {
            if (--h.unfixed[k] == 1) {
              h.addToDegrees(k, -h.weights[k]);
              rescoreScope(k);
            }
          } else if (++h.unfixed[k] == 2) {
            h.addToDegrees(k, h.weights[k]);
            rescoreScope(k);
          }
        }
      }
      pendingScopeSize = 0;
      for (int q = 0; q < pendingSearchSize; q++) {
        int i = pendingSearch[q];
        inPendingSearch[i] = false;
        if (h.vars[i].singleton()) {
          remove(i);
        } else {
          update(i, score(i));
        }
      }
      pendingSearchSize = 0;
      IntVar chosen = heapSize == 0 ? null : h.vars[heap[0]];
      if (h.checking) {
        check(chosen);
      }
      return chosen;
    }

    /** Compares the selection with one made from scratch: the counts, degrees and the variable. */
    private void check(IntVar chosen) {
      int[] counts = new int[h.unfixed.length];
      for (int x = 0; x < h.scopeVars.length; x++) {
        if (!h.scopeVars[x].singleton()) {
          for (int k : h.occurrences[x]) {
            counts[k]++;
          }
        }
      }
      if (!Arrays.equals(counts, h.unfixed)) {
        int k = 0;
        while (counts[k] == h.unfixed[k]) {
          k++;
        }
        throw new IllegalStateException("dom/wdeg: wrong unfixed count of constraint " + k);
      }
      IntVar best = null;
      double bestScore = Double.MAX_VALUE;
      for (int i = 0; i < h.vars.length; i++) {
        double w = 0.0d;
        for (int k : h.varConstraints[i]) {
          if (counts[k] >= 2) {
            w += h.weights[k];
          }
        }
        if (w != h.degrees[i]) {
          throw new IllegalStateException("dom/wdeg: wrong degree of " + h.vars[i]);
        }
        IntVar v = h.vars[i];
        if (!v.singleton()) {
          double score = w > 0.0d ? v.getSize() / w : Double.MAX_VALUE / 2 + v.getSize();
          if (best == null || score < bestScore) {
            best = v;
            bestScore = score;
          }
        }
      }
      if (best != chosen) {
        throw new IllegalStateException("dom/wdeg: selected " + chosen + " instead of " + best);
      }
    }

    private double score(int i) {
      double w = h.degrees[i];
      int size = h.vars[i].getSize();
      // a variable without constraints left comes last, smaller domains first
      return w > 0.0d ? size / w : Double.MAX_VALUE / 2 + size;
    }

    private boolean less(int a, int b) {
      return key[a] < key[b] || (key[a] == key[b] && a < b);
    }

    private void update(int i, double k) {
      int p = heapPos[i];
      key[i] = k;
      if (p < 0) {
        p = heapSize++;
        heap[p] = i;
        heapPos[i] = p;
      }
      up(p);
      down(heapPos[i]);
    }

    private void remove(int i) {
      int p = heapPos[i];
      if (p < 0) {
        return;
      }
      int last = heap[--heapSize];
      heapPos[i] = -1;
      if (p < heapSize) {
        heap[p] = last;
        heapPos[last] = p;
        up(p);
        down(heapPos[last]);
      }
    }

    private void up(int p) {
      int i = heap[p];
      while (p > 0) {
        int parent = (p - 1) >> 1;
        int j = heap[parent];
        if (!less(i, j)) {
          break;
        }
        heap[p] = j;
        heapPos[j] = p;
        p = parent;
      }
      heap[p] = i;
      heapPos[i] = p;
    }

    private void down(int p) {
      int i = heap[p];
      while (true) {
        int c = 2 * p + 1;
        if (c >= heapSize) {
          break;
        }
        if (c + 1 < heapSize && less(heap[c + 1], heap[c])) {
          c++;
        }
        int j = heap[c];
        if (!less(j, i)) {
          break;
        }
        heap[p] = j;
        heapPos[j] = p;
        p = c;
      }
      heap[p] = i;
      heapPos[i] = p;
    }
  }

  @Override
  public int getChoiceValue() {
    return indomain.indomain(selected);
  }

  @Override
  public PrimitiveConstraint getChoiceConstraint(int index) {
    return null;
  }

  @Override
  public Map<IntVar, Integer> getVariablesMapping() {
    Map<IntVar, Integer> mapping = new IdentityHashMap<>();
    for (int i = 0; i < vars.length; i++) {
      mapping.putIfAbsent(vars[i], i);
    }
    return mapping;
  }

  @Override
  public int getIndex() {
    return 0;
  }

  @Override
  public void onFailure(Constraint failed, Var decision) {
    Integer k = failed == null ? null : constraintIndex.get(failed);
    if (k != null) {
      switch (weighting) {
        case WDEG -> {
          weights[k] += 1.0d;
          if (unfixed[k] >= 2) {
            addToDegrees(k, 1.0d);
            if (incremental != null) {
              incremental.rescoreScope(k);
            }
          }
        }
        case CACD -> increaseVariableWeights(k);
        case CHS -> {
          double reward = 1.0d / (conflicts - lastConflict[k] + 1);
          weights[k] = (1.0d - alpha) * weights[k] + alpha * reward;
          lastConflict[k] = conflicts;
        }
      }
    }
    conflicts++;
    if (alpha > CHS_ALPHA_MIN) {
      alpha -= CHS_ALPHA_STEP;
    }
  }

  private void increaseVariableWeights(int k) {
    int[] positions = scopePositions[k];
    int localUnfixed = 0;
    for (int p = 0; p < positions.length; p += 2) {
      if (!vars[positions[p]].singleton()) {
        localUnfixed++;
      }
    }
    for (int p = 0; p < positions.length; p += 2) {
      IntVar v = vars[positions[p]];
      if (!v.singleton()) {
        // the domain may be empty in the failed state
        varWeights[positions[p]][positions[p + 1]] +=
            1.0d / ((double) localUnfixed * Math.max(1, v.getSize()));
      }
    }
  }

  /**
   * Forgets the weights every given number of restarts, as Choco does (every 32 restarts by default
   * there), so the heuristic follows the part of the search the recent runs are in.
   *
   * @param restarts the number of restarts between two flushes; 0 (the default) never flushes.
   * @return this heuristic.
   */
  public DomWdeg flushEvery(int restarts) {
    this.flushEvery = restarts;
    return this;
  }

  @Override
  public void onRestart(FreeSearch search) {
    restarts++;
    if (flushEvery > 0 && restarts % flushEvery == 0) {
      Arrays.fill(weights, weighting == Weighting.CHS ? 0.0d : 1.0d);
      if (varWeights != null) {
        for (double[] w : varWeights) {
          Arrays.fill(w, 1.0d);
        }
      }
      computeDegrees();
      incremental = null;
      return;
    }
    if (weighting == Weighting.CHS) {
      alpha = CHS_ALPHA;
      for (int k = 0; k < weights.length; k++) {
        weights[k] *= Math.pow(CHS_DECAY, (double) conflicts - lastConflict[k]);
      }
    }
  }

  @Override
  public String toString() {
    return "DomWdeg(" + vars.length + " variables, " + weighting + ", " + indomain + ")";
  }
}
