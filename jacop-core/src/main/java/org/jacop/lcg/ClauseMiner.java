/*
 * ClauseMiner.java
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

package org.jacop.lcg;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SimpleSelect;

/**
 * A research tool, not used by the solver: classifies learnt clauses by the constraints whose scope
 * covers their variables. A learnt clause over the variables of one constraint that this constraint
 * alone implies (with the root domains) is a nogood a domain-consistent propagator with exact
 * explanations would have produced or prevented; when only a search proves the implication, the
 * propagator is weaker than its definition on that clause. Clauses that no single constraint
 * implies are tried on pairs of constraints sharing a variable, which points at redundant
 * constraints or combined propagators. Counts go to a file per run.
 *
 * <p>Turned on by {@code -Djacop.lcg.mine=FILE}; {@code jacop.lcg.mine.budget} (default 0.5) caps
 * the share of the time spent mining, {@code jacop.lcg.mine.size} (default 24) the clause size.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class ClauseMiner {

  /** Literal kind [x &gt;= v]. */
  public static final int GE = 0;

  /** Literal kind [x = v]. */
  public static final int EQ = 1;

  private static final long NODE_LIMIT = Long.getLong("jacop.lcg.mine.nodes", 5_000);

  private static final int MAX_CANDIDATES = 12;

  private static final int MAX_PAIRS = 24;

  private static final int EXAMPLES = 6;

  private final AtomicTrail trail;
  private final String file;
  private final double budget =
      Double.parseDouble(System.getProperty("jacop.lcg.mine.budget", "0.5"));

  /** Largest clause mined. */
  public final int maxSize = Integer.getInteger("jacop.lcg.mine.size", 24);

  private final long start = System.nanoTime();
  private long spent;

  private final Map<IntVar, List<Constraint>> constraintsOf = new IdentityHashMap<>();

  // per key: counts (see header()) and examples
  private final Map<String, long[]> counts = new TreeMap<>();
  private final Map<String, List<String>> examples = new TreeMap<>();
  private final long[] totals = new long[8];

  private static final String[] HEADER = {
    "learnt",
    "mined",
    "skipped-budget",
    "skipped-size",
    "covered-one",
    "covered-pair",
    "none",
    "aux"
  };

  // counts per key: candidate constraints tested, implied by propagation, implied only by search,
  // not implied, undecided, clauses where this key was the first search-implied one
  private static final int TESTED = 0;
  private static final int PROPAGATION = 1;
  private static final int SEARCH = 2;
  private static final int NOT_IMPLIED = 3;
  private static final int UNDECIDED = 4;
  private static final int FIRST_GAP = 5;
  private static final int FAIL_ONLY = 6;
  private static final int LITERALS = 7;

  /**
   * Creates a miner over the constraints of a store at the root.
   *
   * @param trail the solver's trail, for root domains
   * @param store the store, whose constraints are read now
   * @param file the file the counts go to
   */
  public ClauseMiner(AtomicTrail trail, Store store, String file) {
    this.trail = trail;
    this.file = file;
    Set<String> excluded =
        Set.of(
            System.getProperty(
                    "jacop.lcg.mine.exclude", "LinearRelaxation,DifferenceCycles,LinearProgram")
                .split(","));
    for (Constraint c : store.getConstraints()) {
      if (excluded.contains(c.getClass().getSimpleName())) {
        continue;
      }
      for (Var v : c.arguments()) {
        if (v instanceof IntVar x) {
          constraintsOf.computeIfAbsent(x, k -> new ArrayList<>()).add(c);
        }
      }
    }
    Runtime.getRuntime().addShutdownHook(new Thread(this::write));
  }

  /** Counts a learnt clause with a literal that is not an atom, which is not mined. */
  public synchronized void auxiliary() {
    totals[0]++;
    totals[7]++;
  }

  /**
   * Mines a learnt clause. Literal k is [x[k] &gt;= value[k]] or [x[k] = value[k]] (by kind[k]),
   * negated unless positive[k]; literal 0 is the one the clause asserts.
   *
   * @param x the variables
   * @param kind the kinds
   * @param value the values
   * @param positive the signs
   */
  public synchronized void learnt(IntVar[] x, int[] kind, int[] value, boolean[] positive) {
    totals[0]++;
    long now = System.nanoTime();
    if (spent > budget * (now - start)) {
      totals[2]++;
      return;
    }
    if (x.length > maxSize) {
      totals[3]++;
      return;
    }
    totals[1]++;
    try {
      mine(x, kind, value, positive);
    } finally {
      spent += System.nanoTime() - now;
    }
  }

  private void mine(IntVar[] x, int[] kind, int[] value, boolean[] positive) {
    Set<IntVar> scope = java.util.Collections.newSetFromMap(new IdentityHashMap<>());
    for (IntVar v : x) {
      scope.add(v);
    }
    IntVar rarest = null;
    for (IntVar v : scope) {
      List<Constraint> cs = constraintsOf.get(v);
      if (cs == null) {
        totals[6]++;
        return;
      }
      if (rarest == null || cs.size() < constraintsOf.get(rarest).size()) {
        rarest = v;
      }
    }
    List<Constraint> single = new ArrayList<>();
    for (Constraint c : constraintsOf.get(rarest)) {
      if (c.arguments().containsAll(scope)) {
        single.add(c);
        if (single.size() == MAX_CANDIDATES) {
          break;
        }
      }
    }
    String gap = null;
    boolean implied = false;
    for (Constraint c : single) {
      String key = c.getClass().getSimpleName() + " |" + scope.size() + "v";
      int r = test(List.of(c), x, kind, value, positive);
      record(key, r, x.length);
      if (r == PROPAGATION) {
        implied = true;
      } else if ((r == SEARCH || r == FAIL_ONLY) && gap == null) {
        gap = key;
        example(key, c.toString(), x, kind, value, positive);
      }
    }
    if (!single.isEmpty()) {
      totals[4]++;
      if (gap != null && !implied) {
        counts.get(gap)[FIRST_GAP]++;
      }
      return;
    }
    // pairs of constraints sharing a variable that together cover the clause
    Set<Constraint> near = new LinkedHashSet<>();
    for (IntVar v : scope) {
      near.addAll(constraintsOf.get(v));
    }
    List<Constraint> list = new ArrayList<>(near);
    int pairs = 0;
    boolean covered = false;
    String pairGap = null;
    boolean pairImplied = false;
    for (int i = 0; i < list.size() && pairs < MAX_PAIRS; i++) {
      Set<Var> a = list.get(i).arguments();
      for (int j = i + 1; j < list.size() && pairs < MAX_PAIRS; j++) {
        Set<Var> b = list.get(j).arguments();
        if (!coversWith(scope, a, b) || !shares(a, b)) {
          continue;
        }
        pairs++;
        covered = true;
        String ka = list.get(i).getClass().getSimpleName();
        String kb = list.get(j).getClass().getSimpleName();
        String key = "pair " + (ka.compareTo(kb) <= 0 ? ka + "+" + kb : kb + "+" + ka);
        int r = test(List.of(list.get(i), list.get(j)), x, kind, value, positive);
        record(key, r, x.length);
        if (r == PROPAGATION) {
          pairImplied = true;
        } else if ((r == SEARCH || r == FAIL_ONLY) && pairGap == null) {
          pairGap = key;
          example(key, list.get(i) + "  &&  " + list.get(j), x, kind, value, positive);
        }
      }
    }
    if (covered) {
      totals[5]++;
      if (pairGap != null && !pairImplied) {
        counts.get(pairGap)[FIRST_GAP]++;
      }
    } else {
      totals[6]++;
    }
  }

  private static boolean coversWith(Set<IntVar> scope, Set<Var> a, Set<Var> b) {
    for (IntVar v : scope) {
      if (!a.contains(v) && !b.contains(v)) {
        return false;
      }
    }
    return true;
  }

  private static boolean shares(Set<Var> a, Set<Var> b) {
    Set<Var> small = a.size() < b.size() ? a : b;
    Set<Var> large = small == a ? b : a;
    for (Var v : small) {
      if (large.contains(v)) {
        return true;
      }
    }
    return false;
  }

  private void record(String key, int result, int literals) {
    long[] c = counts.computeIfAbsent(key, k -> new long[8]);
    c[TESTED]++;
    c[result]++;
    c[LITERALS] += literals;
  }

  private void example(
      String key, String constraint, IntVar[] x, int[] kind, int[] value, boolean[] positive) {
    List<String> list = examples.computeIfAbsent(key, k -> new ArrayList<>());
    if (list.size() >= EXAMPLES) {
      return;
    }
    StringBuilder s = new StringBuilder();
    for (int k = 0; k < x.length; k++) {
      s.append(k == 0 ? "" : " \\/ ").append(literal(x[k], kind[k], value[k], positive[k]));
    }
    String c = constraint.length() > 400 ? constraint.substring(0, 400) + "..." : constraint;
    s.append("   from ").append(c);
    list.add(s.toString());
  }

  private static String literal(IntVar x, int kind, int value, boolean positive) {
    if (kind == GE) {
      return positive ? x.id() + ">=" + value : x.id() + "<=" + (value - 1);
    }
    return x.id() + (positive ? "=" : "!=") + value;
  }

  /**
   * Whether the constraints imply the clause: copies over root domains with every literal but the
   * first false; propagation that fails or makes the first literal true implies it by propagation,
   * otherwise a search with the first literal false decides.
   */
  private int test(List<Constraint> cs, IntVar[] x, int[] kind, int[] value, boolean[] positive) {
    ScratchCopy copy = ScratchCopy.ofAll(trail, cs);
    if (copy == null) {
      return UNDECIDED;
    }
    Store s = copy.store;
    boolean last = false;
    try {
      for (Constraint c : cs) {
        if (!copy.imposeCopy(c)) {
          return UNDECIDED;
        }
      }
      for (int k = 1; k < x.length; k++) {
        falsify(copy, x[k], kind[k], value[k], positive[k]);
      }
      if (!s.consistency()) {
        return PROPAGATION;
      }
      IntVar y = copy.get(x[0]);
      if (holds(y, kind[0], value[0], positive[0])) {
        return PROPAGATION;
      }
      last = true;
      falsify(copy, x[0], kind[0], value[0], positive[0]);
      if (!s.consistency()) {
        return FAIL_ONLY;
      }
    } catch (FailException _) {
      return last ? FAIL_ONLY : PROPAGATION;
    }
    IntVar[] vars =
        copy.copies.values().stream()
            .filter(IntVar.class::isInstance)
            .map(IntVar.class::cast)
            .toArray(IntVar[]::new);
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setAssignSolution(false);
    search.setNodesOut(NODE_LIMIT);
    boolean found;
    try {
      found = search.labeling(s, new SimpleSelect<>(vars, null, new IndomainMin<>()));
    } catch (RuntimeException _) {
      return UNDECIDED;
    }
    if (found) {
      return NOT_IMPLIED;
    }
    return search.getNodes() > NODE_LIMIT ? UNDECIDED : SEARCH;
  }

  private static boolean holds(IntVar y, int kind, int value, boolean positive) {
    if (kind == GE) {
      return positive ? y.min() >= value : y.max() < value;
    }
    return positive ? y.singleton(value) : !y.domain.contains(value);
  }

  // makes the literal false on the copy of its variable
  private static void falsify(ScratchCopy copy, IntVar x, int kind, int value, boolean positive) {
    IntVar y = copy.get(x);
    int level = copy.store.level;
    if (kind == GE) {
      if (positive) {
        y.domain.inMax(level, y, value - 1);
      } else {
        y.domain.inMin(level, y, value);
      }
    } else if (positive) {
      if (y.domain.contains(value)) {
        y.domain.inComplement(level, y, value);
      }
    } else {
      y.domain.in(level, y, value, value);
    }
  }

  private synchronized void write() {
    try (PrintWriter out = new PrintWriter(new FileWriter(file, true))) {
      StringBuilder t = new StringBuilder("totals");
      for (int k = 0; k < totals.length; k++) {
        t.append(' ').append(HEADER[k]).append('=').append(totals[k]);
      }
      out.println(t.append(" spentMs=").append(spent / 1_000_000));
      for (Map.Entry<String, long[]> e : counts.entrySet()) {
        long[] c = e.getValue();
        out.println(
            "key\t"
                + e.getKey()
                + "\ttested="
                + c[TESTED]
                + "\tprop="
                + c[PROPAGATION]
                + "\tsearch="
                + c[SEARCH]
                + "\tnot="
                + c[NOT_IMPLIED]
                + "\tundecided="
                + c[UNDECIDED]
                + "\tfailOnly="
                + c[FAIL_ONLY]
                + "\tgap="
                + c[FIRST_GAP]
                + "\tliterals="
                + c[LITERALS]);
      }
      for (Map.Entry<String, List<String>> e : examples.entrySet()) {
        for (String s : e.getValue()) {
          out.println("example\t" + e.getKey() + "\t" + s);
        }
      }
    } catch (IOException e) {
      System.err.println("% clause miner: " + e);
    }
  }
}
