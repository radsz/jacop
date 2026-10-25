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

import java.util.Arrays;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.jasat.cdcl.ExternalPropagator;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;

/**
 * Lazy clause generation with JaSAT: the constraints of a store propagate as an external propagator
 * of {@link CdclSolver}, whose conflict analysis learns from their explanations.
 *
 * <p>Every integer variable of the store gets the literals {@code [x >= v]} and {@code [x = v]} for
 * the values of its domain after root propagation, linked by clauses so that unit propagation keeps
 * them a domain. The atoms of the store's {@link AtomicTrail} are those literals; the store level
 * follows the solver's decision level. When the solver assigns literals they are applied to the
 * domains and the store propagates; every atom it records goes back to the solver with its
 * explanation as reason, and a failure becomes a conflict clause of the explanations.
 *
 * <p>The literals are created when the solver is built (not lazily yet), so this suits variables
 * with small domains.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class LcgSolver implements ExternalPropagator {

  private final Store store;
  private final CdclSolver sat = new CdclSolver();
  private final AtomicTrail trail;
  private final int baseLevel;
  private final boolean rootFailed;

  // per store variable index: the variables with literals, their root bounds and first literals
  private IntVar[] vars = new IntVar[0];
  private int[] lo = new int[0];
  private int[] hi = new int[0];
  private int[] geBase =
      new int[0]; // DIMACS variable of [x >= lo + 1]; [x >= v] is geBase + v - lo - 1
  private int[] eqBase = new int[0]; // DIMACS variable of [x = lo]; [x = v] is eqBase + v - lo

  // per DIMACS variable: its store variable index, kind (0 ge, 1 eq) and value
  private int[] litVar = new int[1];
  private byte[] litKind = new byte[1];
  private int[] litValue = new int[1];

  // SAT assignments not yet applied to the domains
  private int[] pending = new int[64];
  private int numPending;

  private int pushed; // trail entries below are true in the solver
  private boolean failed;
  private int[] pushedReason;
  private final EntryList reasonEntries = new EntryList();

  /** Statistics: atoms propagated to the solver, and conflicts found by the constraints. */
  public long atomsPropagated;

  /** Statistics: failures of the constraints turned into conflict clauses. */
  public long constraintConflicts;

  /**
   * Builds the solver for the constraints imposed in a store. The store is propagated first; its
   * domains then are the root facts.
   *
   * @param store the store with its variables and constraints
   */
  public LcgSolver(Store store) {
    this.store = store;
    rootFailed = !store.consistency();
    this.baseLevel = store.level; // consistency may raise the level after impositions
    if (!rootFailed) {
      for (int i = 0; i < store.size(); i++) {
        if (store.vars[i] instanceof IntVar x && !x.singleton()) {
          encode(x);
        }
      }
    }
    trail = new AtomicTrail(store);
    sat.connect(this);
  }

  private void encode(IntVar x) {
    int i = x.index();
    if (i >= vars.length) {
      int n = Math.max(i + 1, 2 * vars.length);
      vars = Arrays.copyOf(vars, n);
      lo = Arrays.copyOf(lo, n);
      hi = Arrays.copyOf(hi, n);
      geBase = Arrays.copyOf(geBase, n);
      eqBase = Arrays.copyOf(eqBase, n);
    }
    IntDomain d = x.dom();
    int min = d.min();
    int max = d.max();
    int width = max - min;
    vars[i] = x;
    lo[i] = min;
    hi[i] = max;
    geBase[i] = sat.newVariables(width + (width + 1));
    eqBase[i] = geBase[i] + width;
    int last = eqBase[i] + width;
    if (last >= litVar.length) {
      int n = Math.max(last + 1, 2 * litVar.length);
      litVar = Arrays.copyOf(litVar, n);
      litKind = Arrays.copyOf(litKind, n);
      litValue = Arrays.copyOf(litValue, n);
    }
    for (int v = min + 1; v <= max; v++) {
      int g = geBase[i] + v - min - 1;
      litVar[g] = i;
      litKind[g] = 0;
      litValue[g] = v;
      sat.observe(g);
      if (v > min + 1) {
        sat.addClause(-g, g - 1); // [x >= v] -> [x >= v - 1]
      }
    }
    for (int v = min; v <= max; v++) {
      int e = eqBase[i] + v - min;
      litVar[e] = i;
      litKind[e] = 1;
      litValue[e] = v;
      sat.observe(e);
      int ge = geLit(i, v); // [x >= v], 0 when always true
      int gt = geLit(i, v + 1); // [x >= v + 1], 0 when always false
      if (!d.contains(v)) {
        sat.addClause(-e);
      }
      if (v > min) {
        sat.addClause(-e, ge);
      }
      if (v < max) {
        sat.addClause(-e, -gt);
      }
      // [x >= v] and not [x >= v + 1] -> [x = v]
      if (v == min && v == max) {
        sat.addClause(e);
      } else if (v == min) {
        sat.addClause(e, gt);
      } else if (v == max) {
        sat.addClause(e, -ge);
      } else {
        sat.addClause(e, -ge, gt);
      }
    }
  }

  /** The literal [x >= v] for v in (lo, hi]; outside it the caller handles the constant. */
  private int geLit(int i, int v) {
    if (v <= lo[i] || v > hi[i]) {
      return 0;
    }
    return geBase[i] + v - lo[i] - 1;
  }

  /** The DIMACS literal that is true when a trail entry's atom holds. */
  private int atomLit(int entry) {
    IntVar x = trail.var(entry);
    int i = x.index();
    int v = trail.value(entry);
    return switch (trail.kind(entry)) {
      case AtomicTrail.GE -> geLit(i, v);
      case AtomicTrail.LE -> -geLit(i, v + 1);
      default -> -(eqBase[i] + v - lo[i]);
    };
  }

  /**
   * Returns the solver, for its settings and statistics.
   *
   * @return the CDCL solver
   */
  public CdclSolver sat() {
    return sat;
  }

  /**
   * Solves the store's constraints.
   *
   * @return {@link CdclSolver#SAT}, with every variable then fixed in the store until the next
   *     call, {@link CdclSolver#UNSAT} or {@link CdclSolver#UNKNOWN}
   */
  public int solve() {
    if (rootFailed) {
      return CdclSolver.UNSAT;
    }
    return sat.solve();
  }

  /**
   * Returns the value of a variable in the last solution.
   *
   * @param x a variable of the store
   * @return its value
   */
  public int value(IntVar x) {
    int i = x.index();
    if (i >= vars.length || vars[i] == null) {
      return x.value();
    }
    for (int v = lo[i]; v <= hi[i]; v++) {
      if (sat.modelValue(eqBase[i] + v - lo[i])) {
        return v;
      }
    }
    throw new IllegalStateException("no value for " + x);
  }

  // ------------------------------------------------------------------ the external propagator

  @Override
  public void notifyAssignment(int lit, boolean fixed) {
    if (numPending == pending.length) {
      pending = Arrays.copyOf(pending, 2 * numPending);
    }
    pending[numPending++] = lit;
  }

  @Override
  public void notifyNewDecisionLevel() {
    store.setLevel(store.level + 1);
  }

  @Override
  public void notifyBacktrack(int level) {
    while (store.level > baseLevel + level) {
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
    }
    numPending = 0;
    failed = false;
    pushed = Math.min(pushed, trail.size());
  }

  private void apply(int lit) {
    int var = Math.abs(lit);
    IntVar x = vars[litVar[var]];
    int v = litValue[var];
    store.currentConstraint = null;
    if (litKind[var] == 0) {
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
      while (pushed < trail.size()) {
        int e = pushed++;
        int lit = atomLit(e);
        if (sat.value(lit) > 0) {
          continue;
        }
        if (trail.reason(e) == null) {
          throw new IllegalStateException(
              "atom " + trail.atomString(e) + " has no reason and is not set");
        }
        reasonEntries.clear();
        trail.explain(e, reasonEntries);
        int[] clause = new int[reasonEntries.size() + 1];
        clause[0] = lit;
        for (int k = 0; k < reasonEntries.size(); k++) {
          clause[k + 1] = -atomLit(reasonEntries.get(k));
        }
        pushedReason = clause;
        atomsPropagated++;
        return lit;
      }
      if (numPending == 0) {
        return 0;
      }
      for (int k = 0; k < numPending; k++) {
        apply(pending[k]);
      }
      numPending = 0;
      if (!store.consistency()) {
        failed = true;
        constraintConflicts++;
        int[] clause = conflictClause(store.recentlyFailedConstraint);
        if (clause.length == 0) {
          throw new IllegalStateException("the constraints failed on the root domains");
        }
        pushedReason = clause;
        return clause[0];
      }
    }
  }

  @Override
  public int[] reason(int lit) {
    if (pushedReason == null || pushedReason[0] != lit) {
      throw new IllegalStateException("no reason for " + lit);
    }
    int[] r = pushedReason;
    pushedReason = null;
    return r;
  }

  /**
   * The clause of a failure: the negated atoms of the failed constraint's explanation, each atom
   * not yet in the solver replaced by its own explanation.
   */
  private int[] conflictClause(Constraint failedConstraint) {
    EntryList atoms = new EntryList();
    trail.explainFailure(failedConstraint, atoms);
    boolean[] seen = new boolean[trail.size()];
    EntryList out = new EntryList();
    EntryList stack = atoms;
    while (stack.size() > 0) {
      int e = stack.get(stack.size() - 1);
      stack.truncate(stack.size() - 1);
      if (seen[e]) {
        continue;
      }
      seen[e] = true;
      int lit = atomLit(e);
      if (sat.value(lit) > 0) {
        out.add(e);
      } else {
        trail.explain(e, stack);
      }
    }
    int[] clause = new int[out.size()];
    for (int k = 0; k < out.size(); k++) {
      clause[k] = -atomLit(out.get(k));
    }
    return clause;
  }

  @Override
  public boolean checkModel(int[] model) {
    return true;
  }
}
