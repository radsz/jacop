/*
 * Sweeper.java
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
 * preservation of specified reasonable legal notices and author attributions
 * in the material of this work and in any modifications made to it.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.cdcl;

import java.util.Arrays;

/**
 * SAT sweeping on the irredundant clauses at level 0, as in Kissat 4 ({@code sweep.c}): for each
 * scheduled variable the clauses around it, up to a small depth and size (its environment), are
 * copied into a small {@link CdclSolver}. The models of that sub-solver give candidate backbone
 * literals (true in every model found) and candidate equivalent literals (equal in every model
 * found); flipping single literals in a model refutes candidates cheaply, and each candidate left
 * is checked by solving the environment under the negated assumption. A refuted assumption is an
 * implied unit or binary clause of the environment, hence of the formula.
 *
 * <p>References: A. Biere, K. Fazekas, M. Fleury, N. Froleyks, "Clausal Congruence Closure", SAT
 * 2024, and A. Biere, M. Fleury, N. Froleyks, M. J. H. Heule, "The Kissat SAT solver entering the
 * SAT Competition 2023" (sweeping with the kitten sub-solver); the idea of SAT sweeping goes back
 * to A. Kuehlmann, "Dynamic Transition Relation Simplification for Bounded Property Checking",
 * ICCAD 2004, and A. Mishchenko, S. Chatterjee, R. Jiang, R. K. Brayton, "FRAIGs: A Unifying
 * Representation for Logic Synthesis and Verification", ERL Technical Report 2005.
 *
 * <p>DRAT: the sub-solver writes its learnt clauses to the main proof (renamed to the main
 * variables). They are reverse unit propagation (RUP) consequences of the environment, which is a
 * subset of the main clauses, so every unit and binary found is RUP after them. They are deleted
 * from the proof once the environment is done.
 *
 * <p>Literals are internal ({@code 2 * var + sign}), as in {@link CdclSolver} and {@link
 * Eliminator}.
 */
final class Sweeper {

  // the environment of one variable: depth, variables and clauses, as in Kissat's defaults
  private final int depthLimit;
  private final int varsLimit;
  private final int clausesLimit;

  // conflicts per sub-solver call; the sub-solver's propagations count against the budget
  private static final int CONFLICT_LIMIT = 1000;

  private final int numVars;
  private int[][] clauses;
  private int numClauses;
  private final boolean[] frozen;
  private final ProofOutput proof;

  // occurrence lists: clause indices per literal
  private final int[][] occ;
  private final int[] occSize;

  // root values found here (units) and representatives of the equivalences found
  private final byte[] value;
  private final int[] repr;

  // per environment: local index of a variable (+1), clause stamps
  private final int[] local;
  private int[] clauseStamp;
  private int stamp;

  private final long budget;
  private long work;

  // results: units, substituted variables with their extension stack (as Eliminator's)
  private int[] units = new int[16];
  private int numUnits;
  private final boolean[] substituted;
  private int numSubstituted;
  private int[] stack = new int[16];
  private int stackSize;
  private boolean unsat;

  // representatives to sweep again next, after an equivalence
  private int[] again = new int[16];
  private int numAgain;

  // statistics
  int swept;
  int solves;
  int equivalences;

  /**
   * Creates a sweeper over clauses without assigned literals.
   *
   * @param numVars the number of variables
   * @param clauses the irredundant clauses, internal literals
   * @param n how many of them
   * @param frozen the variables that must stay (they only represent others)
   * @param proof the proof, or null
   * @param budget the sub-solver propagations allowed in total
   * @param rounds the completed sweeping rounds so far, which widen the environments (as Kissat)
   */
  Sweeper(
      int numVars,
      int[][] clauses,
      int n,
      boolean[] frozen,
      ProofOutput proof,
      long budget,
      int rounds) {
    this.numVars = numVars;
    this.clauses = Arrays.copyOf(clauses, Math.max(16, n + n / 8));
    this.numClauses = n;
    this.frozen = frozen;
    this.proof = proof;
    this.substituted = new boolean[numVars];
    this.budget = budget;
    int widen = Math.min(rounds, 5);
    this.depthLimit = Math.min(2 + rounds, 3);
    this.varsLimit = Math.min(256 << widen, 8192);
    this.clausesLimit = Math.min(1024 << widen, 32768);
    occ = new int[2 * numVars][];
    occSize = new int[2 * numVars];
    for (int i = 0; i < n; i++) {
      for (int l : clauses[i]) {
        addOcc(l, i);
      }
    }
    value = new byte[2 * numVars];
    repr = new int[2 * numVars];
    for (int l = 0; l < 2 * numVars; l++) {
      repr[l] = l;
    }
    local = new int[numVars];
    clauseStamp = new int[this.clauses.length];
  }

  private void addOcc(int l, int i) {
    if (occ[l] == null) {
      occ[l] = new int[4];
    } else if (occSize[l] == occ[l].length) {
      occ[l] = Arrays.copyOf(occ[l], 2 * occSize[l]);
    }
    occ[l][occSize[l]++] = i;
  }

  /**
   * Sweeps the variables in the given order, each representative of a new equivalence again right
   * after the variable that found it, until the budget is used up.
   *
   * @param order the variables to sweep
   * @param n how many
   * @param done set for each variable of order swept
   * @return how many variables of order were swept
   */
  int run(int[] order, int n, boolean[] done) {
    int i = 0;
    while (!exhausted()) {
      int v;
      if (numAgain > 0) {
        v = again[--numAgain];
      } else if (i < n) {
        v = order[i++];
        done[v] = true;
      } else {
        break;
      }
      sweep(v);
    }
    return i;
  }

  /**
   * The clauses after sweeping: units removed, equivalent literals substituted.
   *
   * @return the clauses
   */
  int[][] clauses() {
    int k = 0;
    for (int i = 0; i < numClauses; i++) {
      if (clauses[i] != null) {
        k++;
      }
    }
    int[][] out = new int[k][];
    k = 0;
    for (int i = 0; i < numClauses; i++) {
      if (clauses[i] != null) {
        out[k++] = clauses[i];
      }
    }
    return out;
  }

  /**
   * The variables replaced by an equivalent literal; they occur in no clause any more.
   *
   * @return true for each substituted variable
   */
  boolean[] substituted() {
    return substituted;
  }

  /**
   * The number of substituted variables.
   *
   * @return the number of variables replaced by an equivalent literal
   */
  int numSubstituted() {
    return numSubstituted;
  }

  /**
   * The extension stack of the substituted variables, in the format of {@link Eliminator#stack}.
   *
   * @return the stack
   */
  int[] stack() {
    return Arrays.copyOf(stack, stackSize);
  }

  /**
   * Returns whether a variable is worth sweeping: it occurs in both signs, not too often.
   *
   * @param v a variable
   * @return its number of occurrences, or -1 when it is not a candidate
   */
  int candidate(int v) {
    int pos = occSize[2 * v];
    int neg = occSize[2 * v + 1];
    if (pos == 0 || neg == 0 || pos > clausesLimit || neg > clausesLimit) {
      return -1;
    }
    return pos + neg;
  }

  /**
   * Returns whether the budget is used up.
   *
   * @return true when no more variables should be swept
   */
  boolean exhausted() {
    return work >= budget || unsat;
  }

  /**
   * Returns whether the formula was found unsatisfiable.
   *
   * @return true when an environment had no model
   */
  boolean unsat() {
    return unsat;
  }

  /**
   * The units found, internal literals.
   *
   * @return the units
   */
  int[] units() {
    return Arrays.copyOf(units, numUnits);
  }

  private int find(int l) {
    while (repr[l] != l) {
      repr[l] = repr[repr[l]];
      l = repr[l];
    }
    return l;
  }

  private boolean active(int v) {
    return value[2 * v] == 0 && find(2 * v) == 2 * v;
  }

  // ------------------------------------------------------------------- one environment

  // the environment: global variables by local index, clauses in local literals
  private int[] envVars = new int[64];
  private int numEnvVars;
  private int[][] envClauses = new int[64][];
  private int numEnvClauses;
  private int envLiterals;

  // the current model of the environment (local literal values) and flip support
  private boolean[] model;
  private int[][] envOcc;
  private int[] envOccSize;
  private int[] trueCount;

  private CdclSolver sub;
  private ProofForward forward;

  /**
   * Sweeps one variable: builds its environment, solves it and refines the backbone and equivalence
   * candidates.
   *
   * @param v the variable
   */
  void sweep(int v) {
    if (!active(v) || unsat) {
      return;
    }
    swept++;
    stamp++;
    numEnvVars = 0;
    numEnvClauses = 0;
    envLiterals = 0;
    addVar(v);
    int expand = 0;
    int next = 1;
    int depth = 1;
    boolean limit = false;
    while (!limit) {
      if (numEnvClauses >= clausesLimit) {
        break;
      }
      if (expand == next) {
        if (depth >= depthLimit) {
          break;
        }
        next = numEnvVars;
        if (expand == next) {
          break;
        }
        depth++;
      }
      int w = envVars[expand];
      for (int sign = 0; sign < 2 && !limit; sign++) {
        int lit = 2 * w + sign;
        for (int k = 0; k < occSize[lit] && !limit; k++) {
          addClause(occ[lit][k]);
          limit = numEnvVars >= varsLimit || numEnvClauses >= clausesLimit;
        }
      }
      expand++;
    }
    try {
      solveEnvironment();
    } finally {
      for (int i = 0; i < numEnvVars; i++) {
        local[envVars[i]] = 0;
      }
      if (forward != null) {
        forward.deleteAll();
        for (int i = 0; i < numDeferred; i++) {
          proof.delete(deferred[i], 0, deferred[i].length);
          deferred[i] = null;
        }
        numDeferred = 0;
      }
      sub = null;
      forward = null;
    }
  }

  private void addVar(int v) {
    if (local[v] != 0) {
      return;
    }
    if (numEnvVars == envVars.length) {
      envVars = Arrays.copyOf(envVars, 2 * numEnvVars);
    }
    envVars[numEnvVars++] = v;
    local[v] = numEnvVars;
  }

  private void addClause(int ci) {
    if (clauseStamp[ci] == stamp) {
      return;
    }
    clauseStamp[ci] = stamp;
    int[] c = clauses[ci];
    if (c == null) {
      return;
    }
    int k = 0;
    for (int l : c) {
      if (value[l] > 0) {
        return;
      }
    }
    int[] d = new int[c.length];
    for (int l : c) {
      if (value[l] == 0) {
        d[k++] = l;
      }
    }
    for (int i = 0; i < k; i++) {
      addVar(d[i] >> 1);
      d[i] = 2 * (local[d[i] >> 1] - 1) + (d[i] & 1);
    }
    pushEnvClause(k == d.length ? d : Arrays.copyOf(d, k));
    envLiterals += k;
    work += c.length;
  }

  private void pushEnvClause(int[] c) {
    if (numEnvClauses == envClauses.length) {
      envClauses = Arrays.copyOf(envClauses, 2 * numEnvClauses);
    }
    envClauses[numEnvClauses++] = c;
  }

  private int toGlobal(int localLit) {
    return 2 * envVars[localLit >> 1] + (localLit & 1);
  }

  private void solveEnvironment() {
    forward = proof == null ? null : new ProofForward();
    trueCount = null;
    envOcc = null;
    envOccSize = null;
    sub = new CdclSolver();
    sub.setElimination(false);
    sub.setWalk(false);
    sub.setVivification(false);
    if (forward != null) {
      sub.setProof(forward);
    }
    sub.ensureVars(numEnvVars);
    int[] dimacs = new int[16];
    for (int i = 0; i < numEnvClauses; i++) {
      int[] c = envClauses[i];
      if (c.length == 0) {
        found(new int[0]);
        return;
      }
      if (dimacs.length < c.length) {
        dimacs = new int[2 * c.length];
      }
      for (int k = 0; k < c.length; k++) {
        dimacs[k] = CdclSolver.toDimacs(c[k]);
      }
      if (!sub.addClause(dimacs, c.length)) {
        found(new int[0]);
        return;
      }
    }
    int r = solve();
    if (r == CdclSolver.UNSAT) {
      found(new int[0]);
      return;
    }
    if (r != CdclSolver.SAT) {
      return;
    }
    model = new boolean[2 * numEnvVars];
    readModel();
    buildFlipSupport();
    int[] backbone = new int[numEnvVars];
    int nb = 0;
    int[] partition = new int[2 * numEnvVars + 2];
    int np = 0;
    for (int i = 0; i < numEnvVars; i++) {
      if (!active(envVars[i])) {
        continue;
      }
      int lit = model[2 * i] ? 2 * i : 2 * i + 1;
      backbone[nb++] = lit;
      partition[np++] = lit;
    }
    partition[np++] = -1;
    // backbone: each candidate is true in every model found so far
    while (nb > 0 && !exhausted()) {
      nb = flipBackbone(backbone, nb);
      if (nb == 0) {
        break;
      }
      int lit = backbone[--nb];
      if (!active(envVars[lit >> 1]) || !model[lit]) {
        continue;
      }
      if (flip(lit)) {
        continue;
      }
      r = solve(lit ^ 1);
      if (r == CdclSolver.SAT) {
        readModel();
        nb = refineBackbone(backbone, nb);
        np = refinePartition(partition, np);
      } else if (r == CdclSolver.UNSAT) {
        int g = toGlobal(lit);
        found(new int[] {g});
        if (unsat) {
          return;
        }
        addEnvFact(new int[] {lit});
      }
    }
    // equivalences: the literals of a class are equal in every model found so far
    np = refinePartition(partition, np);
    while (np > 2 && !exhausted()) {
      np = flipPartition(partition, np);
      if (np <= 2) {
        break;
      }
      // the last class ends at np - 1, its last two literals are tried
      int lit = partition[np - 3];
      int other = partition[np - 2];
      boolean third = np > 3 && partition[np - 4] >= 0;
      if (!active(envVars[lit >> 1]) || !active(envVars[other >> 1])) {
        np = dropPair(partition, np, lit, active(envVars[lit >> 1]) ? other : lit, third);
        continue;
      }
      int proved = equivalent(lit, other);
      if (proved == -1) {
        np = refinePartition(partition, np); // a model told them apart
        continue;
      }
      if (proved == -2) {
        np = dropPair(partition, np, lit, lit, third); // the limit hit
        continue;
      }
      // other is now represented by lit (or lit by other): drop the represented one
      np = dropPair(partition, np, lit, proved, third);
    }
  }

  /** Removes {@code gone} from the last class of the partition (lit and other are its last two). */
  private static int dropPair(int[] partition, int np, int lit, int gone, boolean third) {
    if (!third) {
      return np - 3; // the class had two literals: it is gone
    }
    if (gone == lit) {
      partition[np - 3] = partition[np - 2];
    }
    partition[np - 2] = -1;
    return np - 1;
  }

  /**
   * Checks lit = other in the environment.
   *
   * @return the literal of the pair that is now represented by the other; -1 when a model refuted
   *     it (the partition is refined) and -2 when a solve hit its limit
   */
  private int equivalent(int lit, int other) {
    int r = solve(lit ^ 1, other);
    if (r == CdclSolver.SAT) {
      readModel();
      return -1;
    }
    if (r != CdclSolver.UNSAT) {
      return -2;
    }
    int[] first = {toGlobal(lit), toGlobal(other ^ 1)};
    if (proof != null) {
      proof.add(first, 0, 2);
    }
    // the first implication helps the second call too
    sub.addClause(CdclSolver.toDimacs(lit), CdclSolver.toDimacs(other ^ 1));
    r = solve(lit, other ^ 1);
    if (r == CdclSolver.SAT) {
      readModel();
      return -1;
    }
    if (r != CdclSolver.UNSAT) {
      return -2;
    }
    int[] second = {toGlobal(lit ^ 1), toGlobal(other)};
    if (proof != null) {
      proof.add(second, 0, 2);
    }
    sub.addClause(CdclSolver.toDimacs(lit ^ 1), CdclSolver.toDimacs(other));
    addEnvFact(new int[] {lit, other ^ 1});
    addEnvFact(new int[] {lit ^ 1, other});
    equivalences++;
    // first[0] = lit, second[1] = other, global literals
    int a = first[0];
    int b = second[1];
    int va = a >> 1;
    int vb = b >> 1;
    // the representative: a frozen variable, else the smaller one, as in Kissat
    boolean keepA = frozen[va] || !frozen[vb] && va < vb;
    if (frozen[va] && frozen[vb]) {
      // neither may go: the equivalence stays as two clauses
      addWorkingClause(new int[] {first[0], first[1]});
      addWorkingClause(new int[] {second[0], second[1]});
      return lit;
    }
    int gone = keepA ? b : a;
    int kept = keepA ? a : b;
    repr[gone] = kept;
    repr[gone ^ 1] = kept ^ 1;
    substitute(gone, kept);
    if (proof != null) {
      deleteLater(first);
      deleteLater(second);
    }
    if (numAgain == again.length) {
      again = Arrays.copyOf(again, 2 * numAgain);
    }
    again[numAgain++] = kept >> 1;
    return keepA ? other : lit;
  }

  private void addWorkingClause(int[] c) {
    if (numClauses == clauses.length) {
      clauses = Arrays.copyOf(clauses, 2 * numClauses);
    }
    clauses[numClauses] = c;
    for (int l : c) {
      addOcc(l, numClauses);
    }
    numClauses++;
    if (clauseStamp.length < clauses.length) {
      clauseStamp = Arrays.copyOf(clauseStamp, clauses.length);
    }
  }

  /**
   * Replaces the literal {@code gone} by {@code kept} (and their negations) in every clause; the
   * variable of gone goes on the extension stack with the two binary clauses of the equivalence.
   */
  private void substitute(int gone, int kept) {
    int v = gone >> 1;
    substituted[v] = true;
    numSubstituted++;
    pushStack(gone, kept ^ 1);
    pushStack(gone ^ 1, kept);
    for (int sign = 0; sign < 2 && !unsat; sign++) {
      int from = gone ^ sign;
      int to = kept ^ sign;
      int[] os = occ[from];
      int n = occSize[from];
      occ[from] = null;
      occSize[from] = 0;
      for (int k = 0; k < n && !unsat; k++) {
        int ci = os[k];
        int[] c = clauses[ci];
        if (c == null || !contains(c, from)) {
          continue;
        }
        int[] d = new int[c.length];
        int m = 0;
        boolean tautology = false;
        for (int l : c) {
          int x = l == from ? to : l;
          if (value[x] > 0 || contains(d, m, x ^ 1)) {
            tautology = true;
            break;
          }
          if (value[x] == 0 && !contains(d, m, x)) {
            d[m++] = x;
          }
        }
        clauses[ci] = null;
        if (!tautology) {
          d = Arrays.copyOf(d, m);
          if (proof != null) {
            proof.add(d, 0, m);
          }
          if (m == 0) {
            unsat = true;
          } else if (m == 1) {
            found(d);
          } else {
            clauses[ci] = d;
            addOcc(to, ci);
          }
        }
        if (proof != null) {
          deleteLater(c);
        }
      }
    }
  }

  private static boolean contains(int[] c, int l) {
    return contains(c, c.length, l);
  }

  private static boolean contains(int[] c, int n, int l) {
    for (int i = 0; i < n; i++) {
      if (c[i] == l) {
        return true;
      }
    }
    return false;
  }

  // proof deletions wait until the environment is done: its sub-solver may still learn clauses
  // that are RUP only with the deleted clauses
  private int[][] deferred = new int[16][];
  private int numDeferred;

  private void deleteLater(int[] c) {
    if (forward == null) {
      if (proof != null) {
        proof.delete(c, 0, c.length);
      }
      return;
    }
    if (numDeferred == deferred.length) {
      deferred = Arrays.copyOf(deferred, 2 * numDeferred);
    }
    deferred[numDeferred++] = c;
  }

  private void pushStack(int pivot, int other) {
    if (stackSize + 3 > stack.length) {
      stack = Arrays.copyOf(stack, 2 * stack.length + 3);
    }
    stack[stackSize++] = pivot;
    stack[stackSize++] = other;
    stack[stackSize++] = 2;
  }

  /** Removes the clauses satisfied by a unit and the unit's negation from the others. */
  private void simplify(int l) {
    for (int sign = 0; sign < 2 && !unsat; sign++) {
      int lit = l ^ sign;
      int[] os = occ[lit];
      int n = occSize[lit];
      occ[lit] = null;
      occSize[lit] = 0;
      for (int k = 0; k < n && !unsat; k++) {
        int ci = os[k];
        int[] c = clauses[ci];
        if (c == null || !contains(c, lit)) {
          continue;
        }
        clauses[ci] = null;
        if (sign == 1) {
          int[] d = new int[c.length - 1];
          int m = 0;
          for (int x : c) {
            if (x != lit && value[x] == 0) {
              d[m++] = x;
            } else if (x != lit && value[x] > 0) {
              m = -1;
              break;
            }
          }
          if (m >= 0) {
            d = Arrays.copyOf(d, m);
            if (proof != null) {
              proof.add(d, 0, m);
            }
            if (m == 0) {
              unsat = true;
            } else if (m == 1) {
              found(d);
            } else {
              clauses[ci] = d;
            }
          }
        }
        if (proof != null) {
          deleteLater(c);
        }
      }
    }
  }

  /** A unit (one literal) or the empty clause found: logged, and kept as a result. */
  private void found(int[] c) {
    if (c.length == 0) {
      unsat = true;
      if (proof != null) {
        proof.add(c, 0, 0);
      }
      return;
    }
    int l = c[0];
    if (value[l] < 0) {
      unsat = true;
      if (proof != null) {
        proof.add(c, 0, 1);
        proof.add(c, 0, 0);
      }
      return;
    }
    if (value[l] > 0) {
      return;
    }
    if (proof != null) {
      proof.add(c, 0, 1);
    }
    value[l] = 1;
    value[l ^ 1] = -1;
    if (numUnits == units.length) {
      units = Arrays.copyOf(units, 2 * numUnits);
    }
    units[numUnits++] = l;
    if (sub != null && local[l >> 1] != 0 && !sub.addClause(CdclSolver.toDimacs(localOf(l)))) {
      unsat = true;
    }
    simplify(l);
  }

  private int localOf(int globalLit) {
    return 2 * (local[globalLit >> 1] - 1) + (globalLit & 1);
  }

  private int solve(int... assumed) {
    solves++;
    long before = sub.propagations;
    sub.setConflictLimit(sub.conflicts + CONFLICT_LIMIT);
    int[] dimacs = new int[assumed.length];
    for (int i = 0; i < assumed.length; i++) {
      dimacs[i] = CdclSolver.toDimacs(assumed[i]);
    }
    int r = sub.solve(dimacs);
    // the sub-solver's propagations, and the clauses and literals each call goes over
    work += sub.propagations - before + numEnvClauses + envLiterals;
    return r;
  }

  private void readModel() {
    work += numEnvVars + envLiterals;
    for (int i = 0; i < numEnvVars; i++) {
      boolean t = sub.modelValue(i + 1);
      model[2 * i] = t;
      model[2 * i + 1] = !t;
    }
    if (trueCount != null) {
      for (int i = 0; i < numEnvClauses; i++) {
        int t = 0;
        for (int l : envClauses[i]) {
          if (model[l]) {
            t++;
          }
        }
        trueCount[i] = t;
      }
    }
  }

  private void buildFlipSupport() {
    envOcc = new int[2 * numEnvVars][];
    envOccSize = new int[2 * numEnvVars];
    trueCount = new int[Math.max(16, numEnvClauses)];
    for (int i = 0; i < numEnvClauses; i++) {
      indexEnvClause(i);
    }
  }

  private void indexEnvClause(int i) {
    int t = 0;
    for (int l : envClauses[i]) {
      if (envOcc[l] == null) {
        envOcc[l] = new int[4];
      } else if (envOccSize[l] == envOcc[l].length) {
        envOcc[l] = Arrays.copyOf(envOcc[l], 2 * envOccSize[l]);
      }
      envOcc[l][envOccSize[l]++] = i;
      if (model[l]) {
        t++;
      }
    }
    if (i >= trueCount.length) {
      trueCount = Arrays.copyOf(trueCount, 2 * i + 2);
    }
    trueCount[i] = t;
  }

  /** A clause found here and now part of the environment: it must stay true under flips. */
  private void addEnvFact(int[] c) {
    pushEnvClause(c);
    indexEnvClause(numEnvClauses - 1);
  }

  /**
   * Flips a true literal of the model when every clause it satisfies has another true literal.
   *
   * @param lit a local literal, true in the model
   * @return whether it was flipped
   */
  private boolean flip(int lit) {
    work++;
    int[] os = envOcc[lit];
    int n = envOccSize[lit];
    for (int k = 0; k < n; k++) {
      if (trueCount[os[k]] == 1) {
        return false;
      }
    }
    for (int k = 0; k < n; k++) {
      trueCount[os[k]]--;
    }
    int[] on = envOcc[lit ^ 1];
    int m = envOccSize[lit ^ 1];
    for (int k = 0; k < m; k++) {
      trueCount[on[k]]++;
    }
    work += n + m;
    model[lit] = false;
    model[lit ^ 1] = true;
    return true;
  }

  private int flipBackbone(int[] backbone, int nb) {
    int j = 0;
    for (int i = 0; i < nb; i++) {
      int lit = backbone[i];
      if (model[lit] && !flip(lit)) {
        backbone[j++] = lit;
      }
    }
    return j;
  }

  private int refineBackbone(int[] backbone, int nb) {
    work += nb;
    int j = 0;
    for (int i = 0; i < nb; i++) {
      if (model[backbone[i]]) {
        backbone[j++] = backbone[i];
      }
    }
    return j;
  }

  /** Splits each class into its true and false literals in the model; drops singletons. */
  private int refinePartition(int[] partition, int np) {
    work += np;
    int[] out = new int[partition.length];
    int j = 0;
    int i = 0;
    while (i < np) {
      int end = i;
      while (partition[end] >= 0) {
        end++;
      }
      for (int pass = 0; pass < 2; pass++) {
        int start = j;
        for (int k = i; k < end; k++) {
          int l = partition[k];
          if (model[l] == (pass == 0) && active(envVars[l >> 1])) {
            out[j++] = l;
          }
        }
        if (j - start >= 2) {
          out[j++] = -1;
        } else {
          j = start;
        }
      }
      i = end + 1;
    }
    System.arraycopy(out, 0, partition, 0, j);
    return j;
  }

  /** Flips literals of the classes: a literal that flips alone leaves its class. */
  private int flipPartition(int[] partition, int np) {
    int dst = 0;
    int src = 0;
    while (src < np) {
      int end = src;
      while (partition[end] >= 0) {
        end++;
      }
      int size = end - src;
      int q = dst;
      for (int p = src; p < end; p++) {
        int lit = partition[p];
        // the class holds literals of equal value; flipping a true one breaks the class
        boolean flipped = size >= 2 && (model[lit] ? flip(lit) : flip(lit ^ 1));
        if (flipped) {
          size--;
        } else {
          partition[q++] = lit;
        }
      }
      if (q - dst >= 2) {
        partition[q++] = -1;
        dst = q;
      }
      src = end + 1;
    }
    return dst;
  }

  /** Forwards the sub-solver's clauses to the main proof in main variables. */
  private final class ProofForward implements ProofOutput {
    private int[] added = new int[64];
    private int numAdded;
    private int[] buffer = new int[16];

    @Override
    public void add(int[] lits, int from, int n) {
      if (buffer.length < n) {
        buffer = new int[2 * n];
      }
      for (int i = 0; i < n; i++) {
        buffer[i] = toGlobal(lits[from + i]);
      }
      proof.add(buffer, 0, n);
      if (n == 0) {
        return;
      }
      while (numAdded + n + 1 > added.length) {
        added = Arrays.copyOf(added, 2 * added.length);
      }
      System.arraycopy(buffer, 0, added, numAdded, n);
      numAdded += n;
      added[numAdded++] = n;
    }

    @Override
    public void delete(int[] lits, int from, int n) {
      // the sub-solver's deletions may name clauses of the main formula: ignored
    }

    void deleteAll() {
      int i = numAdded;
      while (i > 0) {
        int n = added[i - 1];
        int start = i - 1 - n;
        if (n > 1) {
          proof.delete(added, start, n);
        }
        i = start;
      }
      numAdded = 0;
    }
  }
}
