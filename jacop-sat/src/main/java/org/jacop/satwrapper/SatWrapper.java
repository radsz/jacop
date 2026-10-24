/*
 * SatWrapper.java
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

package org.jacop.satwrapper;

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.jasat.cdcl.CdclSolver;
import org.jacop.satwrapper.translation.DomainTranslator;
import org.jacop.satwrapper.translation.SatCpBridge;
import org.jacop.satwrapper.translation.SimpleCpVarDomain;

/**
 * Constraint that connects the CDCL SAT core to the CP solver. The CP search makes the decisions:
 * bounds of registered variables are asserted as literals in the SAT core, each on its own SAT
 * level, and the literals the core propagates are reported back to the CP domains. SAT levels
 * follow CP levels, so backtracking in CP backtracks the SAT core. A SAT conflict is learnt as a
 * clause and makes the CP solver fail until it has backtracked far enough for the clause to be
 * added.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class SatWrapper extends Constraint implements Stateful, SatisfiedPresent {

  /** Registered CP variables. */
  public final Set<IntVar> registeredVars = new HashSet<>();

  /** The SAT core. */
  public final CdclSolver sat = new CdclSolver();

  /** Association from a boolean variable of the SAT core to its CP variable bridge. */
  public SatCpBridge[] boolVarToDomains = new SatCpBridge[50];

  /** Reports literals propagated by the SAT core to CP domains. */
  public final SatChangesListener satChangesListener = new SatChangesListener();

  /** Store this constraint belongs to. */
  public Store store;

  /** The translator of domains to clauses. */
  public final DomainTranslator domainTranslator = new DomainTranslator();

  // true if no clause has been added
  boolean empty = true;

  // association from CP variables to their SAT bridge
  private final Map<IntVar, SatCpBridge> varToSatBridge = new HashMap<>();

  // model clauses waiting to be added to the SAT core
  private final ArrayDeque<int[]> modelClausesToAdd = new ArrayDeque<>();

  // literals to assert at the next call to consistency()
  private int[] toAssert = new int[16];
  private int numToAssert;

  // trail positions below this one have been reported to CP
  private int scanned;

  // CP levels 0..markLevel have been seen by consistency(); for each of them the SAT level and the
  // scanned position when it was first seen
  private int markLevel = -1;
  private int[] satLevelAtCpLevel = new int[16];
  private int[] scannedAtCpLevel = new int[16];

  /** Creates the wrapper with an empty SAT core. */
  public SatWrapper() {
    queueIndex = 1;
    domainTranslator.initialize(this);
    satChangesListener.initialize(this);
  }

  /**
   * Returns the SAT bridge of a CP variable.
   *
   * @param variable the CP variable
   * @return the bridge, or null if the variable is not registered
   */
  public SatCpBridge getSatBridge(IntVar variable) {
    return varToSatBridge.get(variable);
  }

  /**
   * Associates a CP variable with its SAT bridge.
   *
   * @param variable the CP variable
   * @param bridge the bridge
   */
  public void setSatBridge(IntVar variable, SatCpBridge bridge) {
    varToSatBridge.put(variable, bridge);
  }

  /**
   * Registers a CP variable: creates its boolean variables and the clauses that link them.
   *
   * @param variable the CP variable
   */
  public void register(IntVar variable) {
    if (registeredVars.add(variable)) {
      satChangesListener.ensureAccess(variable);
      variable.putModelConstraint(this, IntDomain.BOUND);
      new SimpleCpVarDomain(this, variable);
    }
  }

  /**
   * Creates fresh boolean variables in the SAT core and maps them to a bridge.
   *
   * @param count how many
   * @param bridge the bridge they belong to
   * @return the first new variable; the new ones are consecutive
   */
  public int newBoolVars(int count, SatCpBridge bridge) {
    int first = sat.newVariables(count);
    if (boolVarToDomains.length <= first + count) {
      boolVarToDomains = Arrays.copyOf(boolVarToDomains, 2 * (first + count));
    }
    Arrays.fill(boolVarToDomains, first, first + count, bridge);
    return first;
  }

  @Override
  public void consistency(Store store) {

    if (empty) {
      return;
    }
    do {
      propagate(store);
    } while (numToAssert > 0);
  }

  private void propagate(Store store) {
    markLevels(store.level);
    satChangesListener.clear();

    if (!settle()) {
      fail();
    }

    while (!modelClausesToAdd.isEmpty()) {
      int[] clause = modelClausesToAdd.pop();
      if (sat.addClauseLive(clause, clause.length)) {
        sat.propagateUnits();
      }
      if (!settle()) {
        fail();
      }
    }

    for (int i = 0; i < numToAssert; i++) {
      int literal = toAssert[i];
      int value = sat.value(literal);
      if (value > 0) {
        continue;
      }
      if (value < 0) {
        fail();
      }
      sat.newLevel();
      sat.assume(literal);
      sat.propagateUnits();
      if (!settle()) {
        fail();
      }
    }
    numToAssert = 0;

    // report the literals assigned by the SAT core to the CP domains
    int size = sat.trailSize();
    for (; scanned < size; scanned++) {
      satChangesListener.onAssertion(sat.trailLiteral(scanned));
    }
    satChangesListener.updateCpVariables(store.level);
    satChangesListener.clear();
  }

  /** Learns the pending clause while it is no longer false; false when CP has to fail. */
  private boolean settle() {
    if (!sat.isOk()) {
      return false;
    }
    while (sat.hasPendingClause()) {
      if (sat.pendingFalsified()) {
        return false;
      }
      sat.addPendingClause();
    }
    return true;
  }

  private void fail() {
    numToAssert = 0;
    satChangesListener.clear();
    throw Store.failException;
  }

  private void markLevels(int level) {
    if (level <= markLevel) {
      return;
    }
    if (satLevelAtCpLevel.length <= level) {
      satLevelAtCpLevel = Arrays.copyOf(satLevelAtCpLevel, 2 * level + 2);
      scannedAtCpLevel = Arrays.copyOf(scannedAtCpLevel, 2 * level + 2);
    }
    for (int l = markLevel + 1; l <= level; l++) {
      satLevelAtCpLevel[l] = sat.decisionLevel();
      scannedAtCpLevel[l] = scanned;
    }
    markLevel = level;
  }

  @Override
  public void removeLevel(int cpLevel) {
    numToAssert = 0;
    if (cpLevel > markLevel) {
      return;
    }
    sat.backtrackTo(Math.min(sat.decisionLevel(), satLevelAtCpLevel[cpLevel]));
    // literals reported at the removed CP levels and still assigned are reported again
    scanned = Math.min(scannedAtCpLevel[cpLevel], sat.trailSize());
    markLevel = cpLevel - 1;
  }

  @Override
  public void queueVariable(int level, Var v) {

    // also called for changes made by this constraint: a CP domain can then be stronger than the
    // literals that caused it (holes), and SAT has to know the result
    IntVar intVar = (IntVar) v;
    if (intVar.singleton()) {
      int eqLit = cpVarToBoolVar(intVar, intVar.domain.value(), true);
      if (eqLit != 0 && sat.value(eqLit) <= 0) {
        setBoolVariable(eqLit, true);
      }
    } else {
      int lowerLit = cpVarToBoolVar(intVar, intVar.domain.min() - 1, false);
      int upperLit = cpVarToBoolVar(intVar, intVar.domain.max(), false);
      if (lowerLit != 0 && sat.value(lowerLit) == 0) {
        setBoolVariable(lowerLit, false);
      }
      if (upperLit != 0 && sat.value(upperLit) == 0) {
        setBoolVariable(upperLit, true);
      }
    }
  }

  private void setBoolVariable(int variable, boolean value) {
    if (numToAssert == toAssert.length) {
      toAssert = Arrays.copyOf(toAssert, 2 * numToAssert);
    }
    toAssert[numToAssert++] = value ? variable : -variable;
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {
    return IntDomain.BOUND;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  /**
   * Describes the meaning of a literal.
   *
   * @param literal the literal
   * @return a description such as {@code (x)<=3}
   */
  public String showLiteralMeaning(int literal) {
    if (!isVarLiteral(literal)) {
      return "nothing";
    }
    String relation;
    if (isEqualityBoolVar(literal)) {
      relation = literal > 0 ? "=" : "!=";
    } else {
      relation = literal > 0 ? "<=" : ">";
    }
    return "(" + boolVarToCpVar(literal) + ")" + relation + boolVarToCpValue(literal);
  }

  /**
   * Describes the meaning of a clause.
   *
   * @param literals the literals of the clause
   * @return the meanings of the literals
   */
  public String showClauseMeaning(Iterable<Integer> literals) {
    StringBuilder answer = new StringBuilder();
    for (int i : literals) {
      answer.append(showLiteralMeaning(i)).append(", ");
    }
    return answer.toString();
  }

  @Override
  public String id() {
    return getClass().getName();
  }

  @Override
  public void removeConstraint() {
    // the SAT core holds no resources
  }

  /**
   * Returns false: the clauses are checked by propagation, not here.
   *
   * @return false
   */
  @Override
  public boolean satisfied() {
    return false;
  }

  @Override
  public String toString() {
    return getClass().getName();
  }

  @Override
  public void increaseWeight() {
    // Weight is not used for this constraint; no-op to satisfy interface.
  }

  @Override
  public Set<Var> arguments() {
    return new HashSet<>(registeredVars);
  }

  /**
   * Initializes a wrapper component with this wrapper.
   *
   * @param module the component
   */
  public void addWrapperComponent(WrapperComponent module) {
    module.initialize(this);
  }

  /**
   * Adds a clause of the model.
   *
   * @param clause the literals of the clause
   */
  public void addModelClause(Collection<Integer> clause) {
    addModelClause(clause.stream().mapToInt(Integer::intValue).toArray());
  }

  /**
   * Adds a clause of the model.
   *
   * @param clause the literals of the clause
   */
  public void addModelClause(int[] clause) {
    empty = false;
    modelClausesToAdd.add(clause);
  }

  @Override
  public void impose(Store store) {
    this.store = store;
    store.registerRemoveLevelListener(this);
    store.addChanged(this);
  }

  /**
   * Returns the boolean variable for {@code variable = value} or {@code variable <= value}.
   *
   * @param variable a registered CP variable
   * @param value the value
   * @param isEquality true for {@code =}, false for {@code <=}
   * @return the boolean variable, or 0 if the value is outside the variable's initial domain
   */
  public int cpVarToBoolVar(IntVar variable, int value, boolean isEquality) {
    SatCpBridge range = getSatBridge(variable);
    if (value < range.getMin() || value > range.getMax()) {
      return 0;
    }
    return range.cpValueToBoolVar(value, isEquality);
  }

  /**
   * Returns the bridge a literal belongs to.
   *
   * @param literal the literal
   * @return its bridge
   */
  public SatCpBridge boolVarToDomain(int literal) {
    return boolVarToDomains[Math.abs(literal)];
  }

  /**
   * Returns the CP variable a literal belongs to.
   *
   * @param literal the literal
   * @return its CP variable
   */
  public IntVar boolVarToCpVar(int literal) {
    return boolVarToDomains[Math.abs(literal)].variable;
  }

  /**
   * Returns the CP value a literal stands for.
   *
   * @param literal the literal
   * @return the value
   */
  public int boolVarToCpValue(int literal) {
    return boolVarToDomains[Math.abs(literal)].boolVarToCpValue(literal);
  }

  /**
   * Tells whether a literal stands for an equality (otherwise it stands for {@code <=}).
   *
   * @param literal the literal
   * @return true for an equality literal
   */
  public boolean isEqualityBoolVar(int literal) {
    return boolVarToDomains[Math.abs(literal)].isEqualityBoolVar(literal);
  }

  /**
   * Tells whether a literal belongs to a CP variable.
   *
   * @param literal the literal
   * @return true if it stands for a CP variable's value or bound
   */
  public boolean isVarLiteral(int literal) {
    int varIdx = Math.abs(literal);
    return varIdx != 0 && varIdx < boolVarToDomains.length && boolVarToDomains[varIdx] != null;
  }

  /**
   * Writes the clauses of the SAT core in DIMACS format.
   *
   * @param output the destination
   * @throws IOException if writing fails
   */
  public void toCnf(BufferedWriter output) throws IOException {
    sat.writeDimacs(output);
  }
}
