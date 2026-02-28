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

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.ArrayDeque;
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
import org.jacop.jasat.core.Config;
import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.SolverComponent;
import org.jacop.jasat.core.SolverState;
import org.jacop.jasat.core.Trail;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.modules.ActivityModule;
import org.jacop.jasat.modules.HeuristicAssertionModule;
import org.jacop.jasat.modules.interfaces.ConflictListener;
import org.jacop.jasat.modules.interfaces.ExplanationListener;
import org.jacop.jasat.modules.interfaces.SolutionListener;
import org.jacop.jasat.modules.interfaces.StartStopListener;
import org.jacop.jasat.utils.MemoryPool;
import org.jacop.jasat.utils.Utils;
import org.jacop.jasat.utils.structures.IntQueue;
import org.jacop.satwrapper.translation.DomainClausesDatabase;
import org.jacop.satwrapper.translation.DomainTranslator;
import org.jacop.satwrapper.translation.SatCpBridge;
import org.jacop.satwrapper.translation.SimpleCpVarDomain;

/**
 * Wrapper to communicate between SAT solver and CP solver. It listens for SAT conflicts, so that it
 * can force the CP solver to backtrack until the conflict is resolved in SAT. It listens to
 * propagations, to know which literals are asserted in SAT, to report those assertions on CP
 * variables domains.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class SatWrapper extends Constraint
    implements ConflictListener,
        ExplanationListener,
        StartStopListener,
        SolutionListener,
        Stateful,
        SatisfiedPresent {

  // registered CP variables
  public final Set<IntVar> registeredVars = new HashSet<>();
  // guide assertions
  public final HeuristicAssertionModule assertionModule = null;
  // the DomainClausesDatabase, if any
  public final DomainClausesDatabase domainDatabase;
  // level of verbosity (the higher, the more verbose)
  public final int verbosity = 0;
  // association from CP variables to their SAT bridge (replaces IntVar.satBridge field)
  private final Map<IntVar, SatCpBridge> varToSatBridge = new HashMap<>();
  // model clauses waiting to be added to the SAT solver
  private final ArrayDeque<int[]> modelClausesToAdd = new ArrayDeque<>();
  // sat solver instance
  public Core core;
  // keep track of literals activity, and give search advices (optional)
  public ActivityModule activity;
  // association (boolean variable) -> LiteralRange (and so, IntVar)
  public SatCpBridge[] boolVarToDomains = new SatCpBridge[50];
  // the change listene to plug in the SAT solver
  public SatChangesListener satChangesListener;
  // store this constraint belongs to
  public Store store;
  // pool of int[]
  public MemoryPool pool;
  // the translator of domains
  public DomainTranslator domainTranslator;
  // SAT level to backjump to if failure
  public int levelToBackjumpTo;
  // maps SAT levels to CP levels and conversely
  public Integer[] satToCpLevels = new Integer[5];
  public Integer[] cpToSatLevels = new Integer[5];
  // empty == true if no clauses has been added
  boolean empty = true;
  // the trail of the solver
  private Trail trail;

  // current level for SAT solver
  private int currentSatLevel;
  // next literals to assert during consistency()
  private IntQueue toAssertLiterals;

  // to remember which clause we should learn at next conflict resolution
  private MapClause clauseToLearn;

  // set to true between conflict and explanation
  private boolean mustBacktrack;

  // did the solver reach a solution?
  private boolean hasSolution;

  /** Creates everything in the right order. */
  public SatWrapper() {
    queueIndex = 1;

    // empty config
    Config config = Config.defaultConfig();

    // add itself as a component of the Core
    config.mainComponents.add(this);

    // be *SURE* the constraint db is at first position
    domainDatabase = new DomainClausesDatabase();
    domainDatabase.initialize(this);
    config.clausesDatabases.addFirst(domainDatabase);

    // many detail
    config.timeout = 0;
    config.verbosity = this.verbosity;
    config.debug = false;

    // create solver with this config
    core = new Core(config);

    // setup everything
    core.start();
  }

  /**
   * Gets the SAT bridge for the given variable. Replaces direct access to IntVar.satBridge field.
   *
   * @param variable the IntVar
   * @return the SatCpBridge associated with the variable, or null if not set
   */
  public SatCpBridge getSatBridge(IntVar variable) {
    return varToSatBridge.get(variable);
  }

  /**
   * Sets the SAT bridge for the given variable. Replaces direct assignment to IntVar.satBridge
   * field.
   *
   * @param variable the IntVar
   * @param bridge the SatCpBridge to associate with the variable
   */
  public void setSatBridge(IntVar variable, SatCpBridge bridge) {
    varToSatBridge.put(variable, bridge);
  }

  /**
   * Registers a variable with the SAT wrapper using default translation.
   *
   * @param result the variable to register
   */
  public void register(IntVar result) {
    register(result, true);
  }

  /**
   * Registers the variable so that we can use it in SAT solver.
   *
   * @param variable the CP IntVar variable
   * @param translate indicate whether to use == or {@literal <=}
   */
  public void register(IntVar variable, boolean translate) {

    if (!registeredVars.contains(variable)) {

      registeredVars.add(variable);

      // tell the Sat Change listener
      satChangesListener.ensureAccess(variable);

      // tell the store we watch this variable
      variable.putModelConstraint(this, IntDomain.BOUND);

      SatCpBridge bridge = new SimpleCpVarDomain(this, variable, translate);
      setSatBridge(variable, bridge);
      if (ASSERTS_ENABLED && !log(this, "create default domain", bridge)) {
        throw new IllegalStateException("Assertion failed");
      }
    }
  }

  /**
   * The point where all operations are effectively done in the SAT solver, until no operation
   * remains or a conflict occurs.
   */
  @Override
  public void consistency(Store store) {

    if (empty) {
      return;
    }

    if (mustBacktrack) {
      core.toPropagate.clear();
      toAssertLiterals.clear();
      satChangesListener.clear();
      mustBacktrack = false;
      throw Store.failException;
    }

    // clear the structure that watches changes in literals
    satChangesListener.clear();

    /*
     * Learn the last conflict clause, if any.
     * Then, add waiting clauses to the solver and check consistency
     * again.
     */
    if (clauseToLearn != null) {

      core.currentState = SolverState.UNKNOWN;
      core.toPropagate.clear();

      core.triggerLearnEvent(clauseToLearn);
      core.unitPropagate();
      if (core.currentState == SolverState.CONFLICT) {
        core.toPropagate.clear();
        toAssertLiterals.clear();
        satChangesListener.clear();
        if (mustBacktrack) {
          mustBacktrack = false;
          throw Store.failException;
        }
      }
      clauseToLearn = null;
    }

    while (!modelClausesToAdd.isEmpty()) {
      // find the next clause to add/to learn
      int[] clause = modelClausesToAdd.pop();
      core.addModelClause(clause);

      // check if the solver is in a consistent state, otherwise fail
      core.unitPropagate();
    }

    // XXX NOTE : remember to set this flag to false in case of conflict

    /*
     * take literals that must be asserted, and assert each of them
     */
    while (!toAssertLiterals.isEmpty()) {

      processOneLiteral();

      // check SAT consistency, because the previous assertion may have
      // triggered other propagations.
      core.unitPropagate();
    }

    if (mustBacktrack) {
      core.toPropagate.clear();
      toAssertLiterals.clear();
      satChangesListener.clear();
      mustBacktrack = false;
      throw Store.failException;
    }

    /*
     * report changes in SAT literals to domains of CP variables, using
     * satChangesListener to select most restrictive changes
     */
    satChangesListener.updateCpVariables(store.level);
    satChangesListener.clear();

    if (!toAssertLiterals.isEmpty()) {
      consistency(store);
    }
  }

  /** Assert the next literal from toAssertLiterals. */
  private void processOneLiteral() {
    if (ASSERTS_ENABLED && toAssertLiterals.isEmpty()) {
      throw new IllegalStateException("Assertion failed");
    }

    // take the next literal (already set literals are ignored)
    int literal = toAssertLiterals.pop();
    if (ASSERTS_ENABLED && literal == 0) {
      throw new IllegalStateException("Assertion failed");
    }
    if (trail.isSet(Math.abs(literal))) {
      if (trail.values[Math.abs(literal)] != literal) {
        toAssertLiterals.clear();
        satChangesListener.clear();
        core.toPropagate.clear();
        throw Store.failException;
      }
      if (ASSERTS_ENABLED
          && !log(
              this,
              "literal " + literal + " already set (to " + trail.values[Math.abs(literal)] + ")")) {
        throw new IllegalStateException("Assertion failed");
      }

      return;
    }

    addSatLevel();

    // print what literal we assert, and its meaning
    // log(this, "wrapper assert literal "+literal+
    //   " at (cp level " + store.level +
    //   ", sat level "+currentSatLevel+
    //   ") standing for "+showLiteralMeaning(literal));

    // trigger propagation in *SAT-solver*
    core.assertLiteral(literal, currentSatLevel);
  }

  /** Adds one level for SAT side, and remembers the association between CP and SAT levels. */
  private void addSatLevel() {
    currentSatLevel++;

    // store the associations
    cpToSatLevels = Utils.ensure(cpToSatLevels, store.level);
    satToCpLevels = Utils.ensure(satToCpLevels, currentSatLevel);
    cpToSatLevels[store.level] = currentSatLevel;
    satToCpLevels[currentSatLevel] = store.level;
  }

  /** Wrapper listens for conflicts. */
  public void onConflict(MapClause clause, int level) {
    satChangesListener.clear();
    toAssertLiterals.clear();

    mustBacktrack = true;

    if (ASSERTS_ENABLED && !log(this, "*** conflict occurred at sat level " + level)) {
      throw new IllegalStateException("Assertion failed");
    }

    // wait for the explanation
  }

  /** Wrapper listens for explanations, to know how deep to backtrack. */
  public void onExplain(MapClause explanation) {
    if (ASSERTS_ENABLED && !mustBacktrack) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && core.explanationClause != explanation) {
      throw new IllegalStateException("Assertion failed");
    }

    // get clause to learn after backjump
    clauseToLearn = explanation;

    if (ASSERTS_ENABLED
        && !log(
            this,
            "*** must learn explanation %s meaning %s",
            explanation,
            showClauseMeaning(explanation))) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !log(this, "trail: " + core.trail)) {
      throw new IllegalStateException("Assertion failed");
    }

    // perform failure right now (we should be during consistency())

  }

  /**
   * Called when a solution is found.
   *
   * @param satisfiable indicates if the solution is satisfiable
   */
  public void onSolution(boolean satisfiable) {
    hasSolution = true;
  }

  /**
   * When the CP solver decides to remove a level, the wrapper must force the SAT solver to
   * backtrack accordingly, to keep mappings between the two search trees consistent. This is also
   * the place where the wrapper can decide that a conflict in the SAT solver has been solved.
   */
  @Override
  public void removeLevel(int cpLevel) {

    // remove things to be asserted in SAT, clear some things...
    toAssertLiterals.clear();
    core.toPropagate.clear();

    // this CP level is of no concern to us
    if (cpLevel >= cpToSatLevels.length || cpToSatLevels[cpLevel] == null) {
      return;
    }

    // find the previous CP level that makes sense for the wrapper (-1 if none)
    int previousCpLevel = -1;
    for (int i = cpLevel - 1; i >= 0; i--) {
      if (cpToSatLevels[i] != null) {
        previousCpLevel = i;
        break;
      }
    }
    // log(this, "remove cp level "+cpLevel +
    //   " (previous : "+previousCpLevel+")");

    // this CP level does not correspond to anything anymore
    cpToSatLevels[cpLevel] = null;
    // the new maximum SAT level
    int newMaxSatLevel = previousCpLevel == -1 ? 0 : cpToSatLevels[previousCpLevel];
    if (ASSERTS_ENABLED && newMaxSatLevel < 0) {
      throw new IllegalStateException("Assertion failed");
    }

    if (newMaxSatLevel != currentSatLevel) {

      if (ASSERTS_ENABLED && currentSatLevel <= newMaxSatLevel) {
        throw new IllegalStateException("Assertion failed");
      }
      // we are not at the SAT level we should be, so backjump to reach it

      if (ASSERTS_ENABLED
          && !log(this, "solver backjumps from %d to %d", currentSatLevel, newMaxSatLevel)) {
        throw new IllegalStateException("Assertion failed");
      }

      if (ASSERTS_ENABLED && !log(this, "core SAT level %d", core.currentLevel)) {
        throw new IllegalStateException("Assertion failed");
      }

      core.backjumpToLevel(newMaxSatLevel);
      currentSatLevel = core.currentLevel;
      if (ASSERTS_ENABLED && currentSatLevel != newMaxSatLevel) {
        throw new IllegalStateException("Assertion failed");
      }

      if (clauseToLearn != null) {

        mustBacktrack = clauseToLearn.isUnsatisfiableIn(trail);
      }
    }
  }

  /*
   * this may be called many times without consistency(), or be
   * followed by a removeLevel(), so do not assume anything and just
   * queue things to be asserted
   */
  @Override
  public void queueVariable(int level, Var v) {

    /* KK: Do not queue variable when this constraint (wrapper) executes
     *     its consistency method
     */
    if (store.currentConstraint != null) {
      if (store.currentConstraint.equals(this)) {
        return;
      }
    }

    /*
     * update ranges for this variable (assert some literals).
     * those operations must not be executed here (we must avoid
     * failure), but rather be scheduled for being executed at next call to
     * consistency()
     */
    if (ASSERTS_ENABLED && !registeredVars.contains(v)) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !log(this, "queue variable " + v + " at CP level " + level)) {
      throw new IllegalStateException("Assertion failed");
    }

    // this must be a SatVar
    if (ASSERTS_ENABLED && !(v instanceof IntVar)) {
      throw new IllegalStateException("Assertion failed");
    }
    IntVar intVar = (IntVar) v; // cast it in an IntVar

    if (intVar.singleton()) {
      // singleton => assign this variable to the unique value
      int lit = cpVarToBoolVar(intVar, intVar.domain.value(), true);
      setBoolVariable(lit, true);

    } else {
      // let us check the domain bounds
      int lower = intVar.domain.min();
      int upper = intVar.domain.max();
      if (ASSERTS_ENABLED && upper - lower < 1) {
        throw new IllegalStateException("Assertion failed");
      } // otherwise, singleton

      int lowerLit = cpVarToBoolVar(intVar, lower - 1, false);
      int upperLit = cpVarToBoolVar(intVar, upper, false);

      // if those literals are not yet set, just add them
      if (lowerLit != 0 && !trail.isSet(lowerLit)) {
        setBoolVariable(lowerLit, false);
      }
      if (upperLit != 0 && !trail.isSet(upperLit)) {
        setBoolVariable(upperLit, true);
      }
    }
  }

  /**
   * Called when a boolean variable is set to some boolean value.
   *
   * @param variable the boolean variable
   * @param value the value (true or false) of this variable
   */
  private void setBoolVariable(int variable, boolean value) {
    // notify the constraint clauses database, for propagations
    if (ASSERTS_ENABLED && variable <= 0) {
      throw new IllegalStateException("Assertion failed");
    }
    int literal = value ? variable : -variable;

    toAssertLiterals.add(literal);
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
   * Asks the solver for which literal is the most active. It will return a literal, which can be
   * transformed into a variable and a value from the variable domain. Useful when the CP solver
   * does not know which variable to set to continue research
   *
   * @return a literal corresponding to some possible (variable,value)
   */
  public int getMostActiveLiteral() {
    return assertionModule.findNextVar();
  }

  /**
   * (for debug) show what a literal means.
   *
   * @param literal literal for showing its meaning
   * @return literal meaning
   */
  public String showLiteralMeaning(int literal) {
    if (!isVarLiteral(literal)) {
      return "nothing";
    }

    return "("
        + boolVarToCpVar(literal)
        + ")"
        + (isEqualityBoolVar(literal) ? (literal > 0 ? "=" : "!=") : (literal > 0 ? "<=" : ">"))
        + boolVarToCpValue(literal);
  }

  /**
   * Shows the meaning of a clause as a string.
   *
   * @param literals the literals in the clause
   * @return string representation of clause meaning
   */
  public String showClauseMeaning(Iterable<Integer> literals) {
    StringBuilder answer = new StringBuilder();
    for (int i : literals) {
      answer.append(showLiteralMeaning(i)).append(", ");
    }
    return answer.toString();
  }

  /** {@inheritDoc} */
  @Override
  public String id() {
    return getClass().getName();
  }

  /** {@inheritDoc} */
  @Override
  public void removeConstraint() {
    /*
     * stop solver, and clean up things
     */
    core.stop();
    core = null; // garbage collect
  }

  /** {@inheritDoc} */
  public boolean satisfied() {
    return hasSolution || core.currentState == SolverState.SATISFIABLE;
  }

  /** {@inheritDoc} */
  @Override
  public String toString() {
    return getClass().getName();
  }

  /** {@inheritDoc} */
  @Override
  public void increaseWeight() {
    // Weight is not used for this constraint; no-op to satisfy interface.
  }

  /** {@inheritDoc} */
  @Override
  public Set<Var> arguments() {
    return new HashSet<>(registeredVars);
  }

  /**
   * To add some module to the solver.
   *
   * @param module the module to add
   */
  public void addSolverComponent(SolverComponent module) {
    core.addComponent(module);
  }

  /**
   * Add a component.
   *
   * @param module the component
   */
  public void addWrapperComponent(WrapperComponent module) {
    module.initialize(this);
  }

  /** Asks the solver to forget useless clauses, to free memory. */
  public void forget() {
    core.forget();
  }

  /**
   * Add model (globally valid) clause to solver, in a delayed fashion.
   *
   * @param clause the clause to add
   */
  public void addModelClause(Collection<Integer> clause) {
    int[] toAdd = pool.getNew(clause.size());
    int index = 0;
    for (int i : clause) {
      toAdd[index++] = i;
    }
    modelClausesToAdd.add(toAdd);
  }

  /**
   * Adds a model clause to the SAT solver.
   *
   * @param clause the clause as an array of literals
   */
  public void addModelClause(int[] clause) {

    empty = false;

    modelClausesToAdd.add(clause);
  }

  /**
   * Add the constraint to the wrapper (ie, constraint.imposeToSat(this)).
   *
   * @param constraint the constraint to add
   */
  public void impose(Constraint constraint) {

    System.err.println("impose constraint in SatWrapper is not defined");
    throw new RuntimeException();
  }

  @Override
  public void impose(Store store) {
    this.store = store;

    // make solver quiet, if not debug
    if (!Store.DEBUG) {
      core.verbosity = 0;
    }

    // be warned in case of backtrack
    store.registerRemoveLevelListener(this);

    store.addChanged(this);
    // watch variables
  }

  /**
   * Given a CP variable and a value, retrieve the associated boolean literal for either 'variable =
   * value' or either 'variable {@literal <=} value'.
   *
   * @param variable the CP variable
   * @param value a value in the range of this variable
   * @param isEquality a boolean, true if we want the literal that stands for 'x=d', false for
   *     'x{@literal <=}d'
   * @return the corresponding literal, or 0 if it is out of bounds
   */
  public int cpVarToBoolVar(IntVar variable, int value, boolean isEquality) {

    SatCpBridge range = getSatBridge(variable);

    if (ASSERTS_ENABLED && range == null) {
      throw new IllegalStateException("Assertion failed");
    }

    if (value < range.getMin() || value > range.getMax()) {
      return 0;
    }
    return range.cpValueToBoolVar(value, isEquality);
  }

  /**
   * Returns the CpVarDomain associated with this literal.
   *
   * @param literal the boolean literal
   * @return a range
   */
  public SatCpBridge boolVarToDomain(int literal) {
    int varIdx = Math.abs(literal);
    return boolVarToDomains[varIdx];
  }

  /**
   * Get the IntVar back from a literal.
   *
   * @param literal the literal
   * @return IntVar represented by the literal
   */
  public IntVar boolVarToCpVar(int literal) {
    if (ASSERTS_ENABLED && !isVarLiteral(literal)) {
      throw new IllegalStateException("Assertion failed");
    }

    int varIdx = Math.abs(literal);
    SatCpBridge range = boolVarToDomains[varIdx];
    return range.variable;
  }

  /**
   * Transform a literal 'x=v' into a value 'v' for some CP variable.
   *
   * @param literal literal to be transformed to value it represents
   * @return the value represented by this literal
   */
  public int boolVarToCpValue(int literal) {
    if (ASSERTS_ENABLED && !isVarLiteral(literal)) {
      throw new IllegalStateException("Assertion failed");
    }

    int varIdx = Math.abs(literal);
    // find which range this literal belongs to
    SatCpBridge range = boolVarToDomains[varIdx];
    return range.boolVarToCpValue(varIdx);
  }

  /**
   * Checks if the boolean variable represents an assertion 'x=v' or 'x{@literal <=}v'.
   *
   * @param literal the boolean literal
   * @return true if the literal represents a proposition 'x=v', false if it represents 'x{@literal
   *     <=}v'
   */
  public boolean isEqualityBoolVar(int literal) {
    if (ASSERTS_ENABLED && !isVarLiteral(literal)) {
      throw new IllegalStateException("Assertion failed");
    }
    int varIdx = Math.abs(literal);
    IntVar variable = boolVarToCpVar(literal);
    SatCpBridge range = getSatBridge(variable);
    return range.isEqualityBoolVar(varIdx);
  }

  /**
   * Checks if this literal corresponds to some CP variable.
   *
   * @param literal the literal
   * @return true if this literal stands for some 'x=v' or 'x{@literal <=}v' proposition
   */
  public boolean isVarLiteral(int literal) {
    /*
     * we must ensure it is very fast (called very often)
     */
    int varIdx = Math.abs(literal);
    if (varIdx == 0 || varIdx >= boolVarToDomains.length) {
      return false;
    }
    return boolVarToDomains[varIdx] != null;
  }

  /**
   * Log method, similar to printf. Example: wrapper.log(this, "%s is %d", "foo", 42);
   *
   * @param o the object that logs something (use <code>this</code>)
   * @param format the format string (the message, if no formatting)
   * @param args the arguments to fill in the format
   * @return always true
   */
  public boolean log(Object o, String format, Object... args) {
    if (o == null && format == null && args == null) {
      return true;
    }
    return true;
  }

  /** Called when the SAT solver starts. */
  public void onStart() {
    if (ASSERTS_ENABLED && core == null) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && core.dbStore == null) {
      throw new IllegalStateException("Assertion failed");
    }
    // due to some dependencies problems, we cannot access the database
    // before this point
  }

  /** Called when the SAT solver stops. */
  public void onStop() {
    // No cleanup or notification needed when the solver stops.
  }

  /**
   * Initializes the wrapper with the specified SAT core.
   *
   * @param core the SAT core to initialize with
   */
  public void initialize(Core core) {

    this.core = core;
    // register to events
    core.conflictModules[core.numConflictModules++] = this;
    core.explanationModules[core.numExplanationModules++] = this;
    core.startStopModules[core.numStartStopModules++] = this;
    core.solutionModules[core.numSolutionModules++] = this;

    // get some fields
    this.pool = core.pool;
    this.trail = core.trail;
    this.toAssertLiterals = new IntQueue(pool);

    // sat changes listener
    this.satChangesListener = new SatChangesListener();
    core.addComponent(satChangesListener);
    satChangesListener.initialize(this);

    // domain translator
    domainTranslator = new DomainTranslator();
    domainTranslator.initialize(this);
  }

  /**
   * Writes the SAT problem to CNF format.
   *
   * @param output the buffered writer to write to
   * @throws IOException if an I/O error occurs
   */
  public void toCnf(BufferedWriter output) throws IOException {

    core.dbStore.toCnf(output);
  }
}
