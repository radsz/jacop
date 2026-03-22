/*
 * Core.java
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

package org.jacop.jasat.core;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;
import java.util.Timer;
import org.jacop.jasat.core.clauses.AbstractClausesDatabase;
import org.jacop.jasat.core.clauses.DatabasesStore;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.modules.SearchModule;
import org.jacop.jasat.modules.interfaces.AssertionListener;
import org.jacop.jasat.modules.interfaces.BackjumpListener;
import org.jacop.jasat.modules.interfaces.ClauseListener;
import org.jacop.jasat.modules.interfaces.ConflictListener;
import org.jacop.jasat.modules.interfaces.ExplanationListener;
import org.jacop.jasat.modules.interfaces.ForgetListener;
import org.jacop.jasat.modules.interfaces.PropagateListener;
import org.jacop.jasat.modules.interfaces.SolutionListener;
import org.jacop.jasat.modules.interfaces.StartStopListener;
import org.jacop.jasat.utils.MemoryPool;
import org.jacop.jasat.utils.structures.IntQueue;
import org.jacop.jasat.utils.structures.IntVec;

/**
 * The main solver structure, to be used either by a search component or by another program that
 * uses it for conflict learning and detection.
 *
 * <p>This implements interfaces for being manipulated from the outside, and from its components
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class Core implements SolverComponent {

  // timer for scheduled events (daemon thread)
  public final Timer timer = new Timer(true);
  // stream to log messages to
  public final PrintStream logStream = System.out;
  // for modules.
  public final AssertionListener[] assertionModules = new AssertionListener[5];
  public final BackjumpListener[] backjumpModules = new BackjumpListener[5];
  public final ConflictListener[] conflictModules = new ConflictListener[5];
  public final PropagateListener[] propagateModules = new PropagateListener[5];
  public final SolutionListener[] solutionModules = new SolutionListener[5];
  public final ForgetListener[] forgetModules = new ForgetListener[5];
  public final ClauseListener[] clauseModules = new ClauseListener[5];
  public final ExplanationListener[] explanationModules = new ExplanationListener[5];
  public final StartStopListener[] startStopModules = new StartStopListener[5];
  public final BackjumpListener[] restartModules = new BackjumpListener[5];
  // a time counter
  private final Map<String, Long> timeMap = new HashMap<>();
  // asynchronous unit propagation
  public IntQueue toPropagate;
  // the conflict explanation clause
  public MapClause explanationClause = new MapClause();
  // used to compute throughput of the solver
  public long assignmentNum;
  // is the solver stopped ?
  public boolean isStopped;
  // pool of int[] to avoir allocating too much
  public MemoryPool pool;
  // all current clauses
  public DatabasesStore dbStore;
  // the variable trail
  public Trail trail;
  // the search component
  public SearchModule search;
  // the configuration
  public Config config;
  // sets the verbosity of the solver. The bigger this value is, the more
  // debug messages will be printed.
  // 0 means no messages at all, 1 means only important messages
  public int verbosity;
  // the current level of research
  public int currentLevel;
  // current state of the solver (indicates what to do next)
  public int currentState = SolverState.UNKNOWN;
  // the conflict learning module
  public ConflictLearning conflictLearning;
  public int numAssertionModules;
  public int numBackjumpModules;
  public int numConflictModules;
  public int numPropagateModules;
  public int numSolutionModules;
  public int numForgetModules;
  public int numClauseModules;
  public int numExplanationModules;
  public int numStartStopModules;
  public int numRestartModules;
  private boolean mustForget;
  // the maximum variable allowed
  private int maxVariable;

  /**
   * Creates the solver, which in turn creates all inner components and connect them together.
   *
   * @param config configuration for the solver
   */
  public Core(Config config) {
    // set the config
    if (ASSERTS_ENABLED && !config.check()) {
      throw new IllegalStateException("Assertion failed");
    }
    this.config = config;

    // set some parameters
    verbosity = config.verbosity;

    // create some components
    addComponent(new MemoryPool());
    addComponent(new DatabasesStore());
    addComponent(new Trail());
    addComponent(new ConflictLearning());
    toPropagate = new IntQueue(pool);

    // add instantiated components from configuration object
    for (SolverComponent component : config.mainComponents) {
      addComponent(component);
    }
    // and require the class of the other required components
    for (AbstractClausesDatabase database : config.clausesDatabases) {
      addComponent(database);
    }
  }

  /** Initializes the solver with a default configuration. */
  public Core() {
    this(Config.defaultConfig()); // use a default config
    logc("solver initializes with default config");
  }

  /**
   * Adds a clause to the solver.
   *
   * @param clause the clause to add
   * @return the unique ID of the clause
   */
  public int addModelClause(IntVec clause) {
    int[] newClause = clause.toArray();
    return addClause(newClause, true);
  }

  /**
   * Same as previous, add the clause as a model clause.
   *
   * @param clause the clause to add
   * @return the unique ID of this clause, or -1 if it is trivial
   */
  public int addModelClause(int[] clause) {
    return addClause(clause, true);
  }

  /** Add @param clause to the pool of clauses. */
  private int addClause(int[] clause, boolean isModelClause) {
    int clauseId = dbStore.addClause(clause, isModelClause);

    // notify modules
    for (int i = 0; i < numClauseModules; i++) {
      clauseModules[i].onClauseAdd(clause, clauseId, isModelClause);
    }

    return clauseId;
  }

  /**
   * Checks if the clause can be removed without breaking solver correctness.
   *
   * @param clauseId the unique Id of the clause
   * @return true if removing the clause is allowed
   */
  public boolean canRemove(int clauseId) {
    return dbStore.canRemove(clauseId);
  }

  /**
   * Removes the clause with unique Id, if possible.
   *
   * @param clauseId the unique Id of the clause to remove
   * @return true if success, false if failure
   */
  public boolean removeClause(int clauseId) {
    if (canRemove(clauseId)) {

      // remove the clause, since this is possible
      dbStore.removeClause(clauseId);

      // notify modules
      for (ClauseListener module : clauseModules) {
        module.onClauseRemoval(clauseId);
      }

      return true;
    } else {
      return false;
    }
  }

  /**
   * Decides a single step of search by setting the value of a variable.
   *
   * @param literal the literal to set true
   * @param newLevel the current search level
   */
  public void assertLiteral(int literal, int newLevel) {
    if (ASSERTS_ENABLED && newLevel <= this.currentLevel) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && Math.abs(literal) > maxVariable) {
      throw new IllegalStateException("Assertion failed");
    }

    triggerAssertEvent(literal, newLevel);
  }

  /**
   * Tells the SAT-solver to backtrack to the given level. The level must be lower or equal to the
   * solver's current level.
   *
   * @param level the level to return to
   */
  public void backjumpToLevel(int level) {
    if (ASSERTS_ENABLED && level >= currentLevel) {
      throw new IllegalStateException("Assertion failed");
    }

    triggerBackjumpEvent(level);
  }

  /** Make a restart, that is, restart search from level 0. */
  public void restart() {
    triggerRestartEvent();
  }

  /** Notify all modules that we start. */
  public void start() {
    if (isStopped) {
      throw new AssertionError("should not start when already stopped");
    }

    markTime("start");
    logc("solver starts");

    // first unit propagation (for literals propagated when clauses were added)
    unitPropagate();

    // notify modules
    for (int i = 0; i < numStartStopModules; i++) {
      startStopModules[i].onStart();
    }
  }

  /** Notify all modules that we stop. */
  public void stop() {

    if (!isStopped) {
      // read stop event
      markTime("stop");

      // notify modules
      for (int i = 0; i < numStartStopModules; i++) {
        startStopModules[i].onStop();
      }

      // stop events
      timer.cancel();
      isStopped = true;
    }
  }

  /** Removes the less useful learnt clauses to free memory. */
  public void forget() {
    mustForget = true;
  }

  /**
   * Computes at which level we should backjump to solve the conflict. The solver must be in
   * CONFLICT state.
   *
   * @return a level lower than the current level, in which the solver state would no longer be
   *     CONFLICT.
   */
  public int getLevelToBackjump() {
    if (ASSERTS_ENABLED && explanationClause == null) {
      throw new IllegalStateException("Assertion failed");
    }
    return conflictLearning.getLevelToBackjump(explanationClause);
  }

  /**
   * Computes at which level we should backjump to solve the conflict using the given explanation
   * clause.
   *
   * @param explanationClause the explanation clause
   * @return a level lower than the current level
   */
  public int getLevelToBackjump(MapClause explanationClause) {
    if (ASSERTS_ENABLED && explanationClause == null) {
      throw new IllegalStateException("Assertion failed");
    }
    return conflictLearning.getLevelToBackjump(explanationClause);
  }

  /**
   * Gets a fresh variable that one can use for example for lazy clause generation. If used, every
   * clause added must use only the variables get by this way, or a variable collision could occur.
   *
   * @return a fresh variable
   */
  public int getFreshVariable() {
    int answer = maxVariable + 1;
    setMaxVariable(answer);
    return answer;
  }

  /**
   * Get several new variables at once, more efficiently than running getFreshVariable() @param
   * number times. The variables range from the returned int to the returned int + @param number - 1
   *
   * @param number the number of fresh variables we want
   * @return The first variable in the range of new variables
   */
  public int getManyFreshVariables(int number) {
    int answer = maxVariable + 1;
    setMaxVariable(maxVariable + number);
    return answer;
  }

  /**
   * Returns the current maximum variable.
   *
   * @return the current max variable
   */
  public int getMaxVariable() {
    return maxVariable;
  }

  /**
   * Tells the solver what is the greatest variable in the problem.
   *
   * @param maxVariable the new maximum variable. Must not be lower than solver.getMaxVariable().
   */
  public void setMaxVariable(int maxVariable) {

    if (maxVariable > this.maxVariable) {
      this.maxVariable = maxVariable;
      trail.ensureCapacity(maxVariable);
    } else {
      logc("tried to downgrade the max var from %d to %d", this.maxVariable, maxVariable);
    }
  }

  /**
   * Give the module access to the whole class, even if the solver is only known as a ISatSolver.
   *
   * @param module the module to add to the solver
   */
  public void addComponent(SolverComponent module) {
    module.initialize(this);
  }

  /**
   * Performs propagation on all unit clauses until either : - no unit clause remains - a conflict
   * occurs.
   */
  public void unitPropagate() {
    // propagate until there remain no unit clauses or a conflict occurs
    while (currentState != SolverState.CONFLICT && !toPropagate.isEmpty()) {

      // find the next literal to propagate
      int literalToPropagate = toPropagate.pop();
      if (ASSERTS_ENABLED && trail.values[Math.abs(literalToPropagate)] == -literalToPropagate) {
        throw new IllegalStateException("Assertion failed");
      }

      assignmentNum++;

      // notify the databases so that they can perform unit propagation
      dbStore.assertLiteral(literalToPropagate);
    }

    // at this point, propagation is over. If no conflict or restart,
    // search can continue.
  }

  /** Triggers an event of forget(). */
  private void triggerForgetEvent() {
    if (ASSERTS_ENABLED && currentState != SolverState.UNKNOWN) {
      throw new IllegalStateException("Assertion failed");
    }

    for (int i = 0; i < numForgetModules; i++) {
      forgetModules[i].onForget();
    }
  }

  /**
   * Triggers an event for assertion of a literal.
   *
   * @param literal the literal asserted
   * @param newLevel the new level, after assertion. It must be strictly greater than currentLevel.
   */
  private void triggerAssertEvent(int literal, int newLevel) {
    if (ASSERTS_ENABLED && newLevel <= currentLevel) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && currentState != SolverState.UNKNOWN) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && Math.abs(literal) > maxVariable) {
      throw new IllegalStateException("Assertion failed");
    }

    currentLevel = newLevel;

    // set the literal
    trail.assertLiteral(literal, currentLevel);

    // call modules
    for (int i = 0; i < numAssertionModules; i++) {
      assertionModules[i].onAssertion(literal, currentLevel);
    }

    // watch for unit clauses
    dbStore.assertLiteral(literal);

    // propagate unit clauses
    unitPropagate();
  }

  /**
   * Tells the SAT-solver to return to a normal state after a conflict has been solved (backjump or
   * restart).
   */
  public void triggerIdleEvent() {

    if (ASSERTS_ENABLED
        && !explanationClause.isEmpty()
        && explanationClause.isUnsatisfiableIn(trail)) {
      throw new IllegalStateException("Assertion failed");
    }

    currentState = SolverState.UNKNOWN;

    // if literals to propagate remain, they are obsolete
    toPropagate.clear();
  }

  /**
   * Triggers an event of learning.
   *
   * @param clauseToLearn the clause which is learnt
   */
  public void triggerLearnEvent(MapClause clauseToLearn) {
    if (ASSERTS_ENABLED && currentState != SolverState.UNKNOWN) {
      throw new IllegalStateException("Assertion failed");
    }

    if (clauseToLearn.isEmpty()) {
      logc("tried to learn an empty clause");
      return;
    }

    if (ASSERTS_ENABLED && clauseToLearn.isUnsatisfiableIn(trail)) {
      throw new IllegalStateException("Assertion failed");
    }

    // add the clauseToLearn
    addClause(clauseToLearn.toIntArray(pool), false);

    unitPropagate();
  }

  /**
   * Triggers a conflict. The next step of the research should be conflict learning and then
   * backjumping.
   *
   * @param clause an unsatisfiable clause.
   */
  public void triggerConflictEvent(MapClause clause) {
    if (ASSERTS_ENABLED && currentState == SolverState.CONFLICT) {
      throw new IllegalStateException("Assertion failed");
    }
    if (ASSERTS_ENABLED && !clause.isUnsatisfiableIn(trail)) {
      throw new IllegalStateException("Assertion failed");
    }

    currentState = SolverState.CONFLICT;

    // inform modules
    for (int i = 0; i < numConflictModules; i++) {
      conflictModules[i].onConflict(clause, currentLevel);
    }

    // remember explanation
    explanationClause = clause;
    // clean toPropagate
    toPropagate.clear();

    if (currentLevel > 0) {
      conflictLearning.applyExplainUip(explanationClause);

      // notify modules
      for (int i = 0; i < numExplanationModules; i++) {
        explanationModules[i].onExplain(explanationClause);
      }

    } else {
      if (ASSERTS_ENABLED && currentLevel != 0) {
        throw new IllegalStateException("Assertion failed");
      }

      // conflict at level 0 is UNSAT !
      triggerUnsatEvent();
    }
  }

  /**
   * Triggers a unit propagation event. This keeps the same level.
   *
   * @param literal the unique unset literal, which must be true for the clause to be satisfied
   * @param unitClauseId the unique id of the unit clause that propagates
   */
  public void triggerPropagateEvent(int literal, int unitClauseId) {
    if (ASSERTS_ENABLED && Math.abs(literal) > maxVariable) {
      throw new IllegalStateException("Assertion failed");
    }

    // inform the trail now
    trail.assertLiteral(literal, currentLevel, unitClauseId);

    // modules
    for (int i = 0; i < numPropagateModules; i++) {
      propagateModules[i].onPropagate(literal, unitClauseId);
    }

    // schedule literal to be propagated
    toPropagate.add(literal);
  }

  /**
   * Triggers an event to backjump.
   *
   * @param level the level to backjump to
   */
  public void triggerBackjumpEvent(int level) {
    if (ASSERTS_ENABLED && level >= currentLevel) {
      throw new IllegalStateException("Assertion failed");
    }

    for (int i = 0; i < numBackjumpModules; i++) {
      backjumpModules[i].onBackjump(currentLevel, level);
    }

    // unset everything above level
    trail.backjump(level);
    dbStore.backjump(level);

    toPropagate.clear();

    currentLevel = level;
  }

  /** Triggers an event of restart. */
  public void triggerRestartEvent() {
    if (ASSERTS_ENABLED && currentLevel <= 0) {
      throw new IllegalStateException("Assertion failed");
    }
    int level = currentLevel;

    for (int i = 0; i < numRestartModules; i++) {
      restartModules[i].onRestart(level);
    }

    // a restart *is* a backjump to level 0
    triggerBackjumpEvent(0);

    // good time to forget clauses
    if (mustForget) {
      triggerForgetEvent();
    }

    triggerIdleEvent();
  }

  /** To trigger if the problem is found to be satisfiable. */
  public void triggerSatEvent() {
    currentState = SolverState.SATISFIABLE;

    toPropagate.clear();

    for (int i = 0; i < numSolutionModules; i++) {
      solutionModules[i].onSolution(true);
    }

    stop();
  }

  /** To trigger if the problem is found to be not satisfiable. */
  public void triggerUnsatEvent() {
    currentState = SolverState.UNSATISFIABLE;

    toPropagate.clear();

    for (int i = 0; i < numSolutionModules; i++) {
      solutionModules[i].onSolution(false);
    }

    stop();
  }

  /**
   * Remembers that @param s is associated with the current time (in ms).
   *
   * @param s the mark of current time
   */
  public void markTime(String s) {
    timeMap.put(s, System.currentTimeMillis());
  }

  /**
   * Get the time associated with given mark, or 0 if none.
   *
   * @param s the mark
   * @return the time associated with given mark, or 0 if none
   */
  public long getTime(String s) {
    if (timeMap.containsKey(s)) {
      return timeMap.get(s);
    }
    return 0;
  }

  /**
   * Gets the time difference (in ms) between now and the mark.
   *
   * @param s the mark
   * @return the time elapsed since mark, in ms
   */
  public long getTimeDiff(String s) {
    if (!timeMap.containsKey(s)) {
      return 0;
    } else {
      return System.currentTimeMillis() - timeMap.get(s);
    }
  }

  /*
   * in case the solver reached a solution
   */

  /**
   * Logs important messages in comments.
   *
   * @param s the message
   * @param args the arguments for the message
   */
  public void logc(String s, Object... args) {
    if (verbosity > 0) {
      logStream.print("c ");
      logStream.printf(s, args);
      logStream.println();
    }
  }

  /**
   * Logs less important messages, in comments.
   *
   * @param level verbosity level
   * @param s the message
   * @param args the arguments for the message
   */
  public void logc(int level, String s, Object... args) {
    if (verbosity >= level) {
      logStream.print("c ");
      logStream.printf(s, args);
      logStream.println();
    }
  }

  /**
   * Checks if the solver has found a solution.
   *
   * @return true if the solver reached a solution
   */
  public boolean hasSolution() {
    return currentState == SolverState.SATISFIABLE || currentState == SolverState.UNSATISFIABLE;
  }

  /** Prints the current solution on standard output. */
  public void printSolution() {

    if (ASSERTS_ENABLED && !hasSolution()) {
      throw new IllegalStateException("Assertion failed");
    }
    IO.println("s " + SolverState.show(currentState));

    // for satisfiable instances, print certificate
    if (currentState == SolverState.SATISFIABLE) {
      int count = 0;
      StringBuilder sb = new StringBuilder();
      sb.append("v ");
      for (int i = 0; i < trail.size(); i++) {
        int varIdx = trail.assertionStack.array[i];
        sb.append(trail.values[varIdx]);
        sb.append(' ');
        // if line is full, print it and begin another
        if (++count > 20) {
          IO.println(sb.toString());
          sb = new StringBuilder();
          sb.append("v ");
          count = 0;
        }
      }
      sb.append(0);
      IO.println(sb.toString());
    }
  }

  /**
   * Before exiting, we must know which return code we must give.
   *
   * @return the return code to exit with
   */
  public int getReturnCode() {
    return switch (currentState) {
      case SolverState.UNSATISFIABLE -> 20;
      case SolverState.SATISFIABLE -> 10;
      default -> 0;
    };
  }

  @Override
  public String toString() {
    return "solver ["
        + "dbs="
        + dbStore.currentIndex
        + ","
        + "vars="
        + maxVariable
        + ","
        + "state="
        + currentState
        + "]";
  }

  /**
   * Initializes the core component.
   *
   * @param core the solver core (must be this instance)
   */
  public void initialize(Core core) {
    if (ASSERTS_ENABLED && core != this) {
      throw new IllegalStateException("Assertion failed");
    }
  }
}
