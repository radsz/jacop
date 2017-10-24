/*
 * Core.java
 * <p>
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * The main solver structure, to be used either by a search component or by
 * another program that uses it for conflict learning and detection.
 *
 * This implements interfaces for being manipulated from the outside, and
 * from its components
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 *
 */
public final class Core implements SolverComponent {

    // asynchronous unit propagation
    public IntQueue toPropagate;

    // the conflict explanation clause
    public MapClause explanationClause = new MapClause();

    // used to compute throughput of the solver
    public long assignmentNum = 0;

    // do we have to forget ?
    private boolean mustForget = false;

    // the maximum variable allowed
    private int maxVariable = 0;

    // a time counter
    private Map<String, Long> timeMap = new HashMap<String, Long>();

    // is the solver stopped ?
    public boolean isStopped = false;

    // timer for scheduled events (daemon thread)
    public Timer timer = new Timer(true);

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

    // stream to log messages to
    public PrintStream logStream = System.out;

    // the current level of research
    public int currentLevel = 0;

    // current state of the solver (indicates what to do next)
    public int currentState = SolverState.UNKNOWN;

    // the conflict learning module
    public ConflictLearning conflictLearning;

    // for modules.
    public AssertionListener[] assertionModules = new AssertionListener[5];

    public BackjumpListener[] backjumpModules = new BackjumpListener[5];

    public ConflictListener[] conflictModules = new ConflictListener[5];

    public PropagateListener[] propagateModules = new PropagateListener[5];

    public SolutionListener[] solutionModules = new SolutionListener[5];

    public ForgetListener[] forgetModules = new ForgetListener[5];

    public ClauseListener[] clauseModules = new ClauseListener[5];

    public ExplanationListener[] explanationModules = new ExplanationListener[5];

    public StartStopListener[] startStopModules = new StartStopListener[5];

    public BackjumpListener[] restartModules = new BackjumpListener[5];

    public int numAssertionModules = 0;

    public int numBackjumpModules = 0;

    public int numConflictModules = 0;

    public int numPropagateModules = 0;

    public int numSolutionModules = 0;

    public int numForgetModules = 0;

    public int numClauseModules = 0;

    public int numExplanationModules = 0;

    public int numStartStopModules = 0;

    public int numRestartModules = 0;

    /**
     * adds a clause to the solver
     * @param clause  the clause to add
     * @return the unique ID of the clause
     */
    public int addModelClause(IntVec clause) {
        int[] newClause = clause.toArray();
        return addClause(newClause, true);
    }

    /**
     * same as previous, add the clause as a model clause
     * @param clause  the clause to add
     * @return the unique ID of this clause, or -1 if it is trivial
     */
    public int addModelClause(int[] clause) {
        return addClause(clause, true);
    }

    /**
     * add @param clause to the pool of clauses
     */
    private int addClause(int[] clause, boolean isModelClause) {
        int clauseId = dbStore.addClause(clause, isModelClause);

        // notify modules
        for (int i = 0; i < numClauseModules; ++i)
            clauseModules[i].onClauseAdd(clause, clauseId, isModelClause);

        return clauseId;
    }


    /**
     * predicate : can we remove the clause without breaking the correctness
     * of the solver ?
     * @param clauseId  the unique Id of the clause
     * @return true if removing the clause is allowed
     */
    public boolean canRemove(int clauseId) {
        return dbStore.canRemove(clauseId);
    }

    /**
     * removes the clause with unique Id, if possible
     * @param clauseId  the unique Id of the clause to remove
     * @return true if success, false if failure
     */
    public boolean removeClause(int clauseId) {
        if (canRemove(clauseId)) {

            // remove the clause, since this is possible
            dbStore.removeClause(clauseId);

            // notify modules
            for (ClauseListener module : clauseModules)
                module.onClauseRemoval(clauseId);

            return true;
        } else {
            return false;
        }
    }

    /**
     * decides a single step of search by setting the value of a variable
     * @param literal the literal to set true
     * @param newLevel  the current search level
     */
    public void assertLiteral(int literal, int newLevel) {
        assert newLevel > this.currentLevel;
        assert Math.abs(literal) <= maxVariable;

        triggerAssertEvent(literal, newLevel);
    }

    /**
     * tells the SAT-solver to backtrack to the given level. The level must be
     * lower or equal to the solver's current level.
     * @param level  the level to return to
     */
    public void backjumpToLevel(int level) {
        assert level < currentLevel;

        triggerBackjumpEvent(level);
    }


    /**
     * make a restart, that is, restart search from level 0.
     */
    public void restart() {
        triggerRestartEvent();
    }

    /**
     * notify all modules that we start
     */
    public void start() {
        if (isStopped)
            throw new AssertionError("should not start when already stopped");

        markTime("start");
        logc("solver starts");

        // first unit propagation (for literals propagated when clauses were added)
        unitPropagate();

        // notify modules
        for (int i = 0; i < numStartStopModules; ++i)
            startStopModules[i].onStart();

    }

    /**
     * notify all modules that we stop
     */
    public void stop() {

        if (!isStopped) {
            // read stop event
            markTime("stop");

            // notify modules
            for (int i = 0; i < numStartStopModules; ++i)
                startStopModules[i].onStop();

            // stop events
            timer.cancel();
            isStopped = true;
        }
    }

    /**
     * removes the less useful learnt clauses to free memory
     */
    public void forget() {
        mustForget = true;
    }

    /**
     * Computes at which level we should backjump to solve the conflict.
     * The solver must be in CONFLICT state.
     * @return a level lower than the current level, in which the solver
     * state would no longer be CONFLICT.
     */
    public int getLevelToBackjump() {
        assert explanationClause != null;
        return conflictLearning.getLevelToBackjump(explanationClause);
    }

    public int getLevelToBackjump(MapClause explanationClause) {
        assert explanationClause != null;
        return conflictLearning.getLevelToBackjump(explanationClause);
    }


    /**
     * gets a fresh variable that one can use for example
     * for lazy clause generation. If used, every clause added must use only
     * the variables get by this way, or a variable collision could occur.
     * @return a fresh variable
     */
    public int getFreshVariable() {
        int answer = maxVariable + 1;
        setMaxVariable(answer);
        return answer;
    }


    /**
     * get several new variables at once, more efficiently than
     * running getFreshVariable() @param number times. The variables range
     * from the returned int to the returned int + @param number - 1
     * @param number  the number of fresh variables we want
     * @return The first variable in the range of new variables
     */
    public int getManyFreshVariables(int number) {
        int answer = maxVariable + 1;
        setMaxVariable(maxVariable + number);
        return answer;
    }


    /**
     * Tells the solver what is the greatest variable in the problem
     * @param maxVariable the new maximum variable. Must not be lower than
     * solver.getMaxVariable().
     */
    public void setMaxVariable(int maxVariable) {
        //logc(3, "higher variable for solver : "+maxVariable);

        if (maxVariable > this.maxVariable) {
            this.maxVariable = maxVariable;
            trail.ensureCapacity(maxVariable);
        } else {
            logc("tried to downgrade the max var from %d to %d", this.maxVariable, maxVariable);
        }
    }


    /**
     * @return the current max variable
     */
    public int getMaxVariable() {
        return maxVariable;
    }

    /**
     * give the module access to the whole class, even if the solver is only
     * known as a ISatSolver
     * @param module  the module to add to the solver
     */
    public void addComponent(SolverComponent module) {
        module.initialize(this);
    }

    /**
     * performs propagation on all unit clauses until either :
     * - no unit clause remains
     * - a conflict occurs
     */
    public final void unitPropagate() {
        // propagate until there remain no unit clauses or a conflict occurs
        while (currentState != SolverState.CONFLICT && !toPropagate.isEmpty()) {
            assert toPropagate.size() > 0;

            // find the next literal to propagate
            int literalToPropagate = toPropagate.pop();
            assert trail.values[Math.abs(literalToPropagate)] != -literalToPropagate;

            assignmentNum++;

            // notify the databases so that they can perform unit propagation
            dbStore.assertLiteral(literalToPropagate);

        }

        assert toPropagate.isEmpty() || currentState == SolverState.CONFLICT;
        // at this point, propagation is over. If no conflict or restart,
        // search can continue.
    }

    /**
     * triggers an event of forget()
     */
    private void triggerForgetEvent() {
        assert currentState == SolverState.UNKNOWN;

        for (int i = 0; i < numForgetModules; ++i)
            forgetModules[i].onForget();
    }


    /**
     * triggers an event for assertion of a literal
     * @param literal  the literal asserted
     * @param newLevel  the new level, after assertion. It must be strictly
     * greater than currentLevel.
     */
    private void triggerAssertEvent(int literal, int newLevel) {
        assert newLevel > currentLevel;
        assert currentState == SolverState.UNKNOWN;
        assert Math.abs(literal) <= maxVariable;

        currentLevel = newLevel;

        // set the literal
        trail.assertLiteral(literal, currentLevel);

        // call modules
        for (int i = 0; i < numAssertionModules; ++i)
            assertionModules[i].onAssertion(literal, currentLevel);


        // watch for unit clauses
        dbStore.assertLiteral(literal);

        // propagate unit clauses
        unitPropagate();
    }

    /**
     * tells the SAT-solver to return to a normal state after a conflict has
     * been solved (backjump or restart)
     */
    public void triggerIdleEvent() {

        assert explanationClause.isEmpty() || !explanationClause.isUnsatisfiableIn(trail);

        //		assert explanationClause.isEmpty() || explanationClause.isUnitIn(explanationClause.assertedLiteral, trail);

        currentState = SolverState.UNKNOWN;

        // if literals to propagate remain, they are obsolete
        toPropagate.clear();
    }

    /**
     * triggers an event of learning
     * @param clauseToLearn  the clause which is learnt
     */
    public void triggerLearnEvent(MapClause clauseToLearn) {
        assert currentState == SolverState.UNKNOWN;

        if (clauseToLearn.isEmpty()) {
            logc("tried to learn an empty clause");
            return;
        }

        assert !clauseToLearn.isUnsatisfiableIn(trail);

        // add the clauseToLearn
        addClause(clauseToLearn.toIntArray(pool), false);

        unitPropagate();
    }

    /**
     * triggers a conflict. The next step of the research should be
     * conflict learning and then backjumping.
     * @param clause  an unsatisfiable clause.
     */
    public void triggerConflictEvent(MapClause clause) {
        assert currentState != SolverState.CONFLICT;
        assert clause.isUnsatisfiableIn(trail);

        currentState = SolverState.CONFLICT;

        // inform modules
        for (int i = 0; i < numConflictModules; ++i)
            conflictModules[i].onConflict(clause, currentLevel);

        // remember explanation
        explanationClause = clause;
        // clean toPropagate
        toPropagate.clear();

        if (currentLevel > 0) {
            conflictLearning.applyExplainUIP(explanationClause);

            // notify modules
            for (int i = 0; i < numExplanationModules; ++i)
                explanationModules[i].onExplain(explanationClause);

        } else {
            assert currentLevel == 0;

            // conflict at level 0 is UNSAT !
            triggerUnsatEvent();

        }
    }


    /**
     * triggers a unit propagation event. This keeps the same level.
     * @param literal  the unique unset literal, which must be true for the
     * 	clause to be satisfied
     * @param unitClauseId  the unique id of the unit clause that propagates
     */
    public void triggerPropagateEvent(int literal, int unitClauseId) {
        assert Math.abs(literal) <= maxVariable;
        // dbStore.getConflictClause(unitClauseId, localClause);
        // assert localClause.isUnit(trail);

        // inform the trail now
        trail.assertLiteral(literal, currentLevel, unitClauseId);

        // modules
        for (int i = 0; i < numPropagateModules; ++i)
            propagateModules[i].onPropagate(literal, unitClauseId);


        // schedule literal to be propagated
        toPropagate.add(literal);
    }

    /**
     * triggers an event to backjump
     * @param level  the level to backjump to
     */
    public void triggerBackjumpEvent(int level) {
        assert level < currentLevel;

        for (int i = 0; i < numBackjumpModules; ++i)
            backjumpModules[i].onBackjump(currentLevel, level);

        // unset everything above level
        trail.backjump(level);
        /**
         * @TODO, Currently nothing is done in database on backjumping, this function
         * should not be called and if any work is needed to be done it should be through
         * registered backjump modules. The trail above should be a backjump module.
         */
        dbStore.backjump(level);

        toPropagate.clear();

        currentLevel = level;
    }

    /**
     * triggers an event of restart
     */
    public void triggerRestartEvent() {
        assert currentLevel > 0;
        int level = currentLevel;

        for (int i = 0; i < numRestartModules; ++i)
            restartModules[i].onRestart(level);

        // a restart *is* a backjump to level 0
        triggerBackjumpEvent(0);

        // good time to forget clauses
        if (mustForget)
            triggerForgetEvent();

        // FIXME: is this correct? I guess so, but...
        triggerIdleEvent();
    }

    /**
     * to trigger if the problem is found to be satisfiable
     */
    public void triggerSatEvent() {
        currentState = SolverState.SATISFIABLE;

        toPropagate.clear();

        for (int i = 0; i < numSolutionModules; ++i)
            solutionModules[i].onSolution(true);

        stop();
    }


    /**
     * to trigger if the problem is found to be not satisfiable
     */
    public void triggerUnsatEvent() {
        currentState = SolverState.UNSATISFIABLE;

        toPropagate.clear();

        for (int i = 0; i < numSolutionModules; ++i)
            solutionModules[i].onSolution(false);

        stop();
    }

    /**
     * remembers that @param s is associated with the current time (in ms)
     * @param s  the mark of current time
     */
    public final void markTime(String s) {
        timeMap.put(s, System.currentTimeMillis());
    }

    /**
     * get the time associated with given mark, or 0 if none
     * @param s  the mark
     * @return the time associated with given mark, or 0 if none
     */
    public final long getTime(String s) {
        if (timeMap.containsKey(s))
            return timeMap.get(s);
        return 0;
    }

    /**
     * gets the time difference (in ms) between now and the mark
     * @param s  the mark
     * @return the time elapsed since mark, in ms
     */
    public final long getTimeDiff(String s) {
        if (!timeMap.containsKey(s))
            return 0;
        else
            return System.currentTimeMillis() - timeMap.get(s);
    }

    /**
     * logs important messages in comments
     *
     * @param s the message
     * @param args the arguments for the message
     */
    public final void logc(String s, Object... args) {
        if (verbosity > 0) {
            logStream.print("c ");
            logStream.printf(s, args);
            logStream.println();
        }
    }

    /**
     * logs less important messages, in comments
     *
     * @param level verbosity level
     * @param s the message
     * @param args the arguments for the message
     */
    public final void logc(int level, String s, Object... args) {
        if (verbosity >= level) {
            logStream.print("c ");
            logStream.printf(s, args);
            logStream.println();
        }
    }

	/*
   * in case the solver reached a solution
	 */

    /**
     * @return true if the solver reached a solution
     */
    public final boolean hasSolution() {
        return currentState == SolverState.SATISFIABLE || currentState == SolverState.UNSATISFIABLE;
    }

    /**
     * prints the current solution on standard output
     */
    public final void printSolution() {
        // TODO : clean it (factor code, avoid repetition)

        assert hasSolution();
        System.out.println("s " + SolverState.show(currentState));

        // for satisfiable instances, print certificate
        if (currentState == SolverState.SATISFIABLE) {
            int count = 0;
            StringBuffer sb = new StringBuffer();
            sb.append("v ");
            for (int i = 0; i < trail.size(); ++i) {
                int var = trail.assertionStack.array[i];
                sb.append(trail.values[var]);
                sb.append(' ');
                // if line is full, print it and begin another
                if (++count > 20) {
                    System.out.println(sb.toString());
                    sb = new StringBuffer();
                    sb.append("v ");
                    count = 0;
                }

            }
            sb.append(0);
            System.out.println(sb.toString());
        }
    }

    /**
     * before exiting, we must know which return code we must give
     * @return the return code to exit with
     */
    public final int getReturnCode() {
        switch (currentState) {
            case SolverState.UNSATISFIABLE:
                return 20;
            case SolverState.SATISFIABLE:
                return 10;
            default:
                return 0;
        }
    }

    @Override public String toString() {
        StringBuilder answer = new StringBuilder("solver [");
        answer.append("dbs=").append(dbStore.currentIndex).append(",");
        answer.append("vars=").append(maxVariable).append(",");
        answer.append("state=").append(currentState);
        return answer.append("]").toString();
    }


    /**
     * creates the solver, which in turn creates all inner components and
     * connect them together.
     *
     * @param config configuration for the solver
     */
    public Core(Config config) {
        // set the config
        assert config.check();
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
        for (SolverComponent component : config.mainComponents)
            addComponent(component);
        // and require the class of the other required components
        for (AbstractClausesDatabase database : config.clausesDatabases)
            addComponent(database);
    }

    /**
     * initializes the solver with a default configuration.
     */
    public Core() {
        this(Config.defaultConfig());  // use a default config
        logc("solver initializes with default config");
    }

    public void initialize(Core core) {
        assert core == this;
    }

}
