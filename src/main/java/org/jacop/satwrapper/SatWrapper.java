/*
 * SatWrapper.java
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

package org.jacop.satwrapper;

import java.io.BufferedWriter;
import java.util.*;

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
import org.jacop.satwrapper.translation.SatCPBridge;
import org.jacop.satwrapper.translation.SimpleCpVarDomain;

/*
 * Global TODO:
 * - special database for AllDifferent constraint (efficient propagation without
 * a clique of n^2 clauses to represent difference on n variables). To explain
 * propagations, this database could use a bijection f from NxN to N, in order
 * to be able to retrieve the assertion 'x!=y' from f(x,y) to get efficient
 * resolution (and hence learning).
 */


/**
 * wrapper to communicate between SAT solver and CP solver.
 * It listens for SAT conflicts, so that it can force the CP solver to
 * backtrack until the conflict is resolved in SAT.
 * It listens to propagations, to know which literals are asserted in SAT, to
 * report those assertions on CP variables domains.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */
public final class SatWrapper extends Constraint implements ConflictListener, ExplanationListener, StartStopListener, SolutionListener,
    Stateful, SatisfiedPresent {

    // empty == true if no cluases has been added
    boolean empty = true;

    // sat solver instance
    public Core core;

    /*
     * TODO : a way to add those only if needed
     */
    // keep track of literals activity, and give search advices (optional)
    public ActivityModule activity = null;

    // guide assertions
    public HeuristicAssertionModule assertionModule = null;

    // association from CP variables to boolean variables
    //public HashMap<IntVar, CpVarDomain<? extends IntVar>> cpVarToDomain =
    //	new HashMap<IntVar, CpVarDomain<? extends IntVar>>();
    // TODO : find more efficient ? hard, because IntVar has no unique ID

    // association (boolean variable) -> LiteralRange (and so, IntVar)
    public SatCPBridge[] boolVarToDomains = new SatCPBridge[50];

    // the change listene to plug in the SAT solver
    public SatChangesListener satChangesListener;

    // store this constraint belongs to
    public Store store;

    // pool of int[]
    public MemoryPool pool;

    // the DomainClausesDatabase, if any
    public DomainClausesDatabase domainDatabase;

    // the translator of domains
    public DomainTranslator domainTranslator;

    // registered CP variables
    public final Set<IntVar> registeredVars = new HashSet<IntVar>();

    // SAT level to backjump to if failure
    public int levelToBackjumpTo = 0;

    // maps SAT levels to CP levels and conversely
    public Integer[] satToCpLevels = new Integer[5];
    public Integer[] cpToSatLevels = new Integer[5];

    // level of verbosity (the higher, the more verbose)
    public int verbosity = 0;

    // the trail of the solver
    private Trail trail;

    // current level for SAT solver
    private int currentSatLevel = 0;

    // private final ArrayList<Var> registeredVarsArray = new ArrayList<Var>();

    // model clauses waiting to be added to the SAT solver
    private final ArrayDeque<int[]> modelClausesToAdd = new ArrayDeque<int[]>();

    // next literals to assert during consistency()
    private IntQueue toAssertLiterals;

    // to remember which clause we should learn at next conflict resolution
    private MapClause clauseToLearn;

    // set to true between conflict and explanation
    private boolean mustBacktrack = false;

    // did the solver reach a solution?
    private boolean hasSolution = false;

    public void register(IntVar result) {
        register(result, true);
    }

    /**
     * registers the variable so that we can use it in SAT solver
     *
     * @param variable  the CP IntVar variable
     * @param translate indicate whether to use == or {@literal <=}
     */
    public void register(IntVar variable, boolean translate) {

        if (!registeredVars.contains(variable)) {

            registeredVars.add(variable);
            //	registeredVarsArray.add(variable);

            // tell the Sat Change listener
            satChangesListener.ensureAccess(variable);

            // tell the store we watch this variable
            variable.putModelConstraint(this, IntDomain.BOUND);

            variable.satBridge = new SimpleCpVarDomain(this, variable, translate);
            assert log(this, "create default domain", variable.satBridge);

        }

    }

    /**
     * The point where all operations are effectively done in the SAT solver,
     * until no operation remains or a conflict occurs
     */
    @Override public void consistency(Store store) {

        if (empty)
            return;

        if (mustBacktrack) {
            core.toPropagate.clear();
            toAssertLiterals.clear();
            satChangesListener.clear();
            mustBacktrack = false;
            throw Store.failException;
        }


        assert !mustBacktrack;

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

        // TODO : some flag to disable queueVariable() during propagation ?
        // XXX NOTE : remember to set this flag to false in case of conflict
		
		/*
		 * take literals that must be asserted, and assert each of them
		 */
        while (!toAssertLiterals.isEmpty()) {

            // do assert a literal, and propagate other literals if needed
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

        if (!toAssertLiterals.isEmpty())
            consistency(store);

    }

    /**
     * assert the next literal from toAssertLiterals
     */
    private void processOneLiteral() {
        assert !toAssertLiterals.isEmpty();

        // take the next literal (already set literals are ignored)
        int literal = toAssertLiterals.pop();
        assert literal != 0;
        if (trail.isSet(Math.abs(literal))) {
            if (trail.values[Math.abs(literal)] != literal) {
                toAssertLiterals.clear();
                satChangesListener.clear();
                core.toPropagate.clear();
                throw Store.failException;
            }
            // assert trail.values[Math.abs(literal)] == literal; // not unsat
            assert log(this, "literal " + literal + " already set (to " + trail.values[Math.abs(literal)] + ")");

            return;
        }

        addSatLevel();

        // print what literal we assert, and its meaning
        //log(this, "wrapper assert literal "+literal+
        //		" at (cp level " + store.level +
        //		", sat level "+currentSatLevel+
        //		") standing for "+showLiteralMeaning(literal));

        // trigger propagation in *SAT-solver*
        core.assertLiteral(literal, currentSatLevel);

    }

    /**
     * adds one level for SAT side, and remembers the association between
     * CP and SAT levels
     */
    private void addSatLevel() {
        currentSatLevel++;

        // TODO: inline the resizing of arrays

        // store the associations
        cpToSatLevels = Utils.ensure(cpToSatLevels, store.level);
        satToCpLevels = Utils.ensure(satToCpLevels, currentSatLevel);
        cpToSatLevels[store.level] = currentSatLevel;
        satToCpLevels[currentSatLevel] = store.level;
    }

    /**
     * wrapper listens for conflicts.
     */

    public void onConflict(MapClause clause, int level) {
        satChangesListener.clear();
        toAssertLiterals.clear();

        mustBacktrack = true;

        assert log(this, "*** conflict occurred at sat level " + level);

        // wait for the explanation
    }

    /**
     * wrapper listens for explanations, to know how deep to backtrack
     */

    public void onExplain(MapClause explanation) {
        assert mustBacktrack;
        assert core.explanationClause == explanation;

        // get clause to learn after backjump
        clauseToLearn = explanation;

        assert log(this, "*** must learn explanation %s meaning %s", explanation, showClauseMeaning(explanation));
        assert log(this, "trail: " + core.trail);

        // perform failure right now (we should be during consistency())

    }


    public void onSolution(boolean satisfiable) {
        hasSolution = true;
    }

    /**
     * when the CP solver decides to remove a level, the wrapper must force
     * the SAT solver to backtrack accordingly, to keep mappings between the
     * two search trees consistent.
     * This is also the place where the wrapper can decide that a conflict in
     * the SAT solver has been solved.
     */
    @Override public void removeLevel(int cpLevel) {

        // remove things to be asserted in SAT, clear some things...
        toAssertLiterals.clear();
        core.toPropagate.clear();

        // this CP level is of no concern to us
        if (cpLevel >= cpToSatLevels.length || cpToSatLevels[cpLevel] == null)
            return;

        // find the previous CP level that makes sense for the wrapper (-1 if none)
        int previousCpLevel = -1;
        for (int i = cpLevel - 1; i >= 0; --i) {
            if (cpToSatLevels[i] != null) {
                previousCpLevel = i;
                break;
            }
        }
        //log(this, "remove cp level "+cpLevel +
        //		" (previous : "+previousCpLevel+")");

        // this CP level does not correspond to anything anymore
        cpToSatLevels[cpLevel] = null;
        // the new maximum SAT level
        int newMaxSatLevel = (previousCpLevel == -1) ? 0 : cpToSatLevels[previousCpLevel];
        assert newMaxSatLevel >= 0;

        if (newMaxSatLevel != currentSatLevel) {

            assert currentSatLevel > newMaxSatLevel;
            // we are not at the SAT level we should be, so backjump to reach it

            assert log(this, "solver backjumps from %d to %d", currentSatLevel, newMaxSatLevel);

            assert log(this, "core SAT level %d", core.currentLevel);

            // do the real backjump
            core.backjumpToLevel(newMaxSatLevel);
            currentSatLevel = core.currentLevel;
            assert currentSatLevel == newMaxSatLevel;

            if (clauseToLearn != null) {

                if (clauseToLearn.isUnsatisfiableIn(trail))
                    mustBacktrack = true;
                else {
                    mustBacktrack = false;
                }

            }
            //			else {
            //				core.triggerIdleEvent();
            //			}

        }

    }

    /*
     * this may be called many times without consistency(), or be
     * followed by a removeLevel(), so do not assume anything and just
     * queue things to be asserted
     */
    @Override public void queueVariable(int level, Var var) {

	    /* KK: Do not queue variable when this constraint (wrapper) executes
	     *     its consistency method
	     */
        if (store.currentConstraint != null)
            if (store.currentConstraint.equals(this))
                return;

	        /*
		 * update ranges for this variable (assert some literals).
		 * those operations must not be executed here (we must avoid
		 * failure), but rather be scheduled for being executed at next call to
		 * consistency()
		 */
        assert registeredVars.contains(var);
        assert log(this, "queue variable " + var + " at CP level " + level);

        // this must be a SatVar
        assert IntVar.class.isInstance(var);
        @SuppressWarnings("unchecked") IntVar v = (IntVar) var;  // cast it in an IntVar

        if (v.singleton()) {
            // singleton => assign this variable to the unique value
            int lit = cpVarToBoolVar(v, v.domain.value(), true);
            setBoolVariable(lit, true);

        } else {
            // let us check the domain bounds
            int lower = v.domain.min();
            int upper = v.domain.max();
            assert upper - lower >= 1; // otherwise, singleton

            int lowerLit = cpVarToBoolVar(v, lower - 1, false);
            int upperLit = cpVarToBoolVar(v, upper, false);

            // if those literals are not yet set, just add them
            if (lowerLit != 0 && !trail.isSet(lowerLit))
                setBoolVariable(lowerLit, false);
            if (upperLit != 0 && !trail.isSet(upperLit))
                setBoolVariable(upperLit, true);
        }
    }

    /**
     * called when a boolean variable is set to some boolean value
     *
     * @param variable the boolean variable
     * @param value    the value (true or false) of this variable
     */
    private void setBoolVariable(int variable, boolean value) {
        // notify the constraint clauses database, for propagations
        assert variable > 0;
        int literal = value ? variable : -variable;

        toAssertLiterals.add(literal);
    }

    @Override public int getConsistencyPruningEvent(Var var) {
        return IntDomain.BOUND;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    /**
     * asks the solver for which literal is the most active. It will return
     * a literal, which can be transformed into a variable and a value from
     * the variable domain. Useful when the CP solver does not know which
     * variable to set to continue research
     *
     * @return a literal corresponding to some possible (variable,value)
     */
    public int getMostActiveLiteral() {
        int lit = assertionModule.findNextVar();
        return lit;
    }

    /**
     * (for debug) show what a literal means
     *
     * @param literal literal for showing its meaning
     * @return literal meaning
     */
    public String showLiteralMeaning(int literal) {
        if (!isVarLiteral(literal))
            return "nothing";

        return "(" + boolVarToCpVar(literal) + ")" + (isEqualityBoolVar(literal) ? (literal > 0 ? "=" : "!=") : (literal > 0 ? "<=" : ">"))
            + boolVarToCpValue(literal);
    }

    public String showClauseMeaning(Iterable<Integer> literals) {
        StringBuilder answer = new StringBuilder();
        for (int i : literals)
            answer.append(showLiteralMeaning(i)).append(", ");
        return answer.toString();
    }

    @Override public String id() {
        return getClass().getName();
    }

    @Override public void removeConstraint() {
		/*
		 * stop solver, and clean up things
		 */
        core.stop();
        core = null;  // garbage collect
    }

    public boolean satisfied() {
        return (hasSolution || core.currentState == SolverState.SATISFIABLE);
    }

    @Override public String toString() {
        return getClass().getName();
    }

    @Override public void increaseWeight() {
    }

    @Override public Set<Var> arguments() {
        return new HashSet<>(registeredVars);
    }

    /**
     * to add some module to the solver
     *
     * @param module the module to add
     */
    public final void addSolverComponent(SolverComponent module) {
        core.addComponent(module);
    }

    /**
     * add a component
     *
     * @param module the component
     */
    public final void addWrapperComponent(WrapperComponent module) {
        module.initialize(this);
    }

    /**
     * asks the solver to forget useless clauses, to free memory
     */
    public final void forget() {
        core.forget();
    }

    /**
     * add model (globally valid) clause to solver, in a delayed fashion
     *
     * @param clause the clause to add
     */
    public final void addModelClause(Collection<Integer> clause) {
        int[] toAdd = pool.getNew(clause.size());
        int index = 0;
        for (int i : clause)
            toAdd[index++] = i;
        modelClausesToAdd.add(toAdd);
    }

    public final void addModelClause(int[] clause) {

        empty = false;

        modelClausesToAdd.add(clause);
    }

    /**
     * add the constraint to the wrapper (ie, constraint.imposeToSat(this))
     *
     * @param constraint the constraint to add
     */
    public final void impose(Constraint constraint) {

        System.err.println("impose constraint in SatWrapper is not defined");
        throw new RuntimeException();

        // constraint.imposeToSat(this);
    }

    @Override public final void impose(Store store) {
        this.store = store;

        // make solver quiet, if not debug
        if (!Store.debug)
            core.verbosity = 0;

        // be warned in case of backtrack
        store.registerRemoveLevelListener(this);

        store.addChanged(this);
        // watch variables
    }


    /**
     * given a CP variable and a value, retrieve the associated boolean literal
     * for either 'variable = value' or either 'variable {@literal <=} value'
     *
     * @param variable   the CP variable
     * @param value      a value in the range of this variable
     * @param isEquality a boolean, true if we want the literal that stands for
     *                   'x=d', false for 'x{@literal <=}d'
     * @return the corresponding literal, or 0 if it is out of bounds
     */
    public final int cpVarToBoolVar(IntVar variable, int value, boolean isEquality) {

        SatCPBridge range = variable.satBridge;

        assert range != null;

        if (value < range.min || value > range.max) {
            //System.out.println("Value for " + variable + " is out of bounds for value " + value);
            return 0;
        }
        return range.cpValueToBoolVar(value, isEquality);

    }

    /**
     * returns the CpVarDomain associated with this literal
     *
     * @param literal the boolean literal
     * @return a range
     */
    public final SatCPBridge boolVarToDomain(int literal) {
        int var = Math.abs(literal);
        SatCPBridge range = boolVarToDomains[var];
        return range;
    }

    /**
     * get the IntVar back from a literal
     *
     * @param literal the literal
     * @return IntVar represented by the literal
     */
    public final IntVar boolVarToCpVar(int literal) {
        assert isVarLiteral(literal);

        int var = Math.abs(literal);
        SatCPBridge range = boolVarToDomains[var];
        return range.variable;
    }

    /**
     * transform a literal 'x=v' into a value 'v' for some CP variable
     *
     * @param literal literal to be transformed to value it represents
     * @return the value represented by this literal
     */
    public final int boolVarToCpValue(int literal) {
        assert isVarLiteral(literal);

        int var = Math.abs(literal);
        // find which range this literal belongs to
        SatCPBridge range = boolVarToDomains[var];
        return range.boolVarToCpValue(var);
    }

    /**
     * checks if the boolean variable represents an assertion 'x=v' or 'x{@literal <=}v'
     *
     * @param literal the boolean literal
     * @return true if the literal represents a proposition 'x=v', false if
     * it represents 'x{@literal <=}v'
     */
    public final boolean isEqualityBoolVar(int literal) {
        assert isVarLiteral(literal);
        int var = Math.abs(literal);
        IntVar variable = boolVarToCpVar(literal);
        SatCPBridge range = variable.satBridge;
        return range.isEqualityBoolVar(var);
    }

    /**
     * checks if this literal corresponds to some CP variable
     *
     * @param literal the literal
     * @return true if this literal stands for some 'x=v' or 'x{@literal <=}v' proposition
     */
    public final boolean isVarLiteral(int literal) {
		/*
		 * we must ensure it is very fast (called very often)
		 */
        int var = Math.abs(literal);
        if (var == 0 || var >= boolVarToDomains.length)
            return false;
        return boolVarToDomains[var] != null;
    }

    /**
     * log method, similar to printf.
     * Example: wrapper.log(this, "%s is %d", "foo", 42);
     *
     * @param o      the object that logs something (use <code>this</code>)
     * @param format the format string (the message, if no formatting)
     * @param args   the arguments to fill in the format
     * @return always true
     */
    public boolean log(Object o, String format, Object... args) {
        if (verbosity >= 1) {
            String msg = String.format(format, args);
            System.out.printf("[%s] %s%n", o, msg);
        }
        return true;
    }


    public void onStart() {
        assert core != null;
        assert core.dbStore != null;
        // due to some dependencies problems, we cannot access the database
        // before this point
    }


    public void onStop() {
    }

    /**
     * creates everything in the right order
     */
    public SatWrapper() {
        queueIndex = 1;

        // empty config
        Config config = Config.defaultConfig();

        // add itself as a component of the Core
        config.mainComponents.add(this);

        // be *SURE* the constraint db is at first position
        domainDatabase = new DomainClausesDatabase();
        domainDatabase.initialize(this);
        config.clausesDatabases.add(0, domainDatabase);

        // many detail
        config.timeout = 0;
        config.verbosity = this.verbosity;
        config.debug = false;

        // create solver with this config
        core = new Core(config);

        // setup everything
        core.start();

    }

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

    public void toCNF(BufferedWriter output) throws java.io.IOException {

        core.dbStore.toCNF(output);

    }

}
