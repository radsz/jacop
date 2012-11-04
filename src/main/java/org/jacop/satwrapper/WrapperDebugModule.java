package org.jacop.satwrapper;

import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.modules.interfaces.AssertionListener;
import org.jacop.jasat.modules.interfaces.BackjumpListener;
import org.jacop.jasat.modules.interfaces.ClauseListener;
import org.jacop.jasat.modules.interfaces.ConflictListener;
import org.jacop.jasat.modules.interfaces.ExplanationListener;
import org.jacop.jasat.modules.interfaces.ForgetListener;
import org.jacop.jasat.modules.interfaces.PropagateListener;
import org.jacop.jasat.modules.interfaces.SolutionListener;
import org.jacop.jasat.modules.interfaces.StartStopListener;
import org.jacop.jasat.utils.Utils;


/**
 * a class used to debug, but with additional data
 * @author simon
 *
 */
public final class WrapperDebugModule implements AssertionListener,
		BackjumpListener, ConflictListener, PropagateListener,
		SolutionListener, ForgetListener, ExplanationListener, ClauseListener,
		StartStopListener, WrapperComponent {

	private Core core;
	private MapClause mapClause = new MapClause();
	
	// the associate wrapper
	private SatWrapper wrapper;

	
	public void onRestart(int oldLevel) {
		printLine(true);
		core.logc(3, "restart from level %d <=> CP level %d",
				oldLevel, wrapper.store.level);
		printLine(false);
		printBlank();
	}

	
	public void
	onConflict(MapClause conflictClause, int level) {
		printLine(true);
		core.logc(3, "conflict at level "+level);
		core.logc("conflict clause : "+ conflictClause+" meaning "
				+wrapper.showClauseMeaning(conflictClause));
		printLine(false);
		printBlank();
	}

	
	public void onBackjump(int oldLevel, int newLevel) {
		printLine(true);
		core.logc(3, "backjump from "+oldLevel+"( CP "+
				wrapper.satToCpLevels[oldLevel]+") to "+newLevel+
				" (CP "+wrapper.satToCpLevels[newLevel]+")");
		printLine(false);
		printBlank();
	}

	
	public void onAssertion(int literal, int level) {
		printLine(true);
                
                if (literal == 26 && level == 1)
                    Thread.dumpStack();
                
		core.logc(3, "(at SAT level "+level +", CP level "+ wrapper.store.level+
				") assertion : "+literal+" meaning "+
				wrapper.showLiteralMeaning(literal));
		printLine(false);
		printBlank();
	}

	
	public void onPropagate(int literal, int clauseId) {
		printLine(true);
		core.logc(3, "propagate at level %d literal %d meaning %s",
				core.currentLevel, literal, wrapper.showLiteralMeaning(literal));
		// very dirty hack
		if (core.dbStore.uniqueIdToDb(clauseId) == 0)
			core.logc(3, "cause: special database");
		else {
			mapClause.clear();
			core.dbStore.resolutionWith(clauseId, mapClause);
			core.logc(3, "cause: " + mapClause + " meaning "
							+ wrapper.showClauseMeaning(mapClause));
		}
		printLine(false);
		printBlank();
	}

	
	public void onSolution(boolean satisfiable) {
		printLine(true);
		core.logc(3, "current level : "+core.currentLevel);
		int numOfSetVar = core.trail.size();
		core.logc(3, "number of set vars : "+numOfSetVar);
		core.logc(3, "solver state : "+core.currentState);
		printLine(false);
		printBlank();
	}

	
	public void onExplain(MapClause explanation) {
		printLine(true);
		core.logc("explanation clause : "+ explanation+ " meaning "+
				wrapper.showClauseMeaning(explanation));
		printTrail( "var state :          ", explanation);
		printLine(false);
		printBlank();
	}

	
	public void onClauseAdd(int[] clause, int clauseId, boolean isModelClause) {
		String c = Utils.showClause(clause);
		mapClause.clear();
		mapClause.addAll(clause);
		core.logc(3, "add clause "+(isModelClause ? "(model) ":"(learnt) ")+c
				+" at level "+core.currentLevel+
				" meaning "+wrapper.showClauseMeaning(mapClause));
	
	}

	
	public void onClauseRemoval(int clauseId) {
		core.logc(3, "remove clause "+clauseId);
	}

	
	public void onForget() {
		printLine(true);
		core.logc(3, "forget() called");
		printLine(false);
		printBlank();
	}

	
	public void onStart() {
		printLine(true);
		core.logc(3, "solver started at "+core.getTime("start"));
		printLine(false);
		printBlank();
	}

	public void onStop() {
		printLine(true);
		core.logc(3, "solver stopped at "+core.getTime("stop"));
		printLine(false);
		printBlank();
	}

	private void printLine(boolean start) {
		if (start)
			core.logc(3, "/==================================");
		else
			core.logc(3, "\\==================================");
	}

	private void printBlank() {
		core.logc(3, "");
	}

	private void printTrail(String prefix, MapClause clause) {
		StringBuilder sb = new StringBuilder().append("[ ");
		for (int var : clause.literals.keySet()) {
			int value = core.trail.values[var];
			if (value >= 0)
				sb.append(' ');
			sb.append(value);
			sb.append(' ');
		}
		core.logc(3, prefix + sb.append(']'));
	}

	public void initialize(Core core) {
		this.core = core;
	
		core.assertionModules[core.numAssertionModules++] = this;
		core.backjumpModules[core.numBackjumpModules++] = this;
		core.conflictModules[core.numConflictModules++] = this;
		core.forgetModules[core.numForgetModules++] = this;
		core.propagateModules[core.numPropagateModules++] = this;
		core.restartModules[core.numRestartModules++] = this;
		core.solutionModules[core.numSolutionModules++] = this;
		core.explanationModules[core.numExplanationModules++] = this;
		core.clauseModules[core.numClauseModules++] = this;
		core.startStopModules[core.numStartStopModules++] = this;
	
		mapClause.clear();
		core.verbosity = 3;
	}
	
	
	public void initialize(SatWrapper wrapper) {
		this.wrapper = wrapper;
		initialize(wrapper.core);
	}

}
