/**
 *  Store.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *  Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.jacop.core;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.util.SimpleHashSet;
import org.jacop.util.SparseSet;

/**
 * It is an abstract class to describe all necessary functions of any store.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class Store {

	/**
	 * It creates a logger for this class. It seeks properties in the file
	 * log4j.properties. It needs to be placed in the classpath. In eclipse
	 * project it should be in a build directory.
	 */
	
	// @todo implement logging through log4j. 
	// private static final org.apache.log4j.Logger log = Logger.getLogger(Store.class);	

	/**
	 * It specifies an empty domain. It is often used by any function which
	 * requires to return empty domain. It saves effort creation empty domain
	 * each time it is required.
	 */
	
	// public static final IntDomain emptyDomain = new IntervalDomain(0);

	/**
	 * It stores standard fail exception used when empty domain encountered.
	 */

	public final static FailException failException = new FailException();
		
	/**
	 * It specifies if some debugging information is printed.
	 */
	public static final boolean debug = true;


	/**
	 * It stores constraints scheduled for reevaluation. It does not register
	 * constraints which are already scheduled for reevaluation.
	 */

	public SimpleHashSet<Constraint>[] changed;

	/**
	 * It stores boolean variables as soon as they change (become grounded or
	 * number of constraints being attached is changed). Later each level
	 * remembers the part of the array which contains variables changed at this
	 * level (efficient backtracking).
	 */

	public BooleanVar[] changeHistory4BooleanVariables;

	/**
	 * More advanced constraints may require to be informed of a backtrack to be
	 * able to recover the older versions of the data structures. For example,
	 * the constraints can clear their queue of changed variables if a
	 * backtracks has occurred. It holds the list of constraints which want to be informed
	 * about level being removed before it has actually began.
	 */
	public ArrayList<Constraint> removeLevelListeners = new ArrayList<Constraint>(
			10);

	/**
	 * More advanced constraints may require to be informed of a backtrack to be
	 * able to recover the older versions of the data structures. For example,
	 * the constraints can clear their queue of changed variables if a
	 * backtracks has occurred. It holds the list of constraints which want to be informed
	 * about level being removed after it has been removed.
	 */
	public ArrayList<Constraint> removeLevelLateListeners = new ArrayList<Constraint>(
			10);

	/**
	 * It contains all auxilary variables created by decomposable constraints. They
	 * have to be grounded by search for a solution to be valid.
	 */
	
	public ArrayList<Var> auxilaryVariables = new ArrayList<Var>();

	/**
	 * It stores constraint which is currently re-evaluated.
	 */
	public Constraint currentConstraint = null;

	
	/**
	 * It stores constraint that has recently failed during store.consistency() execution.
	 */
	public Constraint recentlyFailedConstraint = null;

	/**
	 * It stores current queue, which is being evaluated.
	 */

	public int currentQueue = 0;

	/**
	 * It specifies long description of the store.
	 */
	public String description = null;

	/**
	 * Id string of the store.
	 */
	public String id = "Store";

	/**
	 * It specifies the time point in the search. Every time this variable is
	 * increased a new layer of changes to the variables are recorded. This is
	 * the most important variable. It is assumed that initially this value is
	 * equal to zero. Use setLevel function if you want to play with it.
	 */
	public int level = 0;

	/**
	 * A mutable variable is a special variable which can change value during
	 * the search. In the event of backtracks the old value must be restored,
	 * therefore the store keeps information about all mutable variables.
	 */

	protected ArrayList<MutableVar> mutableVariables = new ArrayList<MutableVar>(
			100);

	/**
	 * This variable specifies if there was a new propagation. Any change to any
	 * variable will setup this variable to true. Usefull variable to discover
	 * the idempodence of the consistency propagator.
	 */
	
//	public boolean newPropagation = false;
	
	public boolean propagationHasOccurred = false;

	/**
	 * It stores the number of constraints which were imposed to the store.
	 */
	
	protected int numberOfConstraints = 0;

	/**
	 * It specifies the current pointer to put next changed boolean variable. It
	 * has to be maintained manually (within removeLevel function).
	 */

	public TimeStamp<Integer> pointer4GroundedBooleanVariables = null;

	/**
	 * It stores number of queues used in this store. It has to be at least 1.
	 * No constraint can be imposed with queue index greater or equal this
	 * number.
	 */

	// TODO, create setQueue function so all data structures are properly updated
	// upon changing the number of queues.
	public int queueNo = 5;

	/**
	 * Some constraints maintain complex data structure based on function
	 * recentDomainPruning of a variable, this function for proper functioning
	 * requires to raise store level after imposition and before any changes to
	 * variables of this constraint occur. This flag is set by constraints at
	 * imposition stage.
	 */

	public boolean raiseLevelBeforeConsistency = false;

	/**
	 * It specifies if evaluated constraint should be checked for satisfiability
	 * and removed if it occurs. This checks costs time but can significantly
	 * reduce execution time.
	 */

	protected boolean removeConstraints = false;

	
	/**
	 * It specifies if the weight of variables which are in the scope of the failure
	 * constraint should be increased.
	 */
	
	public boolean variableWeightManagement = false;
	
	/**
	 * It switches on/off debuging of remove level facilities.
	 */

	final boolean removeDebug = false;

	/**
	 * Number of variables stored within a store.
	 */

	protected int size = 0;

	/**
	 * TimeStamp variable is a simpler version of a mutable variable. It is
	 * basically a stack. During search items are push onto the stack. If the
	 * search backtracks then the old values can be simply restored. Simple and
	 * efficient way for getting mutable variable functionality for simple data
	 * types.
	 */
	protected ArrayList<TimeStamp<?>> timeStamps = new ArrayList<TimeStamp<?>>(100);

    /**
	 * This keeps information about watched constraints by given variable.
	 * Watched constraints are active all the time. Use this with care and do
	 * not be surprised if some constraints stay longer than you expect. It can
	 * be directly manipulated in any way (including setting to null if no
	 * watched constraints are being in the queue system).
	 */

	public HashMap<Var, HashSet<Constraint>> watchedConstraints;

	/**
	 * Variable given as a parameter no longer watches constraint given as
	 * parameter. This function will be called when watch is being moved from
	 * one variable to another.
	 * @param v variable at which constraint is no longer watching.
	 * @param C constraint which is no longer watched by given variable.
	 */

	public void deregisterWatchedLiteralConstraint(Var v, Constraint C) {

		watchedConstraints.get(v).remove(C);

	}

	/**
	 * Watched constraint given as parameter is being removed, no variable will
	 * be watching it.
	 * @param C constraint for which all watches are removed.
	 */
	
	public void deregisterWatchedLiteralConstraint(Constraint C) {

		for (Var v : C.arguments()) {
			HashSet<Constraint> forVariable = watchedConstraints.get(v);
			if (forVariable != null)
				forVariable.remove(C);
		}

	}
	
	/**
	 * It returns number of watches which are used to watch constraints. 
	 * 
	 * @return returns the number of watches attached to variables.
	 */
	public int countWatches() {
		
		if (watchedConstraints == null)
			return 0;
		
		int count = 0;
		
		for (Var v : watchedConstraints.keySet())
			count += watchedConstraints.get(v).size();
		
		return count;
		
	}
	
	/**
	 * It register variable to watch given constraint. This function is called
	 * either by impose function of a constraint or by consistency function of a
	 * constraint when watch is being moved.
	 * @param v variable which is used to watch the constraint.
	 * @param C the constraint being used.
	 */

	public void registerWatchedLiteralConstraint(Var v, Constraint C) {

		HashSet<Constraint> forVariable = watchedConstraints.get(v);
		
		if (forVariable != null)
			forVariable.add(C);
		else {
			forVariable = new HashSet<Constraint>();
			forVariable.add(C);
			watchedConstraints.put(v, forVariable);
		}
		
	}
	
	/**
	 * It removes all watches to constraints, therefore
	 * constraints are no longer watched, no longer part of the model.
	 */
	public void clearWatchedConstraint() {
	
		watchedConstraints.clear();
		
	}

	/**
	 * The prefix of any variable which was noname.
	 */
	protected String variableIdPrefix = "_";

	/**
	 * It stores integer variables created within a store.
	 */

	public Var[] vars;
	
	/**
	 * It allows to manage information about changed variables in 
	 * efficient/specialized/tailored manner. 
	 * 
	 */
	public BacktrackableManager trailManager;
	
	/**
	 * It specifies the default constructor of the store.
	 */
	
	public Store() {

		this(100);
		
	}

	/**
	 * It specifies the constructor of the store, which allows to decide what is
	 * the initial size of the Variable list.
	 * @param size specifies the initial number of variables.
	 */
	
	@SuppressWarnings("unchecked")
	public Store(int size) {

		vars = new Var[size];
				
		changed = new SimpleHashSet[queueNo];

		for (int i = 0; i < queueNo; i++)
			changed[i] = new SimpleHashSet<Constraint>(100);

		//trailManager = new SimpleBacktrackableManager(vars, 0);
		trailManager = new IntervalBasedBacktrackableManager(vars, this.size, 10, Math.max( size / 10, 4 ));
		
	}

	/**
	 * This function schedules given constraint for re-evaluation. This function
	 * will most probably be rarely used as constraints require reevaluation
	 * only when a variable changes.
	 * @param c constraint which needs reevaluation.
	 */

	public void addChanged(Constraint c) {
		
		propagationHasOccurred = true;

		if (c.queueIndex < currentQueue)
			currentQueue = c.queueIndex;

		changed[c.queueIndex].add(c);
		
	}


	/**
	 * This function schedules all attached (not yet satisfied constraints) for
	 * given variable for re-evaluation. This function must add all attached
	 * constraints for reevaluation but it will do it any order which suits it.
	 * @param var variable for which some pruning event has occurred.
	 * @param pruningEvent specifies the type of the pruning event.
	 * @param info it specifies detailed information about the change of the variable domain.
	 * the inputs of the currentConstraint in the manner that would validate another execution.
	 */

	public void addChanged(Var var, int pruningEvent, int info) {
		
		propagationHasOccurred = true;

		// It records V as being changed so backtracking later on can be invoked for this variable.
		recordChange(var);

		Domain vDom = var.dom();
		
		Constraint[] addedConstraints = null;
		Constraint c;

		// FIXME, BUG. it should not assume that events are from IntDomain. 
		// Who and when should add constraints to the queue?
		// TEST, now.
		
		for (int j : vDom.getEventsInclusion(pruningEvent)) {

			addedConstraints = vDom.modelConstraints[j];

			for (int i = vDom.modelConstraintsToEvaluate[j] - 1; i >= 0; i--) {

				c = addedConstraints[i];

				c.queueVariable(level, var);

				if (currentConstraint != c) {
					addChanged(c);
				}
				
			}

		}

		ArrayList<Constraint> constr = vDom.searchConstraints;

		for (int i = vDom.searchConstraintsToEvaluate - 1; i >= 0; i--) {

			c = constr.get(i);

			c.queueVariable(level, var);

			if (currentConstraint != c) {

				addChanged(c);

			}
		}

		// Watched constraints
		if (watchedConstraints != null && pruningEvent == IntDomain.GROUND) {

			HashSet<Constraint> list = watchedConstraints.get(var);

			if (list != null)
				for (Constraint con : list) {
					con.queueVariable(level, var);

					if (currentConstraint != con) {
						addChanged(con);
					}
				}
		}
		
		
	}

	/**
	 * It clears the queue of constraints which need to be reevaluated usefull
	 * if different scheme propagation scheme needs to be implemented.
	 */

	public void clearChanged() {

		while (currentQueue < queueNo)
			changed[currentQueue++].clear();

	}

	/**
	 * This function computes the consistency function. It evaluates all
	 * constraints which are in the changed queue. 
	 * @return returns true if all constraints which were in changed queue are consistent, false otherwise.
	 */

	public boolean consistency() {

		if (raiseLevelBeforeConsistency) {
			raiseLevelBeforeConsistency = false;
			setLevel(level + 1);
		}
		
		if (this.sparseSetSize > 0 && this.sparseSet == null)
			sparseSet = new SparseSet(sparseSetSize);

		try {
			
			while (currentQueue < queueNo) {
				// Selects changed constraints from changed queue
				// and evaluates them
				if (currentQueue < queueNo)
					while (!changed[currentQueue].isEmpty()) {

						currentConstraint = getFirstChanged();
						
						currentConstraint.consistency(this);

						if (removeConstraints && currentConstraint.satisfied()) {

							currentConstraint.removeConstraint();
						}
					
					}
								
				currentQueue++;
			}

		} catch (FailException f) {

			if (currentConstraint != null) {

				currentConstraint.cleanAfterFailure();

				if (variableWeightManagement)
					currentConstraint.increaseWeight();

			}

			recentlyFailedConstraint = currentConstraint;
			currentConstraint = null;

			return false;
			
		}

		currentConstraint = null;
		return true;

	}
	
	
	/**
	 * This function is called when a counter of constraints should be
	 * increased. It is most probable that this function will called from the
	 * impose function of the constraint.
	 */
	public void countConstraint() {
		numberOfConstraints++;
	}

	/**
	 * This function is called when a counter of constraints should be increased
	 * by given value. If for some reason some constraints should be counted as
	 * multiple ones than this function could be called.
	 * @param n integer by which the counter of constraints should be increased.
	 */
	public void countConstraint(int n) {
		numberOfConstraints += n;
	}

	/**
	 * This function deregisters a constraint from the listeners queue. The
	 * constraint will know that it has to re-execute its consistency function,
	 * but it will not be informed which variables has changed.
	 * @param C constraint which no longer needs to be removed when level is removed.
	 * @return true if constraint was listening beforehand, otherwise false.
	 */

	public boolean deRegisterRemoveLevelListener(Constraint C) {

		int i = removeLevelListeners.indexOf(C);

		if (i == -1)
			return false;
		else if (removeLevelListeners.remove(i) != null)
			return true;

		return false;
	}

	/**
	 * It may be used for faster retrieval of variables given their id. However, 
	 * by default this variable is not created to reduce memory consumption. If
	 * it exists then it will be used by functions looking for a variable given the name. 
	 */
	
	public HashMap<String, Var> variablesHashMap = new HashMap<String, Var>();
		
	/**
	 * This function looks for a variable with given id. It will first
	 * check the existence of a hashmap variablesHashMap to get the 
	 * variable from the hashmap in constant time. Only if the variable
	 * was not found or hashmap object was not created a linear algorithm
	 * scanning through the whole list of variables will be employed. 
	 * @param id unique identifier of the variable.
	 * @return reference to a variable with the given id.
	 */
	
	public Var findVariable(String id) {
		
		if (variablesHashMap != null) {
			
			Var key = variablesHashMap.get(id);
			
			if (key != null)
				return key;

		}
		
		for (Var v : vars)
			if (v != null && id.equals(v.id()))
				return v;
			
		return null;	
		
	}
	
	/**
	 * It loads CSP from XML file, which uses an extended version of XCSP 2.0.
	 * @param path path pointing at a file 
	 * @param filename 
	 */


	/**
	 * If a constraint is checked for satisfiability and it is satisfied then 
	 * it will not be attached to a variable anymore.
	 * @return true if constraints are checked for satisfiability. 
	 */
	public boolean getCheckSatisfiability() {
		return removeConstraints;
	}

	/**
	 * This function returns the constraint which is currently reevaluated. It
	 * is an easy way to discover which constraint caused a failure right after
	 * the inconsistency is signaled.
	 * @return constraint for which consistency method is being executed.
	 */

	public Constraint getCurrentConstraint() {
		return currentConstraint;
	}

	/**
	 * This function returns the long description of the store.
	 * @return store description.
	 */
	public String getDescription() {
		return description;
	}

	/**
	 * This function returns the constraint scheduled for re-evaluation. It
	 * returns constraints based on criteria first-in-first out. It is simple,
	 * easy, fair, and efficient way of getting constraints for reevaluation.
	 * The constraint is _removed_ from the queue, since it is assumed that they
	 * are reevaluated right away.
	 * @return first constraint which is being marked as the one which needs to be checked for consistency.
	 */

	public Constraint getFirstChanged() {

		return changed[currentQueue].removeFirst();
		
	}

	/**
	 * This function returns the id of the store.
	 * @return id of store.
	 */
	public String getName() {
		return id;
	}

    /**
	 * This function returns the prefix of the automatically generated names for
	 * noname variables.
	 * @return he prefix of the automatically generated names for noname variables.
	 */
	public String getVariableIdPrefix() {
		return variableIdPrefix;
	}

	/**
	 * This function imposes a constraint to a store. The constraint is
	 * scheduled for evaluation for the next store consistency call. Therefore,
	 * the constraint is added to queue of changed constraints.
	 * @param c constraint to be imposed.
	 */

	public void impose(Constraint c) {

		c.impose(this);

	}
	
	/**
	 * This function imposes a constraint to a store. The constraint is
	 * scheduled for evaluation for the next store consistency call. Therefore,
	 * the constraint is added to queue of changed constraints.
	 * @param c constraint to be added to specified queue.
	 * @param queueIndex specifies index of the queue for a constraint.
	 */

	public void impose(Constraint c, int queueIndex) {

		assert (queueIndex < queueNo) : "Constraint queue number larger than permitted by store.";

		c.impose(this, queueIndex);
	}

	/**
	 * In some special cases it may be beneficial to compute consistency of
	 * constraint store immediately after the constraint is imposed. This
	 * function will impose a constraint and call the consistency function of
	 * the store immediately.
	 * @param c constraint to be imposed.
	 * @throws FailException failure exception.
	 */

	public void imposeWithConsistency(Constraint c) throws FailException {

		c.impose(this);
		
		if (!consistency()) {
			throw Store.failException;
		}

	}


	/**
	 * This function imposes a decomposable constraint to a store. The decomposition is
	 * scheduled for evaluation for the next store consistency call. Therefore,
	 * the constraints are added to queue of changed constraints.
	 * @param c constraint to be imposed.
	 */

	public void imposeDecomposition(DecomposedConstraint c) {

		c.imposeDecomposition(this);
		
	}

	/**
	 * This function imposes a constraint decomposition to a store. The decomposition 
	 * constraints are scheduled for evaluation for the next store consistency call. Therefore,
	 * the constraints are added to queue of changed constraints.
	 * @param c constraint to be added to specified queue.
	 * @param queueIndex specifies index of the queue for a constraint.
	 */

	public void imposeDecomposition(DecomposedConstraint c, int queueIndex) {

		assert (queueIndex < queueNo) : "Constraint queue number larger than permitted by store.";
		
		c.imposeDecomposition(this, queueIndex);
	}

	/**
	 * In some special cases it may be beneficial to compute consistency of
	 * constraint store immediately after the decomposed constraint is imposed. This
	 * function will impose constraint decomposition and call the consistency function of
	 * the store immediately.
	 * @param c decomposed constraint to be imposed.
	 */

	public void imposeDecompositionWithConsistency(DecomposedConstraint c) {

		c.imposeDecomposition(this);
		
		if ( !consistency() ) {
			throw Store.failException;
		}


	}
	
	
	
	/**
	 * This function checks if all variables within a store are grounded. It is
	 * advised to make sure that after search all variables are grounded.
	 * 
	 * @return true if all variables are singletons, false otherwise.
	 */
	public boolean isGround() {
		for (Var v : vars)
			if (!v.singleton())
				return false;
		return true;
	}

	/**
	 * This function returns the number of constraints.
	 * @return number of constraints.
	 */

	public int numberConstraints() {
		return numberOfConstraints;
	}

	/**
	 * This function prints the information of the store to standard output
	 * stream.
	 */

	public void print() {
		System.out.println(toString());
	}

	/**
	 * Any constraint may have their own mutable variables which can be register
	 * at store and then store will be responsible for calling appropriate
	 * functions from MutableVar interface to keep the variables consistent with
	 * the search.
	 * @param value MutableVariable to be added and maintained by a store.
	 * @return the position of MutableVariable at which it is being stored.
	 */

	public int putMutableVar(MutableVar value) {
		mutableVariables.add(value);
		return mutableVariables.size() - 1;
	}

	/**
	 * Any entity (for example constraints) may have their own mutable variables
	 * (timestamps) which can be register at store and then store will be
	 * responsible for calling appropriate functions from TimeStamp class to
	 * keep the variables consistent with the search.
	 * @param value timestamp to be added and maintained by a store.
	 * @return the position of timestamp at which it is being stored.
	 */

	public int putMutableVar(TimeStamp<?> value) {
		timeStamps.add(value);
		return timeStamps.size() - 1;
	}

	/**
	 * This function is used to register a variable within a store. It will be
	 * most probably called from variable constructor. It returns the current
	 * position of fdv in a store local data structure.
	 * @param var variable to be registered.
	 * @return position of the variable at which it is being stored.
	 */
	public int putVariable(Var var) {

		Var previousVar = variablesHashMap.put(var.id(), var);
		
		assert (previousVar == null) : "Two variables have the same id " + previousVar + " " + var;
			
		if (var.index != -1) {
			if (vars[var.index] == var) {
				throw new IllegalArgumentException( "\nSetting Variable: Variable already exists: " + var.id());
			}
		}

		// boolean variables are not trailed the same fashion as int variables.
		// return default index specifying that this variable is not stored within vars array.
		if (var instanceof BooleanVar)
			return -1;
		
		if (size < vars.length) {

			vars[size] = var;
			size++;

		} else {

			Var[] oldVars = vars;
			vars = new Var[oldVars.length * 2];

			System.arraycopy(oldVars, 0, vars, 0, size);

			vars[size] = var;
			size++;

			trailManager.update(vars, size);

		}

		trailManager.setSize(size);
		
		return size - 1;
	}

	/**
	 * Any boolean variable which is changed must be recorded by store, so it
	 * can be restored to the previous state if backtracking is performed.
	 * @param recordedVariable boolean variable which has changed.
	 */

	public void recordBooleanChange(BooleanVar recordedVariable) {

		int position = pointer4GroundedBooleanVariables.value();

		if (position >= changeHistory4BooleanVariables.length) {

			BooleanVar[] temp = changeHistory4BooleanVariables;
			changeHistory4BooleanVariables = new BooleanVar[changeHistory4BooleanVariables.length * 2];
			System.arraycopy(temp, 0, changeHistory4BooleanVariables, 0,
					position);
		}

		changeHistory4BooleanVariables[position] = recordedVariable;

		pointer4GroundedBooleanVariables.update(position + 1);

	}

	
	
	
	/**
	 * Any change of finite domain variable must also be recorded, so intervals
	 * denoting changed variables can be updated.
	 * @param recordedVariable variable which has changed.
	 */

	public void recordChange(Var recordedVariable) {
                           
		// Boolean variables or other variables with index -1 are 
		// stored each time they change in the special 1D array.
		if (recordedVariable.index == -1) {
			recordBooleanChange((BooleanVar) recordedVariable);
			return;
		}
		
		assert (trailManager.getLevel() == level) : "An attempt to remeber a changed item at the level which have not been set properly by calling function setLevel()";
		
	//	assert (!trailManager.trailContainsAllChanges 
	//			|| trailManager.levelInfo.get(trailManager.levelInfo.size() - 1) == level) : "An error. Trail should be containing all changes but it is not available";

		trailManager.addChanged(recordedVariable.index);
		
	}

	/**
	 * Any constraint in general may need information what variables have changed
	 * since the last time a consistency was called. This function is called
	 * just *before* removeLevel method is executed for variables, mutable variables, 
	 * and timestamps. 
	 * @param C constraint which is no longer interested in listening to remove level events.
	 * @return true if constraint C was watching remove level events.
	 */

	public boolean registerRemoveLevelListener(Constraint C) {

		if (!removeLevelListeners.contains(C)) {
			return removeLevelListeners.add(C);
		}
		return false;
	}

	
	/**
	 * Any constraint in general may need information what variables have changed
	 * since the last time a consistency was called. This function is called
	 * just *after* removeLevel method is executed for variables, mutable variables, 
	 * and timestamps. 
	 * @param C constraint which is no longer interested in listening to remove level events.
	 * @return true if constraint C was watching remove level events.
	 */

	public boolean registerRemoveLevelLateListener(Constraint C) {

		if (!removeLevelLateListeners.contains(C)) {
			return removeLevelLateListeners.add(C);
		}
		return false;
	}	
	
	/**
	 * This important function removes all changes which has been recorded to
	 * any variable at given level. Before backtracking to earlier level all
	 * levels after earlier level must be removed. The removal order must be
	 * reversed to the creation order.
	 * @param rLevel Store level to be removed.
	 */

	public void removeLevel(int rLevel) {

		while (currentQueue < queueNo) {
			changed[currentQueue++].clear();
		}

		// It has to inform listeners first, as they may use values of
		// mutables variables, just before they get deleted.

		for (Constraint C : removeLevelListeners)
			C.removeLevel(rLevel);

		// It needs to be before as there is a timestamp for number of boolean variables.
		for (TimeStamp<?> var : timeStamps)
			var.removeLevel(rLevel);

		// Boolean Variables.

		if (changeHistory4BooleanVariables != null) {

			int previousPosition = pointer4GroundedBooleanVariables.value();

			pointer4GroundedBooleanVariables.removeLevel(rLevel);

			int currentPosition = pointer4GroundedBooleanVariables.value();

			for (int i = currentPosition; i < previousPosition; i++) {

				Domain dom = changeHistory4BooleanVariables[i].domain;

				// Condition not true, when first constraint imposed
				// on not grounded variable is satisfied then a
				// variable becomes grounded on the same
				// level. Without this condition a null point
				// exception will occur.
				if (dom.stamp == rLevel) {

					changeHistory4BooleanVariables[i].domain.removeLevel(
							rLevel, changeHistory4BooleanVariables[i]);

				}
			}
		}

		// TODO, added functionality.
		trailManager.removeLevel(rLevel);
		
		for (int i = mutableVariables.size() - 1; i >= 0; i--)
			mutableVariables.get(i).removeLevel(rLevel);

		for (Constraint C : removeLevelLateListeners)
			C.removeLevelLate(rLevel);
		
		assert checkInvariants() == null : checkInvariants();
		
	}

	/**
	 * It decides if constraints are checked for satisfiability. If a constraint
	 * is satisfied then it will not be attached to a variable anymore.
	 * @param value boolean value specifying if check for satisfiability should be performed.
	 */
	public void setCheckSatisfiability(boolean value) {
		removeConstraints = value;
	}

	/**
	 * This function sets the long description of the store.
	 * @param description  
	 */
	public void setDescription(String description) {
		this.description = description;
	}

	/**
	 * This function sets the id of the store. This id is used when saving to
	 * XML file.
	 * @param id store id. 
	 */
	public void setID(String id) {
		this.id = id;
	}

	/**
	 * This function allows to proceed with the search, create new layer at
	 * which new values for variables will be recorded. This function is also
	 * used during backtracking, after removing current level the store can be
	 * set to the previous level.
	 * @param levelSetTo level number to which store is changing to.
	 */

	public void setLevel(int levelSetTo) {

		// TODO, functionality added.
		trailManager.setLevel(levelSetTo);

		if (level == levelSetTo)
			return;
				
		if (removeDebug) {

			if (level > levelSetTo && level > 0) {

				for (int i = 0; i < size; i++) {

					if (vars[i].level() >= level) {
						assert trailManager.isRecognizedAsChanged(vars[i].index) : "Variable position " + i + " not properly recorded to have changed ";
					}
				}
			}
		}

		if (removeDebug)
			System.out.println("Store level changes from " + level + " to " + levelSetTo);

		level = levelSetTo;
	}

	/**
	 * This function sets the prefix of the automatically generated names for
	 * noname variables.
	 * @param idPrefix prefix of all variables with automatically generated names.
	 */
	public void setVariableIdPrefix(String idPrefix) {
		variableIdPrefix = idPrefix;
	}

	/**
	 * It returns number of variables in a store.
	 * @return number of variables in a store.
	 */

	public int size() {
		return size;
	}

	/**
	 * It throws an exception after printing trace information if tracing is
	 * switched on.
	 * @param X variable causing the failure exception.
	 * 
	 * @throws FailException is always thrown.
	 */

	public void throwFailException(Var X) {

		throw failException;
		
	}

	/**
	 * This function returns a string a representation of the store. Whatever
	 * seems important may be included here.
	 */

	@Override
	public String toString() {

		StringBuffer result = new StringBuffer();

		result.append("\n*** Store\n");

		for (int i = 0; i < size; i++)
			result.append(vars[i] + "\n");

		int i = 0;
		for (MutableVar var : mutableVariables) {
		    result.append("MutableVar[").append( (int) i++).append("] ").append("(")
			.append( var.value().stamp() ).append(")");

		    result.append(var.value()).append("\n");
		}

		result.append("\n*** Constraints for evaluation:\n{").append( toStringChangedEl() )
		    .append(" }");

		return result.toString();

	}

	/**
	 * This function returns a string representation of the constraints pending
	 * for re-evaluation.
	 * @return string description of changed constraints.
	 */

	public String toStringChangedEl() {

		StringBuffer c = new StringBuffer();

		for (int i = 0; i < queueNo; i++)
			c.append(changed[i].toString() + "\n");

		return c.toString();

	}

	/**
	 * This function trims the store. It will most probably removed constraints
	 * which are satisfied. It may also remove all variables which do not have
	 * any not yet satisfied constraints attached to them. Use with care, since
	 * this function has a mandate to change CSP at previous time points. This
	 * function will be most probably used before search to obtain consize
	 * model.
	 */

	public void trim() {
		System.out.println("Trim method not yet implemented");
	}

	/**
	 * It selects constraints of a given type from queue changed.
	 * @param classname specifies the classname.
	 * @return array of constraints given class type.
	 */

	// FIXME, is it used?
	public ArrayList<Constraint> select(Class<Constraint> classname) {

		Constraint c;
		int currentQueue = 0;
		ArrayList<Constraint> list = new ArrayList<Constraint>();

		while (currentQueue < queueNo) {

			size = changed[currentQueue].size();

			for (int i = 0; i < size; i++) {

				c = changed[currentQueue].removeFirst();

				if (classname.isInstance(c)) {
					list.add(c);
				}

				changed[currentQueue].add(c);

			}

			currentQueue++;
		}

		return list;

	}

	int[][] tuples;

	int tupleNumber = 0;

	/**
	 * It is used by Extensional MDD constraints. It is to represent G_yes. 
	 */
	public SparseSet sparseSet;
	
	/**
	 * It is used by Extensional MDD constraints. It is to represent the size of G_yes. 
	 */
	public int sparseSetSize = 0;

	/**
	 * It recordTuples to store so tuples can be reused across multiple
	 * extensional constraints. It can potentially save memory.
	 * @param ts tuples to be recorded.
	 * @return two-dimensional array with tuples.
	 */

	public int[][] recordTuples(int[][] ts) {

		int[][] sortedTs = sortTuples(ts);

		if (tuples == null) {
			tuples = new int[sortedTs.length][];
			for (int i = 0; i < sortedTs.length; i++) {
				tuples[i] = new int[sortedTs[i].length];
				for (int j = 0; j < sortedTs[i].length; j++)
					tuples[i][j] = sortedTs[i][j];
			}
			tupleNumber = sortedTs.length;

			int[][] reusedTuples = new int[sortedTs.length][];
			for (int i = 0; i < sortedTs.length; i++)
				reusedTuples[i] = tuples[i];

			return reusedTuples;
		}

		int[] position = new int[sortedTs.length];
		boolean[] insert = new boolean[sortedTs.length];
		int insertNo = 0;

		int[][] reusedTuples = new int[sortedTs.length][];

		for (int i = 0; i < sortedTs.length; i++) {
			position[i] = findPositionForInsert(sortedTs[i]);

			insert[i] = true;

			if (smallerEqualTuple(tuples[position[i]], sortedTs[i])
					&& smallerEqualTuple(sortedTs[i], tuples[position[i]]))
				insert[i] = false;

			if (insert[i])
				insertNo++;
			else
				reusedTuples[i] = tuples[position[i]];
		}

		if (insertNo == 0)
			return reusedTuples;

		int[][] tuplesBeforeExtension = tuples;

		if (tupleNumber + insertNo > tuples.length)
			tuples = new int[tuples.length * 2][];
		else
			tuples = new int[tuples.length][];

		int previousPosition = 0;
		int performedInserts = 1;

		for (; previousPosition < insert.length; previousPosition++)
			if (insert[previousPosition])
				break;

		System.arraycopy(tuplesBeforeExtension, 0, tuples, 0,
				position[previousPosition]);

		tuplesBeforeExtension[position[previousPosition]] = new int[sortedTs[previousPosition].length];

		for (int j = 0; j < sortedTs[previousPosition].length; j++)
			tuplesBeforeExtension[position[previousPosition]][j] = sortedTs[previousPosition][j];

		reusedTuples[previousPosition] = tuplesBeforeExtension[position[previousPosition]];

		for (int i = previousPosition + 1; i < sortedTs.length; i++) {

			if (!insert[i])
				continue;

			System.arraycopy(tuplesBeforeExtension, position[previousPosition], // source
					tuples, position[previousPosition] + performedInserts, // target
					position[i] - position[previousPosition]); // quantity

			tuplesBeforeExtension[position[i] + performedInserts] = new int[sortedTs[i].length];

			for (int j = 0; j < sortedTs[i].length; j++)
				tuplesBeforeExtension[position[i] + performedInserts][j] = sortedTs[i][j];

			reusedTuples[i] = tuplesBeforeExtension[position[i]
					+ performedInserts];

			performedInserts++;
			previousPosition = i;
		}

		System.arraycopy(tuplesBeforeExtension, position[previousPosition], // source
				tuples, position[previousPosition] + performedInserts, // target
				tupleNumber - position[previousPosition]); // quantity

		tupleNumber += performedInserts;

		return reusedTuples;

	}

	/**
	 * searches for the position of the tuple in the tuple list.
	 * @param tuple to be compared to.
	 * @return position at which the tuple is stored in tuple list array.
	 */
	public int findPositionForInsert(int[] tuple) {

		int left = 0;
		int right = tupleNumber;

		int position = (left + right) >> 1;

		while (!(left + 1 >= right)) {

			if (smallerEqualTuple(tuples[position], tuple)) {
				left = position;
			} else {
				right = position;
			}

			position = (left + right) >> 1;

		}

		if (smallerEqualTuple(tuple, tuples[left]))
			return left;

		if (smallerEqualTuple(tuple, tuples[right]))
			return right;

		return -1;
	}

	/**
	 * @param ts tuples to be sorted.
	 * @return sorted tuples.
	 * 
	 */
	public int[][] sortTuples(int[][] ts) {

		int[][] result = new int[ts.length][];

		System.arraycopy(ts, 0, result, 0, ts.length);

		for (int i = 0; i < result.length; i++) {

			boolean change = false;

			for (int j = result.length - 1; j > i; j--)
				if (!smallerEqualTuple(result[j - 1], result[j])) {
					change = true;
					int[] tmp = result[j - 1];
					result[j - 1] = result[j];
					result[j] = tmp;
				}

			if (!change)
				break;
		}

		return result;

	}

	/**
	 * It sorts tuples.
	 * @param ts tuples to be sorted.
	 */
	public void sortTuplesWithin(int[][] ts) {

		for (int i = 0; i < ts.length; i++) {

			boolean change = false;

			for (int j = ts.length - 1; j > i; j--)
				if (!smallerEqualTuple(ts[j - 1], ts[j])) {
					change = true;
					int[] tmp = ts[j - 1];
					ts[j - 1] = ts[j];
					ts[j] = tmp;
				}

			if (!change)
				break;
		}

	}

	/**
	 * It compares tuples.
	 * @param left tuple to be compared to.
	 * @param right tuple to compar with.
	 * @return true if the left tuple is larger than right tuple.
	 */
	public boolean smallerEqualTuple(int[] left, int[] right) {

		if (right.length < left.length)
			return false;

		if (right.length > left.length)
			return true;

		for (int i = 0; i < left.length; i++) {
			if (left[i] < right[i])
				return true;
			if (left[i] > right[i])
				return false;
		}

		return true;
	}
	
	/**
	 * It checks invariants to see if the execution went smoothly.
	 * @return description of the violated invariant, null otherwise.
	 */
	public String checkInvariants() {
		
		for (int i = 0; i < size; i++)			
			if ( vars[i].level() > level ) 
				return "Removal of old values was done properly " + vars[i];
			
		return null;
	}

}
