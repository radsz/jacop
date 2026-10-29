/*
 * Store.java
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

package org.jacop.core;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.RemoveLevelLate;
import org.jacop.api.Replaceable;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.util.SparseSet;

/**
 * It is an abstract class to describe all necessary functions of any store.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class Store {

  /** It stores standard fail exception used when empty domain encountered. */
  public static final FailException failException = new FailException();

  /** It specifies if some debugging information is printed. */
  public static final boolean DEBUG = true;

  /**
   * Global switch for runtime assertion-style checks migrated from Java {@code assert}.
   *
   * <p>Default is disabled unless JVM property {@code -Djacop.asserts.enabled=true} is provided.
   */
  public static final boolean ASSERTS_ENABLED = Boolean.getBoolean("jacop.asserts.enabled");

  /** It specifies the seed for random number generators. */
  static long seed;

  static boolean seedPresent;

  /**
   * Centralized random number generator used by all JaCoP components. It is a plain {@link Random}
   * because a {@link java.security.SecureRandom} mixes a seed into its own entropy, so runs with
   * the same seed would differ.
   */
  private static Random random = new Random(); // NOSONAR not used for security

  private static final String CONSTRAINT_QUEUE_TOO_LARGE =
      "Constraint queue number larger than permitted by store.";

  /**
   * Returns the centralized random number generator.
   *
   * @return the shared {@link Random} instance.
   */
  public static Random getRandom() {
    return random;
  }

  /**
   * It stores constraints scheduled for reevaluation. It does not register constraints which are
   * already scheduled for reevaluation.
   */
  public final ConstraintQueue[] changed;

  /**
   * More advanced constraints may require to be informed of a backtrack to be able to recover the
   * older versions of the data structures. For example, the constraints can clear their queue of
   * changed variables if a backtracks has occurred. It holds the list of constraints which want to
   * be informed about level being removed before it has actually began.
   */
  public final Set<Stateful> removeLevelListeners = new ListenerSet<>();

  /** The state of this store in a chain of derived stores. */
  private StoreState state = StoreState.ACTIVE;

  /** True while a derivation writes a solution into this store or propagates it. */
  private boolean returning;

  /** The constraints imposed so far, in imposition order, when recording is on; otherwise null. */
  private List<Constraint> model;

  /** Constraints by the level of their first consistency call, in the order of the levels. */
  private Constraint[] firstRuns = new Constraint[64];

  private int firstRunsSize;

  /** One-time work done so far, in the order of the levels at which it was done. */
  private InitOnce[] initOnce = new InitOnce[16];

  private int initOnceSize;

  /**
   * More advanced constraints may require to be informed of a backtrack to be able to recover the
   * older versions of the data structures. For example, the constraints can clear their queue of
   * changed variables if a backtracks has occurred. It holds the list of constraints which want to
   * be informed about level being removed after it has been removed.
   */
  public final Set<RemoveLevelLate> removeLevelLateListeners = new ListenerSet<>();

  /**
   * It indicates that consistency function should immediately return fail if last inconsistency was
   * not followed yet by removeLevel function.
   */
  public final boolean strict = true;

  /**
   * It allows to manage information about changed variables in efficient/specialized/tailored
   * manner.
   */
  public final BacktrackableManager trailManager;

  /**
   * It may be used for faster retrieval of variables given their id. However, by default this
   * variable is not created to reduce memory consumption. If it exists then it will be used by
   * functions looking for a variable given the name.
   */
  public final Map<String, Var> variablesHashMap = new HashMap<>();

  /**
   * A mutable variable is a special variable which can change value during the search. In the event
   * of backtracks the old value must be restored, therefore the store keeps information about all
   * mutable variables.
   */
  protected final List<MutableVar> mutableVariables = new ArrayList<>(100);

  /**
   * The stateful objects registered with {@link #putMutableVar(Stateful)}. Each one is informed of
   * every removed level. Timestamps are not kept here: the store restores only the timestamps that
   * changed at the removed level.
   */
  protected final List<Stateful> timeStamps = new ArrayList<>(100);

  /** It switches on/off debuging of remove level facilities. */
  final boolean removeDebug = false;

  /**
   * It stores all the active replacements of constraints that are being applied upon constraint
   * imposition. It makes it possible to replace constraints into other constraints. It can be very
   * useful for efficiency or testing purposes.
   */
  private final Map<Class<? extends Constraint>, Set<Replaceable<? extends Constraint>>>
      replacements = new HashMap<>();

  /**
   * It stores boolean variables as soon as they change (become grounded or number of constraints
   * being attached is changed). Later each level remembers the part of the array which contains
   * variables changed at this level (efficient backtracking).
   */
  public BooleanVar[] changeHistory4BooleanVariables;

  /**
   * It contains all auxilary variables created by decomposable constraints. They have to be
   * grounded by search for a solution to be valid.
   */
  public List<Var> auxilaryVariables = new ArrayList<>();

  /** It stores constraint which is currently re-evaluated. */
  public Constraint currentConstraint;

  /**
   * Receives every domain change of an integer variable when set (lazy clause generation); null by
   * default, which costs one test per change.
   */
  public DomainChangeRecorder domainChangeRecorder;

  /** It stores constraint that has recently failed during store.consistency() execution. */
  public Constraint recentlyFailedConstraint;

  /** It stores current queue, which is being evaluated. */
  public int currentQueue;

  /** The number of domain changes reported so far, to tell whether a constraint pruned. */
  private long domainChanges;

  /** Whether consistency() returns after each constraint that changed a domain. */
  private boolean returnAfterPruning;

  /** It specifies long description of the store. */
  public String description;

  /** Id string of the store. */
  public String id = "Store";

  /**
   * It specifies the time point in the search. Every time this variable is increased a new layer of
   * changes to the variables are recorded. This is the most important variable. It is assumed that
   * initially this value is equal to zero. Use setLevel function if you want to play with it.
   */
  public int level;

  /**
   * This variable specifies if there was a new propagation. Any change to any variable will setup
   * this variable to true. Usefull variable to discover the idempodence of the consistency
   * propagator.
   */
  public boolean propagationHasOccurred;

  /** The position in changeHistory4BooleanVariables where the next changed variable is put. */
  private int booleanChangePosition;

  /** The levels at which booleanChangePosition was saved, most recent last. */
  private int[] booleanChangeLevels = new int[16];

  /** The value of booleanChangePosition saved at the corresponding level. */
  private int[] booleanChangeSaved = new int[16];

  private int booleanChangeLevelsSize;

  /**
   * The timestamps (and other trailed values) that got a value at a new level, in the order of the
   * levels.
   */
  private Stateful[] timeStampTrail = new Stateful[64];

  /** The trail of the domains changed in place, see {@link DomainTrail}. */
  final DomainTrail domainTrail = new DomainTrail();

  /** The level of the corresponding entry of timeStampTrail. */
  private int[] timeStampTrailLevel = new int[64];

  private int timeStampTrailSize;

  private int timeStampCount;

  /**
   * It stores number of queues used in this store. It has to be at least 1. No constraint can be
   * imposed with queue index greater or equal this number.
   */

  // upon changing the number of queues.
  public int queueNo = 5;

  /**
   * Some constraints maintain complex data structure based on function recentDomainPruning of a
   * variable, this function for proper functioning requires to raise store level after imposition
   * and before any changes to variables of this constraint occur. This flag is set by constraints
   * at imposition stage.
   */
  public boolean raiseLevelBeforeConsistency;

  /**
   * It specifies if the weight of variables which are in the scope of the failure constraint should
   * be increased.
   */
  public boolean variableWeightManagement;

  /** Number of calls to consistency methods of constraints. */
  public long numberConsistencyCalls;

  /**
   * Time, as given by {@link System#currentTimeMillis()}, after which consistency() fails at once;
   * 0 means no deadline. A search with a time-out sets it while it runs, so that a propagation that
   * does not reach its fixpoint for a long time (for example slowly converging float bounds) cannot
   * overrun the time-out.
   */
  private long consistencyDeadline;

  /** It specifies that consistencyDeadline has passed. */
  private boolean consistencyDeadlinePassed;

  /** Set by {@link #interrupt()}: the deadline stays passed. */
  private volatile boolean interrupted;

  /** This flag is set to true when consistency function of the store encounters failure. */
  public boolean isLastConsistencyFailure;

  /**
   * This keeps information about watched constraints by given variable. Watched constraints are
   * active all the time. Use this with care and do not be surprised if some constraints stay longer
   * than you expect. It can be directly manipulated in any way (including setting to null if no
   * watched constraints are being in the queue system).
   */
  public Map<Var, Set<Constraint>> watchedConstraints;

  /** It stores integer variables created within a store. */
  public Var[] vars;

  /** It is used by Extensional Mdd constraints. It is to represent G_yes. */
  public SparseSet sparseSet;

  /** It is used by Extensional Mdd constraints. It is to represent the size of G_yes. */
  public int sparseSetSize;

  /** It stores the number of constraints which were imposed to the store. */
  protected int numberOfConstraints;

  /** Number of variables stored within a store. */
  protected int size;

  /** The prefix of any variable which was noname. */
  protected String variableIdPrefix = "_";

  /**
   * Variables for accumulated failure count (AFC) for constraints. constraintAfcManagement- opens
   * AFC menagement decay- decay factor allConstraints- all constraints in the store
   */
  boolean constraintAfcManagement;

  Set<Constraint> allConstraints;
  double decay = 0.99d;

  /**
   * The amount added to the AFC weight of a failing constraint. It grows by 1/decay at each
   * failure, which decays all the other weights relative to it.
   */
  double afcIncrement = 1.0d;

  /** The AFC increment above which all weights and the increment are rescaled. */
  static final double AFC_RESCALE_LIMIT = 1e20d;

  /**
   * Variables for pruning count (variable activity) for constraints. variableActivityManagement-
   * opens activity menagement variablePrunnedConstraints- all constraints in the store
   */
  boolean variableActivityManagement;

  Set<Var> variablesPrunned;

  /** It specifies the default constructor of the store. */
  public Store() {

    this(100);
  }

  /**
   * It specifies the constructor of the store, which allows to decide what is the initial size of
   * the Variable list.
   *
   * @param size specifies the initial number of variables.
   */
  public Store(int size) {

    vars = new Var[size];

    changed = new ConstraintQueue[queueNo];

    for (int i = 0; i < queueNo; i++) {
      changed[i] = new ConstraintQueue(this, i);
    }

    trailManager = new TrailBacktrackableManager(vars, this.size);
  }

  /**
   * Returns the seed for the random number generator.
   *
   * @return the seed value.
   * @throws IllegalArgumentException if the seed has not been set.
   */
  public static long getSeed() {
    if (seedPresent) {
      return seed;
    }

    throw new IllegalArgumentException("Not defined seed for random generator");
  }

  /**
   * Sets the seed for the random number generator.
   *
   * @param s the seed value to set.
   */
  public static void setSeed(long s) {
    seed = s;
    seedPresent = true;
    random = new Random(s); // NOSONAR not used for security
  }

  /**
   * Checks whether a seed for the random number generator has been set.
   *
   * @return true if the seed has been set, false otherwise.
   */
  public static boolean seedPresent() {
    return seedPresent;
  }

  /** Resets the seed for the random number generator, marking it as not present. */
  public static void resetSeed() {
    seedPresent = false;
    random = new Random(); // NOSONAR not used for security
  }

  /**
   * Variable given as a parameter no longer watches constraint given as parameter. This function
   * will be called when watch is being moved from one variable to another.
   *
   * @param v variable at which constraint is no longer watching.
   * @param c constraint which is no longer watched by given variable.
   */
  public void deregisterWatchedLiteralConstraint(Var v, Constraint c) {

    watchedConstraints.get(v).remove(c);
  }

  /**
   * Watched constraint given as parameter is being removed, no variable will be watching it.
   *
   * @param c constraint for which all watches are removed.
   */
  public void deregisterWatchedLiteralConstraint(Constraint c) {

    for (Var v : c.arguments()) {
      Set<Constraint> forVariable = watchedConstraints.get(v);
      if (forVariable != null) {
        forVariable.remove(c);
      }
    }
  }

  /**
   * It returns number of watches which are used to watch constraints.
   *
   * @return returns the number of watches attached to variables.
   */
  public int countWatches() {

    if (watchedConstraints == null) {
      return 0;
    }

    int count = 0;

    for (Set<Constraint> c : watchedConstraints.values()) {
      count += c.size();
    }

    return count;
  }

  /**
   * It register variable to watch given constraint. This function is called either by impose
   * function of a constraint or by consistency function of a constraint when watch is being moved.
   *
   * @param v variable which is used to watch the constraint.
   * @param c the constraint being used.
   */
  public void registerWatchedLiteralConstraint(Var v, Constraint c) {

    Set<Constraint> forVariable = watchedConstraints.get(v);

    if (forVariable != null) {
      forVariable.add(c);
    } else {
      forVariable = new LinkedHashSet<>();
      forVariable.add(c);
      watchedConstraints.put(v, forVariable);
    }
  }

  /**
   * It removes all watches to constraints, therefore constraints are no longer watched, no longer
   * part of the model.
   */
  public void clearWatchedConstraint() {

    watchedConstraints.clear();
  }

  /**
   * This function schedules given constraint for re-evaluation. This function will most probably be
   * rarely used as constraints require reevaluation only when a variable changes.
   *
   * @param c constraint which needs reevaluation.
   */
  public void addChanged(Constraint c) {

    propagationHasOccurred = true;

    if (c.getQueueIndex() < currentQueue) {
      currentQueue = c.getQueueIndex();
    }

    changed[c.getQueueIndex()].add(c);
  }

  /**
   * Schedules a constraint in a given queue instead of its own. It is meant for constraints that
   * split their propagation over several queues, for example a cheap pass in their own queue and an
   * expensive one in a later queue. Unlike {@link #addChanged(Constraint)} it does not set {@link
   * #propagationHasOccurred}, as scheduling itself prunes nothing.
   *
   * @param c constraint which needs reevaluation.
   * @param queueIndex the queue in which the constraint is scheduled.
   */
  public void addChanged(Constraint c, int queueIndex) {

    if (queueIndex < currentQueue) {
      currentQueue = queueIndex;
    }

    changed[queueIndex].add(c);
  }

  /**
   * This function schedules all attached (not yet satisfied constraints) for given variable for
   * re-evaluation. This function must add all attached constraints for reevaluation but it will do
   * it any order which suits it.
   *
   * @param v variable for which some pruning event has occurred.
   * @param pruningEvent specifies the type of the pruning event.
   * @param info it specifies detailed information about the change of the variable domain. the
   *     inputs of the currentConstraint in the manner that would validate another execution.
   */
  public void addChanged(Var v, int pruningEvent, int info) {

    propagationHasOccurred = true;
    domainChanges++;

    if (variableActivityManagement) {
      variablesPrunned.add(v);
    }

    Domain vdomain = v.dom();

    // a domain on the domain trail is restored without visiting its variable
    if (!vdomain.onDomainTrail) {
      recordChange(v);
    }

    queueModelConstraintsForVariable(vdomain, v, pruningEvent);
    queueSearchConstraintsForVariable(vdomain, v);

    if (watchedConstraints != null && pruningEvent == IntDomain.GROUND) {
      queueWatchedConstraintsForVariable(v);
    }

    if (v.valueWatches != null && pruningEvent == IntDomain.GROUND) {
      queueValueWatches(v);
    }
  }

  /**
   * Makes a constraint watch a variable for being fixed to 0 or 1. When the variable gets that
   * value, the store calls {@link Constraint#valueWatchFired(int, Var, int)} with the tag, and
   * queues the constraint if the call returns true. Unlike model constraints of a variable, the
   * watches are not restored on backtracking and stay for good, so they are meant for constraints
   * imposed at level 0 that keep track of their watches themselves, as SAT solvers do with watched
   * literals. The constraint must not add a watch on the variable during the call.
   *
   * @param v the variable, with a domain within 0..1.
   * @param value the watched value, 0 or 1.
   * @param c the watching constraint.
   * @param tag the tag given back to the constraint, for example the position of the variable.
   */
  public void watchValue(Var v, int value, Constraint c, int tag) {
    if (v.valueWatches == null) {
      v.valueWatches = new ValueWatches();
    }
    v.valueWatches.add(value, c, tag);
  }

  /**
   * Returns the constraints that watch a value of a variable ({@link #watchValue}), in the order
   * the watches were added, a constraint once even if it watches both values. They are not in the
   * constraint lists of the variable's domain.
   *
   * @param v the variable.
   * @return the watching constraints.
   */
  public List<Constraint> valueWatchers(Var v) {
    ValueWatches watches = v.valueWatches;
    if (watches == null) {
      return List.of();
    }
    Set<Constraint> result = Collections.newSetFromMap(new LinkedHashMap<>());
    for (int value = 0; value < 2; value++) {
      result.addAll(Arrays.asList(watches.constraints[value]).subList(0, watches.size[value]));
    }
    return new ArrayList<>(result);
  }

  /**
   * Removes every value watch of a variable, so the watching constraints are no longer woken by it.
   *
   * @param v the variable.
   */
  public void clearValueWatches(Var v) {
    v.valueWatches = null;
  }

  private void queueValueWatches(Var v) {
    int value = ((IntVar) v).value();
    if (value != 0 && value != 1) {
      return;
    }
    ValueWatches watches = v.valueWatches;
    for (int i = watches.size[value] - 1; i >= 0; i--) {
      Constraint c = watches.constraints[value][i];
      if (c.isEntailed()) {
        continue;
      }
      if (c.valueWatchFired(level, v, watches.tags[value][i]) && currentConstraint != c) {
        addChanged(c);
      }
    }
  }

  /** Constraints marked as entailed during search, in the order of their levels. */
  private Constraint[] entailed = new Constraint[64];

  private int entailedSize;

  /**
   * Marks a constraint as entailed at the current level. The constraint stays attached to its
   * variables, but is not queued any more until the store backtracks below this level, when the
   * mark is cleared.
   *
   * @param c the entailed constraint.
   */
  public void markEntailed(Constraint c) {
    if (c.isEntailed()) {
      return;
    }
    c.setEntailedAt(level);
    if (entailedSize == entailed.length) {
      entailed = Arrays.copyOf(entailed, entailedSize * 2);
    }
    entailed[entailedSize++] = c;
  }

  private void queueModelConstraintsForVariable(Domain vdomain, Var v, int pruningEvent) {
    for (int j : vdomain.getEventsInclusion(pruningEvent)) {
      Constraint[] addedConstraints = vdomain.modelConstraints[j];
      for (int i = vdomain.modelConstraintsToEvaluate[j] - 1; i >= 0; i--) {
        queueModelConstraint(vdomain, v, addedConstraints[i]);
      }
    }
  }

  /** It wakes one model constraint of a changed variable. */
  private void queueModelConstraint(Domain vdomain, Var v, Constraint c) {
    if (c.isEntailed()) {
      // the domain was saved at this level by the change being reported, so the constraint can be
      // detached without a copy; backtracking below this level attaches it again
      if (vdomain.stamp == level) {
        vdomain.removeModelConstraint(level, v, c);
      }
      return;
    }
    if (c.overridesQueueVariable()) {
      c.queueVariable(level, v);
    }
    // the constraint whose pruning wakes the variable is told about the change but not queued again
    if (c != currentConstraint) {
      // addChanged(c) without setting propagationHasOccurred, which addChanged(Var...) did
      int queueIndex = c.getQueueIndex();
      if (queueIndex < currentQueue) {
        currentQueue = queueIndex;
      }
      changed[queueIndex].add(c);
    }
  }

  private void queueSearchConstraintsForVariable(Domain vdomain, Var v) {
    List<Constraint> constr = vdomain.searchConstraints;
    for (int i = vdomain.searchConstraintsToEvaluate - 1; i >= 0; i--) {
      Constraint c = constr.get(i);
      if (c.isEntailed()) {
        continue;
      }
      if (c.overridesQueueVariable()) {
        c.queueVariable(level, v);
      }
      if (currentConstraint != c) {
        addChanged(c);
      }
    }
  }

  private void queueWatchedConstraintsForVariable(Var v) {
    Set<Constraint> list = watchedConstraints.get(v);
    if (list == null) {
      return;
    }
    for (Constraint con : list) {
      if (con.isEntailed()) {
        continue;
      }
      if (con.overridesQueueVariable()) {
        con.queueVariable(level, v);
      }
      if (currentConstraint != con) {
        addChanged(con);
      }
    }
  }

  /**
   * It clears the queue of constraints which need to be reevaluated usefull if different scheme
   * propagation scheme needs to be implemented.
   */
  public void clearChanged() {

    while (currentQueue < queueNo) {
      changed[currentQueue++].clear();
    }
  }

  private void handleConsistencyFailure() {
    if (currentConstraint != null) {
      currentConstraint.cleanAfterFailure();
      if (variableWeightManagement) {
        currentConstraint.increaseWeight();
      }
      if (constraintAfcManagement) {
        updateAfc(currentConstraint);
      }
      if (variableActivityManagement) {
        updateActivities(currentConstraint);
        variablesPrunned.clear();
      }
    }
    recentlyFailedConstraint = currentConstraint;
    currentConstraint = null;
    isLastConsistencyFailure = true;
  }

  /**
   * It returns the time after which consistency() fails at once, 0 if there is none.
   *
   * @return the deadline as given by {@link System#currentTimeMillis()}, or 0.
   */
  public long getConsistencyDeadline() {
    return consistencyDeadline;
  }

  /**
   * It sets the time after which consistency() fails at once. A failure caused by the deadline is
   * not a proof of inconsistency: the caller must check its own time-out after a failure.
   *
   * @param deadline the deadline as given by {@link System#currentTimeMillis()}, or 0 for none.
   */
  public void setConsistencyDeadline(long deadline) {
    consistencyDeadline = interrupted ? 1 : deadline;
    consistencyDeadlinePassed = false;
  }

  /**
   * It stops a search of this store running in another thread, for example one of a parallel
   * portfolio whose result is no longer needed: consistency() fails from now on as if the deadline
   * had passed, which a search with a time-out takes as its time-out. It is a request on a best
   * effort basis; the search notices it within a few hundred propagator calls.
   */
  public void interrupt() {
    interrupted = true;
    consistencyDeadline = 1;
  }

  /**
   * It specifies whether consistency() has failed because of the deadline since it was set.
   *
   * @return true if the deadline set by {@link #setConsistencyDeadline(long)} has passed.
   */
  public boolean isConsistencyDeadlinePassed() {
    return consistencyDeadlinePassed;
  }

  private boolean consistencyDeadlinePassed() {
    // the clock is read every 256 propagator calls only
    if (!consistencyDeadlinePassed
        && (numberConsistencyCalls & 0xFF) == 0
        && System.currentTimeMillis() > consistencyDeadline) {
      consistencyDeadlinePassed = true;
    }
    return consistencyDeadlinePassed;
  }

  /**
   * Makes {@link #consistency()} return after each constraint whose call changed a domain, with the
   * other queued constraints left for the next call, instead of running all of them to a fixpoint.
   * Lazy clause generation uses it to propagate clauses before the next constraint, as clauses are
   * the cheapest propagators it has.
   *
   * @param returnAfterPruning true to return after each pruning constraint, false for a fixpoint.
   */
  public void setReturnAfterPruning(boolean returnAfterPruning) {
    this.returnAfterPruning = returnAfterPruning;
  }

  /**
   * It specifies whether {@link #consistency()} returns after each constraint that changed a
   * domain.
   *
   * @return true if consistency() returns after each pruning constraint.
   */
  public boolean isReturnAfterPruning() {
    return returnAfterPruning;
  }

  /**
   * Checks whether constraints wait in the propagation queues, as they do after {@link
   * #consistency()} returned early (see {@link #setReturnAfterPruning(boolean)}).
   *
   * @return true if some constraint waits for its consistency function.
   */
  public boolean hasPendingConstraints() {
    for (int i = currentQueue; i < queueNo; i++) {
      if (!changed[i].isEmpty()) {
        return true;
      }
    }
    return false;
  }

  /**
   * This function computes the consistency function. It evaluates all constraints which are in the
   * changed queue. With {@link #setReturnAfterPruning(boolean)} it returns after the first
   * constraint that changed a domain instead, and the constraints still queued wait for the next
   * call ({@link #hasPendingConstraints()}).
   *
   * @return returns true if all constraints which were in changed queue are consistent, false
   *     otherwise.
   */
  public boolean consistency() {

    if (state != StoreState.ACTIVE && !returning) {
      throw new IllegalStateException("Store is " + state + "; it cannot propagate");
    }

    if (strict && isLastConsistencyFailure) {
      return false;
    }

    if (raiseLevelBeforeConsistency) {
      raiseLevelBeforeConsistency = false;
      setLevel(level + 1);
    }

    if (this.sparseSetSize > 0 && this.sparseSet == null) {
      sparseSet = new SparseSet(sparseSetSize);
    }

    try {

      while (currentQueue < queueNo) {
        while (!changed[currentQueue].isEmpty()) {
          if (consistencyDeadline > 0 && consistencyDeadlinePassed()) {
            // no constraint failed, so none is blamed for this failure
            currentConstraint = null;
            throw failException;
          }
          currentConstraint = getFirstChanged();
          if (currentConstraint.firstRunAt() < 0) {
            startFirstRun(currentConstraint);
          }
          numberConsistencyCalls++;
          long changesBefore = domainChanges;
          currentConstraint.consistency(this);
          if (variableActivityManagement) {
            updateActivities(currentConstraint);
            variablesPrunned.clear();
          }
          if (returnAfterPruning && domainChanges != changesBefore) {
            currentConstraint = null;
            return true;
          }
        }
        currentQueue++;
      }

    } catch (FailException _) {
      handleConsistencyFailure();
      return false;
    }

    currentConstraint = null;
    return true;
  }

  /**
   * This function is called when a counter of constraints should be increased. It is most probable
   * that this function will called from the impose function of the constraint.
   */
  public void countConstraint() {
    numberOfConstraints++;
  }

  /**
   * This function is called when a counter of constraints should be increased by given value. If
   * for some reason some constraints should be counted as multiple ones than this function could be
   * called.
   *
   * @param n integer by which the counter of constraints should be increased.
   */
  public void countConstraint(int n) {
    numberOfConstraints += n;
  }

  /**
   * This function looks for a variable with given id. It will first check the existence of a
   * hashmap variablesHashMap to get the variable from the hashmap in constant time. Only if the
   * variable was not found or hashmap object was not created a linear algorithm scanning through
   * the whole list of variables will be employed.
   *
   * @param id unique identifier of the variable.
   * @return reference to a variable with the given id.
   */
  public Var findVariable(String id) {

    Var key = variablesHashMap.get(id);

    if (key != null) {
      return key;
    }

    for (Var v : vars) {
      if (v != null && id.equals(v.id())) {
        return v;
      }
    }

    return null;
  }

  /**
   * This function returns the constraint which is currently reevaluated. It is an easy way to
   * discover which constraint caused a failure right after the inconsistency is signaled.
   *
   * @return constraint for which consistency method is being executed.
   */
  public Constraint getCurrentConstraint() {
    return currentConstraint;
  }

  /**
   * This function returns the long description of the store.
   *
   * @return store description.
   */
  public String getDescription() {
    return description;
  }

  /**
   * This function sets the long description of the store.
   *
   * @param description description of the store
   */
  public void setDescription(String description) {
    this.description = description;
  }

  /**
   * This function returns the constraint scheduled for re-evaluation. It returns constraints based
   * on criteria first-in-first out. It is simple, easy, fair, and efficient way of getting
   * constraints for reevaluation. The constraint is _removed_ from the queue, since it is assumed
   * that they are reevaluated right away.
   *
   * @return first constraint which is being marked as the one which needs to be checked for
   *     consistency.
   */
  public Constraint getFirstChanged() {

    return changed[currentQueue].poll();
  }

  /**
   * This function returns the id of the store.
   *
   * @return id of store.
   */
  public String getName() {
    return id;
  }

  /**
   * This function returns the prefix of the automatically generated names for noname variables.
   *
   * @return he prefix of the automatically generated names for noname variables.
   */
  public String getVariableIdPrefix() {
    return variableIdPrefix;
  }

  /**
   * This function sets the prefix of the automatically generated names for noname variables.
   *
   * @param idPrefix prefix of all variables with automatically generated names.
   */
  public void setVariableIdPrefix(String idPrefix) {
    variableIdPrefix = idPrefix;
  }

  /**
   * This function imposes a constraint to a store. The constraint is scheduled for evaluation for
   * the next store consistency call. Therefore, the constraint is added to queue of changed
   * constraints.
   *
   * @param c constraint to be imposed.
   */
  @SuppressWarnings("unchecked")
  public void impose(Constraint c) {

    checkImposeAllowed();
    record(c);
    Optional.ofNullable(replacements.get(c.getClass()))
        .ifPresent(
            l ->
                l.forEach(
                    r -> {
                      Replaceable<Constraint> replacement = (Replaceable<Constraint>) r;
                      if (replacement.isReplaceable(c)) {
                        replacement.replace(c).imposeDecomposition(this);
                      }
                    }));
    c.impose(this);
  }

  /**
   * This function imposes a constraint to a store. The constraint is scheduled for evaluation for
   * the next store consistency call. Therefore, the constraint is added to queue of changed
   * constraints.
   *
   * @param c constraint to be added to specified queue.
   * @param queueIndex specifies index of the queue for a constraint.
   */
  public void impose(Constraint c, int queueIndex) {

    if (ASSERTS_ENABLED && queueIndex >= queueNo) {
      throw new IllegalStateException(String.valueOf(CONSTRAINT_QUEUE_TOO_LARGE));
    }

    checkImposeAllowed();
    record(c);
    c.impose(this, queueIndex);
  }

  /**
   * In some special cases it may be beneficial to compute consistency of constraint store
   * immediately after the constraint is imposed. This function will impose a constraint and call
   * the consistency function of the store immediately.
   *
   * @param c constraint to be imposed.
   * @throws FailException failure exception.
   */
  public void imposeWithConsistency(Constraint c) throws FailException {

    checkImposeAllowed();
    record(c);
    c.impose(this);

    if (!consistency()) {
      throw failException;
    }
  }

  /**
   * In some special cases it may be beneficial to compute consistency of constraint store
   * immediately after the constraint is imposed. This function will impose a constraint and call
   * the consistency function of the store immediately.
   *
   * @param c constraint to be imposed.
   * @param queueIndex constraint priority for evaluation.
   * @throws FailException failure exception.
   */
  public void imposeWithConsistency(Constraint c, int queueIndex) throws FailException {

    if (ASSERTS_ENABLED && queueIndex >= queueNo) {
      throw new IllegalStateException(String.valueOf(CONSTRAINT_QUEUE_TOO_LARGE));
    }

    checkImposeAllowed();
    record(c);
    c.impose(this, queueIndex);

    if (!consistency()) {
      throw failException;
    }
  }

  /**
   * This function imposes a decomposable constraint to a store. The decomposition is scheduled for
   * evaluation for the next store consistency call. Therefore, the constraints are added to queue
   * of changed constraints.
   *
   * @param c constraint to be imposed.
   */
  public <T extends Constraint> void imposeDecomposition(DecomposedConstraint<T> c) {

    c.imposeDecomposition(this);
  }

  /**
   * This function imposes a constraint decomposition to a store. The decomposition constraints are
   * scheduled for evaluation for the next store consistency call. Therefore, the constraints are
   * added to queue of changed constraints.
   *
   * @param c constraint to be added to specified queue.
   * @param queueIndex specifies index of the queue for a constraint.
   */
  public <T extends Constraint> void imposeDecomposition(
      DecomposedConstraint<T> c, int queueIndex) {

    if (ASSERTS_ENABLED && queueIndex >= queueNo) {
      throw new IllegalStateException(String.valueOf(CONSTRAINT_QUEUE_TOO_LARGE));
    }

    c.imposeDecomposition(this, queueIndex);
  }

  /**
   * In some special cases it may be beneficial to compute consistency of constraint store
   * immediately after the decomposed constraint is imposed. This function will impose constraint
   * decomposition and call the consistency function of the store immediately.
   *
   * @param c decomposed constraint to be imposed.
   */
  public <T extends Constraint> void imposeDecompositionWithConsistency(DecomposedConstraint<T> c) {

    c.imposeDecomposition(this);

    if (!consistency()) {
      throw failException;
    }
  }

  /**
   * This function checks if all variables within a store are grounded. It is advised to make sure
   * that after search all variables are grounded.
   *
   * @return true if all variables are singletons, false otherwise.
   */
  public boolean isGround() {
    for (Var v : vars) {
      if (!v.singleton()) {
        return false;
      }
    }
    return true;
  }

  /**
   * This function returns the number of constraints.
   *
   * @return number of constraints.
   */
  public int numberConstraints() {
    return numberOfConstraints;
  }

  /** This function prints the information of the store to standard output stream. */
  public void print() {
    log.debug("{}", this);
  }

  /**
   * Any constraint may have their own mutable variables which can be register at store and then
   * store will be responsible for calling appropriate functions from MutableVar interface to keep
   * the variables consistent with the search.
   *
   * @param value MutableVariable to be added and maintained by a store.
   * @return the position of MutableVariable at which it is being stored.
   */
  public int putMutableVar(MutableVar value) {
    mutableVariables.add(value);
    return mutableVariables.size() - 1;
  }

  /**
   * Any entity (for example constraints) may have their own stateful objects which can be register
   * at store and then store will call their removeLevel function for every removed level. A {@link
   * TimeStamp} registers itself and does not need to be registered.
   *
   * @param value stateful object to be added and maintained by a store.
   * @return the position of the object at which it is being stored.
   */
  public int putMutableVar(Stateful value) {
    timeStamps.add(value);
    return timeStamps.size() - 1;
  }

  /**
   * This function is used to register a variable within a store. It will be most probably called
   * from variable constructor. It returns the current position of fdv in a store local data
   * structure.
   *
   * @param v variable to be registered.
   * @return position of the variable at which it is being stored.
   */
  public int putVariable(Var v) {

    Var previousVar = variablesHashMap.put(v.id(), v);

    if (ASSERTS_ENABLED && previousVar != null) {
      throw new IllegalStateException(
          String.valueOf("Two variables have the same id " + previousVar + " " + v));
    }

    if (v.storeIndex != -1 && vars[v.storeIndex] == v) {
      throw new IllegalArgumentException("\nSetting Variable: Variable already exists: " + v.id());
    }

    // boolean variables are not trailed the same fashion as int variables.
    if (v instanceof BooleanVar) {
      return -1;
    }

    if (size < vars.length) {

      vars[size] = v;
      size++;

    } else {

      Var[] oldVars = vars;
      vars = new Var[oldVars.length * 2];

      System.arraycopy(oldVars, 0, vars, 0, size);

      vars[size] = v;
      size++;

      trailManager.update(vars, size);
    }

    trailManager.setSize(size);

    return size - 1;
  }

  /**
   * Any boolean variable which is changed must be recorded by store, so it can be restored to the
   * previous state if backtracking is performed.
   *
   * @param recordedVariable boolean variable which has changed.
   */
  public void recordBooleanChange(BooleanVar recordedVariable) {

    int position = booleanChangePosition;

    if (position >= changeHistory4BooleanVariables.length) {

      BooleanVar[] temp = changeHistory4BooleanVariables;
      changeHistory4BooleanVariables = new BooleanVar[changeHistory4BooleanVariables.length * 2];
      System.arraycopy(temp, 0, changeHistory4BooleanVariables, 0, position);
    }

    changeHistory4BooleanVariables[position] = recordedVariable;

    int top = booleanChangeLevelsSize - 1;
    if (top < 0 || booleanChangeLevels[top] != level) {
      if (booleanChangeLevelsSize >= booleanChangeLevels.length) {
        growBooleanChangeLevels();
      }
      booleanChangeLevels[booleanChangeLevelsSize] = level;
      booleanChangeSaved[booleanChangeLevelsSize] = position;
      booleanChangeLevelsSize++;
    }

    booleanChangePosition = position + 1;
  }

  private void growBooleanChangeLevels() {
    // An explicit bound instead of Math.max, so the new capacity is provably above
    // booleanChangeLevelsSize.
    if (booleanChangeLevelsSize > (Integer.MAX_VALUE - 16) / 2) {
      throw new IllegalStateException("Trail too large");
    }
    int capacity = 2 * booleanChangeLevelsSize + 16;
    booleanChangeLevels = Arrays.copyOf(booleanChangeLevels, capacity);
    booleanChangeSaved = Arrays.copyOf(booleanChangeSaved, capacity);
  }

  /**
   * Registers a timestamp. The store restores the timestamps that changed at a level when the level
   * is removed, see {@link #recordTimeStampLevel(TimeStamp, int)}.
   *
   * @return the index of the timestamp among the timestamps of this store.
   */
  int registerTimeStamp() {
    return timeStampCount++;
  }

  /**
   * Records that a timestamp got a value at a new level, so the value is removed with the level. A
   * {@link TrailedInts} records itself the same way; its removeLevel restores every level at once.
   *
   * @param timeStamp the timestamp.
   * @param stampLevel the level of the new value.
   */
  void recordTimeStampLevel(Stateful timeStamp, int stampLevel) {
    if (timeStampTrailSize >= timeStampTrail.length) {
      growTimeStampTrail();
    }
    timeStampTrail[timeStampTrailSize] = timeStamp;
    timeStampTrailLevel[timeStampTrailSize] = stampLevel;
    timeStampTrailSize++;
  }

  /**
   * Records that a stateful object changed at the current level. The store calls its removeLevel
   * only when a level at which it changed is removed, as for a timestamp, instead of at every level
   * as for a listener registered with {@link #registerRemoveLevelListener(Stateful)}. The object
   * records itself once per level, at its first change there.
   *
   * @param stateful the object that changed.
   */
  public void recordChange(Stateful stateful) {
    recordTimeStampLevel(stateful, level);
  }

  private void growTimeStampTrail() {
    // An explicit bound instead of Math.max, so the new capacity is provably above
    // timeStampTrailSize.
    if (timeStampTrailSize > (Integer.MAX_VALUE - 64) / 2) {
      throw new IllegalStateException("Trail too large");
    }
    int capacity = 2 * timeStampTrailSize + 64;
    timeStampTrail = Arrays.copyOf(timeStampTrail, capacity);
    timeStampTrailLevel = Arrays.copyOf(timeStampTrailLevel, capacity);
  }

  /**
   * Any change of finite domain variable must also be recorded, so intervals denoting changed
   * variables can be updated.
   *
   * @param recordedVariable variable which has changed.
   */
  public void recordChange(Var recordedVariable) {

    // Boolean variables or other variables with index -1 are
    // stored each time they change in the special 1D array.
    if (recordedVariable.storeIndex == -1) {
      recordBooleanChange((BooleanVar) recordedVariable);
      return;
    }

    if (ASSERTS_ENABLED && trailManager.getLevel() != level) {
      throw new IllegalStateException(
          String.valueOf(
              "An attempt to remeber a changed item at the level which have not been set properly by calling function setLevel()"));
    }

    //                      || trailManager.levelInfo.get(trailManager.levelInfo.size() - 1) ==
    // level) :
    //                             "An error. Trail should be containing all changes but it is not
    // available";

    trailManager.addChanged(recordedVariable.storeIndex);
  }

  /**
   * It makes it possible to register replacement for a particular constraint type.
   *
   * @param replacement that is being registered.
   * @return true if replacement has been added and was not already registered, false otherwise.
   */
  public boolean registerReplacement(Replaceable<? extends Constraint> replacement) {

    if (!replacements.containsKey(replacement.forClass())) {
      replacements.put(replacement.forClass(), new LinkedHashSet<>());
    }

    Set<Replaceable<? extends Constraint>> current = replacements.get(replacement.forClass());

    return current.add(replacement);
  }

  /**
   * It makes it possible to deregister the replacement. The constraint that have been already
   * replaced remained replaced.
   *
   * @param replacement that is being deregister from within the constraint store.
   * @return true if replacement was present and was deregistered, false otherwise.
   */
  public boolean deregisterReplacement(Replaceable<? extends Constraint> replacement) {

    Optional<Set<Replaceable<? extends Constraint>>> forClass =
        Optional.ofNullable(replacements.get(replacement.forClass()));

    return forClass.map(replaceables -> replaceables.remove(replacement)).orElse(false);
  }

  /**
   * Any constraint in general may need information what variables have changed since the last time
   * a consistency was called. This function is called just *before* removeLevel method is executed
   * for variables, mutable variables, and timestamps.
   *
   * @param stateful constraint which is interested in listening to remove level events.
   * @return true if constraint stateful was watching remove level events.
   */
  public boolean registerRemoveLevelListener(Stateful stateful) {

    if (!removeLevelListeners.contains(stateful)) {
      return removeLevelListeners.add(stateful);
    }
    return false;
  }

  /**
   * Any constraint in general may need information what variables have changed since the last time
   * a consistency was called. This function is called just *after* removeLevel method is executed
   * for variables, mutable variables, and timestamps.
   *
   * @param c constraint which is no longer interested in listening to remove level events.
   * @return true if constraint c was watching remove level events.
   */
  public boolean registerRemoveLevelLateListener(RemoveLevelLate c) {

    if (!removeLevelLateListeners.contains(c)) {
      return removeLevelLateListeners.add(c);
    }
    return false;
  }

  /**
   * This important function removes all changes which has been recorded to any variable at given
   * level. Before backtracking to earlier level all levels after earlier level must be removed. The
   * removal order must be reversed to the creation order.
   *
   * @param level Store level to be removed.
   */
  public void removeLevel(int level) {

    if (state != StoreState.ACTIVE && !returning) {
      throw new IllegalStateException("Store is " + state + "; it cannot remove a level");
    }

    // Remove level is called so we clear flag isLastConsistencyFailure.
    isLastConsistencyFailure = false;

    while (currentQueue < queueNo) {
      changed[currentQueue++].clear();
    }

    while (firstRunsSize > 0 && firstRuns[firstRunsSize - 1].firstRunAt() >= level) {
      firstRuns[--firstRunsSize].setFirstRunAt(Constraint.RUN_UNDONE);
      firstRuns[firstRunsSize] = null;
    }

    // One-time work done at this level is due again; listeners below can already see it.
    while (initOnceSize > 0 && initOnce[initOnceSize - 1].level() >= level) {
      initOnce[--initOnceSize].rearm();
      initOnce[initOnceSize] = null;
    }

    // It has to inform listeners first, as they may use values of
    // mutables variables, just before they get deleted.

    for (Object statefulConstraint : ((ListenerSet<Stateful>) removeLevelListeners).elements()) {
      ((Stateful) statefulConstraint).removeLevel(level);
    }

    if (!timeStamps.isEmpty()) {
      for (Stateful v : timeStamps) {
        v.removeLevel(level);
      }
    }

    while (timeStampTrailSize > 0 && timeStampTrailLevel[timeStampTrailSize - 1] >= level) {
      timeStampTrailSize--;
      timeStampTrail[timeStampTrailSize].removeLevel(level);
      timeStampTrail[timeStampTrailSize] = null;
    }

    // Boolean Variables.

    if (changeHistory4BooleanVariables != null) {

      int previousPosition = booleanChangePosition;

      while (booleanChangeLevelsSize > 0
          && booleanChangeLevels[booleanChangeLevelsSize - 1] >= level) {
        booleanChangePosition = booleanChangeSaved[--booleanChangeLevelsSize];
      }

      int currentPosition = booleanChangePosition;

      for (int i = currentPosition; i < previousPosition; i++) {

        Domain dom = changeHistory4BooleanVariables[i].domain;

        // Condition not true, when first constraint imposed
        // on not grounded variable is satisfied then a
        // variable becomes grounded on the same
        // level. Without this condition a null point
        // exception will occur.
        if (dom.stamp == level) {

          changeHistory4BooleanVariables[i].domain.removeLevel(
              level, changeHistory4BooleanVariables[i]);
        }
      }
    }

    domainTrail.removeLevel(level);

    trailManager.removeLevel(level);

    while (entailedSize > 0 && entailed[entailedSize - 1].entailedAt() >= level) {
      entailed[--entailedSize].setEntailedAt(Integer.MAX_VALUE);
      entailed[entailedSize] = null;
    }

    for (int i = mutableVariables.size() - 1; i >= 0; i--) {
      mutableVariables.get(i).removeLevel(level);
    }

    for (Object c : ((ListenerSet<RemoveLevelLate>) removeLevelLateListeners).elements()) {
      ((RemoveLevelLate) c).removeLevelLate(level);
    }

    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
  }

  /**
   * Returns the state of this store in a chain of derived stores.
   *
   * @return the state; {@link StoreState#ACTIVE} for a store that never derived a child.
   */
  public StoreState state() {
    return state;
  }

  /**
   * Sets the state of this store; only a derivation calls it.
   *
   * @param state the new state.
   */
  public void setState(StoreState state) {
    this.state = state;
  }

  /**
   * Runs a step of a derivation's return path (writing a child's solution into this store and
   * propagating it), which a store that is not {@link StoreState#ACTIVE} otherwise refuses.
   *
   * @param step the step.
   */
  public void runReturning(Runnable step) {
    boolean previous = returning;
    returning = true;
    try {
      step.run();
    } finally {
      returning = previous;
    }
  }

  private void checkImposeAllowed() {
    // propagating a returned solution may impose constraints, such as the consequent of IfThen
    if (state != StoreState.ACTIVE && !returning) {
      throw new IllegalStateException("Store is " + state + "; it cannot impose constraints");
    }
  }

  /**
   * Switches on recording: from now on every constraint imposed through this store's {@code impose}
   * methods, including the constraints of decompositions, is appended to {@link #model()}. Checking
   * presolve against the whole original model needs it, so it has to be switched on before the
   * first constraint is imposed.
   *
   * @param on true to record.
   */
  public void recordModel(boolean on) {
    if (on && model == null) {
      model = new ArrayList<>();
    } else if (!on) {
      model = null;
    }
  }

  /**
   * Returns the constraints recorded so far, in imposition order.
   *
   * @return the recorded constraints, or an empty list if recording is off.
   */
  public List<Constraint> model() {
    return model == null ? List.of() : Collections.unmodifiableList(model);
  }

  private void record(Constraint c) {
    if (model != null) {
      model.add(c);
    }
  }

  /**
   * Records the first consistency call of a constraint at the current level. If an earlier first
   * call was undone by removing its level, the constraint's variables are queued again, as imposing
   * the constraint did, since the constraint dropped what it had queued with that level.
   *
   * @param c the constraint about to be called.
   */
  private void startFirstRun(Constraint c) {
    if (c.firstRunAt() == Constraint.RUN_UNDONE && c instanceof UsesQueueVariable) {
      c.arguments().forEach(v -> c.queueVariable(level, v));
    }
    c.setFirstRunAt(level);
    if (firstRunsSize == firstRuns.length) {
      firstRuns = Arrays.copyOf(firstRuns, firstRunsSize * 2);
    }
    firstRuns[firstRunsSize++] = c;
  }

  /**
   * Records one-time work done at the current level, so that removing the level makes it due again.
   *
   * @param work the work just done.
   */
  void recordInitOnce(InitOnce work) {
    if (initOnceSize == initOnce.length) {
      initOnce = Arrays.copyOf(initOnce, 2 * initOnceSize);
    }
    initOnce[initOnceSize++] = work;
  }

  /**
   * This function sets the id of the store. This id is used when saving to XML file.
   *
   * @param id store id.
   */
  public void setId(String id) {
    this.id = id;
  }

  /**
   * This function allows to proceed with the search, create new layer at which new values for
   * variables will be recorded. This function is also used during backtracking, after removing
   * current level the store can be set to the previous level.
   *
   * @param levelSetTo level number to which store is changing to.
   */
  public void setLevel(int levelSetTo) {

    if (state != StoreState.ACTIVE && !returning && levelSetTo != level) {
      throw new IllegalStateException("Store is " + state + "; it cannot change its level");
    }

    trailManager.setLevel(levelSetTo);

    if (level == levelSetTo) {
      return;
    }

    if (removeDebug && level > levelSetTo && level > 0) {

      for (int i = 0; i < size; i++) {

        if (ASSERTS_ENABLED
            && vars[i].level() >= level
            && !trailManager.isRecognizedAsChanged(vars[i].storeIndex)) {
          throw new IllegalStateException(
              String.valueOf("Variable position " + i + " not properly recorded to have changed "));
        }
      }
    }

    if (removeDebug) {
      log.debug("Store level changes from {} to {}", level, levelSetTo);
    }

    level = levelSetTo;
  }

  /**
   * It returns number of variables in a store.
   *
   * @return number of variables in a store.
   */
  public int size() {
    return size;
  }

  /**
   * It throws an exception after printing trace information if tracing is switched on.
   *
   * @param x variable causing the failure exception.
   * @throws FailException is always thrown.
   */
  public void throwFailException(Var x) {

    throw failException;
  }

  /**
   * This function returns a string a representation of the store. Whatever seems important may be
   * included here.
   */
  @Override
  public String toString() {

    StringBuilder result = new StringBuilder();

    result.append("\n*** Store\n");

    // first BooleanVar
    for (Var v : variablesHashMap.values()) {
      if (v instanceof BooleanVar) {
        result.append(v).append("\n");
      }
    }

    // all other variables
    for (int i = 0; i < size; i++) {
      result.append(vars[i]).append("\n");
    }

    int i = 0;
    for (MutableVar v : mutableVariables) {
      result
          .append("MutableVar[")
          .append(i++)
          .append("] ")
          .append("(")
          .append(v.value().stamp())
          .append(")");

      result.append(v.value()).append("\n");
    }

    for (Constraint c : getConstraints()) {
      result.append("*** Constraint:\n").append(c).append("\n");
    }

    result.append("\n*** Constraints for evaluation:\n{").append(toStringChangedEl()).append(" }");

    return result.toString();
  }

  /**
   * Returns the set of all constraints associated with variables in this store.
   *
   * @return set of all constraints.
   */
  public Set<Constraint> getConstraints() {

    Set<Constraint> constraints = new LinkedHashSet<>();

    for (Var v : variablesHashMap.values()) {
      Domain d = v.dom();
      List<Constraint> c = d.constraints();
      constraints.addAll(c);
    }

    return constraints;
  }

  private void updateAfc(Constraint failed) {
    if (allConstraints == null) {
      setAllConstraints();
    }
    // constraints imposed after setAllConstraints() are registered when they first fail
    allConstraints.add(failed);
    afcIncrement /= Math.max(decay, 1e-3d);
    failed.updateAfc(afcIncrement);
    if (afcIncrement > AFC_RESCALE_LIMIT) {
      allConstraints.addAll(getConstraints());
      double factor = 1.0d / afcIncrement;
      for (Constraint c : allConstraints) {
        c.scaleAfc(factor);
      }
      afcIncrement = 1.0d;
    }
  }

  /** Caches the set of all constraints currently present in this store. */
  public void setAllConstraints() {
    allConstraints = getConstraints();
  }

  public double getDecay() {
    return decay;
  }

  public void setDecay(double d) {
    decay = d;
  }

  /**
   * Enables or disables accumulated failure count (AFC) management for constraints.
   *
   * @param m true to enable AFC management, false to disable.
   */
  public void afcManagement(boolean m) {
    constraintAfcManagement = m;
  }

  /**
   * Enables or disables variable activity management for search heuristics.
   *
   * @param m true to enable activity management, false to disable.
   */
  public void activityManagement(boolean m) {
    variableActivityManagement = m;
    variablesPrunned = new LinkedHashSet<>();
  }

  void updateActivities(Constraint constraint) {
    for (Var v : variablesPrunned) {
      v.updateActivity();
    }

    if (decay < 1.0d) {
      for (Var v : constraint.arguments()) {
        if (!variablesPrunned.contains(v)) {
          v.applyDecay();
        }
      }
    }
  }

  /**
   * This function returns a string representation of the constraints pending for re-evaluation.
   *
   * @return string description of changed constraints.
   */
  public String toStringChangedEl() {

    StringBuilder c = new StringBuilder();

    for (int i = 0; i < queueNo; i++) {
      c.append(changed[i].toString()).append("\n");
    }

    return c.toString();
  }

  /**
   * It checks invariants to see if the execution went smoothly.
   *
   * @return description of the violated invariant, null otherwise.
   */
  public String checkInvariants() {

    for (int i = 0; i < size; i++) {
      if (vars[i].level() > level) {
        return "Removal of old values was done properly " + vars[i];
      }
    }

    return null;
  }

  /**
   * Returns a string representation of all variables in this store, ordered alphabetically by id.
   *
   * @return string representation of ordered variables.
   */
  public String toStringOrderedVars() {

    StringBuilder result = new StringBuilder();

    result.append("[");

    // first BooleanVar
    for (String key : new TreeSet<>(variablesHashMap.keySet())) {
      Var v = variablesHashMap.get(key);
      if (v instanceof BooleanVar) {
        result.append(v).append(",");
      }
    }

    // all other variables
    TreeSet<Var> orderedVariables = new TreeSet<>(Comparator.comparing(Var::id));
    orderedVariables.addAll(Arrays.asList(vars).subList(0, size));
    for (Var v : orderedVariables) {
      result.append(v).append(",");
    }

    int i = 0;
    for (MutableVar v : mutableVariables) {
      result
          .append("MutableVar[")
          .append(i++)
          .append("] ")
          .append("(")
          .append(v.value().stamp())
          .append(")");
      result.append(v.value()).append(",");
    }

    result.replace(result.length() - 1, result.length(), "]");
    return result.toString();
  }
}
