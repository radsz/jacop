/*
 * Constraint.java
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

package org.jacop.constraints;

import static java.util.stream.Collectors.joining;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;
import lombok.AccessLevel;
import lombok.NoArgsConstructor;
import org.jacop.api.RemoveLevelLate;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.SwitchesPruningLogging;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.util.BipartiteGraphMatching;

/**
 * Standard unified interface/abstract class for all constraints.
 *
 * <p>Defines how to construct a constraint, impose, check satisfiability, notSatisfiability,
 * enforce consistency.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@NoArgsConstructor(access = AccessLevel.PROTECTED)
public abstract class Constraint extends DecomposedConstraint<Constraint> {

  /**
   * It specifies if upon the failure of the constraint, all variables in the constraint scope
   * should have their weight increased.
   */
  public final boolean isIncreaseWeightEnabled = true;

  public boolean trace = SwitchesPruningLogging.traceConstraint;

  /**
   * It specifies the number id for a given constraint. All constraints within the same type have
   * unique number ids.
   */
  public int numberId;

  public Set<PrimitiveConstraint> constraintScope;

  /** It specifies the event which must occur in order for the consistency function to be called. */
  public Hashtable<Var, Integer> consistencyPruningEvents;

  /**
   * It specifies if the constraint consistency function can be prematurely terminated through other
   * than FailureException exception.
   */
  public boolean earlyTerminationOk;

  /**
   * It specifies if the constraint consistency function requires consistency function executed in
   * one atomic step. A constraint can specify that if any other pruning events are initiated by
   * outside entity then the constraint may not work correctly if the execution is continued, but it
   * will work well if consistency() function is restarted.
   */
  public boolean atomicExecution = true;

  /** It specifies a set of variables that in the scope of this constraint. */
  protected Set<Var> scope;

  Var watchedVariableGrounded;
  /*
   * Handling of AFC (accumulated failure count) for constraints
   *
   */
  double afcWeight = 1.0d;

  /**
   * Constructs a constraint with the specified variable arrays as its scope.
   *
   * @param vars arrays of variables forming the constraint scope.
   */
  protected Constraint(Var[]... vars) {
    setScope(vars);
  }

  /**
   * Constructs a constraint with the scope defined by a stream of variables.
   *
   * @param vars stream of variables forming the constraint scope.
   */
  protected Constraint(Stream<Var> vars) {
    setScope(vars);
  }

  /**
   * Constructs a constraint with scope derived from the given primitive constraints.
   *
   * @param constraints primitive constraints whose variable scopes define this constraint's scope.
   */
  protected Constraint(PrimitiveConstraint[] constraints) {
    setScope(constraints);
  }

  /**
   * Constructs a constraint with scope defined by the given set of variables.
   *
   * @param set the set of variables forming the constraint scope.
   */
  protected Constraint(Set<? extends Var> set) {
    setScope(set);
  }

  /**
   * Converts an integer array to a formatted string representation.
   *
   * @param array the integer array to convert.
   * @return a string representation of the array in the format "[v1, v2, ...]".
   */
  public static String intArrayToString(int[] array) {
    return Arrays.stream(array).mapToObj(Integer::toString).collect(joining(", ", "[", "]"));
  }

  static int toInt(final float f) {
    if (f >= Integer.MIN_VALUE && f <= Integer.MAX_VALUE) {
      return (int) f;
    } else {
      throw new ArithmeticException("Overflow occurred " + f);
    }
  }

  static int toInt(final double f) {
    if (f >= Integer.MIN_VALUE && f <= Integer.MAX_VALUE) {
      return (int) f;
    } else {
      throw new ArithmeticException("Overflow occurred " + f);
    }
  }

  static long toLong(final double f) {
    if (f >= Long.MIN_VALUE && f <= Long.MAX_VALUE) {
      return (long) f;
    } else {
      throw new ArithmeticException("Overflow occurred " + f);
    }
  }

  /**
   * Safely converts a long value to an int, clamping to Integer.MAX_VALUE or Integer.MIN_VALUE on
   * overflow.
   *
   * @param value the long value to convert.
   * @return the int representation, clamped to integer bounds if necessary.
   */
  public static int long2int(long value) {
    if (value > Integer.MAX_VALUE) {
      return Integer.MAX_VALUE;
    } else if (value < Integer.MIN_VALUE) {
      return Integer.MIN_VALUE;
    } else {
      return (int) value;
    }
  }

  /**
   * It returns the variables in a scope of the constraint.
   *
   * @return variables in a scope of the constraint.
   */
  public Set<Var> arguments() {
    return scope;
  }

  protected void setScope(Var... variables) {
    this.scope = Collections.unmodifiableSet(new HashSet<>(Arrays.asList(variables)));
  }

  /**
   * Sets the constraint scope from multiple variable arrays.
   *
   * @param variables arrays of variables to include in the scope.
   */
  protected void setScope(Var[]... variables) {
    setScope(Arrays.stream(variables).flatMap(Arrays::stream));
  }

  /**
   * Sets the constraint scope from a stream of variables.
   *
   * @param scope stream of variables to include in the scope.
   */
  protected void setScope(Stream<Var> scope) {
    setScope(scope.toArray(Var[]::new));
  }

  /**
   * Sets the constraint scope from the variable scopes of the given primitive constraints.
   *
   * @param constraints primitive constraints whose variable scopes define this constraint's scope.
   */
  protected void setScope(PrimitiveConstraint[] constraints) {
    setScope(Arrays.stream(constraints).map(Constraint::arguments).flatMap(Collection::stream));
  }

  /**
   * Sets the constraint scope from a set of variables.
   *
   * @param set the set of variables to include in the scope.
   */
  protected void setScope(Set<? extends Var> set) {
    setScope(set.toArray(new Var[0]));
  }

  protected void setConstraintScope(PrimitiveConstraint... primitiveConstraints) {
    this.constraintScope =
        Collections.unmodifiableSet(new HashSet<>(Arrays.asList(primitiveConstraints)));
  }

  /**
   * It is a (most probably incomplete) consistency function which removes the values from variables
   * domains. Only values which do not have any support in a solution space are removed.
   *
   * @param store constraint store within which the constraint consistency is being checked.
   */
  public abstract void consistency(Store store);

  /**
   * It retrieves the pruning event which causes reevaluation of the constraint.
   *
   * @param var variable for which pruning event is retrieved
   * @return it returns the int code of the pruning event (GROUND, BOUND, ANY, NONE)
   */
  public int getConsistencyPruningEvent(Var var) {

    // If consistency function mode
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(var);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }

    if (constraintScope != null && !constraintScope.isEmpty()) {

      int eventAcross =
          constraintScope.stream()
              .filter(i -> i.arguments().contains(var))
              .mapToInt(i -> i.getNestedPruningEvent(var, true))
              .max()
              .orElse(Integer.MIN_VALUE);

      if (eventAcross != Integer.MIN_VALUE) {
        return eventAcross;
      }
    }

    return getDefaultConsistencyPruningEvent();
  }

  /**
   * It returns the default pruning event used for consistency checking when no specific event is
   * defined for a variable.
   *
   * @return the int code of the default pruning event.
   */
  public abstract int getDefaultConsistencyPruningEvent();

  /**
   * It gives the id string of a constraint.
   *
   * @return string id of the constraint.
   */
  public String id() {
    String constraintType = this.getClass().getSimpleName();
    if (constraintType.isEmpty()) {
      constraintType = this.getClass().getName() + "#";
    }
    return constraintType + numberId;
  }

  /**
   * It imposes the constraint and adjusts the queue index.
   *
   * @param store the constraint store to which the constraint is imposed to.
   * @param queueIndex the index of the queue in the store it is assigned to.
   */
  public void impose(Store store, int queueIndex) {

    assert queueIndex < store.queueNo : "Constraint queue number larger than permitted by store.";

    this.queueIndex = queueIndex;

    impose(store);
  }

  /**
   * It imposes the constraint in a given store.
   *
   * @param store the constraint store to which the constraint is imposed to.
   */
  public void impose(Store store) {

    arguments().forEach(i -> i.putModelConstraint(this, getConsistencyPruningEvent(i)));
    store.addChanged(this);
    store.countConstraint();
    if (constraintScope != null) {
      constraintScope.forEach(i -> i.include(store));
    }
    if (this instanceof UsesQueueVariable) {
      arguments().forEach(i -> queueVariable(store.level, i));
    }

    if (constraintScope != null) {
      Set<RemoveLevelLate> fixpoint = computeFixpoint(this, new HashSet<>());
      fixpoint.forEach(store::registerRemoveLevelLateListener);
    }

    if (this instanceof RemoveLevelLate late) {
      store.registerRemoveLevelLateListener(late);
    }

    if (this instanceof Stateful c && c.isStateful()) {
      store.registerRemoveLevelListener(c);
    }
  }

  /**
   * This is a function called to indicate which variable in a scope of constraint has changed. It
   * also indicates a store level at which the change has occurred.
   *
   * @param level the level of the store at which the change has occurred.
   * @param var variable which has changed.
   */
  public void queueVariable(final int level, final Var var) {}

  private Set<RemoveLevelLate> computeFixpoint(Constraint c, Set<RemoveLevelLate> fixpoint) {
    if (c instanceof RemoveLevelLate late) {
      fixpoint.add(late);
    }
    if (c.constraintScope != null) {
      c.constraintScope.forEach(ic -> computeFixpoint(ic, fixpoint));
    }
    return fixpoint;
  }

  /** It removes the constraint by removing this constraint from all variables. */
  public void removeConstraint() {
    // Stream version is not used due to large performance overhead.
    for (Var v : arguments()) {
      if (!v.singleton()) {
        v.removeConstraint(this);
      }
    }
  }

  /**
   * Sets the watched variable used as a quick check for groundedness.
   *
   * @param var the variable to watch for grounding.
   */
  public void setWatchedVariableGrounded(Var var) {
    watchedVariableGrounded = var;
  }

  /**
   * Checks whether the watched variable is grounded (singleton) or no watched variable is set.
   *
   * @return true if no watched variable is set or the watched variable is a singleton.
   */
  public boolean watchedVariableGrounded() {
    return watchedVariableGrounded == null || watchedVariableGrounded.singleton();
  }

  /**
   * It checks if the constraint has all variables in its scope grounded (singletons).
   *
   * @return true if all variables in constraint scope are singletons, false otherwise.
   */
  public boolean grounded() {

    if (!watchedVariableGrounded()) {
      return false;
    }

    Optional<Var> stillNotGrounded = arguments().stream().filter(i -> !i.singleton()).findFirst();

    if (stillNotGrounded.isPresent()) {
      setWatchedVariableGrounded(stillNotGrounded.get());
      return false;
    } else {
      return true;
    }
  }

  /**
   * It checks if provided variables are grounded (singletons).
   *
   * @param vars variables to be checked if they are grounded.
   * @return true if all variables in constraint scope are singletons, false otherwise.
   */
  public boolean grounded(Var[] vars) {
    return Arrays.stream(vars).filter(i -> !i.singleton()).findFirst().isEmpty();
  }

  /** It produces a string representation of a constraint state. */
  @Override
  public String toString() {
    return arguments().stream().map(Object::toString).collect(joining(", ", id() + "(", ")"));
  }

  /**
   * It specifies a constraint which if imposed by search will enhance propagation of this
   * constraint.
   *
   * @return Constraint enhancing propagation of this constraint.
   */
  public Constraint getGuideConstraint() {
    return null;
  }

  /**
   * This function provides a variable which assigned a value returned by will enhance propagation
   * of this constraint.
   *
   * @return Variable which is a base of enhancing constraint.
   */
  public Var getGuideVariable() {
    return null;
  }

  /**
   * This function provides a value which if assigned to a variable returned by getGuideVariable()
   * will enhance propagation of this constraint.
   *
   * @return Value which is a base of enhancing constraint.
   */
  public int getGuideValue() {
    return Integer.MAX_VALUE;
  }

  /** It increases the weight of the variables in the constraint scope. */
  public void increaseWeight() {

    if (isIncreaseWeightEnabled) {
      arguments().forEach(v -> v.weight++);
    }
  }

  /**
   * It allows to customize the event for a given variable which causes the re-execution of the
   * consistency method for a constraint.
   *
   * @param var variable for which the events are customized.
   * @param pruningEvent the event which must occur to trigger execution of the consistency method.
   */
  public void setConsistencyPruningEvent(final Var var, final int pruningEvent) {

    if (consistencyPruningEvents == null) {
      consistencyPruningEvents = new Hashtable<>();
    }
    consistencyPruningEvents.put(var, pruningEvent);
  }

  /**
   * It returns the number of variables within a constraint scope.
   *
   * @return number of variables in the constraint scope.
   */
  public int numberArgs() {
    return scope.size();
  }

  @Override
  public void imposeDecomposition(Store store) {
    throw new UnsupportedOperationException();
  }

  @Override
  public List<Constraint> decompose(final Store store) {
    throw new UnsupportedOperationException();
  }

  /**
   * Returns the accumulated failure count (AFC) weight of this constraint.
   *
   * @return the current AFC weight.
   */
  public double afc() {
    return afcWeight;
  }

  /**
   * Updates the accumulated failure count (AFC) weight with decay, rescaling all constraint weights
   * if overflow is imminent.
   *
   * @param allConstraints the set of all constraints used for rescaling on overflow.
   * @param decay the decay factor applied to the updated weight.
   */
  public void updateAfc(Set<Constraint> allConstraints, double decay) {
    afcWeight = (afcWeight + 1.0d) / decay;

    if (afcWeight > Double.MAX_VALUE * 1e-50) {
      // re-scale weights
      for (Constraint c : allConstraints) {
        c.afcWeight *= 1e-150;
      }
    }
  }

  /** It is executed after the constraint has failed. It allows to clean some data structures. */
  public void cleanAfterFailure() {}

  /**
   * Appends the string representation of each element in the array to the StringBuilder, separated
   * by commas.
   *
   * @param sb the StringBuilder to append to.
   * @param array the array of objects to append.
   */
  protected static void appendArrayToString(StringBuilder sb, Object[] array) {
    for (int i = 0; i < array.length; i++) {
      sb.append(array[i]);
      if (i < array.length - 1) {
        sb.append(", ");
      }
    }
  }

  /**
   * Computes the maximum bipartite matching between the given variables and their domain values
   * using the Hopcroft-Karp algorithm.
   *
   * @param vs the array of integer variables.
   * @return the size of the maximum matching.
   */
  protected static int computeMaxBipartiteMatching(IntVar[] vs) {
    Map<Integer, Integer> valueMap = new HashMap<>();
    int valueIndex = 0;

    int[][] adj = new int[vs.length + 1][];
    adj[0] = new int[0];

    for (int i = 0; i < vs.length; i++) {
      IntVar v = vs[i];

      adj[i + 1] = new int[v.dom().getSize()];
      int j = 0;
      for (ValueEnumeration e = v.dom().valueEnumeration(); e.hasMoreElements(); ) {
        int el = e.nextElement();
        Integer elIndex = valueMap.get(el);
        if (elIndex == null) {
          valueMap.put(el, valueIndex);
          adj[i + 1][j] = valueIndex + 1;
          valueIndex++;
        } else {
          adj[i + 1][j] = elIndex + 1;
        }
        j++;
      }
    }

    BipartiteGraphMatching matcher = new BipartiteGraphMatching(adj, vs.length, valueMap.size());
    return matcher.hopcroftKarp();
  }

  /**
   * Checks whether the variables cannot be satisfied by a complete matching, i.e., the maximum
   * bipartite matching is smaller than the number of variables.
   *
   * @param vs the array of integer variables.
   * @return true if the maximum matching is less than the number of variables.
   */
  protected static boolean notSatisfiedByMatching(IntVar[] vs) {
    return computeMaxBipartiteMatching(vs) < vs.length;
  }
}
