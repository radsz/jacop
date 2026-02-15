/*
 * SwitchesPruningLogging.java
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

/**
 * It is a container class which specifies all different switches to turn on debugging information.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@SuppressWarnings("PointlessBooleanExpression")
public final class SwitchesPruningLogging {

  /** It is a general switch which can be turned off to switch off all printouts. */
  public static final boolean TRACE = false;

  /** The switch which enables to switch on/off the switches concerning Store operation. */
  public static final boolean TRACE_STORE = TRACE && true;

  /** This switch enables to trace constraints which are being checked for consistency. */
  public static boolean traceConsistencyCheck = TRACE && TRACE_STORE && true;

  /** This switch enables tracing the constraint added to the constraint queue. */
  public static boolean traceQueueingConstraint = TRACE && TRACE_STORE && true;

  /**
   * This switch enables tracing attempt to add the constraint to a queue when it is already added.
   */
  public static boolean traceAlreadyQueuedConstraint = TRACE && TRACE_STORE && true;

  /** This switch enables to traces the constraints which are being imposed. */
  public static boolean traceConstraintImposition = TRACE && TRACE_STORE && true;

  /** It informs what traced constraints failed. */
  public static boolean traceFailedConstraint = TRACE && TRACE_STORE && true;

  /** This switch enables to trace remove level operation. */
  public static boolean traceLevelRemoval = TRACE && TRACE_STORE && true;

  /** This switch enables to trace set the store level. */
  public static boolean traceOperationsOnLevel = TRACE && TRACE_STORE && true;

  /** It specifies if the search traces are active. */
  public static final boolean TRACE_SEARCH = TRACE && true;

  /** It traces the decisions within search. */
  public static final boolean TRACE_SEARCH_TREE = TRACE && TRACE_SEARCH && true;

  /** It turns on all trace printouts in constraints. */
  public static final boolean TRACE_CONSTRAINT = TRACE && true;

  /** It turns on all trace printouts in variables. */
  public static boolean traceVar = TRACE && true;

  /** It traces all constraints have failed. */
  public static boolean traceConstraintFailure = TRACE && true;

  /** This switch enables to trace removal of the store level. */
  public static boolean traceStoreRemoveLevel = TRACE && true;

  /** This switch enables to trace creation of the variable. */
  public static boolean traceVariableCreation = TRACE && true;

  private SwitchesPruningLogging() {}

  /**
   * Logs a message if the given switch is enabled.
   *
   * @param isEnabled whether logging is enabled
   * @param fromClass the class from which the log originates
   * @param pattern the message pattern
   * @param args the arguments for the pattern
   */
  public static void log(boolean isEnabled, Class<?> fromClass, String pattern, Object[] args) {
    // No-op: stub implementation when pruning trace logging is disabled.
  }

  /**
   * Logs a message if the given switch is enabled.
   *
   * @param isEnabled whether logging is enabled
   * @param fromClass the class from which the log originates
   * @param pattern the message pattern
   * @param arg1 the first argument for the pattern
   */
  public static void log(boolean isEnabled, Class<?> fromClass, String pattern, Object arg1) {
    // No-op: stub implementation when pruning trace logging is disabled.
  }

  /**
   * Logs a message if the given switch is enabled.
   *
   * @param isEnabled whether logging is enabled
   * @param fromClass the class from which the log originates
   * @param pattern the message pattern
   * @param arg1 the first argument for the pattern
   * @param arg2 the second argument for the pattern
   */
  public static void log(
      boolean isEnabled, Class<?> fromClass, String pattern, Object arg1, Object arg2) {
    // No-op: stub implementation when pruning trace logging is disabled.
  }
}
