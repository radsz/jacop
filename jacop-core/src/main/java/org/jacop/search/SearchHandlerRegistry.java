/*
 * SearchHandlerRegistry.java
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

package org.jacop.search;

import java.util.Arrays;
import org.jacop.core.Var;

/**
 * Registry for managing cost variable and domain operation handlers. This registry allows modules
 * (jacop-floats, jacop-sets) to register their type-specific handlers, enabling search algorithms
 * to work with different variable types without direct dependencies.
 *
 * <p>Handlers are registered in order of priority. When looking up a handler, the first applicable
 * handler is returned.
 *
 * @author Generated for multi-module refactoring
 * @version 4.11
 */
public class SearchHandlerRegistry {

  /** The registry is created when it is first used, without a lock on every later lookup. */
  private static final class Holder {
    private static final SearchHandlerRegistry INSTANCE = new SearchHandlerRegistry();
  }

  // The handlers are kept in arrays that are replaced on every change, so the lookups done by the
  // search at every node neither lock nor allocate an iterator.
  private volatile CostVariableHandler[] costHandlers = new CostVariableHandler[0];
  private volatile DomainOperationHandler[] domainHandlers = new DomainOperationHandler[0];

  private SearchHandlerRegistry() {
    registerDefaultHandlers();
  }

  /**
   * Gets the singleton instance of the registry.
   *
   * @return the registry instance
   */
  public static SearchHandlerRegistry getInstance() {
    return Holder.INSTANCE;
  }

  private void registerDefaultHandlers() {
    registerCostHandler(new IntCostVariableHandler());
    registerDomainHandler(new IntDomainOperationHandler());
  }

  /**
   * Registers a cost variable handler. Handlers are checked in registration order, so more specific
   * handlers should be registered after general ones.
   *
   * @param handler the handler to register
   */
  public synchronized void registerCostHandler(CostVariableHandler handler) {
    if (handler != null && !Arrays.asList(costHandlers).contains(handler)) {
      CostVariableHandler[] handlers = Arrays.copyOf(costHandlers, costHandlers.length + 1);
      handlers[handlers.length - 1] = handler;
      costHandlers = handlers;
    }
  }

  /**
   * Registers a domain operation handler. Handlers are checked in registration order, so more
   * specific handlers should be registered after general ones.
   *
   * @param handler the handler to register
   */
  public synchronized void registerDomainHandler(DomainOperationHandler handler) {
    if (handler != null && !Arrays.asList(domainHandlers).contains(handler)) {
      DomainOperationHandler[] handlers = Arrays.copyOf(domainHandlers, domainHandlers.length + 1);
      handlers[handlers.length - 1] = handler;
      domainHandlers = handlers;
    }
  }

  /**
   * Finds an applicable cost variable handler for the given variable.
   *
   * @param v the variable to find a handler for
   * @return the first applicable handler, or null if none found
   */
  public CostVariableHandler findCostHandler(Var v) {
    for (CostVariableHandler handler : costHandlers) {
      if (handler.isApplicable(v)) {
        return handler;
      }
    }
    return null;
  }

  /**
   * Finds an applicable domain operation handler for the given variable.
   *
   * @param v the variable to find a handler for
   * @return the first applicable handler, or null if none found
   */
  public DomainOperationHandler findDomainHandler(Var v) {
    for (DomainOperationHandler handler : domainHandlers) {
      if (handler.isApplicable(v)) {
        return handler;
      }
    }
    return null;
  }

  /** Resets the registry to its default state (only IntVar handlers). Useful for testing. */
  public synchronized void reset() {
    costHandlers = new CostVariableHandler[0];
    domainHandlers = new DomainOperationHandler[0];
    registerDefaultHandlers();
  }
}
