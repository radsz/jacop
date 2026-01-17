/*
 * SearchHandlerRegistry.java
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

package org.jacop.search;

import java.util.ArrayList;
import java.util.List;
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

  private static SearchHandlerRegistry instance;

  private final List<CostVariableHandler> costHandlers = new ArrayList<>();
  private final List<DomainOperationHandler> domainHandlers = new ArrayList<>();

  /**
   * Gets the singleton instance of the registry.
   *
   * @return the registry instance
   */
  public static synchronized SearchHandlerRegistry getInstance() {
    if (instance == null) {
      instance = new SearchHandlerRegistry();
      // Register default IntVar handlers
      instance.registerCostHandler(new IntCostVariableHandler());
      instance.registerDomainHandler(new IntDomainOperationHandler());
    }
    return instance;
  }

  /**
   * Registers a cost variable handler. Handlers are checked in registration order, so more specific
   * handlers should be registered after general ones.
   *
   * @param handler the handler to register
   */
  public void registerCostHandler(CostVariableHandler handler) {
    if (handler != null && !costHandlers.contains(handler)) {
      costHandlers.add(handler);
    }
  }

  /**
   * Registers a domain operation handler. Handlers are checked in registration order, so more
   * specific handlers should be registered after general ones.
   *
   * @param handler the handler to register
   */
  public void registerDomainHandler(DomainOperationHandler handler) {
    if (handler != null && !domainHandlers.contains(handler)) {
      domainHandlers.add(handler);
    }
  }

  /**
   * Finds an applicable cost variable handler for the given variable.
   *
   * @param var the variable to find a handler for
   * @return the first applicable handler, or null if none found
   */
  public CostVariableHandler findCostHandler(Var var) {
    for (CostVariableHandler handler : costHandlers) {
      if (handler.isApplicable(var)) {
        return handler;
      }
    }
    return null;
  }

  /**
   * Finds an applicable domain operation handler for the given variable.
   *
   * @param var the variable to find a handler for
   * @return the first applicable handler, or null if none found
   */
  public DomainOperationHandler findDomainHandler(Var var) {
    for (DomainOperationHandler handler : domainHandlers) {
      if (handler.isApplicable(var)) {
        return handler;
      }
    }
    return null;
  }

  /** Resets the registry to its default state (only IntVar handlers). Useful for testing. */
  public synchronized void reset() {
    costHandlers.clear();
    domainHandlers.clear();
    registerCostHandler(new IntCostVariableHandler());
    registerDomainHandler(new IntDomainOperationHandler());
  }
}
