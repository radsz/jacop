/*
 * SetDomainOperationHandler.java
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

package org.jacop.set.search;

import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DomainOperationHandler;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * Handler for SetVar domain operations in search algorithms. This implementation handles set
 * variable domain operations with proper GLB (Greatest Lower Bound) and LUB (Least Upper Bound)
 * handling.
 *
 * @author Generated for multi-module refactoring
 * @version 4.11
 */
public class SetDomainOperationHandler implements DomainOperationHandler {

  @Override
  public boolean isApplicable(Var var) {
    return var instanceof SetVar;
  }

  @Override
  public void inValue(Store store, Var var, int value, boolean leftBranch) {
    if (!(var instanceof SetVar)) {
      throw new IllegalArgumentException("SetDomainOperationHandler can only handle SetVar");
    }
    SetVar setVar = (SetVar) var;
    SetDomain setDomain = (SetDomain) setVar.dom();
    if (leftBranch) {
      // Left branch: add element to GLB (Greatest Lower Bound)
      setDomain.inGLB(store.level, setVar, value);
    } else {
      // Right branch: remove element from LUB (add to LUB complement)
      setDomain.inLUBComplement(store.level, setVar, value);
    }
  }

  @Override
  public void inComplement(Store store, Var var, int value, boolean leftBranch) {
    if (!(var instanceof SetVar)) {
      throw new IllegalArgumentException("SetDomainOperationHandler can only handle SetVar");
    }
    SetVar setVar = (SetVar) var;
    SetDomain setDomain = (SetDomain) setVar.dom();
    if (leftBranch) {
      // Left branch: remove from GLB (add to LUB complement)
      setDomain.inLUBComplement(store.level, setVar, value);
    } else {
      // Right branch: add to GLB
      setDomain.inGLB(store.level, setVar, value);
    }
  }

  @Override
  public String getDomainString(Var var) {
    if (!(var instanceof SetVar)) {
      throw new IllegalArgumentException("SetDomainOperationHandler can only handle SetVar");
    }
    SetVar setVar = (SetVar) var;
    return setVar.dom().toString();
  }
}
