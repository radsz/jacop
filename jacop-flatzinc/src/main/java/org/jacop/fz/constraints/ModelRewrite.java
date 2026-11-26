/*
 * ModelRewrite.java
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

package org.jacop.fz.constraints;

import java.util.HashSet;
import java.util.Set;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.fz.ParserTreeConstants;
import org.jacop.fz.SimpleNode;

/**
 * A rewrite of constraint items of the parsed model: it posts its own constraints in place of the
 * items it replaces, and some variables leave the model with them.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
abstract class ModelRewrite implements ParserTreeConstants {

  /** The support of the FlatZinc front end. */
  final Support support;

  /** The variables of the solve item and of the output, which stay in the model. */
  final Set<IntVar> kept;

  /** The constraint items that are not posted. */
  final Set<SimpleNode> replaced = new HashSet<>();

  /** The variables that left the model. */
  final Set<Var> removed = new HashSet<>();

  ModelRewrite(Support support, Set<IntVar> kept) {
    this.support = support;
    this.kept = kept;
  }

  /**
   * The constraint items that the rewrite replaced; they are not posted.
   *
   * @return the constraint nodes.
   */
  public Set<SimpleNode> replaced() {
    return replaced;
  }

  /**
   * The variables that left the model.
   *
   * @return the variables.
   */
  public Set<Var> removed() {
    return removed;
  }
}
