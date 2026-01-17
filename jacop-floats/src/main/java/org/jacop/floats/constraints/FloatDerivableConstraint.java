/*
 * FloatDerivableConstraint.java
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

package org.jacop.floats.constraints;

import org.jacop.core.Store;
import org.jacop.floats.core.FloatVar;

import java.util.Set;

/**
 * Marker interface for float constraints that support derivative computation.
 * <p>
 * This interface allows Derivative.java to safely call derivative() method
 * without requiring it to be defined in the base Constraint class from jacop-core.
 * Only float constraints that implement this interface can be used with
 * the Derivative utility class.
 *
 * @author Generated for multi-module refactoring
 * @version 4.11
 */
public interface FloatDerivableConstraint {
    /**
     * Computes the derivative of this constraint with respect to variable x.
     *
     * @param store the constraint store
     * @param f     the function variable
     * @param vars  set of variables
     * @param x     the variable to differentiate with respect to
     * @return the derivative as a FloatVar
     */
    FloatVar derivative(Store store, FloatVar f, Set<FloatVar> vars, FloatVar x);
}
