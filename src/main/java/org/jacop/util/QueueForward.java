/*
 * QueueForward.java
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

package org.jacop.util;

import org.jacop.constraints.Constraint;
import org.jacop.api.UsesQueueVariable;
import org.jacop.core.Var;

import java.util.*;

/**
 * Utility class that allows for constraints like Xor, Reified, etc that take other constraints
 * as parameters to forward any changes of variables to the constraints that were provided as arguments.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */
public class QueueForward<T extends Constraint> {

    final public Map<Var, List<T>> forwardMap;

    final public boolean isEmpty;

    public QueueForward(Collection<T> constraints, Collection<Var> variables) {

        forwardMap = Var.createEmptyPositioning();

        for (Var var : variables) {
            forwardMap.put(var, new ArrayList<T>());
            for (T constraint : constraints) {

                if (constraint instanceof UsesQueueVariable && constraint.arguments().contains(var)) {

                    try {
                        // We assume that all constraint needing queueVariable declare this method, even for
                        // the ones that inherit from other constraints.
                        constraint.getClass().getDeclaredMethod("queueVariable", int.class, Var.class);
                        forwardMap.get(var).add(constraint);
                    } catch (NoSuchMethodException e) {
                        // constraint may use empty queueVariable provided by abstract class Constraint
                    }
                }
            }
        }

        for (Var var : variables) {

            List<T> varConstraints = forwardMap.get(var);

            if (varConstraints == null)
                continue;

            if (varConstraints.isEmpty())
                forwardMap.remove(var);

        }

        isEmpty = forwardMap.isEmpty();

    }

    public QueueForward(T[] constraints, Var[] vars) {
        this(Arrays.asList(constraints), Arrays.asList(vars));
    }

    public QueueForward(T[] constraints, Collection<Var> vars) {
        this(Arrays.asList(constraints), vars);
    }

    public QueueForward(T constraint, Collection<Var> vars) {
        this(Arrays.asList(constraint), vars);
    }

    public QueueForward(Collection<T> constraints, Var var) {
        this(constraints, Arrays.asList(var));
    }

    public QueueForward(T constraint, Var var) {
        this(Arrays.asList(constraint), Arrays.asList(var));
    }

    public boolean isEmpty() {
        return isEmpty;
    }

    public void queueForward(int level, Var variable) {

        if (isEmpty)
            return;

        List<T> constraints = forwardMap.get(variable);

        if (constraints == null)
            return;

        for (Constraint constraint : constraints) {
            constraint.queueVariable(level, variable);
        }
    }

}
