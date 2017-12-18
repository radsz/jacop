/*
 * SoftAlldifferent.java
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

package org.jacop.constraints;

import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * This class provides soft-alldifferent constraint by decomposing it
 * either into a network flow constraint or a set of primitive constraints.
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.5
 */

public class SoftAlldifferent extends DecomposedConstraint<Constraint> {

    public List<Constraint> decomposition;

    public final IntVar[] xVars;

    public final IntVar costVar;

    public final ViolationMeasure violationMeasure;

    public SoftAlldifferent(IntVar[] xVars, IntVar costVar, ViolationMeasure violationMeasure) {

        checkInputForNullness("xVars", xVars);
        checkInputForNullness(new String[] {"costVar", "violationMeasure"}, new Object[]{costVar, violationMeasure});

        this.xVars = Arrays.copyOf(xVars, xVars.length);
        this.costVar = costVar;
        this.violationMeasure = violationMeasure;
    }

    public List<Constraint> primitiveDecomposition(Store store) {

        if (decomposition == null) {

            decomposition = new ArrayList<Constraint>();

            if (violationMeasure == ViolationMeasure.DECOMPOSITION_BASED) {

                int n = xVars.length;
                List<IntVar> costs = new ArrayList<IntVar>(n * (n - 1));
                for (int i = 0; i < n; i++) {
                    for (int j = 0; j < i; j++) {
                        IntVar v;
                        costs.add(v = new BooleanVar(store));
                        decomposition.add(new Reified(new XeqY(xVars[i], xVars[j]), v));
                    }
                }
                decomposition.add(new SumInt(costs, "==", costVar));

            } else {
                throw new UnsupportedOperationException("Unsupported violation measure " + violationMeasure);
            }

            return decomposition;
        } else {

            List<Constraint> result = new ArrayList<Constraint>();

            if (violationMeasure == ViolationMeasure.DECOMPOSITION_BASED) {

                int n = xVars.length;
                List<IntVar> costs = new ArrayList<IntVar>(n * (n - 1));
                for (int i = 0; i < n; i++) {
                    for (int j = 0; j < i; j++) {
                        IntVar v;
                        costs.add(v = new BooleanVar(store));
                        result.add(new Reified(new XeqY(xVars[i], xVars[j]), v));
                    }
                }
                result.add(new SumInt(costs, "==", costVar));

            } else {
                throw new UnsupportedOperationException("Unsupported violation measure " + violationMeasure);
            }

            return result;

        }

        // Do we have to add the cost-vars to the list of auxilary variables
        // auxilaryVariables.addAll(costs);
    }

    @Override public List<Constraint> decompose(Store store) {

        if (decomposition == null || decomposition.size() > 1) {

            decomposition = new ArrayList<Constraint>();

            // compute union of all domains
            IntDomain all = new IntervalDomain();
            for (IntVar v : xVars)
                all.addDom(v.domain);

            // create values
            int d = all.getSize();
            IntDomain[] doms = new IntDomain[d];
            ValueEnumeration it = all.valueEnumeration();
            for (int i = 0; it.hasMoreElements(); i++) {
                int value = it.nextElement();
                doms[i] = new BoundDomain(value, value);
            }

            // create constraint
            decomposition.add(new SoftAlldiffBuilder(doms, violationMeasure).build());

            //	SoftAlldiffBuilder soft = new SoftAlldiffBuilder(doms, violationMeasure);
            //	soft.decompositionConstraints = new ArrayList<Constraint>();
            //	soft.primitiveDecomposition(store);

        }

        return decomposition;
    }

    private class SoftAlldiffBuilder extends NetworkBuilder {

        private SoftAlldiffBuilder(IntDomain[] doms, ViolationMeasure vm) {

            super(costVar);

            int n = xVars.length, m = doms.length;
            Node[] d = valueGraph(xVars, doms)[1];
            Node t = addNode("sink", -n);

            if (vm == ViolationMeasure.VARIABLE_BASED) {
                // connect values to sink
                for (int j = 0; j < m; j++) {
                    addArc(d[j], t, 0, 1);
                    addArc(d[j], t, 1);
                }
            } else if (vm == ViolationMeasure.DECOMPOSITION_BASED) {
                // connect values to sink
                for (int j = 0; j < m; j++)
                    for (int cost = 0; cost < n; cost++)
                        addArc(d[j], t, cost, 0, 1);
            } else {

                throw new UnsupportedOperationException("Unknown violation measure : " + vm);

            }
        }

    }

    @Override public void imposeDecomposition(Store store) {

        if (decomposition == null)
            decomposition = decompose(store);

        for (Constraint c : decomposition)
            store.impose(c);

    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer();

        result.append(" : SoftAlldifferent([");

        for (int i = 0; i < xVars.length; i++) {
            result.append(xVars[i]);
            if (i < xVars.length - 1)
                result.append(", ");
        }
        result.append("], " + costVar + ", " + violationMeasure + ")");

        return result.toString();

    }

}
