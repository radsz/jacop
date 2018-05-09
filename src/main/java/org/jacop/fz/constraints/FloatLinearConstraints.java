/**
 * FloatLinearConstraints.java
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
package org.jacop.fz.constraints;

import org.jacop.core.Store;
import org.jacop.core.IntVar;
import org.jacop.constraints.Reified;
import org.jacop.core.FailException;

import org.jacop.fz.*;

import org.jacop.floats.core.FloatVar;

import org.jacop.floats.constraints.LinearFloat;
import org.jacop.floats.constraints.PlteqQ;
import org.jacop.floats.constraints.PltQ;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.PplusCeqR;
import org.jacop.floats.constraints.PeqQ;

/**
 *
 * Generation of set constraints in flatzinc
 *
 * @author Krzysztof Kuchcinski 
 *
 */
class FloatLinearConstraints implements ParserTreeConstants {

    boolean reified;
    Support support;
    Store store;
    
    public FloatLinearConstraints(Support support) {
	this.support = support;
	this.store = support.store;
    }

    void gen_float_lin_eq(SimpleNode node) {
        reified = false;
        float_lin_relation(Support.eq, node);
    }

    void gen_float_lin_eq_reif(SimpleNode node) {
        reified = true;
        float_lin_relation(Support.eq, node);
    }

    void gen_float_lin_le(SimpleNode node) {
        reified = false;
        float_lin_relation(Support.le, node);
    }

    void gen_float_lin_le_reif(SimpleNode node) {
        reified = true;
        float_lin_relation(Support.le, node);
    }

    void gen_float_lin_lt(SimpleNode node) {
        reified = false;
        float_lin_relation(Support.lt, node);
    }

    void gen_float_lin_lt_reif(SimpleNode node) {
        reified = true;
        float_lin_relation(Support.lt, node);
    }

    void gen_float_lin_ne(SimpleNode node) {
        reified = false;
        float_lin_relation(Support.ne, node);
    }

    void gen_float_lin_ne_reif(SimpleNode node) {
        reified = true;
        float_lin_relation(Support.ne, node);
    }

    void float_lin_relation(int operation, SimpleNode node) throws FailException {
        // float_lin_*[_reif] (* = eq | ne | lt | gt | le | ge)

        double[] p1 = support.getFloatArray((SimpleNode) node.jjtGetChild(0));
        FloatVar[] p2 = support.getFloatVarArray((SimpleNode) node.jjtGetChild(1));

        double p3 = support.getFloat((ASTScalarFlatExpr) node.jjtGetChild(2));

        if (reified) { // reified
            IntVar p4 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));

            switch (operation) {
                case Support.eq:
                    support.pose(new Reified(new LinearFloat(p2, p1, "==", p3), p4));
                    break;
                case Support.ne:
                    support.pose(new Reified(new LinearFloat(p2, p1, "!=", p3), p4));
                    break;
                case Support.lt:
                    support.pose(new Reified(new LinearFloat(p2, p1, "<", p3), p4));
                    break;
                case Support.le:
                    support.pose(new Reified(new LinearFloat(p2, p1, "<=", p3), p4));
                    break;
                default:
                    throw new IllegalArgumentException("%% ERROR: Constraint floating-point operation not supported.");
            }
        } else { // non reified
            switch (operation) {
                case Support.eq:

                    if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
                        if (p3 != 0)
                            support.pose(new PplusCeqR(p2[1], p3, p2[0]));
                        else
                            support.pose(new PeqQ(p2[1], p2[0]));
                    } else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
                        if (p3 != 0) {
                            support.pose(new PplusCeqR(p2[0], p3, p2[1]));
                        } else
                            support.pose(new PeqQ(p2[0], p2[1]));
                    } else if (p1.length == 2 && p1[0] == 1 && p1[1] == 1) {
                        support.pose(new PplusQeqR(p2[0], p2[1], new FloatVar(store, p3, p3)));
                    } else
                        support.pose(new LinearFloat(p2, p1, "==", p3));
                    break;
                case Support.ne:
                    support.pose(new LinearFloat(p2, p1, "!=", p3));
                    break;
                case Support.lt:
                    if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0)
                        support.pose(new PltQ(p2[0], p2[1]));
                    else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0)
                        support.pose(new PltQ(p2[1], p2[0]));
                    else
                        support.pose(new LinearFloat(p2, p1, "<", p3));
                    break;
                case Support.le:
                    if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0)
                        support.pose(new PlteqQ(p2[0], p2[1]));
                    else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0)
                        support.pose(new PlteqQ(p2[1], p2[0]));
                    else
                        support.pose(new LinearFloat(p2, p1, "<=", p3));
                    break;
                default:
		    throw new IllegalArgumentException("%% ERROR: Constraint floating-point operation not supported.");
            }
        }
    }
}
