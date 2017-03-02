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

import org.jacop.satwrapper.SatTranslation;

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
class FloatLinearConstraints extends Support implements ParserTreeConstants {

    static boolean reified;

    public FloatLinearConstraints(Store store, Tables d, SatTranslation sat) {
        super(store, d, sat);
    }

    static void gen_float_lin_eq(SimpleNode node) {
        reified = false;
        float_lin_relation(eq, node);
    }

    static void gen_float_lin_eq_reif(SimpleNode node) {
        reified = true;
        float_lin_relation(eq, node);
    }

    static void gen_float_lin_le(SimpleNode node) {
        reified = false;
        float_lin_relation(le, node);
    }

    static void gen_float_lin_le_reif(SimpleNode node) {
        reified = true;
        float_lin_relation(le, node);
    }

    static void gen_float_lin_lt(SimpleNode node) {
        reified = false;
        float_lin_relation(lt, node);
    }

    static void gen_float_lin_lt_reif(SimpleNode node) {
        reified = true;
        float_lin_relation(lt, node);
    }

    static void gen_float_lin_ne(SimpleNode node) {
        reified = false;
        float_lin_relation(ne, node);
    }

    static void gen_float_lin_ne_reif(SimpleNode node) {
        reified = true;
        float_lin_relation(ne, node);
    }

    static void float_lin_relation(int operation, SimpleNode node) throws FailException {
        // float_lin_*[_reif] (* = eq | ne | lt | gt | le | ge)

        double[] p1 = getFloatArray((SimpleNode) node.jjtGetChild(0));
        FloatVar[] p2 = getFloatVarArray((SimpleNode) node.jjtGetChild(1));

        double p3 = getFloat((ASTScalarFlatExpr) node.jjtGetChild(2));

        if (reified) { // reified
            IntVar p4 = getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));

            switch (operation) {
                case eq:
                    pose(new Reified(new LinearFloat(store, p2, p1, "==", p3), p4));
                    break;
                case ne:
                    pose(new Reified(new LinearFloat(store, p2, p1, "!=", p3), p4));
                    break;
                case lt:
                    pose(new Reified(new LinearFloat(store, p2, p1, "<", p3), p4));
                    break;
                case le:
                    pose(new Reified(new LinearFloat(store, p2, p1, "<=", p3), p4));
                    break;
                default:
                    System.err.println("%% ERROR: Constraint floating-point operation not supported.");
                    System.exit(0);
            }
        } else { // non reified
            switch (operation) {
                case eq:

                    if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
                        if (p3 != 0)
                            pose(new PplusCeqR(p2[1], p3, p2[0]));
                        else
                            pose(new PeqQ(p2[1], p2[0]));
                    } else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
                        if (p3 != 0) {
                            pose(new PplusCeqR(p2[0], p3, p2[1]));
                        } else
                            pose(new PeqQ(p2[0], p2[1]));
                    } else if (p1.length == 2 && p1[0] == 1 && p1[1] == 1) {
                        pose(new PplusQeqR(p2[0], p2[1], new FloatVar(store, p3, p3)));
                    } else
                        pose(new LinearFloat(store, p2, p1, "==", p3));
                    break;
                case ne:
                    pose(new LinearFloat(store, p2, p1, "!=", p3));
                    break;
                case lt:
                    if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0)
                        pose(new PltQ(p2[0], p2[1]));
                    else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0)
                        pose(new PltQ(p2[1], p2[0]));
                    else
                        pose(new LinearFloat(store, p2, p1, "<", p3));
                    break;
                case le:
                    if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0)
                        pose(new PlteqQ(p2[0], p2[1]));
                    else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0)
                        pose(new PlteqQ(p2[1], p2[0]));
                    else
                        pose(new LinearFloat(store, p2, p1, "<=", p3));
                    break;
                default:
                    System.err.println("%% ERROR: Constraint floating-point operation not supported.");
                    System.exit(0);
            }
        }
    }
}
