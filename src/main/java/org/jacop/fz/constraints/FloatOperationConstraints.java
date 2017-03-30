/**
 * FloatOperationConstraints.java
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


import org.jacop.fz.*;

import org.jacop.floats.constraints.PplusCeqR;
import org.jacop.floats.constraints.PplusQeqR;
import org.jacop.floats.constraints.PmulQeqR;
import org.jacop.floats.constraints.PmulCeqR;
import org.jacop.floats.constraints.PdivQeqR;
import org.jacop.floats.constraints.AbsPeqR;
import org.jacop.floats.constraints.SqrtPeqR;
import org.jacop.floats.constraints.SinPeqR;
import org.jacop.floats.constraints.CosPeqR;
import org.jacop.floats.constraints.AsinPeqR;
import org.jacop.floats.constraints.AcosPeqR;
import org.jacop.floats.constraints.TanPeqR;
import org.jacop.floats.constraints.AtanPeqR;
import org.jacop.floats.constraints.ExpPeqR;
import org.jacop.floats.constraints.LnPeqR;
import org.jacop.floats.constraints.PdivCeqR;
import org.jacop.floats.constraints.PltC;
import org.jacop.floats.constraints.PeqQ;

import org.jacop.constraints.IfThenElse;
import org.jacop.floats.core.FloatVar;

/**
 *
 * Generation of set constraints in flatzinc
 *
 * @author Krzysztof Kuchcinski 
 *
 */
class FloatOperationConstraints implements ParserTreeConstants {

    Support support;
    Store store;
    
    public FloatOperationConstraints(Support support) {
	this.support = support;
	this.store = support.store;
    }

    void gen_float_abs(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        support.pose(new AbsPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
    }

    void gen_float_acos(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        support.pose(new AcosPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
    }

    void gen_float_asin(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        support.pose(new AsinPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
    }

    void gen_float_atan(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        support.pose(new AtanPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
    }

    void gen_float_cos(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        support.pose(new CosPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
    }

    // void gen_float_cosh(SimpleNode node) {
    // }

    void gen_float_exp(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        support.pose(new ExpPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
    }

    void gen_float_ln(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        support.pose(new LnPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
    }

    void gen_float_log10(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        FloatVar tmp = new FloatVar(store, -1e150, 1e150);
        support.pose(new LnPeqR(support.getFloatVariable(p1), tmp));
        support.pose(new PdivCeqR(tmp, java.lang.Math.log(10), support.getFloatVariable(p2)));
    }

    void gen_float_log2(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        FloatVar tmp = new FloatVar(store, -1e150, 1e150);
        support.pose(new LnPeqR(support.getFloatVariable(p1), tmp));
        support.pose(new PdivCeqR(tmp, java.lang.Math.log(2), support.getFloatVariable(p2)));
    }

    void gen_float_sqrt(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        support.pose(new SqrtPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
    }

    void gen_float_sin(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        support.pose(new SinPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
    }

    // void gen_float_sinh(SimpleNode node) {
    // }

    void gen_float_tan(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        support.pose(new TanPeqR(support.getFloatVariable(p1), support.getFloatVariable(p2)));
    }

    // void gen_float_tanh(SimpleNode node) {
    // }

    void gen_float_max(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

        FloatVar v1 = support.getFloatVariable(p1);
        FloatVar v2 = support.getFloatVariable(p2);
        FloatVar v3 = support.getFloatVariable(p3);

        support.pose(new org.jacop.floats.constraints.Max(new FloatVar[] {v1, v2}, v3));
    }

    void gen_float_min(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

        FloatVar v1 = support.getFloatVariable(p1);
        FloatVar v2 = support.getFloatVariable(p2);
        FloatVar v3 = support.getFloatVariable(p3);

        support.pose(new org.jacop.floats.constraints.Min(new FloatVar[] {v1, v2}, v3));
    }

    void gen_float_plus(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

        if (p1.getType() == 5) {// p1 int
            support.pose(new PplusCeqR(support.getFloatVariable(p2), support.getFloat(p1), support.getFloatVariable(p3)));
        } else if (p2.getType() == 5) {// p2 int
            support.pose(new PplusCeqR(support.getFloatVariable(p1), support.getFloat(p2), support.getFloatVariable(p3)));
        } else
            support.pose(new PplusQeqR(support.getFloatVariable(p1), support.getFloatVariable(p2), support.getFloatVariable(p3)));
    }

    void gen_float_times(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

        if (p1.getType() == 5) {// p1 float
            support.pose(new PmulCeqR(support.getFloatVariable(p2), support.getFloat(p1), support.getFloatVariable(p3)));
        } else if (p2.getType() == 5) {// p2 float
            support.pose(new PmulCeqR(support.getFloatVariable(p1), support.getFloat(p2), support.getFloatVariable(p3)));
        } else
            support.pose(new PmulQeqR(support.getFloatVariable(p1), support.getFloatVariable(p2), support.getFloatVariable(p3)));
    }

    void gen_float_pow(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

        FloatVar v1 = support.getFloatVariable(p1);
        FloatVar v2 = support.getFloatVariable(p2);
        FloatVar v3 = support.getFloatVariable(p3);

        if (v1.min() < 0)
            if (v2.min() == v2.max() && Math.ceil(v2.max()) == v2.max()) {
                // case for integer exponent

                double exponent = v2.min();

                FloatVar tmp0 = new FloatVar(store, 0, 1e150);
                FloatVar tmp1 = new FloatVar(store, -1e150, 1e150);
                FloatVar tmp2 = new FloatVar(store, -1e150, 1e150);
                FloatVar tmp3 = new FloatVar(store, -1e150, 1e150);
                support.pose(new AbsPeqR(v1, tmp0));
                support.pose(new LnPeqR(tmp0, tmp1));
                support.pose(new PmulQeqR(tmp1, v2, tmp2));
                support.pose(new ExpPeqR(tmp2, tmp3));

                if (exponent % 2 == 0)
                    // even
                    support.pose(new PeqQ(tmp3, v3));
                else
                    // odd
                    support.pose(new IfThenElse(new PltC(v1, 0), new PplusQeqR(tmp3, v3, new FloatVar(store, 0, 0)), new PeqQ(tmp3, v3)));

                return;
            } else
                System.err.println(
                    "%% WARNING: constraint float_pow is not defined for negative numbers as first argument (decomposition x^y = exp(y*ln(x))); "
                        + v1 + " has minimal value negative (will be pruned).");

        FloatVar tmp1 = new FloatVar(store, -1e150, 1e150);
        FloatVar tmp2 = new FloatVar(store, -1e150, 1e150);
        support.pose(new LnPeqR(v1, tmp1));
        support.pose(new PmulQeqR(tmp1, v2, tmp2));
        support.pose(new ExpPeqR(tmp2, v3));
    }

    // not supported any longer
    void gen_float_div(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

        support.pose(new PdivQeqR(support.getFloatVariable(p1), support.getFloatVariable(p2), support.getFloatVariable(p3)));
    }
}
