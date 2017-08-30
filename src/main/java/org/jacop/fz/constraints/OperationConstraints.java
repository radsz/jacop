/**
 * OperationConstraints.java
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

import org.jacop.fz.*;

import org.jacop.core.Store;
import org.jacop.core.IntVar;

import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XmulYeqC;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.XdivYeqZ;
import org.jacop.constraints.XmodYeqZ;
import org.jacop.constraints.MinSimple;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.MaxSimple;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.XexpYeqZ;
import org.jacop.floats.constraints.XeqP;

/**
 *
 * Generation of linear constraints in flatzinc
 *
 * @author Krzysztof Kuchcinski 
 *
 */
class OperationConstraints implements ParserTreeConstants {

    Support support;
    Store store;
    
    public OperationConstraints(Support support) {
	this.support = support;
	this.store = support.store;
    }

    void gen_int_min(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

        IntVar v1 = support.getVariable(p1);
        IntVar v2 = support.getVariable(p2);
        IntVar v3 = support.getVariable(p3);

        if (v1.singleton() && v2.singleton()) {
            int min = java.lang.Math.min(v1.value(), v2.value());
            v3.domain.in(store.level, v3, min, min);
        } else if (v1.singleton() && v1.value() <= v2.min()) {
            int min = v1.value();
            v3.domain.in(store.level, v3, min, min);
        } else if (v2.singleton() && v2.value() <= v1.min()) {
            int min = v2.value();
            v3.domain.in(store.level, v3, min, min);
        } else if (v1.min() >= v2.max())
            support.pose(new XeqY(v2, v3));
        else if (v2.min() >= v1.max())
            support.pose(new XeqY(v1, v3));
        else if (v1 == v2)
            support.pose(new XeqY(v1, v3));
        else
            support.pose(new MinSimple(v1, v2, v3));
    }

    void gen_int_max(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

        IntVar v1 = support.getVariable(p1);
        IntVar v2 = support.getVariable(p2);
        IntVar v3 = support.getVariable(p3);

        if (v1.singleton() && v2.singleton()) {
            int max = java.lang.Math.max(v1.value(), v2.value());
            v3.domain.in(store.level, v3, max, max);
        } else if (v1.singleton() && v1.value() >= v2.max()) {
            int max = v1.value();
            v3.domain.in(store.level, v3, max, max);
        } else if (v2.singleton() && v2.value() >= v1.max()) {
            int max = v2.value();
            v3.domain.in(store.level, v3, max, max);
        } else if (v1.min() >= v2.max())
            support.pose(new XeqY(v1, v3));
        else if (v2.min() >= v1.max())
            support.pose(new XeqY(v2, v3));
        else if (v1 == v2)
            support.pose(new XeqY(v1, v3));
        else
            support.pose(new MaxSimple(v1, v2, v3));
    }

    void gen_int_mod(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

        IntVar v1 = support.getVariable(p1);
        IntVar v2 = support.getVariable(p2);
        IntVar v3 = support.getVariable(p3);

        support.pose(new XmodYeqZ(v1, v2, v3));
    }

    void gen_int_div(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

        IntVar v1 = support.getVariable(p1);
        IntVar v2 = support.getVariable(p2);
        IntVar v3 = support.getVariable(p3);

        support.pose(new XdivYeqZ(v1, v2, v3));
    }

    void gen_int_abs(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        IntVar v1 = support.getVariable(p1);
        IntVar v2 = support.getVariable(p2);

        if (support.boundsConsistency)
            support.pose(new AbsXeqY(v1, v2));
        else
            support.pose(new AbsXeqY(v1, v2, true));
    }

    void gen_int_times(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

        if (p1.getType() == 0) {// p1 int
            int c = support.getInt(p1);
            if (c == 1)
                support.pose(new XeqY(support.getVariable(p2), support.getVariable(p3)));
            else if (c == 0) {
		IntVar v3 = support.getVariable(p3);
		v3.domain.in(store.level, v3, 0, 0);
	    }
	    else
                support.pose(new XmulCeqZ(support.getVariable(p2), c, support.getVariable(p3)));
        } else if (p2.getType() == 0) {// p2 int
            int c = support.getInt(p2);
            if (c == 1)
                support.pose(new XeqY(support.getVariable(p1), support.getVariable(p3)));
            else if (c == 0) {
		IntVar v3 = support.getVariable(p3);
		v3.domain.in(store.level, v3, 0, 0);
	    }
	    else
                support.pose(new XmulCeqZ(support.getVariable(p1), support.getInt(p2), support.getVariable(p3)));
        } else if (p3.getType() == 0) {// p3 int
            support.pose(new XmulYeqC(support.getVariable(p1), support.getVariable(p2), support.getInt(p3)));
        } else {
            IntVar v1 = support.getVariable(p1), v2 = support.getVariable(p2), v3 = support.getVariable(p3);
            if (v1.min() >= 0 && v1.max() <= 1 && v2.min() >= 0 && v2.max() <= 1 && v3.min() >= 0 && v3.max() <= 1) {
		if (v1.equals(v2))
		    support.pose(new XeqY(v1, v3));
		else
		    support.pose(new AndBoolSimple(v1, v2, v3));
	    }
            else if ((v1.singleton() && v1.value() == 0) || (v2.singleton() && v2.value() == 0))
                v3.domain.in(store.level, v3, 0, 0);
            else
                support.pose(new XmulYeqZ(v1, v2, v3));
        }
    }

    void gen_int_plus(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

        if (p1.getType() == 0) {// p1 int
            support.pose(new XplusCeqZ(support.getVariable(p2), support.getInt(p1), support.getVariable(p3)));
        } else if (p2.getType() == 0) {// p2 int
            support.pose(new XplusCeqZ(support.getVariable(p1), support.getInt(p2), support.getVariable(p3)));
        } else if (p3.getType() == 0) {// p3 int
            support.pose(new XplusYeqC(support.getVariable(p1), support.getVariable(p2), support.getInt(p3)));
        } else
            support.pose(new XplusYeqZ(support.getVariable(p1), support.getVariable(p2), support.getVariable(p3)));
    }

    void gen_int2float(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        support.pose(new XeqP(support.getVariable(p1), support.getFloatVariable(p2)));
    }

    void gen_int_pow(SimpleNode node) {
        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
        ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);

        IntVar v1 = support.getVariable(p1);
        IntVar v2 = support.getVariable(p2);
        IntVar v3 = support.getVariable(p3);

        support.pose(new XexpYeqZ(v1, v2, v3));
    }
}
