/**
 * FloatComparisonConstraints.java
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
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Reified;

import org.jacop.fz.*;

import org.jacop.floats.core.FloatVar;
import org.jacop.floats.core.FloatDomain;

import org.jacop.floats.constraints.PgteqC;
import org.jacop.floats.constraints.PeqC;
import org.jacop.floats.constraints.PneqC;
import org.jacop.floats.constraints.PeqQ;
import org.jacop.floats.constraints.PneqQ;
import org.jacop.floats.constraints.PltQ;
import org.jacop.floats.constraints.PlteqQ;
import org.jacop.floats.constraints.PlteqC;
import org.jacop.floats.constraints.PgtC;
import org.jacop.floats.constraints.PltC;

/**
 *
 * Generation of set constraints in flatzinc
 *
 * @author Krzysztof Kuchcinski 
 *
 */
class FloatComparisonConstraints implements ParserTreeConstants {

    boolean reified;
    Support support;
    Store store;
    
    public FloatComparisonConstraints(Support support) {
	this.support = support;
	this.store = support.store;
    }

    void gen_float_eq(SimpleNode node) {
        reified = false;
        float_comparison(Support.eq, node);
    }

    void gen_float_eq_reif(SimpleNode node) {
        reified = true;
        float_comparison(Support.eq, node);
    }

    void gen_float_ne(SimpleNode node) {
        reified = false;
        float_comparison(Support.ne, node);
    }

    void gen_float_ne_reif(SimpleNode node) {
        reified = true;
        float_comparison(Support.ne, node);
    }

    void gen_float_le(SimpleNode node) {
        reified = false;
        float_comparison(Support.le, node);
    }

    void gen_float_le_reif(SimpleNode node) {
        reified = true;
        float_comparison(Support.le, node);
    }

    void gen_float_lt(SimpleNode node) {
        reified = false;
        float_comparison(Support.lt, node);
    }

    void gen_float_lt_reif(SimpleNode node) {
        reified = true;
        float_comparison(Support.lt, node);
    }

    void float_comparison(int operation, SimpleNode node) {

        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        if (reified) { // reified constraint
            PrimitiveConstraint c = null;
            ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);
            IntVar v3 = support.getVariable(p3);

            if (p2.getType() == 5) { // var rel float

                FloatVar v1 = support.getFloatVariable(p1);

                double i2 = support.getFloat(p2);
                switch (operation) {

                    case Support.eq:
                        if (v1.min() > i2 || v1.max() < i2) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else if (v1.min() == i2 && v1.singleton()) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (v3.max() == 0) {
                            v1.domain.inComplement(store.level, v1, i2);
                            return;
                        } else if (v3.min() == 1) {
                            v1.domain.in(store.level, v1, i2, i2);
                            return;
                        } else
                            c = new PeqC(v1, i2);
                        break;

                    case Support.ne:
                        if (v1.min() > i2 || v1.max() < i2) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (v1.min() == i2 && v1.singleton()) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else if (v3.max() == 0) {
                            v1.domain.in(store.level, v1, i2, i2);
                            return;
                        } else if (v3.min() == 1) {
                            v1.domain.inComplement(store.level, v1, i2);
                            return;
                        } else
                            c = new PneqC(v1, i2);
                        break;
                    case Support.lt:
                        if (v1.max() < i2) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (v1.min() >= i2) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else
                            c = new PltC(v1, i2);
                        break;
                    case Support.le:
                        if (v1.max() <= i2) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (v1.min() > i2) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else
                            c = new PlteqC(v1, i2);
                        break;
		default:
		    throw new RuntimeException("Internal error in " + getClass().getName());
                }
            } else if (p1.getType() == 5) { // float rel var
                FloatVar v2 = support.getFloatVariable(p2);
                double i1 = support.getFloat(p1);

                switch (operation) {

                    case Support.eq:
                        if (v2.min() > i1 || v2.max() < i1) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else if (v2.min() == i1 && v2.singleton()) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (v3.max() == 0) {
                            v2.domain.inComplement(store.level, v2, i1);
                            return;
                        } else if (v3.min() == 1) {
                            v2.domain.in(store.level, v2, i1, i1);
                            return;
                        } else
                            c = new PeqC(v2, i1);
                        break;

                    case Support.ne:
                        if (v2.min() > i1 || v2.max() < i1) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (v2.min() == i1 && v2.singleton()) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else
                            c = new PneqC(v2, i1);
                        break;
                    case Support.lt:
                        if (i1 < v2.min()) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (i1 >= v2.max()) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else
                            c = new PgtC(v2, i1);
                        break;
                    case Support.le:
                        if (i1 <= v2.min()) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (i1 > v2.max()) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else
                            c = new PgteqC(v2, i1);
                        break;
		default:
		    throw new RuntimeException("Internal error in " + getClass().getName());
                }
            } else { // var rel var
                FloatVar v1 = support.getFloatVariable(p1);
                FloatVar v2 = support.getFloatVariable(p2);

                switch (operation) {
                    case Support.eq:
                        c = new PeqQ(v1, v2);
                        break;
                    case Support.ne:
                        c = new PneqQ(v1, v2);
                        break;
                    case Support.lt:
                        c = new PltQ(v1, v2);
                        break;
                    case Support.le:
                        c = new PlteqQ(v1, v2);
                        break;
		default:
		    throw new RuntimeException("Internal error in " + getClass().getName());
                }
            }

            Constraint cr = new Reified(c, v3);
            support.pose(cr);
        } else { // not reified constraints

            if (p1.getType() == 5) { // first parameter float
                if (p2.getType() == 0 || p2.getType() == 1) { // first parameter float & second parameter float
                    double i1 = support.getFloat(p1);
                    double i2 = support.getFloat(p2);
                    switch (operation) {
                        case Support.eq:
                            if (i1 != i2)
                                throw Store.failException;
                            break;
                        case Support.ne:
                            if (i1 == i2)
                                throw Store.failException;
                            break;
                        case Support.lt:
                            if (i1 >= i2)
                                throw Store.failException;
                            break;
                        case Support.le:
                            if (i1 > i2)
                                throw Store.failException;
                            break;
		    default:
			throw new RuntimeException("Internal error in " + getClass().getName());
                    }
                } else { // first parameter float & second parameter var

                    double i1 = support.getFloat(p1);
                    FloatVar v2 = support.getFloatVariable(p2);

                    switch (operation) {
                        case Support.eq:
                            v2.domain.in(store.level, v2, i1, i1);
                            break;
                        case Support.ne:
                            v2.domain.inComplement(store.level, v2, i1);
                            break;
                        case Support.lt:
                            v2.domain.in(store.level, v2, FloatDomain.next(i1), VariablesParameters.MAX_FLOAT);
                            break;
                        case Support.le:
                            v2.domain.in(store.level, v2, i1, VariablesParameters.MAX_FLOAT);
                            break;
		    default:
			throw new RuntimeException("Internal error in " + getClass().getName());
                    }
                }
            } else { // first parameter var
                if (p2.getType() == 5) { // first parameter var & second parameter float

                    FloatVar v1 = support.getFloatVariable(p1);
                    double i2 = support.getFloat(p2);

                    switch (operation) {
                        case Support.eq:
                            v1.domain.in(store.level, v1, i2, i2);
                            break;
                        case Support.ne:
                            v1.domain.inComplement(store.level, v1, i2);
                            break;
                        case Support.lt:
                            v1.domain.in(store.level, v1, VariablesParameters.MIN_FLOAT, FloatDomain.previous(i2));
                            break;
                        case Support.le:
                            v1.domain.in(store.level, v1, VariablesParameters.MIN_FLOAT, i2);
                            break;
		    default:
			throw new RuntimeException("Internal error in " + getClass().getName());
                    }

                } else { // first parameter var & second parameter var

                    FloatVar v1 = support.getFloatVariable(p1);
                    FloatVar v2 = support.getFloatVariable(p2);

                    switch (operation) {
                        case Support.eq:
                            support.pose(new PeqQ(v1, v2));
                            break;
                        case Support.ne:
                            support.pose(new PneqQ(v1, v2));
                            break;
                        case Support.lt:
                            support.pose(new PltQ(v1, v2));
                            break;
                        case Support.le:
                            support.pose(new PlteqQ(v1, v2));
                            break;
		    default:
			throw new RuntimeException("Internal error in " + getClass().getName());
                    }
                }
            }

        }
    }
}
