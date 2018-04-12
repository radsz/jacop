/**
 * SetConstraints.java
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

import org.jacop.set.core.SetVar;
import org.jacop.set.core.BoundSetDomain;

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Not;

import org.jacop.set.constraints.AleB;
import org.jacop.set.constraints.AltB;
import org.jacop.set.constraints.CardAeqX;
import org.jacop.set.constraints.EinA;
import org.jacop.set.constraints.XinA;
import org.jacop.set.constraints.AinB;

import org.jacop.fz.*;

import org.jacop.set.constraints.AintersectBeqC;
import org.jacop.core.IntDomain;
import org.jacop.set.constraints.AunionBeqC;
import org.jacop.set.constraints.AdiffBeqC;

/**
 *
 * Generation of set constraints in flatzinc
 *
 * @author Krzysztof Kuchcinski 
 *
 */
class SetConstraints implements ParserTreeConstants {

    Support support;
    Store store;
    
    public SetConstraints(Support support) {
	this.support = support;
	this.store = support.store;
    }

    void gen_set_card(SimpleNode node) {
        SetVar v1 = support.getSetVariable(node, 0);
        IntVar v2 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

        if (v2.singleton()) {
            v1.domain.inCardinality(store.level, v1, v2.min(), v2.max());

            if (support.options.debug())
                System.out.println("Cardinality of set " + v1 + " = " + v2);

        } else
            support.pose(new CardAeqX(v1, v2));
    }

    void gen_set_diff(SimpleNode node) {
        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);
        SetVar v3 = support.getSetVariable(node, 2);

        support.pose(new AdiffBeqC(v1, v2, v3));
    }

    void gen_set_eq(SimpleNode node) {
        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);

        PrimitiveConstraint c = new org.jacop.set.constraints.AeqB(v1, v2);
        support.pose(c);
    }

    void gen_set_eq_reif(SimpleNode node) {

        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);
        IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

        PrimitiveConstraint c = new org.jacop.set.constraints.AeqB(v1, v2);
        support.pose(new Reified(c, v3));
    }

    void gen_set_in(SimpleNode node) {
        PrimitiveConstraint c;

        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        SimpleNode v1Type = (SimpleNode) node.jjtGetChild(1);
        if (v1Type.getId() == JJTSETLITERAL) {
            IntDomain d = support.getSetLiteral(node, 1);
            IntVar v1 = support.getVariable(p1);

            v1.domain.in(store.level, v1, d);
            return;
        } else {
            SetVar v2 = support.getSetVariable(node, 1);

            if (p1.getType() == 0) { // p1 int
                int i1 = support.getInt(p1);
                c = new EinA(i1, v2);
            } else { // p1 var
                IntVar v1 = support.getVariable(p1);
                c = new XinA(v1, v2);
            }
        }
        // FIXME, include AinB here?

        support.pose(c);
    }

    void gen_set_in_reif(SimpleNode node) {
        PrimitiveConstraint c;

        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        SimpleNode v1Type = (SimpleNode) node.jjtGetChild(1);
        if (v1Type.getId() == JJTSETLITERAL) {
            IntDomain d = support.getSetLiteral(node, 1);
            IntVar v1 = support.getVariable(p1);
            c = new org.jacop.constraints.In(v1, d);
        } else {
            SetVar v2 = support.getSetVariable(node, 1);

            if (p1.getType() == 0) { // p1 int
                int i1 = support.getInt(p1);
                c = new EinA(i1, v2);
            } else { // p1 var
                IntVar v1 = support.getVariable(p1);
                c = new XinA(v1, v2);
            }
        }
        // FIXME, include AinB here?

        IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

        support.pose(new Reified(c, v3));
    }

    void gen_set_intersect(SimpleNode node) {
        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);
        SetVar v3 = support.getSetVariable(node, 2);

        support.pose(new AintersectBeqC(v1, v2, v3));
    }

    void gen_set_le(SimpleNode node) {
        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);

        support.pose(new AleB(v1, v2));
    }

    void gen_set_le_reif(SimpleNode node) {
        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);
	IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
	
        support.pose(new Reified(new AleB(v1, v2), v3));
    }

    void gen_set_lt(SimpleNode node) {
        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);

        support.pose(new AltB(v1, v2));
    }

    void gen_set_lt_reif(SimpleNode node) {
        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);
	IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

        support.pose(new Reified(new AltB(v1, v2), v3));
    }

    void gen_set_ne(SimpleNode node) {

        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);

        PrimitiveConstraint c = new Not(new org.jacop.set.constraints.AeqB(v1, v2));
        support.pose(c);
    }

    void gen_set_ne_reif(SimpleNode node) {

        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);
        IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

        PrimitiveConstraint c = new Not(new org.jacop.set.constraints.AeqB(v1, v2));
        support.pose(new Reified(c, v3));
    }

    void gen_set_subset(SimpleNode node) {
        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);

        PrimitiveConstraint c = new AinB(v1, v2);
        support.pose(c);
    }

    void gen_set_subset_reif(SimpleNode node) {
        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);

        PrimitiveConstraint c = new AinB(v1, v2);
        IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
        support.pose(new Reified(c, v3));
    }

    void gen_set_symdiff(SimpleNode node) {
        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);
        SetVar v3 = support.getSetVariable(node, 2);

        SetVar t1 = new SetVar(store, new BoundSetDomain(IntDomain.MinInt, IntDomain.MaxInt));
        SetVar t2 = new SetVar(store, new BoundSetDomain(IntDomain.MinInt, IntDomain.MaxInt));

        support.pose(new AdiffBeqC(v1, v2, t1));

        support.pose(new AdiffBeqC(v2, v1, t2));

        support.pose(new AunionBeqC(t1, t2, v3));
    }

    void gen_set_union(SimpleNode node) {
        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);
        SetVar v3 = support.getSetVariable(node, 2);

        support.pose(new AunionBeqC(v1, v2, v3));
    }

    // Not present in current flatzinc
    void gen_set_superset(SimpleNode node) {

        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);

        PrimitiveConstraint c = new AinB(v2, v1);
        support.pose(c);
    }

    // Not present in current flatzinc
    void gen_set_superset_reif(SimpleNode node) {

        SetVar v1 = support.getSetVariable(node, 0);
        SetVar v2 = support.getSetVariable(node, 1);

        PrimitiveConstraint c = new AinB(v2, v1);
        IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));
        support.pose(new Reified(c, v3));
    }
}
