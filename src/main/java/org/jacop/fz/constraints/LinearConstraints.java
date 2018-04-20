/**
 * LinearConstraints.java
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

import org.jacop.fz.*;

import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.constraints.Not;
import org.jacop.constraints.OrBoolVector;

import org.jacop.satwrapper.SatTranslation;
import org.jacop.core.FailException;
import org.jacop.constraints.XorBool;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.OrBoolSimple;

/**
 *
 * Generation of linear constraints in flatzinc
 *
 * @author Krzysztof Kuchcinski 
 *
 */
class LinearConstraints implements ParserTreeConstants {

    Store store;
    Support support;
    SatTranslation sat;
    
    public LinearConstraints(Support support) {
	this.store = support.store;
	this.support = support;
	this.sat = support.sat;
    }

    void gen_bool_lin_eq(SimpleNode node) {

        int[] p1 = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] p2 = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        IntVar par3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

        // If a linear term contains only constants and can be evaluated
        // check if satisfied and do not generate constraint
        if (par3.min() == par3.max() && allConstants(p2)) {
            int el = 0, s = 0;
            while (el < p2.length) {
                s += p2[el].min() * p1[el];
                el++;
            }
            if (s == par3.min())
                return;
            else
                throw store.failException;
        }

        if (allWeightsOne(p1))
            support.pose(new SumBool(p2, "==", par3));
        else {
	    if (p2.length < 15)
		support.pose(new LinearInt(p2, p1, "==", par3));
	    else
		support.pose(new SumWeight(p2, p1, par3));
        }
    }

    void gen_int_lin_eq(SimpleNode node) {
        int_lin_relation(support.eq, node);
    }

    void gen_int_lin_eq_reif(SimpleNode node) {
        int_lin_relation_reif(support.eq, node);
    }

    void gen_int_lin_ne(SimpleNode node) {
        int_lin_relation(support.ne, node);
    }

    void gen_int_lin_ne_reif(SimpleNode node) {
        int_lin_relation_reif(support.ne, node);
    }

    void gen_int_lin_lt(SimpleNode node) {
        int_lin_relation(support.lt, node);
    }

    void gen_int_lin_lt_reif(SimpleNode node) {
        int_lin_relation_reif(support.lt, node);
    }

    void gen_int_lin_le(SimpleNode node) {
        int_lin_relation(support.le, node);
    }

    void gen_int_lin_le_reif(SimpleNode node) {
        int_lin_relation_reif(support.le, node);
    }

    void int_lin_relation_reif(int operation, SimpleNode node) throws FailException {

        int[] p1 = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] p2 = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        int p3 = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));

        // If a linear term contains only constants and can be evaluated
        // check if satisfied and do not generate constraint
        boolean p2Fixed = allConstants(p2);
        int s = 0;
        if (p2Fixed) {
            int el = 0;
            while (el < p2.length) {
                s += p2[el].min() * p1[el];
                el++;
            }
        }

        IntVar p4 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(3));

        IntVar t;
        switch (operation) {
            case Support.eq:

                if (p2Fixed) {
                    if (s == p3)
                        p4.domain.in(store.level, p4, 1, 1);
                    else
                        p4.domain.in(store.level, p4, 0, 0);
                    return;
                }

                if (p1.length == 1) {
                    if (p1[0] == 1) {
			if (p2[0].min() == 0 && p2[0].max() == 1 && p3 >= 0 && p3 <= 1) { // binary variable
			    if (p3 == 0) {
				support.pose(new XneqY(p2[0], p4));
				return;
			    }
			    else if (p3 == 1) {
				support.pose(new XeqY(p2[0], p4));
				return;
			    }
			}
                        else
			    support.pose(new Reified(new XeqC(p2[0], p3), p4));
		    }
                    else
                        support.pose(new Reified(new XmulCeqZ(p2[0], p1[0], support.dictionary.getConstant(p3)), p4));
                } else if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
                    support.pose(new Reified(new XplusCeqZ(p2[1], p3, p2[0]), p4));
                } else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
                    support.pose(new Reified(new XplusCeqZ(p2[0], p3, p2[1]), p4));
                } else if (p1.length == 2 && p1[0] == 1 && p1[1] == 1) {
		    if (binaryVar(p2[0]) && binaryVar(p2[1]) && p3 >= 0 && p3 <= 2) {
			if (p3 == 0)
			    support.pose(new Not(new OrBoolSimple(p2[0], p2[1], p4)));
			else if (p3 == 1)
			    support.pose(new XorBool(new IntVar[] {p2[0], p2[1]}, p4));
			else if (p3 == 2)
			    support.pose(new AndBoolSimple(p2[0], p2[1], p4));
		    }
		    else
			support.pose(new Reified(new XplusYeqC(p2[0], p2[1], p3), p4));
                } else if (p1.length == 2 && p1[0] == -1 && p1[1] == -1) {
                    support.pose(new Reified(new XplusYeqC(p2[0], p2[1], -p3), p4));
                } else {
                    int pos = sumPossible(p1, p3);
                    if (pos > -1) {
                        IntVar[] vect = new IntVar[p1.length - 1];
                        int n = 0;
                        for (int i = 0; i < p2.length; i++)
                            if (i != pos)
                                vect[n++] = p2[i];
                        if (boolSum(vect))
                            support.pose(new Reified(new SumBool(vect, "==", p2[pos]), p4));
                        else
                            support.pose(new Reified(new SumInt(vect, "==", p2[pos]), p4));
                    } else if (allWeightsOne(p1)) {
                        IntVar v = support.dictionary.getConstant(p3);
                        if (boolSum(p2))
                            support.pose(new Reified(new SumBool(p2, "==", v), p4));
                        else
                            support.pose(new Reified(new SumInt(p2, "==", v), p4));
                    } else if (allWeightsMinusOne(p1)) {
                        IntVar v = support.dictionary.getConstant(-p3);
                        if (boolSum(p2))
                            support.pose(new Reified(new SumBool(p2, "==", v), p4));
                        else
                            support.pose(new Reified(new SumInt(p2, "==", v), p4));
                    } else {
                        support.pose(new Reified(new LinearInt(p2, p1, "==", p3), p4));
                    }
                }
                break;
            case Support.ne:
                if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
                    if (p3 == 0)
			if (binaryVar(p2[0]) && binaryVar(p2[1]))
			    // (x != y) <=> b == x xor y = b
			    support.pose(new XorBool(new IntVar[] {p2[0], p2[1]}, p4));
			else
			    support.pose(new Reified(new XneqY(p2[0], p2[1]), p4));
                    else
                        support.pose(new Reified(new Not(new XplusCeqZ(p2[1], p3, p2[0])), p4));
                } else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
                    if (p3 == 0)
			if (binaryVar(p2[0]) && binaryVar(p2[1]))
			    // (x != y) <=> b == x xor y = b
			    support.pose(new XorBool(new IntVar[] {p2[0], p2[1]}, p4));
			else
			    support.pose(new Reified(new XneqY(p2[0], p2[1]), p4));
                    else
                        support.pose(new Reified(new Not(new XplusCeqZ(p2[0], p3, p2[1])), p4));
                } else if (p1.length == 2 && p1[0] == 1 && p1[1] == 1) {
                    support.pose(new Reified(new Not(new XplusYeqC(p2[0], p2[1], p3)), p4));
                } else if (p1.length == 2 && p1[0] == -1 && p1[1] == -1) {
                    support.pose(new Reified(new Not(new XplusYeqC(p2[0], p2[1], -p3)), p4));
                } else if (allWeightsOne(p1)) {
                    if (p1.length == 1)
                        if (p2[0].domain.isIntersecting(p3, p3))
                            support.pose(new Reified(new XneqC(p2[0], p3), p4));
                        else
                            p4.domain.in(store.level, p4, 1, 1);
                    else {
                        t = support.dictionary.getConstant(p3); // new IntVar(store, p3, p3);
                        if (boolSum(p2))
                            support.pose(new Reified(new SumBool(p2, "!=", t), p4));
                        else
                            support.pose(new Reified(new SumInt(p2, "!=", t), p4));
                    }
                } else if (allWeightsMinusOne(p1)) {
                    if (p1.length == 1)
                        if (p2[0].domain.isIntersecting(-p3, -p3))
                            support.pose(new Reified(new XneqC(p2[0], -p3), p4));
                        else
                            p4.domain.in(store.level, p4, 1, 1);
                    else {
                        t = support.dictionary.getConstant(-p3); // new IntVar(store, -p3, -p3);
                        if (boolSum(p2))
                            support.pose(new Reified(new SumBool(p2, "!=", t), p4));
                        else
                            support.pose(new Reified(new SumInt(p2, "!=", t), p4));
                    }
                } else
                    support.pose(new Reified(new LinearInt(p2, p1, "!=", p3), p4));
                break;
            case Support.lt:
                support.pose(new Reified(new LinearInt(p2, p1, "<", p3), p4));
                break;
            // gt not present in the newest flatzinc version
            // case support.gt :
            // 	t = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
            // 	support.pose(new SumWeight(p2, p1, t));
            // 	support.pose(new Reified(new XgtC(t, p3), p4));
            // 	break;
            case Support.le:
                if (p1.length == 2 && p1[0] == 1 && p1[1] == -1)
                    if (p3 == 0)
                        support.pose(new Reified(new XlteqY(p2[0], p2[1]), p4));
                    else if (p4.min() == 1)
			support.pose(new XplusClteqZ(p2[0], -p3, p2[1]));
                    else if (p4.max() == 0)
			support.pose(new Not(new XplusClteqZ(p2[0], -p3, p2[1])));
		    else
                        support.pose(new Reified(new XplusClteqZ(p2[0], -p3, p2[1]), p4));
                else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1)
                    if (p3 == 0)
                        support.pose(new Reified(new XlteqY(p2[1], p2[0]), p4));
                    else if (p4.min() == 1)
			support.pose(new XplusClteqZ(p2[1], -p3, p2[0]));
                    else if (p4.max() == 0)
			support.pose(new Not(new XplusClteqZ(p2[1], -p3, p2[0])));
		    else
                        support.pose(new Reified(new XplusClteqZ(p2[1], -p3, p2[0]), p4));
                else if (p1.length == 1 && p1[0] == 1)
                    support.pose(new Reified(new org.jacop.constraints.XlteqC(p2[0], p3), p4));
                else if (p1.length == 1 && p1[0] == -1)
                    support.pose(new Reified(new org.jacop.constraints.XgteqC(p2[0], -p3), p4));
		else if (boolSum(p2) && p3 == 0 && allPositive(p1)) // very special case: positive weighted sum of 0/1 variables <= 0 =>  (all p2's zero <=> p4)
		    if (support.options.useSat())
			sat.generate_allZero_reif(support.unique(p2), p4);
		    else
			support.pose(new Not(new OrBoolVector(support.unique(p2), p4)));
		else if (boolSum(p2) && p3 == 0 && allNonPositive(p1)) // very special case: negative weighted sum of 0/1 variables <= 0 =>  (p4 = 1)
		    p4.domain.in(store.level, p4, 1, 1);
		else if (allWeightsOne(p1)) {
                    t = support.dictionary.getConstant(p3);
                    if (boolSum(p2))
                        if (p3 == 0)
                            // all p2's zero <=> p4
                            if (support.options.useSat())
                                sat.generate_allZero_reif(support.unique(p2), p4);
                            else
                                support.pose(new Not(new OrBoolVector(support.unique(p2), p4)));
                        else
                            support.pose(new Reified(new SumBool(p2, "<=", t), p4));
                    else
                        support.pose(new Reified(new SumInt(p2, "<=", t), p4));
                } else if (allWeightsMinusOne(p1)) {
                    t = support.dictionary.getConstant(-p3);
                    if (boolSum(p2))
                        support.pose(new Reified(new SumBool(p2, ">=", t), p4));
                    else
                        support.pose(new Reified(new SumInt(p2, ">=", t), p4));
                } else {
                    int posLe = sumLePossible(p1, p3);
                    int posGe = sumGePossible(p1, p3);
                    if (posLe > -1) {
                        IntVar[] vect = new IntVar[p1.length - 1];
                        int n = 0;
                        for (int i = 0; i < p2.length; i++)
                            if (i != posLe)
                                vect[n++] = p2[i];
                        if (boolSum(vect))
                            support.pose(new Reified(new SumBool(vect, "<=", p2[posLe]), p4));
                        else if (vect.length == 2)
                            support.pose(new Reified(new XplusYlteqZ(vect[0], vect[1], p2[posLe]), p4));
                        else
                            support.pose(new Reified(new SumInt(vect, "<=", p2[posLe]), p4));
                    } else if (posGe > -1) {
                        IntVar[] vect = new IntVar[p1.length - 1];
                        int n = 0;
                        for (int i = 0; i < p2.length; i++)
                            if (i != posGe)
                                vect[n++] = p2[i];
                        if (boolSum(vect))
                            support.pose(new Reified(new SumBool(vect, ">=", p2[posGe]), p4));
                        else
                            support.pose(new Reified(new SumInt(vect, ">=", p2[posGe]), p4));
                    } else {
                        support.pose(new Reified(new LinearInt(p2, p1, "<=", p3), p4));
                    }
                }
                break;
            default:
                throw new IllegalArgumentException("%% ERROR: Relation in linear constraint not supported.");
        }
    }

    void int_lin_relation(int operation, SimpleNode node) throws FailException {

        int[] p1 = support.getIntArray((SimpleNode) node.jjtGetChild(0));
        IntVar[] p2 = support.getVarArray((SimpleNode) node.jjtGetChild(1));
        int p3 = support.getInt((ASTScalarFlatExpr) node.jjtGetChild(2));

        // If a linear term contains only constants and can be evaluated
        // check if satisfied and do not generate constraint
        boolean p2Fixed = allConstants(p2);
        int s = 0;
        if (p2Fixed) {
            int el = 0;
            while (el < p2.length) {
                s += p2[el].min() * p1[el];
                el++;
            }
        }

        IntVar t;
        switch (operation) {
            case Support.eq:

                if (p2Fixed)
                    if (s == p3)
                        return;
                    else
                        throw store.failException;

                if (p1.length == 1) {
                    support.pose(new XmulCeqZ(p2[0], p1[0], support.dictionary.getConstant(p3))); // new IntVar(store, p3, p3)));
                } else if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
                    if (p3 != 0)
                        support.pose(new XplusCeqZ(p2[1], p3, p2[0]));
                    else
                        support.pose(new XeqY(p2[1], p2[0]));
                } else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
                    if (p3 != 0) {
                        support.pose(new XplusCeqZ(p2[0], p3, p2[1]));
                    } else
                        support.pose(new XeqY(p2[0], p2[1]));
                } else if (p1.length == 2 && p1[0] == 1 && p1[1] == 1) {
                    support.pose(new XplusYeqC(p2[0], p2[1], p3));
                } else if (p1.length == 2 && p1[0] == -1 && p1[1] == -1) {
                    if (p3 == 0)
                        support.pose(new XplusYeqC(p2[0], p2[1], p3));
                    else
                        support.pose(new XplusYeqC(p2[0], p2[1], -p3));
                } else if (support.domainConsistency && !support.options.getBoundConsistency()) {
                    // We do not impose linear constraint with domain consistency if
                    // the cases are covered by four cases above.

		    // possible use of Table constraint
		    // int[][] tbl = org.jacop.constraints.table.TableMill.linear(p2, p1, p3);
		    // if (tbl != null)
		    // 	if (tbl.length <= 64)
		    // 	    support.pose(new org.jacop.constraints.table.SimpleTable(p2, tbl, true));
		    // 	else
		    // 	    support.pose(new org.jacop.constraints.table.Table(p2, tbl, true));
		    // else
		    // 	support.pose(new LinearIntDom(p2, p1, "==", p3));
		    
                    support.pose(new LinearIntDom(p2, p1, "==", p3));
                } else if ((p3 == 0 && p1.length == 3) && ((p1[0] == -1 && p1[1] == -1 && p1[2] == 1) || (p1[0] == 1 && p1[1] == 1
                    && p1[2] == -1)))
                    support.pose(new XplusYeqZ(p2[0], p2[1], p2[2]));
                else if (p3 == 0 && p1.length == 2 && p1[0] == 1) {
                    support.pose(new XmulCeqZ(p2[1], -p1[1], p2[0]));
                } else if (p3 == 0 && p1.length == 2 && p1[1] == 1) {
                    support.pose(new XmulCeqZ(p2[0], -p1[0], p2[1]));
                } else if (p3 == 0 && p1.length == 2 && p1[0] == -1) {
		    support.pose(new XmulCeqZ(p2[1], p1[1], p2[0]));
		} else if (p3 == 0 && p1.length == 2 && p1[1] == -1) {
		    support.pose(new XmulCeqZ(p2[0], p1[0], p2[1]));
		} else if ((p3 == 0 && p1.length == 3) && ((p1[0] == 1 && p1[1] == -1 && p1[2] == -1) || (p1[0] == -1 && p1[1] == 1
                    && p1[2] == 1))) {
                    if (paramZero(p2[1]))
                        support.pose(new XeqY(p2[2], p2[0]));
                    else if (paramZero(p2[2]))
                        support.pose(new XeqY(p2[1], p2[0]));
                    else
                        support.pose(new XplusYeqZ(p2[1], p2[2], p2[0]));
                } else {
                    int pos = sumPossible(p1, p3);
                    if (pos > -1) {
                        IntVar[] vect = new IntVar[p1.length - 1];
                        int n = 0;
                        for (int i = 0; i < p2.length; i++)
                            if (i != pos)
                                vect[n++] = p2[i];

                        if (boolSum(vect))
                            support.pose(new SumBool(vect, "==", p2[pos]));
                        else if (vect.length == 2)
                            support.pose(new XplusYeqZ(vect[0], vect[1], p2[pos]));
                        else
                            support.pose(new SumInt(vect, "==", p2[pos]));
                    } else if (allWeightsOne(p1)) {
                        IntVar v = support.dictionary.getConstant(p3);
                        if (boolSum(p2))
                            support.pose(new SumBool(p2, "==", v));
                        else
                            support.pose(new SumInt(p2, "==", v));
                    } else if (allWeightsMinusOne(p1)) {
                        IntVar v = support.dictionary.getConstant(-p3);
                        if (boolSum(p2))
                            support.pose(new SumBool(p2, "==", v));
                        else
                            support.pose(new SumInt(p2, "==", v));
                    } else {
                        if (p2.length < 30)
                            support.pose(new LinearInt(p2, p1, "==", p3));
			else
                            support.pose(new SumWeight(p2, p1, p3));
                    }
                }
                break;
            case Support.ne:

                if (p2Fixed)
                    if (s != p3)
                        return;
                    else
                        throw store.failException;

                if (p1.length == 1 && p1[0] == 1)
                    p2[0].domain.inComplement(store.level, p2[0], p3);
                else if (p1.length == 1 && p1[0] == -1)
                    p2[0].domain.inComplement(store.level, p2[0], -p3);
                else if (p1.length == 2 && p3 == 0 && ((p1[0] == 1 && p1[1] == -1) || (p1[0] == -1 && p1[1] == 1)))
                    if (p2[0].max() < p2[1].min() || p2[0].min() > p2[1].max())
                        return;
                    else
                        support.pose(new XneqY(p2[0], p2[1]));
                else {
                    int pos = sumPossible(p1, p3);
                    if (pos > -1) {
                        IntVar[] vect = new IntVar[p1.length - 1];
                        int n = 0;
                        for (int i = 0; i < p2.length; i++)
                            if (i != pos)
                                vect[n++] = p2[i];
                        if (boolSum(vect))
                            support.pose(new SumBool(vect, "!=", p2[pos]));
                        else
                            support.pose(new SumInt(vect, "!=", p2[pos]));
                    } else {
                        if (boolSum(p2) && allWeightsOne(p1))
                            support.pose(new SumBool(p2, "!=", support.dictionary.getConstant(p3)));
                        else
                            support.pose(new LinearInt(p2, p1, "!=", p3));
                    }
                }
                break;
            case Support.lt:

                if (p2Fixed)
                    if (s < p3)
                        return;
                    else
                        throw store.failException;

                if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0)
                    support.pose(new XltY(p2[0], p2[1]));
                else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0)
                    support.pose(new XltY(p2[1], p2[0]));
                else {
                    int posLe = sumLePossible(p1, p3);
                    int posGe = sumGePossible(p1, p3);
                    if (posLe > -1) {
                        IntVar[] vect = new IntVar[p1.length - 1];
                        int n = 0;
                        for (int i = 0; i < p2.length; i++)
                            if (i != posLe)
                                vect[n++] = p2[i];
                        if (boolSum(vect))
                            support.pose(new SumBool(vect, "<", p2[posLe]));
                        else
                            support.pose(new SumInt(vect, "<", p2[posLe]));
                    } else if (posGe > -1) {
                        IntVar[] vect = new IntVar[p1.length - 1];
                        int n = 0;
                        for (int i = 0; i < p2.length; i++)
                            if (i != posGe)
                                vect[n++] = p2[i];
                        if (boolSum(vect))
                            support.pose(new SumBool(vect, ">", p2[posGe]));
                        else
                            support.pose(new SumInt(vect, ">", p2[posGe]));
                    } else {
                        // support.pose(new Linear(store, p2, p1, "<", p3));
                        support.pose(new LinearInt(p2, p1, "<", p3));
                    }
                }
                break;
            case Support.le:

                if (p2Fixed)
                    if (s <= p3)
                        return;
                    else
                        throw store.failException;

                if (p1.length == 1) {

                    if (p1[0] < 0) {
		      int rhsValue = (int) (Math.round(Math.ceil( (float)p3 / (float)p1[0] )));

                        p2[0].domain.inMin(store.level, p2[0], rhsValue);
                        if (support.options.debug())
                            System.out.println("Pruned variable " + p2[0] + " to be >= " + rhsValue);
                        // support.pose(new XgteqC(p2[0], rhsValue));
                    } else { // weight > 0
                        int rhsValue = (int) (Math.round(Math.floor(( (float)p3 / (float)p1[0] ))));

                        p2[0].domain.inMax(store.level, p2[0], rhsValue);

                        if (support.options.debug())
                            System.out.println("Pruned variable " + p2[0] + " to be <= " + rhsValue);
                        // support.pose(new XlteqC(p2[0], rhsValue));
                    }
                } else if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0)
                    support.pose(new XlteqY(p2[0], p2[1]));
                else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0)
                    support.pose(new XlteqY(p2[1], p2[0]));
                else if (p1.length == 2 && p1[0] == 1 && p1[1] == -1)
                    if (p3 == 0)
                        support.pose(new XlteqY(p2[0], p2[1]));
                    else
                        support.pose(new XplusClteqZ(p2[0], -p3, p2[1]));
                else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1)
                    if (p3 == 0)
                        support.pose(new XlteqY(p2[1], p2[0]));
                    else
                        support.pose(new XplusClteqZ(p2[1], -p3, p2[0]));

                else if (allWeightsOne(p1)) {
                    t = support.dictionary.getConstant(p3); //new IntVar(store, p3, p3);
                    if (boolSum(p2))
                        support.pose(new SumBool(p2, "<=", t));
                    else
			if (p2.length == 2)
			    support.pose(new XplusYlteqZ(p2[0], p2[1], t));
			else
			    support.pose(new SumInt(p2, "<=", t));
                } else if (allWeightsMinusOne(p1)) {
                    t = support.dictionary.getConstant(-p3); //new IntVar(store, -p3, -p3);
                    if (boolSum(p2))
                        support.pose(new SumBool(p2, ">=", t));
                    else
                        support.pose(new SumInt(p2, ">=", t));
                } else {
                    int posLe = sumLePossible(p1, p3);
                    int posGe = sumGePossible(p1, p3);
                    if (posLe > -1) {
                        IntVar[] vect = new IntVar[p1.length - 1];
                        int n = 0;
                        for (int i = 0; i < p2.length; i++)
                            if (i != posLe)
                                vect[n++] = p2[i];
                        if (boolSum(vect))
                            support.pose(new SumBool(vect, "<=", p2[posLe]));
                        else if (vect.length == 2)
                            support.pose(new XplusYlteqZ(vect[0], vect[1], p2[posLe]));
                        else
                            support.pose(new SumInt(vect, "<=", p2[posLe]));
                    } else if (posGe > -1) {
                        IntVar[] vect = new IntVar[p1.length - 1];
                        int n = 0;
                        for (int i = 0; i < p2.length; i++)
                            if (i != posGe)
                                vect[n++] = p2[i];
                        if (boolSum(vect))
                            support.pose(new SumBool(vect, ">=", p2[posGe]));
                        else
                            support.pose(new SumInt(vect, ">=", p2[posGe]));
                    } else {
                        support.pose(new LinearInt(p2, p1, "<=", p3));
                    }
                }
                break;
            default:
                throw new IllegalArgumentException("%% ERROR: Relation in linear constraint not supported.");
        }
    }

    boolean allPositive(int[] ws) {
	for (int w : ws) 
	    if (w < 0)
		return false;
	return true;
    }
    
    boolean allNonPositive(int[] ws) {
	for (int w : ws) 
	    if (w > 0)
		return false;
	return true;

    }
    
    boolean allConstants(IntVar[] p) {
        boolean sat = true;
        int k = 0;
        while (sat && k < p.length) {
            sat = (p[k].min() == p[k].max());
            k++;
        }
        return sat;
    }

    boolean allWeightsOne(int[] w) {
        //boolean allOne=true;
        for (int i = 0; i < w.length; i++)
            if (w[i] != 1)
                return false;
        return true;
    }

    boolean allWeightsMinusOne(int[] w) {
        //boolean allOne=true;
        for (int i = 0; i < w.length; i++)
            if (w[i] != -1)
                return false;
        return true;
    }

    boolean boolSum(IntVar[] vs) {
        for (IntVar v : vs)
            if (v.min() < 0 || v.max() > 1)
                return false;
        return true;
    }

    int sumPossible(int[] ws, int result) {
        if (result == 0) {
            int one = 0, minusOne = 0;
            int lastOnePosition = -1, lastMinusOnePosition = -1;

            for (int i = 0; i < ws.length; i++)
                if (ws[i] == 1) {
                    one++;
                    lastOnePosition = i;
                } else if (ws[i] == -1) {
                    minusOne++;
                    lastMinusOnePosition = i;
                }

            if (one == 1 && minusOne == ws.length - 1)
                return lastOnePosition;
            else if (minusOne == 1 && one == ws.length - 1)
                return lastMinusOnePosition;
            else
                return -1;
        } else
            return -1;
    }

    int sumLePossible(int[] ws, int result) {
        if (result == 0) {
            int one = 0, minusOne = 0;
	    int lastMinusOnePosition = -1;

            for (int i = 0; i < ws.length; i++)
                if (ws[i] == 1) {
                    one++;
                } else if (ws[i] == -1) {
                    minusOne++;
                    lastMinusOnePosition = i;
                }

            if (minusOne == 1 && one == ws.length - 1)
                return lastMinusOnePosition;
            else
                return -1;
        } else
            return -1;
    }

    int sumGePossible(int[] ws, int result) {
        if (result == 0) {
            int one = 0, minusOne = 0;
            int lastOnePosition = -1;

            for (int i = 0; i < ws.length; i++)
                if (ws[i] == 1) {
                    one++;
                    lastOnePosition = i;
                } else if (ws[i] == -1) {
                    minusOne++;
                }

            if (one == 1 && minusOne == ws.length - 1)
                return lastOnePosition;
            else
                return -1;
        } else
            return -1;
    }

    boolean paramZero(IntVar v) {
        return v.singleton() && v.value() == 0;
    }

    boolean binaryVar(IntVar v) {
	return v.min() >= 0 && v.max() <= 1;
    }
}
