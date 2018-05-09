/**
 * ComparisonConstraints.java
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
import org.jacop.core.IntDomain;

import org.jacop.fz.*;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XltC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XgtY;
import org.jacop.constraints.XgteqY;
import org.jacop.constraints.XlteqC;

import org.jacop.satwrapper.SatTranslation;
import org.jacop.constraints.XorBool;
import org.jacop.constraints.Not;


/**
 *
 * Generation of comparison constraints in flatzinc
 *
 * @author Krzysztof Kuchcinski 
 *
 */
class ComparisonConstraints implements ParserTreeConstants {

    boolean reified;
    Support support;
    Store store;
    SatTranslation sat;
    
    public ComparisonConstraints(Support support) {
	this.support = support;
	this.store = support.store;
	this.sat = support.sat;
    }

    // =========== bool =================
    void gen_bool_eq(SimpleNode node) {

        if (support.options.useSat()) {
            IntVar a = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
            IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

            sat.generate_eq(a, b);
            return;
        }
        reified = false;
        int_comparison(Support.eq, node);
    }

    void gen_bool_eq_reif(SimpleNode node) {

        if (support.options.useSat()) {

            IntVar v1 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
            IntVar v2 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
            IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

            sat.generate_eq_reif(v1, v2, v3);

            return;
        }

        reified = true;
        int_comparison(Support.eq, node);
    }

    void gen_bool_ne(SimpleNode node) {
        if (support.options.useSat()) {

            IntVar a = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
            IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

            sat.generate_not(a, b);
            return;
        }

        reified = false;
        int_comparison(Support.ne, node);
    }

    void gen_bool_ne_reif(SimpleNode node) {

        if (support.options.useSat()) {

            IntVar v1 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
            IntVar v2 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
            IntVar v3 = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

            sat.generate_neq_reif(v1, v2, v3);
            return;
        }

        reified = true;
        int_comparison(Support.ne, node);
    }

    void gen_bool_le(SimpleNode node) {

        if (support.options.useSat()) {

            IntVar a = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
            IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

            sat.generate_le(a, b);
            return;
        }

        reified = false;
        int_comparison(Support.le, node);
    }

    void gen_bool_le_reif(SimpleNode node) {

        if (support.options.useSat()) {

            IntVar a = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
            IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
            IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

            sat.generate_le_reif(a, b, c);
            return;
        }

        reified = true;
        int_comparison(Support.le, node);
    }

    void gen_bool_lt(SimpleNode node) {

        if (support.options.useSat()) {

            IntVar a = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
            IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));

            sat.generate_lt(a, b);
            return;
        }

        reified = false;
        int_comparison(Support.lt, node);
    }

    void gen_bool_lt_reif(SimpleNode node) {

        if (support.options.useSat()) {

            IntVar a = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(0));
            IntVar b = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(1));
            IntVar c = support.getVariable((ASTScalarFlatExpr) node.jjtGetChild(2));

            sat.generate_lt_reif(a, b, c);
        }

        reified = true;
        int_comparison(Support.lt, node);
    }

    // =========== int =================
    void gen_int_eq(SimpleNode node) {
        reified = false;
        int_comparison(Support.eq, node);
    }

    void gen_int_eq_reif(SimpleNode node) {
        reified = true;
        int_comparison(Support.eq, node);
    }

    void gen_int_ne(SimpleNode node) {
        reified = false;
        int_comparison(Support.ne, node);
    }

    void gen_int_ne_reif(SimpleNode node) {
        reified = true;
        int_comparison(Support.ne, node);
    }

    void gen_int_le(SimpleNode node) {
        reified = false;
        int_comparison(Support.le, node);
    }

    void gen_int_le_reif(SimpleNode node) {
        reified = true;
        int_comparison(Support.le, node);
    }

    void gen_int_lt(SimpleNode node) {
        reified = false;
        int_comparison(Support.lt, node);
    }

    void gen_int_lt_reif(SimpleNode node) {
        reified = true;
        int_comparison(Support.lt, node);
    }

    void int_comparison(int operation, SimpleNode node) {

        ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
        ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);

        if (reified) { // reified constraint
            PrimitiveConstraint c = null;
            ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);
            IntVar v3 = support.getVariable(p3);

            if (p2.getType() == 0 || p2.getType() == 1) { // var rel int or bool
                IntVar v1 = support.getVariable(p1);

                int i2 = support.getInt(p2);
                if (i2 < IntDomain.MinInt || i2 > IntDomain.MaxInt)
                    throw new ArithmeticException("Constant "+i2+" outside variable bounds ; must be in interval "+IntDomain.MinInt+".."+IntDomain.MaxInt);
                switch (operation) {

                    case Support.eq:
                        if (!v1.domain.contains(i2)) {
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
                        } else if (generateForEqC(v1, i2, v3))
			    return;
			else {
                            // if (support.options.useSat()) {  // it can be moved to SAT solver but it is slow in the current implementation
                            //     sat.generate_eqC_reif(v1, i2, v3);
                            //     return;
                            // }
                            // else
                            // c = new XeqC(v1, i2);
			    support.pose(fzXeqCReified(v1, i2, v3));
			    return;
			}
                        // break;

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
                        } else if (generateForNeqC(v1, i2, v3)) { // binary variable
			    return;
			}
			else
                            // if (support.options.useSat()) {  // it can be moved to SAT solver but it is slow in the current implementation
                            //     sat.generate_neC_reif(v1, i2, v3);
                            //     return;
                            // }
                            // else
                            c = new XneqC(v1, i2);
                        break;
                    case Support.lt:
                        if (v1.max() < i2) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (v1.min() >= i2) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else
                            c = new XltC(v1, i2);
                        break;
                    case Support.gt:
                        if (v1.min() > i2) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (v1.max() <= i2) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else
                            c = new XgtC(v1, i2);
                        break;
                    case Support.le:
                        if (v1.max() <= i2) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (v1.min() > i2) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else
                            c = new XlteqC(v1, i2);
                        break;
                    case Support.ge:
                        if (v1.min() >= i2) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (v1.max() < i2) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else
                            c = new XgteqC(v1, i2);
                        break;
		default:
		    throw new RuntimeException("Internal error in " + getClass().getName());
                }
            } else if (p1.getType() == 0 || p1.getType() == 1) { // int rel var or bool
                IntVar v2 = support.getVariable(p2);
                int i1 = support.getInt(p1);
                if (i1 < IntDomain.MinInt || i1 > IntDomain.MaxInt)
                    throw new ArithmeticException("Constant "+i1+" outside variable bounds; must be in interval "+IntDomain.MinInt+".."+IntDomain.MaxInt);

                switch (operation) {

                    case Support.eq:
                        if (!v2.domain.contains(i1)) { //v2.min() > i1 || v2.max() < i1) {
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
                        } else if (generateForEqC(v2, i1, v3))  // binary variable
			    return;
			else {
                        //     c = new XeqC(v2, i1);
			    support.pose(fzXeqCReified(v2, i1, v3));
			    return;
			}
                        // break;
			
                    case Support.ne:
                        if (v2.min() > i1 || v2.max() < i1) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (v2.min() == i1 && v2.singleton()) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else if (generateForNeqC(v2, i1, v3))
			    return;
			else
                            c = new XneqC(v2, i1);
                        break;
                    case Support.lt:
                        if (i1 < v2.min()) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (i1 >= v2.max()) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else
                            c = new XgtC(v2, i1);
                        break;
                    case Support.gt:
                        if (i1 > v2.max()) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (i1 <= v2.min()) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else
                            c = new XltC(v2, i1);
                        break;
                    case Support.le:
                        if (i1 <= v2.min()) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (i1 > v2.max()) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else
                            // if (support.options.useSat()) {  // it can be moved to SAT solver but it is slow in the current implementation
                            //     sat.generate_geC_reif(v2, i1, v3);
                            //     return;
                            // }
                            // else
                            c = new XgteqC(v2, i1);
                        break;
                    case Support.ge:
                        if (i1 > v2.max()) {
                            v3.domain.in(store.level, v3, 1, 1);
                            return;
                        } else if (i1 < v2.min()) {
                            v3.domain.in(store.level, v3, 0, 0);
                            return;
                        } else
                            c = new XlteqC(v2, i1);
                        break;
		default:
		    throw new RuntimeException("Internal error in " + getClass().getName());
                }
            } else { // var rel var
                IntVar v1 = support.getVariable(p1);
                IntVar v2 = support.getVariable(p2);

                switch (operation) {
                    case Support.eq:
			if (generateForEq(v1, v2, v3))
			    return;
			else if (generateForEq(v2, v1, v3))
			    return;
			else
			    if (binaryVar(v1) && binaryVar(v2)) {
				support.pose(new Not(new XorBool(new IntVar[] {v1, v2}, v3)));
				return;
			    }
			if (v2.singleton())
			    c = new XeqC(v1, v2.value());
			else if (v1.singleton())
			    c = new XeqC(v2, v1.value());
			else
			    c = new XeqY(v1, v2);
                        break;
                    case Support.ne:
			if (generateForNeq(v1, v2, v3))
			    return;
			else if (generateForNeq(v2, v1, v3))
			    return;
			else if (binaryVar(v1) && binaryVar(v2)) {
			    support.pose(new XorBool(new IntVar[] {v1, v2}, v3));
			    return;
			}
			else
			    c = new XneqY(v1, v2);
                        break;
                    case Support.lt:
                        c = new XltY(v1, v2);
                        break;
                    case Support.gt:
                        c = new XgtY(v1, v2);
                        break;
                    case Support.le:
                        c = new XlteqY(v1, v2);
                        break;
                    case Support.ge:
                        c = new XgteqY(v1, v2);
                        break;
		default:
		    throw new RuntimeException("Internal error in " + getClass().getName());
                }
            }

            Constraint cr = new Reified(c, v3);
            support.pose(cr);
        } else { // not reified constraints

            if (p1.getType() == 0 || p1.getType() == 1) { // first parameter int or bool
                if (p2.getType() == 0 || p2.getType() == 1) { // first parameter int/bool & second parameter int/bool
                    int i1 = support.getInt(p1);
                    if (i1 < IntDomain.MinInt || i1 > IntDomain.MaxInt)
                        throw new ArithmeticException("Constant "+i1+" outside variable bounds; must be in interval "+IntDomain.MinInt+".."+IntDomain.MaxInt);
                    int i2 = support.getInt(p2);
                    if (i2 < IntDomain.MinInt || i2 > IntDomain.MaxInt)
                        throw new ArithmeticException("Constant "+i2+" outside variable bounds; must be in interval "+IntDomain.MinInt+".."+IntDomain.MaxInt);
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
                        case Support.gt:
                            if (i1 <= i2)
                                throw Store.failException;
                            break;
                        case Support.le:
                            if (i1 > i2)
                                throw Store.failException;
                            break;
                        case Support.ge:
                            if (i1 < i2)
                                throw Store.failException;
                            break;
		    default:
			throw new RuntimeException("Internal error in " + getClass().getName());
                    }
                } else { // first parameter int/bool & second parameter var

                    int i1 = support.getInt(p1);
                    if (i1 < IntDomain.MinInt || i1 > IntDomain.MaxInt)
                        throw new ArithmeticException("Constant "+i1+" outside variable bounds; must be in interval "+IntDomain.MinInt+".."+IntDomain.MaxInt);
                    IntVar v2 = support.getVariable(p2);

                    switch (operation) {
                        case Support.eq:
                            v2.domain.in(store.level, v2, i1, i1);
                            break;
                        case Support.ne:
                            v2.domain.inComplement(store.level, v2, i1);
                            break;
                        case Support.lt:
                            v2.domain.in(store.level, v2, i1 + 1, IntDomain.MaxInt);
                            break;
                        case Support.gt:
                            v2.domain.in(store.level, v2, IntDomain.MinInt, i1 - 1);
                            break;
                        case Support.le:
                            v2.domain.in(store.level, v2, i1, IntDomain.MaxInt);
                            break;
                        case Support.ge:
                            v2.domain.in(store.level, v2, IntDomain.MinInt, i1);
                            break;
		    default:
			throw new RuntimeException("Internal error in " + getClass().getName());
                    }
                }
            } else { // first parameter var
                if (p2.getType() == 0 || p2.getType() == 1) { // first parameter var & second parameter int

                    IntVar v1 = support.getVariable(p1);
                    int i2 = support.getInt(p2);
                    if (i2 < IntDomain.MinInt || i2 > IntDomain.MaxInt)
                        throw new ArithmeticException("Constant "+i2+" outside variable bounds; must be in interval "+IntDomain.MinInt+".."+IntDomain.MaxInt);

                    switch (operation) {
                        case Support.eq:
                            v1.domain.in(store.level, v1, i2, i2);
                            break;
                        case Support.ne:
                            v1.domain.inComplement(store.level, v1, i2);
                            break;
                        case Support.lt:
                            v1.domain.in(store.level, v1, IntDomain.MinInt, i2 - 1);
                            break;
                        case Support.gt:
                            v1.domain.in(store.level, v1, i2 + 1, IntDomain.MaxInt);
                            break;
                        case Support.le:
                            v1.domain.in(store.level, v1, IntDomain.MinInt, i2);
                            break;
                        case Support.ge:
                            v1.domain.in(store.level, v1, i2, IntDomain.MaxInt);
                            break;
		    default:
			throw new RuntimeException("Internal error in " + getClass().getName());
                    }

                } else { // first parameter var & second parameter var

                    IntVar v1 = support.getVariable(p1);
                    IntVar v2 = support.getVariable(p2);

                    switch (operation) {
                        case Support.eq:
                            support.pose(new XeqY(v1, v2));
                            break;
                        case Support.ne:
                            support.pose(new XneqY(v1, v2));
                            break;
                        case Support.lt:
                            support.pose(new XltY(v1, v2));
                            break;
                        case Support.gt:
                            support.pose(new XgtY(v1, v2));
                            break;
                        case Support.le:
                            support.pose(new XlteqY(v1, v2));
                            break;
                        case Support.ge:
                            support.pose(new XgteqY(v1, v2));
                            break;
		    default:
			throw new RuntimeException("Internal error in " + getClass().getName());
                    }
                }
            }
        }
    }


    boolean generateForEqC(IntVar v1, int i2, IntVar b) {
	if (v1.min() >= 0 && v1.max() <= 1) { // binary variables
	    if (i2 == 0) {
		support.pose(new XneqY(v1, b));
		return true;
	    }
	    else if (i2 == 1) {
		support.pose(new XeqY(v1, b));
		return true;
	    }
	}
	return false;
    }
    
    boolean generateForNeqC(IntVar v1, int i2, IntVar b) {
	if (v1.min() >= 0 && v1.max() <= 1) { // binary variables
	    if (i2 == 0) {
		support.pose(new XeqY(v1, b));
		return true;
	    }
	    else if (i2 == 1) {
		support.pose(new XneqY(v1, b));
		return true;
	    }
	}
	return false;
    }
    
    boolean generateForEq(IntVar v1, IntVar v2, IntVar b) {
	if (v1.min() >= 0 && v1.max() <= 1) {
	    if (v2.singleton())
		if (v2.value() == 1) {
		    support.pose(new XeqY(v1, b));
		    return true;
		}
		else if (v2.value() == 0) {
		    support.pose(new XneqY(v1, b));
		    return true;
		}
	}
	return false;
    }

    boolean generateForNeq(IntVar v1, IntVar v2, IntVar b) {
	if (v1.min() >= 0 && v1.max() <= 1) {
	    if (v2.singleton())
		if (v2.value() == 1) {
		    support.pose(new XneqY(v1, b));
		    return true;
		}
		else if (v2.value() == 0) {
		    support.pose(new XeqY(v1, b));
		    return true;
		}
	}
	return false;
    }

    boolean binaryVar(IntVar v) {
	return v.min() >= 0 && v.max() <= 1;
    }
    
    Constraint fzXeqCReified( IntVar x, Integer c, IntVar b) {

	    return new Constraint(new IntVar[] {x, b}) {

	    @Override public void consistency(final Store store) {

		if (x.singleton(c)) {
		    b.domain.in(store.level, b, 1, 1);
		} else if (!x.domain.contains(c)) {
		    b.domain.in(store.level, b, 0, 0);
		    removeConstraint();
		} else if (b.max() == 0) {// x==c must be false
		    x.domain.inComplement(store.level, x, c);
		    removeConstraint();
		}
		else if (b.min() == 1) // x==c must be true
		    x.domain.in(store.level, x, c, c);
	    }

	    @Override public int getDefaultConsistencyPruningEvent() {
		return IntDomain.ANY;
	    }
    
	    @Override public String toString() {
		return "fz : XeqC_Reified("+x+", " + c + ", " + b + " )";
	    }	
	};
    }
}
