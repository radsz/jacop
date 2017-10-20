/*
 * Constraints.java
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
package org.jacop.fz;

import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

import org.jacop.satwrapper.SatTranslation;

import org.jacop.fz.constraints.Support;

/**
 *
 * The part of the parser responsible for parsing constraints. 
 *
 * @author Krzysztof Kuchcinski 
 * @version 4.5
 *
 */
public class Constraints implements ParserTreeConstants {

    Tables dictionary;
    Store store;
    String p;

    boolean debug;
    
    final static int eq = 0, ne = 1, lt = 2, gt = 3, le = 4, ge = 5;

    // ============ SAT solver interface ==============
    SatTranslation sat;

    Support support;
    
    final org.jacop.fz.constraints.ConstraintFncs cf; // = new org.jacop.fz.constraints.ConstraintFncs(store, dict, sat);

    /**
     * It creates an object to parse the constraint part of the flatzinc file.
     * @param store the constraint store in which the constraints are being created.
     * @param dict the current dictionary (tables of all variables and constants)
     */
    public Constraints(Store store, Tables dict) {
        this.store = store;
        this.dictionary = dict;

        sat = new SatTranslation(store);
        // impose SAT-solver
        sat.impose();

	support = new Support(store, dict, sat);
	
	cf = new org.jacop.fz.constraints.ConstraintFncs(support);

    }
    
    void setOptions(Options options) {
	support.options = options;
        debug = options.debug();
    }
    
    void generateAllConstraints(SimpleNode astTree) throws Throwable {

	sat.debug = debug;
	
        int n = astTree.jjtGetNumChildren();

        for (int i = 0; i < n; i++) {
            SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
            // go for ConstraintItems
            if (node.getId() == JJTCONSTRAINTITEMS) {

                int k = node.jjtGetNumChildren();
                for (int j = 0; j < k; j++) {
                    SimpleNode snode = (SimpleNode) node.jjtGetChild(j);
                    generateConstraint(snode);
                }
            }
        }

        support.poseDelayedConstraints();

    }

    void generateConstraint(SimpleNode constraintWithAnnotations) throws Throwable {

        // if (debug)
        //   constraintWithAnnotations.dump("");

        // default consistency - bounds
        support.boundsConsistency = true;
        support.domainConsistency = false;
        support.definedVar = null;

        int numberChildren = constraintWithAnnotations.jjtGetNumChildren();
        if (numberChildren > 1) {
            support.parseAnnotations(constraintWithAnnotations);
        }

        SimpleNode node = (SimpleNode) constraintWithAnnotations.jjtGetChild(0);

        // Generate constraint
        if (node.getId() == JJTCONSTELEM) {

            p = ((ASTConstElem) node).getName();

            try {

                java.lang.reflect.Method method = cf.getClass().getMethod(p, SimpleNode.class);
                method.invoke(cf, node);

            } catch (NoSuchMethodException e) {
                throw new RuntimeException("%% JaCoP flatzinc back-end: constraint " + p + " is not supported.");
            } catch (IllegalAccessException e) {
                System.out.println(e);
            } catch (java.lang.reflect.InvocationTargetException e) {
                System.out.println("%% problem detected for " + p);
		
                try {
                    throw e.getCause();
                } catch (FailException fe) {
                    throw fe;
                } catch (ArithmeticException ae) {
                    throw ae;
                } catch(IllegalArgumentException ie) {
		    throw ie;
		} catch (ParseException pe) {
                    throw pe;
                } catch (TokenMgrError te) {
                    throw te;
                } catch (ArrayIndexOutOfBoundsException ie) {
                    throw ie;
                } catch (OutOfMemoryError me) {
                    throw me;
                } catch (StackOverflowError stack) {
                    throw stack;
                } catch (TrivialSolution trivial) {
                    throw trivial;
                }
            }
        }
    }

    void generateAlias(SimpleNode constraintWithAnnotations) {

        SimpleNode node = (SimpleNode) constraintWithAnnotations.jjtGetChild(0);

        if (node.getId() == JJTCONSTELEM) {

            p = ((ASTConstElem) node).getName();

            if (p.startsWith("bool2int") || p.startsWith("int2bool")) {

                ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
                ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
                IntVar v1 = support.getVariable(p1), v2 = support.getVariable(p2);
                dictionary.addAlias(v1, v2);

                if (v1.singleton() || v2.singleton()) {
                    v1.domain.in(store.level, v1, v2.domain);
                    v2.domain.in(store.level, v2, v1.domain);
                }

                if (debug)
                    System.out.println("Alias: " + v1 + " == " + v2);
            }
        }
    }
}
    
